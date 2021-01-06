# A Perl module implementing a basic asynchronous event functionality compatible
# with AnyEvent
#
# Copyright (C) 2008-2020  Yann Riou <yaribzh@gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#

package SimpleEvent;

use strict;
use warnings;

use File::Spec::Functions qw'devnull';
use IO::Select;
use List::Util 'first';
use POSIX qw':sys_wait_h';
use Socket;
use Storable qw'freeze thaw';
use Tie::RefHash;
use Time::HiRes;

use SimpleLog;

my $moduleVersion='0.5';

sub any (&@) { my $c = shift; return defined first {&$c} @_; }
sub all (&@) { my $c = shift; return ! defined first {! &$c} @_; }
sub none (&@) { my $c = shift; return ! defined first {&$c} @_; }
sub notall (&@) { my $c = shift; return defined first {! &$c} @_; }
sub getVersion { return $moduleVersion }

my %conf = ( mode => undef,
             timeSlice => 1,
             maxChildProcesses => 16,
             maxQueuedProcesses => 128,
             sLog => SimpleLog->new(logFiles => [''], logLevels => [4], useANSICodes => [-t STDOUT ? 1 : 0], useTimestamps => [-t STDOUT ? 0 : 1], prefix => "[SimpleEvent] ") );

my %forkedProcesses;
my %win32Processes;
tie %win32Processes, 'Tie::RefHash';
my @queuedProcesses;
my %signals;
my %sockets;
tie %sockets, 'Tie::RefHash';
my %timers;
my $endLoopCondition;

my $osIsWindows=$^O eq 'MSWin32';

sub slog {
  $conf{sLog}->log(@_);
}

sub init {
  my (%params) = @_;
  foreach my $param (keys %params) {
    if(any {$param eq $_} (keys %conf)) {
      $conf{$param}=$params{$param};
    }else{
      slog("Ignoring invalid initialization parameter ($param)",2)
    }
  }

  if(! defined $conf{mode} || $conf{mode} eq 'AnyEvent') {
    eval "use AnyEvent";
    if($@) {
      if(defined $conf{mode}) {
        slog("Unable to load AnyEvent module: $@",1);
        return 0;
      }
      $conf{mode}='internal';
    }else{
      $conf{mode}='AnyEvent';
    }
  }elsif($conf{mode} ne 'internal') {
    slog("Invalid mode value \"$conf{mode}\"",1);
    return 0;
  }

  $SIG{CHLD} = sub { local ($!, $?); _reapForkedProcesses(); } if(! $osIsWindows && $conf{mode} eq 'internal');

  if($osIsWindows) {
    eval "use Win32";
    eval "use Win32::Process";
  }

  if($conf{mode} eq 'AnyEvent') {
    my $anyEventModel=AnyEvent::detect();
    slog("Event loop initialized using model $anyEventModel",3);
    $endLoopCondition=AE::cv();
  }else{
    slog("Event loop initialized using internal model",3);
    $endLoopCondition=0;
  }

  return 1;
}

sub getModel {
  return undef unless(defined $endLoopCondition);
  return 'internal' if($conf{mode} eq 'internal');
  return AnyEvent::detect();
}

sub startLoop {
  my $p_cleanUpFunction=shift;
  if(! defined $endLoopCondition) {
    slog('Unable to start main loop, event loop is uninitialized',1);
    return 0;
  }
  slog('Starting event loop...',3);
  if($conf{mode} eq 'AnyEvent') {
    my $processManagerTimer=AE::timer(0,$conf{timeSlice},\&_manageProcesses);
    $endLoopCondition->recv();
  }else{
    while(! $endLoopCondition) {
      _checkSimpleTimers();
      _checkSimpleSockets();
      _manageProcesses();
    }
  }
  slog('Event loop stopped',3);
  if(defined $p_cleanUpFunction) {
    my @remainingPids=keys %forkedProcesses;
    my @remainingWin32Processes=keys %win32Processes;
    my @remainingSignals=keys %signals;
    my @remainingSockets=keys %sockets;
    my @remainingTimers=keys %timers;
    &{$p_cleanUpFunction}(\@remainingPids,\@remainingWin32Processes,\@queuedProcesses,\@remainingSignals,\@remainingSockets,\@remainingTimers);
  }
  my ($nbRemainingForkedProcesses,$nbRemainingWin32Processes,$nbQueuedProcesses)=(scalar keys %forkedProcesses,scalar keys %win32Processes,scalar @queuedProcesses);
  my ($nbRemainingSignals,$nbRemainingSockets,$nbRemainingTimers)=(scalar keys %signals,scalar keys %sockets, scalar keys %timers);
  slog("$nbRemainingForkedProcesses forked process".($nbRemainingForkedProcesses>1?'es are':' is').' still running',2) if($nbRemainingForkedProcesses);
  slog("$nbRemainingWin32Processes Win32 process".($nbRemainingWin32Processes>1?'es are':' is').' still running',2) if($nbRemainingWin32Processes);
  slog("$nbQueuedProcesses process".($nbQueuedProcesses>1?'es are':' is').' still queued',2) if($nbQueuedProcesses);
  slog("$nbRemainingSignals signal handler".($nbRemainingSignals>1?'s are':' is').' still registered',2) if($nbRemainingSignals);
  slog("$nbRemainingSockets socket".($nbRemainingSockets>1?'s are':' is').' still registered',2) if($nbRemainingSockets);
  slog("$nbRemainingTimers timer".($nbRemainingTimers>1?'s are':' is').' still registered',2) if($nbRemainingTimers);
}

sub stopLoop {
  if(! defined $endLoopCondition) {
    slog('Unable to end main loop, event loop is uninitialized',1);
    return 0;
  }
  slog('Stopping event loop...',3);
  if($conf{mode} eq 'AnyEvent') {
    $endLoopCondition->send();
  }else{
    $endLoopCondition=1;
  }
  return 1;
}

sub forkProcess {
  if(! defined $endLoopCondition) {
    slog('Unable to fork process, event loop is uninitialized',1);
    return 0;
  }
  my ($p_processFunction,$p_endCallback,$preventQueuing)=@_;
  if((keys %forkedProcesses) + (keys %win32Processes) >= $conf{maxChildProcesses}) {
    if($preventQueuing) {
      slog("Unable to fork process, maximum number of child process ($conf{maxChildProcesses}) is already running",1);
      return 0;
    }elsif(@queuedProcesses >= $conf{maxQueuedProcesses}) {
      slog('Unable to fork process, child process queue is full',1);
      return 0;
    }else{
      slog('Queuing new fork request',5);
      push(@queuedProcesses,{type => 'fork', function => $p_processFunction, callback => $p_endCallback});
      return -1;
    }
  }
  return _forkProcess($p_processFunction,$p_endCallback);
}

sub _forkProcess {
  my ($p_processFunction,$p_endCallback)=@_;
  my $childPid = fork();
  if(! defined $childPid) {
    slog("Unable to fork process, $!",1);
    return 0;
  }
  if($childPid == 0) {
    local $SIG{CHLD};
    if($osIsWindows) {
      no warnings 'redefine';
      eval "sub Win32::Process::DESTROY {}";
      close(STDIN);
      open(STDIN,'<',devnull());
    }
    &{$p_processFunction}();
    exit 0;
  }
  slog("Forked new process (PID: $childPid)",5);
  if($conf{mode} eq 'internal' || $osIsWindows) {
    $forkedProcesses{$childPid}=$p_endCallback;
  }else{
    $forkedProcesses{$childPid}=AE::child($childPid,
                                          sub {
                                            &{$p_endCallback}($_[0],$_[1] >> 8,$_[1] & 127,$_[1] & 128);
                                            delete $forkedProcesses{$childPid};
                                          } );
  }
  return $childPid;
}

sub forkCall {
  if(! defined $endLoopCondition) {
    slog('Unable to fork function call, event loop is uninitialized',1);
    return 0;
  }
  my ($p_processFunction,$p_endCallback,$preventQueuing)=@_;
  my ($inSocket,$outSocket);
  if(! socketpair($inSocket,$outSocket,AF_UNIX,SOCK_STREAM,PF_UNSPEC)) {
    slog("Unable to fork function call, cannot create socketpair: $!",1);
    return 0;
  }
  my ($readResultStatus,$readResultData)=(-1);
  my $forkResult = forkProcess(
    sub {
      close($outSocket);
      my $callResult = eval { freeze([undef, &{$p_processFunction}()]); };
      $callResult = freeze(["$@"]) if $@;
      print $inSocket $callResult;
      close($inSocket);
      exit 0;
    },
    sub {
      if(! $readResultStatus) {
        $p_endCallback->();
        return;
      }
      if($readResultStatus != 2) {
        my ($readStatus,$readResult)=_readSocketNonBlocking($outSocket);
        $readResultStatus=$readStatus;
        unregisterSocket($outSocket);
        close($outSocket);
        if(! $readStatus) {
          slog("Unable to read data from socketpair, $readResult",1);
          $p_endCallback->();
          return;
        }
        $readResultData.=$readResult;
      }
      slog('Socket pair not closed after forked call!',2) unless($readResultStatus == 2);
      my $r_callResult = eval { thaw($readResultData); };
      $r_callResult//=[$@];
      $@=shift(@{$r_callResult});
      slog("Error in forked call, $@",1) if($@);
      $p_endCallback->(@{$r_callResult});
    },
    $preventQueuing );
  if(! $forkResult) {
    slog('Unable to fork function call, error in forkProcess()',1);
    close($outSocket);
  }else{
    my $regSockRes=registerSocket($outSocket,
                                  sub {
                                    my ($readStatus,$readResult)=_readSocketNonBlocking($outSocket);
                                    $readResultStatus=$readStatus;
                                    if(! $readStatus) {
                                      unregisterSocket($outSocket);
                                      close($outSocket);
                                      slog("Unable to read data from socketpair, $readResult",1);
                                    }else{
                                      $readResultData.=$readResult;
                                      if($readStatus == 2) {
                                        unregisterSocket($outSocket);
                                        close($outSocket);
                                      }
                                    }
                                  });
    slog('Unable to register socket for forked function call, error in registerSocket()',1) unless($regSockRes);
  }
  return $forkResult;
}

sub _readSocketNonBlocking {
  my $socket=shift;
  my $result='';
  while(my @canRead=IO::Select->new($socket)->can_read(0)) {
    my $readLength=$socket->sysread(my $readData,POSIX::BUFSIZ);
    return (0,$!) unless(defined $readLength);
    return (2,$result) unless($readLength);
    $result.=$readData;
  }
  return (1,$result);
}

sub createWin32Process {
  if(! defined $endLoopCondition) {
    slog('Unable to create Win32 process, event loop is uninitialized',1);
    return 0;
  }
  if(! $osIsWindows) {
    slog('Unable to create Win32 process, incompatible OS',1);
    return 0;
  }
  my ($applicationPath,$p_commandParams,$workingDirectory,$p_endCallback,$p_stdRedirections,$preventQueuing)=@_;
  if((keys %forkedProcesses) + (keys %win32Processes) >= $conf{maxChildProcesses}) {
    if($preventQueuing) {
      slog("Unable to create Win32 process, maximum number of child process ($conf{maxChildProcesses}) is already running",1);
      return 0;
    }elsif(@queuedProcesses >= $conf{maxQueuedProcesses}) {
      slog('Unable to create Win32 process, child process queue is full',1);
      return 0;
    }else{
      slog('Queuing new win32 process',5);
      push(@queuedProcesses,{type => 'win32',
                             applicationPath => $applicationPath,
                             commandParams => $p_commandParams,
                             workingDirectory => $workingDirectory,
                             callback => $p_endCallback,
                             redirections => $p_stdRedirections});
      return -1;
    }
  }
  return _createWin32Process($applicationPath,$p_commandParams,$workingDirectory,$p_endCallback,$p_stdRedirections);
}

sub _createWin32Process {
  my ($applicationPath,$p_commandParams,$workingDirectory,$p_endCallback,$p_stdRedirections)=@_;
  my ($inheritHandles,$previousStdout,$previousStderr)=(0,undef,undef);
  if(defined $p_stdRedirections) {
    $inheritHandles=1;
    open($previousStdout,'>&',\*STDOUT);
    open($previousStderr,'>&',\*STDERR);
    foreach my $p_redirection (@{$p_stdRedirections}) {
      if(lc($p_redirection->[0]) eq 'stdout') {
        open(STDOUT,$p_redirection->[1]);
      }elsif(lc($p_redirection->[0]) eq 'stderr') {
        open(STDERR,$p_redirection->[1]);
      }
    }
  }
  my $win32ProcCreateRes = Win32::Process::Create(my $win32Process,
                                                  $applicationPath,
                                                  join(' ',map {_escapeWin32Parameter($_)} ($applicationPath,@{$p_commandParams})),
                                                  $inheritHandles,
                                                  0,
                                                  $workingDirectory);
  if(defined $p_stdRedirections) {
    open(STDOUT,'>&',$previousStdout);
    open(STDERR,'>&',$previousStderr);
  }
  if(! $win32ProcCreateRes) {
    my $errorNb=Win32::GetLastError();
    my $errorMsg=$errorNb?Win32::FormatMessage($errorNb):'unknown error';
    $errorMsg=~s/\cM?\cJ$//;
    slog("Unable to create Win32 process ($errorMsg)",1);
    return 0;
  }
  slog('Created new Win32 process (PID: '.$win32Process->GetProcessID().')',5);
  $win32Processes{$win32Process}=$p_endCallback;
  return $win32Process;
}

sub _escapeWin32Parameter {
  my $arg = shift;
  $arg =~ s/(\\*)"/$1$1\\"/g;
  if($arg =~ /[ \t]/) {
    $arg =~ s/(\\*)$/$1$1/;
    $arg = "\"$arg\"";
  }
  return $arg;
}

sub closeAllUserFds {
  if(! $osIsWindows) {
    my $devFdFh;
    if(opendir($devFdFh,'/dev/fd') || opendir($devFdFh,'/proc/self/fd')) {
      my @fds = sort { $a <=> $b } (grep {/^\d+$/} readdir($devFdFh));
      if(@fds < 20 || "@fds" ne join(' ', 0..$#fds)) {
        foreach my $fd (@fds) {
          POSIX::close($fd) if($fd > $^F);
        }
        return;
      }
    }
  }
  my $maxFd = eval {POSIX::sysconf(POSIX::_SC_OPEN_MAX()) -1} // 1023;
  for my $fd (($^F+1)..$maxFd) {
    POSIX::close($fd);
  }
}

sub createDetachedProcess {
  my ($applicationPath,$p_commandParams,$workingDirectory,$createNewConsole)=@_;
  if($osIsWindows) {
    my $createFlag = $createNewConsole ? Win32::Process::CREATE_NEW_CONSOLE() : Win32::Process::DETACHED_PROCESS();
    my $win32ProcCreateRes = Win32::Process::Create(my $win32Process,
                                                    $applicationPath,
                                                    join(' ',map {_escapeWin32Parameter($_)} ($applicationPath,@{$p_commandParams})),
                                                    0,
                                                    $createFlag,
                                                    $workingDirectory);
    if(! $win32ProcCreateRes) {
      my $errorNb=Win32::GetLastError();
      my $errorMsg=$errorNb?Win32::FormatMessage($errorNb):'unknown error';
      $errorMsg=~s/\cM?\cJ$//;
      slog("Unable to create detached process ($errorMsg)",1);
      return 0;
    }
    slog('Created new detached Win32 process (PID: '.$win32Process->GetProcessID().')',5);
    return $win32Process;
  }else{
    slog('Ignoring new console mode for detached process creation (only supported on Windows system)',2) if($createNewConsole);
    my $forkRes = forkProcess(
      sub {
        if(! POSIX::setsid()) {
          slog('Unable to call POSIX::setsid() for detached process creation',1);
          exit 1;
        }
        my $childPid = fork();
        if(! defined $childPid) {
          slog("Unable to fork process for detached process creation (fork 2), $!",1);
          exit 2;
        }
        exit 0 if($childPid);
        chdir($workingDirectory);
        closeAllUserFds();
        my $nullDevice=devnull();
        open(STDIN,'<',$nullDevice);
        open(STDOUT,'>',$nullDevice);
        open(STDERR,'>',$nullDevice);
        exec {$applicationPath} ($applicationPath,@{$p_commandParams});
      },
      sub {
        my (undef,$exitCode,$signalNb,$hasCoreDump)=@_;
        if($exitCode || $signalNb || $hasCoreDump) {
          slog('Error during detached process creation (first forked process exited abnormally)',1);
        }
      },
      0);
    if(! $forkRes) {
      slog("Unable to fork process for detached process creation (fork 1), $!",1);
      return 0;
    }else{
      slog('Created new detached daemon process',5);
      return 1;
    }
  }
}

sub _manageProcesses {
  if($osIsWindows) {
    _reapForkedProcesses();
    _reapWin32Processes();
  }
  _checkQueuedProcesses();
}

sub _reapForkedProcesses {
  while(my $pid = waitpid(-1,WNOHANG)) {
    last if($pid == -1);
    if(exists $forkedProcesses{$pid}) {
      slog("End of forked process (PID: $pid), calling callback",5);
      &{$forkedProcesses{$pid}}($pid,$? >> 8,$? & 127,$? & 128);
      delete $forkedProcesses{$pid};
    }else{
      slog("End of forked process (PID: $pid) (unknown child process)",5);
    }
  }
}

sub _reapWin32Processes {
  foreach my $win32Process (keys %win32Processes) {
    $win32Process->GetExitCode(my $exitCode);
    if($exitCode != Win32::Process::STILL_ACTIVE()) {
      my $pid=$win32Process->GetProcessID();
      slog("End of Win32 process (PID: $pid), calling callback",5);
      &{$win32Processes{$win32Process}}($pid,$exitCode);
      delete $win32Processes{$win32Process};
    }
  }
}

sub _checkQueuedProcesses {
  while(@queuedProcesses && $conf{maxChildProcesses} > (keys %forkedProcesses) + (keys %win32Processes)) {
    my $p_queuedProcess=shift(@queuedProcesses);
    if($p_queuedProcess->{type} eq 'fork') {
      _forkProcess($p_queuedProcess->{function},$p_queuedProcess->{callback});
    }else{
      _createWin32Process($p_queuedProcess->{applicationPath},$p_queuedProcess->{commandParams},$p_queuedProcess->{workingDirectory},$p_queuedProcess->{callback},$p_queuedProcess->{redirections});
    }
  }
}

sub registerSocket {
  if(! defined $endLoopCondition) {
    slog('Unable to register socket, event loop is uninitialized',1);
    return 0;
  }
  my ($socket,$p_readCallback)=@_;
  if(exists $sockets{$socket}) {
    slog('Unable to register socket in event loop: this socket has already been registered!',2);
    return 0;
  }
  if($conf{mode} eq 'internal') {
    $sockets{$socket}=$p_readCallback;
  }else{
    $sockets{$socket}=AE::io($socket,0,sub { &{$p_readCallback}($socket); });
  }
  slog('New socket registered',5);
  return 1;
}

sub unregisterSocket {
  my $socket=shift;
  if(! exists $sockets{$socket}) {
    slog('Unable to unregister socket in event loop: unknown socket!',2);
    return 0;
  }
  delete $sockets{$socket};
  slog('Socket unregistered',5);
  return 1;
}

sub _checkSimpleSockets {
  if(%sockets) {
    my @pendingSockets=IO::Select->new(keys %sockets)->can_read($conf{timeSlice});
    foreach my $pendingSock (@pendingSockets) {
      next unless(exists $sockets{$pendingSock}); # sockets can be unregistered by forked process exit callbacks at any time (linux), or by any other socket callback
      &{$sockets{$pendingSock}}($pendingSock);
    }
  }else{
    Time::HiRes::usleep($conf{timeSlice} * 1_000_000);
  }
}

sub registerSignal {
  if(! defined $endLoopCondition) {
    slog('Unable to register signal, event loop is uninitialized',1);
    return 0;
  }
  if($osIsWindows) {
    slog('Unable to register signal, incompatible OS',1);
    return 0;
  }
  my ($signal,$p_signalCallback)=@_;
  if(exists $signals{$signal}) {
    slog('Unable to register signal \"$signal\" in event loop: this signal has already been registered!',2);
    return 0;
  }
  if($conf{mode} eq 'internal') {
    $SIG{$signal}=$p_signalCallback;
    $signals{$signal}=$p_signalCallback;
  }else{
    $signals{$signal}=AE::signal($signal,$p_signalCallback);
  }
  slog("Signal $signal registered",5);
  return 1;
}

sub unregisterSignal {
  my $signal=shift;
  if(! exists $signals{$signal}) {
    slog('Unable to unregister signal in event loop: unknown signal!',2);
    return 0;
  }
  $SIG{$signal}='DEFAULT' if($conf{mode} eq 'internal');
  delete $signals{$signal};
  slog("Signal $signal unregistered",5);
  return 1;
}

sub addTimer {
  my ($name,$delay,$interval,$p_callback)=@_;
  if(! defined $endLoopCondition) {
    slog("Unable to add timer \"$name\", event loop is uninitialized",1);
    return 0;
  }
  if(exists $timers{$name}) {
    slog("Unable to add timer \"$name\" in event loop: this timer has already been registered!",2);
    return 0;
  }
  slog("Adding timer \"$name\" (delay:$delay, interval:$interval)",5);
  if($conf{mode} eq 'internal') {
    $timers{$name}={nextRun => Time::HiRes::time+$delay, interval => $interval, callback => $p_callback};
  }else{
    $timers{$name}=AE::timer($delay,$interval,sub { removeTimer($name) unless($interval); &{$p_callback}(); });
  }
  return 1;
}

sub removeTimer {
  my $name=shift;
  if(! exists $timers{$name}) {
    slog("Unable to remove timer \"$name\" from event loop: unknown timer!",2);
    return 0;
  }
  slog("Removing timer \"$name\"",5);
  delete $timers{$name};
  return 1;
}

sub _checkSimpleTimers {
  foreach my $timerName (keys %timers) {
    next unless(exists $timers{$timerName}); # timers can be removed by forked process exit callbacks at any time (linux), or by any other timer callback
    if(Time::HiRes::time >= $timers{$timerName}->{nextRun}) {
      if($timers{$timerName}->{interval}) {
        $timers{$timerName}->{nextRun}=Time::HiRes::time+$timers{$timerName}->{interval};
        &{$timers{$timerName}->{callback}}();
      }else{
        my $p_timerCallback=$timers{$timerName}->{callback};
        removeTimer($timerName);
        &{$p_timerCallback}();
      }
    }
  }
}

sub _debug {

  eval "use Data::Dumper";
  $Data::Dumper::Sortkeys=1;

  my $sep=0;
  if(%forkedProcesses) {
    $sep=1;
    print "forkedProcesses:\n";
    print Dumper(\%forkedProcesses);
  }
  if(%win32Processes) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "win32Processes:\n";
    print Dumper(\%win32Processes);
  }
  if(@queuedProcesses) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "queuedProcesses:\n";
    print Dumper(\@queuedProcesses);
  }
  if(%signals) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "signals:\n";
    print Dumper(\%signals);
  }
  if(%sockets) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "sockets:\n";
    print Dumper(\%sockets);
  }
  if(%timers) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "timers:\n";
    print Dumper(\%timers);
  }
  print +('#' x 79)."\n";
}

1;
