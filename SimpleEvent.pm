# A Perl module implementing a basic asynchronous event functionality compatible
# with AnyEvent
#
# Copyright (C) 2008-2015  Yann Riou <yaribzh@gmail.com>
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

use IO::Select;
use List::Util 'first';
use POSIX qw':sys_wait_h';
use Socket;
use Storable qw'freeze thaw';
use Tie::RefHash;
use Time::HiRes;

use SimpleLog;

my $moduleVersion='0.1';

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
      slog("Ignoring invalid constructor parameter ($param)",2)
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
    }
    &{$p_processFunction}();
    exit 0;
  }
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
  shutdown($inSocket, 0);
  shutdown($outSocket, 1);
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
      close($inSocket);
      my $freezedCallResult;
      my ($readData,$readLength);
      while(my @canRead=IO::Select->new($outSocket)->can_read(0)) {
        $readLength=$outSocket->sysread($readData,POSIX::BUFSIZ);
        if(! defined $readLength) {
          my $E="$!";
          slog("Unable to read data from socketpair, $E",1);
          $freezedCallResult=freeze([$E]);
          last;
        }
        last if($readLength == 0);
        $freezedCallResult.=$readData;
      }
      close($outSocket);
      my $callResult = eval { thaw($freezedCallResult); };
      $callResult//=[$@];
      $@=shift(@{$callResult});
      slog("Error in forked call, $@",1) if($@);
      &{$p_endCallback}(@{$callResult});
    },
    $preventQueuing );
  if(! $forkResult) {
    slog('Unable to fork function call, error in forkProcess()',1);
    close($inSocket);
    close($outSocket);
  }
  return $forkResult;
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
      &{$forkedProcesses{$pid}}($pid,$? >> 8,$? & 127,$? & 128);
      delete $forkedProcesses{$pid};
    }
  }
}

sub _reapWin32Processes {
  foreach my $win32Process (keys %win32Processes) {
    $win32Process->GetExitCode(my $exitCode);
    if($exitCode != Win32::Process::STILL_ACTIVE()) {
      &{$win32Processes{$win32Process}}($win32Process->GetProcessID(),$exitCode);
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
  return 1;
}

sub unregisterSocket {
  my $socket=shift;
  if(! exists $sockets{$socket}) {
    slog('Unable to unregister socket in event loop: unknown socket!',2);
    return 0;
  }
  delete $sockets{$socket};
  return 1;
}

sub _checkSimpleSockets {
  if(%sockets) {
    my @pendingSockets=IO::Select->new(keys %sockets)->can_read($conf{timeSlice});
    foreach my $pendingSock (@pendingSockets) {
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
  if(exists $conf{signals}->{$signal}) {
    slog('Unable to register signal \"$signal\" in event loop: this signal has already been registered!',2);
    return 0;
  }
  if($conf{mode} eq 'internal') {
    $SIG{$signal}=$p_signalCallback;
    $conf{signals}->{$signal}=$p_signalCallback;
  }else{
    $conf{signals}->{$signal}=AE::signal($signal,$p_signalCallback);
  }
  return 1;
}

sub unregisterSignal {
  my $signal=shift;
  if(! exists $conf{signals}->{$signal}) {
    slog('Unable to unregister signal in event loop: unknown signal!',2);
    return 0;
  }
  $SIG{$signal}='DEFAULT' if($conf{mode} eq 'internal');
  delete $conf{signals}->{$signal};
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
  if($conf{mode} eq 'internal') {
    $timers{$name}={nextRun => time+$delay, interval => $interval, callback => $p_callback};
  }else{
    $timers{$name}=AE::timer($delay,$interval,sub { &{$p_callback}(); removeTimer($name) unless($interval); });
  }
  return 1;
}

sub removeTimer {
  my $name=shift;
  if(! exists $timers{$name}) {
    slog("Unable to remove timer \"$name\" from event loop: unknown timer!",2);
    return 0;
  }
  delete $timers{$name};
  return 1;
}

sub _checkSimpleTimers {
  foreach my $timerName (keys %timers) {
    if(time >= $timers{$timerName}->{nextRun}) {
      &{$timers{$timerName}->{callback}}();
      if(exists $timers{$timerName}) {
        if($timers{$timerName}->{interval}) {
          $timers{$timerName}->{nextRun}=time+$timers{$timerName}->{interval};
        }else{
          removeTimer($timerName);
        }
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
