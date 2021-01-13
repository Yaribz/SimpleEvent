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
use Scalar::Util;
use Socket;
use Storable qw'freeze thaw';
use Tie::RefHash;
use Time::HiRes;

use SimpleLog;

my $moduleVersion='0.7';

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
my %win32Processes; tie %win32Processes, 'Tie::RefHash';
my @queuedProcesses;
my @reapedProcesses;
my %procHandles;
my ($procHdlTs,$procHdlNb)=(time,0);
my %signals;
my %sockets; tie %sockets, 'Tie::RefHash';
my $r_autoClosedHandles;
my %timers;
my $endLoopCondition;

my $osIsWindows=$^O eq 'MSWin32';

sub slog {
  $conf{sLog}->log(@_);
}

sub hasEvalError {
  if($@) {
    chomp($@);
    return 1;
  }else{
    return 0;
  }
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
    if(hasEvalError()) {
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
    ${Win32::Process::}{CLONE_SKIP}=sub{1}; # Workaround for Win32::Process not being thread-safe
  }

  if($conf{mode} eq 'AnyEvent') {
    if($osIsWindows) {
      if(exists $::{'EV::'}) {
        slog('The AnyEvent module cannot be used with the EV library on Windows system',1);
        return 0;
      }
      while(defined (my $eventModelIdx = first {$AnyEvent::models[$_][1] eq 'AnyEvent::Impl::EV'} (0..$#AnyEvent::models))) {
        splice(@AnyEvent::models,$eventModelIdx,1);
      }
    }
    my $anyEventModel=AnyEvent::detect();
    slog("Event loop initialized using model $anyEventModel (time slice: ".($conf{timeSlice}*1000).'ms)',3);
    if($osIsWindows && $anyEventModel eq 'AnyEvent::Impl::EV') {
      slog('The AnyEvent module cannot be used with the EV library on Windows system',1);
      return 0;
    }
    $endLoopCondition=AE::cv();
  }else{
    slog('Event loop initialized using internal model (time slice: '.($conf{timeSlice}*1000).'ms)',3);
    $endLoopCondition=0;
  }

  return 1;
}

sub getModel {
  return undef unless(defined $endLoopCondition);
  return 'internal' if($conf{mode} eq 'internal');
  return AnyEvent::detect();
}

sub getNbRunningProcesses { return %forkedProcesses + scalar(keys %win32Processes); }
sub getNbQueuedProcesses { return scalar @queuedProcesses; }
sub getNbSignals { return scalar %signals; }
sub getNbSockets { return scalar(keys %sockets); }
sub getNbTimers { return scalar %timers; }

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
      last if($endLoopCondition);
      _checkSimpleSockets();
      last if($endLoopCondition);
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

sub getNewProcessHandle {
  my $currentTs=time;
  if($currentTs>$procHdlTs) {
    $procHdlTs=$currentTs;
    $procHdlNb=1;
  }else{
    $procHdlNb++;
  }
  return "$procHdlTs#$procHdlNb";
}

sub forkProcess {
  if(! defined $endLoopCondition) {
    slog('Unable to fork process, event loop is uninitialized',1);
    return 0;
  }
  my ($p_processFunction,$p_endCallback,$preventQueuing,$r_keptHandles)=@_;
  if((keys %forkedProcesses) + (keys %win32Processes) >= $conf{maxChildProcesses}) {
    if($preventQueuing) {
      slog("Unable to fork process, maximum number of child process ($conf{maxChildProcesses}) is already running",1);
      return 0;
    }elsif(@queuedProcesses >= $conf{maxQueuedProcesses}) {
      slog('Unable to fork process, child process queue is full',1);
      return 0;
    }else{
      my $procHandle=getNewProcessHandle();
      slog("Queuing new fork request [$procHandle]",5);
      push(@queuedProcesses,{type => 'fork', function => $p_processFunction, callback => $p_endCallback, procHandle => $procHandle, keptHandles => $r_keptHandles});
      $procHandles{$procHandle}=['queued'];
      return wantarray() ? (-1,$procHandle) : -1;
    }
  }
  return _forkProcess($p_processFunction,$p_endCallback,undef,$r_keptHandles);
}

sub _forkProcess {
  my ($p_processFunction,$p_endCallback,$procHandle,$r_keptHandles)=@_;
  my @autoClosedHandlesForThisFork;
  {
    my @autoClosedHandles;
    foreach my $autoClosedHandle (@{$r_autoClosedHandles}) {
      if(! defined $autoClosedHandle) {
        slog('Removing destroyed handle from the auto-close on fork list',5);
        next;
      }
      push(@autoClosedHandles,$autoClosedHandle);
      Scalar::Util::weaken($autoClosedHandles[-1]);
      if(ref($autoClosedHandle) eq 'REF') {
        $autoClosedHandle=$$autoClosedHandle;
        next unless(defined $autoClosedHandle);
      }
      if(none {defined $_ && $autoClosedHandle == $_} @{$r_keptHandles}) {
        push(@autoClosedHandlesForThisFork,$autoClosedHandle);
        Scalar::Util::weaken($autoClosedHandlesForThisFork[-1]);
      }
    }
    $r_autoClosedHandles=\@autoClosedHandles;
    foreach my $registeredSocket (keys %sockets) {
      next unless(defined $registeredSocket
                  && (none {defined $_ && $registeredSocket == $_} @{$r_keptHandles}));
      push(@autoClosedHandlesForThisFork,$registeredSocket);
      Scalar::Util::weaken($autoClosedHandlesForThisFork[-1]);
    }
  }
  my $childPid = fork();
  if(! defined $childPid) {
    slog("Unable to fork process, $!",1);
    if(defined $procHandle) {
      if(defined $procHandles{$procHandle}[2]) {
        my $forkCallSocket=$procHandles{$procHandle}[2];
        unregisterSocket($forkCallSocket) if(exists $sockets{$forkCallSocket});
      }
      delete $procHandles{$procHandle};
    }
    return 0;
  }
  if($childPid == 0) {
    local $SIG{CHLD};

    # Workaround for IO::Socket::SSL misbehaving with fork()
    foreach my $r_possibleIoSocketSslHandle (@{$r_autoClosedHandles},keys %sockets) {
      my ($r_handle,$handleRefType) = ($r_possibleIoSocketSslHandle,ref($r_possibleIoSocketSslHandle));
      next if($handleRefType eq '');
      ($r_handle,$handleRefType) = ($$r_handle,ref($$r_handle)) if($handleRefType eq 'REF');
      ${*$r_handle}{_SimpleEvent_ioSocketSslForkWorkaround}=1 if($handleRefType eq 'IO::Socket::SSL');
    }
    if(my $r_stopSslFunc=delete ${IO::Socket::SSL::}{stop_SSL}) {
      ${IO::Socket::SSL::}{stop_SSL}=sub { my $self=$_[0];
                                           undef ${*$self}{_SSL_object} if(exists ${*$self}{_SimpleEvent_ioSocketSslForkWorkaround});
                                           &{$r_stopSslFunc}(@_); };
    }

    # Workaround for Windows console multiplexing STDIN between threads
    if($osIsWindows) {
      close(STDIN);
      open(STDIN,'<',devnull());
    }

    # Delete shared handles as much as possible to avoid race conditions on I/O
    map {close($_) if(Scalar::Util::openhandle($_))} @autoClosedHandlesForThisFork;

    # Remove all internal SimpleEvent data related to parent process
    @autoClosedHandlesForThisFork=();
    $r_keptHandles=undef;
    %forkedProcesses=();
    %win32Processes=();
    @queuedProcesses=();
    @reapedProcesses=();
    %procHandles=();
    %signals=();
    %sockets=();
    $r_autoClosedHandles=undef;
    %timers=();

    # Call the child process function
    &{$p_processFunction}();

    # Exit if not done yet by the child process function
    exit 0;
  }
  if(defined $procHandle) {
    $procHandles{$procHandle}[0]='forked';
    $procHandles{$procHandle}[1]=$childPid;
  }else{
    $procHandle=getNewProcessHandle();
    $procHandles{$procHandle}=['forked',$childPid];
  }
  slog("Forked new process (PID: $childPid) [$procHandle]",5);
  if($conf{mode} eq 'internal' || $osIsWindows) {
    $forkedProcesses{$childPid}=sub { delete $procHandles{$procHandle};
                                      &{$p_endCallback}(@_); };
  }else{
    $forkedProcesses{$childPid}=AE::child($childPid,
                                          sub {
                                            slog("End of forked process (PID: $childPid), calling callback",5);
                                            delete $procHandles{$procHandle};
                                            &{$p_endCallback}($_[0],$_[1] >> 8,$_[1] & 127,$_[1] & 128);
                                            delete $forkedProcesses{$childPid};
                                          } );
  }
  return wantarray() ? ($childPid,$procHandle) : $childPid;
}

sub forkCall {
  if(! defined $endLoopCondition) {
    slog('Unable to fork function call, event loop is uninitialized',1);
    return 0;
  }
  my ($p_processFunction,$p_endCallback,$preventQueuing,$r_keptHandles)=@_;
  my ($inSocket,$outSocket);
  if(! socketpair($inSocket,$outSocket,AF_UNIX,SOCK_STREAM,PF_UNSPEC)) {
    slog("Unable to fork function call, cannot create socketpair: $!",1);
    return 0;
  }
  my ($readResultStatus,$readResultData)=(-1);
  my ($forkResult,$procHandle);($forkResult,$procHandle) = forkProcess(
    sub {
      close($outSocket);
      my $callResult = eval { freeze([undef, &{$p_processFunction}()]); };
      $callResult = freeze(["$@"]) if($@);
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
          slog("Unable to read data from socketpair [$procHandle], $readResult",1);
          $p_endCallback->();
          return;
        }
        $readResultData.=$readResult;
      }
      slog("Socket pair not closed after forked call! [$procHandle]",2) unless($readResultStatus == 2);
      my $r_callResult = eval { thaw($readResultData); };
      $r_callResult//=[$@];
      $@=shift(@{$r_callResult});
      slog("Error in forked call, $@",1) if(hasEvalError());
      $p_endCallback->(@{$r_callResult});
    },
    $preventQueuing,
    $r_keptHandles );
  if(! $forkResult) {
    slog('Unable to fork function call, error in forkProcess()',1);
    close($inSocket);
    close($outSocket);
  }else{
    my $regSockRes=registerSocket($outSocket,
                                  sub {
                                    my ($readStatus,$readResult)=_readSocketNonBlocking($outSocket);
                                    $readResultStatus=$readStatus;
                                    if(! $readStatus) {
                                      unregisterSocket($outSocket);
                                      close($outSocket);
                                      slog("Unable to read data from socketpair [$procHandle], $readResult",1);
                                    }else{
                                      $readResultData.=$readResult;
                                      if($readStatus == 2) {
                                        unregisterSocket($outSocket);
                                        close($outSocket);
                                      }
                                    }
                                  });
    if($regSockRes) {
      $procHandles{$procHandle}[2]=$outSocket;
    }else{
      slog("Unable to register socket for forked function call, error in registerSocket() [$procHandle]",1);
    }
  }
  return wantarray() ? ($forkResult,$procHandle) : $forkResult;
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
      my $procHandle=getNewProcessHandle();
      slog("Queuing new Win32 process [$procHandle]",5);
      push(@queuedProcesses,{type => 'win32',
                             applicationPath => $applicationPath,
                             commandParams => $p_commandParams,
                             workingDirectory => $workingDirectory,
                             callback => $p_endCallback,
                             redirections => $p_stdRedirections,
                             procHandle => $procHandle});
      $procHandles{$procHandle}=['queued'];
      return wantarray() ? (-1,$procHandle) : -1;
    }
  }
  return _createWin32Process($applicationPath,$p_commandParams,$workingDirectory,$p_endCallback,$p_stdRedirections);
}

sub _createWin32Process {
  my ($applicationPath,$p_commandParams,$workingDirectory,$p_endCallback,$p_stdRedirections,$procHandle)=@_;
  my ($previousStdout,$previousStderr)=(undef,undef);
  my @cmdRedirs;
  if(defined $p_stdRedirections) {
    foreach my $p_redirection (@{$p_stdRedirections}) {
      if(lc($p_redirection->[0]) eq 'stdout') {
        open($previousStdout,'>&',\*STDOUT) unless(defined $previousStdout);
        open(STDOUT,$p_redirection->[1]);
      }elsif(lc($p_redirection->[0]) eq 'stderr') {
        open($previousStderr,'>&',\*STDERR) unless(defined $previousStderr);
        open(STDERR,$p_redirection->[1]);
      }elsif(lc($p_redirection->[0]) =~ /^cmdredir(out|err)$/) {
        if($p_redirection->[1] =~ /^(>>?)\s*(.+)$/) {
          my ($redirMode,$redirTarget)=($1,$2);
          $redirMode="2$redirMode" if(lc(substr($p_redirection->[0],-3)) eq 'err');
          if($redirTarget =~ /^&(1|2|STDOUT|STDERR)$/) {
            my $aliasNb={STDOUT => 1, STDERR => 2}->{$1}//$1;
            push(@cmdRedirs,"$redirMode\&$aliasNb");
          }else{
            push(@cmdRedirs,$redirMode._escapeWin32Parameter($redirTarget));
          }
        }else{
          slog("Ignoring invalid command line redirection during Win32 process creation \"$p_redirection->[1]\"",2);
        }
      }else{
        slog("Ignoring invalid redirection during Win32 process creation \"$p_redirection->[0]\"",2);
      }
    }
  }
  my $win32ProcCreateRes = Win32::Process::Create(my $win32Process,
                                                  $applicationPath,
                                                  join(' ',map {_escapeWin32Parameter($_)} ($applicationPath,@{$p_commandParams}),@cmdRedirs),
                                                  0,
                                                  0,
                                                  $workingDirectory);
  open(STDOUT,'>&',$previousStdout) if(defined $previousStdout);
  open(STDERR,'>&',$previousStderr) if(defined $previousStderr);
  if(! $win32ProcCreateRes) {
    my $errorNb=Win32::GetLastError();
    my $errorMsg=$errorNb?Win32::FormatMessage($errorNb):'unknown error';
    $errorMsg=~s/\cM?\cJ$//;
    slog("Unable to create Win32 process ($errorMsg)",1);
    delete $procHandles{$procHandle} if(defined $procHandle);
    return 0;
  }
  $procHandle//=getNewProcessHandle();
  slog('Created new Win32 process (PID: '.$win32Process->GetProcessID().") [$procHandle]",5);
  $procHandles{$procHandle}=['win32',$win32Process];
  $win32Processes{$win32Process}=sub { delete $procHandles{$procHandle};
                                       &{$p_endCallback}(@_); };
  return wantarray() ? ($win32Process,$procHandle) : $win32Process;
}

sub removeProcessCallback {
  my $procHandle=shift;
  if(! defined $procHandle) {
    slog('Unable to remove process callback: undefined process handle value',2);
    return 0;
  }
  if(! exists $procHandles{$procHandle}) {
    slog("Unable to remove process callback: unknown process handle ($procHandle)",2);
    return 0;
  }
  if($procHandles{$procHandle}[0] eq 'queued') {
    my $queueIdx = first {$procHandle eq $queuedProcesses[$_]{procHandle}} (0..$#queuedProcesses);
    if(! defined $queueIdx) {
      slog("Unable to remove callback for queued process: inconsistent process handle ($procHandle)",0);
      return 0;
    }
    splice(@queuedProcesses,$queueIdx,1);
    if(defined $procHandles{$procHandle}[2]) {
      my $forkCallSocket=$procHandles{$procHandle}[2];
      unregisterSocket($forkCallSocket) if(exists $sockets{$forkCallSocket});
    }
    delete $procHandles{$procHandle};
    slog("Removed queued process [$procHandle]",5);
    return 1;
  }elsif($procHandles{$procHandle}[0] eq 'forked') {
    my ($pid,$forkCallSocket)=($procHandles{$procHandle}[1],$procHandles{$procHandle}[2]);
    if(exists $forkedProcesses{$pid} && defined $forkedProcesses{$pid}) {
      if($conf{mode} eq 'internal' || $osIsWindows) {
        $forkedProcesses{$pid}=undef;
      }else{
        $forkedProcesses{$pid}=AE::child($pid, sub { slog("End of forked process (PID: $pid), no callback",5);
                                                     delete $forkedProcesses{$pid}; } );
      }
      unregisterSocket($forkCallSocket) if(defined $forkCallSocket && exists $sockets{$forkCallSocket});
      delete $procHandles{$procHandle};
      slog("Removed forked process callback for PID $pid [$procHandle]",5);
      return 1;
    }
    slog("Unable to remove forked process callback for PID $pid : inconsistent process handle ($procHandle)",0);
    return 0;
  }elsif($procHandles{$procHandle}[0] eq 'win32') {
    my $win32Process=$procHandles{$procHandle}[1];
    if(exists $win32Processes{$win32Process}) {
      $win32Processes{$win32Process}=undef;
      delete $procHandles{$procHandle};
      slog('Removed Win32 process callback for PID '.$win32Process->GetProcessID()." [$procHandle]",5);
      return 1;
    }
    slog('Unable to remove Win32 process callback for PID '.$win32Process->GetProcessID()." : inconsistent process handle ($procHandle)",0);
    return 0;
  }else{
    slog("Unable to remove process callback: invalid process handle ($procHandle)",0);
    return 0;
  }
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
    _handleReapedProcesses();
    _reapAndHandleWin32Processes();
  }elsif($conf{mode} eq 'internal') {
    _handleReapedProcesses();
  }
  _checkQueuedProcesses();
}

sub _reapForkedProcesses {
  while(my $pid = waitpid(-1,WNOHANG)) {
    last if($pid == -1);
    push(@reapedProcesses,[$pid,$?]);
  }
}

sub _handleReapedProcesses {
  while(my $r_reapedProcess=shift(@reapedProcesses)) {
    my ($pid,$exitCode)=@{$r_reapedProcess};
    if(exists $forkedProcesses{$pid}) {
      if(defined $forkedProcesses{$pid}) {
        slog("End of forked process (PID: $pid), calling callback",5);
        &{$forkedProcesses{$pid}}($pid,$exitCode >> 8,$exitCode & 127,$exitCode & 128);
      }else{
        slog("End of forked process (PID: $pid), no callback",5);
      }
      delete $forkedProcesses{$pid};
    }else{
      slog("End of forked process (PID: $pid) (unknown child process)",5);
    }
  }
}

sub _reapAndHandleWin32Processes {
  foreach my $win32Process (keys %win32Processes) {
    $win32Process->GetExitCode(my $exitCode);
    if($exitCode != Win32::Process::STILL_ACTIVE()) {
      my $pid=$win32Process->GetProcessID();
      if(defined $win32Processes{$win32Process}) {
        slog("End of Win32 process (PID: $pid), calling callback",5);
        &{$win32Processes{$win32Process}}($pid,$exitCode);
      }else{
        slog("End of Win32 process (PID: $pid), no callback",5);
      }
      delete $win32Processes{$win32Process};
    }
  }
}

sub _checkQueuedProcesses {
  while(@queuedProcesses && $conf{maxChildProcesses} > (keys %forkedProcesses) + (keys %win32Processes)) {
    my $p_queuedProcess=shift(@queuedProcesses);
    if($p_queuedProcess->{type} eq 'fork') {
      slog("Unqueuing new fork request [$p_queuedProcess->{procHandle}]",5);
      _forkProcess($p_queuedProcess->{function},$p_queuedProcess->{callback},$p_queuedProcess->{procHandle},$p_queuedProcess->{keptHandles});
    }else{
      slog("Unqueuing new Win32 process [$p_queuedProcess->{procHandle}]",5);
      _createWin32Process($p_queuedProcess->{applicationPath},$p_queuedProcess->{commandParams},$p_queuedProcess->{workingDirectory},$p_queuedProcess->{callback},$p_queuedProcess->{redirections},$p_queuedProcess->{procHandle});
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

sub addAutoCloseOnFork {
  my $rc=1;
  my $nbAdded=0;
  foreach my $hdl (@_) {
    my $hdlAddr=Scalar::Util::refaddr($hdl);
    if(! defined $hdlAddr) {
      slog('Unable to add handle to the auto-close on fork list: not a reference!',1);
      $rc=0;
    }elsif(any {defined $_ && Scalar::Util::refaddr($_) == $hdlAddr} @{$r_autoClosedHandles}) {
      slog('Unable to add handle to the auto-close on fork list: handle is already added',2);
      $rc=2 if($rc == 1);
    }else{
      push(@{$r_autoClosedHandles},$hdl);
      Scalar::Util::weaken($r_autoClosedHandles->[-1]);
      $nbAdded++;
    }
  }
  slog("Added $nbAdded handle".($nbAdded>1?'s':'').' to the auto-close on fork list',5);
  return $rc;
}

sub removeAutoCloseOnFork {
  my $rc=1;
  my $nbRemoved=0;
  foreach my $hdl (@_) {
    my $hdlAddr=Scalar::Util::refaddr($hdl);
    if(! defined $hdlAddr) {
      slog('Unable to remove handle from the auto-close on fork list: not a reference!',1);
      $rc=0;
    }elsif(defined (my $idx = first {my $r_ach=$r_autoClosedHandles->[$_];
                                     defined $r_ach && Scalar::Util::refaddr($r_ach) == $hdlAddr} (0..$#{$r_autoClosedHandles}))) {
      splice(@{$r_autoClosedHandles},$idx,1);
      $nbRemoved++;
    }else{
      slog('Unable to remove handle from the auto-close on fork list: handle is not in current list',2);
      $rc=2 if($rc == 1);
    }
  }
  slog("Removed $nbRemoved handle".($nbRemoved>1?'s':'').' from the auto-close on fork list',5);
  return $rc;
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
  if(@reapedProcesses) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "reapedProcesses:\n";
    print Dumper(\@reapedProcesses);
  }
  if(%procHandles) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "procHandles:\n";
    print Dumper(\%procHandles);
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
