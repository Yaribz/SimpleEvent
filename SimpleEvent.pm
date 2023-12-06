# A Perl module implementing a basic asynchronous event functionality compatible
# with AnyEvent
#
# Copyright (C) 2008-2023  Yann Riou <yaribzh@gmail.com>
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

use Fcntl 'LOCK_NB';
use File::Spec::Functions qw'devnull';
use IO::Select;
use List::Util qw'first sum0';
use POSIX qw':sys_wait_h';
use Scalar::Util;
use Socket;
use Storable qw'freeze thaw';
use Tie::RefHash;
use Time::HiRes;

use SimpleLog;

my $moduleVersion='0.16';

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
my %fileLockRequests;
my %forkedProcessCallbacks;
my $endLoopCondition;
my %proxyPackages;

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
    eval 'use Win32';
    eval 'use Win32::Process';
    eval 'use Win32API::File';
    ${Win32::Process::}{CLONE_SKIP}=sub{1}; # Workaround for Win32::Process not being thread-safe
  }

  my $eventModel;
  if($conf{mode} eq 'AnyEvent') {
    $eventModel=AnyEvent::detect();
    $endLoopCondition=AE::cv();
  }else{
    $eventModel='internal';
    $endLoopCondition=0;
  }
  slog("Event loop initialized using $eventModel model (time slice: ".($conf{timeSlice}*1000).'ms)',3);

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
sub getNbFileLockRequests { return scalar %fileLockRequests }
sub getNbForkedProcessCallbacks { return scalar %forkedProcessCallbacks }

sub startLoop {
  my $p_cleanUpFunction=shift;
  if(! defined $endLoopCondition) {
    slog('Unable to start main loop, event loop is uninitialized',1);
    return 0;
  }
  slog('Starting event loop...',3);
  if($conf{mode} eq 'AnyEvent') {
    my $processAndLockManagementTimer=AE::timer(0,$conf{timeSlice},sub {_manageProcesses();_checkFileLockRequests();});
    $endLoopCondition->recv();
  }else{
    while(! $endLoopCondition) {
      _checkSimpleTimers();
      last if($endLoopCondition);
      _checkFileLockRequests();
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
    my @remainingFileLockRequests=keys %fileLockRequests;
    my @remainingForkedProcessCallbacks=keys %forkedProcessCallbacks;
    &{$p_cleanUpFunction}(\@remainingPids,\@remainingWin32Processes,\@queuedProcesses,\@remainingSignals,\@remainingSockets,\@remainingTimers,\@remainingFileLockRequests,\@remainingForkedProcessCallbacks);
  }
  my ($nbRemainingForkedProcesses,$nbRemainingWin32Processes,$nbQueuedProcesses)=(scalar keys %forkedProcesses,scalar keys %win32Processes,getNbQueuedProcesses());
  my ($nbRemainingSignals,$nbRemainingSockets,$nbRemainingTimers,$nbRemainingFileLockRequests)=(getNbSignals(),getNbSockets(),getNbTimers(),getNbFileLockRequests());
  my $nbForkedProcessCallbacks=getNbForkedProcessCallbacks();
  slog("$nbRemainingForkedProcesses forked process".($nbRemainingForkedProcesses>1?'es are':' is').' still running',2) if($nbRemainingForkedProcesses);
  slog("$nbRemainingWin32Processes Win32 process".($nbRemainingWin32Processes>1?'es are':' is').' still running',2) if($nbRemainingWin32Processes);
  slog("$nbQueuedProcesses process".($nbQueuedProcesses>1?'es are':' is').' still queued',2) if($nbQueuedProcesses);
  slog("$nbRemainingSignals signal handler".($nbRemainingSignals>1?'s are':' is').' still registered',2) if($nbRemainingSignals);
  slog("$nbRemainingSockets socket".($nbRemainingSockets>1?'s are':' is').' still registered',2) if($nbRemainingSockets);
  slog("$nbRemainingTimers timer".($nbRemainingTimers>1?'s are':' is').' still registered',2) if($nbRemainingTimers);
  slog("$nbRemainingFileLockRequests file lock request".($nbRemainingFileLockRequests>1?'s are':' is').' still registered',2) if($nbRemainingFileLockRequests);
  slog("$nbForkedProcessCallbacks forked process callback".($nbForkedProcessCallbacks>1?'s are':' is').' still registered',2) if($nbForkedProcessCallbacks);
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
  if($osIsWindows) {
    my $codeRefType=ref($p_processFunction);
    if($codeRefType ne 'CODE') {
      my $reason=$codeRefType eq '' ? 'not a code reference' : "unsupported code reference type: $codeRefType";
      slog('Unable to fork function call, '.$reason,1);
      return 0;
    }
  }
  my $originPackage=getOriginPackage();
  $p_endCallback=encapsulateCallback($p_endCallback,$originPackage) unless(ref $p_endCallback eq 'CODE');
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
      push(@queuedProcesses,{type => 'fork', function => $p_processFunction, callback => $p_endCallback, procHandle => $procHandle, keptHandles => $r_keptHandles, originPackage => $originPackage});
      $procHandles{$procHandle}=['queued'];
      return wantarray() ? (-1,$procHandle) : -1;
    }
  }
  return _forkProcess($p_processFunction,$p_endCallback,undef,$r_keptHandles,$originPackage);
}

my ($inlinePythonWorkaroundDone,$anyeventTlsWorkaroundDone,$libEvWorkaroundDone);
sub _forkProcess {
  my ($p_processFunction,$p_endCallback,$procHandle,$r_keptHandles,$originPackage)=@_;
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
      Scalar::Util::weaken($autoClosedHandlesForThisFork[-1]) if(ref $registeredSocket);
    }
  }

  # Workaround for Inline::Python not being thread safe
  if(! $inlinePythonWorkaroundDone && defined $Inline::Python::VERSION) {
    ${Inline::Python::Object::}{CLONE_SKIP}=sub {1};
    ${Inline::Python::Object::Data::}{CLONE_SKIP}=sub {1};
    ${Inline::Python::Function::}{CLONE_SKIP}=sub {1};
    ${Inline::Python::Boolean::}{CLONE_SKIP}=sub {1};
    $inlinePythonWorkaroundDone=1;
  }

  # Workaround for AnyEvent::TLS not being thread safe (AnyEvent::TLS::_put_session($$) and AnyEvent::TLS::DESTROY())
  if(! $anyeventTlsWorkaroundDone && defined $AnyEvent::TLS::VERSION) {
    ${AnyEvent::TLS::}{CLONE_SKIP}=sub {1};
    $anyeventTlsWorkaroundDone=1;
  }
  
  # Workaround for EV not being thread safe
  if(! $libEvWorkaroundDone && defined $EV::VERSION) {
    map {${EV::}{$_}{CLONE_SKIP}=sub {1} if(defined *{${EV::}{$_}}{HASH})} (keys %EV::);
    $libEvWorkaroundDone=1;
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

    map {$forkedProcessCallbacks{$_}[0]->()} (sort keys %forkedProcessCallbacks);
    
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
    foreach my $handleToClose (@autoClosedHandlesForThisFork) {
      next unless(defined $handleToClose);
      if(Scalar::Util::openhandle($handleToClose)) {
        close($handleToClose);
      }elsif(! $osIsWindows && ref($handleToClose) eq '' && $handleToClose =~ /^\d+$/) {
        POSIX::close($handleToClose);
      }
    }
    map {POSIX::close($sockets{$_}[2]) if(defined $sockets{$_}[2])} (keys %sockets);

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
    %fileLockRequests=();
    %forkedProcessCallbacks=();

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
    $forkedProcesses{$childPid}=[sub { delete $procHandles{$procHandle};
                                             &{$p_endCallback}(@_); },
                                 $originPackage];
  }else{
    $forkedProcesses{$childPid}=[AE::child($childPid,
                                          sub {
                                            slog("End of forked process (PID: $childPid), calling callback",5);
                                            delete $procHandles{$procHandle};
                                            &{$p_endCallback}($_[0],$_[1] >> 8,$_[1] & 127,$_[1] & 128);
                                            delete $forkedProcesses{$childPid};
                                           } ),
                                 $originPackage];
  }
  return wantarray() ? ($childPid,$procHandle) : $childPid;
}

sub forkCall {
  if(! defined $endLoopCondition) {
    slog('Unable to fork function call, event loop is uninitialized',1);
    return 0;
  }
  my ($p_processFunction,$p_endCallback,$preventQueuing,$r_keptHandles)=@_;
  if($osIsWindows) {
    my $codeRefType=ref($p_processFunction);
    if($codeRefType ne 'CODE') {
      my $reason=$codeRefType eq '' ? 'not a code reference' : "unsupported code reference type: $codeRefType";
      slog('Unable to fork function call, '.$reason,1);
      return 0;
    }
  }
  $p_endCallback=encapsulateCallback($p_endCallback) unless(ref $p_endCallback eq 'CODE');
  my ($inSocket,$outSocket);
  if(! socketpair($inSocket,$outSocket,AF_UNIX,SOCK_STREAM,PF_UNSPEC)) {
    slog("Unable to fork function call, cannot create socketpair: $!",1);
    return 0;
  }
  if($osIsWindows) {
    win32HdlDisableInheritance($inSocket);
    win32HdlDisableInheritance($outSocket);
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
  my $readSocketSelect=IO::Select->new($socket);
  while(my @canRead=$readSocketSelect->can_read(0)) {
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
  my $originPackage=getOriginPackage();
  $p_endCallback=encapsulateCallback($p_endCallback,$originPackage) unless(ref $p_endCallback eq 'CODE');
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
                             procHandle => $procHandle,
                             originPackage => $originPackage});
      $procHandles{$procHandle}=['queued'];
      return wantarray() ? (-1,$procHandle) : -1;
    }
  }
  return _createWin32Process($applicationPath,$p_commandParams,$workingDirectory,$p_endCallback,$p_stdRedirections,undef,$originPackage);
}

sub _createWin32Process {
  my ($applicationPath,$p_commandParams,$workingDirectory,$p_endCallback,$p_stdRedirections,$procHandle,$originPackage)=@_;
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
  $win32Processes{$win32Process}=[sub { delete $procHandles{$procHandle};
                                        &{$p_endCallback}(@_); },
                                  $originPackage];
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
        $forkedProcesses{$pid}=[AE::child($pid, sub { slog("End of forked process (PID: $pid), no callback",5);
                                                      delete $forkedProcesses{$pid}; } ),
                                __PACKAGE__];
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
    if(exists $win32Processes{$win32Process} && defined $win32Processes{$win32Process}) {
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
        &{$forkedProcesses{$pid}[0]}($pid,$exitCode >> 8,$exitCode & 127,$exitCode & 128);
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
        &{$win32Processes{$win32Process}[0]}($pid,$exitCode);
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
      _forkProcess($p_queuedProcess->{function},$p_queuedProcess->{callback},$p_queuedProcess->{procHandle},$p_queuedProcess->{keptHandles},$p_queuedProcess->{originPackage});
    }else{
      slog("Unqueuing new Win32 process [$p_queuedProcess->{procHandle}]",5);
      _createWin32Process($p_queuedProcess->{applicationPath},$p_queuedProcess->{commandParams},$p_queuedProcess->{workingDirectory},$p_queuedProcess->{callback},$p_queuedProcess->{redirections},$p_queuedProcess->{procHandle},$p_queuedProcess->{originPackage});
    }
  }
}

sub registerSocket {
  if(! defined $endLoopCondition) {
    slog('Unable to register socket, event loop is uninitialized',1);
    return 0;
  }
  my ($socket,$p_readCallback)=@_;
  my $socketFileno;
  my $socketBaseRefType=Scalar::Util::reftype($socket);
  if(defined $socketBaseRefType) {
    if($socketBaseRefType ne 'GLOB') {
      if($osIsWindows || ! eval { $socketFileno=$socket->fileno() }) {
        slog('Unable to register socket, invalid socket type: '.ref($socket),1);
        return 0;
      }
    }
  }else{
    if($socket =~ /^\d+$/) {
      if($osIsWindows) {
        slog('Unable to register socket: registering socket from file descriptor not supported on Windows',1);
        return 0;
      }
      $socketFileno=$socket;
    }else{
      slog("Unable to register socket, unknown socket value: $socket",1);
      return 0;
    }
  }
  if(defined $socketFileno && $socketFileno != -1) {
    if($conf{mode} eq 'internal') {
      if(my $handleFromFd=IO::Handle->new_from_fd($socketFileno,'+<')) {
        $socket=$handleFromFd;
      }else{
        slog("Unable to register socket: $!",1);
        return 0;
      }
    }else{
      $socket=$socketFileno;
    }
  }
  if(exists $sockets{$socket}) {
    slog('Unable to register socket in event loop: this socket has already been registered!',2);
    return 0;
  }
  my $originPackage=getOriginPackage();
  $p_readCallback=encapsulateCallback($p_readCallback,$originPackage) unless(ref $p_readCallback eq 'CODE');
  if($conf{mode} eq 'internal') {
    $sockets{$socket}=[$p_readCallback,$originPackage,$socketFileno];
  }else{
    $sockets{$socket}=[AE::io($socket,0,sub { &{$p_readCallback}($socket); }),$originPackage];
  }
  slog('New socket registered',5);
  win32HdlDisableInheritance($socket) if($osIsWindows);
  return defined $socketFileno ? $socket : 1;
}

sub unregisterSocket {
  my $socket=shift;
  if(! exists $sockets{$socket}) {
    if(! $osIsWindows) {
      my $socketFileno;
      if(ref $socket eq '') {
        $socketFileno=$socket if($socket =~ /^\d+$/);
      }else{
        eval { $socketFileno=$socket->fileno() };
      }
      if(defined $socketFileno) {
        my @socketsToRemove=grep {defined $sockets{$_}[2] && $sockets{$_}[2] == $socketFileno} (keys %sockets);
        if(@socketsToRemove) {
          delete @sockets{@socketsToRemove};
          my $nbSocketsRemoved=scalar @socketsToRemove;
          if($nbSocketsRemoved < 2) {
            slog('Socket unregistered',5);
          }else{
            slog("$nbSocketsRemoved sockets unregistered",5);
          }
          return $nbSocketsRemoved;
        }
      }
    }
    slog('Unable to unregister socket in event loop: unknown socket!',2);
    return 0;
  }
  delete $sockets{$socket};
  slog('Socket unregistered',5);
  return 1;
}

sub socketGracefulShutdown {
  my ($socket,$timeout,$r_callback)=@_;
  $timeout//=5;

  if(! Scalar::Util::openhandle($socket)) {
    slog('Unable to perform graceful shutdown on socket: not an open handle',1);
    return 0;
  }
  
  if(exists $sockets{$socket}) {
    slog('Unable to perform graceful shutdown on socket: socket is already registered',1);
    return 0;
  }
  
  if(defined $r_callback && ! defined $endLoopCondition) {
    slog('Unable to perform asynchronous graceful shutdown on socket: event loop is uninitialized',1);
    return 0;
  }
  
  my $res=shutdown($socket,1);
  if(! defined $res) {
    slog('Unable to perform graceful shutdown on socket: not a valid handle',1);
    return 0;
  }elsif(! $res) {
    slog("Unable to perform graceful shutdown on socket: failed to shutdown socket ($!)",1);
    return 0;
  }
  
  if(defined $r_callback) {
    $r_callback=encapsulateCallback($r_callback) unless(ref $r_callback eq 'CODE');
    my $timerName='socketGracefulShutdownTimeout#'.Scalar::Util::refaddr($socket);
    addTimer($timerName,
             $timeout,
             0,
             sub {
               unregisterSocket($socket);
               close($socket);
               $r_callback->(2,'timeout during graceful socket shutdown')
             });
    registerSocket($socket,
                   sub {
                     my $readLength=$socket->sysread(my $ignored,4096);
                     return if($readLength);
                     my ($rc,$warning)=defined $readLength?(1):(2,$!);
                     unregisterSocket($socket);
                     removeTimer($timerName);
                     close($socket);
                     $r_callback->($rc,$warning);
                   });
    return 1;
  }else{
    my $timeoutTime=Time::HiRes::time+$timeout;
    my $nbLingerPackets=0;
    my $shutdownSel=IO::Select->new($socket);
    while($nbLingerPackets<10) {
      my $maxWait=$timeoutTime-Time::HiRes::time;
      $maxWait=0 if($maxWait < 0);
      last unless($shutdownSel->can_read($maxWait));
      my $readLength=$socket->sysread(my $ignored,4096);
      if($readLength) {
        $nbLingerPackets++ unless($maxWait);
        next;
      }
      my ($rc,$warning)=defined $readLength?(1):(2,$!);
      close($socket);
      return wantarray() ? ($rc,$warning) : $rc;
    }
    close($socket);
    return wantarray() ? (2,'timeout during graceful socket shutdown'):2;
  }
  
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

sub win32HdlDisableInheritance {
  my $winHdl=Win32API::File::GetOsFHandle(shift);
  if($winHdl == Win32API::File::INVALID_HANDLE_VALUE()) {
    slog('Unable to retrieve Windows handle to disable inheritance: '.$^E,2);
    return 0;
  }
  if(Win32API::File::SetHandleInformation($winHdl,Win32API::File::HANDLE_FLAG_INHERIT(),0)) {
    return 1;
  }else{
    slog('Unable to disable Windows handle inheritance: '.$^E,2);
    return 0;
  }
}

sub _checkSimpleSockets {
  if(%sockets) {
    my @pendingSockets=IO::Select->new(keys %sockets)->can_read($conf{timeSlice});
    foreach my $pendingSock (@pendingSockets) {
      next unless(exists $sockets{$pendingSock}); # sockets can be unregistered by forked process exit callbacks at any time (linux), or by any other socket callback
      &{$sockets{$pendingSock}[0]}($pendingSock);
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
  my $originPackage=getOriginPackage();
  $p_signalCallback=encapsulateCallback($p_signalCallback,$originPackage) unless(ref $p_signalCallback eq 'CODE');
  if($conf{mode} eq 'internal') {
    $SIG{$signal}=$p_signalCallback;
    $signals{$signal}=[$p_signalCallback,$originPackage];
  }else{
    $signals{$signal}=[AE::signal($signal,$p_signalCallback),$originPackage];
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
  my $originPackage=getOriginPackage();
  $p_callback=encapsulateCallback($p_callback,$originPackage) unless(ref $p_callback eq 'CODE');
  if($conf{mode} eq 'internal') {
    $timers{$name}=[{nextRun => Time::HiRes::time+$delay, interval => $interval, callback => $p_callback},$originPackage];
  }else{
    $timers{$name}=[AE::timer($delay,$interval,sub { removeTimer($name) unless($interval); &{$p_callback}(); }),$originPackage];
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
    if(Time::HiRes::time >= $timers{$timerName}[0]{nextRun}) {
      if($timers{$timerName}[0]{interval}) {
        $timers{$timerName}[0]{nextRun}=Time::HiRes::time+$timers{$timerName}[0]{interval};
        &{$timers{$timerName}[0]{callback}}();
      }else{
        my $p_timerCallback=$timers{$timerName}[0]{callback};
        removeTimer($timerName);
        &{$p_timerCallback}();
      }
    }
  }
}

sub addForkedProcessCallback {
  my ($name,$r_callback)=@_;
  if(exists $forkedProcessCallbacks{$name}) {
    slog("Unable to add forked process callback \"$name\": duplicate forked process callback name!",2);
    return 0;
  }
  slog("Adding forked process callback \"$name\"",5);
  my $originPackage=getOriginPackage();
  $r_callback=encapsulateCallback($r_callback,$originPackage) unless(ref $r_callback eq 'CODE');
  $forkedProcessCallbacks{$name}=[$r_callback,$originPackage];
  return 1;
}

sub removeForkedProcessCallback {
  my $name=shift;
  my $r_fpcb=delete $forkedProcessCallbacks{$name};
  if(! defined $r_fpcb) {
    slog("Unable to remove forked process callback \"$name\": unknown forked process callback name!",2);
    return 0;
  }
  slog("Removing forked process callback \"$name\"",5);
  return 1;
}

sub requestFileLock {
  my ($name,$file,$mode,$r_callback,$timeout,$r_timeoutCallback)=@_;
  if(! defined $endLoopCondition) {
    slog("Unable to process file lock request \"$name\", event loop is uninitialized",1);
    return 0;
  }
  if(exists $fileLockRequests{$name}) {
    slog("Unable to process file lock request \"$name\": this file lock request is already in progress!",2);
    return 0;
  }
  my $originPackage=getOriginPackage();
  $r_callback=encapsulateCallback($r_callback,$originPackage) unless(ref $r_callback eq 'CODE');
  if(open(my $lockHdl,'>',$file)) {
    if(flock($lockHdl,$mode | LOCK_NB)) {
      win32HdlDisableInheritance($lockHdl) if($osIsWindows);
      slog("File lock request \"$name\" processed directly (file:$file, mode:$mode".($timeout?", timeout:$timeout":'').')',5);
      $r_callback->($lockHdl);
      return 1;
    }else{
      close($lockHdl);
    }
  }else{
    slog("Unable to process file lock request \"$name\": could not open file \"$file\" for writing",2);
    return 0;
  }
  my $timeoutTimer;
  if($timeout) {
    $timeoutTimer='fileLockRequestTimeout('.$name.')';
    $r_timeoutCallback=encapsulateCallback($r_timeoutCallback,$originPackage) if(defined $r_timeoutCallback && ref $r_timeoutCallback ne 'CODE');
    addTimer($timeoutTimer,
             $timeout,
             0,
             sub {
               delete $fileLockRequests{$name};
               slog("Removing file lock request \"$name\" (timeout)",5);
               $r_timeoutCallback->($name) if(defined $r_timeoutCallback);
             });
  }
  slog("File lock request \"$name\" queued for retry (file:$file, mode:$mode".($timeout?", timeout:$timeout":'').')',5);
  $fileLockRequests{$name}=[{file => $file,
                             mode => $mode,
                             callback => $r_callback,
                             timeoutTimer => $timeoutTimer},
                            $originPackage];
  return 1;
}

sub removeFileLockRequest {
  my $name=shift;
  my $r_req=delete $fileLockRequests{$name};
  if(! defined $r_req) {
    slog("Unable to remove file lock request \"$name\": unknown file lock request!",2);
    return 0;
  }
  slog("Removing file lock request \"$name\"",5);
  my $timeoutTimer=$r_req->[0]{timeoutTimer};
  removeTimer($timeoutTimer) if(defined $timeoutTimer && exists $timers{$timeoutTimer});
  return 1;
}

sub _checkFileLockRequests {
  foreach my $requestName (keys %fileLockRequests) {
    my $r_req=$fileLockRequests{$requestName};
    next unless(defined $r_req); # file lock requests can be removed by forked process exit callbacks at any time (linux), or by any other file lock request callback
    if(open(my $lockHdl,'>',$r_req->[0]{file})) {
      if(flock($lockHdl,$r_req->[0]{mode} | LOCK_NB)) {
        win32HdlDisableInheritance($lockHdl) if($osIsWindows);
        removeFileLockRequest($requestName);
        $r_req->[0]{callback}->($lockHdl,$requestName);
        next;
      }else{
        close($lockHdl);
      }
    }else{
      slog("Unable to process file lock request \"$requestName\" (retry): could not open file \"$r_req->[0]{file}\" for writing",5);
    }
  }
}

sub addProxyPackage {
  my $packageName=shift;
  if(exists $proxyPackages{$packageName}) {
    slog("Unable to add proxy package \"$packageName\", this package is already declared as proxy package",2);
    return 0;
  }else{
    $proxyPackages{$packageName}=1;
    return 1;
  }
}

sub removeProxyPackage {
  my $packageName=shift;
  if(exists $proxyPackages{$packageName}) {
    delete $proxyPackages{$packageName};
    return 1;
  }else{
    slog("Unable to remove proxy package \"$packageName\", this package is not declared as proxy package",2);
    return 0;
  }
}

my %INTERNAL_CALLBACKS=(forkProcess => { createDetachedProcess => 1 },
                        registerSocket => { forkCall => 1 },
                        addTimer => { requestFileLock => 1} );
my $INTERNAL_PACKAGE_PREFIX=__PACKAGE__.'::';
my $INTERNAL_PACKAGE_PREFIX_LENGTH=length($INTERNAL_PACKAGE_PREFIX);
sub isInternalCallback {
  my ($calledFunc,$callerFunc)=@_;
  return 0 unless(defined $calledFunc && defined $callerFunc);
  foreach my $func ($calledFunc,$callerFunc) {
    return 0 unless(rindex($func,$INTERNAL_PACKAGE_PREFIX,0) == 0);
    substr($func,0,$INTERNAL_PACKAGE_PREFIX_LENGTH,'');
  }
  return 1 if(exists $INTERNAL_CALLBACKS{$calledFunc} && exists $INTERNAL_CALLBACKS{$calledFunc}{$callerFunc});
  return 0;
}

sub getOriginPackage {
  my $skippedNestLevel=shift//0;
  return __PACKAGE__ if(isInternalCallback((caller(1+$skippedNestLevel))[3],(caller(2+$skippedNestLevel))[3]));
  my $nestLevel=1+$skippedNestLevel;
  while(my $callerPackage=caller($nestLevel++)) {
    next if($callerPackage eq __PACKAGE__ || exists $proxyPackages{$callerPackage} || (any {rindex($callerPackage,$_.'::',0)==0} (keys %proxyPackages)));
    return $callerPackage;
  }
  return '_UNKNWON_';
}

sub encapsulateCallback {
  my ($r_cb,$originPackage)=@_;
  $originPackage//=getOriginPackage(1);
  return eval("package $originPackage; sub { \&{\$r_cb}(\@_); }");
}

sub removeAllCallbacks {
  my ($callbackType,$originPackage)=@_;
  $originPackage//=getOriginPackage();
  my @knownCallbackTypes=('processes','signals','sockets','timers','fileLockRequests','forkedProcessCallbacks');
  if(defined $callbackType && (none {$callbackType eq $_} @knownCallbackTypes)) {
    slog("Invalid call to removeAllCallbacks function: unknown callback type \"$callbackType\"",1);
    return undef;
  }
  my @callbackTypes=defined($callbackType)?($callbackType):@knownCallbackTypes;
  my $nbRemovedCallbacks=0;
  foreach my $type (@callbackTypes) {
    if($type eq 'processes') {
      my @procHandlesToRemove=map {$_->{procHandle}} (grep {$_->{originPackage} eq $originPackage} @queuedProcesses);
      foreach my $procHandle (keys %procHandles) {
        if($procHandles{$procHandle}[0] eq 'forked') {
          my $pid=$procHandles{$procHandle}[1];
          push(@procHandlesToRemove,$procHandle) if(exists $forkedProcesses{$pid} && defined $forkedProcesses{$pid} && $forkedProcesses{$pid}[1] eq $originPackage);
        }elsif($procHandles{$procHandle}[0] eq 'win32') {
          my $win32Process=$procHandles{$procHandle}[1];
          push(@procHandlesToRemove,$procHandle) if(exists $win32Processes{$win32Process} && defined $win32Processes{$win32Process} && $win32Processes{$win32Process}[1] eq $originPackage);
        }
      }
      my @removeResults=map {removeProcessCallback($_)} @procHandlesToRemove;
      $nbRemovedCallbacks+=sum0(@removeResults);
    }elsif($type eq 'signals') {
      my @signalsToRemove=grep {$signals{$_}[1] eq $originPackage} (keys %signals);
      my @unregisterResults=map {unregisterSignal($_)} @signalsToRemove;
      $nbRemovedCallbacks+=sum0(@unregisterResults);
    }elsif($type eq 'sockets') {
      my @socketsToRemove=grep {$sockets{$_}[1] eq $originPackage} (keys %sockets);
      my @unregisterResults=map {unregisterSocket($_)} @socketsToRemove;
      $nbRemovedCallbacks+=sum0(@unregisterResults);
    }elsif($type eq 'timers') {
      my @timersToRemove=grep {$timers{$_}[1] eq $originPackage} (keys %timers);
      my @removeResults=map {removeTimer($_)} @timersToRemove;
      $nbRemovedCallbacks+=sum0(@removeResults);
    }elsif($type eq 'fileLockRequests') {
      my @fileLockRequestsToRemove=grep {$fileLockRequests{$_}[1] eq $originPackage} (keys %fileLockRequests);
      my @removeResults=map {removeFileLockRequest($_)} @fileLockRequestsToRemove;
      $nbRemovedCallbacks+=sum0(@removeResults);
    }elsif($type eq 'forkedProcessCallbacks') {
      my @forkedProcessCallbacksToRemove=grep {$forkedProcessCallbacks{$_}[1] eq $originPackage} (keys %forkedProcessCallbacks);
      my @removeResults=map {removeForkedProcessCallback($_)} @forkedProcessCallbacksToRemove;
      $nbRemovedCallbacks+=sum0(@removeResults);
    }
  }
  return $nbRemovedCallbacks;
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
  if(%fileLockRequests) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "fileLockRequests:\n";
    print Dumper(\%fileLockRequests);
  }
  if(%forkedProcessCallbacks) {
    print +('-' x 40)."\n" if($sep);
    $sep=1;
    print "forkedProcessCallbacks:\n";
    print Dumper(\%forkedProcessCallbacks);
  }
  print +('#' x 79)."\n";
}

1;
