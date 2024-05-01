/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Error
import Lake.Util.EStateT
import Lean.Data.Json
import Lean.Message

open Lean

namespace Lake

inductive Verbosity
| quiet
| normal
| verbose
deriving Repr, DecidableEq, Ord

instance : LT Verbosity := ltOfOrd
instance : LE Verbosity := leOfOrd
instance : Min Verbosity := minOfLe
instance : Max Verbosity := maxOfLe

instance : Inhabited Verbosity := ⟨.normal⟩

inductive LogLevel
| trace
| info
| warning
| error
deriving Inhabited, Repr, DecidableEq, Ord, ToJson, FromJson

instance : LT LogLevel := ltOfOrd
instance : LE LogLevel := leOfOrd
instance : Min LogLevel := minOfLe
instance : Max LogLevel := maxOfLe

protected def LogLevel.toString : LogLevel → String
| .trace => "trace"
| .info => "info"
| .warning => "warning"
| .error => "error"

protected def LogLevel.ofMessageSeverity : MessageSeverity → LogLevel
| .information => .info
| .warning => .warning
| .error => .error

instance : ToString LogLevel := ⟨LogLevel.toString⟩

def LogLevel.visibleAtVerbosity (self : LogLevel) (verbosity : Verbosity) : Bool :=
  match self with
  | .trace => verbosity == .verbose
  | .info => verbosity != .quiet
  | _ => true

structure LogEntry where
  level : LogLevel
  message : String
  deriving Inhabited, ToJson, FromJson

protected def LogEntry.toString (self : LogEntry) : String :=
  s!"{self.level}: {self.message.trim}"

instance : ToString LogEntry := ⟨LogEntry.toString⟩

class MonadLog (m : Type u → Type v) where
  logEntry (e : LogEntry) : m PUnit

export MonadLog (logEntry)

@[inline] def logVerbose [Monad m] [MonadLog m] (message : String) : m PUnit := do
  logEntry {level := .trace, message}

@[inline] def logInfo [Monad m] [MonadLog m] (message : String) : m PUnit := do
  logEntry {level := .info, message}

@[inline] def logWarning [MonadLog m] (message : String) : m PUnit :=
  logEntry {level := .warning, message}

@[inline] def logError  [MonadLog m] (message : String) : m PUnit :=
  logEntry {level := .error, message}

def logToIO (e : LogEntry) (verbosity : Verbosity) : BaseIO PUnit := do
  match e.level with
  | .trace => if verbosity == .verbose then
    IO.println e.message.trim |>.catchExceptions fun _ => pure ()
  | .info => if verbosity != .quiet then
    IO.println e.message.trim |>.catchExceptions fun _ => pure ()
  | .warning => IO.eprintln s!"warning: {e.message.trim}" |>.catchExceptions fun _ => pure ()
  | .error => IO.eprintln s!"error: {e.message.trim}" |>.catchExceptions fun _ => pure ()

def logToStream (e : LogEntry) (h : IO.FS.Stream) (verbosity : Verbosity) : BaseIO PUnit := do
  match e.level with
  | .trace => if verbosity == .verbose then
    h.putStrLn s!"trace: {e.message.trim}" |>.catchExceptions fun _ => pure ()
  | .info => if verbosity != .quiet then
    h.putStrLn s!"info: {e.message.trim}" |>.catchExceptions fun _ => pure ()
  | .warning => h.putStrLn s!"warning: {e.message.trim}" |>.catchExceptions fun _ => pure ()
  | .error => h.putStrLn s!"error: {e.message.trim}" |>.catchExceptions fun _ => pure ()

@[specialize] def logSerialMessage (msg : SerialMessage) [MonadLog m] : m PUnit :=
  let str := msg.data
  let str := if msg.caption.trim.isEmpty then
    str.trim else s!"{msg.caption.trim}:\n{str.trim}"
  logEntry {
    level := .ofMessageSeverity msg.severity
    message := mkErrorStringWithPos msg.fileName msg.pos str msg.endPos
  }

namespace MonadLog

@[specialize] def nop [Pure m] : MonadLog m :=
  ⟨fun _ => pure ()⟩

instance [Pure m] : Inhabited (MonadLog m) := ⟨MonadLog.nop⟩

@[specialize] def io [MonadLiftT BaseIO m] (verbosity := Verbosity.normal) : MonadLog m where
  logEntry e := logToIO e verbosity

@[inline] def stream [MonadLiftT BaseIO m] (h : IO.FS.Stream) (verbosity := Verbosity.normal) : MonadLog m where
  logEntry e := logToStream e h verbosity

@[inline] def stdout [MonadLiftT BaseIO m] (verbosity := Verbosity.normal) : MonadLog m where
  logEntry e := liftM (m := BaseIO) do logToStream e (← IO.getStdout) verbosity

@[inline] def stderr [MonadLiftT BaseIO m] (verbosity := Verbosity.normal) : MonadLog m where
  logEntry e := liftM (m := BaseIO) do logToStream e (← IO.getStderr) verbosity

@[inline] def lift [MonadLiftT m n] (self : MonadLog m) : MonadLog n where
  logEntry e := liftM <| self.logEntry e

instance [MonadLift m n] [methods : MonadLog m] : MonadLog n := lift methods

end MonadLog

abbrev MonadLogT (m : Type u → Type v) (n : Type v → Type w) :=
  ReaderT (MonadLog m) n

instance [Pure n] [Inhabited α] : Inhabited (MonadLogT m n α) :=
  ⟨fun _ => pure Inhabited.default⟩

instance [Monad n] [MonadLiftT m n] : MonadLog (MonadLogT m n) where
  logEntry e := do (← read).logEntry e

@[inline] def MonadLogT.adaptMethods [Monad n]
(f : MonadLog m → MonadLog m') (self : MonadLogT m' n α) : MonadLogT m n α :=
  ReaderT.adapt f self

@[inline] def  MonadLogT.ignoreLog [Pure m] (self : MonadLogT m n α) : n α :=
  self MonadLog.nop

structure Log where
  entries : Array LogEntry

namespace Log

@[inline] def empty : Log :=
  .mk #[]

instance : EmptyCollection Log := ⟨Log.empty⟩

@[inline] def isEmpty (log : Log) : Bool :=
  log.entries.isEmpty

@[inline] def size (log : Log) : Nat :=
  log.entries.size

@[inline] def push (log : Log) (e : LogEntry) : Log :=
  .mk <| log.entries.push e

@[inline] def append (log : Log) (o : Log) : Log :=
  .mk <| log.entries.append o.entries

instance : Append Log := ⟨Log.append⟩

@[inline] def shrink (log : Log) (n : Nat) : Log :=
  (.mk <| log.entries.shrink n)

@[inline] def split (log : Log) (n : Nat) : Log × Log :=
  (.mk <| log.entries.extract 0 n, log.shrink n)

def toString (log : Log) : String :=
  log.entries.foldl (· ++ ·.toString ++ "\n") ""

instance : ToString Log := ⟨Log.toString⟩

@[inline] def replay [Monad m] [logger : MonadLog m] (log : Log) : m PUnit :=
  log.entries.forM fun e => logger.logEntry e

@[inline] def filter (f : LogEntry → Bool) (log : Log) : Log :=
  .mk <| log.entries.filter f

def filterByVerbosity (log : Log) (verbosity := Verbosity.normal) : Log :=
  log.filter (·.level.visibleAtVerbosity verbosity)

@[inline] def any (f : LogEntry → Bool) (log : Log) : Bool :=
  log.entries.any f

def hasVisibleEntries (log : Log) (verbosity := Verbosity.normal) : Bool :=
  log.any (·.level.visibleAtVerbosity verbosity)

end Log

class MonadGetLog (m : Type → Type v) where
  getLog : m Log

@[inline] def MonadGetLog.getLogSize [Functor m] [MonadGetLog m] : m Nat :=
  (·.size) <$> getLog

export MonadGetLog (getLog getLogSize)

instance [MonadLift m n] [MonadGetLog m] : MonadGetLog n where
  getLog := liftM (m := m) getLog

abbrev LogT (m : Type → Type) :=
  StateT Log m

namespace LogT

instance [Monad m] : MonadGetLog (LogT m) := ⟨get⟩

@[inline] protected def log [Monad m] (e : LogEntry) : LogT m PUnit :=
  modify (·.push e)

instance [Monad m] : MonadLog (LogT m) := ⟨LogT.log⟩

end LogT

abbrev ELogT (m : Type → Type) :=
  EStateT Nat Log m

namespace ELogT

instance [Pure m] : MonadGetLog (ELogT m) := ⟨get⟩

@[inline] protected def log [Monad m] (e : LogEntry) : ELogT m PUnit :=
  modify (·.push e)

instance [Monad m] : MonadLog (ELogT m) := ⟨ELogT.log⟩

/-- Performs `x` and groups all logs generated into an error block. -/
@[inline] def errorWithLog [Monad m] (x : ELogT m α) : ELogT m β := fun s => do
  let iniSz := s.size
  match (← x.run s) with
  | .ok _ log | .error _ log => pure (.error iniSz log)

@[inline] protected def error [Monad m] (msg : String) : ELogT m α :=
  errorWithLog (logError msg)

instance [Monad m] : MonadError (ELogT m) := ⟨ELogT.error⟩

@[inline] def replayLog [Alternative n] [Monad n] [logger : MonadLog n] [MonadLiftT m n] (self : ELogT m α) : n α := do
  match (← self {}) with
  | .ok a log => log.replay (logger := logger) *> pure a
  | .error _ log => log.replay (logger := logger) *> failure

@[inline] def catchFailure [Monad m] (f : Log → LogT m α) (self : ELogT m α) : LogT m α := fun log => do
  match (← self log) with
  | .error n log => let (h,t) := log.split n; f h t
  | .ok a log => return (a, log)

@[inline] def captureLog [Monad m] (self : ELogT m α) : m (Option α × Log) := do
 match (← self {}) with
 | .ok a log => return (some a, log)
 | .error _ log => return (none, log)

end ELogT

export ELogT (errorWithLog)

abbrev LogIO := ELogT BaseIO

instance : MonadLift IO LogIO := ⟨MonadError.runIO⟩
