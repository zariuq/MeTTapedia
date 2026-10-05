import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.LookupKey
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.TapeActions
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextPaths

/-!
# State-symbol dispatch through ordinary rho communication

The dispatcher receives state and symbol code, assembles an output as process
data, and lifts that data into a name. It then sends a request on the resulting
key. Three canonical COMM steps perform the entire operation; no substitution
inside a literal quotation or host-language lookup occurs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Dispatch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Stack TapeActions

abbrev liftPort : Pattern := port 11

def launch : Pattern := receive liftPort (send (.bvar 0) zero)

def assembly : Pattern :=
  parallel [send liftPort (send (.bvar 1) (drop 0)), launch]

def program : Pattern := receive statePort (receive scannedPort assembly)

private theorem subst_launch (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement launch = launch := by
  simp [launch, receive, send, semanticSubstProc, semanticSubstName, zero]

theorem subst_program (k : Nat) (replacement : Pattern) :
    semanticSubstProc k replacement program = program := by
  simp [program, receive, assembly, parallel, send, drop, semanticSubstProc,
    semanticSubstProcList, semanticSubstName, subst_launch]

theorem normalize_program : semanticNormalizeProc program = program := by
  simp [program, receive, assembly, launch, parallel, send, drop, zero,
    semanticNormalizeProc, semanticNormalizeProcList, semanticNormalizeName]

theorem program_coreShape : rhoProcCoreShape program = true := by
  simp [program, receive, assembly, launch, parallel, send, drop, zero,
    rhoProcCoreShape, rhoProcCoreShapeList, rhoNameCoreShape]

theorem program_binderSafe (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" depth program = true := by
  simp [program, receive, assembly, launch, parallel, send, drop, zero,
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt,
    Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeListAt]

theorem state_received (state : Nat) :
    semanticCommSubst (receive scannedPort assembly) (symbolCode state) =
      receive scannedPort (parallel [send liftPort (send (port state) (drop 0)), launch]) := by
  simp [semanticCommSubst, receive, assembly, parallel, send, drop,
    semanticSubstProc, semanticSubstProcList, semanticSubstName,
    normalize_symbolCode, subst_launch]
  rfl

theorem scanned_received (state scanned : Nat) :
    semanticCommSubst (parallel [send liftPort (send (port state) (drop 0)), launch])
        (symbolCode scanned) =
      parallel [send liftPort (LookupKey.data state scanned), launch] := by
  simp [semanticCommSubst, LookupKey.data, parallel, send, drop,
    semanticSubstProc, semanticSubstProcList, semanticSubstName,
    normalize_symbolCode, subst_launch]

theorem key_received (state scanned : Nat) :
    semanticCommSubst (send (.bvar 0) zero) (LookupKey.data state scanned) =
      send (LookupKey.key state scanned) zero := by
  simp [semanticCommSubst, send, semanticSubstProc, semanticSubstName,
    LookupKey.key, zero]

def invocation (state scanned : Nat) : Pattern :=
  parallel [send statePort (symbolCode state), program, send scannedPort (symbolCode scanned)]

theorem invocation_reduces (state scanned : Nat) :
    Nonempty (ReducesN 3 (invocation state scanned)
      (send (LookupKey.key state scanned) zero)) := by
  have first : Reduces (invocation state scanned)
      (parallel [receive scannedPort
        (parallel [send liftPort (send (port state) (drop 0)), launch]),
        send scannedPort (symbolCode scanned)]) := by
    change Reduces (parallel ([send statePort (symbolCode state),
      receive statePort (receive scannedPort assembly)] ++
        [send scannedPort (symbolCode scanned)])) _
    simpa only [state_received, List.singleton_append] using
      (Reduces.comm (n := statePort) (q := symbolCode state)
        (p := receive scannedPort assembly) (rest := [send scannedPort (symbolCode scanned)]))
  have secondRaw := Reduces.comm (n := scannedPort) (q := symbolCode scanned)
    (p := parallel [send liftPort (send (port state) (drop 0)), launch]) (rest := [])
  rw [scanned_received] at secondRaw
  have second : Reduces
      (parallel [receive scannedPort
        (parallel [send liftPort (send (port state) (drop 0)), launch]),
        send scannedPort (symbolCode scanned)])
      (parallel [send liftPort (LookupKey.data state scanned), launch]) :=
    .equiv (StructuralCongruence.par_comm _ _) secondRaw (StructuralCongruence.par_singleton _)
  have thirdRaw := Reduces.comm (n := liftPort) (q := LookupKey.data state scanned)
    (p := send (.bvar 0) zero) (rest := [])
  rw [key_received] at thirdRaw
  have third : Reduces (parallel [send liftPort (LookupKey.data state scanned), launch])
      (send (LookupKey.key state scanned) zero) :=
    .equiv (.refl _) thirdRaw (StructuralCongruence.par_singleton _)
  exact ⟨.succ first (.succ second (.succ third (.zero _)))⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Bridges.TuringMachine.Dispatch
