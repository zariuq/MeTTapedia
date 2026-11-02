import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedScopedInstantiation
import Mettapedia.Logic.LP.TermEquality

/-!
# Two actual calls: private scope versus intentional capture

Each call uses the same source computation-function shape with a shared Need
producer inside it. Instantiation acts before execution. Private labels become
distinct across calls; captured labels retain one identity and one joint store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedScopedInstantiation.Controls

open Mettapedia.Machines.BranchLocalNeed NeedReference
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open PolarizedNeed PolarizedNeedMachine
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic.LP

abbrev signature : LPSignature where
  constants := Bool
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

abbrev Symbol := SourceTerm (signature := signature) (Private := Unit) (Shared := Unit)
abbrev ScopedSymbol := ActiveTerm (signature := signature) (Private := Unit) (Shared := Unit)
abbrev Source (v : Nat) := Computation Symbol Unit (Equation Symbol) 0 v 0
abbrev Target (v : Nat) := Computation ScopedSymbol Unit (Equation ScopedSymbol) 0 v 0
abbrev Runtime := NeedMachine ScopedSymbol Unit (Equation ScopedSymbol) Empty Empty 0

instance : DecidableEq ScopedSymbol :=
  inferInstanceAs (DecidableEq (Term (signature.withVars (ScopedVar Unit ⊕ Unit))))

def privateName : Symbol := .var (.inl ())
def capturedName : Symbol := .var (.inr ())
def sourceConstant (value : Bool) : Symbol := .const value
def constant (value : Bool) : ScopedSymbol := .const value
def scopedPrivate (scope : Nat) : ScopedSymbol := ScopedVariables.termAt scope privateName
def scopedCapture : ScopedSymbol := .var (.inr ())

def call {v : Nat} (name : Symbol) (target : Bool) : Source v :=
  .valueApply
    (.valueLambda
      (.letNeed (.emit (name, sourceConstant target) (.returnValue (.native (.head name))))
        (.bindValue (.forceNeed 0) (.forceNeed 0))))
    (.native (.head (sourceConstant false)))

def activate {v : Nat} (scope : Nat) (source : Source v) : Target v :=
  PolarizedNeedParameterMap.code (ScopedVariables.termAt scope)
    (ScopedEquationInstantiation.equationAt scope) source

def twoCalls (firstScope secondScope : Nat) (name : Symbol) : Target 0 :=
  .bindValue (activate firstScope (call name false)) (activate secondScope (call name true))

def primitive (_ : Unit) (value : Tm ScopedSymbol 0) : Produced (Tm ScopedSymbol 0) Empty Empty :=
  .value value

def world : NeedWorld ScopedSymbol Unit (Equation ScopedSymbol) Empty Empty 0 :=
  ⟨0, [], .empty, .empty, 0, 0⟩

def closure (body : Target 0) : Closure ScopedSymbol Unit (Equation ScopedSymbol) 0 :=
  ⟨0, 0, 0, body, ids, Fin.elim0, Fin.elim0⟩

def check := PolarizedConstraintExecution.FirstOrderProfile.check
  (signature.withVars (ScopedVar Unit ⊕ Unit))

def observe (machine : Runtime) : Option ScopedSymbol × EquationStore ScopedSymbol :=
  ((match haltedOutcome machine with
    | some (.value (.returned (.native (.head symbol)))) => some symbol
    | _ => none), machine.world.receipts.effects)

def rawOutputs (fuel : Nat) (body : Target 0) :=
  ((NeedConstraintEffects.rawCore (extension primitive)).answerOccurrences fuel
    (PolarizedConstraintExecution.initial (closure body) world)).map observe

def outputs (fuel : Nat) (body : Target 0) :=
  ((PolarizedConstraintExecution.machine primitive [] check).answerOccurrences fuel
    (PolarizedConstraintExecution.initial (closure body) world)).map observe

theorem outputs_exact (fuel : Nat) (body : Target 0) :
    outputs fuel body = (rawOutputs fuel body).filter (fun observation => check observation.2) := by
  unfold outputs
  rw [PolarizedConstraintExecution.ordered_occurrences_exact
    (FirstOrder.action (signature.withVars (ScopedVar Unit ⊕ Unit))) primitive [] check
    (PolarizedConstraintExecution.FirstOrderProfile.check_exact _)]
  simpa only [rawOutputs, List.nil_append, Function.comp_def, observe] using
    (List.filter_map (f := observe) (p := fun observation => check observation.2)
      (l := (NeedConstraintEffects.rawCore (extension primitive)).answerOccurrences fuel
        (PolarizedConstraintExecution.initial (closure body) world))).symm

theorem two_private_calls_raw :
    rawOutputs 100 (twoCalls 0 1 privateName) =
      [(some (scopedPrivate 1), [(scopedPrivate 0, constant false), (scopedPrivate 1, constant true)])] := by
  decide +kernel

theorem distinct_private_store_accepted :
    check [(scopedPrivate 0, constant false), (scopedPrivate 1, constant true)] = true := by
  apply (PolarizedConstraintExecution.FirstOrderProfile.check_exact
    (signature.withVars (ScopedVar Unit ⊕ Unit)) _).mpr
  refine ⟨fun name => match name with
    | .inl identity => constant (identity.scope != 0)
    | .inr _ => constant false, ?_⟩
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem two_fresh_private_calls_succeed :
    outputs 100 (twoCalls 0 1 privateName) =
      [(some (scopedPrivate 1), [(scopedPrivate 0, constant false), (scopedPrivate 1, constant true)])] := by
  rw [outputs_exact, two_private_calls_raw]
  simp [distinct_private_store_accepted]

theorem conflicting_store_rejected (name : ScopedSymbol) :
    check [(name, constant false), (name, constant true)] = false := by
  cases checked : check [(name, constant false), (name, constant true)] with
  | false => rfl
  | true =>
      obtain ⟨assignment, models⟩ :=
        (PolarizedConstraintExecution.FirstOrderProfile.check_exact
          (signature.withVars (ScopedVar Unit ⊕ Unit)) _).mp checked
      have left := models (name, constant false) (by simp)
      have right := models (name, constant true) (by simp)
      change assignment.applyTerm name = constant false at left
      change assignment.applyTerm name = constant true at right
      have impossible := left.symm.trans right
      cases impossible

theorem reused_private_scope_is_refused : outputs 100 (twoCalls 0 0 privateName) = [] := by
  rw [outputs_exact]
  have raw : rawOutputs 100 (twoCalls 0 0 privateName) =
      [(some (scopedPrivate 0), [(scopedPrivate 0, constant false), (scopedPrivate 0, constant true)])] := by
    decide +kernel
  rw [raw]
  simp [conflicting_store_rejected]

theorem shared_capture_stays_shared : outputs 100 (twoCalls 0 1 capturedName) = [] := by
  rw [outputs_exact]
  have raw : rawOutputs 100 (twoCalls 0 1 capturedName) =
      [(some scopedCapture, [(scopedCapture, constant false), (scopedCapture, constant true)])] := by
    decide +kernel
  rw [raw]
  simp [conflicting_store_rejected]

/-- The first-class argument thunk's body is instantiated before it is
captured; this checks a source quotation position, not just a final store. -/
theorem passed_thunk_keeps_its_activation :
    activate 7 (.valueApply (.valueLambda (.forceThunk (.variable 0)))
      (.thunk (.emit (privateName, sourceConstant false) (.returnValue (.native (.head privateName)))))) =
    (.valueApply (.valueLambda (.forceThunk (.variable 0)))
      (.thunk (.emit (scopedPrivate 7, constant false) (.returnValue (.native (.head (scopedPrivate 7)))))) : Target 0) := rfl

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.PolarizedScopedInstantiation.Controls
