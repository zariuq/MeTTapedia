import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationSupportPrograms

/-!
# A cold cost model for the factored scope certificate

The measured component is constant-support compatibility with a new rule
family. Both methods use the same already qualified source package and the
same source programs. The model counts syntax-node visits for source
construction and compatibility checks; set-operation calls and wall time
are separate measurements. It does not price the dependent type checker.

The cache pays for constructing its footprint and independently validating
it against the submitted context. A changed context requires validation
again. No table revision identifier substitutes for that validation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.Cost

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open ComputationSyntax

variable {Head : Type}

def wholeCheck {n m : Nat} (context : Context Head n m) (term : Tm Head m) (name : DeclName) : Bool :=
  decide (name ∉ support (context.plug term))

theorem scope_eq_whole {n m : Nat} (cache : Cache Head n m) (valid : cache.check = true)
    (term : Tm Head m) (name : DeclName) :
    cache.scope term name = wholeCheck cache.context term name := by
  have footprint : cache.footprint = fixed cache.context := of_decide_eq_true valid
  simp only [Cache.scope, wholeCheck, footprint, plug_support]

def nodes : {n : Nat} → Tm Head n → Nat
  | _, .var _ | _, .head _ | _, .const _ => 1
  | _, .pi first second | _, .sigma first second => 1 + nodes first + nodes second
  | _, .id type left right => 1 + nodes type + nodes left + nodes right
  | _, .lam body => 1 + nodes body
  | _, .app first second | _, .pair first second => 1 + nodes first + nodes second
  | _, .fst inner | _, .snd inner | _, .refl inner => 1 + nodes inner

theorem payload_nodes (size : Nat) : nodes (Programs.payload size : Tower.Tm 0) = 2 * size + 1 := by
  induction size with
  | zero => rfl
  | succ size ih => simp only [Programs.payload, nodes, ih]; omega

theorem local_nodes (count : Nat) : nodes (Programs.localTerm count : Tower.Tm 0) = 4 * count + 1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [Programs.localTerm, TowerVectorsModel.addC, TowerVectorsModel.zeroC, nodes, ih]
    omega

def localVisits : Nat → Nat
  | 0 => nodes (Programs.localTerm 0 : Tower.Tm 0)
  | count + 1 => nodes (Programs.localTerm (count + 1) : Tower.Tm 0) + localVisits count

theorem local_visits (count : Nat) : localVisits count = 2 * count * (count + 1) + (count + 1) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [localVisits, local_nodes, ih]
    ring

/-- Source construction is paid by both representations. -/
def construction (size count : Nat) : Nat :=
  nodes (Programs.payload size : Tower.Tm 0) + localVisits count + 1

/-- Every request traverses the complete plugged source term. -/
def reference (size count : Nat) : Nat :=
  construction size count + localVisits count +
    (count + 1) * (nodes (Programs.payload size : Tower.Tm 0) + 1)

/-- The fixed context is traversed twice, for construction and validation. -/
def factored (size count : Nat) : Nat :=
  construction size count + localVisits count + 2 * (nodes (Programs.payload size : Tower.Tm 0) + 2)

theorem fourfold_family (size : Nat) (large : 512 ≤ size) : 4 * factored size 64 ≤ reference size 64 := by
  simp only [factored, reference, construction, payload_nodes, local_visits]
  omega

theorem small_case_loses : reference 0 0 = 6 ∧ factored 0 0 = 10 := by decide

def cache (size : Nat) : Cache Tower.Head 0 0 :=
  ⟨Programs.context size, fixed (Programs.context size)⟩

theorem cache_checked (size : Nat) : (cache size).check = true := by
  simp only [cache, Cache.check, decide_true]

theorem same_checks (size count : Nat) (name : DeclName) :
    (cache size).scope (Programs.localTerm count) name =
      wholeCheck (Programs.context size) (Programs.localTerm count) name :=
  scope_eq_whole (cache size) (cache_checked size) _ _

def changedContext : Cache Tower.Head 0 0 :=
  ⟨.pairFst .hole (.const (.mkSimple "new-row")), ∅⟩

theorem changed_context_refused : changedContext.check = false := by decide

theorem changed_theory_refused :
    (cache 1).scope (Programs.localTerm 0) TowerNumbersModel.zero = false := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.Cost

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.Cost.scope_eq_whole
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationSupport.Cost.fourfold_family
