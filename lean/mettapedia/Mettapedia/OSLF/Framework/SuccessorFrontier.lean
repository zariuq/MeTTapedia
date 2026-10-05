import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Boolean observations of a qualified successor frontier

A finite successor query implements one-step modalities when its membership
relation is independently proved equal to the GSLT's step relation. Existential
folding realizes the step-future diamond; universal folding realizes the
existing forward box. The adjoint OSLF box quantifies over predecessors.

These comparisons apply to complete frontiers and Boolean predicates. Runtime
faults and incomplete searches require explicit outcomes beyond this interface.
The list retains duplicates, while both Boolean folds forget multiplicity.
Membership adequacy certifies the state relation; occurrence counts need
their own contract.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SuccessorFrontier

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities

universe uTerm

section Qualified

variable (theory : GSLT.{uTerm}) (successors : theory.Term → List theory.Term)
    (qualified : ∀ state next, next ∈ successors state ↔ theory.Step state next)

include qualified

/-- An existential Boolean fold computes the GSLT's step-future diamond. -/
theorem any_iff_diamond (test : theory.Term → Bool) (state : theory.Term) :
    (successors state).any test = true ↔
      gsltDiamond theory (fun next => test next = true) state := by
  rw [List.any_eq_true, gsltDiamond_spec]
  constructor
  · rintro ⟨next, member, satisfied⟩
    exact ⟨next, (qualified state next).mp member, satisfied⟩
  · rintro ⟨next, step, satisfied⟩
    exact ⟨next, (qualified state next).mpr step, satisfied⟩

/-- A universal Boolean fold computes the forward box of the same reduction span. -/
theorem all_iff_forwardBox (test : theory.Term → Bool) (state : theory.Term) :
    (successors state).all test = true ↔
      derivedForwardBox (gsltSpan theory) (fun next => test next = true) state := by
  rw [List.all_eq_true]
  simp only [derivedForwardBox, ui, pb, Function.comp, gsltSpan]
  constructor
  · intro universal ⟨origin, next, step⟩ equal
    change origin = state at equal
    subst origin
    exact universal next ((qualified state next).mpr step)
  · intro universal next member
    exact universal ⟨state, next, (qualified state next).mp member⟩ rfl

/-- An empty complete frontier is equivalent to an actual normal form. -/
theorem nil_iff_normal (state : theory.Term) :
    successors state = [] ↔ theory.IsNormalForm state := by
  constructor
  · intro empty ⟨next, step⟩
    have member := (qualified state next).mpr step
    simp [empty] at member
  · intro normal
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro next member
    exact normal ⟨next, (qualified state next).mp member⟩

end Qualified

namespace Controls

/-- A two-state system with the single edge from true to false. -/
abbrev oneEdge : GSLT := equalityGSLT Bool (fun source target => source = true ∧ target = false)

/-- The complete finite frontier of the two-state control. -/
def successors (state : Bool) : List Bool := if state then [false] else []

/-- The control query agrees with the independently specified step relation. -/
theorem successors_qualified (state next : Bool) :
    next ∈ successors state ↔ oneEdge.Step state next := by
  cases state <;> cases next <;> simp [successors, oneEdge, equalityGSLT_step]

/-- The genuine successor satisfies the positive Boolean predicate. -/
theorem positive_frontier :
    (successors true).any (fun state => !state) = true ∧
      (successors true).all (fun state => !state) = true := by
  decide

/-- Forward and adjoint boxes can disagree at the very same state. -/
theorem outgoing_box_not_adjoint_box :
    ¬ derivedForwardBox (gsltSpan oneEdge) (fun state => state = true) true ∧
      gsltBox oneEdge (fun state => state = true) true := by
  constructor
  · intro universal
    have impossible : (false : Bool) = true :=
      universal ⟨true, false, ⟨rfl, rfl⟩⟩ rfl
    cases impossible
  · apply (gsltBox_spec oneEdge (fun state : Bool => state = true) true).mpr
    intro source step
    have impossible : (true : Bool) = false := step.2
    cases impossible

/-- Omitting an enabled successor violates the query's completeness contract. -/
theorem empty_query_not_qualified :
    ¬ (∀ state next : Bool, next ∈ ([] : List Bool) ↔ oneEdge.Step state next) := by
  intro qualified
  have impossible := (qualified true false).mpr ⟨rfl, rfl⟩
  cases impossible

/-- Boolean modal readout forgets multiplicity retained by the frontier list. -/
theorem duplicate_frontier_same_modal_readout (test : Bool → Bool) :
    ([false] : List Bool).any test = [false, false].any test ∧
      ([false] : List Bool).all test = [false, false].all test ∧
      ([false] : List Bool).length ≠ [false, false].length := by
  cases same : test false <;> simp [same]

end Controls

end Mettapedia.OSLF.Framework.SuccessorFrontier
