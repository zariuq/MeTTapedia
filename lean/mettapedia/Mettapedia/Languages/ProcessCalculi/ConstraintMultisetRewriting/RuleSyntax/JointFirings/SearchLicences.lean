import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Knowledge

/-!
# Prefix pruning and guard reuse for joint firings

On a fixed frame and at one entry cut, extending a fitted selection
adds constraints to its information. Inconsistency is a permanent
refusal. A guard already entailed stays entailed; a currently
unentailed guard is not a permanent refusal. The distinctions apply
to the same joint information in the source semantics, not to
internal search bookkeeping.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {E : Extensions.{uO, uH, uE} Hom} {P : Program Tm}

namespace Bag

variable (X : Frames Tm Hom) {s : State Tm O} {frame : E.Ext s.frame}
  {prior complete : List (Member O E P frame)}

/-- The opened equations of any retained member remain in the joint
information, including equations from the rows, not only its tells. -/
theorem models_of_members_subset
    (included : ∀ m ∈ prior, m ∈ complete) {b : Obj} {σ : Hom (E.target frame) b}
    (solved : X.Models σ ((⟨frame, complete⟩ : Bag O E P s.frame).information X s)) :
    X.Models σ ((⟨frame, prior⟩ : Bag O E P s.frame).information X s) := by
  obtain ⟨base, full⟩ := (Frames.models_append σ _ _).mp solved
  exact (Frames.models_append σ _ _).mpr ⟨base, fun equation member => by
    obtain ⟨m, retained, own⟩ := List.mem_flatMap.mp member
    exact full equation (List.mem_flatMap.mpr ⟨m, included m retained, own⟩)⟩

theorem unsolvable_prunes_extensions
    (included : ∀ m ∈ prior, m ∈ complete)
    (inconsistent : ¬ X.Solvable ((⟨frame, prior⟩ : Bag O E P s.frame).information X s)) :
    ¬ X.Solvable ((⟨frame, complete⟩ : Bag O E P s.frame).information X s) := by
  rintro ⟨b, σ, solves⟩
  exact inconsistent ⟨b, σ, models_of_members_subset X included solves⟩

/-- A completed guard on the entry cut can be retained while more
members refine its possible solutions. This also applies to a query
over that *same* entry cut. It says nothing about later cuts. -/
theorem entailed_guard_survives_extension
    (included : ∀ m ∈ prior, m ∈ complete)
    (guard : {b : Obj} → Hom (E.target frame) b → Prop)
    (known : X.Entails ((⟨frame, prior⟩ : Bag O E P s.frame).information X s) (fun _ σ => guard σ)) :
    X.Entails ((⟨frame, complete⟩ : Bag O E P s.frame).information X s) (fun _ σ => guard σ) :=
  fun b σ solves => known b σ (models_of_members_subset X included solves)

variable [DecidableEq O]

theorem no_joint_admission_after_inconsistent_prefix
    (included : ∀ m ∈ prior, m ∈ complete)
    (inconsistent : ¬ X.Solvable ((⟨frame, prior⟩ : Bag O E P s.frame).information X s)) :
    ¬ (⟨frame, complete⟩ : Bag O E P s.frame).Admits X s := fun admitted =>
  unsolvable_prunes_extensions X included inconsistent admitted.2.2.1

end Bag

namespace Controls

open Knowledge

/-- Refusing a candidate alone is not a certificate that no joint
extension can admit it. The two equations in the source example
justify the two guards together. -/
theorem individual_refusal_is_not_a_pruning_certificate :
    (∀ m ∈ both.members, ¬ m.firing.Admits Examples.X start) ∧
      both.Admits Examples.X start :=
  ⟨no_order, both_admitted⟩

end Controls

#print axioms Bag.unsolvable_prunes_extensions
#print axioms Bag.entailed_guard_survives_extension
#print axioms Bag.no_joint_admission_after_inconsistent_prefix
#print axioms Controls.individual_refusal_is_not_a_pruning_certificate

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
