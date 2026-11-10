import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGenericFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceWeakBranching

/-!
# Weak and branching identity over the generic step

The weak layer of `RaceWeak` and `RaceWeakBranching` is stated for every Hennessy–Milner system, so it
applies to the labelled step of every instance of the interface (`Generic.system`), with any frames.

* **Transport-equivalent states are weakly and branching bisimilar** (`weakBisimilar_of_same`,
  `branchingBisimilar_of_same`), for every transport that keeps the labels.
* **On the one-frame instance the weak notions are those of `RaceWeak`** (`weakMoves_lift_iff`,
  `weakBisimilar_lift_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic

open Interface (Frames Transport)
open AnnotatedRuns (Firing firstOrder)

universe uOb uTm uHm uO uSt uF uI uL

section Generic

variable {Obj : Type uOb} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uHm}
  {X : Frames Tm Hom} {O : Type uO} [DecidableEq O] {State : Type uSt} {Fir : State → Type uF}
  {L : Type uL}
variable (P : Interface.Step X O State Fir) (offers : L → (s : State) → Fir s → Prop)
  (internal : L → Prop)

/-- **Weak bisimilarity of the generic step**, with the program's internal labels. -/
def WeakBisimilar (s t : State) : Prop := Weak.Bisimilar (system P offers) internal s t

/-- **Branching bisimilarity of the generic step.** -/
def BranchingBisimilar (s t : State) : Prop := Weak.BranchingBisimilar (system P offers) internal s t

variable {P offers internal}

/-- **Transport-equivalent states are weakly bisimilar.** -/
theorem weakBisimilar_of_same (T : Transport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)
    (invariant : Invariant P offers T) {s t : State} (same : T.Same s t) :
    WeakBisimilar P offers internal s t :=
  Weak.bisimilar_of_strong (bisimilar_of_same T invariant same)

/-- **Transport-equivalent states are branching bisimilar.** -/
theorem branchingBisimilar_of_same (T : Transport.{uOb, uTm, uHm, uO, uSt, uF, uI} P)
    (invariant : Invariant P offers T) {s t : State} (same : T.Same s t) :
    BranchingBisimilar P offers internal s t :=
  Weak.branching_of_strong (bisimilar_of_same T invariant same)

end Generic

section FirstOrder

variable {T : Type*} {S : Type*} {O : Type*} [DecidableEq O] {L : Type*}
  {A : SubstitutionAction T S} {label : O → T} {offers : L → Firing T S O → Prop} {internal : L → Prop}

theorem silent_lift_iff {C D : Configuration T O} :
    Weak.Silent (system (firstOrder A label).toStep (lift offers)) internal C D ↔
      Weak.Silent (Race.system A label offers) internal C D :=
  exists_congr fun _ => and_congr_right fun _ => moves_lift_iff

theorem silently_lift_iff {C D : Configuration T O} :
    Weak.Silently (system (firstOrder A label).toStep (lift offers)) internal C D ↔
      Weak.Silently (Race.system A label offers) internal C D := by
  constructor
  · rintro ⟨z, chain, equiv⟩
    exact ⟨z, Relation.ReflTransGen.mono (fun _ _ step => silent_lift_iff.mp step) _ _ chain, equiv⟩
  · rintro ⟨z, chain, equiv⟩
    exact ⟨z, Relation.ReflTransGen.mono (fun _ _ step => silent_lift_iff.mpr step) _ _ chain, equiv⟩

/-- **Weak moves of the lift are those of `RaceWeak`.** -/
theorem weakMoves_lift_iff {C D : Configuration T O} {ℓ : L} :
    Weak.Act (system (firstOrder A label).toStep (lift offers)) internal ℓ C D ↔
      WeakMoves A label offers internal C ℓ D :=
  or_congr (and_congr_right fun _ => silently_lift_iff)
    (and_congr_right fun _ => exists₂_congr fun _ _ =>
      and_congr silently_lift_iff (and_congr moves_lift_iff silently_lift_iff))

/-- **Weak bisimilarity of the lift is weak bisimilarity of `RaceWeak`.** -/
theorem weakBisimilar_lift_iff {C D : Configuration T O} :
    WeakBisimilar (firstOrder A label).toStep (lift offers) internal C D ↔
      Race.WeakBisimilar A label offers internal C D := by
  constructor
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨R, ⟨fun a b rel ℓ a' moved => ?_, fun a b rel ℓ b' moved => ?_,
      fun _ _ _ atom => atom.elim⟩, related⟩
    · obtain ⟨b'', moved', rel'⟩ := forward rel ℓ (weakMoves_lift_iff.mpr moved)
      exact ⟨b'', weakMoves_lift_iff.mp moved', rel'⟩
    · obtain ⟨a'', moved', rel'⟩ := backward rel ℓ (weakMoves_lift_iff.mpr moved)
      exact ⟨a'', weakMoves_lift_iff.mp moved', rel'⟩
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨R, ⟨fun a b rel ℓ a' moved => ?_, fun a b rel ℓ b' moved => ?_,
      fun _ _ _ atom => atom.elim⟩, related⟩
    · obtain ⟨b'', moved', rel'⟩ := forward rel ℓ (weakMoves_lift_iff.mp moved)
      exact ⟨b'', weakMoves_lift_iff.mpr moved', rel'⟩
    · obtain ⟨a'', moved', rel'⟩ := backward rel ℓ (weakMoves_lift_iff.mp moved)
      exact ⟨a'', weakMoves_lift_iff.mpr moved', rel'⟩

end FirstOrder

#print axioms weakBisimilar_of_same
#print axioms branchingBisimilar_of_same
#print axioms weakMoves_lift_iff
#print axioms weakBisimilar_lift_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic
