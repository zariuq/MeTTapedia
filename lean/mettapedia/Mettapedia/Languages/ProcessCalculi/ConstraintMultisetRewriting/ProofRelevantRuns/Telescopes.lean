import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullTelescopesControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullSwapControls

/-!
# Helper swaps: cells that keep event identity, and why they are not strict

Two firings that make helper telescopes `H₁` and `H₂` over one frame `Γ` commute only up to an
isomorphism of their composite frames: `f` then `g` ends at `Γ.H₁.H₂⁺`, `g` then `f` at `Γ.H₂.H₁⁺`
(`DependentFull.telescope_diamond`). The interchange of helper firings is therefore a square whose
vertical side is a frame isomorphism, not a globular cell. Each composite frame has two legs: the
projection that keeps the helpers made by one firing, and the lift that keeps the helpers made by
the other.

* `KeepsProvenance`: a comparison of the two composite frames **keeps event identity** when it
  sends the helpers made by each firing to the helpers made by the same firing, that is, when it
  commutes with the legs.
* `keepsProvenance_iff`: **the block exchange is the only comparison that keeps event identity.**
* `endo_keeping_legs`, `round_trip`: **coherence**: an endomorphism of a composite frame that keeps
  both legs is the identity, so every two composites of exchanges between the same composite
  frames that keep event identity agree; the round trip of exchanges is the identity.
* `point_exchange_ne_id`, `identity_not_keepsProvenance`: **the exchange is not strict**. Where the
  two firings make the same helper type, the two composite frames are one frame, and the
  exchange is an automorphism of it that is not the identity. The identity comparison swaps the two
  firings' helpers. This is the precise obstruction to strict commutation: identifying the two
  composites by the identity of frames loses event identity, and the composite states themselves
  differ (`DependentFull.SwapControls.composites_differ`). Commutation holds up to the exchange,
  and up to nothing smaller.

Where a helper's type mentions another firing's helper there is no swap at all
(`DependentFull.SwapControls.refl_no_swap`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface Interface.DependentFull

section Provenance

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

/-- The frame after a firing that makes `first` and then a firing that makes `second`. -/
abbrev composite (first second : Helpers Γ) : Context rules :=
  (second.reindex first.weaken).frame

/-- **A comparison of the two composite frames keeps event identity** when the helpers made by each
firing go to the helpers made by the same firing. -/
def KeepsProvenance (first second : Helpers Γ)
    (comparison : composite first second ⟶ composite second first) : Prop :=
  comparison ≫ (first.reindex second.weaken).weaken = Helpers.lift first.weaken second ∧
    comparison ≫ Helpers.lift second.weaken first = (second.reindex first.weaken).weaken

/-- The block exchange keeps event identity. -/
theorem exchange_keepsProvenance (first second : Helpers Γ) :
    KeepsProvenance first second (exchange first second) :=
  ⟨exchange_weaken first second, exchange_lift first second⟩

/-- **The block exchange is the only comparison that keeps event identity.** -/
theorem keepsProvenance_iff (first second : Helpers Γ)
    (comparison : composite first second ⟶ composite second first) :
    KeepsProvenance first second comparison ↔ comparison = exchange first second := by
  constructor
  · intro keeps
    exact exchange_unique first second comparison keeps.1 keeps.2
  · intro same
    subst same
    exact exchange_keepsProvenance first second

/-- **Coherence**: an endomorphism of a composite frame that keeps both legs is the identity. -/
theorem endo_keeping_legs (first second : Helpers Γ)
    (m : composite first second ⟶ composite first second)
    (keepsFirst : m ≫ (second.reindex first.weaken).weaken = (second.reindex first.weaken).weaken)
    (keepsSecond : m ≫ Helpers.lift first.weaken second = Helpers.lift first.weaken second) :
    m = 𝟙 _ := by
  have one := Helpers.into_unique first.weaken second (second.reindex first.weaken).weaken
    (Helpers.lift first.weaken second) (Helpers.lift_weaken first.weaken second).symm m
    keepsFirst keepsSecond
  have two := Helpers.into_unique first.weaken second (second.reindex first.weaken).weaken
    (Helpers.lift first.weaken second) (Helpers.lift_weaken first.weaken second).symm (𝟙 _)
    (Category.id_comp _) (Category.id_comp _)
  exact one.trans two.symm

/-- **Two comparisons that keep event identity agree**, whatever composites of exchanges they are. -/
theorem keepsProvenance_unique (first second : Helpers Γ)
    {one two : composite first second ⟶ composite second first}
    (keepsOne : KeepsProvenance first second one) (keepsTwo : KeepsProvenance first second two) :
    one = two :=
  ((keepsProvenance_iff first second one).mp keepsOne).trans
    ((keepsProvenance_iff first second two).mp keepsTwo).symm

/-- **The round trip of exchanges is the identity**, as an instance of coherence. -/
theorem round_trip (first second : Helpers Γ) :
    exchange first second ≫ exchange second first = 𝟙 _ :=
  endo_keeping_legs first second _
    (by rw [Category.assoc, exchange_weaken, exchange_lift])
    (by rw [Category.assoc, exchange_lift, exchange_weaken])

end Provenance

/-! ## The exchange is not strict -/

section Strict

open DependentFull.Controls DependentFull.TelescopeControls

/-- The composite frame `X, x : X, y : X` of two firings that each make one helper of type `X`. -/
theorem point_composite_arity : (composite pointHelpers pointHelpers).arity = 3 := rfl

/-- The exchange sends the newest variable to the second newest. -/
theorem point_exchange_newest :
    subst (exchange pointHelpers pointHelpers).substitution (.var 0 : Tm Tower.Head 3) =
      (.var 1 : Tm Tower.Head 3) :=
  rfl

/-- The identity sends the newest variable to itself. -/
theorem point_identity_newest :
    subst (𝟙 (composite pointHelpers pointHelpers) : composite pointHelpers pointHelpers ⟶ _).substitution
      (.var 0 : Tm Tower.Head 3) = (.var 0 : Tm Tower.Head 3) :=
  rfl

/-- **The exchange of two firings that make the same helper type is not the identity**, although
the two composite frames are one frame. -/
theorem point_exchange_ne_id :
    exchange pointHelpers pointHelpers ≠ 𝟙 (composite pointHelpers pointHelpers) := by
  intro same
  have newest := congrArg (fun φ : composite pointHelpers pointHelpers ⟶ composite pointHelpers pointHelpers =>
    subst φ.substitution (.var 0 : Tm Tower.Head 3)) same
  have clash : (.var 1 : Tm Tower.Head 3) = (.var 0 : Tm Tower.Head 3) :=
    point_exchange_newest.symm.trans (newest.trans point_identity_newest)
  exact absurd (congrArg Fin.val (Tm.var.inj clash)) (by decide)

/-- **The identity comparison does not keep event identity**: it sends the helper of each firing to
the helper of the other. Strict commutation, which compares the composites by the identity, is
therefore not available for helper firings. -/
theorem identity_not_keepsProvenance :
    ¬ KeepsProvenance pointHelpers pointHelpers (𝟙 (composite pointHelpers pointHelpers)) :=
  fun keeps => point_exchange_ne_id ((keepsProvenance_iff _ _ _).mp keeps).symm

end Strict

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofRelevantRuns
