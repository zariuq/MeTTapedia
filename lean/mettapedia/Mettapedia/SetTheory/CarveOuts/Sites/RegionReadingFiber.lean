import Mettapedia.SetTheory.CarveOuts.Sites.ProductSite
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings
import Mettapedia.GSLT.Core.NonFactorization

/-!
# What the region value at one context forgets

The region value of a formula at a point is the join of the smaller regions, at the same
context, on which the formula is forced. That join determines forcing at the same context.
It does not determine forcing after a later arrow.

On the labelled context paths, with the two-element frame of propositions, let membership
hold only after the context has grown. At the empty context the region value of `x ∈ x` is
bottom, the same as the region value of falsity, and neither formula is forced there. Along
the extension by the label `0`, membership is forced and falsity is not.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sites

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledContextPaths
open Mettapedia.GSLT.Core.NonFactorization

/-- Propositions as a frame, from the complete lattice whose join is existential
quantification and the Heyting structure whose implication is implication. The
Boolean algebra on propositions is not used: its top is packaged with excluded
middle. -/
instance (priority := 2000) : Order.Frame Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.instHeytingAlgebra

/-- The join of a set of propositions is existential quantification. The join
inherited through the conditionally complete lattice is the complete linear
order, and that order decides comparisons. -/
instance (priority := 3000) : SupSet Prop where
  sSup s := ∃ a ∈ s, a

/-- The meet of a set of propositions is universal quantification. -/
instance (priority := 3000) : InfSet Prop where
  sInf s := ∀ a ∈ s, a

/-- The top proposition. The top inherited from the Boolean algebra is packaged
with excluded middle. -/
instance (priority := 3000) : Top Prop where
  top := True

/-- The bottom proposition. -/
instance (priority := 3000) : Bot Prop where
  bot := False

/-- One value at every point of the product of labelled contexts with propositions. -/
def pointValues : (World × Propᵒᵈ) ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The empty context, read on the top proposition. -/
def here : World × Propᵒᵈ :=
  (initial, (⊤ : Prop))

/-- The one environment. -/
def pointEnv (p : World × Propᵒᵈ) : Environment pointValues 1 p :=
  fun _ => PUnit.unit

theorem transport_pointEnv {p q : World × Propᵒᵈ} (a : p ⟶ q) :
    transport pointValues a (pointEnv p) = pointEnv q :=
  rfl

/-- Membership holds exactly once the context length is positive. -/
def laterModel : Model pointValues where
  member p _ _ := p.1.length ≠ 0
  member_transport := by
    intro p q arrow _ _ holds targetZero
    apply holds
    exact Nat.eq_zero_of_add_eq_zero_right (arrow.1.property.trans targetZero)

/-- `x ∈ x`. -/
def selfMember : Formula 1 :=
  .member 0 0

/-- At the empty context, membership is forced only on the bottom proposition. -/
theorem selfMember_initial_iff {V : Prop} (hV : V ≤ region here) :
    siteForce pointValues laterModel selfMember (below here V)
        (transport pointValues (shrink here hV) (pointEnv here)) ↔
      V ≤ ⊥ := by
  rw [transport_pointEnv]
  change Covered V (fun _ _ => laterModel.member (below here V) (pointEnv _ 0) (pointEnv _ 0)) ↔
    V ≤ ⊥
  refine (covered_congr fun _ _ => ?_).trans covered_false_iff
  exact ⟨fun holds => holds rfl, fun holds => holds.elim⟩

/-- **The region value of membership at the empty context is bottom.** -/
theorem selfMember_region_bot :
    regionValue laterModel selfMember here (pointEnv here) = ⊥ := by
  refine eq_of_le_iff_below (regionValue_le selfMember here (pointEnv here)) bot_le fun V hV => ?_
  exact ((siteForce_shrink_iff selfMember here (pointEnv here) hV).symm).trans
    (selfMember_initial_iff hV)

/-- **Along the extension, membership is forced.** -/
theorem selfMember_after_extension :
    siteForce pointValues laterModel selfMember (forward here next)
      (transport pointValues (forwardArrow here (extension 0)) (pointEnv here)) := by
  unfold siteForce
  exact covered_self Nat.one_ne_zero

/-- **Along the extension, falsity is not forced.** -/
theorem bottom_not_after_extension :
    ¬ siteForce pointValues laterModel .bottom (forward here next)
      (transport pointValues (forwardArrow here (extension 0)) (pointEnv here)) := by
  intro holds
  exact (covered_false_iff.mp holds) True.intro

/-- The region value at the empty context. -/
def regionAtHere (φ : Formula 1) : Prop :=
  regionValue laterModel φ here (pointEnv here)

/-- Forcing at the target of the extension by `0`. -/
def forcedAfterExtension (φ : Formula 1) : Prop :=
  siteForce pointValues laterModel φ (forward here next)
    (transport pointValues (forwardArrow here (extension 0)) (pointEnv here))

/-- **The region value at the empty context forgets the extension.** Membership and falsity
have the same region value there, and only membership is forced after extending by `0`. -/
def laterFiber : NonTrivialFiber regionAtHere forcedAfterExtension :=
  NonTrivialFiber.ofProp
    (selfMember_region_bot.trans (regionValue_bottom here (pointEnv here)).symm)
    selfMember_after_extension
    bottom_not_after_extension

/-- At the empty context itself the two formulas still agree: neither is forced. -/
theorem neither_forced_at_source :
    ¬ siteForce pointValues laterModel selfMember here (pointEnv here) ∧
      ¬ siteForce pointValues laterModel .bottom here (pointEnv here) := by
  constructor
  · intro holds
    exact (selfMember_region_bot ▸
      (siteForce_iff_le_regionValue selfMember here (pointEnv here)).mp holds) True.intro
  · intro holds
    exact ((regionValue_bottom here (pointEnv here)) ▸
      (siteForce_iff_le_regionValue .bottom here (pointEnv here)).mp holds) True.intro

end Mettapedia.SetTheory.CarveOuts.Sites
