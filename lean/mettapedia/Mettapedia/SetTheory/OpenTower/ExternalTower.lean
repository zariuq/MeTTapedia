import Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure
import Mettapedia.SetTheory.OpenTower.InternalTower
import Foundation.FirstOrder.SetTheory.Basic

/-!
# The external tower: one level of `ZFSet` inside the next

This is meaning (b) of "open tower" (see `InternalTower`): the external schema of
embeddings between Lean's universe levels. It needs no internal inaccessible hypothesis; it
still uses Lean's metatheory and universe rules, so it is neither an absolute consistency
proof nor an internal theorem that inaccessibles are cofinal. The pre-set lift
descends to a membership-preserving embedding `lift : ZFSet.{u} → ZFSet.{u+1}`
(`ZFSetUniverseLift`), whose image is an end-extension: every member of a lifted set is a
lifted set (`mem_lift`). The image of the whole lower level is a *set* of the next level
(`image_is_set`, the set `carrierCode`), closed in the sense of the internal tower
(`image_closed`) and containing `ω` (`omega_mem_image`). A level never sees itself whole in
this way (`not_seen_whole_at_same_level`).

**The lower level is a set model of everything true at the lower level.** The lift is an
isomorphism of the lower level onto the members of `carrierCode` (`liftEquiv`), so the two
are elementarily equivalent for the first-order language of set theory
(`image_elementarilyEquivalent`): every sentence true at level `u` is true in the set
`carrierCode` at level `u + 1`, and conversely.

**Internal and external, compared.** At level `u + 1` the external stage `carrierCode` is an
ordinary closed set, so it is one stage of the internal tower of that level. Every stage of
the internal tower of level `u` lifts to a closed member of it (`lift_stage_mem_image`), so
the internal tower of the lower level, a proper class there, is bounded by one set one level
up. Under `CofinalInaccessibles.{u}` the external stage is a *limit* stage: every member lies
in a closed member (`image_members_in_closed_members`), so it is the least closed set around
none of its members (`image_not_successor`). Without that hypothesis the external step still
gives one closed set containing `ω` at every successor level (`exists_closed_omega_succ`), and
two nested ones two levels up (`exists_nested_closed_omega`). A closed set containing `ω` is a
set model of `𝗭𝗙𝗖` (`ZFCStages.closed_models_zfc`).

**Openness across levels is a schema.** Universe levels are not terms: no Lean proposition
quantifies over them, and no type is the union of `ZFSet.{u}` over all `u`. A
universe-polymorphic theorem such as `exists_closed_omega_succ` is checked once and holds at each
level written down; the statement "level `u + n` has `n` nested closed sets for every `n`"
has no Lean form, because `u + n` with `n : ℕ` is not a level. Each Lean statement sees
finitely many levels.

The embedding, its injectivity and its preservation of membership are free of choice. The
image set `carrierCode` uses Mathlib's `ZFSet.range`, and its closure uses replacement, both
of which depend on choice.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.ExternalTower

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetUniverseLift ZFSetLiftedUniverseClosure
open InternalTower
open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-! ## The embedding and its image -/

/-- The membership-preserving embedding of one level into the next. -/
def liftEmbedding : ZFSet.{u} ↪ ZFSet.{u + 1} := ⟨lift, lift_injective⟩

theorem liftEmbedding_mem_iff {x y : ZFSet.{u}} :
    liftEmbedding x ∈ liftEmbedding y ↔ x ∈ y :=
  lift_mem_lift

/-- An end-extension: members of lifted sets are lifted sets. -/
theorem mem_liftEmbedding {x : ZFSet.{u + 1}} {y : ZFSet.{u}} :
    x ∈ liftEmbedding y ↔ ∃ z ∈ y, liftEmbedding z = x :=
  mem_lift

/-- **The lower level, seen whole.** The image of the embedding is a set of the next level. -/
theorem image_is_set : ∃ c : ZFSet.{u + 1}, ∀ x, x ∈ c ↔ ∃ y : ZFSet.{u}, lift y = x :=
  ⟨carrierCode, fun _ => mem_carrierCode⟩

theorem image_closed : Closed carrierCode.{u} := carrierCode_closed

theorem image_transitive : ZFSet.IsTransitive carrierCode.{u} := carrierCode_transitive

/-- No level sees itself whole: no set of a level has its members in bijection with the
level. -/
theorem not_seen_whole_at_same_level :
    ¬ ∃ a : ZFSet.{u}, Nonempty (ZFSetDependentProducts.Elements a ≃ ZFSet.{u}) :=
  no_same_level_carrier_code

theorem image_not_lift (y : ZFSet.{u}) : lift y ≠ carrierCode.{u} := by
  intro equal
  have member : lift y ∈ carrierCode.{u} := mem_carrierCode.mpr ⟨y, rfl⟩
  rw [equal] at member
  exact carrier_not_member member

/-! ## The finite ordinals and `ω` are preserved -/

theorem lift_insert (a b : ZFSet.{u}) : lift (insert a b) = insert (lift a) (lift b) := by
  apply ZFSet.ext
  intro z
  rw [mem_lift, ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases ZFSet.mem_insert_iff.mp hx with rfl | hxb
    · exact Or.inl rfl
    · exact Or.inr (lift_mem_lift.mpr hxb)
  · rintro (rfl | hz)
    · exact ⟨a, ZFSet.mem_insert _ _, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := mem_lift.mp hz
      exact ⟨x, ZFSet.mem_insert_of_mem _ hx, rfl⟩

theorem lift_natCode (n : ℕ) : lift (natCode.{u} n) = natCode.{u + 1} n := by
  induction n with
  | zero => exact lift_empty
  | succ n ih =>
    change lift (insert (natCode.{u} n) (natCode.{u} n)) =
      insert (natCode.{u + 1} n) (natCode.{u + 1} n)
    rw [lift_insert, ih]

theorem lift_omega : lift (ZFSet.omega.{u}) = ZFSet.omega.{u + 1} := by
  apply ZFSet.ext
  intro x
  rw [mem_lift, mem_omega_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨n, rfl⟩ := mem_omega_iff.mp hz
    exact ⟨n, (lift_natCode n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨natCode.{u} n, mem_omega_iff.mpr ⟨n, rfl⟩, lift_natCode n⟩

theorem omega_mem_image : ZFSet.omega.{u + 1} ∈ carrierCode.{u} :=
  mem_carrierCode.mpr ⟨ZFSet.omega, lift_omega⟩

/-! ## The image is a copy of the lower level -/

/-- The members of a set, as a structure for the language of set theory. -/
def Members (U : ZFSet.{u}) : Type (u + 1) := {x : ZFSet.{u} // x ∈ U}

instance (U : ZFSet.{u}) : SetStructure (Members U) := ⟨fun y x => x.1 ∈ y.1⟩

@[simp] theorem Members.mem_iff {U : ZFSet.{u}} {x y : Members U} : x ∈ y ↔ x.1 ∈ y.1 :=
  Iff.rfl

theorem Members.ext {U : ZFSet.{u}} {x y : Members U} (h : x.1 = y.1) : x = y :=
  Subtype.ext h

instance : Nonempty (Members carrierCode.{u}) :=
  ⟨⟨ZFSet.omega, omega_mem_image⟩⟩

/-- The lift as an isomorphism of the lower level onto the members of its image. -/
noncomputable def liftEquiv : ZFSet.{u} ≃ Members carrierCode.{u} where
  toFun x := ⟨lift x, mem_carrierCode.mpr ⟨x, rfl⟩⟩
  invFun y := lowerValue y.1
  left_inv x := lowerValue_lift x
  right_inv y := Subtype.ext (lift_lowerValue y.2)

theorem liftEquiv_mem_iff {x y : ZFSet.{u}} : liftEquiv x ∈ liftEquiv y ↔ x ∈ y :=
  lift_mem_lift

/-- **The image is elementarily equivalent to the lower level** for the first-order language
of set theory. -/
theorem image_elementarilyEquivalent : ZFSet.{u} ≡ₑ[ℒₛₑₜ] Members carrierCode.{u} := by
  apply Structure.ElementaryEquiv.of_equiv liftEquiv
  · intro k R v₁ v₂ h
    rcases Language.Set.rel_eq_eq_or_mem R with ⟨rfl, (rfl | rfl)⟩
    · change v₁ 0 = v₁ 1 ↔ v₂ 0 = v₂ 1
      rw [← h 0, ← h 1]
      exact liftEquiv.apply_eq_iff_eq.symm
    · change v₁ 0 ∈ v₁ 1 ↔ v₂ 0 ∈ v₂ 1
      rw [← h 0, ← h 1]
      exact liftEquiv_mem_iff.symm
  · intro _ f
    exact Empty.elim f

/-- Every sentence true at a level is true in its image one level up, and conversely. -/
theorem models_iff_image (φ : Sentence ℒₛₑₜ) :
    ZFSet.{u} ⊧ₘ φ ↔ Members carrierCode.{u} ⊧ₘ φ :=
  image_elementarilyEquivalent.models

theorem modelsTheory_iff_image (T : Theory ℒₛₑₜ) :
    ZFSet.{u} ⊧ₘ* T ↔ Members carrierCode.{u} ⊧ₘ* T :=
  image_elementarilyEquivalent.modelsTheory

/-! ## Internal and external, compared -/

/-- Every stage of the internal tower of the lower level lifts to a closed member of the image.
The lower tower, a proper class at its own level, is bounded by one set one level up. -/
theorem lift_stage_mem_image (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) (n : ℕ) :
    lift (stage h N n) ∈ carrierCode.{u} ∧ Closed (lift (stage h N n)) :=
  ⟨mem_carrierCode.mpr ⟨_, rfl⟩, closed_lift (stage_closed h N n)⟩

/-- So are the stages of the ordinal-indexed tower, which are not all members of any set at
the lower level (`ordinalStage_unbounded`). -/
theorem lift_ordinalStage_mem_image (h : CofinalInaccessibles.{u}) (N : ZFSet.{u})
    (α : Ordinal.{u}) :
    lift (ordinalStage h N α) ∈ carrierCode.{u} ∧ Closed (lift (ordinalStage h N α)) :=
  ⟨mem_carrierCode.mpr ⟨_, rfl⟩, closed_lift (ordinalStage_closed h N α)⟩

/-- **A limit stage.** Under cofinally many inaccessibles at the lower level, every member of
the image lies in a closed member of it. -/
theorem image_members_in_closed_members (h : CofinalInaccessibles.{u}) {M : ZFSet.{u + 1}}
    (hM : M ∈ carrierCode.{u}) : ∃ V ∈ carrierCode.{u}, M ∈ V ∧ Closed V :=
  ⟨(carrierUniverse h ⟨M, hM⟩).1, (carrierUniverse h ⟨M, hM⟩).2,
    carrierUniverse_contains h ⟨M, hM⟩, carrierUniverse_closed h ⟨M, hM⟩⟩

/-- The image is the least closed set around none of its members. -/
theorem image_not_successor (h : CofinalInaccessibles.{u}) {M : ZFSet.{u + 1}}
    (hM : M ∈ carrierCode.{u}) : ∃ V, Closed V ∧ M ∈ V ∧ ¬ carrierCode.{u} ⊆ V := by
  obtain ⟨V, hV, hMV, hVclosed⟩ := image_members_in_closed_members h hM
  exact ⟨V, hVclosed, hMV, fun below => ZFSet.mem_irrefl V (below hV)⟩

/-- Under hypotheses at both levels, least closed sets commute with the lift
(`ZFSetLiftedUniverseClosure.lift_univOf`); in particular the lifted ω-tower is the ω-tower
over the lifted base. -/
theorem lift_stage (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
    (N : ZFSet.{u}) (n : ℕ) : lift (stage small N n) = stage large (lift N) n := by
  induction n with
  | zero => exact lift_univOf small large N
  | succ n ih =>
    change lift (univOf small (stage small N n)) = univOf large (stage large (lift N) n)
    rw [lift_univOf small large, ih]

/-! ## What the external step gives without any hypothesis -/

/-- Every successor level has a closed set containing `ω`. -/
theorem exists_closed_omega_succ : ∃ U : ZFSet.{u + 1}, Closed U ∧ ZFSet.omega ∈ U :=
  ⟨carrierCode, carrierCode_closed, omega_mem_image⟩

/-- Two levels up there are two nested closed sets containing `ω`. -/
theorem exists_nested_closed_omega :
    ∃ U V : ZFSet.{u + 2}, Closed U ∧ Closed V ∧ ZFSet.omega ∈ U ∧ U ∈ V := by
  refine ⟨lift carrierCode.{u}, carrierCode.{u + 1}, closed_lift carrierCode_closed,
    carrierCode_closed, ?_, mem_carrierCode.mpr ⟨_, rfl⟩⟩
  rw [← lift_omega]
  exact lift_mem_lift.mpr omega_mem_image

#print axioms liftEmbedding
#print axioms liftEmbedding_mem_iff
#print axioms mem_liftEmbedding
#print axioms image_is_set
#print axioms image_closed
#print axioms not_seen_whole_at_same_level
#print axioms lift_omega
#print axioms omega_mem_image
#print axioms image_elementarilyEquivalent
#print axioms models_iff_image
#print axioms lift_stage_mem_image
#print axioms image_members_in_closed_members
#print axioms image_not_successor
#print axioms lift_stage
#print axioms exists_closed_omega_succ
#print axioms exists_nested_closed_omega

end Mettapedia.SetTheory.OpenTower.ExternalTower
