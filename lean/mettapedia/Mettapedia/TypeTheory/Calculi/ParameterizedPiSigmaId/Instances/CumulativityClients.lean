import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Checking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.RootCumulativityEta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerDecidability
/-!
# Discriminating clients of cumulative subtyping

Terms of the cumulative tower that tell the covariant cumulativity of the
judgment apart from the alternatives it excludes.

* A pair of a small type and one of its elements is a pair of a type of `𝒰₁`
  and an element, and a pair type over `𝒰₁` is not usable over `𝒰₀`.
* Domains are invariant: a function of small types is not a function of all
  types of `𝒰₁`, and a function of all types of `𝒰₁` is not a function of the
  small ones, although each small type is a type of `𝒰₁`.
* Reflexivity at a raised carrier: for `X : 𝒰₀`, `refl X` proves `X = X` at the
  carrier `𝒰₀` and at the carrier `𝒰₁`. The two identity types differ and have
  no common upper bound, so `refl X` has no least type. The same holds for a
  family `F : Π A 𝒰₀` at the carriers `Π A 𝒰₀` and `Π A 𝒰₁`. At a rigid carrier
  reflexivity has a least type.
* The kernel checks a family and its η-expansion at the raised codomain, refuses
  the family at a function type with another domain, and decides the tower's
  subtyping.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TowerModel

/-! ## Reflexivity at several carriers -/

/-- Expected-carrier checking constructs reflexivity at either carrier, without
any subtyping between identity types. -/
theorem refl_at_both_carriers {Head : Type} {R : Rules Head} {n : Nat}
    {Γ : Ctx Head n} {t A B : Tm Head n}
    (typed : Typed R Γ t A) (below : Below R Γ A B) :
    Typed R Γ (.refl t) (.id A t t) ∧ Typed R Γ (.refl t) (.id B t t) :=
  ⟨.reflIntro typed, .reflIntro (.sub typed below)⟩

/-- The same at function carriers, once dependent function types are covariant
in their codomain: excluding universes alone does not make reflexivity
principal. -/
theorem refl_at_both_function_carriers {Head : Type} {R : Rules Head} {n : Nat}
    {Γ : Ctx Head n} {f A : Tm Head n} {B C : Tm Head (n + 1)} {u v w : Head}
    (typed : Typed R Γ f (.pi A B))
    (lower : Typed R Γ (.pi A B) (.head u)) (hu : R.isUniverse u)
    (upper : Typed R Γ (.pi A C) (.head v)) (hv : R.isUniverse v)
    (domain : Typed R Γ A (.head w)) (hw : R.isUniverse w)
    (codomains : Below R (.snoc Γ A) B C) :
    Typed R Γ (.refl f) (.id (.pi A B) f f) ∧ Typed R Γ (.refl f) (.id (.pi A C) f f) :=
  refl_at_both_carriers typed (.subPi lower hu upper hv (.refl domain) hw codomains)

/-- A term with two unequal types of rigid shape has no least type: a least
type would be below both, hence equal to both. -/
theorem no_least_type_of_rigid_types {Head L : Type} [LevelOrder L] {S : Setting Head L}
    (facts : FormFacts S.R S.roles) {n : Nat}
    {Γ : Ctx Head n} {t R₁ R₂ : Tm Head n} (formed : CtxFormed S.R Γ)
    (shape₁ : RigidShape S.R S.roles Γ R₁) (shape₂ : RigidShape S.R S.roles Γ R₂)
    (typed₁ : Typed S.R Γ t R₁) (typed₂ : Typed S.R Γ t R₂)
    (unequal : ¬ TypeEq S.R Γ R₁ R₂) :
    ¬ ∃ T, Typed S.R Γ t T ∧ ∀ {X}, Typed S.R Γ t X → TypeLe S.R Γ T X := by
  rintro ⟨T, _, least⟩
  have e₁ := RigidShape.below_eq facts shape₁ formed
    (TypeLe.toBelow (least typed₁) (Typed.isType typed₁ formed))
  have e₂ := RigidShape.below_eq facts shape₂ formed
    (TypeLe.toBelow (least typed₂) (Typed.isType typed₂ formed))
  exact unequal (TypeEq.trans S.levels (TypeEq.symm e₁) e₂)

/-! ## The tower's kernel -/

section Tower

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- Head typing of the tower is a function. -/
theorem Tower.headsTyped {h u u' : Tower.Head} (first : Tower.rules.headTyping h u)
    (second : Tower.rules.headTyping h u') : u = u' := by
  cases first <;> cases second <;> rfl

/-- The universe order of the tower is decided. -/
theorem Tower.decideCumulative (u v : Tower.Head) :
    Tower.rules.cumulative u v ∨ ¬ Tower.rules.cumulative u v :=
  Decidable.em (Tower.Cumulative u v)

/-- Whether a type of the tower is usable at another is decided. -/
theorem Tower.below_decide {A B : Tm Tower.Head n} (formed : CtxFormed Tower.rules Γ)
    (typeA : IsType Tower.rules Γ A) (typeB : IsType Tower.rules Γ B) :
    Below Tower.rules Γ A B ∨ ¬ Below Tower.rules Γ A B :=
  Below.decide (S := setting fun _ => 0) TowerModel.facts roots heads algebra decideHeads
      TowerModel.complete
    Tower.decideCumulative formed typeA typeB

/-- On the bidirectional fragment, the tower's kernel checks a term against a
type exactly when the term has the type. -/
theorem Tower.check_iff_typed {t E : Tm Tower.Head n} (fragment : Bidirectional .check t)
    (formed : CtxFormed Tower.rules Γ) :
    Check Tower.rules TowerModel.roles Γ t E ↔ Typed Tower.rules Γ t E :=
  Check.iff_typed (S := setting fun _ => 0) TowerModel.facts algebra Tower.headsTyped
    fragment formed

/-- The universes at levels 0 and 1 are distinct types. -/
theorem universe₀_ne_universe₁ (formed : CtxFormed Tower.rules Γ) :
    ¬ TypeEq Tower.rules Γ universe₀ universe₁ := fun e => by
  rcases Tower.head_injective e formed with same | same
  · cases same
  · have := same (fun _ => 0)
    simp [LevelExpr.eval, Tower.zero] at this

/-- `𝒰₁` is not usable at `𝒰₀`. -/
theorem universe₁_not_below_universe₀ (formed : CtxFormed Tower.rules Γ) :
    ¬ Below Tower.rules Γ universe₁ universe₀ := fun le => by
  obtain ⟨v, _, eV, c⟩ := (Below.universe_iff (S := setting fun _ => 0) TowerModel.facts
    algebra formed (Tower.IsUniverse.sort _)).1 le
  have raise : Tower.rules.cumulative (.sort (.succ Tower.zero)) (.sort Tower.zero) :=
    algebra.same_right c (HeadSame.symm (levels fun _ => 0) (Tower.head_injective eV formed))
  have := raise (fun _ => 0)
  simp [LevelExpr.eval, Tower.zero] at this

/-! ## A pair at the next universe -/

/-- `X : 𝒰₀, x : X`. -/
abbrev elementContext : Ctx Tower.Head 2 := .snoc (.snoc .nil universe₀) (.var 0)

theorem elementContext_formed : CtxFormed Tower.rules elementContext :=
  .snoc (.snoc .nil ⟨_, Tower.IsUniverse.sort _, .headType (Tower.HeadTyping.sort _)⟩)
    ⟨_, Tower.IsUniverse.sort _, .var 0⟩

/-- The type `Σ (Y : 𝒰). Y` of pairs of a type of a universe and an element. -/
abbrev pointedAt (U : Tm Tower.Head n) : Tm Tower.Head n := .sigma U (.var 0)

theorem pointedAt₀_typed :
    Typed Tower.rules Γ (pointedAt universe₀) (.head (.sort (.max (.succ Tower.zero) Tower.zero))) :=
  .sigmaForm (.headType (Tower.HeadTyping.sort _)) (Tower.IsUniverse.sort _) (.var 0)
    (Tower.IsUniverse.sort _) (Tower.Join.sorts _ _)

theorem pointedAt₁_typed :
    Typed Tower.rules Γ (pointedAt universe₁)
      (.head (.sort (.max (.succ (.succ Tower.zero)) (.succ Tower.zero)))) :=
  .sigmaForm (.headType (Tower.HeadTyping.sort _)) (Tower.IsUniverse.sort _) (.var 0)
    (Tower.IsUniverse.sort _) (Tower.Join.sorts _ _)

/-- A small type and one of its elements. -/
theorem pair_typed :
    Typed Tower.rules elementContext (.pair (.var 1) (.var 0)) (pointedAt universe₀) :=
  .pairIntro pointedAt₀_typed (Tower.IsUniverse.sort _) (.var 1) (.var 0)

/-- `Σ (Y : 𝒰₀). Y` is usable at `Σ (Y : 𝒰₁). Y`. -/
theorem pointed_below : Below Tower.rules Γ (pointedAt universe₀) (pointedAt universe₁) :=
  .subSigma pointedAt₀_typed (Tower.IsUniverse.sort _) pointedAt₁_typed (Tower.IsUniverse.sort _)
    (.subUniv (fun _ => Nat.le_succ _)) (.subEqual (.refl (.var 0)) (Tower.IsUniverse.sort _))

/-- So the pair is a pair of a type of `𝒰₁` and an element. -/
theorem pair_typed_at_next_universe :
    Typed Tower.rules elementContext (.pair (.var 1) (.var 0)) (pointedAt universe₁) :=
  .sub pair_typed pointed_below

/-- `Σ (Y : 𝒰₁). Y` is not usable at `Σ (Y : 𝒰₀). Y`. -/
theorem pointed_not_below (formed : CtxFormed Tower.rules Γ) :
    ¬ Below Tower.rules Γ (pointedAt universe₁) (pointedAt universe₀) := fun le => by
  obtain ⟨_, _, eT, leA, _⟩ := (Below.sigma_iff (S := setting fun _ => 0) TowerModel.facts
    formed ⟨_, Tower.IsUniverse.sort _, pointedAt₁_typed⟩).1 le
  obtain ⟨eA, _⟩ := Tower.sigma_injective eT formed
  exact universe₁_not_below_universe₀ formed (.subTrans leA (TypeEq.below (TypeEq.symm eA)))

/-! ## Invariant domains -/

theorem piUniverse_typed {n : Nat} {Γ : Ctx Tower.Head n} (level : LevelExpr) :
    IsType Tower.rules Γ (.pi (.head (.sort level)) universe₀) :=
  ⟨_, Tower.IsUniverse.sort _, .piForm (.headType (Tower.HeadTyping.sort _))
    (Tower.IsUniverse.sort _) (.headType (Tower.HeadTyping.sort _)) (Tower.IsUniverse.sort _)
    (Tower.Join.sorts _ _)⟩

/-- A function of small types is not a function of all types of `𝒰₁`: the
domain is not covariant. -/
theorem domain_raise_refused (formed : CtxFormed Tower.rules Γ) :
    ¬ Below Tower.rules Γ (.pi universe₀ universe₀) (.pi universe₁ universe₀) := fun le => by
  obtain ⟨_, _, eT, eA, _⟩ := (Below.pi_iff (S := setting fun _ => 0) TowerModel.facts
    formed (piUniverse_typed _)).1 le
  obtain ⟨e₁, _⟩ := Tower.pi_injective eT formed
  exact universe₀_ne_universe₁ formed (TypeEq.trans (levels fun _ => 0) eA (TypeEq.symm e₁))

/-- A function of all types of `𝒰₁` is not a function of the small types,
although each small type is a type of `𝒰₁`: the domain is not contravariant. -/
theorem domain_contravariance_refused (formed : CtxFormed Tower.rules Γ) :
    ¬ Below Tower.rules Γ (.pi universe₁ universe₀) (.pi universe₀ universe₀) := fun le => by
  obtain ⟨_, _, eT, eA, _⟩ := (Below.pi_iff (S := setting fun _ => 0) TowerModel.facts
    formed (piUniverse_typed _)).1 le
  obtain ⟨e₀, _⟩ := Tower.pi_injective eT formed
  exact universe₀_ne_universe₁ formed (TypeEq.trans (levels fun _ => 0) e₀ (TypeEq.symm eA))

/-! ## Reflexivity at raised carriers -/

/-- `X : 𝒰₀`. -/
abbrev typeContext : Ctx Tower.Head 1 := .snoc .nil universe₀

theorem typeContext_formed : CtxFormed Tower.rules typeContext :=
  .snoc .nil ⟨_, Tower.IsUniverse.sort _, .headType (Tower.HeadTyping.sort _)⟩

/-- `refl X` proves `X = X` at the carrier `𝒰₀` and at the raised carrier `𝒰₁`. -/
theorem refl_type_at_both_carriers :
    Typed Tower.rules typeContext (.refl (.var 0)) (.id universe₀ (.var 0) (.var 0)) ∧
      Typed Tower.rules typeContext (.refl (.var 0)) (.id universe₁ (.var 0) (.var 0)) :=
  refl_at_both_carriers (.var 0) (.subUniv (fun _ => Nat.le_succ _))

/-- The two identity types differ: identity types are not covariant in their
carrier. -/
theorem raised_carrier_ne :
    ¬ TypeEq Tower.rules typeContext (.id universe₀ (.var 0) (.var 0))
      (.id universe₁ (.var 0) (.var 0)) := fun e =>
  universe₀_ne_universe₁ typeContext_formed (Tower.id_injective e typeContext_formed).1

/-- They have no common upper bound. -/
theorem raised_carriers_apart :
    ¬ BoundedAbove Tower.rules typeContext (.id universe₀ (.var 0) (.var 0))
      (.id universe₁ (.var 0) (.var 0)) :=
  not_boundedAbove_rigid (S := setting fun _ => 0)
    (RigidShape.rigid (S := setting fun _ => 0) TowerModel.facts .id typeContext_formed)
    (RigidShape.rigid (S := setting fun _ => 0) TowerModel.facts .id typeContext_formed)
        raised_carrier_ne

/-- So `refl X` has no least type. -/
theorem refl_type_no_least_type :
    ¬ ∃ T, Typed Tower.rules typeContext (.refl (.var 0)) T ∧
      ∀ {X}, Typed Tower.rules typeContext (.refl (.var 0)) X →
        TypeLe Tower.rules typeContext T X :=
  no_least_type_of_rigid_types (S := setting fun _ => 0) TowerModel.facts
    typeContext_formed .id .id refl_type_at_both_carriers.1 refl_type_at_both_carriers.2
    raised_carrier_ne

/-- In `A : 𝒰₀, F : Π A 𝒰₀`, `refl F` proves `F = F` at the carriers `Π A 𝒰₀` and
`Π A 𝒰₁`. -/
theorem refl_family_at_both_carriers :
    Typed Tower.rules familyContext (.refl (.var 0))
        (.id (.pi (.var 1) universe₀) (.var 0) (.var 0)) ∧
      Typed Tower.rules familyContext (.refl (.var 0))
        (.id (.pi (.var 1) universe₁) (.var 0) (.var 0)) :=
  refl_at_both_carriers (.var 0) family_types_below

/-- The two identity types differ. -/
theorem raised_function_carrier_ne :
    ¬ TypeEq Tower.rules familyContext (.id (.pi (.var 1) universe₀) (.var 0) (.var 0))
      (.id (.pi (.var 1) universe₁) (.var 0) (.var 0)) := fun e => by
  obtain ⟨eC, _⟩ := Tower.id_injective e familyContext_formed
  obtain ⟨_, eB⟩ := Tower.pi_injective eC familyContext_formed
  exact universe₀_ne_universe₁ (.snoc familyContext_formed ⟨_, Tower.IsUniverse.sort _, .var 1⟩)
    eB

/-- So `refl F` has no least type either. -/
theorem refl_family_no_least_type :
    ¬ ∃ T, Typed Tower.rules familyContext (.refl (.var 0)) T ∧
      ∀ {X}, Typed Tower.rules familyContext (.refl (.var 0)) X →
        TypeLe Tower.rules familyContext T X :=
  no_least_type_of_rigid_types (S := setting fun _ => 0) TowerModel.facts
    familyContext_formed .id .id refl_family_at_both_carriers.1 refl_family_at_both_carriers.2
    raised_function_carrier_ne

/-- At a rigid carrier reflexivity has a least type: in `X : 𝒰₀, x : X`, the
kernel synthesizes `Id X x x` for `refl x`, and every type of `refl x` is above
it. -/
theorem refl_element_least_type :
    Synth Tower.rules TowerModel.roles elementContext (.refl (.var 0))
        (.id (.var 1) (.var 0) (.var 0)) ∧
      ∀ {X}, Typed Tower.rules elementContext (.refl (.var 0)) X →
        TypeLe Tower.rules elementContext (.id (.var 1) (.var 0) (.var 0)) X := by
  have synth : Synth Tower.rules TowerModel.roles elementContext (.refl (.var 0))
      (.id (.var 1) (.var 0) (.var 0)) := .refl (.var 0) (.neutral (.var 1))
  exact ⟨synth, (Synth.principal (S := setting fun _ => 0) TowerModel.facts algebra
    Tower.headsTyped synth elementContext_formed).2⟩

/-! ## The kernel on a family -/

/-- The kernel checks the family `F : Π A 𝒰₀` itself at `Π A 𝒰₁`. -/
theorem family_checked_at_raised_codomain :
    Check Tower.rules TowerModel.roles familyContext (.var 0) (.pi (.var 1) universe₁) :=
  (Tower.check_iff_typed (.synthesized (.var 0)) familyContext_formed).2
    family_typed_at_raised_codomain

/-- The kernel checks the η-expansion `λ x. F x` at `Π A 𝒰₁`. -/
theorem eta_expansion_checked_at_raised_codomain :
    Check Tower.rules TowerModel.roles familyContext (.lam (.app (.var 1) (.var 0)))
      (.pi (.var 1) universe₁) :=
  (Tower.check_iff_typed (.lam (.synthesized (.app (.var 1) (.synthesized (.var 0)))))
    familyContext_formed).2 etaExpansion_typed_at_raised_codomain

/-- The kernel refuses the family at a function type over another domain:
`F : Π A 𝒰₀` is not a function of small types. -/
theorem family_not_checked_at_other_domain :
    ¬ Check Tower.rules TowerModel.roles familyContext (.var 0) (.pi universe₀ universe₀) := by
  intro check
  have typing := Check.sound (S := setting fun _ => 0) TowerModel.facts algebra
    Tower.headsTyped check familyContext_formed
  have synth : Synth Tower.rules TowerModel.roles familyContext (.var 0)
      (.pi (.var 1) universe₀) := .var 0
  obtain ⟨_, principal⟩ := Synth.principal (S := setting fun _ => 0) TowerModel.facts
    algebra Tower.headsTyped synth familyContext_formed
  obtain ⟨eA, _⟩ := TypeLe.pi_parts (S := setting fun _ => 0) TowerModel.facts
    (principal typing) (Typed.isType (S := setting fun _ => 0) typing
      familyContext_formed) familyContext_formed
  exact (TypeEq.neutral_form TowerModel.facts eA
    familyContext_formed (.var 1) (.inl ⟨_, rfl⟩)).not_former.1 _ rfl

end Tower

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
