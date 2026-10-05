import Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingExtension
import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# The relative free-account adjunction for full binding clones

The left adjoint adjoins occurrence-local account actions to an observed
full binding clone.  The right adjoint forgets only the action operation,
retaining every marked value, all source operators, substitution and the
source observation.  This auxiliary algebraic adjunction is not identified
with the authored Cost language transformer or its resource execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open FreeBindingTerms
open AccountBindingQuotientSubstitution
open FreeAccountBindingModel
open FreeAccountBindingExtension

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S) (accountSort : S.Srt)

/-- Transport the free model along a genuine observed full-clone map. -/
noncomputable def freeMap {first second : Over Q} (mapping : first ⟶ second) :
    model Q accountSort first ⟶ model Q accountSort second :=
  extend Q accountSort first (model Q accountSort second)
    (mapping ≫ FreeAccountBindingModel.unit Q accountSort second)

theorem unit_naturality {first second : Over Q} (mapping : first ⟶ second) :
    FreeAccountBindingModel.unit Q accountSort first ≫
        (AccountBindingAlgebra.forget Q accountSort).map (freeMap Q accountSort mapping) =
      mapping ≫ FreeAccountBindingModel.unit Q accountSort second :=
  extend_unit Q accountSort first (model Q accountSort second) _

/-- The universal extension provides the functor laws on arbitrary full
clone maps; these laws do not replace the accounted carrier by the base. -/
noncomputable def free : Over Q ⥤ AccountBindingAlgebra.Model Q accountSort where
  obj := model Q accountSort
  map := freeMap Q accountSort
  map_id := by
    intro base
    change extend Q accountSort base (model Q accountSort base)
      ((𝟙 base) ≫ FreeAccountBindingModel.unit Q accountSort base) = 𝟙 _
    rw [Category.id_comp]
    symm
    apply extend_unique Q accountSort base (model Q accountSort base) _ (𝟙 _)
    simp
  map_comp := by
    intro first second third before after
    symm
    apply extend_unique Q accountSort first (model Q accountSort third)
      ((before ≫ after) ≫ FreeAccountBindingModel.unit Q accountSort third)
      (freeMap Q accountSort before ≫ freeMap Q accountSort after)
    rw [Functor.map_comp, ← Category.assoc, unit_naturality, Category.assoc,
      unit_naturality, ← Category.assoc]

theorem extend_precompose {first second : Over Q} (mapping : first ⟶ second)
    (target : AccountBindingAlgebra.Model Q accountSort)
    (generator : second ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) :
    freeMap Q accountSort mapping ≫ extend Q accountSort second target generator =
      extend Q accountSort first target (mapping ≫ generator) := by
  apply extend_unique Q accountSort first target _
    (freeMap Q accountSort mapping ≫ extend Q accountSort second target generator)
  rw [Functor.map_comp, ← Category.assoc, unit_naturality, Category.assoc, extend_unit]

/-- Natural universal property in the source-observed full-clone category. -/
noncomputable def adjunction : free Q accountSort ⊣ AccountBindingAlgebra.forget Q accountSort :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv Q accountSort
      homEquiv_naturality_left_symm := by
        intro first second target mapping generator
        exact (extend_precompose Q accountSort mapping target generator).symm
      homEquiv_naturality_right := by
        intro source first second mapping after
        exact (Category.assoc (FreeAccountBindingModel.unit Q accountSort source)
          mapping.underlying after.underlying).symm }

/-- The actual monad induced by this auxiliary full-binding adjunction. -/
noncomputable def accountMonad : Monad (Over Q) := (adjunction Q accountSort).toMonad

theorem monad_obj (base : Over Q) :
    (accountMonad Q accountSort).obj base =
      (AccountBindingAlgebra.forget Q accountSort).obj (model Q accountSort base) := rfl

/-- The adjunction unit is the independently constructed full-clone
generator map over the unchanged source observation. -/
theorem monad_unit (base : Over Q) :
    (accountMonad Q accountSort).η.app base =
      FreeAccountBindingModel.unit Q accountSort base := by
  change FreeAccountBindingModel.unit Q accountSort base ≫
    (AccountBindingAlgebra.forget Q accountSort).map (𝟙 (model Q accountSort base)) = _
  simp

/-- Multiplication interprets the outer free account extension in the
inner accounted model, with the whole inner carrier as its generators. -/
theorem monad_multiplication (base : Over Q) :
    (accountMonad Q accountSort).μ.app base =
      (AccountBindingAlgebra.forget Q accountSort).map
        (extend Q accountSort
          ((AccountBindingAlgebra.forget Q accountSort).obj (model Q accountSort base))
          (model Q accountSort base) (𝟙 _)) := rfl

theorem monad_unit_gen (base : Over Q) {Γ : Ctx S} {sort : S.Srt}
    (value : base.left.substitution.Carrier Γ sort) :
    ((accountMonad Q accountSort).η.app base).left.raw.map value =
      project Q accountSort base (.gen value) := by
  rw [monad_unit]
  rfl

/-- An outer generator carries its entire marked inner value through
multiplication; it is not replaced by the source observation. -/
theorem multiplication_gen (base : Over Q) {Γ : Ctx S} {sort : S.Srt}
    (value : Carrier Q accountSort base Γ sort) :
    ((accountMonad Q accountSort).μ.app base).left.raw.map
      (project Q accountSort
        ((AccountBindingAlgebra.forget Q accountSort).obj (model Q accountSort base))
        (.gen value)) = value := rfl

/-- Multiplication retains occurrence-local ordered account action. -/
theorem multiplication_account (base : Over Q) {Γ : Ctx S} {sort : S.Srt}
    (word : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Carrier Q accountSort
      ((AccountBindingAlgebra.forget Q accountSort).obj (model Q accountSort base)) Γ sort) :
    ((accountMonad Q accountSort).μ.app base).left.raw.map
        (act Q accountSort
          ((AccountBindingAlgebra.forget Q accountSort).obj (model Q accountSort base)) word value) =
      act Q accountSort base word
        (((accountMonad Q accountSort).μ.app base).left.raw.map value) := by
  exact (extend Q accountSort
    ((AccountBindingAlgebra.forget Q accountSort).obj (model Q accountSort base))
    (model Q accountSort base) (𝟙 _)).map_act word value

/-- Multiplication respects full marked substitution environments, including
those subsequently lifted beneath binders by the original source operators. -/
theorem multiplication_substitute (base : Over Q) {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S
      ((accountMonad Q accountSort).obj ((accountMonad Q accountSort).obj base)).left.substitution.Carrier
      Γ Δ)
    (value : ((accountMonad Q accountSort).obj
      ((accountMonad Q accountSort).obj base)).left.substitution.Carrier Γ sort) :
    ((accountMonad Q accountSort).μ.app base).left.raw.map
      (((accountMonad Q accountSort).obj ((accountMonad Q accountSort).obj base)).left.substitution.substitute
        env value) =
      ((accountMonad Q accountSort).obj base).left.substitution.substitute
        (fun s v => ((accountMonad Q accountSort).μ.app base).left.raw.map (env s v))
        (((accountMonad Q accountSort).μ.app base).left.raw.map value) :=
  ((accountMonad Q accountSort).μ.app base).left.map_substitute env value

/-- A nontrivial local inner action gives two genuinely distinct nested
classes with the same multiplication.  A pure outer action distinguishes
the classes while retaining the complete marked inner clone. -/
theorem multiplication_not_injective (base : Over Q) {Γ : Ctx S} {sort : S.Srt}
    (word : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Carrier Q accountSort base Γ sort)
    (nontrivial : act Q accountSort base word value ≠ value) :
    ¬ Function.Injective (((accountMonad Q accountSort).μ.app base).left.raw.map
      (Γ := Γ) (s := sort)) := by
  let inner := (AccountBindingAlgebra.forget Q accountSort).obj (model Q accountSort base)
  let pureOuter := AccountBindingAlgebra.pure Q accountSort inner
  let probe := extend Q accountSort inner pureOuter (𝟙 inner)
  intro injective
  have multiplied :
      ((accountMonad Q accountSort).μ.app base).left.raw.map
          (project Q accountSort inner (.account word (.gen value))) =
        ((accountMonad Q accountSort).μ.app base).left.raw.map
          (project Q accountSort inner (.gen (act Q accountSort base word value))) := rfl
  have nested := injective multiplied
  have distinguished := congrArg probe.underlying.left.raw.map nested
  have same : value = act Q accountSort base word value := distinguished
  exact nontrivial same.symm

end Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingAdjunction
