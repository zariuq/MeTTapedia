import Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel

/-!
# The universal extension into accounted full binding clones

The structural fold descends because every generated relation was proved
sound in independently specified targets.  It preserves the original source
operators, whole marked substitution environments and local account action.
Uniqueness is proved among genuine accounted clone morphisms over the source.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingExtension

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open FreeBindingTerms
open RawAccountBindingExtension
open RawAccountBindingLaws
open AccountBindingCongruence
open AccountBindingQuotientSubstitution
open AccountBindingQuotientModel
open FreeAccountBindingModel

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S)
  (accountSort : S.Srt) (base : Over Q)
  (target : AccountBindingAlgebra.Model Q accountSort)
  (generator : base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target)

/-- The independently validated target fold, now descended to classes. -/
def extendMap {Γ : Ctx S} {sort : S.Srt} :
    Carrier Q accountSort base Γ sort → target.observed.left.substitution.Carrier Γ sort :=
  Quotient.lift (interpret Q accountSort base target generator) (by
    intro left right related
    rcases related with ⟨witness⟩
    exact derivation_sound Q accountSort base target generator witness)

theorem extend_project {Γ : Ctx S} {sort : S.Srt}
    (value : Raw Q accountSort base Γ sort) :
    extendMap Q accountSort base target generator (project Q accountSort base value) =
      interpret Q accountSort base target generator value := rfl

theorem extend_representativeEnv {Γ Δ : Ctx S}
    (env : Environment S (Carrier Q accountSort base) Γ Δ) :
    (fun s v => interpret Q accountSort base target generator
      (representativeEnv Q accountSort base env s v)) =
      (fun s v => extendMap Q accountSort base target generator (env s v)) := by
  funext sort v
  exact congrArg (extendMap Q accountSort base target generator)
    (project_representativeEnv Q accountSort base env sort v)

theorem extend_representativeArgs :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (Carrier Q accountSort base) arities Γ),
      interpretArguments Q accountSort base target generator
        (representativeArgs Q accountSort base args) =
        FamilyArgs.map (extendMap Q accountSort base target generator) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg₂ FamilyArgs.cons
      (congrArg (extendMap Q accountSort base target generator) (Quotient.out_eq head))
      (extend_representativeArgs tail)

theorem extend_substitute {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier Q accountSort base) Γ Δ)
    (value : Carrier Q accountSort base Γ sort) :
    extendMap Q accountSort base target generator (substitute Q accountSort base env value) =
      target.observed.left.substitution.substitute
        (fun s v => extendMap Q accountSort base target generator (env s v))
        (extendMap Q accountSort base target generator value) := by
  induction value using Quotient.inductionOn with
  | _ raw =>
      change target.observed.left.substitution.substitute
        (fun s v => interpret Q accountSort base target generator
          (representativeEnv Q accountSort base env s v))
        (interpret Q accountSort base target generator raw) = _
      exact congrArg (fun values => target.observed.left.substitution.substitute values
        (interpret Q accountSort base target generator raw))
        (extend_representativeEnv Q accountSort base target generator env)

/-- The extension is a full clone morphism, not merely a family of fibre
functions or a fold through environments in the generator image. -/
noncomputable def extendCloneHom :
    FreeBindingClone.Hom (AccountBindingQuotientModel.algebra Q accountSort base)
      target.observed.left where
  raw :=
    { map := extendMap Q accountSort base target generator
      map_variable := by intro Γ sort v; exact generator.left.raw.map_variable v
      map_operation := by
        intro Γ sort op args
        exact congrArg (target.observed.left.operation op)
          (extend_representativeArgs Q accountSort base target generator args) }
  map_substitute := extend_substitute Q accountSort base target generator

/-- The universal candidate preserves the full source observation and every
local action, in addition to the complete binding clone. -/
noncomputable def extend : model Q accountSort base ⟶ target where
  underlying := Over.homMk (extendCloneHom Q accountSort base target generator) (by
    apply FreeBindingClone.Hom.ext
    apply FreeBindingTerms.Hom.ext
    intro Γ sort value
    induction value using Quotient.inductionOn with
    | _ raw => exact observe_interpret Q accountSort base target generator raw)
  map_act := by
    intro Γ sort word value
    induction value using Quotient.inductionOn with
    | _ raw => rfl

/-- The extension agrees with the supplied genuine generator arrow. -/
theorem extend_unit : FreeAccountBindingModel.unit Q accountSort base ≫
    (AccountBindingAlgebra.forget Q accountSort).map
      (extend Q accountSort base target generator) = generator := by
  apply Over.OverMorphism.ext
  apply FreeBindingClone.Hom.ext
  exact FreeBindingTerms.Hom.ext (fun _ => rfl)

variable {F : Ctx S → S.Srt → Type u}

theorem map_projectArguments
    (mapping : {Γ : Ctx S} → {sort : S.Srt} → Carrier Q accountSort base Γ sort → F Γ sort) :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : Arguments Q accountSort base arities Γ),
      FamilyArgs.map mapping (projectArguments Q accountSort base args) =
        Arguments.map Q accountSort base
          (fun {_Γ _sort} value => mapping (project Q accountSort base value)) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg (FamilyArgs.cons
      (mapping (project Q accountSort base head))) (map_projectArguments mapping tail)

/-- Any genuine target arrow extending the base supplies a raw constructor
map.  Its substitution field keeps the whole marked environment. -/
noncomputable def constructorMapOfHom
    (arrow : model Q accountSort base ⟶ target)
    (agrees : FreeAccountBindingModel.unit Q accountSort base ≫
      (AccountBindingAlgebra.forget Q accountSort).map arrow = generator) :
    ConstructorMap Q accountSort base target generator where
  map := fun value => arrow.underlying.left.raw.map (project Q accountSort base value)
  map_gen := by
    intro Γ sort value
    exact congrArg (fun h : base ⟶ target.observed => h.left.raw.map value) agrees
  map_operation := by
    intro Γ sort op args
    exact (congrArg arrow.underlying.left.raw.map
      (operation_project Q accountSort base op args).symm).trans
      ((arrow.underlying.left.raw.map_operation op _).trans
        (congrArg (target.observed.left.operation op)
          (map_projectArguments Q accountSort base arrow.underlying.left.raw.map args)))
  map_account := by
    intro Γ sort word value
    exact arrow.map_act word (project Q accountSort base value)
  map_substitute := by
    intro Γ Δ sort env value
    have mapped := arrow.underlying.left.map_substitute
      (fun s v => project Q accountSort base (env s v)) (project Q accountSort base value)
    exact (congrArg arrow.underlying.left.raw.map
      (substitute_represented Q accountSort base
        (fun s v => project Q accountSort base (env s v)) env
        (by intro _ _; rfl) (project Q accountSort base value)).symm).trans
      mapped

/-- Every genuine accounted clone extension is the descended structural
fold.  This proves uniqueness on all marked values, not only on generators. -/
theorem extend_unique (arrow : model Q accountSort base ⟶ target)
    (agrees : FreeAccountBindingModel.unit Q accountSort base ≫
      (AccountBindingAlgebra.forget Q accountSort).map arrow = generator) :
    arrow = extend Q accountSort base target generator := by
  apply AccountBindingAlgebra.Hom.ext
  apply Over.OverMorphism.ext
  apply FreeBindingClone.Hom.ext
  apply FreeBindingTerms.Hom.ext
  intro Γ sort value
  induction value using Quotient.inductionOn with
  | _ raw =>
    exact constructorMap_unique Q accountSort base target generator
      (constructorMapOfHom Q accountSort base target generator arrow agrees) raw

/-- Genuine hom-set equivalence for the proposed free/forget construction. -/
noncomputable def homEquiv :
    (model Q accountSort base ⟶ target) ≃
      (base ⟶ (AccountBindingAlgebra.forget Q accountSort).obj target) where
  toFun arrow := FreeAccountBindingModel.unit Q accountSort base ≫
    (AccountBindingAlgebra.forget Q accountSort).map arrow
  invFun := extend Q accountSort base target
  left_inv arrow := (extend_unique Q accountSort base target _ arrow rfl).symm
  right_inv := extend_unit Q accountSort base target

end Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingExtension
