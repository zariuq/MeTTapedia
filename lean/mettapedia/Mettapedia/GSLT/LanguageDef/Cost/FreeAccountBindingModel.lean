import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientModel

/-!
# Relative occurrence-local account model and its generator map

The quotient binding clone carries the validated local account action and
the full source observation.  Its generator map is an actual morphism of
binding clones over the source.  The universal extension into arbitrary
accounted models is constructed separately.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open FreeBindingTerms
open RawAccountBindingExtension
open RawAccountBindingLaws
open AccountBindingCongruence
open AccountBindingQuotientSubstitution
open AccountBindingQuotientModel

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S)
  (accountSort : S.Srt) (base : Over Q)

/-- The observation is well-defined by structural soundness of every raw
congruence derivation; it forgets accounts but keeps source meaning. -/
def observation {Γ : Ctx S} {sort : S.Srt} :
    Carrier Q accountSort base Γ sort → Q.substitution.Carrier Γ sort :=
  Quotient.lift (observe Q accountSort base) (by
    intro left right related
    rcases related with ⟨witness⟩
    exact derivation_observe Q accountSort base witness)

theorem observation_project {Γ : Ctx S} {sort : S.Srt}
    (value : Raw Q accountSort base Γ sort) :
    observation Q accountSort base (project Q accountSort base value) =
      observe Q accountSort base value := rfl

theorem observe_representativeEnv {Γ Δ : Ctx S}
    (env : Environment S (Carrier Q accountSort base) Γ Δ) :
    (fun s v => observe Q accountSort base
      (representativeEnv Q accountSort base env s v)) =
      (fun s v => observation Q accountSort base (env s v)) := by
  funext sort v
  exact congrArg (observation Q accountSort base)
    (project_representativeEnv Q accountSort base env sort v)

theorem observe_representativeArgs :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S (Carrier Q accountSort base) arities Γ),
      observeArguments Q accountSort base (representativeArgs Q accountSort base args) =
        FamilyArgs.map (observation Q accountSort base) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg₂ FamilyArgs.cons
      (congrArg (observation Q accountSort base) (Quotient.out_eq head))
      (observe_representativeArgs tail)

theorem observation_substitute {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier Q accountSort base) Γ Δ)
    (value : Carrier Q accountSort base Γ sort) :
    observation Q accountSort base (substitute Q accountSort base env value) =
      Q.substitution.substitute (fun s v => observation Q accountSort base (env s v))
        (observation Q accountSort base value) := by
  induction value using Quotient.inductionOn with
  | _ raw =>
      change Q.substitution.substitute
        (fun s v => observe Q accountSort base (representativeEnv Q accountSort base env s v))
        (observe Q accountSort base raw) = _
      exact congrArg (fun values => Q.substitution.substitute values
        (observe Q accountSort base raw)) (observe_representativeEnv Q accountSort base env)

/-- Full source observation preserves every operator and arbitrary marked
semantic substitution, not just the injected generator image. -/
noncomputable def observationHom :
    FreeBindingClone.Hom (AccountBindingQuotientModel.algebra Q accountSort base) Q where
  raw :=
    { map := observation Q accountSort base
      map_variable := by
        intro Γ sort v
        exact base.hom.raw.map_variable v
      map_operation := by
        intro Γ sort op args
        exact congrArg (Q.operation op) (observe_representativeArgs Q accountSort base args) }
  map_substitute := observation_substitute Q accountSort base

/-- Local action descends by the explicit account congruence. -/
def act {Γ : Ctx S} {sort : S.Srt}
    (word : SourceAccountSubstitution.Account Q accountSort Γ) :
    Carrier Q accountSort base Γ sort → Carrier Q accountSort base Γ sort :=
  Quotient.lift (fun value => project Q accountSort base (.account word value))
    (by
      intro left right related
      rcases related with ⟨witness⟩
      exact project_derivation Q accountSort base (.account word witness))

theorem act_project {Γ : Ctx S} {sort : S.Srt}
    (word : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Raw Q accountSort base Γ sort) :
    act Q accountSort base word (project Q accountSort base value) =
      project Q accountSort base (.account word value) := rfl

theorem act_one {Γ : Ctx S} {sort : S.Srt}
    (value : Carrier Q accountSort base Γ sort) : act Q accountSort base 1 value = value := by
  induction value using Quotient.inductionOn with
  | _ raw => exact project_equation Q accountSort base (.accountOne raw)

theorem act_mul {Γ : Ctx S} {sort : S.Srt}
    (first second : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Carrier Q accountSort base Γ sort) :
    act Q accountSort base (first * second) value =
      act Q accountSort base first (act Q accountSort base second value) := by
  induction value using Quotient.inductionOn with
  | _ raw => exact project_equation Q accountSort base (.accountMul first second raw)

theorem observation_act {Γ : Ctx S} {sort : S.Srt}
    (word : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Carrier Q accountSort base Γ sort) :
    observation Q accountSort base (act Q accountSort base word value) =
      observation Q accountSort base value := by
  induction value using Quotient.inductionOn with
  | _ raw => rfl

theorem act_substitute {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier Q accountSort base) Γ Δ)
    (word : SourceAccountSubstitution.Account Q accountSort Γ)
    (value : Carrier Q accountSort base Γ sort) :
    substitute Q accountSort base env (act Q accountSort base word value) =
      act Q accountSort base (SourceAccountSubstitution.substitute Q accountSort
        (fun s v => observation Q accountSort base (env s v)) word)
        (substitute Q accountSort base env value) := by
  induction value using Quotient.inductionOn with
  | _ raw =>
      have sound := project_equation Q accountSort base
        (.substituteAccount (representativeEnv Q accountSort base env) word raw)
      change project Q accountSort base (.substitute _ (.account word raw)) =
        project Q accountSort base (.account _ (.substitute _ raw))
      rw [← observe_representativeEnv Q accountSort base env]
      exact sound

/-- The concrete relative accounted binding model.  Source equations are
observed through `Q`; they are not separately appended to the raw relation. -/
noncomputable def model : AccountBindingAlgebra.Model Q accountSort where
  observed := Over.mk (observationHom Q accountSort base)
  act := act Q accountSort base
  act_one := act_one Q accountSort base
  act_mul := act_mul Q accountSort base
  observe_act := observation_act Q accountSort base
  act_substitute := act_substitute Q accountSort base

theorem project_genArguments :
    ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
      (args : FamilyArgs S base.left.substitution.Carrier arities Γ),
      projectArguments Q accountSort base (genArguments Q accountSort base args) =
        FamilyArgs.map (fun {_Γ _sort} value =>
          project Q accountSort base (.gen value)) args
  | _, _, .nil => rfl
  | _, _, .cons head tail => congrArg (FamilyArgs.cons
      (project Q accountSort base (.gen head))) (project_genArguments tail)

/-- Injecting the base clone preserves its full substitution, using the
validated generator equations rather than erased marked environments. -/
noncomputable def generatorHom :
    FreeBindingClone.Hom base.left (AccountBindingQuotientModel.algebra Q accountSort base) where
  raw :=
    { map := fun value => project Q accountSort base (.gen value)
      map_variable := by intro Γ sort v; rfl
      map_operation := by
        intro Γ sort op args
        exact (project_equation Q accountSort base (.genOperation op args)).trans
          (operation_represented Q accountSort base op _ _
            (project_genArguments Q accountSort base args)).symm }
  map_substitute := by
    intro Γ Δ sort env value
    exact (project_equation Q accountSort base (.genSubstitute env value)).trans
      (substitute_represented Q accountSort base _ (fun s v => .gen (env s v))
        (by intro _ _; rfl) (project Q accountSort base (.gen value))).symm

/-- The genuine over-source generator morphism retains the entire base
binding clone when only the account action is forgotten. -/
noncomputable def unit : base ⟶
    (AccountBindingAlgebra.forget Q accountSort).obj (model Q accountSort base) :=
  Over.homMk (generatorHom Q accountSort base) (by
    apply FreeBindingClone.Hom.ext
    exact FreeBindingTerms.Hom.ext (fun _ => rfl))

end Mettapedia.GSLT.LanguageDef.Cost.FreeAccountBindingModel
