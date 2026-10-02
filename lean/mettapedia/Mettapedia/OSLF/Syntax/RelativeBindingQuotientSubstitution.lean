import Mettapedia.OSLF.Syntax.RelativeBindingCongruence

/-!
# Full substitution on relative binding classes

The validated relative congruence is quotiented at each typed context and
sort. A substitution environment supplies entire quotient classes, including
new operators beneath binders. Representative choices do not affect the
operation, by pointwise full-environment congruence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RelativeBindingQuotientSubstitution

open FreeBindingTerms BindingSubstitutionAlgebra SecondOrderContext
open RawRelativeBindingExtension RawRelativeBindingLaws RelativeBindingCongruence

universe u

variable {S : Signature} (extension : Object S)
  (base : BindingCloneAlgebra.Algebra.{u} S)
  (family : EqAxiom (withMetas S extension.arities) [] → Prop)

abbrev Carrier (Γ : Ctx S) (sort : S.Srt) : Type u :=
  Quotient (RelativeBindingCongruence.setoid extension base family Γ sort)

def project {Γ : Ctx S} {sort : S.Srt} (value : Raw extension base Γ sort) :
    Carrier extension base family Γ sort := Quotient.mk _ value

theorem project_equation {Γ : Ctx S} {sort : S.Srt} {left right : Raw extension base Γ sort}
    (witness : Equation extension base family left right) :
    project extension base family left = project extension base family right :=
  Quotient.sound ⟨Derivation.equation witness⟩

theorem project_derivation {Γ : Ctx S} {sort : S.Srt} {left right : Raw extension base Γ sort}
    (witness : Derivation extension base family left right) :
    project extension base family left = project extension base family right := Quotient.sound ⟨witness⟩

noncomputable def representativeEnv {Γ Δ : Ctx S}
    (environment : Environment (withMetas S extension.arities) (Carrier (S := S) extension base family) Γ Δ) :
    Environment S (Raw extension base) Γ Δ := fun sort index => Quotient.out (environment sort index)

theorem project_representativeEnv {Γ Δ : Ctx S}
    (environment : Environment (withMetas S extension.arities) (Carrier (S := S) extension base family) Γ Δ)
    (sort : S.Srt) (index : Var Γ sort) :
    project extension base family (representativeEnv extension base family environment sort index) =
      environment sort index := Quotient.out_eq _

def substituteRaw {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Environment S (Raw extension base) Γ Δ) :
    Carrier extension base family Γ sort → Carrier extension base family Δ sort :=
  Quotient.lift (fun value => project extension base family (.substitute environment value))
    (by
      intro left right related
      rcases related with ⟨witness⟩
      exact project_derivation extension base family
        (.substitute (fun _ _ => .refl _) witness))

theorem substituteRaw_project {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Environment S (Raw extension base) Γ Δ) (value : Raw extension base Γ sort) :
    substituteRaw extension base family environment (project extension base family value) =
      project extension base family (.substitute environment value) := rfl

noncomputable def substitute {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Environment (withMetas S extension.arities) (Carrier (S := S) extension base family) Γ Δ)
    (value : Carrier extension base family Γ sort) : Carrier extension base family Δ sort :=
  substituteRaw extension base family (representativeEnv extension base family environment) value

theorem substituteRaw_environment_congr {Γ Δ : Ctx S} {sort : S.Srt}
    (first second : Environment S (Raw extension base) Γ Δ)
    (agree : ∀ sort index, project extension base family (first sort index) =
      project extension base family (second sort index))
    (value : Carrier extension base family Γ sort) :
    substituteRaw extension base family first value = substituteRaw extension base family second value := by
  classical
  induction value using Quotient.inductionOn with
  | _ raw =>
      exact project_derivation extension base family
        (.substitute (fun sort index => Classical.choice (Quotient.exact (agree sort index))) (.refl raw))

theorem substitute_represented {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Environment (withMetas S extension.arities) (Carrier (S := S) extension base family) Γ Δ)
    (rawEnvironment : Environment S (Raw extension base) Γ Δ)
    (agree : ∀ sort index, project extension base family (rawEnvironment sort index) =
      environment sort index) (value : Carrier extension base family Γ sort) :
    substitute extension base family environment value =
      substituteRaw extension base family rawEnvironment value := by
  apply substituteRaw_environment_congr extension base family
  intro sort index
  exact (project_representativeEnv extension base family environment sort index).trans
    (agree sort index).symm

theorem substitute_var {Γ Δ : Ctx S} {sort : S.Srt}
    (environment : Environment (withMetas S extension.arities) (Carrier (S := S) extension base family) Γ Δ)
    (index : Var Γ sort) :
    substitute extension base family environment
        (project extension base family (injectVariable extension base index)) = environment sort index := by
  exact (project_equation extension base family
    (.substituteVariable (representativeEnv extension base family environment) index)).trans
      (project_representativeEnv extension base family environment sort index)

theorem substitute_identity {Γ : Ctx S} {sort : S.Srt}
    (value : Carrier extension base family Γ sort) :
    substitute extension base family
        (fun _ index => project extension base family (injectVariable extension base index)) value =
      value := by
  rw [substitute_represented extension base family _
    (fun _ index => injectVariable extension base index) (by intro _ _; rfl)]
  induction value using Quotient.inductionOn with
  | _ raw => exact project_equation extension base family (.substituteIdentity raw)

theorem substitute_comp {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (first : Environment (withMetas S extension.arities) (Carrier (S := S) extension base family) Γ Δ)
    (second : Environment (withMetas S extension.arities) (Carrier (S := S) extension base family) Δ Θ)
    (value : Carrier extension base family Γ sort) :
    substitute extension base family second (substitute extension base family first value) =
      substitute extension base family
        (fun sort index => substitute extension base family second (first sort index)) value := by
  have represented : ∀ sort index,
      project extension base family (.substitute (representativeEnv extension base family second)
        (representativeEnv extension base family first sort index)) =
        substitute extension base family second (first sort index) := by
    intro sort index
    change substituteRaw extension base family (representativeEnv extension base family second)
        (project extension base family (representativeEnv extension base family first sort index)) = _
    rw [project_representativeEnv]
    rfl
  rw [substitute_represented extension base family _ _ represented]
  induction value using Quotient.inductionOn with
  | _ raw =>
      exact project_equation extension base family
        (.substituteComp (representativeEnv extension base family first)
          (representativeEnv extension base family second) raw)

noncomputable def algebra : BindingSubstitutionAlgebra.Algebra.{u} (withMetas S extension.arities) where
  Carrier := Carrier (S := S) extension base family
  injectVar := fun index => project extension base family (injectVariable extension base index)
  substitute := substitute extension base family
  substitute_var := by
    intro Γ Δ environment sort index
    exact substitute_var extension base family environment index
  substitute_identity := substitute_identity extension base family
  substitute_comp := substitute_comp extension base family

theorem weaken_project {Γ : Ctx S} {sort fresh : S.Srt} (value : Raw extension base Γ sort) :
    (algebra extension base family).weaken (fresh := fresh) (project extension base family value) =
      project extension base family (RawRelativeBindingLaws.weaken extension base value) := by
  change substitute extension base family
      (fun _ index => project extension base family (injectVariable extension base (.succ index)))
      (project extension base family value) = _
  exact substitute_represented extension base family _
    (fun _ index => injectVariable extension base (.succ index)) (by intro _ _; rfl)
    (project extension base family value)

theorem liftEnvironment_represented {Γ Δ : Ctx S}
    (environment : Environment (withMetas S extension.arities) (Carrier (S := S) extension base family) Γ Δ) :
    ∀ binders sort (index : Var (binders ++ Γ) sort),
      project extension base family
          (RawRelativeBindingLaws.liftEnvironment extension base
            (representativeEnv extension base family environment) binders sort index) =
        (algebra extension base family).liftEnvironment environment binders sort index
  | [], sort, index => project_representativeEnv extension base family environment sort index
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ old => by
      change project extension base family (RawRelativeBindingLaws.weaken extension base _) =
        (algebra extension base family).weaken
          ((algebra extension base family).liftEnvironment environment binders sort old)
      rw [← liftEnvironment_represented environment binders sort old, weaken_project]

end Mettapedia.OSLF.Binding.RelativeBindingQuotientSubstitution
