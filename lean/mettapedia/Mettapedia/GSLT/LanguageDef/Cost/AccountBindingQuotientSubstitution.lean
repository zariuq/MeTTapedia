import Mettapedia.GSLT.LanguageDef.Cost.AccountBindingCongruence

/-!
# Simultaneous substitution of relative account classes

The validated raw congruence is quotiented in each typed context.  A semantic
environment supplies whole accounted classes.  Choosing representatives is
independent of those choices, by the raw substitution congruence; no marked
environment is projected to unaccounted base values.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open BindingSubstitutionAlgebra
open RawAccountBindingExtension
open RawAccountBindingLaws
open AccountBindingCongruence

universe u

variable {S : Signature} (Q : BindingCloneAlgebra.Algebra.{u} S)
  (accountSort : S.Srt) (base : Over Q)

abbrev Carrier (Γ : Ctx S) (sort : S.Srt) : Type u :=
  Quotient (AccountBindingCongruence.setoid Q accountSort base Γ sort)

/-- Quotient projection, with the original expression still available to
clients that retain an origin certificate. -/
def project {Γ : Ctx S} {sort : S.Srt}
    (value : Raw Q accountSort base Γ sort) : Carrier Q accountSort base Γ sort :=
  Quotient.mk _ value

theorem project_equation {Γ : Ctx S} {sort : S.Srt}
    {left right : Raw Q accountSort base Γ sort}
    (witness : Equation Q accountSort base left right) :
    project Q accountSort base left = project Q accountSort base right :=
  Quotient.sound ⟨Derivation.equation witness⟩

theorem project_derivation {Γ : Ctx S} {sort : S.Srt}
    {left right : Raw Q accountSort base Γ sort}
    (witness : Derivation Q accountSort base left right) :
    project Q accountSort base left = project Q accountSort base right :=
  Quotient.sound ⟨witness⟩

/-- The complete raw representative of every supplied marked value. -/
noncomputable def representativeEnv {Γ Δ : Ctx S}
    (env : Environment S (Carrier Q accountSort base) Γ Δ) :
    Environment S (Raw Q accountSort base) Γ Δ :=
  fun sort v => Quotient.out (env sort v)

theorem project_representativeEnv {Γ Δ : Ctx S}
    (env : Environment S (Carrier Q accountSort base) Γ Δ)
    (sort : S.Srt) (v : Var Γ sort) :
    project Q accountSort base (representativeEnv Q accountSort base env sort v) =
      env sort v := Quotient.out_eq _

/-- Raw environments act on classes by a well-defined explicit substitution
node.  Its environment fields are retained without an erasure step. -/
def substituteRaw {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Raw Q accountSort base) Γ Δ) :
    Carrier Q accountSort base Γ sort → Carrier Q accountSort base Δ sort :=
  Quotient.lift (fun value => project Q accountSort base (.substitute env value))
    (by
      intro left right related
      rcases related with ⟨witness⟩
      exact project_derivation Q accountSort base
        (.substitute (fun _ _ => .refl _) witness))

theorem substituteRaw_project {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Raw Q accountSort base) Γ Δ)
    (value : Raw Q accountSort base Γ sort) :
    substituteRaw Q accountSort base env (project Q accountSort base value) =
      project Q accountSort base (.substitute env value) := rfl

/-- Quotient-valued simultaneous substitution uses the entire supplied
environment. -/
noncomputable def substitute {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier Q accountSort base) Γ Δ)
    (value : Carrier Q accountSort base Γ sort) : Carrier Q accountSort base Δ sort :=
  substituteRaw Q accountSort base (representativeEnv Q accountSort base env) value

theorem substituteRaw_environment_congr {Γ Δ : Ctx S} {sort : S.Srt}
    (first second : Environment S (Raw Q accountSort base) Γ Δ)
    (agree : ∀ s v, project Q accountSort base (first s v) =
      project Q accountSort base (second s v))
    (value : Carrier Q accountSort base Γ sort) :
    substituteRaw Q accountSort base first value =
      substituteRaw Q accountSort base second value := by
  classical
  induction value using Quotient.inductionOn with
  | _ raw =>
      exact project_derivation Q accountSort base
        (.substitute (fun s v => Classical.choice (Quotient.exact (agree s v))) (.refl raw))

/-- An arbitrary displayed environment may be used in place of the chosen
representatives whenever it represents those same whole classes. -/
theorem substitute_represented {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier Q accountSort base) Γ Δ)
    (rawEnv : Environment S (Raw Q accountSort base) Γ Δ)
    (agree : ∀ s v, project Q accountSort base (rawEnv s v) = env s v)
    (value : Carrier Q accountSort base Γ sort) :
    substitute Q accountSort base env value =
      substituteRaw Q accountSort base rawEnv value := by
  apply substituteRaw_environment_congr Q accountSort base
  intro sort v
  exact (project_representativeEnv Q accountSort base env sort v).trans (agree sort v).symm

theorem substitute_var {Γ Δ : Ctx S} {sort : S.Srt}
    (env : Environment S (Carrier Q accountSort base) Γ Δ) (v : Var Γ sort) :
    substitute Q accountSort base env
        (project Q accountSort base (sourceVariable Q accountSort base v)) = env sort v := by
  exact (project_equation Q accountSort base
    (.substituteVariable (representativeEnv Q accountSort base env) v)).trans
      (project_representativeEnv Q accountSort base env sort v)

theorem substitute_identity {Γ : Ctx S} {sort : S.Srt}
    (value : Carrier Q accountSort base Γ sort) :
    substitute Q accountSort base
        (fun _ v => project Q accountSort base (sourceVariable Q accountSort base v))
        value = value := by
  rw [substitute_represented Q accountSort base _
    (fun _ v => sourceVariable Q accountSort base v) (by intro _ _; rfl)]
  induction value using Quotient.inductionOn with
  | _ raw => exact project_equation Q accountSort base (.substituteIdentity raw)

theorem substitute_comp {Γ Δ Θ : Ctx S} {sort : S.Srt}
    (first : Environment S (Carrier Q accountSort base) Γ Δ)
    (second : Environment S (Carrier Q accountSort base) Δ Θ)
    (value : Carrier Q accountSort base Γ sort) :
    substitute Q accountSort base second (substitute Q accountSort base first value) =
      substitute Q accountSort base
        (fun s v => substitute Q accountSort base second (first s v)) value := by
  have represented : ∀ s v,
      project Q accountSort base (.substitute (representativeEnv Q accountSort base second)
        (representativeEnv Q accountSort base first s v)) =
        substitute Q accountSort base second (first s v) := by
    intro s v
    change substituteRaw Q accountSort base (representativeEnv Q accountSort base second)
        (project Q accountSort base (representativeEnv Q accountSort base first s v)) = _
    rw [project_representativeEnv]
    rfl
  rw [substitute_represented Q accountSort base _ _ represented]
  induction value using Quotient.inductionOn with
  | _ raw =>
    exact project_equation Q accountSort base
      (.substituteComp (representativeEnv Q accountSort base first)
        (representativeEnv Q accountSort base second) raw)

/-- The validated quotient fibres form a full substitution clone. -/
noncomputable def algebra : BindingSubstitutionAlgebra.Algebra.{u} S where
  Carrier := Carrier Q accountSort base
  injectVar := fun v => project Q accountSort base (sourceVariable Q accountSort base v)
  substitute := substitute Q accountSort base
  substitute_var := by
    intro Γ Δ env sort v
    exact substitute_var Q accountSort base env v
  substitute_identity := substitute_identity Q accountSort base
  substitute_comp := substitute_comp Q accountSort base

theorem weaken_project {Γ : Ctx S} {sort fresh : S.Srt}
    (value : Raw Q accountSort base Γ sort) :
    (algebra Q accountSort base).weaken (fresh := fresh) (project Q accountSort base value) =
      project Q accountSort base (RawAccountBindingLaws.weaken Q accountSort base value) := by
  change substitute Q accountSort base
      (fun _ v => project Q accountSort base (sourceVariable Q accountSort base (.succ v)))
      (project Q accountSort base value) = _
  exact substitute_represented Q accountSort base _
    (fun _ v => sourceVariable Q accountSort base (.succ v)) (by intro _ _; rfl)
    (project Q accountSort base value)

/-- The semantic binder lift agrees with the class of the raw full-value
lift at every bound and free variable. -/
theorem liftEnvironment_represented {Γ Δ : Ctx S}
    (env : Environment S (Carrier Q accountSort base) Γ Δ) :
    ∀ binders sort (v : Var (binders ++ Γ) sort),
      project Q accountSort base
          (RawAccountBindingLaws.liftEnvironment Q accountSort base
            (representativeEnv Q accountSort base env) binders sort v) =
        (algebra Q accountSort base).liftEnvironment env binders sort v
  | [], sort, v => project_representativeEnv Q accountSort base env sort v
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ old => by
      change project Q accountSort base (RawAccountBindingLaws.weaken Q accountSort base _) =
        (algebra Q accountSort base).weaken
          ((algebra Q accountSort base).liftEnvironment env binders sort old)
      rw [← liftEnvironment_represented env binders sort old, weaken_project]

end Mettapedia.GSLT.LanguageDef.Cost.AccountBindingQuotientSubstitution
