import Mettapedia.Languages.MeTTa.PureKernel.RegularNormalizationBoundary
import Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation

/-!
# A constructor-faithful skeleton for tower conversion

The cumulative presentation adds explicit universe heads and semantic equality
between level expressions, but its computational term constructors are the
same as those of the regular Pure kernel.  This module forgets only the choice
of universe head and transports tower conversion to ordinary beta conversion.

The transport is intentionally one-way.  It is used to prove structural
negative facts: two tower terms whose erased constructor skeletons are distinct
normal forms cannot be convertible.  It makes no claim that erasure reflects
typing or universe equality.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation

namespace TowerConversionSkeleton

open Mettapedia.Languages.MeTTa.PureKernel
open Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

/-- Forget the identity of a tower head while retaining every computational
constructor, binder, variable, and declaration constant. -/
def erase : Tower.Tm n → Syntax.PureTm n
  | .var index => .var index
  | .const name => .const name
  | .head _ => .u0
  | .pi domain codomain => .pi (erase domain) (erase codomain)
  | .sigma domain codomain => .sigma (erase domain) (erase codomain)
  | .id carrier left right => .id (erase carrier) (erase left) (erase right)
  | .lam body => .lam (erase body)
  | .app function argument => .app (erase function) (erase argument)
  | .pair first second => .pair (erase first) (erase second)
  | .fst pair => .fst (erase pair)
  | .snd pair => .snd (erase pair)
  | .refl term => .refl (erase term)

private theorem old_liftRen_eq (rnm : Ren n m) :
    Mettapedia.Languages.MeTTa.PureKernel.Renaming.liftRen rnm =
      liftRen rnm := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro earlier
    rfl

/-- Skeleton erasure commutes with term-variable renaming. -/
@[simp] theorem erase_rename (rnm : Ren n m) (term : Tower.Tm n) :
    erase (Presentation.rename rnm term) =
      Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename rnm
        (erase term) := by
  induction term generalizing m with
  | var index => rfl
  | const name => rfl
  | head head => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename,
        ihDomain, old_liftRen_eq, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename,
        ihDomain, old_liftRen_eq, ihCodomain]
  | id carrier left right ihCarrier ihLeft ihRight =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename,
        ihCarrier, ihLeft, ihRight]
  | lam body ihBody =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename,
        old_liftRen_eq, ihBody]
  | app function argument ihFunction ihArgument =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename,
        ihFunction, ihArgument]
  | pair first second ihFirst ihSecond =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename,
        ihFirst, ihSecond]
  | fst pair ihPair =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename, ihPair]
  | snd pair ihPair =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename, ihPair]
  | refl term ihTerm =>
      simp only [Presentation.rename, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename, ihTerm]

private theorem erase_liftSub (sigma : Sub Tower.Head n m) :
    (fun index => erase (liftSub sigma index)) =
      Mettapedia.Languages.MeTTa.PureKernel.Substitution.liftSub
        (fun index => erase (sigma index)) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro earlier
    exact erase_rename wk (sigma earlier)

/-- Skeleton erasure commutes with simultaneous substitution. -/
@[simp] theorem erase_subst (sigma : Sub Tower.Head n m)
    (term : Tower.Tm n) :
    erase (Presentation.subst sigma term) =
      Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst
        (fun index => erase (sigma index)) (erase term) := by
  induction term generalizing m with
  | var index => rfl
  | const name => rfl
  | head head => rfl
  | pi domain codomain ihDomain ihCodomain =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst,
        ihDomain, erase_liftSub, ihCodomain]
  | sigma domain codomain ihDomain ihCodomain =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst,
        ihDomain, erase_liftSub, ihCodomain]
  | id carrier left right ihCarrier ihLeft ihRight =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst,
        ihCarrier, ihLeft, ihRight]
  | lam body ihBody =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst,
        erase_liftSub, ihBody]
  | app function argument ihFunction ihArgument =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst,
        ihFunction, ihArgument]
  | pair first second ihFirst ihSecond =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst,
        ihFirst, ihSecond]
  | fst pair ihPair =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst, ihPair]
  | snd pair ihPair =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst, ihPair]
  | refl term ihTerm =>
      simp only [Presentation.subst, erase,
        Mettapedia.Languages.MeTTa.PureKernel.Substitution.subst, ihTerm]

/-- Skeleton erasure commutes with opening one binder. -/
@[simp] theorem erase_inst0 (argument : Tower.Tm n)
    (body : Tower.Tm (n + 1)) :
    erase (Presentation.inst0 argument body) =
      Mettapedia.Languages.MeTTa.PureKernel.Substitution.inst0
        (erase argument) (erase body) := by
  rw [Presentation.inst0,
    Mettapedia.Languages.MeTTa.PureKernel.Substitution.inst0,
    erase_subst]
  congr 1
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro earlier
    rfl

private theorem redStar_congIdTy
    {carrier carrier' left right : Syntax.PureTm n}
    (steps : Reduction.RedStar carrier carrier') :
    Reduction.RedStar (.id carrier left right) (.id carrier' left right) :=
  Reduction.RedStar.map
    (F := fun term => .id term left right)
    (fun step => .congIdTy step) steps

private theorem redStar_congIdLeft
    {carrier left left' right : Syntax.PureTm n}
    (steps : Reduction.RedStar left left') :
    Reduction.RedStar (.id carrier left right) (.id carrier left' right) :=
  Reduction.RedStar.map
    (F := fun term => .id carrier term right)
    (fun step => .congIdLeft step) steps

private theorem redStar_congIdRight
    {carrier left right right' : Syntax.PureTm n}
    (steps : Reduction.RedStar right right') :
    Reduction.RedStar (.id carrier left right) (.id carrier left right') :=
  Reduction.RedStar.map
    (F := fun term => .id carrier left term)
    (fun step => .congIdRight step) steps

/-- A tower computation or head-equality step becomes zero or more ordinary
Pure beta steps after erasing the universe-head identity. -/
theorem step_erases {left right : Tower.Tm n}
    (step : Step Tower.HeadEq left right) :
    Reduction.RedStar (erase left) (erase right) := by
  induction step with
  | betaPi body argument =>
      simpa only [erase, erase_inst0] using
        (Reduction.red_to_redStar
          (Reduction.Red.betaPi (erase body) (erase argument)))
  | betaSigmaFst first second =>
      exact Reduction.red_to_redStar
        (Reduction.Red.betaSigmaFst (erase first) (erase second))
  | betaSigmaSnd first second =>
      exact Reduction.red_to_redStar
        (Reduction.Red.betaSigmaSnd (erase first) (erase second))
  | head headEquality => exact Reduction.RedStar.refl _
  | root impossible => exact False.elim impossible
  | congPiDom inner ih => exact Reduction.RedStar.congPiDom ih
  | congPiCod inner ih => exact Reduction.RedStar.congPiCod ih
  | congSigmaDom inner ih => exact Reduction.RedStar.congSigmaDom ih
  | congSigmaCod inner ih => exact Reduction.RedStar.congSigmaCod ih
  | congIdTy inner ih => exact redStar_congIdTy ih
  | congIdLeft inner ih => exact redStar_congIdLeft ih
  | congIdRight inner ih => exact redStar_congIdRight ih
  | congLam inner ih => exact Reduction.RedStar.congLam ih
  | congAppFun inner ih => exact Reduction.RedStar.congAppFun ih
  | congAppArg inner ih => exact Reduction.RedStar.congAppArg ih
  | congPairFst inner ih => exact Reduction.RedStar.congPairFst ih
  | congPairSnd inner ih => exact Reduction.RedStar.congPairSnd ih
  | congFst inner ih => exact Reduction.RedStar.congFst ih
  | congSnd inner ih => exact Reduction.RedStar.congSnd ih
  | congRefl inner ih => exact Reduction.RedStar.congRefl ih

/-- Tower conversion cannot identify more computational constructor skeletons
than ordinary beta conversion does. -/
theorem conv_erases {left right : Tower.Tm n}
    (conversion : Conv Tower.HeadEq left right) :
    Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv
      (erase left) (erase right) := by
  induction conversion with
  | rel left right step =>
      exact Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_implies_conv
        (step_erases step)
  | refl term => exact Relation.EqvGen.refl _
  | symm left right relation ih => exact Relation.EqvGen.symm _ _ ih
  | trans left middle right first second ihFirst ihSecond =>
      exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- Distinct ordinary normal-form skeletons certify non-convertibility in the
tower. -/
theorem erase_eq_of_conv {left right : Tower.Tm n}
    (leftNormal : RedNormal (erase left))
    (rightNormal : RedNormal (erase right))
    (conversion : Conv Tower.HeadEq left right) :
    erase left = erase right := by
  exact normalForms_eq_of_conv
    (Reduction.RedStar.refl _) (Reduction.RedStar.refl _)
    leftNormal rightNormal (conv_erases conversion)

theorem not_conv_of_normal_erase_ne {left right : Tower.Tm n}
    (leftNormal : RedNormal (erase left))
    (rightNormal : RedNormal (erase right))
    (distinct : erase left ≠ erase right) :
    ¬ Conv Tower.HeadEq left right := by
  intro conversion
  exact distinct (erase_eq_of_conv leftNormal rightNormal conversion)

/-! ## Constructor separation and identity injectivity -/

private theorem old_redStar_u0_eq {target : Syntax.PureTm n}
    (steps : Reduction.RedStar .u0 target) : target = .u0 := by
  apply RedNormal.redStar_eq (term := (.u0 : Syntax.PureTm n))
  · intro reduct step
    cases step
  · exact steps

/-- A dependent-function type cannot convert to a universe head.  No
normality premise on its components is needed: reduction preserves the outer
`Pi` constructor. -/
theorem not_conv_pi_head (domain : Tower.Tm n)
    (codomain : Tower.Tm (n + 1)) (head : Tower.Head) :
    ¬ Conv Tower.HeadEq (.pi domain codomain) (.head head) := by
  intro conversion
  have erased := conv_erases conversion
  rcases Mettapedia.Languages.MeTTa.PureKernel.Confluence.church_rosser_conv
      erased with ⟨common, piSteps, headSteps⟩
  rcases Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_pi_head
      piSteps with ⟨domain', codomain', commonShape⟩
  have commonHead : common = (.u0 : Syntax.PureTm n) :=
    old_redStar_u0_eq headSteps
  rw [commonHead] at commonShape
  cases commonShape

/-- Dependent-function and dependent-pair constructors remain disjoint under
tower conversion. -/
theorem not_conv_pi_sigma (piDomain : Tower.Tm n)
    (piCodomain : Tower.Tm (n + 1)) (sigmaDomain : Tower.Tm n)
    (sigmaCodomain : Tower.Tm (n + 1)) :
    ¬ Conv Tower.HeadEq (.pi piDomain piCodomain)
      (.sigma sigmaDomain sigmaCodomain) := by
  intro conversion
  have erased := conv_erases conversion
  rcases Mettapedia.Languages.MeTTa.PureKernel.Confluence.church_rosser_conv
      erased with ⟨common, piSteps, sigmaSteps⟩
  rcases Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_pi_head
      piSteps with ⟨piDomain', piCodomain', piShape⟩
  rcases Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_sigma_head
      sigmaSteps with ⟨sigmaDomain', sigmaCodomain', sigmaShape⟩
  rw [piShape] at sigmaShape
  cases sigmaShape

/-- `Pi` conversion preserves domain and codomain conversion after erasing
only the choice of tower universe head. -/
theorem pi_components_of_conv
    {domain domain' : Tower.Tm n}
    {codomain codomain' : Tower.Tm (n + 1)}
    (conversion : Conv Tower.HeadEq
      (.pi domain codomain) (.pi domain' codomain')) :
    Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv
        (erase domain) (erase domain') ∧
      Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv
        (erase codomain) (erase codomain') :=
  Mettapedia.Languages.MeTTa.PureKernel.Confluence.pi_injectivity
    (conv_erases conversion)

private theorem old_red_id_head {carrier left right target : Syntax.PureTm n}
    (step : Reduction.Red (.id carrier left right) target) :
    ∃ carrier' left' right', target = .id carrier' left' right' := by
  cases step with
  | congIdTy inner => exact ⟨_, _, _, rfl⟩
  | congIdLeft inner => exact ⟨_, _, _, rfl⟩
  | congIdRight inner => exact ⟨_, _, _, rfl⟩

private theorem old_redStar_id_head
    {carrier left right target : Syntax.PureTm n}
    (steps : Reduction.RedStar (.id carrier left right) target) :
    ∃ carrier' left' right', target = .id carrier' left' right' := by
  induction steps with
  | refl => exact ⟨carrier, left, right, rfl⟩
  | tail earlier finalStep ih =>
      rcases ih with ⟨carrier', left', right', shape⟩
      rw [shape] at finalStep
      exact old_red_id_head finalStep

/-- An identity type cannot convert to a universe head. -/
theorem not_conv_id_head (carrier left right : Tower.Tm n)
    (head : Tower.Head) :
    ¬ Conv Tower.HeadEq (.id carrier left right) (.head head) := by
  intro conversion
  have erased := conv_erases conversion
  rcases Mettapedia.Languages.MeTTa.PureKernel.Confluence.church_rosser_conv
      erased with ⟨common, idSteps, headSteps⟩
  rcases old_redStar_id_head idSteps with
    ⟨carrier', left', right', commonShape⟩
  have commonHead : common = (.u0 : Syntax.PureTm n) :=
    old_redStar_u0_eq headSteps
  rw [commonHead] at commonShape
  cases commonShape

private theorem old_redStar_id_decomp_full
    {carrier left right target : Syntax.PureTm n}
    (steps : Reduction.RedStar (.id carrier left right) target) :
    ∃ carrier' left' right',
      target = .id carrier' left' right' ∧
      Reduction.RedStar carrier carrier' ∧
      Reduction.RedStar left left' ∧
      Reduction.RedStar right right' := by
  induction steps with
  | refl =>
      exact ⟨carrier, left, right, rfl, Reduction.RedStar.refl _,
        Reduction.RedStar.refl _, Reduction.RedStar.refl _⟩
  | tail earlier finalStep ih =>
      rcases ih with
        ⟨carrier', left', right', shape, carrierSteps, leftSteps, rightSteps⟩
      rw [shape] at finalStep
      cases finalStep with
      | congIdTy carrierStep =>
          exact ⟨_, _, _, rfl, Reduction.RedStar.tail carrierSteps carrierStep,
            leftSteps, rightSteps⟩
      | congIdLeft leftStep =>
          exact ⟨_, _, _, rfl, carrierSteps,
            Reduction.RedStar.tail leftSteps leftStep, rightSteps⟩
      | congIdRight rightStep =>
          exact ⟨_, _, _, rfl, carrierSteps, leftSteps,
            Reduction.RedStar.tail rightSteps rightStep⟩

private theorem old_redStar_id_decomp
    {carrier left right carrier' left' right' : Syntax.PureTm n}
    (steps : Reduction.RedStar (.id carrier left right)
      (.id carrier' left' right')) :
    Reduction.RedStar carrier carrier' ∧
      Reduction.RedStar left left' ∧ Reduction.RedStar right right' := by
  rcases old_redStar_id_decomp_full steps with
    ⟨commonCarrier, commonLeft, commonRight, shape,
      carrierSteps, leftSteps, rightSteps⟩
  simp at shape
  obtain ⟨rfl, rfl, rfl⟩ := shape
  exact ⟨carrierSteps, leftSteps, rightSteps⟩

/-- Ordinary identity conversion preserves all three components.  This local
generalization fills the identity analogue of the existing `Pi` and `Sigma`
injectivity theorems. -/
theorem pure_id_components_of_conv
    {carrier left right carrier' left' right' : Syntax.PureTm n}
    (conversion : Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv
      (.id carrier left right) (.id carrier' left' right')) :
    Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv carrier carrier' ∧
      Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv left left' ∧
      Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv right right' := by
  rcases Mettapedia.Languages.MeTTa.PureKernel.Confluence.church_rosser_conv
      conversion with ⟨common, firstSteps, secondSteps⟩
  rcases old_redStar_id_head firstSteps with
    ⟨commonCarrier, commonLeft, commonRight, commonShape⟩
  have firstSteps' : Reduction.RedStar (.id carrier left right)
      (.id commonCarrier commonLeft commonRight) := by
    simpa [commonShape] using firstSteps
  have secondSteps' : Reduction.RedStar (.id carrier' left' right')
      (.id commonCarrier commonLeft commonRight) := by
    simpa [commonShape] using secondSteps
  obtain ⟨carrierFirst, leftFirst, rightFirst⟩ :=
    old_redStar_id_decomp firstSteps'
  obtain ⟨carrierSecond, leftSecond, rightSecond⟩ :=
    old_redStar_id_decomp secondSteps'
  exact ⟨
    Relation.EqvGen.trans _ _ _
      (Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_implies_conv
        carrierFirst)
      (Relation.EqvGen.symm _ _
        (Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_implies_conv
          carrierSecond)),
    Relation.EqvGen.trans _ _ _
      (Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_implies_conv
        leftFirst)
      (Relation.EqvGen.symm _ _
        (Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_implies_conv
          leftSecond)),
    Relation.EqvGen.trans _ _ _
      (Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_implies_conv
        rightFirst)
      (Relation.EqvGen.symm _ _
        (Mettapedia.Languages.MeTTa.PureKernel.Confluence.redStar_implies_conv
          rightSecond))⟩

/-- Identity conversion preserves the carrier and both endpoint conversions
after forgetting only the choice of tower universe head. -/
theorem id_components_of_conv
    {carrier left right carrier' left' right' : Tower.Tm n}
    (conversion : Conv Tower.HeadEq (.id carrier left right)
      (.id carrier' left' right')) :
    Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv
        (erase carrier) (erase carrier') ∧
      Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv
        (erase left) (erase left') ∧
      Mettapedia.Languages.MeTTa.PureKernel.Typing.Conv
        (erase right) (erase right') :=
  pure_id_components_of_conv (conv_erases conversion)

/-! ## Small normal-form certificates used by authority obstructions -/

theorem erase_var_normal (index : Fin n) :
    RedNormal (erase (.var index : Tower.Tm n)) := by
  intro target step
  cases step

theorem erase_head_normal (head : Tower.Head) :
    RedNormal (erase (.head head : Tower.Tm n)) := by
  intro target step
  cases step

theorem erase_pi_normal {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    (domainNormal : RedNormal (erase domain))
    (codomainNormal : RedNormal (erase codomain)) :
    RedNormal (erase (.pi domain codomain)) := by
  intro target step
  cases step with
  | congPiDom inner => exact domainNormal _ inner
  | congPiCod inner => exact codomainNormal _ inner

theorem erase_sigma_normal {domain : Tower.Tm n}
    {codomain : Tower.Tm (n + 1)}
    (domainNormal : RedNormal (erase domain))
    (codomainNormal : RedNormal (erase codomain)) :
    RedNormal (erase (.sigma domain codomain)) := by
  intro target step
  cases step with
  | congSigmaDom inner => exact domainNormal _ inner
  | congSigmaCod inner => exact codomainNormal _ inner

theorem erase_id_normal {carrier left right : Tower.Tm n}
    (carrierNormal : RedNormal (erase carrier))
    (leftNormal : RedNormal (erase left))
    (rightNormal : RedNormal (erase right)) :
    RedNormal (erase (.id carrier left right)) := by
  intro target step
  cases step with
  | congIdTy inner => exact carrierNormal _ inner
  | congIdLeft inner => exact leftNormal _ inner
  | congIdRight inner => exact rightNormal _ inner

end TowerConversionSkeleton

end Mettapedia.Languages.MeTTa.PureKernel.Universe.Presentation
