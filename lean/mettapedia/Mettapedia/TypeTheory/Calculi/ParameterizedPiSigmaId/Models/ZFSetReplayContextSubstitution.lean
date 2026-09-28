import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayContext
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayCoherence

/-!
# Context membership and dependent substitution of replay interpretations

The telescope's environment predicate is characterized by all of its actual
lookup-formation certificates. Substitution therefore has a local membership
criterion: every image belongs to the interpretation of its substituted
lookup type. The certificates are transformed by the existing algorithm.
No normalization restriction is imposed on these dependent type expressions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay
open ZFSetTypeExpressionInterpretation (Environment)

universe u
variable {Head : Type} {ConversionCode : Nat → Type}
variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- Lookup interpretation is available even when the telescope has no valid
environment. No inhabitant of the context is used to construct these views. -/
theorem lookupFormation_assembles {n : Nat} (code : ContextCode Head ConversionCode n) :
    ∀ {context : Ctx Head n} {valid : Environment.{u} n → Prop},
      assembleContext heads constants code context = some valid →
      ∀ index, ∃ meaning,
        assemble heads constants (code.lookupFormation renameConversion index).2
          (context.lookup index) (.head (code.lookupFormation renameConversion index).1) = some meaning := by
  induction code with
  | nil => intro context valid assembled index; exact Fin.elim0 index
  | snoc prior level formation ih =>
      intro context valid assembled index
      cases context with
      | snoc context A =>
          simp only [assembleContext, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at assembled
          obtain ⟨priorValid, atPrior, a, atA, rfl⟩ := assembled
          refine Fin.cases ?_ (fun priorIndex => ?_) index
          · refine ⟨a.reindex wk, ?_⟩
            simpa only [ContextCode.lookupFormation, Fin.cases_zero, Ctx.lookup, rename] using
              assemble_rename renameConversion heads constants formation A (.head level) a atA wk
          · obtain ⟨meaning, atMeaning⟩ := ih atPrior priorIndex
            refine ⟨meaning.reindex wk, ?_⟩
            simpa only [ContextCode.lookupFormation, Fin.cases_succ, Ctx.lookup, rename] using
              assemble_rename renameConversion heads constants
                (prior.lookupFormation renameConversion priorIndex).2
                (context.lookup priorIndex) (.head (prior.lookupFormation renameConversion priorIndex).1)
                meaning atMeaning wk

/-- The converse to variable membership: satisfying every interpreted lookup
type is exactly satisfying the assembled telescope, including dependencies. -/
theorem valid_iff_lookup_membership {n : Nat} (code : ContextCode Head ConversionCode n) :
    ∀ {context : Ctx Head n} {valid : Environment.{u} n → Prop},
      assembleContext heads constants code context = some valid →
      ∀ (meanings : Fin n → Meaning.{u} n),
        (∀ index, assemble heads constants (code.lookupFormation renameConversion index).2
          (context.lookup index) (.head (code.lookupFormation renameConversion index).1) =
            some (meanings index)) →
      ∀ env, valid env ↔ ∀ index, env index ∈ (meanings index).value env := by
  induction code with
  | nil =>
      intro context valid assembled meanings atMeanings env
      cases context
      simp only [assembleContext, Option.some.injEq] at assembled
      subst valid
      exact ⟨fun _ index => Fin.elim0 index, fun _ => trivial⟩
  | snoc prior level formation ih =>
      intro context valid assembled meanings atMeanings env
      cases context with
      | snoc context A =>
          simp only [assembleContext, Option.bind_eq_bind, Option.bind_eq_some_iff,
            Option.pure_def, Option.some.injEq] at assembled
          obtain ⟨priorValid, atPrior, a, atA, rfl⟩ := assembled
          classical
          choose priorMeanings atPriorMeanings using
            lookupFormation_assembles renameConversion heads constants prior atPrior
          have newest : meanings 0 = a.reindex wk := by
            have computed := assemble_rename renameConversion heads constants formation A (.head level) a atA wk
            have observed := atMeanings 0
            simp only [ContextCode.lookupFormation, Fin.cases_zero, Ctx.lookup] at observed
            exact Option.some.inj (observed.symm.trans computed)
          have older : ∀ index, meanings index.succ = (priorMeanings index).reindex wk := by
            intro index
            have computed := assemble_rename renameConversion heads constants
              (prior.lookupFormation renameConversion index).2 (context.lookup index)
              (.head (prior.lookupFormation renameConversion index).1)
              (priorMeanings index) (atPriorMeanings index) wk
            have observed := atMeanings index.succ
            simp only [ContextCode.lookupFormation, Fin.cases_succ, Ctx.lookup] at observed
            exact Option.some.inj (observed.symm.trans computed)
          constructor
          · intro holds index
            refine Fin.cases ?_ (fun priorIndex => ?_) index
            · rw [newest]; exact holds.2
            · rw [older]
              exact ((ih atPrior priorMeanings atPriorMeanings (env ∘ wk)).mp holds.1) priorIndex
          · intro members
            constructor
            · apply (ih atPrior priorMeanings atPriorMeanings (env ∘ wk)).mpr
              intro index
              have member := members index.succ
              rw [older] at member
              exact member
            · have member := members 0
              rw [newest] at member
              exact member

#print axioms lookupFormation_assembles
#print axioms valid_iff_lookup_membership

variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)
variable (renamePreserves : ∀ {n m} (ρ : Ren n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (renameConversion ρ code) (rename ρ left) (rename ρ right) = true)

include renamePreserves in
/-- A substitution maps an environment into the source telescope precisely
when its images inhabit the actual substituted lookup types. Each type value
comes with the certificate-substitution algorithm's assembly equation. -/
theorem substitution_valid_iff {n m : Nat}
    (context : Ctx Head n) (contextCode : ContextCode Head ConversionCode n)
    (valid : Environment.{u} n → Prop)
    (contextAccepted : checkContext R conversionCheck context contextCode = true)
    (atContext : assembleContext heads constants contextCode context = some valid)
    (σ : Sub Head n m) (codes : Fin n → Code Head ConversionCode m)
    (images : Fin n → Meaning.{u} m)
    (atImages : ∀ index, assemble heads constants (codes index) (σ index)
      (subst σ (context.lookup index)) = some (images index)) :
    ∃ types : Fin n → Meaning.{u} m,
      (∀ index, assemble heads constants
        ((contextCode.lookupFormation renameConversion index).2.substitute
          renameConversion substituteConversion σ codes (context.lookup index)
          (.head (contextCode.lookupFormation renameConversion index).1))
        (subst σ (context.lookup index))
        (.head (contextCode.lookupFormation renameConversion index).1) = some (types index)) ∧
      ∀ env, valid (imageEnvironment images env) ↔
        ∀ index, (images index).value env ∈ (types index).value env := by
  classical
  choose meanings atMeanings using
    lookupFormation_assembles renameConversion heads constants contextCode atContext
  have transformed := fun index => assemble_substitute renameConversion substituteConversion
    heads constants R conversionCheck (contextCode.lookupFormation renameConversion index).2
    (meanings index)
    (contextCode.lookupFormation_checked R conversionCheck renameConversion renamePreserves
      contextAccepted index).2 (atMeanings index) σ codes images atImages
  choose types atTypes values domains using transformed
  refine ⟨types, atTypes, ?_⟩
  intro env
  rw [valid_iff_lookup_membership renameConversion heads constants contextCode atContext
    meanings atMeanings]
  constructor
  · intro members index
    rw [values]
    exact members index
  · intro members index
    have member := members index
    rw [values] at member
    exact member

#print axioms substitution_valid_iff

variable (substitutePreserves : ∀ {n m} (σ : Sub Head n m) (code : ConversionCode n)
  {left right : Tm Head n}, conversionCheck code left right = true →
    conversionCheck (substituteConversion σ code) (subst σ left) (subst σ right) = true)

include renamePreserves substitutePreserves in
/-- Checked substitution transports an established semantic typing judgment
to the actual transformed term and formation certificates. The image premises
are local membership in each substituted lookup type, not an assumption that
the whole source context or every derivation is semantically sound. -/
theorem substitute_membership {n m : Nat}
    (sourceContext : Ctx Head n) (contextCode : ContextCode Head ConversionCode n)
    (targetContext : Ctx Head m) (sourceValid : Environment.{u} n → Prop)
    (targetValid : Environment.{u} m → Prop)
    (subject type : Tm Head n) (level : Head)
    (subjectCode formation : Code Head ConversionCode n) (meaning typeMeaning : Meaning.{u} n)
    (contextAccepted : checkContext R conversionCheck sourceContext contextCode = true)
    (subjectAccepted : check R conversionCheck sourceContext subject type subjectCode = true)
    (formationAccepted : check R conversionCheck sourceContext type (.head level) formation = true)
    (atContext : assembleContext heads constants contextCode sourceContext = some sourceValid)
    (atSubject : assemble heads constants subjectCode subject type = some meaning)
    (atFormation : assemble heads constants formation type (.head level) = some typeMeaning)
    (sourceTyped : ∀ env, sourceValid env → meaning.value env ∈ typeMeaning.value env)
    (σ : Sub Head n m) (codes : Fin n → Code Head ConversionCode m)
    (images imageTypes : Fin n → Meaning.{u} m)
    (imagesChecked : ∀ index, check R conversionCheck targetContext (σ index)
      (subst σ (sourceContext.lookup index)) (codes index) = true)
    (atImages : ∀ index, assemble heads constants (codes index) (σ index)
      (subst σ (sourceContext.lookup index)) = some (images index))
    (atImageTypes : ∀ index, assemble heads constants
      ((contextCode.lookupFormation renameConversion index).2.substitute
        renameConversion substituteConversion σ codes (sourceContext.lookup index)
        (.head (contextCode.lookupFormation renameConversion index).1))
      (subst σ (sourceContext.lookup index))
      (.head (contextCode.lookupFormation renameConversion index).1) = some (imageTypes index))
    (imagesTyped : ∀ env, targetValid env →
      ∀ index, (images index).value env ∈ (imageTypes index).value env) :
    let resultCode := subjectCode.substitute renameConversion substituteConversion σ codes subject type
    let resultFormation := formation.substitute renameConversion substituteConversion σ codes type (.head level)
    check R conversionCheck targetContext (subst σ subject) (subst σ type) resultCode = true ∧
      check R conversionCheck targetContext (subst σ type) (.head level) resultFormation = true ∧
      ∃ result resultType,
        assemble heads constants resultCode (subst σ subject) (subst σ type) = some result ∧
        assemble heads constants resultFormation (subst σ type) (.head level) = some resultType ∧
        ∀ env, targetValid env → result.value env ∈ resultType.value env := by
  obtain ⟨types, atTypes, validity⟩ := substitution_valid_iff renameConversion heads constants
    substituteConversion R conversionCheck renamePreserves sourceContext contextCode sourceValid
    contextAccepted atContext σ codes images atImages
  have agrees : ∀ index, types index = imageTypes index := by
    intro index
    exact Option.some.inj ((atTypes index).symm.trans (atImageTypes index))
  obtain ⟨result, atResult, resultValues, _⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R conversionCheck
      subjectCode meaning subjectAccepted atSubject σ codes images atImages
  obtain ⟨resultType, atResultType, typeValues, _⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R conversionCheck
      formation typeMeaning formationAccepted atFormation σ codes images atImages
  refine ⟨check_substitute renameConversion substituteConversion R conversionCheck
      renamePreserves substitutePreserves subjectCode subjectAccepted σ codes imagesChecked,
    check_substitute renameConversion substituteConversion R conversionCheck
      renamePreserves substitutePreserves formation formationAccepted σ codes imagesChecked,
    result, resultType, atResult, atResultType, ?_⟩
  intro env admitted
  rw [resultValues, typeValues]
  apply sourceTyped
  apply (validity env).mpr
  intro index
  rw [agrees]
  exact imagesTyped env admitted index

#print axioms substitute_membership

/-- Composing the existing finite image-certificate arrays gives the composite
environment map. Both the syntax substitution and the replay composition are
the existing operations, including their weakening beneath binders. -/
theorem composeImageCodes_environment {n m k : Nat}
    (sourceContext : Ctx Head n) (middleContext : Ctx Head m)
    (σ : Sub Head n m) (first : Fin n → Code Head ConversionCode m)
    (τ : Sub Head m k) (second : Fin m → Code Head ConversionCode k)
    (firstMeanings : Fin n → Meaning.{u} m) (secondMeanings : Fin m → Meaning.{u} k)
    (firstChecked : ∀ index, check R conversionCheck middleContext (σ index)
      (subst σ (sourceContext.lookup index)) (first index) = true)
    (atFirst : ∀ index, assemble heads constants (first index) (σ index)
      (subst σ (sourceContext.lookup index)) = some (firstMeanings index))
    (atSecond : ∀ index, assemble heads constants (second index) (τ index)
      (subst τ (middleContext.lookup index)) = some (secondMeanings index)) :
    ∃ composite : Fin n → Meaning.{u} k,
      (∀ index, assemble heads constants
        (composeImageCodes renameConversion substituteConversion sourceContext σ first τ second index)
        (subComp τ σ index) (subst (subComp τ σ) (sourceContext.lookup index)) = some (composite index)) ∧
      ∀ env, imageEnvironment composite env =
        imageEnvironment firstMeanings (imageEnvironment secondMeanings env) := by
  classical
  have transformed := fun index => assemble_substitute renameConversion substituteConversion
    heads constants R conversionCheck (first index) (firstMeanings index) (firstChecked index)
    (atFirst index) τ second secondMeanings atSecond
  choose composite atComposite values domains using transformed
  refine ⟨composite, ?_, ?_⟩
  · intro index
    simpa only [composeImageCodes, subst_subComp, subComp] using atComposite index
  · intro env
    funext index
    exact values index env

#print axioms composeImageCodes_environment

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
