import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInferenceCategoryObjects
import Mathlib.CategoryTheory.Equivalence

/-!
# The persistent inference execution category at proof observation

Objects supply canonical physical seed boards. Morphisms are actual selected
executions modulo their ordered proof-vector observation. Identity has no
physical steps. Composition retains the first representative's entire trace,
then realizes the second representative's observed proof at that physical
endpoint. The cut theorem proves representative independence and the category
laws. The resulting category is equivalent to the well-scoped full subcategory
of CertificateGSLT's classifying category.

The quotient deliberately forgets request traffic, allocation identities,
unselected work and cost. It does not identify raw physical histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaKernel (Value locatedAction)
open InferenceRequestExecution (Occurrence)
open InferenceJudgmentBoards
open _root_.CategoryTheory

variable {definition : ValidatedCalculusLanguageDef}

namespace PersistentContext

abbrev Representative (source target : PersistentContext definition) :=
  Execution (definition := definition) source.state source.board target.board.judgments

abbrev Morphism (source target : PersistentContext definition) :=
  ObservedExecution definition source.state source.board target.board.judgments

noncomputable def readout {source target : PersistentContext definition}
    (morphism : Morphism source target) :
    OpenDerivationList definition source.board.judgments target.board.judgments :=
  observeQuotient morphism

theorem readout_injective {source target : PersistentContext definition} :
    Function.Injective (readout (source := source) (target := target)) :=
  (proofObservationEquiv source.consistent).injective

noncomputable def identityRepresentative (context : PersistentContext definition) :
    Representative context context :=
  identityExecution context.board (ContextMap.id _)

theorem identity_has_no_steps (context : PersistentContext definition) :
    context.identityRepresentative.actors = [] := rfl

noncomputable def identity (context : PersistentContext definition) : Morphism context context :=
  Quotient.mk _ context.identityRepresentative

theorem readout_identity (context : PersistentContext definition) :
    readout context.identity = assumptionEnvironment definition context.board.judgments :=
  identityExecution_observe context.board (ContextMap.id _)

noncomputable def continuation {source middle target : PersistentContext definition}
    (first : Representative source middle) (second : Representative middle target) :
    Execution (definition := definition) first.after first.board target.board.judgments :=
  Classical.choose (realizes_cut source.consistent first second.observe)

noncomputable def composeRepresentative {source middle target : PersistentContext definition}
    (first : Representative source middle) (second : Representative middle target) :
    Representative source target := first.follow (continuation first second)

theorem composition_keeps_first_physical_trace {source middle target : PersistentContext definition}
    (first : Representative source middle) (second : Representative middle target) :
    (composeRepresentative first second).trace =
      first.trace.append (continuation first second).trace := rfl

theorem composition_actor_sequence {source middle target : PersistentContext definition}
    (first : Representative source middle) (second : Representative middle target) :
    (composeRepresentative first second).actors =
      first.actors ++ (continuation first second).actors := rfl

theorem composeRepresentative_observe {source middle target : PersistentContext definition}
    (first : Representative source middle) (second : Representative middle target) :
    (composeRepresentative first second).observe = second.observe.bind first.observe :=
  Classical.choose_spec (realizes_cut source.consistent first second.observe)

noncomputable def compose {source middle target : PersistentContext definition}
    (first : Morphism source middle) (second : Morphism middle target) : Morphism source target :=
  Quotient.lift₂ (fun first second => Quotient.mk _ (composeRepresentative first second))
    (by
      intro _ _ _ _ firstEq secondEq
      apply Quotient.sound
      change _ = _ at firstEq secondEq ⊢
      rw [composeRepresentative_observe, composeRepresentative_observe, firstEq, secondEq]) first second

theorem readout_compose {source middle target : PersistentContext definition}
    (first : Morphism source middle) (second : Morphism middle target) :
    readout (compose first second) = (readout second).bind (readout first) := by
  induction first, second using Quotient.inductionOn₂ with
  | _ first second => exact composeRepresentative_observe first second

noncomputable instance category (definition : ValidatedCalculusLanguageDef) :
    Category (PersistentContext definition) where
  Hom := Morphism
  id := identity
  comp := compose
  id_comp morphism := by
    apply readout_injective
    rw [readout_compose, readout_identity]
    exact OpenDerivationList.bind_assumptionEnvironment _
  comp_id morphism := by
    apply readout_injective
    rw [readout_compose, readout_identity]
    exact OpenDerivationList.assumptionEnvironment_bind _
  assoc first second third := by
    apply readout_injective
    rw [readout_compose, readout_compose, readout_compose, readout_compose]
    exact (OpenDerivationList.bind_assoc (readout third) (readout second) (readout first)).symm

end PersistentContext

noncomputable def proofFunctor (definition : ValidatedCalculusLanguageDef) :
    PersistentContext definition ⥤ ScopedProofContexts definition where
  obj context := context.proofContext
  map morphism := ObjectProperty.homMk (PersistentContext.readout morphism)
  map_id context := by
    apply ObjectProperty.hom_ext
    exact PersistentContext.readout_identity context
  map_comp first second := by
    apply ObjectProperty.hom_ext
    exact PersistentContext.readout_compose first second

noncomputable def proofFunctorFullyFaithful (definition : ValidatedCalculusLanguageDef) :
    (proofFunctor definition).FullyFaithful where
  preimage {source target} proof := Quotient.mk _ (compile source.consistent proof.hom)
  map_preimage {source target} proof := by
    apply ObjectProperty.hom_ext
    exact compile_observe source.consistent proof.hom
  preimage_map {source target} execution := by
    apply PersistentContext.readout_injective
    exact compile_observe source.consistent (PersistentContext.readout execution)

instance proofFunctor_full (definition : ValidatedCalculusLanguageDef) : (proofFunctor definition).Full :=
  (proofFunctorFullyFaithful definition).full

instance proofFunctor_faithful (definition : ValidatedCalculusLanguageDef) :
    (proofFunctor definition).Faithful := (proofFunctorFullyFaithful definition).faithful

instance proofFunctor_essSurj (definition : ValidatedCalculusLanguageDef) :
    (proofFunctor definition).EssSurj where
  mem_essImage target := by
    let source : PersistentContext definition := ⟨target.obj.judgments, target.property⟩
    refine ⟨source, ⟨eqToIso ?_⟩⟩
    apply ObjectProperty.FullSubcategory.ext
    exact congrArg ClassifyingContext.mk source.board_judgments

instance proofFunctor_isEquivalence (definition : ValidatedCalculusLanguageDef) :
    (proofFunctor definition).IsEquivalence where

noncomputable def persistentInferenceEquivalence (definition : ValidatedCalculusLanguageDef) :
    PersistentContext definition ≌ ScopedProofContexts definition :=
  (proofFunctor definition).asEquivalence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PersistentInference
