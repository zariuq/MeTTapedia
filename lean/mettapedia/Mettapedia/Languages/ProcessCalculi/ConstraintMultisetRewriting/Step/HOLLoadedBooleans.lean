import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameDomains
import Mettapedia.Languages.HOLLight.SourceProfileModels

/-! # Boolean meanings earned from the received defining equations

The seven interpreted Boolean schemas occur in the actual export cache.
Their meanings follow in every full-domain model of that cache, including
the constructed model on the indexed frame carriers. No Boolean meaning is
added as an independent model assumption.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedBooleans

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open DefinitionAdapters SignatureFormation DefinitionHistorySchemas
open StandardTheoryInterpretation StandardTheoryInterpretation.Interpretation

def booleanDefinitions : List ContextConstantDefinitionResult :=
  [Source.truthResult, Source.conjunctionResult, Source.implicationResult, Source.universalResult,
    Source.existentialResult, Source.falsityResult, Source.negationResult]

theorem booleans_cached (result : ContextConstantDefinitionResult) (member : result ∈ booleanDefinitions) :
    ∃ fact ∈ HOLSemanticDefinitions.received.received.registered.cache,
      fact.sequent = result.output.definitionTheorem.sequent := by
  have checked : booleanDefinitions.all (fun result =>
      HOLSemanticDefinitions.received.received.registered.cache.toList.any
        (fun fact => ExportReplay.claimsSame [result.output.definitionTheorem.sequent] [fact])) = true := by
    decide +kernel
  obtain ⟨fact, present, agrees⟩ := List.any_eq_true.mp ((List.all_eq_true.mp checked) result member)
  have same := (ExportReplay.claimsSame_eq_true_iff [result.output.definitionTheorem.sequent] [fact]).mp agrees
  exact ⟨fact, by simpa using present, (List.cons.inj same).1.symm⟩

universe w

variable (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
  (equations : ∀ fact ∈ HOLSemanticDefinitions.received.received.registered.cache, ∀ substitution : TypeSubst,
    ∃ formula : HOL.ClosedFormula Symbol,
      TranslatesCompositionally []
        ((TermSubst.mk substitution []).applyDB fact.sequent.concl.term) .prop formula ∧
      model.models formula)

include equations in
theorem cached_schema {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    (parameter : Name)
    (equalityRegistered : context.signature.constants Const.equality = some (Ty.equality (.var parameter)))
    (cached : ∃ fact ∈ HOLSemanticDefinitions.received.received.registered.cache,
      fact.sequent = result.output.definitionTheorem.sequent) (substitution : TypeSubst) :
    model.models (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema result)) := by
  obtain ⟨fact, member, same⟩ := cached
  obtain ⟨formula, translated, holds⟩ := equations fact member substitution
  rw [same] at translated
  have canonical := constantInstanceSchema_translated accepted substitution
  have equalFormula := TranslatesCompositionally.unique_eq translated canonical
  rw [constantSchema_type_image accepted parameter equalityRegistered substitution]
  exact equalFormula ▸ holds

private theorem equality_after {context : TheoryContext} {instances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory context instances name source = some result)
    {parameter : Name}
    (registered : context.signature.constants Const.equality = some (Ty.equality (.var parameter))) :
    result.context.signature.constants Const.equality = some (Ty.equality (.var parameter)) :=
  (admitConstantInTheory_result accepted).2.2.1.2 _ _ registered

structure Meanings (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) : Prop where
  truth : model.constDen Symbols.truth = ULift.up True
  conjunction : ∀ left right, model.constDen Symbols.conjunction left right = ULift.up (left.down ∧ right.down)
  implication : ∀ left right, model.constDen Symbols.implication left right = ULift.up (left.down → right.down)
  universal : ∀ operand predicate, model.constDen (Symbols.universal operand) predicate =
    ULift.up (∀ value, model.adm operand value → (predicate value).down)
  existential : ∀ operand predicate, model.constDen (Symbols.existential operand) predicate =
    ULift.up (∃ value, model.adm operand value ∧ (predicate value).down)
  falsity : model.constDen Symbols.falsity = ULift.up False
  negation : ∀ proposition, model.constDen Symbols.negation proposition = ULift.up (¬ proposition.down)

include equations in
theorem meanings_of_cache (full : model.FullDomains) : Meanings model := by
  let parameter := SourceProfileModels.primitives.equalityParameter
  have eq0 := SourceProfileModels.primitives.equalityRegistered
  have eq1 : Source.truthContext.signature.constants Const.equality = some (Ty.equality (.var parameter)) := by
    simpa only [Source.truthContext] using equality_after Source.truthAdmitted eq0
  have eq2 : Source.conjunctionContext.signature.constants Const.equality = some (Ty.equality (.var parameter)) := by
    simpa only [Source.conjunctionContext] using equality_after Source.conjunctionAdmitted eq1
  have eq3 : Source.implicationContext.signature.constants Const.equality = some (Ty.equality (.var parameter)) := by
    simpa only [Source.implicationContext] using equality_after Source.implicationAdmitted eq2
  have eq4 : Source.universalContext.signature.constants Const.equality = some (Ty.equality (.var parameter)) := by
    simpa only [Source.universalContext] using equality_after Source.universalAdmitted eq3
  have eq5 : Source.existentialContext.signature.constants Const.equality = some (Ty.equality (.var parameter)) := by
    simpa only [Source.existentialContext] using equality_after Source.existentialAdmitted eq4
  have eq6 : Source.falsityContext.signature.constants Const.equality = some (Ty.equality (.var parameter)) := by
    simpa only [Source.falsityContext] using equality_after Source.falsityAdmitted eq5
  have truth := truth_of_schema model full parameter eq0
    (cached_schema model equations Source.truthAdmitted parameter eq0 (booleans_cached _ (by simp [booleanDefinitions])))
  have conjunction := conjunction_of_schema model full parameter eq1
    (cached_schema model equations Source.conjunctionAdmitted parameter eq1 (booleans_cached _ (by simp [booleanDefinitions]))) truth
  have implication := implication_of_schema model full parameter eq2
    (cached_schema model equations Source.implicationAdmitted parameter eq2 (booleans_cached _ (by simp [booleanDefinitions]))) conjunction
  have universal := universal_of_schema model full parameter eq3
    (cached_schema model equations Source.universalAdmitted parameter eq3 (booleans_cached _ (by simp [booleanDefinitions]))) truth
  have existential := existential_of_schema model full parameter eq4
    (cached_schema model equations Source.existentialAdmitted parameter eq4 (booleans_cached _ (by simp [booleanDefinitions]))) universal implication
  have falsity := falsity_of_schema model full parameter eq5
    (cached_schema model equations Source.falsityAdmitted parameter eq5 (booleans_cached _ (by simp [booleanDefinitions]))) universal
  have negation := negation_of_schema model full parameter eq6
    (cached_schema model equations Source.negationAdmitted parameter eq6 (booleans_cached _ (by simp [booleanDefinitions]))) implication falsity
  exact ⟨truth, conjunction, implication, universal, existential, falsity, negation⟩

universe uO uT uH uOcc

theorem encoded_model_has_boolean_meanings
    (Obj : Type uO) (Tm : Obj → Type uT) (Hom : Obj → Obj → Type uH) (O : Type uOcc)
    (other : TypeFamilySemantics.OperatorFamilies.{max uO uT uH uOcc})
    (prior : TypeFamilySemantics.Assignment.{max uO uT uH uOcc}) :
    ∃ finalModel : HOL.HenkinModel.{0,0,(max uO uT uH uOcc)+1} AtomicTy Symbol,
      finalModel.Carrier = (HOLFrameDomains.initial Obj Tm Hom O other prior).Carrier ∧
      finalModel.FullDomains ∧ Meanings finalModel := by
  obtain ⟨actual, carriers, full, definitions⟩ := HOLFrameDomains.loaded_model_exists Obj Tm Hom O other prior
  exact ⟨actual, carriers, full, meanings_of_cache actual definitions full⟩

#print axioms booleans_cached
#print axioms meanings_of_cache
#print axioms encoded_model_has_boolean_meanings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLLoadedBooleans
