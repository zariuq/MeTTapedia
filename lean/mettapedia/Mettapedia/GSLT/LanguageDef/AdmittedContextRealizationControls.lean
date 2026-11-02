import Mettapedia.Logic.HOL.PredicateContextInstantiation
import Mettapedia.GSLT.LanguageDef.AdmittedSourceCasePremiseControls

/-!
# Original Cons premises instantiate a dependent predicate context

The source interpretation has separate length, element and recursive-child
variables. The target retains an open child array. Original source guards
provide the data proofs; the complete child condition and explicit Peano
premises provide membership at the requested index. The resulting variable
assignment keeps these three source occurrences in their declared order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContextRealizationControls

open Mettapedia.Logic.HOL
open PredicateContexts FiniteConstructorEncoding
open AdmittedContainerGeneratedControls

noncomputable section

def target : List (Formula Symbol AdmittedSourceCasePremiseControls.context) := AdmittedSourceCasePremiseControls.hypotheses ++
  [NaturalNumeralProofs.separation (weakenCtx AdmittedSourceCasePremiseControls.context AdmittedChildPremiseControls.zero) (weakenCtx AdmittedSourceCasePremiseControls.context AdmittedChildPremiseControls.successor),
    NaturalNumeralProofs.injectivity (weakenCtx AdmittedSourceCasePremiseControls.context AdmittedChildPremiseControls.successor),
    NaturalRecursionProofs.inductionPrinciple (weakenCtx AdmittedSourceCasePremiseControls.context AdmittedChildPremiseControls.zero) (weakenCtx AdmittedSourceCasePremiseControls.context AdmittedChildPremiseControls.successor)]

def placement : ProofSyntax.OccurrenceMap AdmittedSourceCasePremiseControls.hypotheses target :=
  ProofSyntax.OccurrenceMap.appendRight _ _

private theorem identityFrame : AdmittedSourceCasePremiseControls.signature.subst Subst.id = AdmittedSourceCasePremiseControls.signature := by
  apply RecursiveSpacePredicate.Contextual.eq_of_fields
    (first := AdmittedSourceCasePremiseControls.signature.subst Subst.id)
    (second := AdmittedSourceCasePremiseControls.signature) rfl rfl rfl
  all_goals apply heq_of_eq; exact subst_id _

private theorem condition_congr
    {first second : RecursiveSpacePredicate.Contextual Symbol AdmittedSourceCasePremiseControls.context}
    (same : first = second)
    {firstPredicate : Term Symbol AdmittedSourceCasePremiseControls.context (first.space ⇒ .prop)}
    {secondPredicate : Term Symbol AdmittedSourceCasePremiseControls.context (second.space ⇒ .prop)}
    {firstPayload : Term Symbol AdmittedSourceCasePremiseControls.context first.payload}
    {secondPayload : Term Symbol AdmittedSourceCasePremiseControls.context second.payload}
    {firstChildren : Term Symbol AdmittedSourceCasePremiseControls.context (first.number ⇒ first.space)}
    {secondChildren : Term Symbol AdmittedSourceCasePremiseControls.context (second.number ⇒ second.space)}
    (predicateSame : HEq firstPredicate secondPredicate) (payloadSame : HEq firstPayload secondPayload)
    (childrenSame : HEq firstChildren secondChildren) :
    first.childConditions firstPredicate firstPayload firstChildren =
      second.childConditions secondPredicate secondPayload secondChildren := by
  cases same
  cases predicateSame
  cases payloadSame
  cases childrenSame
  rfl

theorem condition_exact :
    ((AdmittedSourceCasePremiseControls.signature.constructorScope.subst AdmittedSourceCasePremiseControls.images).childConditions
      (subst AdmittedSourceCasePremiseControls.images (weaken (weaken (weaken AdmittedSourceCasePremiseControls.predicate))))
      AdmittedSourceCasePremiseControls.data (subst AdmittedSourceCasePremiseControls.images AdmittedSourceCasePremiseControls.signature.constructorChildren)) = AdmittedChildPremiseControls.conditions := by
  apply condition_congr
    ((AdmittedSourceCasePremiseControls.signature.constructorScope_instantiate Subst.id
      AdmittedSourceCasePremiseControls.tag AdmittedSourceCasePremiseControls.data
      AdmittedSourceCasePremiseControls.children).trans identityFrame)
  · apply heq_of_eq
    exact (AdmittedSourceCasePremiseControls.signature.constructorSubstitution_weaken Subst.id
      AdmittedSourceCasePremiseControls.tag AdmittedSourceCasePremiseControls.data
      AdmittedSourceCasePremiseControls.children AdmittedSourceCasePremiseControls.predicate).trans (subst_id _)
  · rfl
  · rfl

@[irreducible] def conditionProof : ProofSyntax Symbol target AdmittedChildPremiseControls.conditions :=
  ProofSyntax.castIndices rfl condition_exact (AdmittedSourceCasePremiseControls.fullChildCondition.mono placement)

def peanoInputs : ProofSyntax.HypothesisSubstitution AdmittedChildPremiseControls.assumptions.tail target :=
  fun position => (ProofSyntax.hyp (Δ := AdmittedChildPremiseControls.assumptions.tail) position).mono
    (ProofSyntax.OccurrenceMap.appendLeft AdmittedSourceCasePremiseControls.hypotheses _)

@[irreducible] def oldInputs : ProofSyntax.HypothesisSubstitution AdmittedChildPremiseControls.assumptions target :=
  ProofSyntax.HypothesisSubstitution.append [AdmittedChildPremiseControls.conditions]
    AdmittedChildPremiseControls.assumptions.tail target
    (ProofSyntax.HypothesisSubstitution.single conditionProof) peanoInputs

@[irreducible] def selectedChild :=
  ProofSyntax.substituteHypotheses oldInputs AdmittedChildPremiseControls.selectedChild

abbrev familyType : Ty BaseCode := space ⇒ number ⇒ .prop
def familyContext : Telescope Symbol [familyType] := .snoc .nil (PredicateProducts.full familyType)
def familyValue : Term Symbol AdmittedSourceCasePremiseControls.context familyType :=
  AdmittedChildPremiseControls.signature.memberProgram
    (AdmittedChildPremiseControls.constructors.rootProgram AdmittedContainerInductionControls.ctor)

@[irreducible] def childMember : ProofSyntax Symbol target
    (.app (.app familyValue (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target))
      AdmittedChildPremiseControls.target) := .andEL (.andER selectedChild)

def numberPredicate : Term Symbol [familyType] (number ⇒ .prop) :=
  weakenCtx [familyType] (guards.value .length)
def elementPredicate : Term Symbol [number, familyType] (element ⇒ .prop) :=
  weakenCtx [number, familyType] (guards.value .payload)

def lengthContext : Telescope Symbol [number, familyType] := .snoc familyContext numberPredicate
def dataContext : Telescope Symbol [element, number, familyType] := .snoc lengthContext elementPredicate

def childPredicate : Term Symbol [element, number, familyType] (space ⇒ .prop) :=
  .lam (.app (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)) (.var (.vs (.vs .vz))))

def sourceContext : Telescope Symbol [space, element, number, familyType] := .snoc dataContext childPredicate

def emptyImages : Subst Symbol [] AdmittedSourceCasePremiseControls.context := fun impossible => nomatch impossible
def familyImages : Subst Symbol [familyType] AdmittedSourceCasePremiseControls.context :=
  Subst.cons familyValue emptyImages
def lengthImages : Subst Symbol [number, familyType] AdmittedSourceCasePremiseControls.context := Subst.cons (.const .zero) familyImages
def dataImages : Subst Symbol [element, number, familyType] AdmittedSourceCasePremiseControls.context := Subst.cons (.const .flagTrue) lengthImages
def images : Subst Symbol [space, element, number, familyType] AdmittedSourceCasePremiseControls.context :=
  Subst.cons (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target) dataImages

def emptyRealizer : (Telescope.nil : Telescope Symbol []).Realizes emptyImages target :=
  fun impossible => nomatch impossible

def familyProof : ProofSyntax Symbol target (.app (PredicateProducts.full familyType) familyValue) :=
  .impE (.eqPropER (.beta familyValue .top)) .topI

def familyRealizer : familyContext.Realizes familyImages target :=
  Telescope.Realizes.cons emptyRealizer (PredicateProducts.full familyType) familyValue familyProof

def lengthProof : ProofSyntax Symbol target (.app (subst familyImages numberPredicate) (.const .zero)) :=
  (AdmittedSourceCasePremiseControls.fields.1).mono placement

def lengthRealizer : lengthContext.Realizes lengthImages target :=
  Telescope.Realizes.cons familyRealizer numberPredicate (.const .zero) lengthProof

def elementProof : ProofSyntax Symbol target (.app (subst lengthImages elementPredicate) (.const .flagTrue)) :=
  (AdmittedSourceCasePremiseControls.fields.2.1).mono placement

def dataRealizer : dataContext.Realizes dataImages target :=
  Telescope.Realizes.cons lengthRealizer elementPredicate (.const .flagTrue) elementProof

@[irreducible] def childBeta {hypotheses : List (Formula Symbol AdmittedSourceCasePremiseControls.context)} :
    ProofSyntax Symbol hypotheses (.eq
      (.app (subst dataImages childPredicate) (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target))
      (.app (.app familyValue (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target))
        AdmittedChildPremiseControls.target)) := by
  let body : Term Symbol (space :: AdmittedSourceCasePremiseControls.context) .prop :=
    .app (.app (weaken familyValue) (.var .vz)) (weaken AdmittedChildPremiseControls.target)
  let child := Term.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target
  have computation : instantiate child body = .app (.app familyValue child) AdmittedChildPremiseControls.target := by
    change Term.app (Term.app (subst (Subst.single child) (weaken familyValue)) child)
      (subst (Subst.single child) (weaken AdmittedChildPremiseControls.target)) = _
    rw [PredicateFixedPoint.subst_single_weaken, PredicateFixedPoint.subst_single_weaken]
  exact ProofSyntax.castIndices rfl (congrArg (Term.eq (.app (subst dataImages childPredicate) child)) computation)
    (.beta child body)

theorem childBeta_free {hypotheses : List (Formula Symbol AdmittedSourceCasePremiseControls.context)} :
    (childBeta (hypotheses := hypotheses)).FunctionExtensionalityFree := by
  simp only [childBeta, ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree]

@[irreducible] def childProof : ProofSyntax Symbol target (.app (subst dataImages childPredicate)
    (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target)) :=
  .impE (.eqPropER childBeta) childMember

def realizer : sourceContext.Realizes images target :=
  Telescope.Realizes.cons dataRealizer childPredicate (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target) childProof

theorem conditionProof_free : conditionProof.FunctionExtensionalityFree := by
  simpa only [conditionProof, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_mono] using AdmittedSourceCasePremiseControls.fullChildCondition_free

theorem peanoInputs_free : ∀ occurrence, (peanoInputs occurrence).FunctionExtensionalityFree := by
  intro occurrence
  exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr True.intro

set_option backward.isDefEq.respectTransparency true in
theorem oldInputs_free : ∀ occurrence, (oldInputs occurrence).FunctionExtensionalityFree := by
  unfold oldInputs
  exact ProofSyntax.HypothesisSubstitution.append_free [AdmittedChildPremiseControls.conditions]
    AdmittedChildPremiseControls.assumptions.tail target
    (ProofSyntax.HypothesisSubstitution.single conditionProof) peanoInputs
    (ProofSyntax.HypothesisSubstitution.single_free conditionProof conditionProof_free) peanoInputs_free

theorem selectedChild_free : selectedChild.FunctionExtensionalityFree := by
  unfold selectedChild
  exact ProofSyntax.substituteHypotheses_free oldInputs AdmittedChildPremiseControls.selectedChild
    AdmittedChildPremiseControls.selectedChild_free oldInputs_free

private theorem equalityApply_free {hypotheses : List (Formula Symbol AdmittedSourceCasePremiseControls.context)}
    {first second : Formula Symbol AdmittedSourceCasePremiseControls.context}
    (equality : ProofSyntax Symbol hypotheses (.eq first second)) (present : ProofSyntax Symbol hypotheses second)
    (equalityFree : equality.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (ProofSyntax.impE (ProofSyntax.eqPropER equality) present).FunctionExtensionalityFree :=
  ⟨equalityFree, presentFree⟩

private theorem middle_free {hypotheses : List (Formula Symbol AdmittedSourceCasePremiseControls.context)}
    {first second third : Formula Symbol AdmittedSourceCasePremiseControls.context}
    (proof : ProofSyntax Symbol hypotheses (.and first (.and second third))) (free : proof.FunctionExtensionalityFree) :
    (ProofSyntax.andEL (ProofSyntax.andER proof)).FunctionExtensionalityFree := free

theorem childMember_free : childMember.FunctionExtensionalityFree := by
  unfold childMember
  exact middle_free selectedChild selectedChild_free

set_option backward.isDefEq.respectTransparency true in
theorem childProof_free : childProof.FunctionExtensionalityFree := by
  unfold childProof
  exact equalityApply_free childBeta childMember childBeta_free childMember_free

theorem realizer_free : ∀ {type} (index : Var [space, element, number, familyType] type),
    (realizer index).FunctionExtensionalityFree := by
  apply Telescope.Realizes.cons_free
  · apply Telescope.Realizes.cons_free
    · apply Telescope.Realizes.cons_free
      · apply Telescope.Realizes.cons_free
        · intro type impossible
          nomatch impossible
        · exact ⟨True.intro, True.intro⟩
      · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr AdmittedSourceCasePremiseControls.fields_free.1
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr AdmittedSourceCasePremiseControls.fields_free.2.1
  · exact childProof_free

def referenceRealizer : sourceContext.Realizes images AdmittedChildPremiseControls.assumptions := by
  let empty : (Telescope.nil : Telescope Symbol []).Realizes emptyImages AdmittedChildPremiseControls.assumptions :=
    fun impossible => nomatch impossible
  let family : familyContext.Realizes familyImages AdmittedChildPremiseControls.assumptions :=
    Telescope.Realizes.cons empty (PredicateProducts.full familyType) familyValue
      (.impE (.eqPropER (.beta familyValue .top)) .topI)
  let length : lengthContext.Realizes lengthImages AdmittedChildPremiseControls.assumptions :=
    Telescope.Realizes.cons family numberPredicate (.const .zero) AdmittedChildPremiseControls.fields.1
  let data : dataContext.Realizes dataImages AdmittedChildPremiseControls.assumptions :=
    Telescope.Realizes.cons length elementPredicate (.const .flagTrue) AdmittedChildPremiseControls.fields.2.1
  exact fun {type} index => Telescope.Realizes.cons data childPredicate
    (.app AdmittedChildPremiseControls.children AdmittedChildPremiseControls.target)
    (.impE (.eqPropER childBeta) (.andEL (.andER AdmittedChildPremiseControls.selectedChild))) index

theorem source_environment_realizable : sourceContext.Satisfies model
    (Soundness.substVal model images AdmittedChildPremiseModelControls.world) :=
  referenceRealizer.satisfies_subst model (model.functionsRespectEqv_of_fullDomains full)
    AdmittedChildPremiseModelControls.world
    (by intro type index; exact full type (AdmittedChildPremiseModelControls.world index))
    AdmittedChildPremiseModelControls.assumptions_realizable

def badImages : Subst Symbol [space, element, number, familyType] AdmittedSourceCasePremiseControls.context :=
  Subst.cons (.const .bottom) dataImages

theorem bottom_child_refused : ¬ sourceContext.Satisfies model
    (Soundness.substVal model badImages AdmittedChildPremiseModelControls.world) := by
  intro holds
  have available := sourceContext.satisfies_variable model _ holds
    (.vz : Var [space, element, number, familyType] space)
  have member : (model.denote
      (AdmittedContainerInductionControls.member (.const .bottom) (.const .zero))
      AdmittedChildPremiseModelControls.world).down := available
  have separation := Soundness.extDerivation_sound
    (AdmittedContainerInductionControls.nonbottom (.const .bottom) (.const .zero)).erase
    (M := model) (ρ := AdmittedChildPremiseModelControls.world)
    (model.functionsRespectEqv_of_fullDomains full)
    (by intro type index; exact full type (AdmittedChildPremiseModelControls.world index)) (by
      intro formula present
      rcases List.mem_cons.mp present with rfl | rest
      · change (model.denote (weakenCtx AdmittedSourceCasePremiseControls.context
          (AdmittedContainerInductionControls.injectivity (Γ := []))) AdmittedChildPremiseModelControls.world).down
        rw [model.denote_weakenCtx]
        exact AdmittedContainerInductionControls.injectivity_valid
      · rcases List.mem_cons.mp rest with rfl | absent
        · change (model.denote (weakenCtx AdmittedSourceCasePremiseControls.context
            (AdmittedContainerInductionControls.separation (Γ := []))) AdmittedChildPremiseModelControls.world).down
          rw [model.denote_weakenCtx]
          exact AdmittedContainerInductionControls.separation_valid
        · exact False.elim (List.not_mem_nil absent))
  exact separation member rfl

theorem distinct_source_occurrences :
    (sourceContext.occurrence (.vz : Var [space, element, number, familyType] space)).val = 0 ∧
    (sourceContext.occurrence (.vs .vz : Var [space, element, number, familyType] element)).val = 1 ∧
    (sourceContext.occurrence (.vs (.vs .vz) : Var [space, element, number, familyType] number)).val = 2 :=
  ⟨rfl, rfl, rfl⟩

#print axioms condition_exact
#print axioms realizer
#print axioms realizer_free
#print axioms source_environment_realizable
#print axioms bottom_child_refused

end
end Mettapedia.GSLT.LanguageDef.AdmittedContextRealizationControls
