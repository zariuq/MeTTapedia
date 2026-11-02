import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedEnvironmentBindings
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeGuardedRealizabilityControls
import Mettapedia.GSLT.LanguageDef.SourceIndexSelectionControls

/-!
# Dependent source application at an admitted selected child

The source program has a type A, a family B on A, a child x : A and an
induction result r : B x. The typed program returns that supplied result.
Its interpretation assigns the child to the actual selected native array
lookup and opens the induction result only in its local continuation.
The source formation and lexical reading remain separate checked data;
this does not provide a whole-universe interpretation or a complete
constructor-case compiler.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedDependentMethodControls

open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open NativeNaturalVectorFamilies
open PredicateContexts AdmittedContainerGeneratedControls

local instance : DecidableEq BaseCode := fun first second => by
  cases first <;> cases second <;>
    first | exact isTrue rfl | exact isFalse (by intro same; cases same)

namespace Source

def profile := NativeGuardedRealizability.Controls.profile
def theory := Programs.Annotated.church profile
def universeHead : Tower.Head := NativeGuardedRealizability.Controls.universeHead
def nextHead : Tower.Head := NativeGuardedRealizability.Controls.nextHead

abbrev valuePredicate : Ty BaseCode := space ⇒ .prop
abbrev familyCarrier : Ty BaseCode := space ⇒ valuePredicate
def fullPredicate : ClosedTerm Symbol (valuePredicate ⇒ .prop) := .lam .top

def lex : LexicalReading Tower.Head BaseCode Symbol where
  constCode? _ := none
  headCode? head := if head = universeHead then some ⟨valuePredicate ⇒ .prop, fullPredicate⟩ else none

theorem universe_formed {n : Nat} (context : CCtx Tower.Head n) :
    CIsType theory context (.head universeHead) :=
  ⟨nextHead, by decide +kernel, .headType (by decide +kernel)⟩

def baseContext : GuardedContext theory lex [valuePredicate] where
  source := .snoc .nil (.head universeHead)
  telescope := .snoc .nil fullPredicate
  formed := .snoc .nil (universe_formed .nil)
  reading := .snoc .nil (.head (by simp [lex, fullPredicate]))

theorem base_domain_formed : CIsType theory baseContext.source (.var 0) :=
  ⟨universeHead, by decide +kernel, .var 0⟩

def familyType : CTm Tower.Head 1 := .pi (.var 0) (.head universeHead)
def familyPredicate : Term Symbol [valuePredicate] (familyCarrier ⇒ .prop) :=
  PredicateProducts.pi (.var .vz) (weakenCtx _ fullPredicate)

theorem family_read : Reads lex (Γ := [valuePredicate]) familyType familyPredicate :=
  .product (Reads.var (lex := lex) (.vz : Var [valuePredicate] valuePredicate))
    (.head (by simp [lex, fullPredicate]))

theorem family_formed : CIsType theory baseContext.source familyType :=
  CIsType.pi (Programs.Annotated.levelModel profile) base_domain_formed (universe_formed _)

def familyContext := baseContext.snoc familyPredicate family_read family_formed

def domain : CTm Tower.Head 2 := .var 1
def domainPredicate : Term Symbol [familyCarrier, valuePredicate] valuePredicate := .var (.vs .vz)

theorem domain_read : Reads lex (Γ := [familyCarrier, valuePredicate]) domain domainPredicate :=
  Reads.var (lex := lex) (.vs .vz : Var [familyCarrier, valuePredicate] valuePredicate)
theorem domain_formed : CIsType theory familyContext.source domain :=
  ⟨universeHead, by decide +kernel, .var 1⟩

def childContext := familyContext.snoc domainPredicate domain_read domain_formed
def resultType : CTm Tower.Head 3 := .app (.var 1) (.var 0)
def resultPredicate : Term Symbol [space, familyCarrier, valuePredicate] valuePredicate :=
  .app (.var (.vs .vz)) (.var .vz)

theorem result_read : Reads lex (Γ := [space, familyCarrier, valuePredicate]) resultType resultPredicate :=
  .application (Reads.var (lex := lex) (.vs .vz : Var [space, familyCarrier, valuePredicate] familyCarrier))
    (Reads.var (lex := lex) (.vz : Var [space, familyCarrier, valuePredicate] space))
theorem result_formed : CIsType theory childContext.source resultType := by
  have family : CTyped theory childContext.source (.var 1) (.pi (.var 2) (.head universeHead)) := .var 1
  have child : CTyped theory childContext.source (.var 0) (.var 2) := .var 0
  exact ⟨universeHead, by decide +kernel, .appElim family child⟩

def resultContext := childContext.snoc resultPredicate result_read result_formed
def resultValue := GuardedRealizer.ofVariable [] resultContext (.vz : Var [space, space, familyCarrier, valuePredicate] space)

theorem repeated_result_formed : CIsType theory resultContext.source (.app (.var 2) (.var 1)) := by
  have family : CTyped theory resultContext.source (.var 2) (.pi (.var 3) (.head universeHead)) := .var 2
  have child : CTyped theory resultContext.source (.var 1) (.var 3) := .var 1
  exact ⟨universeHead, by decide +kernel, .appElim family child⟩

def innerMethod := GuardedRealizer.abstraction (Programs.Annotated.levelModel profile)
  resultPredicate result_read result_formed repeated_result_formed resultValue

theorem inner_type_formed : CIsType theory childContext.source
    (.pi resultType (.app (.var 2) (.var 1))) :=
  CIsType.pi (Programs.Annotated.levelModel profile) result_formed repeated_result_formed

def method := GuardedRealizer.abstraction (Programs.Annotated.levelModel profile)
  domainPredicate domain_read domain_formed inner_type_formed innerMethod

def firstWeakening := GuardedSubstitution.weakening [] familyContext domainPredicate domain_read domain_formed
def secondWeakening := GuardedSubstitution.weakening [] childContext resultPredicate result_read result_formed
def openMethod := (method.substitute firstWeakening).substitute secondWeakening
def childValue := GuardedRealizer.ofVariable [] resultContext
  (.vs .vz : Var [space, space, familyCarrier, valuePredicate] space)

def supplied : SuppliedArguments [] resultContext [(.var 1 : CTm Tower.Head 4), .var 0]
    (.pi (.var 3) (.pi (.app (.var 3) (.var 0)) (.app (.var 4) (.var 1))))
    (space ⇒ space ⇒ space) (.app (.var 2) (.var 1)) space :=
  .cons childValue (.cons resultValue (.nil _ _))

def completed := supplied.apply openMethod

theorem method_free : method.Free :=
  GuardedRealizer.abstraction_free _ _ _ _ _ _
    (GuardedRealizer.abstraction_free _ _ _ _ _ _ (GuardedRealizer.ofVariable_free [] resultContext _))

theorem firstWeakening_free : firstWeakening.Free :=
  GuardedSubstitution.ofRenaming_free [] familyContext childContext wk Rename.weaken (fun _ => rfl)
    (CCtxRen.wk familyContext.source domain)

theorem secondWeakening_free : secondWeakening.Free :=
  GuardedSubstitution.ofRenaming_free [] childContext resultContext wk Rename.weaken (fun _ => rfl)
    (CCtxRen.wk childContext.source resultType)

theorem completed_free : completed.Free :=
  supplied.apply_free openMethod
    ⟨GuardedRealizer.ofVariable_free [] resultContext _, GuardedRealizer.ofVariable_free [] resultContext _, True.intro⟩
    (GuardedRealizer.substitute_free _ _
      (GuardedRealizer.substitute_free _ _ method_free firstWeakening_free) secondWeakening_free)

theorem complete_source_typing : CTyped theory resultContext.source
    (.app (.app (.lam (.var 3) (.lam (.app (.var 3) (.var 0)) (.var 0))) (.var 1)) (.var 0))
    (.app (.var 2) (.var 1)) := completed.typed

def firstOpenMethod := method.substitute firstWeakening

def inputExists : Formula Symbol [space, familyCarrier, valuePredicate] :=
  .ex (.app (weaken resultPredicate) (.var .vz))

def goal : Formula Symbol [space, familyCarrier, valuePredicate] :=
  .ex (.and (.app (weaken resultPredicate) (.var .vz))
    (.eq (.app (.app (weaken firstOpenMethod.term) (.var (.vs .vz))) (.var .vz)) (.var .vz)))

theorem first_open_term : firstOpenMethod.term = .lam (.lam (.var .vz)) := rfl
theorem completed_term : completed.term =
    .app (.app (.lam (.lam (.var .vz))) (.var (.vs .vz))) (.var .vz) := rfl

def continuation : ProofSyntax Symbol (resultContext.hypotheses []) (weaken goal) := by
  have same : completed.predicate = weaken resultPredicate :=
    Reader.term_unique completed.typeRead
      (result_read.rename Rename.weaken wk (fun _ => rfl))
  have member : ProofSyntax Symbol (resultContext.hypotheses []) (.app (weaken resultPredicate) completed.term) :=
    ProofSyntax.castIndices rfl (congrArg (fun predicate => Term.app predicate completed.term) same) completed.member
  apply ProofSyntax.exI completed.term
  change ProofSyntax Symbol (resultContext.hypotheses [])
    (.and (.app (weaken resultPredicate) completed.term)
      (.eq (.app (.app (weaken firstOpenMethod.term) (.var (.vs .vz))) completed.term) completed.term))
  refine .andI member ?_
  rw [first_open_term]
  exact CurriedGuardProgramProofs.beta2 (.var .vz) (.var (.vs .vz)) completed.term

theorem continuation_free : continuation.FunctionExtensionalityFree := by
  unfold continuation
  exact ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr completed_free,
    CurriedGuardProgramProofs.beta2_free _ _ _⟩

def inputHypotheses := inputExists :: childContext.hypotheses []
def inputGuards : childContext.telescope.Realizes Subst.id inputHypotheses :=
  Telescope.Realizes.mono (GuardedSubstitution.identity [] childContext).guards
    (ProofSyntax.OccurrenceMap.prepend inputExists)

def noRoots : ProofSyntax.HypothesisSubstitution (assumptions ([] : List (ClosedFormula Symbol))
    [space, familyCarrier, valuePredicate]) inputHypotheses := fun impossible => nomatch impossible

def available : ProofSyntax Symbol inputHypotheses
    (.ex (.app (weaken (subst Subst.id resultPredicate)) (.var .vz))) :=
  ProofSyntax.castIndices rfl (by rw [subst_id]; rfl)
    (.hyp (Δ := inputHypotheses) ⟨0, by change 0 < Nat.succ _; exact Nat.zero_lt_succ _⟩)

def consumed := childContext.eliminateWitness Subst.id inputGuards noRoots resultPredicate result_read result_formed
  available continuation

def closeInput : ProofSyntax Symbol (childContext.hypotheses []) (.imp inputExists goal) :=
  .impI (ProofSyntax.castIndices rfl (subst_id goal) consumed)

theorem closeInput_free : closeInput.FunctionExtensionalityFree := by
  unfold closeInput
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply GuardedContext.eliminateWitness_free
  · unfold inputGuards
    apply Telescope.Realizes.mono_free
    exact GuardedSubstitution.identity_free [] childContext
  · intro impossible
    nomatch impossible
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial
  · exact continuation_free

theorem result_is_supplied (candidate : HenkinModel BaseCode Symbol)
    (values : candidate.Valuation [space, space, familyCarrier, valuePredicate]) :
    candidate.denote completed.term values = values (.vz : Var [space, space, familyCarrier, valuePredicate] space) := rfl

def contextCertificate : Programs.Annotated.JudgmentReplay.ContextCertificate profile 4 := by
  annotated_context_certificate 12000 resultContext.formed

def applicationCertificate : Programs.Annotated.JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 complete_source_typing

theorem context_checked : Programs.Annotated.JudgmentReplay.checkContext profile resultContext.source contextCertificate = true := by
  decide +kernel

theorem application_checked : Programs.Annotated.JudgmentReplay.check profile applicationCertificate
    (.typing resultContext.source
      (.app (.app (.lam (.var 3) (.lam (.app (.var 3) (.var 0)) (.var 0))) (.var 1)) (.var 0))
      (.app (.var 2) (.var 1))) = true := by decide +kernel

theorem changed_result_type_refused : Programs.Annotated.JudgmentReplay.check profile applicationCertificate
    (.typing resultContext.source
      (.app (.app (.lam (.var 3) (.lam (.app (.var 3) (.var 0)) (.var 0))) (.var 1)) (.var 0))
      (.var 3)) = false := by decide +kernel

theorem exchanged_arguments_refused : Programs.Annotated.JudgmentReplay.check profile applicationCertificate
    (.typing resultContext.source
      (.app (.app (.lam (.var 3) (.lam (.app (.var 3) (.var 0)) (.var 0))) (.var 0)) (.var 1))
      (.app (.var 2) (.var 1))) = false := by decide +kernel

#print axioms complete_source_typing
#print axioms completed_free
#print axioms closeInput_free

end Source

namespace Native

open CurriedPredicates FiniteConstructorEncoding OrderedPositionPrograms
open IndexedConstructorGuards
open AdmittedChildPremiseControls (zero successor)

noncomputable section

abbrev context : Ctx BaseCode := [number, number ⇒ space]
def images : Subst Symbol AdmittedChildPremiseControls.context context := Subst.ofRename Rename.weaken
def constructors := AdmittedChildPremiseControls.constructors.subst images
def plans := fun row => substitute images (AdmittedChildPremiseControls.plans row)
def signature := (PositionPrograms.ofSegments constructors zero successor plans).contextual
  (subst images AdmittedContainerInductionControls.bottom) (subst images AdmittedContainerInductionControls.ctor)
def membership := signature.memberProgram (constructors.rootProgram (subst images AdmittedContainerInductionControls.ctor))
def child : Term Symbol context space := .app (subst images AdmittedChildPremiseControls.children) (.var .vz)
def index : Term Symbol context number := subst images AdmittedChildPremiseControls.target

def incoming : Formula Symbol context := PositionPrograms.selectedChildBody
  AdmittedChildPremiseControls.constructors zero successor AdmittedChildPremiseControls.plans
  AdmittedContainerInductionControls.bottom AdmittedContainerInductionControls.ctor AdmittedContainerInductionControls.motive
  consOccurrence AdmittedChildPremiseControls.arguments AdmittedChildPremiseControls.children 0 AdmittedChildPremiseControls.target

def target := incoming :: weakenHyps AdmittedChildPremiseControls.assumptions

def childMember : ProofSyntax Symbol target (.app (.app membership child) index) :=
  .andEL (.andER (.hyp (Δ := target) ⟨0, by change 0 < Nat.succ _; exact Nat.zero_lt_succ _⟩))

def childNonbottom : ProofSyntax Symbol target (.not (.eq child (.const .bottom))) :=
  .impE (.eqPropEL (AdmittedContainerInductionControls.motive_beta child index))
    (.andER (.andER (.hyp (Δ := target) ⟨0, by change 0 < Nat.succ _; exact Nat.zero_lt_succ _⟩)))

def typeValue : Term Symbol context Source.valuePredicate :=
  .lam (.app (.app (weaken membership) (.var .vz)) (weaken index))

def familyBody : Formula Symbol (space :: space :: context) :=
  .and (.not (.eq (.var (.vs .vz)) (.const .bottom))) (.not (.eq (.var .vz) (.const .bottom)))
def familyValue : Term Symbol context Source.familyCarrier := .lam (.lam familyBody)

def emptyImages : Subst Symbol [] context := fun impossible => nomatch impossible
def typeImages : Subst Symbol [Source.valuePredicate] context := Subst.cons typeValue emptyImages
def familyImages : Subst Symbol [Source.familyCarrier, Source.valuePredicate] context := Subst.cons familyValue typeImages
def childImages : Subst Symbol [space, Source.familyCarrier, Source.valuePredicate] context := Subst.cons child familyImages

def emptyGuards : (Telescope.nil : Telescope Symbol []).Realizes emptyImages target := fun impossible => nomatch impossible
def typeProof : ProofSyntax Symbol target (.app (weakenCtx context Source.fullPredicate) typeValue) :=
  .impE (.eqPropER (.beta typeValue .top)) .topI
def typeGuards : Source.baseContext.telescope.Realizes typeImages target :=
  Telescope.Realizes.cons emptyGuards Source.fullPredicate typeValue typeProof

def familyProof : ProofSyntax Symbol target (.app (subst typeImages Source.familyPredicate) familyValue) := by
  rw [Source.familyPredicate, PredicateProducts.subst_pi, subst_weakenCtx]
  apply PredicateProducts.introduce
  exact .impE (.eqPropER (.beta _ .top)) .topI

def familyGuards : Source.familyContext.telescope.Realizes familyImages target :=
  Telescope.Realizes.cons typeGuards Source.familyPredicate familyValue familyProof

private def reducedBeta {ambient : Ctx BaseCode} {domain codomain : Ty BaseCode}
    {hypotheses : List (Formula Symbol ambient)} (argument : Term Symbol ambient domain)
    (body : Term Symbol (domain :: ambient) codomain) (value : Term Symbol ambient codomain)
    (reduction : instantiate argument body = value) :
    {proof : ProofSyntax Symbol hypotheses (.eq (.app (.lam body) argument) value) // proof.FunctionExtensionalityFree} :=
  ⟨ProofSyntax.castIndices rfl (congrArg (Term.eq (.app (.lam body) argument)) reduction) (.beta argument body),
    (ProofSyntax.functionExtensionalityFree_castIndices rfl _ (.beta argument body)).mpr True.intro⟩

@[irreducible] private def childBetaEvidence :
    {proof : ProofSyntax Symbol target (.eq (.app typeValue child) (.app (.app membership child) index)) //
      proof.FunctionExtensionalityFree} := by
  let body : Formula Symbol (space :: context) := .app (.app (weaken membership) (.var .vz)) (weaken index)
  have reduction : instantiate child body = .app (.app membership child) index := by
    simp only [body, instantiate, HOL.subst, Subst.single, PredicateFixedPoint.subst_single_weaken]
    rfl
  exact reducedBeta child body _ reduction

@[irreducible] def childBeta : ProofSyntax Symbol target
    (.eq (.app typeValue child) (.app (.app membership child) index)) := childBetaEvidence.val

@[irreducible] def childProof : ProofSyntax Symbol target (.app (subst familyImages Source.domainPredicate) child) :=
  .impE (.eqPropER childBeta) childMember

def childGuards : Source.childContext.telescope.Realizes childImages target :=
  Telescope.Realizes.cons familyGuards Source.domainPredicate child childProof

def noRoots : ProofSyntax.HypothesisSubstitution (assumptions ([] : List (ClosedFormula Symbol)) context) target :=
  fun impossible => nomatch impossible

def bound : ProofSyntax Symbol target
    (subst childImages (.imp Source.inputExists Source.goal)) :=
  Source.familyContext.bindValue familyImages familyGuards noRoots Source.domainPredicate Source.domain_read
    Source.domain_formed child childProof Source.closeInput

def inputProof : ProofSyntax Symbol target (subst childImages Source.inputExists) := by
  have beta : ProofSyntax Symbol target (.eq (.app (.app familyValue child) child)
      (.and (.not (.eq child (.const .bottom))) (.not (.eq child (.const .bottom))))) :=
    CurriedGuardProgramProofs.beta2 familyBody child child
  have present := ProofSyntax.impE (.eqPropER beta) (.andI childNonbottom childNonbottom)
  apply ProofSyntax.exI child
  apply ProofSyntax.castIndices rfl ?_ present
  simp only [Source.resultPredicate, instantiate, HOL.subst, Subst.single, Subst.lift]
  rfl

def result : ProofSyntax Symbol target (subst childImages Source.goal) := .impE bound inputProof

theorem childMember_free : childMember.FunctionExtensionalityFree := by trivial
theorem childNonbottom_free : childNonbottom.FunctionExtensionalityFree :=
  ⟨AdmittedContainerInductionControls.motive_beta_free _ _, True.intro⟩

theorem typeGuards_free : ∀ {type} (position : Var [Source.valuePredicate] type),
    (typeGuards position).FunctionExtensionalityFree := by
  apply Telescope.Realizes.cons_free
  · intro type impossible
    nomatch impossible
  · exact ⟨True.intro, True.intro⟩

theorem familyProof_free : familyProof.FunctionExtensionalityFree := by
  unfold familyProof
  apply PredicateProducts.introduce_free
  exact ⟨True.intro, True.intro⟩

theorem familyGuards_free : ∀ {type} (position : Var [Source.familyCarrier, Source.valuePredicate] type),
    (familyGuards position).FunctionExtensionalityFree :=
  Telescope.Realizes.cons_free typeGuards Source.familyPredicate familyValue familyProof typeGuards_free familyProof_free

set_option backward.isDefEq.respectTransparency true in
theorem childBeta_free : childBeta.FunctionExtensionalityFree := by
  unfold childBeta
  exact childBetaEvidence.property

private theorem equalityApply_free {hypotheses : List (Formula Symbol context)}
    {first second : Formula Symbol context}
    (equality : ProofSyntax Symbol hypotheses (.eq first second)) (present : ProofSyntax Symbol hypotheses second)
    (equalityFree : equality.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (ProofSyntax.impE (ProofSyntax.eqPropER equality) present).FunctionExtensionalityFree :=
  ⟨equalityFree, presentFree⟩

set_option backward.isDefEq.respectTransparency true in
theorem childProof_free : childProof.FunctionExtensionalityFree := by
  unfold childProof
  exact equalityApply_free childBeta childMember childBeta_free childMember_free

theorem childGuards_free : ∀ {type} (position : Var [space, Source.familyCarrier, Source.valuePredicate] type),
    (childGuards position).FunctionExtensionalityFree :=
  Telescope.Realizes.cons_free familyGuards Source.domainPredicate child childProof familyGuards_free childProof_free

theorem bound_free : bound.FunctionExtensionalityFree := by
  apply GuardedContext.bindValue_free
  · exact familyGuards_free
  · intro impossible
    nomatch impossible
  · exact childProof_free
  · exact Source.closeInput_free

theorem inputProof_free : inputProof.FunctionExtensionalityFree := by
  unfold inputProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ⟨CurriedGuardProgramProofs.beta2_free _ _ _, ⟨childNonbottom_free, childNonbottom_free⟩⟩

theorem result_free : result.FunctionExtensionalityFree := ⟨bound_free, inputProof_free⟩

def outputBody : Formula Symbol context := .and incoming (subst childImages Source.goal)
def output : Formula Symbol AdmittedChildPremiseControls.context := .ex outputBody

def outputProof : ProofSyntax Symbol AdmittedChildPremiseControls.assumptions output :=
  .impE (ContextualTrinity.exImp (.allI (.impI (.andI
    (.hyp (Δ := target) ⟨0, by change 0 < Nat.succ _; exact Nat.zero_lt_succ _⟩) result))))
    SourceIndexSelectionControls.Cons.child

theorem outputProof_free : outputProof.FunctionExtensionalityFree := by
  unfold outputProof
  constructor
  · apply (ContextualTrinity.exImp_free _).mpr
    exact ⟨True.intro, result_free⟩
  · exact SourceIndexSelectionControls.Cons.child_free

theorem output_valid : (model.denote output AdmittedChildPremiseModelControls.world).down :=
  Soundness.extDerivation_sound outputProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (by intro type position; exact full type (AdmittedChildPremiseModelControls.world position))
    AdmittedChildPremiseModelControls.assumptions_realizable

theorem target_realizable : ∃ values : model.Valuation context, Soundness.SatisfiesHyps model values target := by
  have opening := SourceIndexSelectionControls.Cons.child_valid
  change ∃ slot : Ty.denote model.Carrier number, _ ∧ _ at opening
  obtain ⟨slot, _, body⟩ := opening
  refine ⟨model.extend AdmittedChildPremiseModelControls.world slot, ?_⟩
  intro formula inside
  rcases List.mem_cons.mp inside with rfl | rest
  · exact body
  · obtain ⟨old, member, rfl⟩ := List.mem_map.mp rest
    rw [Soundness.denote_weaken]
    exact AdmittedChildPremiseModelControls.assumptions_realizable old member

def badResultImages : Subst Symbol [space, space, Source.familyCarrier, Source.valuePredicate] context :=
  Subst.cons (.const .bottom) childImages

theorem bottom_result_refused : ¬ Nonempty (Source.resultContext.telescope.Realizes badResultImages target) := by
  rintro ⟨bad⟩
  obtain ⟨values, holds⟩ := target_realizable
  have valid := Soundness.extDerivation_sound (bad (.vz : Var [space, space, Source.familyCarrier, Source.valuePredicate] space)).erase
    (M := model) (ρ := values) (model.functionsRespectEqv_of_fullDomains full)
    (by intro type position; exact full type (values position)) holds
  change _ ∧ ¬ (model.denote (.const .bottom) values = model.denote (.const .bottom) values) at valid
  exact valid.2 rfl

theorem source_and_target_scopes_differ :
    [space, space, Source.familyCarrier, Source.valuePredicate].length = 4 ∧ context.length = 2 := ⟨rfl, rfl⟩

#print axioms outputProof_free
#print axioms output_valid
#print axioms bottom_result_refused

end
end Native
end Mettapedia.GSLT.LanguageDef.AdmittedDependentMethodControls
