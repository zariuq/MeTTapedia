import Mettapedia.Languages.HOLLight.AdmittedConstructorMethodCompilation
import Mettapedia.Languages.HOLLight.IndexedInductionSchemas
import Mettapedia.Languages.HOLLight.AdmittedMembershipSchemas
import Mettapedia.Logic.HOL.ConstantExpansionProofsFree
import Mettapedia.Logic.HOL.HOLLightBooleanConversions

/-!
# Joining an admitted constructor method to shared indexed induction

The concrete finite-row proof supplies the parametric method. A checked
bridge supplies the strengthened constructor method, and that derived proof
discharges the shared induction schema's sole premise. The original
representation laws remain attached to the resulting certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.HOLLight.AdmittedInductionComposition

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open HOL Mettapedia.GSLT.LanguageDef
open RetainedCompilation

/-- Reindex only the exactness proof, retaining the original executable
certificate and theorem value. -/
def reindexConclusion {Γ : HOL.Ctx AtomicTy} (names : ReverseTranslation.Naming Γ)
    {Δ : List (HOL.Formula Symbol Γ)} {first last : HOL.Formula Symbol Γ}
    (input : Compiled emptyAxiomPolicy names Δ first) (same : first = last) :
    Compiled emptyAxiomPolicy names Δ last :=
  ⟨input.proof, input.hypotheses_exact,
    input.conclusion_exact.trans (congrArg (ReverseTranslation.reverseCanonical names) same)⟩

def reindexAssumptions {Γ : HOL.Ctx AtomicTy} (names : ReverseTranslation.Naming Γ)
    {first last : List (HOL.Formula Symbol Γ)} {conclusion : HOL.Formula Symbol Γ}
    (input : Compiled emptyAxiomPolicy names first conclusion) (same : first = last) :
    Compiled emptyAxiomPolicy names last conclusion :=
  ⟨input.proof,
    input.hypotheses_exact.trans (congrArg (ReverseTranslation.reverseHypotheses names) same),
    input.conclusion_exact⟩

/-- Compose a proved premise with a single-premise schema without padding
either certificate with the other proof's context. -/
def dischargePremise {Γ : HOL.Ctx AtomicTy} (names : ReverseTranslation.Naming Γ)
    {Δ : List (HOL.Formula Symbol Γ)} {premise conclusion : HOL.Formula Symbol Γ}
    (produced : Compiled emptyAxiomPolicy names Δ premise)
    (consumer : Compiled emptyAxiomPolicy names [premise] conclusion) :
    Compiled emptyAxiomPolicy names Δ conclusion := by
  let joined := AdmittedMembershipSchemas.proveHypothesis produced.proof consumer.proof
    (produced.boolean.trans consumer.boolean.symm)
  refine ⟨joined, ?_, ?_⟩
  · change produced.proof.result.sequent.hyp ∪
      consumer.proof.result.sequent.hyp.erase produced.proof.result.sequent.concl =
        ReverseTranslation.reverseHypotheses names Δ
    rw [produced.hypotheses_exact, consumer.hypotheses_exact, produced.conclusion_exact,
      ReverseTranslation.reverseHypotheses_cons, ReverseTranslation.reverseHypotheses_nil]
    simp
  · change consumer.proof.result.sequent.concl = _
    exact consumer.conclusion_exact

/-- A hypothesis-free conversion changes the conclusion without importing
the argument's hypotheses into the conversion certificate. -/
def convertConclusion {Γ : HOL.Ctx AtomicTy} (names : ReverseTranslation.Naming Γ)
    {Δ : List (HOL.Formula Symbol Γ)} {first last : HOL.Formula Symbol Γ}
    (equation : Compiled emptyAxiomPolicy names [] (.eq first last))
    (argument : Compiled emptyAxiomPolicy names Δ first) (origin : ProofExecution.Origin) :
    Compiled emptyAxiomPolicy names Δ last := by
  let result := EqualityExpansion.eqMpResult equation.proof.result argument.proof.result
    (ReverseTranslation.reverseCanonical names last)
  have checked := EqualityExpansion.eqMpResult_checked equation.proof.result argument.proof.result
    (ReverseTranslation.reverseCanonical names first) (ReverseTranslation.reverseCanonical names last)
    equation.equalityView argument.conclusion_exact.symm
  let joined := CheckedProof.binary equation.proof argument.proof result
    (GraphExpansion.primitiveBlock (.inference (.eqMp equation.proof.result argument.proof.result)) result origin)
    (GraphExpansion.primitiveBlock_checked (.inference (.eqMp equation.proof.result argument.proof.result))
      result origin checked) origin
  refine ⟨joined, ?_, rfl⟩
  change equation.proof.result.sequent.hyp ∪ argument.proof.result.sequent.hyp = _
  rw [equation.hypotheses_exact, ReverseTranslation.reverseHypotheses_nil, argument.hypotheses_exact]
  exact Finset.empty_union _

namespace Source

open AdmittedNonbottomCompilation

def intermediate : HOL.Formula AdmittedContainerGeneratedControls.Symbol inputContext :=
  .imp member (.app (.app (ConstructorNonbottom.motive bottom constructors.index) value) index)

def conclusion : HOL.Formula AdmittedContainerGeneratedControls.Symbol inputContext :=
  .imp member (.not (.eq value bottom))

def beta : ProofSyntax AdmittedContainerGeneratedControls.Symbol [] (.eq intermediate conclusion) :=
  ProofSyntax.impCongr (.eqRefl member) (ConstructorNonbottom.motive_beta bottom value index)

theorem beta_free : beta.FunctionExtensionalityFree := by
  apply (ProofSyntax.impCongr_free _ _).mpr
  exact ⟨trivial, ConstructorNonbottom.motive_beta_free _ _ _⟩

end Source

variable (operations : AdmittedMembershipCompilation.Operations)

abbrev context := AdmittedNonbottomCompilation.inputContext.map
  (HOL.Ty.substitute (AdmittedMembershipCompilation.interpretation operations).types)

def family : RecursiveSpacePredicate.Contextual Symbol (context operations) :=
  AdmittedConstructorMethodCompilation.family.read (AdmittedMembershipCompilation.interpretation operations)

def root : HOL.Term Symbol (context operations)
    ((family operations).space ⇒ HOL.Ty.substitute
      (AdmittedMembershipCompilation.interpretation operations).types AdmittedNonbottomCompilation.constructors.index ⇒ .prop) :=
  (AdmittedMembershipCompilation.interpretation operations).term
    (AdmittedNonbottomCompilation.constructors.rootProgram AdmittedNonbottomCompilation.constructor)

def property : HOL.Term Symbol (context operations)
    ((family operations).space ⇒ HOL.Ty.substitute
      (AdmittedMembershipCompilation.interpretation operations).types AdmittedNonbottomCompilation.constructors.index ⇒ .prop) :=
  (AdmittedMembershipCompilation.interpretation operations).term
    (ConstructorNonbottom.motive AdmittedNonbottomCompilation.bottom AdmittedNonbottomCompilation.constructors.index)

def point : HOL.Term Symbol (context operations) (family operations).space :=
  (AdmittedMembershipCompilation.interpretation operations).term AdmittedNonbottomCompilation.value

def target : HOL.Term Symbol (context operations) (HOL.Ty.substitute
    (AdmittedMembershipCompilation.interpretation operations).types AdmittedNonbottomCompilation.constructors.index) :=
  (AdmittedMembershipCompilation.interpretation operations).term AdmittedNonbottomCompilation.index

def inputs := IndexedInductionSchemas.Bindings.ofSignature (family operations) (root operations)
  (property operations) (point operations) (target operations)

def names (prefixName : String) : ReverseTranslation.Naming (context operations) :=
  AdmittedConstructorMethodCompilation.closedNames operations prefixName

set_option backward.isDefEq.respectTransparency false in
theorem concrete_method_image :
    (AdmittedMembershipCompilation.interpretation operations).term AdmittedConstructorMethodCompilation.closedConclusion =
      (inputs operations).instanceParametric := by
  rw [AdmittedConstructorMethodCompilation.closedConclusion_source,
    RecursiveSpacePredicate.Contextual.read_parametricMethod]
  unfold AdmittedConstructorMethodCompilation.lifted
  rw [RecursiveSpacePredicate.Contextual.read_indexedLift]
  exact (IndexedInductionSchemas.Bindings.ofSignature_parametric
    (family operations) (root operations) (property operations) (point operations) (target operations)).symm

#print axioms concrete_method_image

def concreteMethod (callerNames : ReverseTranslation.Naming (context operations)) :
    Compiled emptyAxiomPolicy callerNames
      ((AdmittedConstructorMethodCompilation.closedAssumptions.map
        (AdmittedMembershipCompilation.interpretation operations).term).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (inputs operations).instanceParametric) :=
  reindexConclusion callerNames
    (InterpretedCompilation.compile (AdmittedMembershipCompilation.interpretation operations)
      AdmittedConstructorMethodCompilation.closedProof AdmittedConstructorMethodCompilation.closedProof_free
      callerNames ("admitted-closed-constructor-method", 0))
    (congrArg ImpredicativeConnectives.expand (concrete_method_image operations))

#print axioms concreteMethod

def compile (prefixName : String) (callerNames : ReverseTranslation.Naming (context operations)) :
    Compiled emptyAxiomPolicy callerNames
      ((AdmittedConstructorMethodCompilation.closedAssumptions.map
        (AdmittedMembershipCompilation.interpretation operations).term).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand (inputs operations).instanceConclusion) :=
  let concrete := concreteMethod operations callerNames
  let bridge := (inputs operations).compileBridge (prefixName ++ "_bridge") callerNames
  let induction := (inputs operations).compile (prefixName ++ "_induction") callerNames
  let method := dischargePremise callerNames concrete bridge
  dischargePremise callerNames method induction

set_option backward.isDefEq.respectTransparency false in
theorem intermediate_image :
    (AdmittedMembershipCompilation.interpretation operations).term Source.intermediate =
      (inputs operations).instanceConclusion := by
  apply Eq.trans ?_ (IndexedInductionSchemas.Bindings.ofSignature_conclusion
    (family operations) (root operations) (property operations) (point operations) (target operations)).symm
  unfold Source.intermediate AdmittedNonbottomCompilation.member
    IndexedConstructorGuards.PositionPrograms.nonbottomMember
  rw [HOL.TermInterpretation.term_imp, HOL.TermInterpretation.term_app,
    HOL.TermInterpretation.term_app, RecursiveSpacePredicate.Contextual.read_memberProgram]
  rfl

def compileIntermediate (prefixName : String) (callerNames : ReverseTranslation.Naming (context operations)) :
    Compiled emptyAxiomPolicy callerNames
      ((AdmittedConstructorMethodCompilation.closedAssumptions.map
        (AdmittedMembershipCompilation.interpretation operations).term).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand
        ((AdmittedMembershipCompilation.interpretation operations).term Source.intermediate)) :=
  reindexConclusion callerNames (compile operations prefixName callerNames)
    (congrArg ImpredicativeConnectives.expand (intermediate_image operations).symm)

def compileSource (prefixName : String) (callerNames : ReverseTranslation.Naming (context operations)) :
    Compiled emptyAxiomPolicy callerNames
      ((AdmittedConstructorMethodCompilation.closedAssumptions.map
        (AdmittedMembershipCompilation.interpretation operations).term).map ImpredicativeConnectives.expand)
      (ImpredicativeConnectives.expand
        ((AdmittedMembershipCompilation.interpretation operations).term Source.conclusion)) :=
  let equation := InterpretedCompilation.compile (AdmittedMembershipCompilation.interpretation operations)
    Source.beta Source.beta_free callerNames ("admitted-induction-result-beta", 0)
  convertConclusion callerNames equation (compileIntermediate operations prefixName callerNames)
    ("admitted-induction-result-transport", 0)

def closedAssumptions : List (HOL.ClosedFormula Symbol) :=
  (AdmittedNonbottomCompilation.assumptions.map
    (AdmittedMembershipCompilation.interpretation operations).term).map ImpredicativeConnectives.expand

set_option backward.isDefEq.respectTransparency false in
theorem input_assumptions :
    (AdmittedConstructorMethodCompilation.closedAssumptions.map
      (AdmittedMembershipCompilation.interpretation operations).term).map ImpredicativeConnectives.expand =
    HOL.weakenHyps (σ := operations.number) (HOL.weakenHyps (σ := operations.space) (closedAssumptions operations)) := by
  have source : AdmittedConstructorMethodCompilation.closedAssumptions =
      AdmittedNonbottomCompilation.assumptions.map (HOL.weakenCtx AdmittedNonbottomCompilation.inputContext) := by
    rfl
  rw [source]
  change AdmittedNonbottomCompilation.assumptions.map
      (fun formula => ImpredicativeConnectives.expand
        ((AdmittedMembershipCompilation.interpretation operations).term
          (HOL.weakenCtx AdmittedNonbottomCompilation.inputContext formula))) =
    AdmittedNonbottomCompilation.assumptions.map
      (fun formula => HOL.weaken (HOL.weaken (ImpredicativeConnectives.expand
        ((AdmittedMembershipCompilation.interpretation operations).term formula))))
  apply List.map_congr_left
  intro formula _
  rw [HOL.TermInterpretation.term_weakenCtx, HOLLightBooleanConversions.expand_weakenCtx]
  rfl

def outerBody : HOL.Formula Symbol [operations.space] :=
  .all (ImpredicativeConnectives.expand
    ((AdmittedMembershipCompilation.interpretation operations).term Source.conclusion))

def outerNames : ReverseTranslation.Naming [operations.space] :=
  ReverseTranslation.Naming.cons
    (ReverseTranslation.freshBinderName ReverseTranslation.Naming.empty
      (outerBody operations) (closedAssumptions operations)) ReverseTranslation.Naming.empty

def inputNames : ReverseTranslation.Naming (context operations) :=
  ReverseTranslation.Naming.cons
    (ReverseTranslation.freshBinderName (outerNames operations)
      (ImpredicativeConnectives.expand
        ((AdmittedMembershipCompilation.interpretation operations).term Source.conclusion))
      (HOL.weakenHyps (σ := operations.space) (closedAssumptions operations))) (outerNames operations)

def compileClosed (prefixName : String) :
    Compiled emptyAxiomPolicy ReverseTranslation.Naming.empty (closedAssumptions operations)
      (ImpredicativeConnectives.expand
        ((AdmittedMembershipCompilation.interpretation operations).term AdmittedNonbottomCompilation.statement)) := by
  let body := compileSource operations prefixName (inputNames operations)
  let bodyTyped := reindexAssumptions (inputNames operations) body (input_assumptions operations)
  let one := Compiled.universalIntro bodyTyped ("admitted-induction-close-index", 0)
  exact Compiled.universalIntro one ("admitted-induction-close-value", 0)

#print axioms compile
#print axioms intermediate_image
#print axioms Source.beta_free
#print axioms compileSource
#print axioms input_assumptions
#print axioms compileClosed

end Mettapedia.Languages.HOLLight.AdmittedInductionComposition
