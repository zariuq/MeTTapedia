import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILLearnedProofRelevantAdmission
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SyntacticContextualCategory
import Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist

/-!
# Checked MIL derivations as intrinsic Prime programs

This module closes one exact-image part of the Prime hosted-language seam.
The generic checker retains the authored proof tree; the independent
proof-relevant semantics interprets it as a relation; and a typed vocabulary
quotation internalizes that relation as an inhabitant of Prime's native
indexed hypothesis family.

The construction is general over every checked `MIL.Rel source target` goal in
the learned calculus language.  It is not a special grandparent evaluator, and it
does not claim that every Prime typing judgment is already presented to the
generic checker.  A formed native context is required explicitly.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILCheckedNativePrograms

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckedNativeWaist
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open MILLearnedProofRelevantAdmission

universe uSort uCarrier uPrimitive

/-! ## Formed native vocabulary quotations -/

/-- A native vocabulary quotation together with the formation evidence for
its ambient declaration-aware context.  This is the authoritative input
shape: a raw telescope cannot be substituted for a formed context. -/
structure FormedVocabularyQuotation
    (vocabulary : MILSchemaElaboration.Semantic.Vocabulary.{uSort, uCarrier,
      uPrimitive})
    (context : Tower.Ctx n)
    extends IntrinsicMILHypothesis.TypedVocabularyQuotation vocabulary context
    where
  contextWellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules context

namespace FormedVocabularyQuotation

/-- The quotation's ambient telescope as an object of the syntactic
contextual category. -/
def formedContext
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : FormedVocabularyQuotation vocabulary context) :
    SyntacticContextual.FormedContext IntrinsicMILHypothesis.rules where
  arity := n
  context := context
  wellFormed := quotation.contextWellFormed

/-- The native hypothesis family at the quoted endpoints is independently
formed over the quotation's formed context. -/
def hypothesisType
    {vocabulary : MILSchemaElaboration.Semantic.Vocabulary}
    {context : Tower.Ctx n}
    (quotation : FormedVocabularyQuotation vocabulary context)
    (source target : vocabulary.SortCode) :
    SyntacticContextual.TypeOver quotation.formedContext where
  code := IntrinsicMILHypothesis.hypothesisApp quotation.sorts
    quotation.primitives (quotation.sortCode source)
      (quotation.sortCode target)
  level := .sort IntrinsicMILHypothesis.hypothesisLevel
  isUniverse := .sort IntrinsicMILHypothesis.hypothesisLevel
  formed := IntrinsicMILHypothesis.hypothesisApp_hasType
    quotation.sortsTyping quotation.primitivesTyping
      (quotation.sortCodeTyping source) (quotation.sortCodeTyping target)

end FormedVocabularyQuotation

/-! ## One checked derivation, one native proof program -/

abbrev HostedQuotation (context : Tower.Ctx n) :=
  FormedVocabularyQuotation MILLearnedProofRelevantAdmission.vocabulary context

/-- The native term constructed directly from independent relational
evidence.  This is the language-specific realization map used by both the
concrete checked-program API and the common checked-native waist. -/
noncomputable def nativeTermOfReach
    {context : Tower.Ctx n} (quotation : HostedQuotation context)
    {source target : Pattern} (evidence : Reach source target) :
    SyntacticContextual.Term quotation.formedContext
      (quotation.hypothesisType () ()) := by
  let witness := evidence.toIntrinsic
  let program := IntrinsicMILSemanticAdequacy.Program.ofHypothesis
    quotation.toTypedVocabularyQuotation witness.hypothesis
  exact
    { code := IntrinsicMILHypothesis.quoteHypothesis
        quotation.toTypedVocabularyQuotation witness.hypothesis
      typed := program.hasType }

/-- A native artifact is an intrinsically typed term together with its formed
type index.  The sigma permits different hosted goal families to choose
different dependent result types while sharing one generic waist. -/
abbrev NativeArtifact
    {context : Tower.Ctx n} (quotation : HostedQuotation context)
    (_goal : Pattern × Pattern) :=
  Sigma fun type : SyntacticContextual.TypeOver quotation.formedContext =>
    SyntacticContextual.Term quotation.formedContext type

/-- Rel/Chain evidence displayed as Prime's native indexed `Hyp` term. -/
noncomputable def nativeRealization
    {context : Tower.Ctx n} (quotation : HostedQuotation context) :
    NativeRealization (Pattern × Pattern)
      (fun goal => MILLearnedProofRelevantAdmission.Meaning
        (MILCheckedChain.relates goal.1 goal.2)) where
  Artifact := NativeArtifact quotation
  realize := by
    intro goal evidence
    exact ⟨quotation.hypothesisType () (), nativeTermOfReach quotation evidence⟩

/-- The common checked-to-native waist instantiated by the learned Rel/Chain
calculus language.  Checking, interpretation, and native construction remain three
separate fields. -/
noncomputable def checkedNativeWaist
    {context : Tower.Ctx n} (quotation : HostedQuotation context) :
    CheckedNativeWaist MILCheckedChain.learned.target where
  Meaning := MILLearnedProofRelevantAdmission.Meaning
  semantics := MILLearnedProofRelevantAdmission.learnedSemantics.targetSemantics
  Goal := Pattern × Pattern
  surface := fun goal => MILCheckedChain.relates goal.1 goal.2
  native := nativeRealization quotation

/-- A generic-checker derivation of one relational goal.  Its native term,
typing derivation, and proof-relevant denotation are derived below rather than
stored as unrelated claims. -/
structure CheckedNativeProgram
    {context : Tower.Ctx n} (quotation : HostedQuotation context)
    (source target : Pattern) : Type where
  checked : Derivation MILCheckedChain.learned.target
    (MILCheckedChain.relates source target)

namespace CheckedNativeProgram

/-- Interpret the exact checked derivation in the independently supplied
proof-relevant semantics. -/
noncomputable def relationalEvidence
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (program : CheckedNativeProgram quotation source target) :
    Reach source target :=
  MILLearnedProofRelevantAdmission.learnedSemantics.interpret program.checked

/-- Turn the retained relational derivation into an intrinsic hypothesis
program without forgetting its intermediate witnesses. -/
noncomputable def intrinsicWitness
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (program : CheckedNativeProgram quotation source target) :
    IntrinsicWitness source target :=
  program.relationalEvidence.toIntrinsic

/-- Structural evidence that the quoted term belongs to the native
constructor image. -/
noncomputable def intrinsicProgram
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (program : CheckedNativeProgram quotation source target) :
    IntrinsicMILSemanticAdequacy.Program quotation.toTypedVocabularyQuotation
      (source := ()) (target := ())
      (IntrinsicMILHypothesis.quoteHypothesis
        quotation.toTypedVocabularyQuotation
        program.intrinsicWitness.hypothesis) :=
  IntrinsicMILSemanticAdequacy.Program.ofHypothesis
    quotation.toTypedVocabularyQuotation program.intrinsicWitness.hypothesis

/-- The checker-to-native bridge lands in a proof-carrying term over a formed
context and a formed indexed-family type. -/
noncomputable def nativeTerm
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (program : CheckedNativeProgram quotation source target) :
    SyntacticContextual.Term quotation.formedContext
      (quotation.hypothesisType () ()) :=
  nativeTermOfReach quotation program.relationalEvidence

/-- The concrete Rel/Chain API is exactly a consumer of the common waist. -/
noncomputable def toWaist
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (program : CheckedNativeProgram quotation source target) :
    (checkedNativeWaist quotation).CheckedProgram (source, target) :=
  ⟨program.checked⟩

/-- Projecting the common retained graph produces the same intrinsic term as
the specialized Rel/Chain API. -/
theorem toWaist_artifact_code
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (program : CheckedNativeProgram quotation source target) :
    program.toWaist.artifact.2.code = program.nativeTerm.code :=
  rfl

/-- The native program retains an inhabitant of its exact relational fibre,
not only Boolean endpoint reachability. -/
noncomputable def nativeEvidence
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern}
    (program : CheckedNativeProgram quotation source target) :
    program.intrinsicProgram.denotation.evidence source target := by
  exact (program.intrinsicProgram.evidenceEquiv source target).symm
    (by
      simpa [intrinsicProgram, intrinsicWitness] using
        program.intrinsicWitness.evidence)

end CheckedNativeProgram

/-! ## Exact raw-proof retention -/

/-- The hosted image of an externally supplied raw proof.  Exact erasure is
part of the carrier, so a different proof of the same endpoint is not silently
substituted. -/
structure CheckedRawNativeProgram
    {context : Tower.Ctx n} (quotation : HostedQuotation context)
    (source target : Pattern) (raw : RawProof) : Type where
  checked : Derivation MILCheckedChain.learned.target
    (MILCheckedChain.relates source target)
  erases : checked.erase = raw

namespace CheckedRawNativeProgram

def toChecked
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof}
    (program : CheckedRawNativeProgram quotation source target raw) :
    CheckedNativeProgram quotation source target :=
  ⟨program.checked⟩

/-- The specialized exact-erasure carrier maps directly to the common waist. -/
noncomputable def toWaist
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof}
    (program : CheckedRawNativeProgram quotation source target raw) :
    (checkedNativeWaist quotation).CheckedRawProgram (source, target) raw where
  checked := program.checked
  erases := program.erases

/-- The common waist contains no additional proof object beyond the
specialized exact-erasure carrier. -/
noncomputable def ofWaist
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof}
    (program : (checkedNativeWaist quotation).CheckedRawProgram
      (source, target) raw) :
    CheckedRawNativeProgram quotation source target raw where
  checked := program.checked
  erases := program.erases

/-- Specialized and common exact-erasure programs are equivalent, not merely
equisupported. -/
noncomputable def waistEquiv
    {context : Tower.Ctx n} {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof} :
    CheckedRawNativeProgram quotation source target raw ≃
      (checkedNativeWaist quotation).CheckedRawProgram
        (source, target) raw where
  toFun := toWaist
  invFun := ofWaist
  left_inv := by
    intro program
    cases program
    rfl
  right_inv := by
    intro program
    cases program
    rfl

end CheckedRawNativeProgram

/-- The raw generic checker accepts exactly when the same raw proof inhabits
the formed native bridge. -/
theorem checkedRaw_iff_nonempty_native
    {context : Tower.Ctx n} (quotation : HostedQuotation context)
    (source target : Pattern) (raw : RawProof) :
    checkRaw MILCheckedChain.learned.target
        (MILCheckedChain.relates source target) raw = true ↔
      Nonempty (CheckedRawNativeProgram quotation source target raw) := by
  constructor
  · intro accepted
    rcases (G2_checkRaw_iff_exists_derivation_erases_to.mp accepted) with
      ⟨derivation, erases⟩
    exact ⟨⟨derivation, erases⟩⟩
  · rintro ⟨program⟩
    rw [← program.erases]
    exact checkRaw_erase program.checked

/-! ## An inhabited formed quotation -/

namespace FormedQuotationCanary

/-- Extend the native family parameters by one sort inhabitant. -/
def contextSPS : Tower.Ctx 3 :=
  .snoc IntrinsicMILHypothesis.contextSP (.var 1)

/-- The common primitive-relation type at the chosen sort inhabitant. -/
def relationAtSPS : Tower.Tm 3 :=
  .app (.app (.var 1) (.var 0)) (.var 0)

/-- Extend by the first primitive witness. -/
def contextSPSM : Tower.Ctx 4 :=
  .snoc contextSPS relationAtSPS

/-- The same primitive-relation type after the first witness is added. -/
def relationAtSPSM : Tower.Tm 4 :=
  .app (.app (.var 2) (.var 1)) (.var 1)

/-- Extend by the second primitive witness.  The resulting context contains
exactly the data needed to quote the learned mother/father vocabulary. -/
def contextSPSMF : Tower.Ctx 5 :=
  .snoc contextSPSM relationAtSPSM

def contextSWellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules
      IntrinsicMILHypothesis.contextS := by
  apply ContextWellFormed.snoc
  · exact .nil
  · exact IntrinsicMILHypothesis.includeTowerTyping (.headType (.sort
      IntrinsicMILHypothesis.sortLevel))
  · exact .sort (.succ IntrinsicMILHypothesis.sortLevel)

def contextSPWellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules
      IntrinsicMILHypothesis.contextSP := by
  apply ContextWellFormed.snoc
  · exact contextSWellFormed
  · exact IntrinsicMILHypothesis.includeTowerTyping
      IntrinsicMILHypothesis.primitiveFamilyType_hasType
  · exact .sort IntrinsicMILHypothesis.primitiveFamilyTypeLevel

def contextSPSWellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules contextSPS := by
  apply ContextWellFormed.snoc
  · exact contextSPWellFormed
  · exact Presentation.HasType.var 1
  · exact .sort IntrinsicMILHypothesis.sortLevel

theorem relationAtSPS_hasType :
    IntrinsicMILHypothesis.HasType contextSPS relationAtSPS
      (sortTm IntrinsicMILHypothesis.primitiveLevel) := by
  apply IntrinsicMILHypothesis.primitiveFamilyApp_hasType
  · exact Presentation.HasType.var 1
  · exact Presentation.HasType.var 0
  · exact Presentation.HasType.var 0

def contextSPSMWellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules contextSPSM := by
  apply ContextWellFormed.snoc
  · exact contextSPSWellFormed
  · exact relationAtSPS_hasType
  · exact .sort IntrinsicMILHypothesis.primitiveLevel

theorem relationAtSPSM_hasType :
    IntrinsicMILHypothesis.HasType contextSPSM relationAtSPSM
      (sortTm IntrinsicMILHypothesis.primitiveLevel) := by
  apply IntrinsicMILHypothesis.primitiveFamilyApp_hasType
  · exact Presentation.HasType.var 2
  · exact Presentation.HasType.var 1
  · exact Presentation.HasType.var 1

def contextSPSMFWellFormed :
    ContextWellFormed IntrinsicMILHypothesis.rules contextSPSMF := by
  apply ContextWellFormed.snoc
  · exact contextSPSMWellFormed
  · exact relationAtSPSM_hasType
  · exact .sort IntrinsicMILHypothesis.primitiveLevel

/-- A concrete formed quotation of the learned vocabulary.  It witnesses that
the checked-to-native bridge has an inhabited source, independently of the
grandparent proof subsequently passed through it. -/
def quotation : HostedQuotation contextSPSMF where
  sorts := .var 4
  primitives := .var 3
  sortCode := fun _ => .var 2
  primitiveCode := fun symbol =>
    match symbol with
    | .mother => .var 1
    | .father => .var 0
  sortsTyping := Presentation.HasType.var 4
  primitivesTyping := Presentation.HasType.var 3
  sortCodeTyping := fun _ => Presentation.HasType.var 2
  primitiveCodeTyping := by
    intro source target symbol
    cases symbol with
    | mother => exact Presentation.HasType.var 1
    | father => exact Presentation.HasType.var 0
  contextWellFormed := contextSPSMFWellFormed

end FormedQuotationCanary

/-! ## Positive and negative controls -/

noncomputable def grandparent
    {context : Tower.Ctx n} (quotation : HostedQuotation context) :
    CheckedRawNativeProgram quotation MILCheckedChain.alice
      MILCheckedChain.carol MILCheckedChain.grandparentProof where
  checked := MILLearnedProofRelevantAdmission.grandparentDerivation
  erases := MILLearnedProofRelevantAdmission.grandparentDerivation_erase

/-- The checked grandparent proof preserves its exact raw artifact, constructs
a term in a formed Prime context, and retains proof-relevant relational
evidence. -/
theorem grandparent_preserves_checker_native_and_relational_layers
    {context : Tower.Ctx n} (quotation : HostedQuotation context) :
    (grandparent quotation).checked.erase = MILCheckedChain.grandparentProof ∧
      IntrinsicMILHypothesis.HasType context
        (grandparent quotation).toChecked.nativeTerm.code
        (quotation.hypothesisType () ()).code ∧
      Nonempty
        ((grandparent quotation).toChecked.intrinsicProgram.denotation.evidence
          MILCheckedChain.alice MILCheckedChain.carol) := by
  exact ⟨(grandparent quotation).erases,
    (grandparent quotation).toChecked.nativeTerm.typed,
    ⟨(grandparent quotation).toChecked.nativeEvidence⟩⟩

/-- The positive control is inhabited without assuming a quotation from the
caller: the concrete formed vocabulary quotes the checked grandparent proof
all the way into a typed native program. -/
theorem concrete_grandparent_is_checked_native_and_relational :
    (grandparent FormedQuotationCanary.quotation).checked.erase =
        MILCheckedChain.grandparentProof ∧
      IntrinsicMILHypothesis.HasType FormedQuotationCanary.contextSPSMF
        (grandparent FormedQuotationCanary.quotation).toChecked.nativeTerm.code
        (FormedQuotationCanary.quotation.hypothesisType () ()).code ∧
      Nonempty
        ((grandparent FormedQuotationCanary.quotation).toChecked.intrinsicProgram.denotation.evidence
          MILCheckedChain.alice MILCheckedChain.carol) :=
  grandparent_preserves_checker_native_and_relational_layers
    FormedQuotationCanary.quotation

/-- The concrete positive control crosses the common waist with the identical
raw proof and the identical native term projection. -/
theorem concrete_grandparent_crosses_common_waist :
    (grandparent FormedQuotationCanary.quotation).toWaist.checked.erase =
        MILCheckedChain.grandparentProof ∧
      (grandparent FormedQuotationCanary.quotation).toWaist.toChecked.artifact.2.code =
        (grandparent FormedQuotationCanary.quotation).toChecked.nativeTerm.code := by
  exact ⟨(grandparent FormedQuotationCanary.quotation).erases,
    CheckedNativeProgram.toWaist_artifact_code _⟩

/-- The ill-shared-middle raw proof cannot cross the checker-to-native seam.
Unsupported or rejected proof syntax therefore cannot acquire a typed native
program merely because its desired endpoint is meaningful. -/
theorem wrong_middle_has_no_native_program
    {context : Tower.Ctx n} (quotation : HostedQuotation context) :
    ¬ Nonempty
      (CheckedRawNativeProgram quotation MILCheckedChain.alice
        MILCheckedChain.bob MILCheckedChain.wrongMiddleProof) := by
  intro inhabited
  have accepted :=
    (checkedRaw_iff_nonempty_native quotation MILCheckedChain.alice
      MILCheckedChain.bob MILCheckedChain.wrongMiddleProof).2 inhabited
  rw [MILCheckedChain.wrongMiddleProof_rejected] at accepted
  contradiction

/-- The refusing control is concrete as well: even the inhabited formed
quotation cannot turn an ill-shared-middle raw tree into a native program. -/
theorem concrete_wrong_middle_has_no_native_program :
    ¬ Nonempty
      (CheckedRawNativeProgram FormedQuotationCanary.quotation
        MILCheckedChain.alice MILCheckedChain.bob
        MILCheckedChain.wrongMiddleProof) :=
  wrong_middle_has_no_native_program FormedQuotationCanary.quotation

/-- The same refusing proof cannot inhabit the common waist. -/
theorem concrete_wrong_middle_has_no_common_waist_program :
    ¬ Nonempty
      ((checkedNativeWaist FormedQuotationCanary.quotation).CheckedRawProgram
        (MILCheckedChain.alice, MILCheckedChain.bob)
        MILCheckedChain.wrongMiddleProof) := by
  intro inhabited
  apply concrete_wrong_middle_has_no_native_program
  rcases inhabited with ⟨program⟩
  exact ⟨CheckedRawNativeProgram.ofWaist program⟩

#print axioms checkedRaw_iff_nonempty_native
#print axioms grandparent_preserves_checker_native_and_relational_layers
#print axioms concrete_grandparent_is_checked_native_and_relational
#print axioms wrong_middle_has_no_native_program
#print axioms concrete_wrong_middle_has_no_native_program
#print axioms CheckedRawNativeProgram.waistEquiv
#print axioms concrete_grandparent_crosses_common_waist
#print axioms concrete_wrong_middle_has_no_common_waist_program

end MILCheckedNativePrograms
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
