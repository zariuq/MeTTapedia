import Mettapedia.Languages.Metamath.InferenceNormalFoldReflection
import Mettapedia.Languages.Metamath.InferenceNormalParserTrace

/-!
# Exact source reflection for accepted normal Metamath traces

This module joins the parser's exact source-ordered normal trace to the
proof-relevant native stack certificate.  The result is one source-pinned
generated proof tree whose authored postfix labels are exactly the submitted
parser labels and whose assembled derivation inhabits the generated native
`Proves` judgment.

All runtime execution and projection lookup use the same pre-insertion
database.  The accepted boundary additionally retains the exact post-insert
database, target freshness, and absence of self-reference.  No chronology is
read from the projection's label-sorted assertion collection.

The theorem consumes an exact parser trace.  Constructing that trace from the
whole byte-parser loop requires a separate token-ledger invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.InferenceNormalTraceReflection

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceNormalStepReflection
open Mettapedia.Languages.Metamath.InferenceNormalFoldReflection
open Mettapedia.Languages.Metamath.InferenceNormalParserTrace
open Metamath.Verify

/-- Retained generated native evidence for one accepted exact normal trace.
The tree is data in `Type`; the remaining fields certify its exact relationship
to the submitted tokens and the pre- and post-insertion runtime states. -/
structure ExactNormalSourceTreeEvidence
    (s : ParserState) (targetLabel : String) (targetFrame : RuntimeFrame)
    (firstToken : ByteSlice) (remainingTokens : List ByteSlice)
    (initial final : RuntimeProofState)
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (formula : ConstantHeadedFormula)
    (hprojection : presentationOfProjection? projection = some target.1) : Type where
  tree : GeneratedProvesTree projection target formula
  labels_eq :
    tree.labels = submittedNormalLabels firstToken remainingTokens
  erasure_eq :
    (tree.toDerivation hprojection).erase = tree.canonicalRawProof
  postfix_eq :
    rawProofLeadingPremisePostfixLabels
        (tree.toDerivation hprojection).erase =
      submittedNormalLabels firstToken remainingTokens
  exact_fold :
    (submittedNormalLabels firstToken remainingTokens).foldlM
        (fun state label => s.db.stepNormal state label)
        {initial with ptp := .normal} = .ok final
  final_formula : final.fmla = formula.toRuntime
  final_stack : final.stack = #[formula.toRuntime]
  post_db :
    (s.finishProof final).db =
      s.db.insert final.pos targetLabel
        (.assert formula.toRuntime targetFrame)
  target_fresh : s.db.find? targetLabel = none
  no_self_reference :
    targetLabel ∉ submittedNormalLabels firstToken remainingTokens

/-- The generic generated native derivation retained by exact source-tree
evidence. -/
def ExactNormalSourceTreeEvidence.nativeEvidence
    {s : ParserState} {targetLabel : String} {targetFrame : RuntimeFrame}
    {firstToken : ByteSlice} {remainingTokens : List ByteSlice}
    {initial final : RuntimeProofState}
    {projection : PrefixProjection} {target : ValidatedPresentation}
    {formula : ConstantHeadedFormula}
    {hprojection : presentationOfProjection? projection = some target.1}
    (evidence : ExactNormalSourceTreeEvidence s targetLabel targetFrame
      firstToken remainingTokens initial final projection target formula
      hprojection) :
    Derivation target (proves (encodeFormula formula)) :=
  evidence.tree.toDerivation hprojection

/-- Construct retained Type-valued native evidence from an accepted exact
normal parser trace. -/
noncomputable def exactNormalTrace_sourceTreeEvidence
    (s : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (targetFrame : RuntimeFrame)
    (firstToken : ByteSlice) (remainingTokens : List ByteSlice)
    (initial afterFirst final : RuntimeProofState)
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final)
    (hfinish : (s.finishProof final).db.error? = none)
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (formula : ConstantHeadedFormula)
    (hproject : projectPrefix? s.db = some projection)
    (hprojection : presentationOfProjection? projection = some target.1)
    (htargetFormula : targetFormula = formula.toRuntime) :
    ExactNormalSourceTreeEvidence s targetLabel targetFrame firstToken
      remainingTokens initial final projection target formula hprojection := by
  obtain ⟨hfold, _hlabel, hfinalFormula, _hframe, _hmode,
      hfinalStack, hpost, hfresh, hnoSelf⟩ :=
    trace.accepted_prefix_boundary hfinish
  let base : RuntimeProofState := {initial with ptp := .normal}
  have hbaseStack : base.stack = #[] := by
    simp [base, trace.initial_eq, DB.mkProofState]
  let seed := NativeStackCertificate.of_stack_eq_empty
    s.db projection target base hbaseStack
  have hfoldBase :
      (submittedNormalLabels firstToken remainingTokens).foldlM
          (fun state label => s.db.stepNormal state label) base = .ok final := by
    simpa [base] using hfold
  have finalCertificate :
      NativeStackCertificate s.db projection target base
        (submittedNormalLabels firstToken remainingTokens) final := by
    simpa using NativeStackCertificate.foldlM hprojection hproject seed
      (submittedNormalLabels firstToken remainingTokens) hfoldBase
  have hstackFormula : final.stack = #[formula.toRuntime] := by
    simpa [htargetFormula] using hfinalStack
  let extracted := NativeStackCertificate.extractSingletonTree
    finalCertificate formula hstackFormula
  let tree : GeneratedProvesTree projection target formula := extracted.1
  have hlabels :
      tree.labels = submittedNormalLabels firstToken remainingTokens :=
    extracted.2
  have herasure :
      (tree.toDerivation hprojection).erase = tree.canonicalRawProof :=
    tree.erase_toDerivation hprojection
  have hpostfix :
      rawProofLeadingPremisePostfixLabels
          (tree.toDerivation hprojection).erase =
        submittedNormalLabels firstToken remainingTokens := by
    calc
      rawProofLeadingPremisePostfixLabels
          (tree.toDerivation hprojection).erase = tree.labels :=
        tree.erase_toDerivation_postfixLabels hprojection
      _ = submittedNormalLabels firstToken remainingTokens := hlabels
  have hfinalFormula' : final.fmla = formula.toRuntime :=
    hfinalFormula.trans htargetFormula
  have hpost' :
      (s.finishProof final).db =
        s.db.insert final.pos targetLabel
          (.assert formula.toRuntime targetFrame) := by
    simpa [htargetFormula] using hpost
  exact
    { tree := tree
      labels_eq := hlabels
      erasure_eq := herasure
      postfix_eq := hpostfix
      exact_fold := hfold
      final_formula := hfinalFormula'
      final_stack := hstackFormula
      post_db := hpost'
      target_fresh := hfresh
      no_self_reference := hnoSelf }

/-- An accepted exact normal parser trace reflects to one source-pinned native
proof tree over the same pre-insertion projection.

The fold equation retains both complete parser proof states.  The erasure and
postfix equations expose the generated native derivation independently of the
runtime execution, while the final three fields close the insertion boundary
and rule out use of the theorem being proved. -/
theorem exactNormalTrace_reflects_sourceTree
    (s : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (targetFrame : RuntimeFrame)
    (firstToken : ByteSlice) (remainingTokens : List ByteSlice)
    (initial afterFirst final : RuntimeProofState)
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final)
    (hfinish : (s.finishProof final).db.error? = none)
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (formula : ConstantHeadedFormula)
    (hproject : projectPrefix? s.db = some projection)
    (hprojection : presentationOfProjection? projection = some target.1)
    (htargetFormula : targetFormula = formula.toRuntime) :
    ∃ tree : GeneratedProvesTree projection target formula,
      tree.labels = submittedNormalLabels firstToken remainingTokens ∧
      (tree.toDerivation hprojection).erase = tree.canonicalRawProof ∧
      rawProofLeadingPremisePostfixLabels
          (tree.toDerivation hprojection).erase =
        submittedNormalLabels firstToken remainingTokens ∧
      (submittedNormalLabels firstToken remainingTokens).foldlM
          (fun state label => s.db.stepNormal state label)
          {initial with ptp := .normal} = .ok final ∧
      final.fmla = formula.toRuntime ∧
      final.stack = #[formula.toRuntime] ∧
      (s.finishProof final).db =
        s.db.insert final.pos targetLabel
          (.assert formula.toRuntime targetFrame) ∧
      s.db.find? targetLabel = none ∧
      targetLabel ∉ submittedNormalLabels firstToken remainingTokens := by
  let evidence := exactNormalTrace_sourceTreeEvidence
    s pos targetLabel targetFormula targetFrame firstToken remainingTokens
    initial afterFirst final trace hfinish projection target formula hproject
    hprojection htargetFormula
  exact ⟨evidence.tree, evidence.labels_eq, evidence.erasure_eq,
    evidence.postfix_eq, evidence.exact_fold, evidence.final_formula,
    evidence.final_stack, evidence.post_db, evidence.target_fresh,
    evidence.no_self_reference⟩

/-! ## Positive and negative boundaries -/

/-- Positive: an accepted exact trace exposes an actual native `Proves`
derivation with the exact submitted label sequence. -/
example
    (s : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (targetFrame : RuntimeFrame)
    (firstToken : ByteSlice) (remainingTokens : List ByteSlice)
    (initial afterFirst final : RuntimeProofState)
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final)
    (hfinish : (s.finishProof final).db.error? = none)
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (formula : ConstantHeadedFormula)
    (hproject : projectPrefix? s.db = some projection)
    (hprojection : presentationOfProjection? projection = some target.1)
    (htargetFormula : targetFormula = formula.toRuntime) :
    ∃ tree : GeneratedProvesTree projection target formula,
      tree.labels = submittedNormalLabels firstToken remainingTokens ∧
        (tree.toDerivation hprojection).erase = tree.canonicalRawProof := by
  obtain ⟨tree, hlabels, _herasure, _hpostfix, _hfold, _hformula,
      _hstack, _hpost, _hfresh, _hnoSelf⟩ :=
    exactNormalTrace_reflects_sourceTree s pos targetLabel targetFormula
      targetFrame firstToken remainingTokens initial afterFirst final trace
      hfinish projection target formula hproject hprojection htargetFormula
  exact ⟨tree, hlabels, tree.erase_toDerivation hprojection⟩

/-- Negative: the reflected authored source labels cannot contain the theorem
label that `finishProof` inserts. -/
example
    (s : ParserState) (pos : Pos) (targetLabel : String)
    (targetFormula : RuntimeFormula) (targetFrame : RuntimeFrame)
    (firstToken : ByteSlice) (remainingTokens : List ByteSlice)
    (initial afterFirst final : RuntimeProofState)
    (trace : ExactNormalParserTrace s pos targetLabel targetFormula targetFrame
      firstToken remainingTokens initial afterFirst final)
    (hfinish : (s.finishProof final).db.error? = none)
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (formula : ConstantHeadedFormula)
    (hproject : projectPrefix? s.db = some projection)
    (hprojection : presentationOfProjection? projection = some target.1)
    (htargetFormula : targetFormula = formula.toRuntime) :
    ∃ tree : GeneratedProvesTree projection target formula,
      tree.labels = submittedNormalLabels firstToken remainingTokens ∧
      targetLabel ∉ tree.labels := by
  obtain ⟨tree, hlabels, _herasure, _hpostfix, _hfold, _hformula,
      _hstack, _hpost, _hfresh, hnoSelf⟩ :=
    exactNormalTrace_reflects_sourceTree s pos targetLabel targetFormula
      targetFrame firstToken remainingTokens initial afterFirst final trace
      hfinish projection target formula hproject hprojection htargetFormula
  exact ⟨tree, hlabels, by simpa [hlabels] using hnoSelf⟩

end Mettapedia.Languages.Metamath.InferenceNormalTraceReflection
