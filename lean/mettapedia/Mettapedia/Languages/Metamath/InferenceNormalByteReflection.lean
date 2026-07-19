import Mettapedia.Languages.Metamath.InferenceNormalByteLedger
import Mettapedia.Languages.Metamath.InferenceNormalTraceReflection

/-!
# Native reflection from a normal token ledger

This module composes the proof-relevant normal token ledger with the generated
native `Proves` reflection theorem. The result retains the live trimming
equation in addition to exact source-label order, pre-insertion execution,
post-insertion database, freshness, and absence of self-reference.

This is the normal-proof lane. Compressed proof actions and whole-input event
completeness remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.InferenceNormalByteReflection

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceGeneratedProvesExecution
open Mettapedia.Languages.Metamath.InferenceNormalByteLedger
open Mettapedia.Languages.Metamath.InferenceNormalParserTrace
open Mettapedia.Languages.Metamath.InferenceNormalTraceReflection
open Metamath.Verify

/-- Retained Type-valued native evidence constructed from a normal token
ledger. The generated tree is usable data; the named proof fields authenticate
its exact source and runtime boundary. -/
structure NormalLedgerNativeReflection
    (ledger : NormalTokenLedger) (projection : PrefixProjection)
    (target : ValidatedPresentation)
    (formula : ConstantHeadedFormula) : Type where
  pre_projection : projectPrefix? ledger.anchor.db = some projection
  target_formula : ledger.targetFormula = formula.toRuntime
  finish_success :
    (ledger.anchor.finishProof ledger.final).db.error? = none
  trim_origin :
    ledger.anchor.db.trimFrame' ledger.targetFormula = .ok ledger.targetFrame
  tree : GeneratedProvesTree projection target formula
  labels_eq :
    tree.labels = submittedNormalLabels ledger.firstToken ledger.remainingTokens
  fold_eq :
    (submittedNormalLabels ledger.firstToken ledger.remainingTokens).foldlM
        (fun state label => ledger.anchor.db.stepNormal state label)
        {ledger.initial with ptp := .normal} = .ok ledger.final
  final_formula : ledger.final.fmla = formula.toRuntime
  final_stack : ledger.final.stack = #[formula.toRuntime]
  post_insert :
    (ledger.anchor.finishProof ledger.final).db =
      ledger.anchor.db.insert ledger.final.pos ledger.targetLabel
        (.assert formula.toRuntime ledger.targetFrame)
  target_fresh : ledger.anchor.db.find? ledger.targetLabel = none
  no_self :
    ledger.targetLabel ∉
      submittedNormalLabels ledger.firstToken ledger.remainingTokens

/-- The actual generic generated native derivation retained by a ledger
reflection. -/
def NormalLedgerNativeReflection.nativeEvidence
    {ledger : NormalTokenLedger} {projection : PrefixProjection}
    {target : ValidatedPresentation} {formula : ConstantHeadedFormula}
    (reflection : NormalLedgerNativeReflection ledger projection target formula)
    (hprojection : presentationOfProjection? projection = some target.1) :
    Derivation target (proves (encodeFormula formula)) :=
  reflection.tree.toDerivation hprojection

/-- Construct retained native evidence directly from a ledger. No parser trace
is accepted as an input; it is derived structurally from the ledger. -/
noncomputable def NormalTokenLedger.reflectNative
    (ledger : NormalTokenLedger)
    (hfinish : (ledger.anchor.finishProof ledger.final).db.error? = none)
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (formula : ConstantHeadedFormula)
    (hproject : projectPrefix? ledger.anchor.db = some projection)
    (hprojection : presentationOfProjection? projection = some target.1)
    (htargetFormula : ledger.targetFormula = formula.toRuntime) :
    NormalLedgerNativeReflection ledger projection target formula := by
  let source := exactNormalTrace_sourceTreeEvidence
    ledger.anchor ledger.pos ledger.targetLabel ledger.targetFormula
    ledger.targetFrame ledger.firstToken ledger.remainingTokens ledger.initial
    ledger.afterFirst ledger.final ledger.toExactNormalParserTrace hfinish
    projection target formula hproject hprojection htargetFormula
  exact
    { pre_projection := hproject
      target_formula := htargetFormula
      finish_success := hfinish
      trim_origin := ledger.trim_origin
      tree := source.tree
      labels_eq := source.labels_eq
      fold_eq := source.exact_fold
      final_formula := source.final_formula
      final_stack := source.final_stack
      post_insert := source.post_db
      target_fresh := source.target_fresh
      no_self := source.no_self_reference }

/-- A successfully finished normal token ledger constructs generated native
proof evidence over the exact pre-insertion projection. -/
theorem NormalTokenLedger.reflects_sourceTree
    (ledger : NormalTokenLedger)
    (hfinish : (ledger.anchor.finishProof ledger.final).db.error? = none)
    (projection : PrefixProjection) (target : ValidatedPresentation)
    (formula : ConstantHeadedFormula)
    (hproject : projectPrefix? ledger.anchor.db = some projection)
    (hprojection : presentationOfProjection? projection = some target.1)
    (htargetFormula : ledger.targetFormula = formula.toRuntime) :
    ledger.anchor.db.trimFrame' ledger.targetFormula = .ok ledger.targetFrame ∧
      ∃ tree : GeneratedProvesTree projection target formula,
        tree.labels = submittedNormalLabels ledger.firstToken
          ledger.remainingTokens ∧
        (tree.toDerivation hprojection).erase = tree.canonicalRawProof ∧
        rawProofLeadingPremisePostfixLabels
            (tree.toDerivation hprojection).erase =
          submittedNormalLabels ledger.firstToken ledger.remainingTokens ∧
        (submittedNormalLabels ledger.firstToken ledger.remainingTokens).foldlM
            (fun state label => ledger.anchor.db.stepNormal state label)
            {ledger.initial with ptp := .normal} = .ok ledger.final ∧
        ledger.final.fmla = formula.toRuntime ∧
        ledger.final.stack = #[formula.toRuntime] ∧
        (ledger.anchor.finishProof ledger.final).db =
          ledger.anchor.db.insert ledger.final.pos ledger.targetLabel
            (.assert formula.toRuntime ledger.targetFrame) ∧
        ledger.anchor.db.find? ledger.targetLabel = none ∧
        ledger.targetLabel ∉
          submittedNormalLabels ledger.firstToken ledger.remainingTokens := by
  let reflection :=
    Mettapedia.Languages.Metamath.InferenceNormalByteReflection.NormalTokenLedger.reflectNative
      ledger hfinish projection target formula hproject hprojection
      htargetFormula
  refine ⟨reflection.trim_origin, reflection.tree, reflection.labels_eq,
    reflection.tree.erase_toDerivation hprojection, ?_, reflection.fold_eq,
    reflection.final_formula, reflection.final_stack, reflection.post_insert,
    reflection.target_fresh, reflection.no_self⟩
  calc
    rawProofLeadingPremisePostfixLabels
        (reflection.tree.toDerivation hprojection).erase =
      reflection.tree.labels :=
        reflection.tree.erase_toDerivation_postfixLabels hprojection
    _ = submittedNormalLabels ledger.firstToken ledger.remainingTokens :=
      reflection.labels_eq

/-- Negative calibration: reflected native evidence cannot use the theorem
label inserted by its own successful `finishProof`. -/
theorem NormalTokenLedger.reflected_labels_exclude_target
    (ledger : NormalTokenLedger)
    (hfinish : (ledger.anchor.finishProof ledger.final).db.error? = none) :
    ledger.targetLabel ∉
      submittedNormalLabels ledger.firstToken ledger.remainingTokens := by
  obtain ⟨_fold, _label, _formula, _frame, _mode, _stack, _post, _fresh,
      noSelf⟩ :=
    ledger.toExactNormalParserTrace.accepted_prefix_boundary hfinish
  exact noSelf

/-- The named self-reference boundary of retained native evidence. -/
theorem NormalLedgerNativeReflection.labels_exclude_target
    {ledger : NormalTokenLedger} {projection : PrefixProjection}
    {target : ValidatedPresentation} {formula : ConstantHeadedFormula}
    (reflection : NormalLedgerNativeReflection ledger projection target formula) :
    ledger.targetLabel ∉
      submittedNormalLabels ledger.firstToken ledger.remainingTokens :=
  reflection.no_self

end Mettapedia.Languages.Metamath.InferenceNormalByteReflection
