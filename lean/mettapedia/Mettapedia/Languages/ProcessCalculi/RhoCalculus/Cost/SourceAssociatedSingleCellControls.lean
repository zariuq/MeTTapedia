import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedSingleCell
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLocatedControls

/-!
# Copied and discarded signed code under one physical cell

The payload contains a genuine signed communication redex. One receiver
duplicates it and another ignores it. Both initial configurations use the
commitment computed from their own complete original source. They execute a
real firing, and every execution from either configuration has depth at most
one. Signed redex syntax therefore neither replenishes authority when copied
nor incurs an extra firing when discarded.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedSingleCellControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open ActivationGenerated ActivationLocatedControls SourceAssociatedLocatedExecution

/-- Two uses of the receiver's sole bound name. -/
def duplicateBodySource : Pattern := .collection .hashBag [boundBodySource, boundBodySource] none

def duplicateBody : CostTerm LiteralAuthority :=
  .par (.drop (.bvar 0)) (.par (.drop (.bvar 0)) .nil)

theorem duplicate_body_image : CodeImage 1 duplicateBodySource duplicateBody :=
  .collection (.cons (.drop (.bvar (by decide +kernel)))
    (.cons (.drop (.bvar (by decide +kernel))) .nil))

/-- The communicated code itself contains a sealed communication pair. -/
def redexSource : Pattern := .apply costSignedConstructorName
  [.collection .hashBag
    [.apply (costBaseConstructorName "PInput") [nilChannelSource, .lambda none zeroSource],
     .apply (costBaseConstructorName "POutput") [nilChannelSource, zeroSource]] none,
   unitSource]

def signedRedex : CostTerm LiteralAuthority :=
  .signed (.par (.recv nilChannelLocation .nil) (.send nilChannelLocation .nil)) {unitSource}

theorem redex_image : CodeImage 0 redexSource signedRedex :=
  .signed unitTyped unit_accepted
    (.pair (.recv .baseZeroQuote .zero) (.send .baseZeroQuote .zero))

/-- The same original seal is retained on both actual copies. -/
theorem duplicate_result : duplicateBody.commSubst signedRedex =
    .par signedRedex (.par signedRedex .nil) := by
  simp [duplicateBody, CostTerm.commSubst, CostTerm.substitute, CostTerm.lift_zero]

theorem discard_result : (CostTerm.nil : CostTerm LiteralAuthority).commSubst signedRedex = .nil := rfl

/-- Signed code, even when copied, contributes no physical purse cell. -/
theorem duplicate_result_has_no_purse :
    ((duplicateBody.commSubst signedRedex).components).physicalPurseCells = 0 := by
  rw [duplicate_result]
  simp [signedRedex, CostTerm.components, CostConfig.physicalPurseMeasure,
    CostTerm.physicalPurseMeasure]

theorem discarded_result_has_no_purse :
    (((CostTerm.nil : CostTerm LiteralAuthority).commSubst signedRedex).components).physicalPurseCells = 0 := by
  rw [discard_result]
  simp [CostTerm.components, CostConfig.physicalPurseMeasure]

/-- The two copies are still in the actual closed generated code domain. -/
theorem duplicated_code_image : CodeImage 0
    (.collection .hashBag [redexSource, redexSource] none)
    (duplicateBody.commSubst signedRedex) := by
  rw [duplicate_result]
  exact .collection (.cons redex_image (.cons redex_image .nil))

/-- The ordinary collector sees two separate redex occurrences, with equal seals. -/
theorem duplicated_code_has_two_redexes :
    (RawCostConfig.wholeRedexes (literalEncodeTerm (duplicateBody.commSubst signedRedex)).components).length = 2 := by
  rw [duplicate_result]
  simp [literalEncodeTerm, CostTerm.relabel, encodeCostTerm, CostProc.relabel, encodeCostProc,
    CostName.relabel, encodeCostName, signedRedex, nilChannelLocation, RawCostTerm.components,
    RawCostConfig.wholeRedexes, collectWholesAux, wholeAt?]

/-- Neither signed occurrence can fire without physical funding. -/
theorem duplicated_code_unfunded {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm
      (duplicateBody.commSubst signedRedex))) finalId finalComponents) : path.depth = 0 :=
  SourceAssociatedSingleCell.unfunded_code_path_depth_eq_zero duplicated_code_image path

/-- An actual parser-admitted receiver creates the two signed copies. -/
theorem duplicate_actual_firing :
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm
        (SourceAssociatedSingleCell.isolated channel duplicateBody signedRedex
          (authority channelSource duplicateBodySource redexSource))).normalizeConfig ∧
      ∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm
        (SourceAssociatedSingleCell.isolated channel duplicateBody signedRedex
          (authority channelSource duplicateBodySource redexSource)))) 1
        (applyTracedStep (initialTraceComponents (literalEncodeTerm
          (SourceAssociatedSingleCell.isolated channel duplicateBody signedRedex
            (authority channelSource duplicateBodySource redexSource)))) step 0),
        path.depth = 1 :=
  SourceAssociatedSingleCell.exists_one_firing channel_image duplicate_body_image redex_image

/-- Neither copy can increase the number of funded firings. -/
theorem duplicate_every_path_depth_le_one {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm
      (SourceAssociatedSingleCell.isolated channel duplicateBody signedRedex
        (authority channelSource duplicateBodySource redexSource)))) finalId finalComponents) :
    path.depth ≤ 1 :=
  SourceAssociatedSingleCell.every_path_depth_le_one channel_image duplicate_body_image redex_image path

/-- Ignoring a redex-bearing payload is also a real firing. -/
theorem discard_actual_firing :
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm
        (SourceAssociatedSingleCell.isolated channel .nil signedRedex
          (authority channelSource zeroSource redexSource))).normalizeConfig ∧
      ∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm
        (SourceAssociatedSingleCell.isolated channel .nil signedRedex
          (authority channelSource zeroSource redexSource)))) 1
        (applyTracedStep (initialTraceComponents (literalEncodeTerm
          (SourceAssociatedSingleCell.isolated channel .nil signedRedex
            (authority channelSource zeroSource redexSource)))) step 0),
        path.depth = 1 :=
  SourceAssociatedSingleCell.exists_one_firing channel_image CodeImage.zero redex_image

/-- The discarded latent interaction never adds another charged firing. -/
theorem discard_every_path_depth_le_one {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm
      (SourceAssociatedSingleCell.isolated channel .nil signedRedex
        (authority channelSource zeroSource redexSource)))) finalId finalComponents) :
    path.depth ≤ 1 :=
  SourceAssociatedSingleCell.every_path_depth_le_one channel_image CodeImage.zero redex_image path

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.SourceAssociatedSingleCellControls
