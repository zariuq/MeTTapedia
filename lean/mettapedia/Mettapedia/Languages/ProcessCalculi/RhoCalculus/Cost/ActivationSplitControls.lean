import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSplitCanonicalEntry
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationLocatedControls

/-!
# Discriminating split-funding controls

A bound-name receiver communicates a nonempty signed payload at a nonempty
quoted channel. Separate generated signatures fund one actual split firing
with two cells, retaining nonempty ordered tails. One product signature is
still one exact literal authority atom and cannot supply a two-atom split
demand from one cell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- One singleton-headed occurrence cannot exactly cover a two-atom demand,
even if its authority equals one or both demanded atoms. -/
theorem exactPurseCovers_two_atoms_single_cell (demand : RawCostSig)
    (two : demand.length = 2) (purse : RawIndexedPurse) (atomic : purse.head.length = 1) :
    exactPurseCovers demand [purse] = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro cover member
  have source := exactPurseCovers_sublist member
  have bound : cover.length ≤ 1 := by simpa using source.length_le
  have heads : cover.Forall (fun choice => choice.head.length = 1) := by
    rw [List.forall_iff_forall_mem]
    intro choice chosen
    have same : choice = purse := by simpa using source.subset chosen
    exact same ▸ atomic
  have spend := congrArg Multiset.card (exactPurseCovers_spend_sound member)
  rw [rawSelectedSpend_card_eq_length heads] at spend
  change cover.length = demand.length at spend
  omega

namespace ActivationGenerated

/-- The actual split catalogue remains empty with just one singleton funding
cell. This statement concerns exact authority, regardless of signature spelling. -/
theorem locatedSplit_one_cell_blocked (location : RawCostName) (body payload : RawCostTerm)
    (recvAuthority sendAuthority availableAuthority : String) (tail : RawCostStack) :
    runtimeCostCandidatesFromConfig
      [.signed (.recv location body) [recvAuthority], .signed (.send location payload) [sendAuthority],
       .purse location ([availableAuthority] :: tail)] = [] := by
  have noCover : ∀ index,
      exactPurseCovers (RawCostSig.normalize [recvAuthority, sendAuthority])
        [({ index := index, location := location, head := [availableAuthority], tail := tail } : RawIndexedPurse)] = [] := by
    intro index
    apply exactPurseCovers_two_atoms_single_cell
    · exact stableSortBy_length _ _
    · rfl
  simp [runtimeCostCandidatesFromConfig, RawCostConfig.purses, collectPursesAux,
    RawCostConfig.wholeRedexes, collectWholesAux,
    RawCostConfig.recvEndpoints, collectRecvsAux,
    RawCostConfig.sendEndpoints, collectSendsAux, splitCandidates,
    matchingPurses]
  simpa [RawCostSig.normalize, stableSortBy, stableInsertBy] using noCover 2

end ActivationGenerated

namespace ActivationSplitControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ActivationGenerated ActivationLocatedControls

def productTyped : TypedSignature productSource :=
  ⟨{productSource}, rfl, checkHasType_sound (by decide +kernel)⟩

theorem product_accepted : signature? productSource = some productTyped := by
  have typed : checkHasType rhoCIGSLT.costWholeLanguage FreeTypeContext.empty [] productSource
      (.base costSignatureSortName) = true := by decide +kernel
  unfold signature?
  rw [dif_pos typed]
  rfl

theorem product_authority_is_singleton : productTyped.val.card = 1 := by
  rw [productTyped.property.1, Multiset.card_singleton]

def recvTailSource : Pattern := .apply costTokenStackConsConstructorName [unitSource, emptySource]
def sendTailSource : Pattern := .apply costTokenStackConsConstructorName [productSource, emptySource]
def recvTail : CostStack LiteralAuthority := .cons {unitSource} .empty
def sendTail : CostStack LiteralAuthority := .cons {productSource} .empty

theorem recv_tail_image : StackImage recvTailSource recvTail := .cons unitTyped unit_accepted .empty
theorem send_tail_image : StackImage sendTailSource sendTail := .cons productTyped product_accepted .empty

def source : CostTerm LiteralAuthority :=
  decodedSplitReceiver channel (.drop (.bvar 0)) payload {unitSource} {productSource} recvTail sendTail

/-- A real split firing consumes two admitted cells and leaves the two
nonempty temporal tails, with exact unit/product syntax authority retained. -/
theorem actual_two_generated_purse_execution :
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm source).normalizeConfig ∧
      decodeCostSig step.spend = {literalAuthorityKey unitSource} + {literalAuthorityKey productSource} ∧
      step.selectedPurses.length = 2 ∧
      (∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm source)) 1
          (applyTracedStep (initialTraceComponents (literalEncodeTerm source)) step 0), path.depth = 1) ∧
      (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm source)) step 0).map
        RawTraceComponent.term)).ResourceSeparated ∧
      (decodeRawConfig (literalEncodeTerm source).normalizeConfig).physicalPurseCells =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm source)) step 0).map
          RawTraceComponent.term)).physicalPurseCells + 2 ∧
      (decodeRawConfig (literalEncodeTerm source).normalizeConfig).storedSignatures =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm source)) step 0).map
          RawTraceComponent.term)).storedSignatures +
          ({literalAuthorityKey unitSource} + {literalAuthorityKey productSource}) ∧
      (decodeRawConfig (literalEncodeTerm source).normalizeConfig).physicalPurseOccurrences =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm source)) step 0).map
          RawTraceComponent.term)).physicalPurseOccurrences :=
  channel_image.split_canonical_entry_resource_balance
    (CodeImage.drop (NameImage.bvar (index := 0) (by decide +kernel))) payload_image
    unitTyped unit_accepted productTyped product_accepted recv_tail_image send_tail_image

theorem actual_product_cell_does_not_split :
    runtimeCostCandidatesFromConfig
      [.signed (.recv (literalEncodeName channel) (.drop (.bvar 0))) [literalAuthorityKey unitSource],
       .signed (.send (literalEncodeName channel) (literalEncodeTerm payload)) [literalAuthorityKey unitSource],
       .purse (literalEncodeName channel) [[literalAuthorityKey productSource]]] = [] :=
  locatedSplit_one_cell_blocked _ _ _ _ _ _ []

end ActivationSplitControls
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
