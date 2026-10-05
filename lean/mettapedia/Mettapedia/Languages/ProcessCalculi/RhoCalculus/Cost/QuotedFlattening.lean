import Mettapedia.GSLT.LanguageDef.Cost.QuotedFlattening
import Mettapedia.GSLT.LanguageDef.Cost.FlatteningObstruction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditarySupportedIterationObstruction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryCollapsingPlanStopRestoration

/-!
# Admitted nested Cost wrappers and their structural flattening obstruction

The witnesses live in the second generated language of rho's selected first
Cost object. They are closed, sorted and reflection-certified, and the actual
region compiler supplies their retained elaborations. No compact Cost2
canonical section is assumed.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.QuotedFlattening

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Framework.ConstructorCategory

noncomputable section

abbrev source : CIGSLT := rhoHereditaryCostLayer.compactOutput.toCIGSLT

def nestedUnitPattern : Pattern :=
  .apply costSignedConstructorName
    [.apply (costBaseConstructorName costSignedConstructorName)
      [.apply (costBaseConstructorName (costBaseConstructorName "PZero")) [],
       .apply (costBaseConstructorName costSignatureUnitConstructorName) []],
     .apply costSignatureUnitConstructorName []]

theorem nestedUnitPattern_typed :
    HasType source.costWholeLanguage FreeTypeContext.empty []
      nestedUnitPattern (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide +kernel)

def wrappedSort : LangSort source.costWholeLanguage :=
  ⟨costWrappedSortName, source.costWrappedSortName_mem_costWhole⟩

/-- The nested wrapper is a reflection-certified term, not an
untyped raw tree used only to obtain a contradiction. -/
def nestedUnitTerm :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage FreeTypeContext.empty [] wrappedSort := by
  refine ⟨nestedUnitPattern,
    ⟨⟨nestedUnitPattern_typed, rfl, rfl,
      nestedUnitPattern_typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [nestedUnitPattern, binderSafeAt, binderSafeListAt]

/-- The retained second-layer compiler accepts the same nested wrapper. -/
def nestedUnitElaboration :
    CostElabTerm source FreeTypeContext.empty [] wrappedSort :=
  CostOpenElaboration.compileTerm source nestedUnitTerm

@[simp] theorem nestedUnitElaboration_erases :
    CostOpenElaboration.erase nestedUnitElaboration = nestedUnitTerm :=
  CostOpenElaboration.erase_compileTerm source nestedUnitTerm

/-- Literal double-wrapper multiplication cannot be the structural action
of a continued morphism. This obstruction already holds on an admitted
closed Cost2 term and is independent of a second-layer canonical section. -/
theorem nestedUnit_no_structural_flattening
    (symbols : LanguageDefSymbolMap) (targetSignature : Pattern) :
    mapPattern symbols nestedUnitTerm.1 ≠
      .apply costSignedConstructorName
        [.apply (costBaseConstructorName "PZero") [], targetSignature] :=
  Mettapedia.GSLT.LanguageDef.Cost.QuotedFlattening.mapPattern_nestedWrapper_ne_singleWrapper
    _ _ _ _ _ _ _ _ _

/-- A temporal stack containing `count` actual unit-key cells. Its length is
independent of any interpretation of the unit signature as a debit. -/
def unitStack (count : Nat) : Pattern :=
  match count with
  | 0 => .apply costTokenStackEmptyConstructorName []
  | count + 1 => .apply costTokenStackConsConstructorName
      [.apply costSignatureUnitConstructorName [], unitStack count]

/-- Two accounts in the actual iterated grammar: the old funding apparatus
inside a new signed term, in contact with the new funding apparatus. -/
def nestedFundingPattern (outer inner : Nat) : Pattern :=
  .apply costContactConstructorName
    [.apply costSignedConstructorName
      [.apply (costBaseConstructorName costFundingConstructorName)
        [mapPattern costBaseLanguageDefSymbolMap (unitStack inner)],
       .apply costSignatureUnitConstructorName []],
     .apply costFundingConstructorName [unitStack outer]]

theorem nestedFunding_left_typed :
    HasType source.costWholeLanguage FreeTypeContext.empty []
      (nestedFundingPattern 1 2) (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide +kernel)

theorem nestedFunding_right_typed :
    HasType source.costWholeLanguage FreeTypeContext.empty []
      (nestedFundingPattern 2 1) (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide +kernel)

def nestedFundingLeftTerm :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage FreeTypeContext.empty [] wrappedSort := by
  refine ⟨nestedFundingPattern 1 2,
    ⟨⟨nestedFunding_left_typed, rfl, rfl,
      nestedFunding_left_typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [nestedFundingPattern, unitStack, mapPattern, mapPatternList,
    binderSafeAt, binderSafeListAt]

def nestedFundingRightTerm :
    ReflectiveWellSorted.OpenTerm source.costWholeReflectionProfile
      source.costWholeLanguage FreeTypeContext.empty [] wrappedSort := by
  refine ⟨nestedFundingPattern 2 1,
    ⟨⟨nestedFunding_right_typed, rfl, rfl,
      nestedFunding_right_typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [nestedFundingPattern, unitStack, mapPattern, mapPatternList,
    binderSafeAt, binderSafeListAt]

/-- Both accounts are nonempty on each side; exchanging their one/two-cell
boundary changes the admitted retained term. -/
theorem nestedFunding_terms_ne :
    nestedFundingLeftTerm ≠ nestedFundingRightTerm := by
  intro equality
  have patterns := congrArg Subtype.val equality
  simp [nestedFundingLeftTerm, nestedFundingRightTerm, nestedFundingPattern,
    unitStack, mapPattern, mapPatternList] at patterns

def nestedFundingLeft : CostElabTerm source FreeTypeContext.empty [] wrappedSort :=
  CostOpenElaboration.compileTerm source nestedFundingLeftTerm

def nestedFundingRight : CostElabTerm source FreeTypeContext.empty [] wrappedSort :=
  CostOpenElaboration.compileTerm source nestedFundingRightTerm

/-- The selected region compiler retains the exhibited account boundary. -/
theorem nestedFunding_elaborations_ne : nestedFundingLeft ≠ nestedFundingRight := by
  intro equality
  exact nestedFunding_terms_ne (congrArg CostOpenElaboration.erase equality)

/-- Count cells in a declared unit-key stack, rejecting every other shape.
The constructor names specify which Cost layer supplies the stack. -/
def readUnitStack (empty cons unit : String) : Pattern → Option Nat
  | .apply label [] => if label = empty then some 0 else none
  | .apply label [.apply head [], tail] =>
      if label = cons ∧ head = unit then (readUnitStack empty cons unit tail).map
        Nat.succ else none
  | _ => none

@[simp] theorem readUnitStack_unitStack (count : Nat) :
    readUnitStack costTokenStackEmptyConstructorName costTokenStackConsConstructorName
      costSignatureUnitConstructorName (unitStack count) = some count := by
  induction count with
  | zero => simp [unitStack, readUnitStack]
  | succ count inductionHypothesis => simp [unitStack, readUnitStack, inductionHypothesis]

@[simp] theorem readUnitStack_base_unitStack (count : Nat) :
    readUnitStack (costBaseConstructorName costTokenStackEmptyConstructorName)
      (costBaseConstructorName costTokenStackConsConstructorName)
      (costBaseConstructorName costSignatureUnitConstructorName)
      (mapPattern costBaseLanguageDefSymbolMap (unitStack count)) = some count := by
  induction count with
  | zero => simp [unitStack, readUnitStack, mapPattern, mapPatternList,
      costBaseLanguageDefSymbolMap]
  | succ count inductionHypothesis =>
    simpa [unitStack, readUnitStack, mapPattern, mapPatternList,
      costBaseLanguageDefSymbolMap] using congrArg (Option.map Nat.succ) inductionHypothesis

/-- Recover the two temporal accounts from the declared nested funding
fragment. This is a partial observation on all compact terms; it makes no
assertion that an arbitrary Cost2 term belongs to that fragment. -/
def readFundingAccounts : Pattern → Option (Nat × Nat)
  | .apply contact
      [.apply signed [.apply oldFunding [inner], .apply signature []],
       .apply funding [outer]] =>
    if contact = costContactConstructorName ∧ signed = costSignedConstructorName ∧
        oldFunding = costBaseConstructorName costFundingConstructorName ∧
        signature = costSignatureUnitConstructorName ∧ funding = costFundingConstructorName
    then do
      let outerCount ← readUnitStack costTokenStackEmptyConstructorName
        costTokenStackConsConstructorName costSignatureUnitConstructorName outer
      let innerCount ← readUnitStack
        (costBaseConstructorName costTokenStackEmptyConstructorName)
        (costBaseConstructorName costTokenStackConsConstructorName)
        (costBaseConstructorName costSignatureUnitConstructorName) inner
      pure (outerCount, innerCount)
    else none
  | _ => none

@[simp] theorem readFundingAccounts_nestedFundingPattern (outer inner : Nat) :
    readFundingAccounts (nestedFundingPattern outer inner) = some (outer, inner) := by
  simp [readFundingAccounts, nestedFundingPattern]

@[simp] theorem readFundingAccounts_left :
    readFundingAccounts nestedFundingLeftTerm.1 = some (1, 2) := by
  decide +kernel

@[simp] theorem readFundingAccounts_right :
    readFundingAccounts nestedFundingRightTerm.1 = some (2, 1) := by
  decide +kernel

/-- Concatenation on the unit-key fragment. Multiplicity is retained while
the boundary between the outer and inner chronological words is discarded. -/
def flattenFundingReadout
    (term : CostElabTerm source FreeTypeContext.empty [] wrappedSort) :
    Option Pattern :=
  (readFundingAccounts term.1.1).map fun accounts =>
    .apply costFundingConstructorName [unitStack (accounts.1 + accounts.2)]

/-- The proposed account merge identifies explicit, admitted, distinct
retained Cost2 terms, with both accounts nonempty on both sides. -/
theorem admitted_nonempty_boundary_collision :
    nestedFundingLeft ≠ nestedFundingRight ∧
      readFundingAccounts nestedFundingLeft.1.1 = some (1, 2) ∧
      readFundingAccounts nestedFundingRight.1.1 = some (2, 1) ∧
      flattenFundingReadout nestedFundingLeft =
        some (.apply costFundingConstructorName [unitStack 3]) ∧
      flattenFundingReadout nestedFundingRight =
        some (.apply costFundingConstructorName [unitStack 3]) := by
  refine ⟨nestedFunding_elaborations_ne, readFundingAccounts_left,
    readFundingAccounts_right, ?_, ?_⟩
  · change (readFundingAccounts nestedFundingLeftTerm.1).map _ = _
    rw [readFundingAccounts_left]
    rfl
  · change (readFundingAccounts nestedFundingRightTerm.1).map _ = _
    rw [readFundingAccounts_right]
    rfl

/-- Account concatenation cannot be a faithful map of this retained carrier.
This statement concerns elaborations; it does not identify them with compact
canonical keys of an as-yet unconstructed Cost2 continued object. -/
theorem flattenFundingReadout_not_injective :
    ¬ Function.Injective flattenFundingReadout := by
  intro injective
  exact nestedFunding_elaborations_ne (injective
    (admitted_nonempty_boundary_collision.2.2.2.1.trans
      admitted_nonempty_boundary_collision.2.2.2.2.symm))

/-- The common account readout itself belongs to the actual first-layer
grammar. A collision is therefore not obtained by returning invalid syntax. -/
theorem flattenedFunding_typed :
    HasType source.theory.presentation.presentation.language
      FreeTypeContext.empty []
      (.apply costFundingConstructorName [unitStack 3])
      (.base costWrappedSortName) := by
  exact checkHasType_sound (by decide +kernel)

/-- The common target is also admitted by the reflection profile used for
the existing first-layer canonical keys. -/
def flattenedFundingTerm : source.CanonicalCarrier := by
  refine ⟨.apply costFundingConstructorName [unitStack 3],
    ⟨⟨flattenedFunding_typed, rfl, rfl,
      flattenedFunding_typed.isWellScopedAt⟩, ?_⟩⟩
  intro declaration membership
  simp [unitStack, binderSafeAt, binderSafeListAt]

/-- An actual reachable canonical key for the flattened target. The source
objects of the collision remain retained Cost2 elaborations, and are not
silently promoted to compact Cost2 canonical keys. -/
def flattenedFundingKey : source.CanonicalKey :=
  ⟨source.canonical.normalize flattenedFundingTerm,
    source.canonical.normalize_idempotent flattenedFundingTerm⟩

theorem flattenedFundingKey_reachable :
    source.canonical.normalize flattenedFundingTerm = flattenedFundingKey.1 :=
  rfl

/-- The erased boundary is exactly the nonempty free-word boundary from the
algebraic control, now paired with the actual admitted terms above. All three
letters are unit-key token cells; none is an empty stack. -/
theorem admitted_boundary_has_word_control :
    nestedFundingLeft ≠ nestedFundingRight ∧
      (([()], [(), ()]) : List Unit × List Unit) ≠ ([(), ()], [()]) ∧
      ([()] : List Unit) ++ [(), ()] = [(), ()] ++ [()] ∧
      flattenFundingReadout nestedFundingLeft =
        flattenFundingReadout nestedFundingRight := by
  have words :=
    Mettapedia.GSLT.LanguageDef.Cost.FlatteningObstruction.list_append_forgets_nonempty_boundary
      () () ()
  exact ⟨nestedFunding_elaborations_ne, words.1, words.2,
    admitted_nonempty_boundary_collision.2.2.2.1.trans
      admitted_nonempty_boundary_collision.2.2.2.2.symm⟩

/-- Reject a signed body when a token stack is required. -/
theorem readUnitStack_rejects_nested_wrapper :
    readUnitStack costTokenStackEmptyConstructorName costTokenStackConsConstructorName
      costSignatureUnitConstructorName nestedUnitPattern = none := by
  decide +kernel

end

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.QuotedFlattening
