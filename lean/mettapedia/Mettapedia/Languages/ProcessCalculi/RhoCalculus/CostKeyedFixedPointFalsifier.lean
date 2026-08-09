import Mathlib.Tactic
import Mettapedia.GSLT.LanguageDef.CostRestorationRelationQuoteArm
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalOrderAgnostic

/-!
# Compiled boundaries for the apex recursion

Two kernel-checked facts that pin the shape of the universal typed apex
recursion.

First, the cross-colour quote gap is real: the wrapped quote constructor is
a language-level quote of the generated rho Cost language while being
distinct from the base declaration's own quote constructor, so an aligned
pair headed by it satisfies neither the ordinary-head hypothesis of the
aligned arm nor the collapse shape of the Quote/Drop arms.  The new
language-quote arm covers exactly this configuration.

Second, the tempting fixed-point shortcut is false: keyed canonical output
with tied keys is not a fixed point of plain canonicalization.  Tied keys
preserve input order while plain canonicalization sorts by structural code,
so re-canonicalizing a keyed output can reorder it.  Any proof step that
treats hereditary keyed output as plain-canonical-fixed is therefore
unsound whenever semantically tied elements have distinct spellings — which
is precisely the configuration that motivated hereditary normalization.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostKeyedFixedPointFalsifier

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-! ## The cross-colour quote gap is a real typed configuration -/

/-- The wrapped quote constructor is a language-level quote of the generated
rho Cost language. -/
theorem rhoWrappedQuote_isLanguageQuote :
    ReflectiveContextSupport.isQuoteConstructor rhoCIGSLT.costWholeReflectionProfile
      (costWrappedConstructorName "NQuote") = true := by
  decide

/-- The wrapped quote constructor is not the base generated declaration's
own quote constructor, so the aligned inversion admits it while the
ordinary-head hypothesis of the aligned apex arm rejects it. -/
theorem rhoWrappedQuote_ne_baseDeclarationQuote :
    costWrappedConstructorName "NQuote" ≠
      (costStaticReflectivePresentationDecl rhoCIGSLT .base
        rhoReflectivePresentation).quoteConstructor := by
  decide

/-! ## The fixed-point shortcut is false -/

/-- Keyed canonical output with tied keys is not a fixed point of plain
canonicalization: the tied-key output preserves the input order of a
two-element bag, and plain canonicalization re-sorts it by structural
code. -/
theorem keyedTies_output_not_plain_canonical_fixed :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (fun _ _ => (0 : Nat))
          rhoReflectivePresentation.toReflectivePresentationDecl 0
          (.collection .hashBag [.fvar "b", .fvar "a"] none)) ≠
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (fun _ _ => (0 : Nat))
        rhoReflectivePresentation.toReflectivePresentationDecl 0
        (.collection .hashBag [.fvar "b", .fvar "a"] none) := by
  have ordered : Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
        (.fvar "a") ≤
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode (.fvar "b") := by
    decide
  have swapped :
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
          [Pattern.fvar "b", Pattern.fvar "a"] =
        [Pattern.fvar "a", Pattern.fvar "b"] := by
    calc
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
          [Pattern.fvar "b", Pattern.fvar "a"] =
          Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns
            [Pattern.fvar "a", Pattern.fvar "b"] :=
        Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns_eq_of_perm
          (List.Perm.swap (Pattern.fvar "a") (Pattern.fvar "b") [])
      _ = [Pattern.fvar "a", Pattern.fvar "b"] := by
        simpa using
          Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le
            Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode
            (.fvar "a") (.fvar "b") ordered
  have sortConst : ∀ x y : Pattern,
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
          (fun _ => (0 : Nat)) [x, y] = [x, y] := by
    intro x y
    exact Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le
      (fun _ => (0 : Nat)) x y (le_refl 0)
  have keyedSide :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
          (fun _ _ => (0 : Nat))
          rhoReflectivePresentation.toReflectivePresentationDecl 0
          (.collection .hashBag [.fvar "b", .fvar "a"] none) =
        .collection .hashBag [.fvar "b", .fvar "a"] none := by
    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
      rhoReflectivePresentation, sortConst]
  have plainSide :
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
          rhoReflectivePresentation.toReflectivePresentationDecl
          (.collection .hashBag [.fvar "b", .fvar "a"] none) =
        .collection .hashBag [.fvar "a", .fvar "b"] none := by
    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeList,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElements,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel,
      rhoReflectivePresentation, swapped]
  intro fixed
  rw [keyedSide, plainSide] at fixed
  simp at fixed

/-- Although tied semantic keys falsify exact fixed-point equality, the keyed
and plain representatives still agree in the precise quotient that forgets
only bare-parallel order.  This positive companion prevents the negative
canary from being misread as a failure of canonical semantic content. -/
theorem keyedTies_output_parallelOrderAgnostic_plain :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.ParallelOrderAgnostic
      rhoReflectivePresentation.toReflectivePresentationDecl
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (fun _ _ => (0 : Nat))
        rhoReflectivePresentation.toReflectivePresentationDecl 0
        (.collection .hashBag [.fvar "b", .fvar "a"] none))
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        (.collection .hashBag [.fvar "b", .fvar "a"] none)) :=
  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt_parallelOrderAgnostic
    (fun _ _ => (0 : Nat))
    rhoReflectivePresentation.toReflectivePresentationDecl 0 _

/-! ## Endpoint key depths cannot be chosen independently at a parallel root -/

/-- One atom whose restored de Bruijn index changes with the visible depth. -/
def rhoDepthApexShiftingKey : CostStaticAtomKey where
  sourceType := .base "T"
  sourceSupport := []
  targetType := .base "T"
  targetSupport := []
  normal := .bvar 0

/-- The depth-sensitive raw key cannot occur in the proof-relevant Cost atom
carrier.  Its recorded target support is empty, while its normalized value is
the free de Bruijn index zero; any genuine typing derivation at that support
would therefore contradict ordinary local scope.

This theorem is the reachability boundary of the raw cospan counterexample
below: the counterexample refutes an unrestricted theorem about proof-free
keys, but it does not refute the typed rho apex required by the executor. -/
theorem rhoDepthApexShiftingKey_not_typed
    (color : CostStaticColor) (targetFree : WellSorted.FreeTypeContext)
    (atom : TypedCostStaticAtom rhoCIGSLT color targetFree) :
    atom.key ≠ rhoDepthApexShiftingKey := by
  intro keyEquality
  have wellScoped : atom.key.normal.isWellScopedAt
      atom.key.targetSupport.length = true :=
    WellSorted.HasType.isWellScopedAt atom.normalTyped
  rw [keyEquality] at wellScoped
  simp [rhoDepthApexShiftingKey, Pattern.isWellScopedAt] at wellScoped

/-- Empty target context used by the typed depth-sensitivity witness. -/
def rhoDepthSensitiveTargetFree : WellSorted.FreeTypeContext := fun _ => none

/-- A genuine typed semantic atom may retain a bound variable when its target
support retains that binder.  Thus typing alone does not make arbitrary atom
values independent of the visible restoration depth. -/
def rhoTypedDepthSensitiveAtom (color : CostStaticColor) :
    TypedCostStaticAtom rhoCIGSLT color rhoDepthSensitiveTargetFree where
  key :=
    { sourceType := .base (costBaseSortName "Name")
      sourceSupport := [.base (costBaseSortName "Name")]
      targetType := .base (costBaseSortName "Name")
      targetSupport := [.base (costBaseSortName "Name")]
      normal := .bvar 0 }
  normalWellSorted := by
    refine ⟨⟨.bvar (by simp), ?_, ?_, ?_⟩, ?_⟩
    · simp [Pattern.hasCanonicalBinderMetadata]
    · simp [WellSorted.isObjectPattern]
    · rfl
    · intro presentation membership
      simp [Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt]

/-- The typed witness is genuinely depth-sensitive: inserting it one binder
above its retained support preserves index zero, while inserting it three
binders above that support shifts the index to two.  Therefore the reachable
apex proof must use occurrence support and synchronized visible depths, not
merely the existence of typed atoms. -/
theorem rhoTypedDepthSensitiveAtom_lift_differs
    (color : CostStaticColor) :
    Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
        (1 - (rhoTypedDepthSensitiveAtom color).key.targetSupport.length)
        (rhoTypedDepthSensitiveAtom color).key.normal ≠
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
        (3 - (rhoTypedDepthSensitiveAtom color).key.targetSupport.length)
        (rhoTypedDepthSensitiveAtom color).key.normal := by
  cases color <;>
    simp [rhoTypedDepthSensitiveAtom,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

/-- One atom whose restored value is independent of the visible depth. -/
def rhoDepthApexStableKey : CostStaticAtomKey where
  sourceType := .base "T"
  sourceSupport := []
  targetType := .base "T"
  targetSupport := []
  normal := .fvar ""

/-- The two semantic keys used by the depth counterexample. -/
def rhoDepthApexEndpointKey (slot : Fin 2) : CostStaticAtomKey :=
  if slot.1 = 0 then rhoDepthApexShiftingKey else rhoDepthApexStableKey

/-- A direct two-slot cospan.  Its identity legs make the counterexample
independent of the executable deduplication algorithm used by `ofFunctions`. -/
def rhoDepthApexCospan : CostStaticAtomKeyCospan
    rhoDepthApexEndpointKey rhoDepthApexEndpointKey where
  commonKeys := [rhoDepthApexShiftingKey, rhoDepthApexStableKey]
  commonNodup := by
    simp [rhoDepthApexShiftingKey, rhoDepthApexStableKey]
  leftSlot := fun slot => slot
  rightSlot := fun slot => slot
  leftCommutes := by
    intro slot
    fin_cases slot <;> rfl
  rightCommutes := by
    intro slot
    fin_cases slot <;> rfl
  leftExtensional := by
    intro first second
    constructor
    · intro equality
      exact congrArg rhoDepthApexEndpointKey equality
    · intro equality
      fin_cases first <;> fin_cases second <;>
        simp [rhoDepthApexEndpointKey, rhoDepthApexShiftingKey,
          rhoDepthApexStableKey] at equality ⊢
  rightExtensional := by
    intro first second
    constructor
    · intro equality
      exact congrArg rhoDepthApexEndpointKey equality
    · intro equality
      fin_cases first <;> fin_cases second <;>
        simp [rhoDepthApexEndpointKey, rhoDepthApexShiftingKey,
          rhoDepthApexStableKey] at equality ⊢
  crossExtensional := by
    intro left right
    constructor
    · intro equality
      exact congrArg rhoDepthApexEndpointKey equality
    · intro equality
      fin_cases left <;> fin_cases right <;>
        simp [rhoDepthApexEndpointKey, rhoDepthApexShiftingKey,
          rhoDepthApexStableKey] at equality ⊢

/-- Common spelling of the depth-sensitive atom. -/
def rhoDepthApexFirstAtom : Pattern :=
  .fvar (rhoDepthApexCospan.commonAtomName
    (rhoDepthApexCospan.leftSlot 0))

/-- Common spelling of the depth-stable atom. -/
def rhoDepthApexSecondAtom : Pattern :=
  .fvar (rhoDepthApexCospan.commonAtomName
    (rhoDepthApexCospan.leftSlot 1))

/-- The common raw parallel frame used at both endpoints. -/
def rhoDepthApexRaw : Pattern :=
  .collection .hashBag [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] none

/-- Canonicalize the common frame at a chosen semantic-key depth. -/
def rhoDepthApexKeyed (depth : Nat) : Pattern :=
  Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
    (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
    rhoReflectivePresentation.toReflectivePresentationDecl depth
    rhoDepthApexRaw

/-- Restore one keyed representative at a common comparison depth. -/
def rhoDepthApexRestored (keyDepth restoreDepth : Nat) : Pattern :=
  ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
    rhoDepthApexCospan.commonSupport rhoDepthApexCospan.commonAssignment
    restoreDepth (rhoDepthApexKeyed keyDepth)

@[simp] theorem rhoDepthApex_commonSupport_first :
    rhoDepthApexCospan.commonSupport
      (rhoDepthApexCospan.commonAtomName
        (rhoDepthApexCospan.leftSlot 0)) = [] := by
  rw [rhoDepthApexCospan.commonSupport_commonAtomName,
    rhoDepthApexCospan.leftCommutes]
  rfl

@[simp] theorem rhoDepthApex_commonSupport_second :
    rhoDepthApexCospan.commonSupport
      (rhoDepthApexCospan.commonAtomName
        (rhoDepthApexCospan.leftSlot 1)) = [] := by
  rw [rhoDepthApexCospan.commonSupport_commonAtomName,
    rhoDepthApexCospan.leftCommutes]
  rfl

@[simp] theorem rhoDepthApex_commonAssignment_first :
    rhoDepthApexCospan.commonAssignment
      (rhoDepthApexCospan.commonAtomName
        (rhoDepthApexCospan.leftSlot 0)) = .bvar 0 := by
  rw [rhoDepthApexCospan.commonAssignment_commonAtomName,
    rhoDepthApexCospan.leftCommutes]
  rfl

@[simp] theorem rhoDepthApex_commonAssignment_second :
    rhoDepthApexCospan.commonAssignment
      (rhoDepthApexCospan.commonAtomName
        (rhoDepthApexCospan.leftSlot 1)) = .fvar "" := by
  rw [rhoDepthApexCospan.commonAssignment_commonAtomName,
    rhoDepthApexCospan.leftCommutes]
  rfl

theorem rhoDepthApex_restore_first_zero :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
      rhoDepthApexCospan.commonSupport rhoDepthApexCospan.commonAssignment 0
      rhoDepthApexFirstAtom = .bvar 0 := by
  simp only [rhoDepthApexFirstAtom, ReflectiveContextSupport.substituteAt]
  rw [rhoDepthApex_commonSupport_first,
    rhoDepthApex_commonAssignment_first]
  simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem rhoDepthApex_restore_first_two :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
      rhoDepthApexCospan.commonSupport rhoDepthApexCospan.commonAssignment 2
      rhoDepthApexFirstAtom = .bvar 2 := by
  simp only [rhoDepthApexFirstAtom, ReflectiveContextSupport.substituteAt]
  rw [rhoDepthApex_commonSupport_first,
    rhoDepthApex_commonAssignment_first]
  simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem rhoDepthApex_restore_second (depth : Nat) :
    ReflectiveContextSupport.substituteAt rhoCIGSLT.costWholeReflectionProfile
      rhoDepthApexCospan.commonSupport rhoDepthApexCospan.commonAssignment depth
      rhoDepthApexSecondAtom = .fvar "" := by
  simp only [rhoDepthApexSecondAtom, ReflectiveContextSupport.substituteAt]
  rw [rhoDepthApex_commonSupport_second,
    rhoDepthApex_commonAssignment_second]
  simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]

theorem rhoDepthApex_key_zero_first :
    rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0
      rhoDepthApexFirstAtom = 0 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    rhoDepthApex_restore_first_zero,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode, Nat.pair]

theorem rhoDepthApex_key_zero_second :
    rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0
      rhoDepthApexSecondAtom = 2 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    rhoDepthApex_restore_second,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.stringCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.charListCode, Nat.pair]

theorem rhoDepthApex_key_two_first :
    rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 2
      rhoDepthApexFirstAtom = 4 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    rhoDepthApex_restore_first_two,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode, Nat.pair]

theorem rhoDepthApex_key_two_second :
    rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 2
      rhoDepthApexSecondAtom = 2 := by
  simp [CostStaticAtomKeyCospan.commonSemanticPatternKeyAt,
    rhoDepthApex_restore_second,
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.stringCode,
    Mettapedia.OSLF.MeTTaIL.PatternCode.charListCode, Nat.pair]

theorem rhoDepthApex_sorted_zero :
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
        [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] =
      [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] := by
  apply Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy_pair_eq_of_le
  simp [rhoDepthApex_key_zero_first, rhoDepthApex_key_zero_second]

theorem rhoDepthApex_sorted_two :
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 2)
        [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] =
      [rhoDepthApexSecondAtom, rhoDepthApexFirstAtom] := by
  simp [Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatternsBy, List.mergeSort,
    rhoDepthApex_key_two_first, rhoDepthApex_key_two_second]

@[simp] theorem rhoDepthApex_canonicalize_first (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        rhoReflectivePresentation.toReflectivePresentationDecl depth
        rhoDepthApexFirstAtom = rhoDepthApexFirstAtom := by
  simp [rhoDepthApexFirstAtom,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt]

@[simp] theorem rhoDepthApex_canonicalize_second (depth : Nat) :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        rhoReflectivePresentation.toReflectivePresentationDecl depth
        rhoDepthApexSecondAtom = rhoDepthApexSecondAtom := by
  simp [rhoDepthApexSecondAtom,
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt]

theorem rhoDepthApex_keyed_zero_eq :
    rhoDepthApexKeyed 0 = .collection .hashBag
      [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] none := by
  unfold rhoDepthApexKeyed rhoDepthApexRaw
  change Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
      rhoReflectivePresentation.toReflectivePresentationDecl
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
        rhoReflectivePresentation.toReflectivePresentationDecl
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
          rhoReflectivePresentation.toReflectivePresentationDecl 0
          [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom])) = _
  rw [show Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
      (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
      rhoReflectivePresentation.toReflectivePresentationDecl 0
      [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] =
        [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] by
    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt]]
  rw [show Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
      (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 0)
      rhoReflectivePresentation.toReflectivePresentationDecl
      [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] =
        [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] by
    simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
      rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] using
        rhoDepthApex_sorted_zero]
  rfl

theorem rhoDepthApex_keyed_two_eq :
    rhoDepthApexKeyed 2 = .collection .hashBag
      [rhoDepthApexSecondAtom, rhoDepthApexFirstAtom] none := by
  unfold rhoDepthApexKeyed rhoDepthApexRaw
  change Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.collapseParallel
      rhoReflectivePresentation.toReflectivePresentationDecl
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 2)
        rhoReflectivePresentation.toReflectivePresentationDecl
        (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
          (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
          rhoReflectivePresentation.toReflectivePresentationDecl 2
          [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom])) = _
  rw [show Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt
      (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
      rhoReflectivePresentation.toReflectivePresentationDecl 2
      [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] =
        [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] by
    simp [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeListByAt]]
  rw [show Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy
      (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT 2)
      rhoReflectivePresentation.toReflectivePresentationDecl
      [rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] =
        [rhoDepthApexSecondAtom, rhoDepthApexFirstAtom] by
    simpa [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.normalizeParallelElementsBy,
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.parallelSplice,
      rhoDepthApexFirstAtom, rhoDepthApexSecondAtom] using
        rhoDepthApex_sorted_two]
  rfl

theorem rhoDepthApex_restored_zero_eq :
    rhoDepthApexRestored 0 0 =
      .collection .hashBag [.bvar 0, .fvar ""] none := by
  rw [rhoDepthApexRestored, rhoDepthApex_keyed_zero_eq]
  simp [ReflectiveContextSupport.substituteAt,
    rhoDepthApex_restore_first_zero, rhoDepthApex_restore_second]

theorem rhoDepthApex_restored_two_eq :
    rhoDepthApexRestored 2 0 =
      .collection .hashBag [.fvar "", .bvar 0] none := by
  rw [rhoDepthApexRestored, rhoDepthApex_keyed_two_eq]
  simp [ReflectiveContextSupport.substituteAt,
    rhoDepthApex_restore_first_zero, rhoDepthApex_restore_second]

/-- Positive control: a representative compared at one key depth admits the
reflexive common-restoration apex. -/
theorem rhoDepthApex_sameKeyDepth :
    CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
      rhoDepthApexCospan rhoReflectivePresentation.toReflectivePresentationDecl
      0 (rhoDepthApexKeyed 0) (rhoDepthApexKeyed 0) :=
  CostStaticAtomKeyCospan.CommonRestorationApex.refl rhoDepthApexCospan
    rhoReflectivePresentation.toReflectivePresentationDecl 0 _

/-- The unrestricted apex helper with independently chosen endpoint key
depths is false.  A parallel root must canonicalize both endpoints at its one
common visible depth; quote resets belong inside the recursive cases. -/
theorem rhoDepthApex_unequalKeyDepths_no_commonApex :
    ¬ CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
      rhoDepthApexCospan rhoReflectivePresentation.toReflectivePresentationDecl
      0 (rhoDepthApexKeyed 0) (rhoDepthApexKeyed 2) := by
  intro apex
  have restored := apex.restored_eq
  change rhoDepthApexRestored 0 0 = rhoDepthApexRestored 2 0 at restored
  rw [rhoDepthApex_restored_zero_eq, rhoDepthApex_restored_two_eq] at restored
  simp at restored

/-! ## Plain canonical equality at one root depth is still insufficient -/

/-- Embed the depth-sensitive raw frame beneath the authored Quote/Drop
shell.  Plain canonicalization removes this shell, whereas keyed
canonicalization resets the payload to visible depth zero. -/
def rhoDepthApexQuoteDrop : Pattern :=
  .apply rhoReflectivePresentation.quoteConstructor
    [.apply rhoReflectivePresentation.dropConstructor [rhoDepthApexRaw]]

/-- The embedded Quote/Drop redex and its payload have the same ordinary
reflective canonical form. -/
theorem rhoDepthApexQuoteDrop_canonical_eq :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        rhoDepthApexQuoteDrop =
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation.toReflectivePresentationDecl
        rhoDepthApexRaw := by
  unfold rhoDepthApexQuoteDrop
  exact Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize_quote_drop
    rhoReflectivePresentation.toReflectivePresentationDecl (by decide)
    rhoDepthApexRaw

/-- At ambient depth two the Quote/Drop endpoint still selects the payload's
depth-zero keyed representative. -/
theorem rhoDepthApexQuoteDrop_keyed_two_eq :
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        rhoReflectivePresentation.toReflectivePresentationDecl 2
        rhoDepthApexQuoteDrop = rhoDepthApexKeyed 0 := by
  unfold rhoDepthApexQuoteDrop rhoDepthApexKeyed
  exact Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt_quote_drop
    (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
    rhoReflectivePresentation.toReflectivePresentationDecl (by decide) 2
    rhoDepthApexRaw

/-- Even equal ambient root depths plus ordinary canonical equality do not
construct a common apex for arbitrary proof-free keys.  Quote/Drop resets the
left payload's semantic-key depth to zero while the unquoted right payload
remains at depth two, reproducing the unequal-depth obstruction above.

The reachable rho theorem must therefore consume the typed reflective-support
certificates carried by its actual static frames; a syntax-only helper would
be false. -/
theorem rhoDepthApex_canonical_eq_sameRootDepth_no_commonApex :
    ¬ CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
      rhoDepthApexCospan rhoReflectivePresentation.toReflectivePresentationDecl
      0
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        rhoReflectivePresentation.toReflectivePresentationDecl 2
        rhoDepthApexQuoteDrop)
      (Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalizeByAt
        (rhoDepthApexCospan.commonSemanticPatternKeyAt rhoCIGSLT)
        rhoReflectivePresentation.toReflectivePresentationDecl 2
        rhoDepthApexRaw) := by
  rw [rhoDepthApexQuoteDrop_keyed_two_eq]
  change ¬ CostStaticAtomKeyCospan.CommonRestorationApex rhoCIGSLT
    rhoDepthApexCospan rhoReflectivePresentation.toReflectivePresentationDecl
    0 (rhoDepthApexKeyed 0) (rhoDepthApexKeyed 2)
  exact rhoDepthApex_unequalKeyDepths_no_commonApex

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostKeyedFixedPointFalsifier
