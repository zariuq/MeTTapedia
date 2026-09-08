import Mettapedia.GSLT.Parsing.PlainBnfSourceScalarCodec
import Mettapedia.GSLT.Parsing.PlainBnfLexicalInhabitation

/-!
# A partial observation for the authored exclusion scan

This predicate constrains exclusion queries on canonical natural-number
scalar lists, and the integer/disequality premises needed by that scan.
It uses the independently defined `gapAfter` and `exceptGapCheck`; it does
not contain source rules, evaluate Horn programs, or invoke proof replay.
Every observed query constrains its entire output term, including outputs
which do not already have Boolean-result shape.

Other relations, other root lexical constructors, malformed scalar lists,
negative scan indices, and alias-bearing disequality operands are outside
this observation. On those inputs the predicate imposes no constraint.
That is not grammar admission or evidence of successful execution. The
actual source program must separately preserve this predicate for all its
applicable clause/provider steps before it licenses no-invention.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfExclusionLocalModel

open HornCertificate HornIntegerProvider
open PlainBnfSourceScalarCodec (encodeScalars decodeScalars)
open PlainBnfLexicalInhabitation (gapAfter exceptGapCheck)

def resultTerm (result : Bool) : GroundTerm :=
  .atom (if result then "BNFYesV1" else "BNFNoV1")

def exclusionGoal (excluded : List Nat) (output : GroundTerm) : GroundAtom :=
  ⟨"BNFLexicalMatcherInhabitedV1",
    .cons (.app "bnf-v1:lexical-except" (.cons (encodeScalars excluded) .nil))
      (.cons output .nil)⟩

def tailGoal (previous : Nat) (excluded : List Nat) (output : GroundTerm) : GroundAtom :=
  ⟨"BNFExclusionTailInhabitedV1", .cons (.integer previous)
    (.cons (encodeScalars excluded) (.cons output .nil))⟩

def gapGoal (previous next : Nat) (excluded : List Nat) (output : GroundTerm) : GroundAtom :=
  ⟨"BNFExclusionGapInhabitedV1", .cons (.integer previous) (.cons (.integer next)
    (.cons (encodeScalars excluded) (.cons output .nil)))⟩

def differentGoal (left right : GroundTerm) : GroundAtom :=
  ⟨"different", .cons left (.cons right .nil)⟩

def integerGoal (relation : String) (left right : Int) : GroundAtom :=
  ⟨relation, .cons (.integer left) (.cons (.integer right) .nil)⟩

/-- A partial observation, not an input validator or an execution relation. -/
def Meaning : GroundAtom → Prop
  | ⟨"BNFLexicalMatcherInhabitedV1",
      .cons (.app "bnf-v1:lexical-except" (.cons source .nil)) (.cons output .nil)⟩ =>
      match decodeScalars source with
      | some excluded => output = resultTerm (exceptGapCheck excluded)
      | none => True
  | ⟨"BNFExclusionTailInhabitedV1",
      .cons (.integer previous) (.cons source (.cons output .nil))⟩ =>
      if 0 ≤ previous then
        match decodeScalars source with
        | some excluded => output = resultTerm (gapAfter previous.toNat excluded)
        | none => True
      else True
  | ⟨"BNFExclusionGapInhabitedV1",
      .cons (.integer previous) (.cons (.integer next) (.cons source (.cons output .nil)))⟩ =>
      if 0 ≤ previous ∧ 0 ≤ next then
        match decodeScalars source with
        | some excluded => output = resultTerm (gapAfter previous.toNat (next.toNat :: excluded))
        | none => True
      else True
  | ⟨"different", .cons left (.cons right .nil)⟩ =>
      AliasFree left → AliasFree right → left ≠ right
  | ⟨"ground-integer-less", .cons (.integer left) (.cons (.integer right) .nil)⟩ =>
      left < right
  | ⟨"ground-integer-not-less", .cons (.integer left) (.cons (.integer right) .nil)⟩ =>
      right ≤ left
  | ⟨"ground-integer-gap", .cons (.integer left) (.cons (.integer right) .nil)⟩ =>
      left + 1 < right
  | ⟨"ground-integer-no-gap", .cons (.integer left) (.cons (.integer right) .nil)⟩ =>
      right ≤ left + 1
  | _ => True

theorem Meaning_of_other (goal : GroundAtom)
    (notRoot : goal.relation ≠ "BNFLexicalMatcherInhabitedV1")
    (notTail : goal.relation ≠ "BNFExclusionTailInhabitedV1")
    (notGap : goal.relation ≠ "BNFExclusionGapInhabitedV1")
    (notDifferent : goal.relation ≠ "different")
    (notLess : goal.relation ≠ "ground-integer-less")
    (notNotLess : goal.relation ≠ "ground-integer-not-less")
    (notIntegerGap : goal.relation ≠ "ground-integer-gap")
    (notNoGap : goal.relation ≠ "ground-integer-no-gap") : Meaning goal := by
  unfold Meaning
  split <;> simp_all

theorem resultTerm_injective : Function.Injective resultTerm := by
  intro left right same
  cases left <;> cases right <;> simp_all [resultTerm]

@[simp] theorem resultTerm_eq_iff (left right : Bool) :
    resultTerm left = resultTerm right ↔ left = right :=
  ⟨fun same => resultTerm_injective same, congrArg resultTerm⟩

@[simp] theorem meaning_exclusion_iff (excluded : List Nat) (output : GroundTerm) :
    Meaning (exclusionGoal excluded output) ↔ output = resultTerm (exceptGapCheck excluded) := by
  simp [Meaning, exclusionGoal]

@[simp] theorem meaning_tail_iff (previous : Nat) (excluded : List Nat) (output : GroundTerm) :
    Meaning (tailGoal previous excluded output) ↔ output = resultTerm (gapAfter previous excluded) := by
  simp [Meaning, tailGoal]

@[simp] theorem meaning_gap_iff (previous next : Nat) (excluded : List Nat) (output : GroundTerm) :
    Meaning (gapGoal previous next excluded output) ↔
      output = resultTerm (gapAfter previous (next :: excluded)) := by
  simp [Meaning, gapGoal]

@[simp] theorem meaning_exclusion_result_iff (excluded : List Nat) (result : Bool) :
    Meaning (exclusionGoal excluded (resultTerm result)) ↔ result = exceptGapCheck excluded := by
  simp

@[simp] theorem meaning_tail_result_iff (previous : Nat) (excluded : List Nat) (result : Bool) :
    Meaning (tailGoal previous excluded (resultTerm result)) ↔ result = gapAfter previous excluded := by
  simp

@[simp] theorem meaning_gap_result_iff (previous next : Nat) (excluded : List Nat) (result : Bool) :
    Meaning (gapGoal previous next excluded (resultTerm result)) ↔
      result = gapAfter previous (next :: excluded) := by
  simp

theorem meaning_different_iff {left right : GroundTerm}
    (leftCanonical : AliasFree left) (rightCanonical : AliasFree right) :
    Meaning (differentGoal left right) ↔ left ≠ right := by
  simp [Meaning, differentGoal, leftCanonical, rightCanonical]

@[simp] theorem meaning_less_iff (left right : Int) :
    Meaning (integerGoal "ground-integer-less" left right) ↔ left < right := Iff.rfl

@[simp] theorem meaning_notLess_iff (left right : Int) :
    Meaning (integerGoal "ground-integer-not-less" left right) ↔ right ≤ left := Iff.rfl

@[simp] theorem meaning_gap_integer_iff (left right : Int) :
    Meaning (integerGoal "ground-integer-gap" left right) ↔ left + 1 < right := Iff.rfl

@[simp] theorem meaning_noGap_iff (left right : Int) :
    Meaning (integerGoal "ground-integer-no-gap" left right) ↔ right ≤ left + 1 := Iff.rfl

/-! ## The independent scan's local equations -/

theorem gapAfter_surrogate (excluded : List Nat) :
    gapAfter 55295 (57344 :: excluded) = gapAfter 57344 excluded := by
  simp [gapAfter]

theorem gapAfter_noGap (previous next : Nat) (excluded : List Nat)
    (notHole : ¬ (previous = 55295 ∧ next = 57344))
    (noGap : next ≤ previous + 1) :
    gapAfter previous (next :: excluded) = gapAfter next excluded := by
  simp [gapAfter, notHole, show ¬ previous + 1 < next by omega]

theorem gapAfter_gap (previous next : Nat) (excluded : List Nat)
    (notHole : ¬ (previous = 55295 ∧ next = 57344))
    (gap : previous + 1 < next) :
    gapAfter previous (next :: excluded) = true := by
  simp [gapAfter, notHole, gap]

theorem meaning_surrogate_iff (excluded : List Nat) (output : GroundTerm) :
    Meaning (gapGoal 55295 57344 excluded output) ↔ Meaning (tailGoal 57344 excluded output) := by
  simp [gapAfter_surrogate]

theorem meaning_noGap_tail_iff (previous next : Nat) (excluded : List Nat) (output : GroundTerm)
    (notHole : ¬ (previous = 55295 ∧ next = 57344))
    (noGap : next ≤ previous + 1) :
    Meaning (gapGoal previous next excluded output) ↔ Meaning (tailGoal next excluded output) := by
  simp [gapAfter_noGap previous next excluded notHole noGap]

theorem meaning_real_gap_iff (previous next : Nat) (excluded : List Nat) (output : GroundTerm)
    (notHole : ¬ (previous = 55295 ∧ next = 57344))
    (gap : previous + 1 < next) :
    Meaning (gapGoal previous next excluded output) ↔ output = resultTerm true := by
  simp [gapAfter_gap previous next excluded notHole gap]

/-! ## Local implications on arbitrary ground terms

These are equations of the partial observation. They do not declare rules
or claim that any program contains the corresponding clauses.
-/

def scalarCons (first rest : GroundTerm) : GroundTerm :=
  .app "bnf-v1:scalars-cons" (.cons first (.cons rest .nil))

def scalarPair (first second : GroundTerm) : GroundTerm :=
  .app "BNFScalarPairV1" (.cons first (.cons second .nil))

def rawExclusionGoal (source output : GroundTerm) : GroundAtom :=
  ⟨"BNFLexicalMatcherInhabitedV1",
    .cons (.app "bnf-v1:lexical-except" (.cons source .nil)) (.cons output .nil)⟩

def rawTailGoal (previous source output : GroundTerm) : GroundAtom :=
  ⟨"BNFExclusionTailInhabitedV1", .cons previous (.cons source (.cons output .nil))⟩

def rawGapGoal (previous next source output : GroundTerm) : GroundAtom :=
  ⟨"BNFExclusionGapInhabitedV1", .cons previous (.cons next (.cons source (.cons output .nil)))⟩

def rawIntegerGoal (relation : String) (first second : GroundTerm) : GroundAtom :=
  ⟨relation, .cons first (.cons second .nil)⟩

theorem meaning_rawExclusion_iff (source output : GroundTerm) :
    Meaning (rawExclusionGoal source output) ↔
      ∀ excluded, source = encodeScalars excluded →
        output = resultTerm (exceptGapCheck excluded) := by
  constructor
  · intro observed excluded sourceEq
    subst source
    exact (meaning_exclusion_iff excluded output).mp observed
  · intro observed
    cases decoded : decodeScalars source with
    | none => simp [Meaning, rawExclusionGoal, decoded]
    | some excluded =>
      have outputEq := observed excluded
        (PlainBnfSourceScalarCodec.decodeScalars_reflects source excluded decoded)
      simpa [Meaning, rawExclusionGoal, decoded] using outputEq

theorem meaning_rawTail_iff (previous source output : GroundTerm) :
    Meaning (rawTailGoal previous source output) ↔
      ∀ (value : Nat) (excluded : List Nat), previous = .integer value → source = encodeScalars excluded →
        output = resultTerm (gapAfter value excluded) := by
  constructor
  · intro observed value excluded previousEq sourceEq
    subst previous
    subst source
    exact (meaning_tail_iff value excluded output).mp observed
  · intro observed
    cases previous with
    | atom name => simp [Meaning, rawTailGoal]
    | app name arguments => simp [Meaning, rawTailGoal]
    | integer value =>
      by_cases nonnegative : 0 ≤ value
      · cases decoded : decodeScalars source with
        | none => simp [Meaning, rawTailGoal, nonnegative, decoded]
        | some excluded =>
          have outputEq := observed value.toNat excluded
            (by simp [Int.toNat_of_nonneg nonnegative])
            (PlainBnfSourceScalarCodec.decodeScalars_reflects source excluded decoded)
          simpa [Meaning, rawTailGoal, nonnegative, decoded] using outputEq
      · simp [Meaning, rawTailGoal, nonnegative]

theorem meaning_rawGap_iff (previous next source output : GroundTerm) :
    Meaning (rawGapGoal previous next source output) ↔
      ∀ (first second : Nat) (excluded : List Nat), previous = .integer first → next = .integer second →
        source = encodeScalars excluded →
          output = resultTerm (gapAfter first (second :: excluded)) := by
  constructor
  · intro observed first second excluded previousEq nextEq sourceEq
    subst previous
    subst next
    subst source
    exact (meaning_gap_iff first second excluded output).mp observed
  · intro observed
    cases previous with
    | atom name => simp [Meaning, rawGapGoal]
    | app name arguments => simp [Meaning, rawGapGoal]
    | integer first =>
      cases next with
      | atom name => simp [Meaning, rawGapGoal]
      | app name arguments => simp [Meaning, rawGapGoal]
      | integer second =>
        by_cases nonnegative : 0 ≤ first ∧ 0 ≤ second
        · cases decoded : decodeScalars source with
          | none => simp [Meaning, rawGapGoal, nonnegative, decoded]
          | some excluded =>
            have outputEq := observed first.toNat second.toNat excluded
              (by simp [Int.toNat_of_nonneg nonnegative.1])
              (by simp [Int.toNat_of_nonneg nonnegative.2])
              (PlainBnfSourceScalarCodec.decodeScalars_reflects source excluded decoded)
            simpa [Meaning, rawGapGoal, nonnegative, decoded] using outputEq
        · simp [Meaning, rawGapGoal, nonnegative]

private theorem scalarCons_encode_iff (first rest : GroundTerm) (head : Nat) (tail : List Nat) :
    scalarCons first rest = encodeScalars (head :: tail) ↔
      first = .integer head ∧ rest = encodeScalars tail := by
  simp [scalarCons, encodeScalars]

private theorem scalarCons_ne_nil (first rest : GroundTerm) :
    scalarCons first rest ≠ encodeScalars [] := by
  simp [scalarCons, encodeScalars]

theorem empty_exclusion_local :
    Meaning (rawExclusionGoal (encodeScalars []) (resultTerm true)) := by
  change Meaning (exclusionGoal [] (resultTerm true))
  simp [exceptGapCheck]

theorem zero_exclusion_local (tail output : GroundTerm)
    (premise : Meaning (rawTailGoal (.integer 0) tail output)) :
    Meaning (rawExclusionGoal (scalarCons (.integer 0) tail) output) := by
  apply (meaning_rawExclusion_iff _ _).mpr
  intro excluded sourceEq
  cases excluded with
  | nil => exact False.elim (scalarCons_ne_nil _ _ sourceEq)
  | cons first rest =>
    obtain ⟨firstEq, tailEq⟩ := (scalarCons_encode_iff _ _ _ _).mp sourceEq
    have zero : first = 0 := by simpa using firstEq.symm
    subst first
    have observed := (meaning_rawTail_iff _ _ _).mp premise 0 rest rfl tailEq
    simpa [exceptGapCheck] using observed

theorem missing_zero_local (first tail : GroundTerm)
    (premise : Meaning (differentGoal first (.integer 0))) :
    Meaning (rawExclusionGoal (scalarCons first tail) (resultTerm true)) := by
  apply (meaning_rawExclusion_iff _ _).mpr
  intro excluded sourceEq
  cases excluded with
  | nil => exact False.elim (scalarCons_ne_nil _ _ sourceEq)
  | cons head rest =>
    obtain ⟨firstEq, _⟩ := (scalarCons_encode_iff _ _ _ _).mp sourceEq
    subst first
    have different := (meaning_different_iff (.integer head) (.integer 0)).mp premise
    have nonzero : head ≠ 0 := by simpa using different
    simp [exceptGapCheck, nonzero]

theorem tail_less_local (last : GroundTerm)
    (premise : Meaning (rawIntegerGoal "ground-integer-less" last (.integer 1114111))) :
    Meaning (rawTailGoal last (encodeScalars []) (resultTerm true)) := by
  apply (meaning_rawTail_iff _ _ _).mpr
  intro value excluded lastEq sourceEq
  subst last
  have nil : excluded = [] := (PlainBnfSourceScalarCodec.encodeScalars_injective sourceEq).symm
  subst excluded
  have below : (value : Int) < 1114111 := premise
  have belowNat : value < 1114111 := by exact_mod_cast below
  simp [gapAfter, belowNat]

theorem tail_notLess_local (last : GroundTerm)
    (premise : Meaning (rawIntegerGoal "ground-integer-not-less" last (.integer 1114111))) :
    Meaning (rawTailGoal last (encodeScalars []) (resultTerm false)) := by
  apply (meaning_rawTail_iff _ _ _).mpr
  intro value excluded lastEq sourceEq
  subst last
  have nil : excluded = [] := (PlainBnfSourceScalarCodec.encodeScalars_injective sourceEq).symm
  subst excluded
  have above : 1114111 ≤ (value : Int) := premise
  have aboveNat : 1114111 ≤ value := by exact_mod_cast above
  simp [gapAfter, show ¬ value < 1114111 by omega]

theorem tail_cons_local (previous next tail output : GroundTerm)
    (premise : Meaning (rawGapGoal previous next tail output)) :
    Meaning (rawTailGoal previous (scalarCons next tail) output) := by
  apply (meaning_rawTail_iff _ _ _).mpr
  intro value excluded previousEq sourceEq
  cases excluded with
  | nil => exact False.elim (scalarCons_ne_nil _ _ sourceEq)
  | cons head rest =>
    obtain ⟨nextEq, tailEq⟩ := (scalarCons_encode_iff _ _ _ _).mp sourceEq
    exact (meaning_rawGap_iff _ _ _ _).mp premise value head rest previousEq nextEq tailEq

theorem surrogate_local (tail output : GroundTerm)
    (premise : Meaning (rawTailGoal (.integer 57344) tail output)) :
    Meaning (rawGapGoal (.integer 55295) (.integer 57344) tail output) := by
  apply (meaning_rawGap_iff _ _ _ _).mpr
  intro first second excluded firstEq secondEq sourceEq
  have firstInt : (first : Int) = 55295 := by simpa using firstEq.symm
  have secondInt : (second : Int) = 57344 := by simpa using secondEq.symm
  have firstValue : first = 55295 := by exact_mod_cast firstInt
  have secondValue : second = 57344 := by exact_mod_cast secondInt
  subst first
  subst second
  simpa [gapAfter_surrogate] using
    (meaning_rawTail_iff _ _ _).mp premise 57344 excluded rfl sourceEq

private theorem scalarPair_aliasFree (first second : Nat) :
    AliasFree (scalarPair (.integer first) (.integer second)) :=
  .app (by decide) (.cons (.integer first) (.cons (.integer second) .nil))

private theorem distinct_pair_not_hole (first second : Nat)
    (premise : Meaning (differentGoal (scalarPair (.integer first) (.integer second))
      (scalarPair (.integer 55295) (.integer 57344)))) :
    ¬ (first = 55295 ∧ second = 57344) := by
  have distinct := (meaning_different_iff (scalarPair_aliasFree first second)
    (scalarPair_aliasFree 55295 57344)).mp premise
  rintro ⟨rfl, rfl⟩
  exact distinct rfl

theorem gap_local (previous next tail : GroundTerm)
    (different : Meaning (differentGoal (scalarPair previous next)
      (scalarPair (.integer 55295) (.integer 57344))))
    (numerical : Meaning (rawIntegerGoal "ground-integer-gap" previous next)) :
    Meaning (rawGapGoal previous next tail (resultTerm true)) := by
  apply (meaning_rawGap_iff _ _ _ _).mpr
  intro first second excluded previousEq nextEq _
  subst previous
  subst next
  have notHole := distinct_pair_not_hole first second different
  have gapInt : (first : Int) + 1 < second := numerical
  have gap : first + 1 < second := by exact_mod_cast gapInt
  simp [gapAfter_gap first second excluded notHole gap]

theorem no_gap_local (previous next tail output : GroundTerm)
    (different : Meaning (differentGoal (scalarPair previous next)
      (scalarPair (.integer 55295) (.integer 57344))))
    (numerical : Meaning (rawIntegerGoal "ground-integer-no-gap" previous next))
    (recursive : Meaning (rawTailGoal next tail output)) :
    Meaning (rawGapGoal previous next tail output) := by
  apply (meaning_rawGap_iff _ _ _ _).mpr
  intro first second excluded previousEq nextEq sourceEq
  subst previous
  subst next
  have notHole := distinct_pair_not_hole first second different
  have noGapInt : (second : Int) ≤ (first : Int) + 1 := numerical
  have noGap : second ≤ first + 1 := by exact_mod_cast noGapInt
  simpa [gapAfter_noGap first second excluded notHole noGap] using
    (meaning_rawTail_iff _ _ _).mp recursive second excluded rfl sourceEq

theorem points_local (source output : GroundTerm) :
    Meaning ⟨"BNFLexicalMatcherInhabitedV1",
      .cons (.app "bnf-v1:lexical-points" (.cons source .nil)) (.cons output .nil)⟩ := by
  simp [Meaning]

/-! ## Positive and discriminating negative controls -/

theorem independent_exclusion_result_satisfies (excluded : List Nat) :
    Meaning (exclusionGoal excluded (resultTerm (exceptGapCheck excluded))) := by simp

theorem opposite_exclusion_result_is_false (excluded : List Nat) :
    ¬ Meaning (exclusionGoal excluded (resultTerm (!(exceptGapCheck excluded)))) := by simp

theorem arbitrary_forged_result_is_false (excluded : List Nat) :
    ¬ Meaning (exclusionGoal excluded (.atom "ForgedResult")) := by
  simp only [meaning_exclusion_iff]
  cases exceptGapCheck excluded <;> simp [resultTerm]

theorem forged_tail_result_is_false (previous : Nat) (excluded : List Nat) :
    ¬ Meaning (tailGoal previous excluded (.app "not-a-boolean-result" .nil)) := by
  simp only [meaning_tail_iff]
  cases gapAfter previous excluded <;> simp [resultTerm]

theorem forged_gap_result_is_false (previous next : Nat) (excluded : List Nat) :
    ¬ Meaning (gapGoal previous next excluded (.integer 7)) := by
  simp only [meaning_gap_iff]
  cases gapAfter previous (next :: excluded) <;> simp [resultTerm]

theorem integer_controls :
    Meaning (integerGoal "ground-integer-less" 0 1) ∧
      ¬ Meaning (integerGoal "ground-integer-less" 1 0) ∧
      Meaning (integerGoal "ground-integer-no-gap" 0 1) ∧
      ¬ Meaning (integerGoal "ground-integer-gap" 0 1) := by simp

theorem structural_disequality_controls :
    Meaning (differentGoal (.integer 0) (.integer 1)) ∧
      ¬ Meaning (differentGoal (.integer 0) (.integer 0)) := by
  simp [meaning_different_iff (.integer 0) (.integer 1),
    meaning_different_iff (.integer 0) (.integer 0)]

/-- Unobserved syntax satisfies the predicate but is still rejected by the
source decoder. This prevents using `Meaning` as an admission test. -/
theorem malformed_profile_is_not_admission :
    Meaning ⟨"BNFLexicalMatcherInhabitedV1",
      .cons (.app "bnf-v1:lexical-except" (.cons (.atom "not-a-list") .nil))
        (.cons (.atom "ForgedResult") .nil)⟩ ∧
      decodeScalars (.atom "not-a-list") = none := by
  simp [Meaning, decodeScalars]

theorem negative_scan_index_is_unobserved (excluded : List Nat) (output : GroundTerm) :
    Meaning ⟨"BNFExclusionTailInhabitedV1", .cons (.integer (-1))
      (.cons (encodeScalars excluded) (.cons output .nil))⟩ := by simp [Meaning]

theorem other_lexical_constructor_is_unobserved (output : GroundTerm) :
    Meaning ⟨"BNFLexicalMatcherInhabitedV1",
      .cons (.app "bnf-v1:lexical-points" (.cons (encodeScalars []) .nil))
        (.cons output .nil)⟩ := by simp [Meaning]

theorem unknown_relation_is_unobserved (arguments : GroundTerms) :
    Meaning ⟨"unobserved-relation", arguments⟩ := by simp [Meaning]

/-- Admission checks cannot be recovered from this scan observation. -/
theorem invalid_unicode_inventory_is_not_admitted_by_meaning :
    Meaning (exclusionGoal [55296] (resultTerm true)) ∧
      ParserProfileSemantics.isUnicodeScalar 55296 = false := by
  simp [exceptGapCheck, ParserProfileSemantics.isUnicodeScalar]

#print axioms meaning_exclusion_iff
#print axioms meaning_gap_iff
#print axioms meaning_different_iff
#print axioms meaning_noGap_tail_iff
#print axioms opposite_exclusion_result_is_false
#print axioms arbitrary_forged_result_is_false
#print axioms zero_exclusion_local
#print axioms tail_cons_local
#print axioms gap_local
#print axioms no_gap_local

end Mettapedia.GSLT.Parsing.PlainBnfExclusionLocalModel
