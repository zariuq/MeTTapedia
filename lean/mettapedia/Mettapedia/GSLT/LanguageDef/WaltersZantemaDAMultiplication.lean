import Mettapedia.GSLT.LanguageDef.WaltersZantemaDAAddition

/-!
# Certified digit multiplication for Walters--Zantema DA

This file follows paper rules 5, 6, 9, and 10.  Digit multiplication is
performed by the authored `star` recursion; full multiplication is the
authored shift-and-add recursion.  Addition is discharged through the exact
rule-2/3/4 graph proved in `WaltersZantemaDAAddition`.
-/

namespace Mettapedia.GSLT.LanguageDef.WaltersZantemaDA

namespace MultiStep

theorem mapAddLeft {schema : Schema} (right : SemanticTerm)
    {source target : SemanticTerm} (steps : MultiStep schema source target) :
    MultiStep schema (.add source right) (.add target right) := by
  induction steps with
  | refl => exact .refl
  | tail previous finalStep inductionHypothesis =>
      exact .tail inductionHypothesis (.addLeft finalStep)

theorem mapAddRight {schema : Schema} (left : SemanticTerm)
    {source target : SemanticTerm} (steps : MultiStep schema source target) :
    MultiStep schema (.add left source) (.add left target) := by
  induction steps with
  | refl => exact .refl
  | tail previous finalStep inductionHypothesis =>
      exact .tail inductionHypothesis (.addRight finalStep)

theorem mapMulLeft {schema : Schema} (right : SemanticTerm)
    {source target : SemanticTerm} (steps : MultiStep schema source target) :
    MultiStep schema (.mul source right) (.mul target right) := by
  induction steps with
  | refl => exact .refl
  | tail previous finalStep inductionHypothesis =>
      exact .tail inductionHypothesis (.mulLeft finalStep)

theorem mapStar {schema : Schema} (index : Nat)
    {source target : SemanticTerm} (steps : MultiStep schema source target) :
    MultiStep schema (.star index source) (.star index target) := by
  induction steps with
  | refl => exact .refl
  | tail previous finalStep inductionHypothesis =>
      exact .tail inductionHypothesis (.star index finalStep)

end MultiStep

/-! ## The bounded product numeral embedded in paper rule 10 -/

/-- The at-most-two-digit numeral placed literally in each finite instance of
paper rule 10. -/
def digitProductDigits (schema : Schema) (first second : Nat) : List Nat :=
  let product := first * second
  if product = 0 then []
  else
    let high := product / schema.radix
    let low := product % schema.radix
    if high = 0 then [low] else [low, high]

theorem semanticDigitProductNumeral_eq_termOfDigits
    (schema : Schema) (first second : Nat) :
    semanticDigitProductNumeral schema first second =
      termOfDigits (digitProductDigits schema first second) := by
  unfold semanticDigitProductNumeral digitProductDigits
  by_cases productZero : first * second = 0
  · simp [productZero, termOfDigits]
  · simp only [productZero, if_false]
    by_cases highZero : first * second / schema.radix = 0
    · simp [highZero, termOfDigits]
    · simp [highZero, termOfDigits]

theorem digitProductDigits_in_range (schema : Schema) {first second : Nat}
    (firstDigit : first < schema.radix)
    (secondDigit : second < schema.radix) :
    DigitsInRange schema (digitProductDigits schema first second) := by
  have radixPositive : 0 < schema.radix :=
    lt_of_lt_of_le (by decide : 0 < 2) schema.radix_ge_two
  have productBound : first * second < schema.radix * schema.radix := by
    nlinarith
  have lowBound : first * second % schema.radix < schema.radix :=
    Nat.mod_lt _ radixPositive
  have highBound : first * second / schema.radix < schema.radix :=
    (Nat.div_lt_iff_lt_mul radixPositive).2 (by
      simpa [Nat.mul_comm] using productBound)
  unfold digitProductDigits
  by_cases productZero : first * second = 0
  · simp [productZero, DigitsInRange]
  · simp only [productZero, if_false]
    by_cases highZero : first * second / schema.radix = 0
    · intro digit member
      simp only [highZero, if_pos, List.mem_cons, List.not_mem_nil,
        or_false] at member
      subst digit
      exact lowBound
    · intro digit member
      simp only [highZero, if_false, List.mem_cons] at member
      rcases member with rfl | member
      · exact lowBound
      · rcases member with rfl | impossible
        · exact highBound
        · simp at impossible

theorem decodeDigits_digitProductDigits (schema : Schema)
    (first second : Nat) :
    decodeDigits schema (digitProductDigits schema first second) =
      first * second := by
  rw [← termOfDigits_denote schema (fun _ => 0)]
  rw [← semanticDigitProductNumeral_eq_termOfDigits]
  exact semanticDigitProductNumeral_denote schema (fun _ => 0) first second

theorem decodeDigits_zero_cons_encodeDigits (schema : Schema) (number : Nat) :
    decodeDigits schema (0 :: encodeDigits schema number) =
      schema.radix * number := by
  simp only [decodeDigits, Nat.ofDigits, encodeDigits]
  rw [Nat.ofDigits_digits]
  simp

/-! ## Certified rule-9/10 digit multiplication -/

/-- One digit times an arbitrary in-range numeral reduces through rules 9/10
and the already-certified addition graph to its canonical product. -/
theorem starDigits_reach (schema : Schema) {factor : Nat} {digits : List Nat}
    (factorDigit : factor < schema.radix)
    (digitsRange : DigitsInRange schema digits) :
    MultiStep schema (.star factor (termOfDigits digits))
      (encodeTerm schema (factor * decodeDigits schema digits)) := by
  induction digits with
  | nil =>
      simpa [termOfDigits, encodeTerm, encodeDigits, decodeDigits,
        Nat.ofDigits] using
        MultiStep.single (Step.root (RootStep.rule9 schema factorDigit))
  | cons digit digits inductionHypothesis =>
      have digitRange : digit < schema.radix := digitsRange digit (by simp)
      have tailRange : DigitsInRange schema digits := by
        intro value member
        exact digitsRange value (List.mem_cons_of_mem digit member)
      let productDigits := digitProductDigits schema factor digit
      have productRange : DigitsInRange schema productDigits :=
        digitProductDigits_in_range schema factorDigit digitRange
      have root :
          MultiStep schema (.star factor (.digit digit (termOfDigits digits)))
            (.add (.digit 0 (.star factor (termOfDigits digits)))
              (termOfDigits productDigits)) := by
        simpa [productDigits, semanticDigitProductNumeral_eq_termOfDigits] using
          MultiStep.single
            (Step.root (RootStep.rule10 schema factorDigit digitRange
              (termOfDigits digits)))
      have recursive := inductionHypothesis tailRange
      have recursiveUnder := MultiStep.mapAddLeft (termOfDigits productDigits)
        (MultiStep.mapDigit 0 recursive)
      have shiftedRange : DigitsInRange schema
          (0 :: encodeDigits schema (factor * decodeDigits schema digits)) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact lt_of_lt_of_le (by decide : 0 < 2) schema.radix_ge_two
        · exact (encodeDigits_canonical schema
            (factor * decodeDigits schema digits)).1 value member
      have addition := addDigits_canonical_reach schema shiftedRange productRange
      have resultEquation :
          decodeDigits schema
              (0 :: encodeDigits schema (factor * decodeDigits schema digits)) +
            decodeDigits schema productDigits =
          factor * decodeDigits schema (digit :: digits) := by
        rw [decodeDigits_zero_cons_encodeDigits,
          decodeDigits_digitProductDigits]
        simp only [decodeDigits, Nat.ofDigits]
        norm_num
        ring
      rw [resultEquation] at addition
      exact (root.trans recursiveUnder).trans (by
        simpa [encodeTerm, termOfDigits] using addition)

/-! ## Certified rule-5/6 full multiplication -/

/-- Full shift-and-add multiplication reduces through rules 5/6/9/10 and the
authored addition rules to the canonical product numeral. -/
theorem multiplyDigits_reach (schema : Schema) {left right : List Nat}
    (leftRange : DigitsInRange schema left)
    (rightRange : DigitsInRange schema right) :
    MultiStep schema (.mul (termOfDigits left) (termOfDigits right))
      (encodeTerm schema
        (decodeDigits schema left * decodeDigits schema right)) := by
  induction left with
  | nil =>
      simpa [termOfDigits, encodeTerm, encodeDigits, decodeDigits,
        Nat.ofDigits] using
        MultiStep.single
          (Step.root (RootStep.rule5 schema (termOfDigits right)))
  | cons digit left inductionHypothesis =>
      have digitRange : digit < schema.radix := leftRange digit (by simp)
      have tailRange : DigitsInRange schema left := by
        intro value member
        exact leftRange value (List.mem_cons_of_mem digit member)
      have root :
          MultiStep schema
            (.mul (.digit digit (termOfDigits left)) (termOfDigits right))
            (.add (.digit 0 (.mul (termOfDigits left) (termOfDigits right)))
              (.star digit (termOfDigits right))) := by
        exact MultiStep.single
          (Step.root (RootStep.rule6 schema digitRange
            (termOfDigits left) (termOfDigits right)))
      have recursive := inductionHypothesis tailRange
      have recursiveUnder := MultiStep.mapAddLeft
        (.star digit (termOfDigits right))
        (MultiStep.mapDigit 0 recursive)
      have digitProduct := starDigits_reach schema digitRange rightRange
      have digitProductUnder := MultiStep.mapAddRight
        (.digit 0 (encodeTerm schema
          (decodeDigits schema left * decodeDigits schema right)))
        digitProduct
      have shiftedRange : DigitsInRange schema
          (0 :: encodeDigits schema
            (decodeDigits schema left * decodeDigits schema right)) := by
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact lt_of_lt_of_le (by decide : 0 < 2) schema.radix_ge_two
        · exact (encodeDigits_canonical schema
            (decodeDigits schema left * decodeDigits schema right)).1 value member
      have productRange := (encodeDigits_canonical schema
        (digit * decodeDigits schema right)).1
      have addition := addDigits_canonical_reach schema shiftedRange productRange
      have resultEquation :
          decodeDigits schema
              (0 :: encodeDigits schema
                (decodeDigits schema left * decodeDigits schema right)) +
            decodeDigits schema
              (encodeDigits schema (digit * decodeDigits schema right)) =
          decodeDigits schema (digit :: left) * decodeDigits schema right := by
        rw [decodeDigits_zero_cons_encodeDigits,
          decodeDigits_encodeDigits]
        simp only [decodeDigits, Nat.ofDigits]
        norm_num
        ring
      rw [resultEquation] at addition
      exact ((root.trans recursiveUnder).trans digitProductUnder).trans (by
        simpa [encodeTerm, termOfDigits] using addition)

/-- The complete multiplication graph for canonical generated numerals. -/
theorem encoded_multiplication_graph
    (schema : Schema) (first second result : Nat) :
    MultiStep schema
        (.mul (encodeTerm schema first) (encodeTerm schema second))
        (encodeTerm schema result) ↔
      result = first * second := by
  constructor
  · intro path
    have preserved := multiStep_sound path (fun _ => 0)
    simpa [SemanticTerm.denote, encodeTerm_denote, Nat.mul_comm] using preserved.symm
  · intro resultEquation
    subst result
    simpa [encodeTerm, decodeDigits_encodeDigits] using
      multiplyDigits_reach schema
        (encodeDigits_canonical schema first).1
        (encodeDigits_canonical schema second).1

/-- Positive control for nested shift-and-add and carry propagation. -/
theorem radixTwo_seven_times_six_reaches_forty_two :
    MultiStep radixTwo
      (.mul (encodeTerm radixTwo 7) (encodeTerm radixTwo 6))
      (encodeTerm radixTwo 42) := by
  exact (encoded_multiplication_graph radixTwo 7 6 42).2 rfl

/-- Negative no-invention control for multiplication. -/
theorem radixTwo_seven_times_six_not_forty_one :
    ¬ MultiStep radixTwo
      (.mul (encodeTerm radixTwo 7) (encodeTerm radixTwo 6))
      (encodeTerm radixTwo 41) := by
  intro path
  have impossible := (encoded_multiplication_graph radixTwo 7 6 41).1 path
  omega

#print axioms starDigits_reach
#print axioms multiplyDigits_reach
#print axioms encoded_multiplication_graph
#print axioms radixTwo_seven_times_six_not_forty_one

end Mettapedia.GSLT.LanguageDef.WaltersZantemaDA
