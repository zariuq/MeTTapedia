import Mettapedia.GSLT.LanguageDef.WaltersZantemaDASemantics

/-!
# Certified digit addition for Walters--Zantema DA

This file follows the paper rules themselves.  `incrementDigits` is rules
7--8 and `addDigits` is rules 2--4.  The reachability proofs construct paths in
the contextual closure of the generated root rules; arithmetic correctness is
then a corollary of the previously proved step soundness.
-/

namespace Mettapedia.GSLT.LanguageDef.WaltersZantemaDA

/-- Paper-style numeral term from least-significant-digit-first data. -/
def termOfDigits : List Nat → SemanticTerm
  | [] => .empty
  | digit :: digits => .digit digit (termOfDigits digits)

/-- Every digit belongs to the selected finite radix. -/
def DigitsInRange (schema : Schema) (digits : List Nat) : Prop :=
  ∀ digit ∈ digits, digit < schema.radix

theorem termOfDigits_denote (schema : Schema) (valuation : String → Nat)
    (digits : List Nat) :
    (termOfDigits digits).denote schema valuation = decodeDigits schema digits := by
  induction digits with
  | nil => rfl
  | cons digit digits inductionHypothesis =>
      simp [termOfDigits, SemanticTerm.denote, decodeDigits, Nat.ofDigits,
        inductionHypothesis, Nat.add_comm]

theorem termOfDigits_toPattern (digits : List Nat) :
    (termOfDigits digits).toPattern = patternOfDigits digits := by
  induction digits with
  | nil => rfl
  | cons digit digits inductionHypothesis =>
      simp [termOfDigits, SemanticTerm.toPattern, patternOfDigits,
        inductionHypothesis]

/-- Canonical semantic numeral for one natural number. -/
def encodeTerm (schema : Schema) (number : Nat) : SemanticTerm :=
  termOfDigits (encodeDigits schema number)

theorem encodeTerm_denote (schema : Schema) (valuation : String → Nat)
    (number : Nat) :
    (encodeTerm schema number).denote schema valuation = number := by
  rw [encodeTerm, termOfDigits_denote, decodeDigits_encodeDigits]

theorem encodeTerm_toPattern (schema : Schema) (number : Nat) :
    (encodeTerm schema number).toPattern = encodePattern schema number := by
  exact termOfDigits_toPattern (encodeDigits schema number)

namespace MultiStep

theorem single {schema : Schema} {source target : SemanticTerm}
    (step : Step schema source target) : MultiStep schema source target :=
  Relation.ReflTransGen.tail .refl step

theorem mapDigit {schema : Schema} (index : Nat) {source target : SemanticTerm}
    (steps : MultiStep schema source target) :
    MultiStep schema (.digit index source) (.digit index target) := by
  induction steps with
  | refl => exact .refl
  | tail previous finalStep inductionHypothesis =>
      exact .tail inductionHypothesis (.digit index finalStep)

theorem mapSucc {schema : Schema} {source target : SemanticTerm}
    (steps : MultiStep schema source target) :
    MultiStep schema (.succ source) (.succ target) := by
  induction steps with
  | refl => exact .refl
  | tail previous finalStep inductionHypothesis =>
      exact .tail inductionHypothesis (.succ finalStep)

end MultiStep

/-- Digit-list successor, directly mirroring paper rules 7--8. -/
def incrementDigits (schema : Schema) : List Nat → List Nat
  | [] => [1]
  | digit :: digits =>
      if digit + 1 < schema.radix then (digit + 1) :: digits
      else 0 :: incrementDigits schema digits

theorem incrementDigits_in_range (schema : Schema) {digits : List Nat}
    (inRange : DigitsInRange schema digits) :
    DigitsInRange schema (incrementDigits schema digits) := by
  induction digits with
  | nil =>
      intro digit member
      simp only [incrementDigits, List.mem_cons, List.not_mem_nil, or_false] at member
      subst digit
      exact schema.radix_ge_two
  | cons digit digits inductionHypothesis =>
      have digitRange : digit < schema.radix := inRange digit (by simp)
      have tailRange : DigitsInRange schema digits := by
        intro value member
        exact inRange value (List.mem_cons_of_mem digit member)
      by_cases noCarry : digit + 1 < schema.radix
      · intro value member
        rw [incrementDigits, if_pos noCarry] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact noCarry
        · exact tailRange value member
      · intro value member
        rw [incrementDigits, if_neg noCarry] at member
        rcases List.mem_cons.mp member with rfl | member
        · exact lt_of_lt_of_le (by decide : 0 < 2) schema.radix_ge_two
        · exact inductionHypothesis tailRange value member

/-- Every in-range digit list has a certified successor reduction. -/
theorem incrementDigits_reach (schema : Schema) {digits : List Nat}
    (inRange : DigitsInRange schema digits) :
    MultiStep schema (.succ (termOfDigits digits))
      (termOfDigits (incrementDigits schema digits)) := by
  induction digits with
  | nil =>
      simpa [termOfDigits, incrementDigits] using
        MultiStep.single (Step.root (RootStep.rule7 schema))
  | cons digit digits inductionHypothesis =>
      have digitRange : digit < schema.radix := inRange digit (by simp)
      have tailRange : DigitsInRange schema digits := by
        intro value member
        exact inRange value (List.mem_cons_of_mem digit member)
      by_cases carry : schema.radix ≤ 1 + digit
      · have digitPlusOne : digit + 1 = schema.radix := by omega
        have sumMod : (1 + digit) % schema.radix = 0 := by
          rw [Nat.add_comm, digitPlusOne, Nat.mod_self]
        have noSmallIncrement : ¬digit + 1 < schema.radix := by omega
        have root :
            MultiStep schema
              (.succ (.digit digit (termOfDigits digits)))
              (.digit 0 (.succ (termOfDigits digits))) := by
          simpa [semanticCarryApply, carry, digitSum, sumMod] using
            MultiStep.single
              (Step.root (RootStep.rule8 schema digitRange
                (termOfDigits digits)))
        have recursive :=
          MultiStep.mapDigit 0 (inductionHypothesis tailRange)
        exact root.trans (by
          simpa [termOfDigits, incrementDigits, noSmallIncrement] using recursive)
      · have noCarry : 1 + digit < schema.radix := Nat.lt_of_not_ge carry
        have smallIncrement : digit + 1 < schema.radix := by omega
        have sumMod : (1 + digit) % schema.radix = 1 + digit :=
          Nat.mod_eq_of_lt noCarry
        have carry' : ¬ schema.radix ≤ digit + 1 := by omega
        have sumMod' : (digit + 1) % schema.radix = digit + 1 :=
          Nat.mod_eq_of_lt smallIncrement
        simpa [termOfDigits, incrementDigits, smallIncrement,
          semanticCarryApply, carry, carry', digitSum, sumMod, sumMod', Nat.add_comm] using
          MultiStep.single
            (Step.root (RootStep.rule8 schema digitRange
              (termOfDigits digits)))

/-! ## Canonical numeral normalization by paper rule 1 -/

/-- Remove only the zeroes beyond the most-significant nonzero digit.  This is
the list-level strategy implemented by paper rule 1, `()0 -> ()`. -/
def normalizeDigits (schema : Schema) : List Nat → List Nat
  | [] => []
  | digit :: digits =>
      match normalizeDigits schema digits with
      | [] => if digit = 0 then [] else [digit]
      | next :: rest => digit :: next :: rest

theorem decodeDigits_normalizeDigits (schema : Schema) (digits : List Nat) :
    decodeDigits schema (normalizeDigits schema digits) =
      decodeDigits schema digits := by
  induction digits with
  | nil => rfl
  | cons digit digits inductionHypothesis =>
      simp only [normalizeDigits]
      cases normalized : normalizeDigits schema digits with
      | nil =>
          have tailZero : Nat.ofDigits schema.radix digits = 0 := by
            simpa only [decodeDigits, normalized, Nat.ofDigits_nil] using
              inductionHypothesis.symm
          by_cases digitZero : digit = 0
          · subst digit
            simp [decodeDigits, Nat.ofDigits, tailZero]
          · simp [digitZero, decodeDigits, Nat.ofDigits, tailZero]
      | cons next rest =>
          have tailEquation :
              Nat.ofDigits schema.radix (next :: rest) =
                Nat.ofDigits schema.radix digits := by
            simpa only [decodeDigits, normalized] using inductionHypothesis
          change digit + schema.radix * Nat.ofDigits schema.radix (next :: rest) =
            digit + schema.radix * Nat.ofDigits schema.radix digits
          rw [tailEquation]

theorem normalizeDigits_in_range (schema : Schema) {digits : List Nat}
    (inRange : DigitsInRange schema digits) :
    DigitsInRange schema (normalizeDigits schema digits) := by
  induction digits with
  | nil => simp [normalizeDigits, DigitsInRange]
  | cons digit digits inductionHypothesis =>
      have digitRange : digit < schema.radix := inRange digit (by simp)
      have tailRange : DigitsInRange schema digits := by
        intro value member
        exact inRange value (List.mem_cons_of_mem digit member)
      have normalizedTailRange := inductionHypothesis tailRange
      simp only [normalizeDigits]
      cases normalized : normalizeDigits schema digits with
      | nil =>
          by_cases digitZero : digit = 0
          · simp [digitZero, DigitsInRange]
          · intro value member
            simp only [digitZero, if_false, List.mem_cons,
              List.not_mem_nil, or_false] at member
            subst value
            exact digitRange
      | cons next rest =>
          intro value member
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact digitRange
          · exact normalizedTailRange value (by simpa [normalized] using member)

theorem normalizeDigits_getLast?_ne_zero (schema : Schema) (digits : List Nat) :
    (normalizeDigits schema digits).getLast? ≠ some 0 := by
  induction digits with
  | nil => simp [normalizeDigits]
  | cons digit digits inductionHypothesis =>
      simp only [normalizeDigits]
      cases normalized : normalizeDigits schema digits with
      | nil =>
          by_cases digitZero : digit = 0
          · simp [digitZero]
          · simp [digitZero]
      | cons next rest =>
          have tailLast : (next :: rest).getLast? ≠ some 0 := by
            simpa [normalized] using inductionHypothesis
          simpa using tailLast

theorem normalizeDigits_last_ne_zero (schema : Schema) (digits : List Nat)
    (nonempty : normalizeDigits schema digits ≠ []) :
    (normalizeDigits schema digits).getLast nonempty ≠ 0 := by
  intro lastZero
  apply normalizeDigits_getLast?_ne_zero schema digits
  rw [List.getLast?_eq_getLast_of_ne_nil nonempty, lastZero]

theorem normalizeDigits_canonical (schema : Schema) {digits : List Nat}
    (inRange : DigitsInRange schema digits) :
    CanonicalDigits schema (normalizeDigits schema digits) := by
  exact ⟨normalizeDigits_in_range schema inRange,
    normalizeDigits_last_ne_zero schema digits⟩

theorem normalizeDigits_eq_encodeDigits (schema : Schema) {digits : List Nat}
    (inRange : DigitsInRange schema digits) :
    normalizeDigits schema digits =
      encodeDigits schema (decodeDigits schema digits) := by
  apply decodeDigits_injective_on_canonical schema
    (normalizeDigits_canonical schema inRange)
    (encodeDigits_canonical schema (decodeDigits schema digits))
  rw [decodeDigits_normalizeDigits, decodeDigits_encodeDigits]

/-- Paper rule 1, under digit contexts, reaches the unique canonical numeral. -/
theorem normalizeDigits_reach (schema : Schema) (digits : List Nat) :
    MultiStep schema (termOfDigits digits)
      (termOfDigits (normalizeDigits schema digits)) := by
  induction digits with
  | nil => exact .refl
  | cons digit digits inductionHypothesis =>
      have nested := MultiStep.mapDigit digit inductionHypothesis
      cases normalized : normalizeDigits schema digits with
      | nil =>
          by_cases digitZero : digit = 0
          · subst digit
            exact nested.trans (by
              simpa [termOfDigits, normalizeDigits, normalized] using
                MultiStep.single (Step.root (RootStep.rule1 schema)))
          · simpa [termOfDigits, normalizeDigits, normalized, digitZero] using nested
      | cons next rest =>
          simpa [termOfDigits, normalizeDigits, normalized] using nested

/-- Digit-list addition, directly mirroring paper rules 2--4. -/
def addDigits (schema : Schema) : List Nat → List Nat → List Nat
  | [], right => right
  | left, [] => left
  | first :: left, second :: right =>
      let outputDigit := (first + second) % schema.radix
      if schema.radix ≤ first + second then
        outputDigit :: incrementDigits schema (addDigits schema left right)
      else
        outputDigit :: addDigits schema left right

theorem addDigits_in_range (schema : Schema) {left right : List Nat}
    (leftRange : DigitsInRange schema left)
    (rightRange : DigitsInRange schema right) :
    DigitsInRange schema (addDigits schema left right) := by
  induction left generalizing right with
  | nil => simpa [addDigits] using rightRange
  | cons first left inductionHypothesis =>
      cases right with
      | nil => simpa [addDigits] using leftRange
      | cons second right =>
          have radixLowerBound := schema.radix_ge_two
          have radixPositive : 0 < schema.radix := by omega
          have leftTailRange : DigitsInRange schema left := by
            intro digit member
            exact leftRange digit (List.mem_cons_of_mem first member)
          have rightTailRange : DigitsInRange schema right := by
            intro digit member
            exact rightRange digit (List.mem_cons_of_mem second member)
          have recursiveRange := inductionHypothesis leftTailRange rightTailRange
          by_cases carry : schema.radix ≤ first + second
          · intro digit member
            rw [addDigits, if_pos carry] at member
            rcases List.mem_cons.mp member with rfl | member
            · exact Nat.mod_lt _ radixPositive
            · exact incrementDigits_in_range schema recursiveRange digit member
          · intro digit member
            rw [addDigits, if_neg carry] at member
            rcases List.mem_cons.mp member with rfl | member
            · exact Nat.mod_lt _ radixPositive
            · exact recursiveRange digit member

/-- Every pair of in-range digit lists has a certified rule-2/3/4 reduction. -/
theorem addDigits_reach (schema : Schema) {left right : List Nat}
    (leftRange : DigitsInRange schema left)
    (rightRange : DigitsInRange schema right) :
    MultiStep schema (.add (termOfDigits left) (termOfDigits right))
      (termOfDigits (addDigits schema left right)) := by
  induction left generalizing right with
  | nil =>
      simpa [termOfDigits, addDigits] using
        MultiStep.single (Step.root (RootStep.rule2 schema (termOfDigits right)))
  | cons first left inductionHypothesis =>
      cases right with
      | nil =>
          simpa [termOfDigits, addDigits] using
            MultiStep.single
              (Step.root (RootStep.rule3 schema (termOfDigits (first :: left))))
      | cons second right =>
          have firstRange : first < schema.radix := leftRange first (by simp)
          have secondRange : second < schema.radix := rightRange second (by simp)
          have leftTailRange : DigitsInRange schema left := by
            intro digit member
            exact leftRange digit (List.mem_cons_of_mem first member)
          have rightTailRange : DigitsInRange schema right := by
            intro digit member
            exact rightRange digit (List.mem_cons_of_mem second member)
          have recursive := inductionHypothesis leftTailRange rightTailRange
          let outputDigit := (first + second) % schema.radix
          by_cases carry : schema.radix ≤ first + second
          · have root :
                MultiStep schema
                  (.add (.digit first (termOfDigits left))
                    (.digit second (termOfDigits right)))
                  (.digit outputDigit
                    (.succ (.add (termOfDigits left) (termOfDigits right)))) := by
              simpa [outputDigit, semanticCarryApply, carry, digitSum] using
                MultiStep.single
                  (Step.root (RootStep.rule4 schema firstRange secondRange
                    (termOfDigits left) (termOfDigits right)))
            have underContexts :=
              MultiStep.mapDigit outputDigit (MultiStep.mapSucc recursive)
            have increment := incrementDigits_reach schema
              (addDigits_in_range schema leftTailRange rightTailRange)
            have normalizedIncrement := MultiStep.mapDigit outputDigit increment
            exact (root.trans underContexts).trans (by
              simpa [termOfDigits, addDigits, carry, outputDigit] using
                normalizedIncrement)
          · have root :
                MultiStep schema
                  (.add (.digit first (termOfDigits left))
                    (.digit second (termOfDigits right)))
                  (.digit outputDigit
                    (.add (termOfDigits left) (termOfDigits right))) := by
              simpa [outputDigit, semanticCarryApply, carry, digitSum] using
                MultiStep.single
                  (Step.root (RootStep.rule4 schema firstRange secondRange
                    (termOfDigits left) (termOfDigits right)))
            exact root.trans (by
              simpa [termOfDigits, addDigits, carry, outputDigit] using
                MultiStep.mapDigit outputDigit recursive)

/-- The certified digit algorithm computes the natural-number addition graph. -/
theorem decodeDigits_addDigits (schema : Schema) {left right : List Nat}
    (leftRange : DigitsInRange schema left)
    (rightRange : DigitsInRange schema right) :
    decodeDigits schema (addDigits schema left right) =
      decodeDigits schema left + decodeDigits schema right := by
  have path := addDigits_reach schema leftRange rightRange
  have preserved := multiStep_sound path (fun _ => 0)
  simpa [SemanticTerm.denote, termOfDigits_denote] using preserved.symm

/-- The concrete digit algorithm has the exact natural-number denotation. -/
theorem addDigits_denotes_addition (schema : Schema) (first second : Nat) :
    decodeDigits schema
        (addDigits schema (encodeDigits schema first) (encodeDigits schema second)) =
      first + second := by
  rw [decodeDigits_addDigits schema
    (encodeDigits_canonical schema first).1
    (encodeDigits_canonical schema second).1,
    decodeDigits_encodeDigits, decodeDigits_encodeDigits]

/-- Addition followed only by paper rule 1 reaches the canonical numeral. -/
theorem addDigits_canonical_reach (schema : Schema) {left right : List Nat}
    (leftRange : DigitsInRange schema left)
    (rightRange : DigitsInRange schema right) :
    MultiStep schema (.add (termOfDigits left) (termOfDigits right))
      (encodeTerm schema
        (decodeDigits schema left + decodeDigits schema right)) := by
  have addition := addDigits_reach schema leftRange rightRange
  have normalization := normalizeDigits_reach schema (addDigits schema left right)
  have normalizedPath := addition.trans normalization
  have range := addDigits_in_range schema leftRange rightRange
  have canonical := normalizeDigits_eq_encodeDigits schema range
  have denotation := decodeDigits_addDigits schema leftRange rightRange
  simpa [encodeTerm, canonical, denotation] using normalizedPath

/-- The complete addition graph for canonical generated numerals.  The reverse
direction is a certified reduction path; the forward direction is
no-invention from rule soundness. -/
theorem encoded_addition_graph (schema : Schema) (first second result : Nat) :
    MultiStep schema
        (.add (encodeTerm schema first) (encodeTerm schema second))
        (encodeTerm schema result) ↔
      result = first + second := by
  constructor
  · intro path
    have preserved := multiStep_sound path (fun _ => 0)
    simpa [SemanticTerm.denote, encodeTerm_denote, Nat.add_comm] using preserved.symm
  · intro resultEquation
    subst result
    simpa [encodeTerm, decodeDigits_encodeDigits] using
      addDigits_canonical_reach schema
        (encodeDigits_canonical schema first).1
        (encodeDigits_canonical schema second).1

/-- Positive operational control: the full radix-two carry ripple is an
authored-rule path to eight. -/
theorem radixTwo_seven_plus_one_reaches_eight :
    MultiStep radixTwo
      (.add (encodeTerm radixTwo 7) (encodeTerm radixTwo 1))
      (encodeTerm radixTwo 8) := by
  exact (encoded_addition_graph radixTwo 7 1 8).2 rfl

/-- Negative operational control: no authored-rule path may invent seven as
the result of seven plus one. -/
theorem radixTwo_seven_plus_one_not_seven :
    ¬ MultiStep radixTwo
      (.add (encodeTerm radixTwo 7) (encodeTerm radixTwo 1))
      (encodeTerm radixTwo 7) := by
  intro path
  have impossible := (encoded_addition_graph radixTwo 7 1 7).1 path
  omega

/-- Positive ripple-carry control at radix two. -/
theorem radixTwo_addDigits_seven_one :
    addDigits radixTwo [1, 1, 1] [1] = [0, 0, 0, 1] := by
  decide

/-- Negative control: ripple carry cannot stop one digit early. -/
theorem radixTwo_addDigits_seven_one_not_truncated :
    addDigits radixTwo [1, 1, 1] [1] ≠ [0, 0, 1] := by
  decide

#print axioms incrementDigits_reach
#print axioms addDigits_reach
#print axioms decodeDigits_addDigits
#print axioms encoded_addition_graph
#print axioms radixTwo_addDigits_seven_one_not_truncated

end Mettapedia.GSLT.LanguageDef.WaltersZantemaDA
