import Mettapedia.GSLT.LanguageDef.WaltersZantemaDA

/-!
# Contextual semantics of Walters--Zantema DA

The generated `LanguageDef` contains exactly the premise-free root rules from
the paper.  This file gives those roots their standard term-rewriting meaning:
substitution followed by closure under the DA constructors.  Administrative
congruence rules used by an executable generic engine belong to a later
realization and are not counted as paper rules.
-/

namespace Mettapedia.GSLT.LanguageDef.WaltersZantemaDA

namespace SemanticTerm

/-- Simultaneous substitution of authored DA metavariables. -/
def instantiate (substitution : String → SemanticTerm) : SemanticTerm → SemanticTerm
  | .variable name => substitution name
  | .empty => .empty
  | .digit index body => .digit index (instantiate substitution body)
  | .add left right => .add (instantiate substitution left)
      (instantiate substitution right)
  | .mul left right => .mul (instantiate substitution left)
      (instantiate substitution right)
  | .succ body => .succ (instantiate substitution body)
  | .star index body => .star index (instantiate substitution body)

@[simp] theorem instantiate_semanticCarryApply (schema : Schema)
    (first second : Nat) (substitution : String → SemanticTerm)
    (body : SemanticTerm) :
    (semanticCarryApply schema first second body).instantiate substitution =
      semanticCarryApply schema first second (body.instantiate substitution) := by
  by_cases carry : schema.radix ≤ first + second
  · simp only [semanticCarryApply, carry, if_pos]
    rfl
  · simp only [semanticCarryApply, carry]
    rfl

/-- Denotation commutes with simultaneous substitution. -/
theorem denote_instantiate (schema : Schema) (valuation : String → Nat)
    (substitution : String → SemanticTerm) (term : SemanticTerm) :
    (term.instantiate substitution).denote schema valuation =
      term.denote schema
        (fun name => (substitution name).denote schema valuation) := by
  induction term <;> simp [instantiate, denote, *]

end SemanticTerm

/-- One instantiated application of a generated paper rule at the root. -/
inductive RootStep (schema : Schema) : SemanticTerm → SemanticTerm → Prop where
  | apply {authored : AuthoredRule schema}
      (member : authored ∈ authoredRules schema)
      (substitution : String → SemanticTerm) :
      RootStep schema
        (authored.left.instantiate substitution)
        (authored.right.instantiate substitution)

namespace RootStep

/-- Every instantiated root contraction preserves natural-number denotation. -/
theorem sound {schema : Schema} {source target : SemanticTerm}
    (step : RootStep schema source target) (valuation : String → Nat) :
    source.denote schema valuation = target.denote schema valuation := by
  cases step with
  | apply member substitution =>
      rw [SemanticTerm.denote_instantiate, SemanticTerm.denote_instantiate]
      exact authoredRules_sound schema _ member
        (fun name => (substitution name).denote schema valuation)

private theorem authoredRule1_member (schema : Schema) :
    authoredRule1 schema ∈ authoredRules schema := by
  simp [authoredRules]

private theorem authoredRule2_member (schema : Schema) :
    authoredRule2 schema ∈ authoredRules schema := by
  simp only [authoredRules, List.mem_append]
  exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)

private theorem authoredRule3_member (schema : Schema) :
    authoredRule3 schema ∈ authoredRules schema := by
  simp only [authoredRules, List.mem_append]
  exact Or.inl
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

private theorem authoredRule4_member (schema : Schema) {first second : Nat}
    (firstDigit : first < schema.radix)
    (secondDigit : second < schema.radix) :
    authoredRule4 schema first second ∈ authoredRules schema := by
  have familyMember :
      authoredRule4 schema first second ∈ authoredRule4Family schema := by
    rw [authoredRule4Family, List.mem_flatMap]
    refine ⟨first, (Schema.mem_digits_iff schema first).mpr firstDigit, ?_⟩
    rw [List.mem_map]
    exact ⟨second, (Schema.mem_digits_iff schema second).mpr secondDigit, rfl⟩
  simp only [authoredRules, List.mem_append]
  exact Or.inr (Or.inl familyMember)

private theorem authoredRule5_member (schema : Schema) :
    authoredRule5 schema ∈ authoredRules schema := by
  simp [authoredRules]

private theorem authoredRule6_member (schema : Schema) {index : Nat}
    (indexDigit : index < schema.radix) :
    authoredRule6 schema index ∈ authoredRules schema := by
  have familyMember :
      authoredRule6 schema index ∈ authoredRule6Family schema := by
    rw [authoredRule6Family, List.mem_map]
    exact ⟨index, (Schema.mem_digits_iff schema index).mpr indexDigit, rfl⟩
  simp only [authoredRules, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inl familyMember)))

private theorem authoredRule7_member (schema : Schema) :
    authoredRule7 schema ∈ authoredRules schema := by
  simp only [authoredRules, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl List.mem_cons_self))))

private theorem authoredRule8_member (schema : Schema) {index : Nat}
    (indexDigit : index < schema.radix) :
    authoredRule8 schema index ∈ authoredRules schema := by
  have familyMember :
      authoredRule8 schema index ∈ authoredRule8Family schema := by
    rw [authoredRule8Family, List.mem_map]
    exact ⟨index, (Schema.mem_digits_iff schema index).mpr indexDigit, rfl⟩
  simp only [authoredRules, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl familyMember)))))

private theorem authoredRule9_member (schema : Schema) {index : Nat}
    (indexDigit : index < schema.radix) :
    authoredRule9 schema index ∈ authoredRules schema := by
  have familyMember :
      authoredRule9 schema index ∈ authoredRule9Family schema := by
    rw [authoredRule9Family, List.mem_map]
    exact ⟨index, (Schema.mem_digits_iff schema index).mpr indexDigit, rfl⟩
  simp only [authoredRules, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl familyMember))))))

private theorem authoredRule10_member (schema : Schema) {first second : Nat}
    (firstDigit : first < schema.radix)
    (secondDigit : second < schema.radix) :
    authoredRule10 schema first second ∈ authoredRules schema := by
  have familyMember :
      authoredRule10 schema first second ∈ authoredRule10Family schema := by
    rw [authoredRule10Family, List.mem_flatMap]
    refine ⟨first, (Schema.mem_digits_iff schema first).mpr firstDigit, ?_⟩
    rw [List.mem_map]
    exact ⟨second, (Schema.mem_digits_iff schema second).mpr secondDigit, rfl⟩
  simp only [authoredRules, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr familyMember))))))

private def substituteOne (term : SemanticTerm) : String → SemanticTerm :=
  fun name => if name = "x" then term else .empty

private def substituteTwo (first second : SemanticTerm) :
    String → SemanticTerm :=
  fun name => if name = "x" then first else if name = "y" then second else .empty

private theorem instantiate_semanticDigitProductNumeral
    (schema : Schema) (first second : Nat)
    (substitution : String → SemanticTerm) :
    (semanticDigitProductNumeral schema first second).instantiate substitution =
      semanticDigitProductNumeral schema first second := by
  unfold semanticDigitProductNumeral
  by_cases productZero : first * second = 0
  · simp [productZero, SemanticTerm.instantiate]
  · simp only [productZero, if_false]
    by_cases highZero : first * second / schema.radix = 0
    · simp [highZero, SemanticTerm.instantiate]
    · simp [highZero, SemanticTerm.instantiate]

/-- Direct root contraction for paper rule 1. -/
theorem rule1 (schema : Schema) :
    RootStep schema (.digit 0 .empty) .empty := by
  simpa [authoredRule1, SemanticTerm.instantiate] using
    (RootStep.apply (authoredRule1_member schema) (fun _ => .empty))

/-- Direct root contraction for paper rule 2. -/
theorem rule2 (schema : Schema) (term : SemanticTerm) :
    RootStep schema (.add .empty term) term := by
  simpa [authoredRule2, substituteOne, SemanticTerm.instantiate] using
    (RootStep.apply (authoredRule2_member schema) (substituteOne term))

/-- Direct root contraction for paper rule 3. -/
theorem rule3 (schema : Schema) (term : SemanticTerm) :
    RootStep schema (.add term .empty) term := by
  simpa [authoredRule3, substituteOne, SemanticTerm.instantiate] using
    (RootStep.apply (authoredRule3_member schema) (substituteOne term))

/-- Direct root contraction for one finite instance of paper rule 4. -/
theorem rule4 (schema : Schema) {first second : Nat}
    (firstDigit : first < schema.radix)
    (secondDigit : second < schema.radix)
    (left right : SemanticTerm) :
    RootStep schema
      (.add (.digit first left) (.digit second right))
      (.digit (digitSum schema first second)
        (semanticCarryApply schema first second (.add left right))) := by
  simpa [authoredRule4, substituteTwo, SemanticTerm.instantiate] using
    (RootStep.apply
      (authoredRule4_member schema firstDigit secondDigit)
      (substituteTwo left right))

/-- Direct root contraction for paper rule 5. -/
theorem rule5 (schema : Schema) (right : SemanticTerm) :
    RootStep schema (.mul .empty right) .empty := by
  simpa [authoredRule5, substituteOne, SemanticTerm.instantiate] using
    (RootStep.apply (authoredRule5_member schema) (substituteOne right))

/-- Direct root contraction for one finite instance of paper rule 6. -/
theorem rule6 (schema : Schema) {index : Nat}
    (indexDigit : index < schema.radix) (left right : SemanticTerm) :
    RootStep schema (.mul (.digit index left) right)
      (.add (.digit 0 (.mul left right)) (.star index right)) := by
  simpa [authoredRule6, substituteTwo, SemanticTerm.instantiate] using
    (RootStep.apply (authoredRule6_member schema indexDigit)
      (substituteTwo left right))

/-- Direct root contraction for paper rule 7. -/
theorem rule7 (schema : Schema) :
    RootStep schema (.succ .empty) (.digit 1 .empty) := by
  simpa [authoredRule7, SemanticTerm.instantiate] using
    (RootStep.apply (authoredRule7_member schema) (fun _ => .empty))

/-- Direct root contraction for one finite instance of paper rule 8. -/
theorem rule8 (schema : Schema) {index : Nat}
    (indexDigit : index < schema.radix) (body : SemanticTerm) :
    RootStep schema (.succ (.digit index body))
      (.digit (digitSum schema 1 index)
        (semanticCarryApply schema 1 index body)) := by
  simpa [authoredRule8, substituteOne, SemanticTerm.instantiate] using
    (RootStep.apply (authoredRule8_member schema indexDigit)
      (substituteOne body))

/-- Direct root contraction for paper rule 9. -/
theorem rule9 (schema : Schema) {index : Nat}
    (indexDigit : index < schema.radix) :
    RootStep schema (.star index .empty) .empty := by
  simpa [authoredRule9, SemanticTerm.instantiate] using
    (RootStep.apply (authoredRule9_member schema indexDigit) (fun _ => .empty))

/-- Direct root contraction for one finite instance of paper rule 10. -/
theorem rule10 (schema : Schema) {first second : Nat}
    (firstDigit : first < schema.radix)
    (secondDigit : second < schema.radix) (body : SemanticTerm) :
    RootStep schema (.star first (.digit second body))
      (.add (.digit 0 (.star first body))
        (semanticDigitProductNumeral schema first second)) := by
  have applied := RootStep.apply
    (authoredRule10_member schema firstDigit secondDigit)
    (substituteOne body)
  simpa [authoredRule10, substituteOne, SemanticTerm.instantiate,
    instantiate_semanticDigitProductNumeral] using applied

end RootStep

/-- Standard contextual closure of the DA root contractions.  The constructors
are exactly the DA signature, so no unrelated `Pattern` shape acquires
reduction authority. -/
inductive Step (schema : Schema) : SemanticTerm → SemanticTerm → Prop where
  | root {source target} : RootStep schema source target → Step schema source target
  | digit {source target} (index : Nat) :
      Step schema source target →
      Step schema (.digit index source) (.digit index target)
  | addLeft {source target right} :
      Step schema source target →
      Step schema (.add source right) (.add target right)
  | addRight {left source target} :
      Step schema source target →
      Step schema (.add left source) (.add left target)
  | mulLeft {source target right} :
      Step schema source target →
      Step schema (.mul source right) (.mul target right)
  | mulRight {left source target} :
      Step schema source target →
      Step schema (.mul left source) (.mul left target)
  | succ {source target} :
      Step schema source target →
      Step schema (.succ source) (.succ target)
  | star {source target} (index : Nat) :
      Step schema source target →
      Step schema (.star index source) (.star index target)

namespace Step

/-- Contextual closure cannot invent a different natural-number denotation. -/
theorem sound {schema : Schema} {source target : SemanticTerm}
    (step : Step schema source target) (valuation : String → Nat) :
    source.denote schema valuation = target.denote schema valuation := by
  induction step with
  | root rootStep => exact rootStep.sound valuation
  | digit index _ inductionHypothesis =>
      simp only [SemanticTerm.denote]
      rw [inductionHypothesis]
  | addLeft _ inductionHypothesis =>
      simp only [SemanticTerm.denote]
      rw [inductionHypothesis]
  | addRight _ inductionHypothesis =>
      simp only [SemanticTerm.denote]
      rw [inductionHypothesis]
  | mulLeft _ inductionHypothesis =>
      simp only [SemanticTerm.denote]
      rw [inductionHypothesis]
  | mulRight _ inductionHypothesis =>
      simp only [SemanticTerm.denote]
      rw [inductionHypothesis]
  | succ _ inductionHypothesis =>
      simp only [SemanticTerm.denote]
      rw [inductionHypothesis]
  | star index _ inductionHypothesis =>
      simp only [SemanticTerm.denote]
      rw [inductionHypothesis]

end Step

/-- Zero or more contextual DA contractions. -/
abbrev MultiStep (schema : Schema) := Relation.ReflTransGen (Step schema)

/-- Denotation is invariant along every finite DA reduction. -/
theorem multiStep_sound {schema : Schema} {source target : SemanticTerm}
    (steps : MultiStep schema source target) (valuation : String → Nat) :
    source.denote schema valuation = target.denote schema valuation := by
  induction steps with
  | refl => rfl
  | tail previous finalStep inductionHypothesis =>
      exact inductionHypothesis.trans (finalStep.sound valuation)

/-! ## Positive and negative semantic controls -/

private def emptySubstitution : String → SemanticTerm :=
  fun _ => .empty

/-- The generated carry rule really contracts `1 + 1` to binary `10`. -/
theorem radixTwo_one_plus_one_root :
    RootStep radixTwo
      (.add (.digit 1 .empty) (.digit 1 .empty))
      (.digit 0 (.succ (.add .empty .empty))) := by
  have familyMember :
      authoredRule4 radixTwo 1 1 ∈ authoredRule4Family radixTwo := by
    decide
  have member : authoredRule4 radixTwo 1 1 ∈ authoredRules radixTwo := by
    simp only [authoredRules, List.mem_append]
    exact Or.inr (Or.inl familyMember)
  simpa [authoredRule4, emptySubstitution, SemanticTerm.instantiate,
    semanticCarryApply, digitSum, radixTwo] using
    (RootStep.apply member emptySubstitution)

/-- A dropped-carry target is impossible for the same selected paper rule. -/
theorem radixTwo_one_plus_one_not_dropped_by_selected_rule :
    (authoredRule4 radixTwo 1 1).right.instantiate emptySubstitution ≠
      .digit 0 (.add .empty .empty) := by
  decide

#print axioms SemanticTerm.denote_instantiate
#print axioms RootStep.sound
#print axioms Step.sound
#print axioms multiStep_sound
#print axioms radixTwo_one_plus_one_root
#print axioms radixTwo_one_plus_one_not_dropped_by_selected_rule

end Mettapedia.GSLT.LanguageDef.WaltersZantemaDA
