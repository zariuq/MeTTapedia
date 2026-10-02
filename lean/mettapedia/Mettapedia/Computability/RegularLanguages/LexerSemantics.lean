import Mettapedia.Computability.RegularLanguages.Lexer

/-!
# Independent maximal-munch tokenization derivations

The derivation rules inspect independent language membership, positive prefix
lengths and authored rule priority. They do not call the executable lexer or
tokenizer. The executable tokenizer is proved to produce exactly these
finite derivations, whose results are unique.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- Independent maximal-munch semantics, including EOF and refusal positions. -/
inductive TokenizationDerivation (rules : List (LexerRule α)) :
    Nat → List α → TokenizationResult α → Prop
  | eof (offset : Nat) : TokenizationDerivation rules offset [] ⟨[], [], none⟩
  | refusal (offset : Nat) (input : List α) (nonempty : input ≠ [])
      (unrecognized : ∀ candidate, ¬ LexerCandidate rules input candidate) :
      TokenizationDerivation rules offset input ⟨[], input, some offset⟩
  | next (offset : Nat) (input : List α) (selected : LexerMatch) (tail : TokenizationResult α)
      (selection : LexerSelection rules input selected)
      (later : TokenizationDerivation rules (offset + selected.length)
        (input.drop selected.length) tail) :
      TokenizationDerivation rules offset input
        ⟨⟨selected.ruleIndex, input.take selected.length⟩ :: tail.tokens,
          tail.remaining, tail.refusedAt⟩

theorem LexerSelection.input_nonempty {rules : List (LexerRule α)} {input : List α}
    {selected : LexerMatch} (selection : LexerSelection rules input selected) : input ≠ [] := by
  intro empty
  obtain ⟨positive, rule, _, bounded, _⟩ := selection.1
  simp only [empty, List.length_nil] at bounded
  omega

/-- Determinacy follows from semantic maximality and authored priority, without running the algorithm. -/
theorem TokenizationDerivation.deterministic {rules : List (LexerRule α)} {offset : Nat}
    {input : List α} {first second : TokenizationResult α}
    (hfirst : TokenizationDerivation rules offset input first)
    (hsecond : TokenizationDerivation rules offset input second) : first = second := by
  induction hfirst generalizing second with
  | eof offset =>
    cases hsecond with
    | eof => rfl
    | refusal offset input nonempty unrecognized => exact False.elim (nonempty rfl)
    | next offset input selected tail selection later => exact False.elim (selection.input_nonempty rfl)
  | refusal offset input nonempty unrecognized =>
    cases hsecond with
    | eof => exact False.elim (nonempty rfl)
    | refusal => rfl
    | next offset input selected tail selection later =>
      exact False.elim (unrecognized selected selection.1)
  | next offset input selected tail selection later ih =>
    cases hsecond with
    | eof => exact False.elim (selection.input_nonempty rfl)
    | refusal offset input nonempty unrecognized =>
      exact False.elim (unrecognized selected selection.1)
    | next offset input other otherTail otherSelection otherLater =>
      have same := lexerSelection_unique selection otherSelection
      subst other
      have tails := ih otherLater
      subst otherTail
      rfl

/-- Every executable invocation has an independent semantic derivation. -/
theorem tokenizeFrom_correct (rules : List (LexerRule α)) (offset : Nat) (input : List α) :
    TokenizationDerivation rules offset input (tokenizeFrom rules offset input) := by
  fun_induction tokenizeFrom rules offset input with
  | case1 offset => exact .eof offset
  | case2 offset input nonempty absent =>
    exact .refusal offset input nonempty ((lexOne_none_iff rules input).mp absent)
  | case3 offset input nonempty selected found tail ih =>
    exact .next offset input selected tail ((lexOne_some_iff rules input selected).mp found) ih

/-- Execution and the independent derivation relation agree exactly. -/
theorem tokenizeFrom_eq_iff (rules : List (LexerRule α)) (offset : Nat) (input : List α)
    (result : TokenizationResult α) :
    tokenizeFrom rules offset input = result ↔ TokenizationDerivation rules offset input result := by
  constructor
  · intro same
    exact same ▸ tokenizeFrom_correct rules offset input
  · intro derivation
    exact (tokenizeFrom_correct rules offset input).deterministic derivation

theorem tokenize_correct (rules : List (LexerRule α)) (input : List α) :
    TokenizationDerivation rules 0 input (tokenize rules input) :=
  tokenizeFrom_correct rules 0 input

theorem tokenize_eq_iff (rules : List (LexerRule α)) (input : List α) (result : TokenizationResult α) :
    tokenize rules input = result ↔ TokenizationDerivation rules 0 input result :=
  tokenizeFrom_eq_iff rules 0 input result

/-- An independent derivation preserves every original input symbol in order. -/
theorem TokenizationDerivation.reconstruct {rules : List (LexerRule α)} {offset : Nat}
    {input : List α} {result : TokenizationResult α}
    (derivation : TokenizationDerivation rules offset input result) :
    result.tokens.flatMap LexerToken.text ++ result.remaining = input := by
  induction derivation with
  | eof => rfl
  | refusal => rfl
  | next offset input selected tail selection later ih =>
    change (input.take selected.length ++ tail.tokens.flatMap LexerToken.text) ++ tail.remaining = input
    rw [List.append_assoc, ih, List.take_append_drop]

/-- Token words and their authored rule positions are justified by independent language membership. -/
theorem TokenizationDerivation.tokens_valid {rules : List (LexerRule α)} {offset : Nat}
    {input : List α} {result : TokenizationResult α}
    (derivation : TokenizationDerivation rules offset input result) :
    ∀ token ∈ result.tokens, token.Valid rules := by
  induction derivation with
  | eof => simp
  | refusal => simp
  | next offset input selected tail selection later ih =>
    intro token member
    change token ∈ ⟨selected.ruleIndex, input.take selected.length⟩ :: tail.tokens at member
    rcases List.mem_cons.mp member with rfl | member
    · obtain ⟨positive, rule, atIndex, bounded, accepted⟩ := selection.1
      refine ⟨?_, rule, atIndex, accepted⟩
      change 0 < (input.take selected.length).length
      rw [List.length_take, Nat.min_eq_left bounded]
      exact positive
    · exact ih token member

namespace LexerSemanticsControls

/-- The independent derivation selects the earlier keyword on an equal-length tie. -/
theorem keyword_priority_derivation :
    TokenizationDerivation [LexerRule.literal "if".toList, asciiIdentifierRule] 0 "if".toList
      ⟨[⟨0, "if".toList⟩], [], none⟩ :=
  .next 0 "if".toList ⟨0, 2⟩ ⟨[], [], none⟩
    ((lexOne_some_iff _ _ _).mp LexerControls.keyword_identifier_tie) (.eof 2)

/-- The identifier token has the same text, but violates authored priority. -/
theorem wrong_priority_not_derivable :
    ¬ TokenizationDerivation [LexerRule.literal "if".toList, asciiIdentifierRule] 0 "if".toList
      ⟨[⟨1, "if".toList⟩], [], none⟩ := by
  intro wrong
  have same := keyword_priority_derivation.deterministic wrong
  cases same

/-- Membership and reconstruction alone cannot certify maximal-munch tokenization. -/
theorem membership_reconstruction_not_sufficient :
    (∀ token ∈ ([⟨1, "if".toList⟩] : List (LexerToken Char)),
      token.Valid [LexerRule.literal "if".toList, asciiIdentifierRule]) ∧
    ([⟨1, "if".toList⟩] : List (LexerToken Char)).flatMap LexerToken.text = "if".toList ∧
    ¬ TokenizationDerivation [LexerRule.literal "if".toList, asciiIdentifierRule] 0 "if".toList
      ⟨[⟨1, "if".toList⟩], [], none⟩ := by
  refine ⟨?_, by simp, wrong_priority_not_derivable⟩
  intro token member
  have same : token = ⟨1, "if".toList⟩ := by simpa only [List.mem_singleton] using member
  subst token
  refine ⟨by decide, asciiIdentifierRule, rfl, ?_⟩
  change "if".toList ≠ [] ∧ ∀ c ∈ "if".toList, 'a' ≤ c ∧ c ≤ 'z'
  decide

end LexerSemanticsControls

end Mettapedia.Computability.RegularLanguages
