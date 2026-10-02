import Mettapedia.Computability.RegularLanguages.Search
import Mathlib.Data.List.Enum
import Mathlib.Tactic.SplitIfs

/-!
# Maximal-munch lexing with authored rule priority

Each executable rule is related to an independently specified language.
Selection considers each rule's longest prefix, excludes empty prefixes,
and prefers longer options before earlier rule positions.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- An executable membership test for an independently specified language. -/
structure LexerRule (α : Type u) where
  language : Language α
  accepts : List α → Bool
  accepts_correct : ∀ word, accepts word = true ↔ word ∈ language

/-- The authored rule position and the positive length selected for one token. -/
structure LexerMatch where
  ruleIndex : Nat
  length : Nat
  deriving DecidableEq, Repr

/-- Membership decisions are obtained from the rule's executable test. -/
@[instance_reducible]
def LexerRule.membershipDecision (rule : LexerRule α) :
    DecidablePred (· ∈ rule.language) := fun word =>
  if accepted : rule.accepts word = true then
    isTrue ((rule.accepts_correct word).mp accepted)
  else isFalse (fun member => accepted ((rule.accepts_correct word).mpr member))

/-- A greater match length wins; equal lengths prefer the earlier rule position. -/
def LexerMatch.Dominates (selected candidate : LexerMatch) : Prop :=
  candidate.length ≤ selected.length ∧
    (candidate.length = selected.length → selected.ruleIndex ≤ candidate.ruleIndex)

private theorem dominates_refl (candidate : LexerMatch) : candidate.Dominates candidate :=
  ⟨le_rfl, fun _ => le_rfl⟩

private theorem dominates_trans {a b c : LexerMatch}
    (ab : a.Dominates b) (bc : b.Dominates c) : a.Dominates c := by
  refine ⟨le_trans bc.1 ab.1, ?_⟩
  intro same
  have abLength := ab.1
  have bcLength := bc.1
  have ba : b.length = a.length := by omega
  have cb : c.length = b.length := by omega
  exact le_trans (ab.2 ba) (bc.2 cb)

private theorem dominates_antisymm {a b : LexerMatch}
    (ab : a.Dominates b) (ba : b.Dominates a) : a = b := by
  have abLength := ab.1
  have baLength := ba.1
  have lengths : a.length = b.length := by omega
  have indices : a.ruleIndex = b.ruleIndex := by
    have := ab.2 lengths.symm
    have := ba.2 lengths
    omega
  cases a
  cases b
  simp_all

private def chooseMatch (a b : LexerMatch) : LexerMatch :=
  if a.length < b.length then b
  else if b.length < a.length then a
  else if a.ruleIndex ≤ b.ruleIndex then a else b

private theorem chooseMatch_mem (a b : LexerMatch) : chooseMatch a b = a ∨ chooseMatch a b = b := by
  unfold chooseMatch
  split_ifs <;> simp

private theorem chooseMatch_left (a b : LexerMatch) : (chooseMatch a b).Dominates a := by
  unfold chooseMatch LexerMatch.Dominates
  split_ifs <;> constructor <;> (try intro equal) <;> omega

private theorem chooseMatch_right (a b : LexerMatch) : (chooseMatch a b).Dominates b := by
  unfold chooseMatch LexerMatch.Dominates
  split_ifs <;> constructor <;> (try intro equal) <;> omega

private def bestMatch : List LexerMatch → Option LexerMatch
  | [] => none
  | candidate :: rest =>
    match bestMatch rest with
    | none => some candidate
    | some later => some (chooseMatch candidate later)

private theorem bestMatch_spec (options : List LexerMatch) :
    (∃ selected, bestMatch options = some selected ∧ selected ∈ options ∧
      ∀ candidate ∈ options, selected.Dominates candidate) ∨
    (options = [] ∧ bestMatch options = none) := by
  induction options with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | cons candidate rest ih =>
    rcases ih with ⟨later, result, member, largest⟩ | ⟨rfl, result⟩
    · refine Or.inl ⟨chooseMatch candidate later, by simp only [bestMatch, result], ?_, ?_⟩
      · rcases chooseMatch_mem candidate later with same | same
        · simp [same]
        · simp [same, member]
      · intro other accepted
        rcases List.mem_cons.mp accepted with rfl | accepted
        · exact chooseMatch_left other later
        · exact dominates_trans (chooseMatch_right candidate later) (largest other accepted)
    · exact Or.inl ⟨candidate, rfl, by simp, by
        intro other accepted
        have : other = candidate := by simpa using accepted
        subst other
        exact dominates_refl candidate⟩

private theorem bestMatch_some_iff (options : List LexerMatch) (selected : LexerMatch) :
    bestMatch options = some selected ↔ selected ∈ options ∧
      ∀ candidate ∈ options, selected.Dominates candidate := by
  rcases bestMatch_spec options with ⟨best, result, member, largest⟩ | ⟨rfl, result⟩
  · rw [result, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨member, largest⟩
    · rintro ⟨selectedMember, selectedLargest⟩
      exact dominates_antisymm (largest selected selectedMember) (selectedLargest best member)
  · simp [bestMatch]

private theorem bestMatch_none_iff (options : List LexerMatch) :
    bestMatch options = none ↔ options = [] := by
  rcases bestMatch_spec options with ⟨best, result, member, largest⟩ | ⟨rfl, result⟩
  · rw [result]
    simp only [Option.some_ne_none, false_iff]
    intro empty
    simp [empty] at member
  · simp [bestMatch]

/-- The positive longest prefix for one rule at its authored position. -/
def ruleCandidate (rule : LexerRule α) (input : List α) (index : Nat) : Option LexerMatch :=
  letI := rule.membershipDecision
  (longestPrefix rule.language input).bind fun n =>
    if n = 0 then none else some ⟨index, n⟩

theorem ruleCandidate_some_iff (rule : LexerRule α) (input : List α) (index : Nat)
    (selected : LexerMatch) :
    ruleCandidate rule input index = some selected ↔
      selected.ruleIndex = index ∧ 0 < selected.length ∧
        PrefixMatch rule.language input selected.length ∧
        ∀ n, PrefixMatch rule.language input n → n ≤ selected.length := by
  let := rule.membershipDecision
  unfold ruleCandidate
  constructor
  · intro selectedResult
    cases result : longestPrefix rule.language input with
    | none =>
      simp only [result, Option.bind_none] at selectedResult
      contradiction
    | some n =>
      by_cases empty : n = 0
      · simp only [result, Option.bind_some, if_pos empty] at selectedResult
        contradiction
      · simp only [result, Option.bind_some, if_neg empty, Option.some.injEq] at selectedResult
        cases selectedResult
        obtain ⟨matched, largest⟩ := (longestPrefix_some_iff rule.language input n).mp result
        exact ⟨rfl, by change 0 < n; omega, matched, largest⟩
  · rintro ⟨indexEq, positive, matched, largest⟩
    have result := (longestPrefix_some_iff rule.language input selected.length).mpr ⟨matched, largest⟩
    rw [result]
    simp only [Option.bind_some, if_neg (by omega : selected.length ≠ 0), Option.some.injEq]
    cases selected
    simp_all

theorem ruleCandidate_complete (rule : LexerRule α) (input : List α) (index n : Nat)
    (positive : 0 < n) (matched : PrefixMatch rule.language input n) :
    ∃ selected, ruleCandidate rule input index = some selected ∧
      n ≤ selected.length ∧ selected.ruleIndex = index := by
  let := rule.membershipDecision
  cases result : longestPrefix rule.language input with
  | none => exact False.elim (((longestPrefix_none_iff rule.language input).mp result) n matched)
  | some length =>
    obtain ⟨accepted, largest⟩ := (longestPrefix_some_iff rule.language input length).mp result
    have bound := largest n matched
    refine ⟨⟨index, length⟩, ?_, bound, rfl⟩
    exact (ruleCandidate_some_iff rule input index _).mpr ⟨rfl, by change 0 < length; omega, accepted, largest⟩

/-- All per-rule positive maxima, with positions from the authored rule list. -/
def lexerCandidates (rules : List (LexerRule α)) (input : List α) : List LexerMatch :=
  rules.zipIdx.filterMap fun pair => ruleCandidate pair.1 input pair.2

theorem mem_lexerCandidates_iff (rules : List (LexerRule α)) (input : List α)
    (selected : LexerMatch) :
    selected ∈ lexerCandidates rules input ↔
      ∃ rule, rules[selected.ruleIndex]? = some rule ∧
        0 < selected.length ∧ PrefixMatch rule.language input selected.length ∧
          ∀ n, PrefixMatch rule.language input n → n ≤ selected.length := by
  simp only [lexerCandidates, List.mem_filterMap]
  constructor
  · rintro ⟨⟨rule, index⟩, atIndex, result⟩
    obtain ⟨rfl, positive, matched, largest⟩ := (ruleCandidate_some_iff rule input index selected).mp result
    exact ⟨rule, List.mem_zipIdx_iff_getElem?.mp atIndex, positive, matched, largest⟩
  · rintro ⟨rule, atIndex, positive, matched, largest⟩
    exact ⟨(rule, selected.ruleIndex), List.mem_zipIdx_iff_getElem?.mpr atIndex,
      (ruleCandidate_some_iff rule input selected.ruleIndex selected).mpr
        ⟨rfl, positive, matched, largest⟩⟩

/-- A positive accepted prefix at a particular authored rule position. -/
def LexerCandidate (rules : List (LexerRule α)) (input : List α) (candidate : LexerMatch) : Prop :=
  0 < candidate.length ∧ ∃ rule, rules[candidate.ruleIndex]? = some rule ∧
    PrefixMatch rule.language input candidate.length

/-- Longest positive match, with the earliest authored position among ties. -/
def LexerSelection (rules : List (LexerRule α)) (input : List α) (selected : LexerMatch) : Prop :=
  LexerCandidate rules input selected ∧
    ∀ candidate, LexerCandidate rules input candidate → selected.Dominates candidate

/-- Select the longest positive accepted prefix, breaking ties by rule position. -/
def lexOne (rules : List (LexerRule α)) (input : List α) : Option LexerMatch :=
  bestMatch (lexerCandidates rules input)

private theorem lexerCandidate_of_mem {rules : List (LexerRule α)} {input : List α}
    {candidate : LexerMatch} (member : candidate ∈ lexerCandidates rules input) :
    LexerCandidate rules input candidate := by
  obtain ⟨rule, atIndex, positive, matched, _⟩ := (mem_lexerCandidates_iff rules input candidate).mp member
  exact ⟨positive, rule, atIndex, matched⟩

private theorem lexerCandidates_complete {rules : List (LexerRule α)} {input : List α}
    {candidate : LexerMatch} (accepted : LexerCandidate rules input candidate) :
    ∃ larger, larger ∈ lexerCandidates rules input ∧ larger.Dominates candidate := by
  obtain ⟨positive, rule, atIndex, matched⟩ := accepted
  obtain ⟨larger, result, bound, sameIndex⟩ := ruleCandidate_complete rule input
    candidate.ruleIndex candidate.length positive matched
  obtain ⟨_, largerPositive, largerMatched, largest⟩ :=
    (ruleCandidate_some_iff rule input candidate.ruleIndex larger).mp result
  refine ⟨larger, (mem_lexerCandidates_iff rules input larger).mpr
    ⟨rule, sameIndex ▸ atIndex, largerPositive, largerMatched, largest⟩, bound, ?_⟩
  intro _
  omega

theorem lexOne_some_iff (rules : List (LexerRule α)) (input : List α)
    (selected : LexerMatch) : lexOne rules input = some selected ↔ LexerSelection rules input selected := by
  rw [lexOne, bestMatch_some_iff]
  constructor
  · rintro ⟨member, largest⟩
    refine ⟨lexerCandidate_of_mem member, ?_⟩
    intro candidate accepted
    obtain ⟨larger, member, dominates⟩ := lexerCandidates_complete accepted
    exact dominates_trans (largest larger member) dominates
  · rintro ⟨accepted, largest⟩
    obtain ⟨larger, member, dominates⟩ := lexerCandidates_complete accepted
    have same := dominates_antisymm (largest larger (lexerCandidate_of_mem member)) dominates
    subst larger
    exact ⟨member, fun candidate h => largest candidate (lexerCandidate_of_mem h)⟩

theorem lexOne_none_iff (rules : List (LexerRule α)) (input : List α) :
    lexOne rules input = none ↔ ∀ candidate, ¬ LexerCandidate rules input candidate := by
  rw [lexOne, bestMatch_none_iff]
  constructor
  · intro empty candidate accepted
    obtain ⟨larger, member, _⟩ := lexerCandidates_complete accepted
    simp [empty] at member
  · intro absent
    cases candidates : lexerCandidates rules input with
    | nil => rfl
    | cons candidate rest =>
      have member : candidate ∈ lexerCandidates rules input := by
        rw [candidates]
        exact List.mem_cons_self
      exact False.elim (absent candidate (lexerCandidate_of_mem member))

theorem lexOne_complete (rules : List (LexerRule α)) (input : List α)
    (candidate : LexerMatch) (accepted : LexerCandidate rules input candidate) :
    ∃ selected, lexOne rules input = some selected ∧ selected.Dominates candidate := by
  cases result : lexOne rules input with
  | none => exact False.elim (((lexOne_none_iff rules input).mp result) candidate accepted)
  | some selected => exact ⟨selected, rfl, ((lexOne_some_iff rules input selected).mp result).2 candidate accepted⟩

theorem lexerSelection_unique {rules : List (LexerRule α)} {input : List α}
    {first second : LexerMatch} (hfirst : LexerSelection rules input first)
    (hsecond : LexerSelection rules input second) : first = second :=
  dominates_antisymm (hfirst.2 second hsecond.1) (hsecond.2 first hfirst.1)

theorem lexOne_positive {rules : List (LexerRule α)} {input : List α} {selected : LexerMatch}
    (result : lexOne rules input = some selected) : 0 < selected.length :=
  ((lexOne_some_iff rules input selected).mp result).1.1

theorem lexOne_bound {rules : List (LexerRule α)} {input : List α} {selected : LexerMatch}
    (result : lexOne rules input = some selected) : selected.length ≤ input.length := by
  obtain ⟨_, rule, _, matched⟩ := ((lexOne_some_iff rules input selected).mp result).1
  exact matched.1

theorem lexOne_membership {rules : List (LexerRule α)} {input : List α} {selected : LexerMatch}
    (result : lexOne rules input = some selected) :
    ∃ rule, rules[selected.ruleIndex]? = some rule ∧ input.take selected.length ∈ rule.language := by
  obtain ⟨_, rule, atIndex, matched⟩ := ((lexOne_some_iff rules input selected).mp result).1
  exact ⟨rule, atIndex, matched.2⟩

theorem lexOne_maximal {rules : List (LexerRule α)} {input : List α} {selected candidate : LexerMatch}
    (result : lexOne rules input = some selected) (accepted : LexerCandidate rules input candidate) :
    candidate.length ≤ selected.length :=
  (((lexOne_some_iff rules input selected).mp result).2 candidate accepted).1

theorem lexOne_priority {rules : List (LexerRule α)} {input : List α} {selected candidate : LexerMatch}
    (result : lexOne rules input = some selected) (accepted : LexerCandidate rules input candidate)
    (sameLength : candidate.length = selected.length) : selected.ruleIndex ≤ candidate.ruleIndex :=
  (((lexOne_some_iff rules input selected).mp result).2 candidate accepted).2 sameLength

theorem lexOne_progress {rules : List (LexerRule α)} {input : List α} {selected : LexerMatch}
    (result : lexOne rules input = some selected) : (input.drop selected.length).length < input.length := by
  have positive := lexOne_positive result
  have bound := lexOne_bound result
  simp only [List.length_drop]
  omega

theorem lexOne_ruleIndex_bound {rules : List (LexerRule α)} {input : List α} {selected : LexerMatch}
    (result : lexOne rules input = some selected) : selected.ruleIndex < rules.length := by
  obtain ⟨rule, atIndex, _⟩ := lexOne_membership result
  exact (List.getElem?_eq_some_iff.mp atIndex).1

/-- A token records both its authored rule position and the original matched word. -/
structure LexerToken (α : Type u) where
  ruleIndex : Nat
  text : List α
  deriving DecidableEq, Repr

/-- Tokens produced so far, the unconsumed input, and the first refusal position.
A missing refusal position means that the entire input was tokenized. -/
structure TokenizationResult (α : Type u) where
  tokens : List (LexerToken α)
  remaining : List α
  refusedAt : Option Nat
  deriving DecidableEq, Repr

/-- Successful tokens are nonempty words in the language of their authored rule. -/
def LexerToken.Valid (rules : List (LexerRule α)) (token : LexerToken α) : Prop :=
  0 < token.text.length ∧ ∃ rule, rules[token.ruleIndex]? = some rule ∧ token.text ∈ rule.language

/-- Tokenize from an absolute input position. A refusal leaves the unmatched suffix intact. -/
def tokenizeFrom (rules : List (LexerRule α)) (offset : Nat) (input : List α) : TokenizationResult α :=
  if input = [] then ⟨[], [], none⟩
  else match _found : lexOne rules input with
    | none => ⟨[], input, some offset⟩
    | some selected =>
      let tail := tokenizeFrom rules (offset + selected.length) (input.drop selected.length)
      ⟨⟨selected.ruleIndex, input.take selected.length⟩ :: tail.tokens, tail.remaining, tail.refusedAt⟩
termination_by input.length
decreasing_by exact lexOne_progress _found


theorem tokenizeFrom_nil (rules : List (LexerRule α)) (offset : Nat) :
    tokenizeFrom rules offset [] = ⟨[], [], none⟩ := by
  rw [tokenizeFrom]
  rfl

theorem tokenizeFrom_refused {rules : List (LexerRule α)} {offset : Nat} {input : List α}
    (nonempty : input ≠ []) (absent : lexOne rules input = none) :
    tokenizeFrom rules offset input = ⟨[], input, some offset⟩ := by
  rw [tokenizeFrom, if_neg nonempty, absent]

theorem tokenizeFrom_next {rules : List (LexerRule α)} {offset : Nat} {input : List α}
    {selected : LexerMatch} (found : lexOne rules input = some selected) :
    tokenizeFrom rules offset input =
      let tail := tokenizeFrom rules (offset + selected.length) (input.drop selected.length)
      ⟨⟨selected.ruleIndex, input.take selected.length⟩ :: tail.tokens, tail.remaining, tail.refusedAt⟩ := by
  have nonempty : input ≠ [] := by
    intro empty
    have positive := lexOne_positive found
    have bound := lexOne_bound found
    simp only [empty, List.length_nil] at bound
    omega
  rw [tokenizeFrom, if_neg nonempty, found]

/-- Total maximal-munch tokenization, with an absolute refusal position on failure. -/
def tokenize (rules : List (LexerRule α)) (input : List α) : TokenizationResult α :=
  tokenizeFrom rules 0 input

theorem lexOne_token_valid {rules : List (LexerRule α)} {input : List α} {selected : LexerMatch}
    (found : lexOne rules input = some selected) :
    LexerToken.Valid rules ⟨selected.ruleIndex, input.take selected.length⟩ := by
  obtain ⟨rule, atIndex, matched⟩ := lexOne_membership found
  refine ⟨?_, rule, atIndex, matched⟩
  change 0 < (input.take selected.length).length
  rw [List.length_take, Nat.min_eq_left (lexOne_bound found)]
  exact lexOne_positive found

theorem tokenizeFrom_reconstruct (rules : List (LexerRule α)) (offset : Nat) (input : List α) :
    (tokenizeFrom rules offset input).tokens.flatMap LexerToken.text ++
      (tokenizeFrom rules offset input).remaining = input := by
  fun_induction tokenizeFrom rules offset input with
  | case1 offset => rfl
  | case2 offset input nonempty absent => rfl
  | case3 offset input nonempty selected found tail ih =>
    change (input.take selected.length ++ tail.tokens.flatMap LexerToken.text) ++ tail.remaining = input
    rw [List.append_assoc]
    change input.take selected.length ++
      ((tokenizeFrom rules (offset + selected.length) (input.drop selected.length)).tokens.flatMap
        LexerToken.text ++ (tokenizeFrom rules (offset + selected.length)
          (input.drop selected.length)).remaining) = input
    rw [ih, List.take_append_drop]

theorem tokenizeFrom_tokens_valid (rules : List (LexerRule α)) (offset : Nat) (input : List α) :
    ∀ token ∈ (tokenizeFrom rules offset input).tokens, token.Valid rules := by
  fun_induction tokenizeFrom rules offset input with
  | case1 offset => simp
  | case2 offset input nonempty absent => simp
  | case3 offset input nonempty selected found tail ih =>
    intro token member
    change token ∈ ⟨selected.ruleIndex, input.take selected.length⟩ :: tail.tokens at member
    rcases List.mem_cons.mp member with rfl | member
    · exact lexOne_token_valid found
    · exact ih token member

theorem tokenizeFrom_complete_iff (rules : List (LexerRule α)) (offset : Nat) (input : List α) :
    (tokenizeFrom rules offset input).refusedAt = none ↔
      (tokenizeFrom rules offset input).remaining = [] := by
  fun_induction tokenizeFrom rules offset input with
  | case1 offset => simp
  | case2 offset input nonempty absent => simp [nonempty]
  | case3 offset input nonempty selected found tail ih => exact ih

theorem tokenizeFrom_refusal (rules : List (LexerRule α)) (offset : Nat) (input : List α)
    (position : Nat) : (tokenizeFrom rules offset input).refusedAt = some position →
      position = offset + ((tokenizeFrom rules offset input).tokens.flatMap LexerToken.text).length ∧
        (tokenizeFrom rules offset input).remaining ≠ [] ∧
        lexOne rules (tokenizeFrom rules offset input).remaining = none := by
  fun_induction tokenizeFrom rules offset input with
  | case1 offset => simp
  | case2 offset input nonempty absent =>
    intro failed
    have same : offset = position := Option.some.inj failed
    subst position
    exact ⟨rfl, nonempty, absent⟩
  | case3 offset input nonempty selected found tail ih =>
    intro failed
    obtain ⟨positionEq, remainingNonempty, absent⟩ := ih failed
    refine ⟨?_, remainingNonempty, absent⟩
    change position = offset + (input.take selected.length ++ tail.tokens.flatMap LexerToken.text).length
    rw [List.length_append, List.length_take, Nat.min_eq_left (lexOne_bound found)]
    change position = (offset + selected.length) + (tail.tokens.flatMap LexerToken.text).length at positionEq
    omega

theorem tokenize_reconstruct (rules : List (LexerRule α)) (input : List α) :
    (tokenize rules input).tokens.flatMap LexerToken.text ++ (tokenize rules input).remaining = input :=
  tokenizeFrom_reconstruct rules 0 input

theorem tokenize_tokens_valid (rules : List (LexerRule α)) (input : List α) :
    ∀ token ∈ (tokenize rules input).tokens, token.Valid rules :=
  tokenizeFrom_tokens_valid rules 0 input

theorem tokenize_complete_iff (rules : List (LexerRule α)) (input : List α) :
    (tokenize rules input).refusedAt = none ↔ (tokenize rules input).remaining = [] :=
  tokenizeFrom_complete_iff rules 0 input

theorem tokenize_refusal (rules : List (LexerRule α)) (input : List α) (position : Nat)
    (failed : (tokenize rules input).refusedAt = some position) :
    position = ((tokenize rules input).tokens.flatMap LexerToken.text).length ∧
      (tokenize rules input).remaining ≠ [] ∧
      lexOne rules (tokenize rules input).remaining = none := by
  simpa only [tokenize, Nat.zero_add] using tokenizeFrom_refusal rules 0 input position failed


/-- A literal-word rule, with singleton-language semantics. -/
def LexerRule.literal [DecidableEq α] (word : List α) : LexerRule α where
  language := {word}
  accepts input := decide (input = word)
  accepts_correct input := by
    change decide (input = word) = true ↔ input = word
    simp

/-- ASCII lower-case identifiers have at least one letter. -/
def asciiIdentifierRule : LexerRule Char where
  language := {word | word ≠ [] ∧ ∀ character ∈ word, 'a' ≤ character ∧ character ≤ 'z'}
  accepts word := !word.isEmpty && word.all (fun character => decide ('a' ≤ character ∧ character ≤ 'z'))
  accepts_correct word := by
    change (!word.isEmpty && word.all (fun character => decide ('a' ≤ character ∧ character ≤ 'z'))) = true ↔
      word ≠ [] ∧ ∀ character ∈ word, 'a' ≤ character ∧ character ≤ 'z'
    simp

namespace LexerControls

/-- On a length tie the keyword's earlier authored position wins. -/
theorem keyword_identifier_tie :
    lexOne [LexerRule.literal "if".toList, asciiIdentifierRule] "if".toList = some ⟨0, 2⟩ := by
  decide

/-- A longer identifier defeats an earlier keyword rule. -/
theorem longer_identifier_wins :
    lexOne [LexerRule.literal "if".toList, asciiIdentifierRule] "ifx".toList = some ⟨1, 3⟩ := by
  decide

/-- Rule priority follows the authored position, including when the identifier is first. -/
theorem identifier_keyword_tie :
    lexOne [asciiIdentifierRule, LexerRule.literal "if".toList] "if".toList = some ⟨0, 2⟩ := by
  decide

/-- A nullable-only rule cannot produce a zero-length token. -/
theorem nullable_only_refuses :
    lexOne [LexerRule.literal ([] : List Char)] "if".toList = none := by
  decide

/-- An earlier empty-word rule does not consume priority from a positive match. -/
theorem nullable_before_keyword :
    lexOne [LexerRule.literal ([] : List Char), LexerRule.literal "if".toList] "if".toList = some ⟨1, 2⟩ := by
  decide

/-- A refused symbol is left untouched and its absolute input position is reported. -/
theorem refusal_position :
    tokenize [LexerRule.literal "if".toList, asciiIdentifierRule] "if!".toList =
      ⟨[⟨0, "if".toList⟩], ['!'], some 2⟩ := by
  unfold tokenize
  rw [tokenizeFrom_next (by decide : lexOne [LexerRule.literal "if".toList, asciiIdentifierRule]
    "if!".toList = some ⟨0, 2⟩)]
  have refused : tokenizeFrom [LexerRule.literal "if".toList, asciiIdentifierRule] 2 ['!'] =
      ⟨[], ['!'], some 2⟩ := tokenizeFrom_refused (by decide) (by decide)
  change (⟨⟨0, "if".toList⟩ :: (tokenizeFrom
      [LexerRule.literal "if".toList, asciiIdentifierRule] 2 ['!']).tokens,
    (tokenizeFrom [LexerRule.literal "if".toList, asciiIdentifierRule] 2 ['!']).remaining,
    (tokenizeFrom [LexerRule.literal "if".toList, asciiIdentifierRule] 2 ['!']).refusedAt⟩ : TokenizationResult Char) = _
  rw [refused]

/-- Repeated maximal-munch selection reconstructs the original token words. -/
theorem mixed_tokens :
    tokenize [LexerRule.literal "if".toList, asciiIdentifierRule, LexerRule.literal [';']]
        "if;ifx".toList =
      ⟨[⟨0, "if".toList⟩, ⟨2, [';']⟩, ⟨1, "ifx".toList⟩], [], none⟩ := by
  let rules := [LexerRule.literal "if".toList, asciiIdentifierRule, LexerRule.literal [';']]
  have final : tokenizeFrom rules 3 "ifx".toList = ⟨[⟨1, "ifx".toList⟩], [], none⟩ := by
    rw [tokenizeFrom_next (by decide : lexOne rules "ifx".toList = some ⟨1, 3⟩)]
    change (⟨⟨1, "ifx".toList⟩ :: (tokenizeFrom rules 6 []).tokens,
      (tokenizeFrom rules 6 []).remaining, (tokenizeFrom rules 6 []).refusedAt⟩ : TokenizationResult Char) = _
    rw [tokenizeFrom_nil]
  have middle : tokenizeFrom rules 2 ";ifx".toList =
      ⟨[⟨2, [';']⟩, ⟨1, "ifx".toList⟩], [], none⟩ := by
    rw [tokenizeFrom_next (by decide : lexOne rules ";ifx".toList = some ⟨2, 1⟩)]
    change (⟨⟨2, [';']⟩ :: (tokenizeFrom rules 3 "ifx".toList).tokens,
      (tokenizeFrom rules 3 "ifx".toList).remaining,
      (tokenizeFrom rules 3 "ifx".toList).refusedAt⟩ : TokenizationResult Char) = _
    rw [final]
  change tokenizeFrom rules 0 "if;ifx".toList = _
  rw [tokenizeFrom_next (by decide : lexOne rules "if;ifx".toList = some ⟨0, 2⟩)]
  change (⟨⟨0, "if".toList⟩ :: (tokenizeFrom rules 2 ";ifx".toList).tokens,
    (tokenizeFrom rules 2 ";ifx".toList).remaining,
    (tokenizeFrom rules 2 ";ifx".toList).refusedAt⟩ : TokenizationResult Char) = _
  rw [middle]

/-- Empty input terminates even if every rule is nullable. -/
theorem nullable_empty_input :
    tokenize [LexerRule.literal ([] : List Char)] [] = ⟨[], [], none⟩ :=
  tokenizeFrom_nil _ _

end LexerControls

end Mettapedia.Computability.RegularLanguages
