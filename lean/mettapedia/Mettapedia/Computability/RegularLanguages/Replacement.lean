import Mettapedia.Computability.RegularLanguages.Search

/-!
# Total replacement with retained match spans

Replacement uses leftmost-longest language search. An empty match advances
past one original symbol, copying that symbol into the output; an empty match
at the end is processed once and terminates. Replacement text is never scanned
again. Templates can insert literal text, the whole matched word, or both.
-/

set_option autoImplicit false

open scoped Computability

namespace Mettapedia.Computability.RegularLanguages

universe u
variable {α : Type u}

/-- Capture-free replacement templates. -/
inductive ReplacementTemplate (α : Type u) where
  | literal : List α → ReplacementTemplate α
  | whole : ReplacementTemplate α
  | append : ReplacementTemplate α → ReplacementTemplate α → ReplacementTemplate α
  deriving Repr

namespace ReplacementTemplate

def render : ReplacementTemplate α → List α → List α
  | literal text, _ => text
  | whole, word => word
  | append left right, word => left.render word ++ right.render word

@[simp] theorem render_literal (text word : List α) :
    (literal text).render word = text := rfl

@[simp] theorem render_whole (word : List α) : whole.render word = word := rfl

@[simp] theorem render_append (left right : ReplacementTemplate α) (word : List α) :
    (append left right).render word = left.render word ++ right.render word := rfl

end ReplacementTemplate

namespace MatchSpan

/-- The first position considered after replacing this match. Empty matches
consume one original symbol for progress; nonempty matches consume their word. -/
def nextCursor (span : MatchSpan) : Nat := span.start + max span.length 1

/-- The original symbol copied after a nonterminal empty match. -/
def emptyGap (span : MatchSpan) (input : List α) : List α :=
  if span.length = 0 then (input.drop span.start).take 1 else []

/-- An empty match at the final position is handled without recurring. -/
def FinalEmpty (span : MatchSpan) (input : List α) : Prop :=
  span.start = input.length ∧ span.length = 0

instance (span : MatchSpan) (input : List α) : Decidable (span.FinalEmpty input) :=
  inferInstanceAs (Decidable (span.start = input.length ∧ span.length = 0))

end MatchSpan

/-- Replacement text together with the spans in the original input. -/
structure ReplacementResult (α : Type u) where
  output : List α
  spans : List MatchSpan
  deriving DecidableEq, Repr

/-- A replacement specification in terms of language membership and order.
It contains no call to the search or replacement algorithms. -/
inductive ReplacementDerivation (L : Language α) (template : ReplacementTemplate α) :
    List α → List α → List MatchSpan → Prop where
  | noMatch (input : List α) (absent : ∀ span, ¬ SpanMatch L input span) :
      ReplacementDerivation L template input input []
  | finalEmpty (input : List α) (span : MatchSpan)
      (chosen : LeftmostLongest L input span) (final : span.FinalEmpty input) :
      ReplacementDerivation L template input
        (input.take span.start ++ template.render (span.text input)) [span]
  | step (input : List α) (span : MatchSpan) (output : List α) (spans : List MatchSpan)
      (chosen : LeftmostLongest L input span) (nonfinal : ¬ span.FinalEmpty input)
      (rest : ReplacementDerivation L template (input.drop span.nextCursor) output spans) :
      ReplacementDerivation L template input
        (input.take span.start ++ template.render (span.text input) ++
          span.emptyGap input ++ output)
        (span :: spans.map (MatchSpan.shiftBy span.nextCursor))

variable (L : Language α) [DecidablePred (· ∈ L)]

/-- Replace only the first leftmost-longest match. -/
def replaceFirst (template : ReplacementTemplate α) (input : List α) : ReplacementResult α :=
  match search L input with
  | none => ⟨input, []⟩
  | some span => ⟨input.take span.start ++ template.render (span.text input) ++
      input.drop (span.start + span.length), [span]⟩

/-- Repeatedly replace leftmost-longest matches. Recursion decreases the
remaining original input's length, including when the match is empty. -/
def replaceAll (template : ReplacementTemplate α) (input : List α) : ReplacementResult α :=
  match _found : search L input with
  | none => ⟨input, []⟩
  | some span =>
      if _finalEmpty : span.FinalEmpty input then
        ⟨input.take span.start ++ template.render (span.text input), [span]⟩
      else
        let rest := replaceAll template (input.drop span.nextCursor)
        ⟨input.take span.start ++ template.render (span.text input) ++
          span.emptyGap input ++ rest.output,
          span :: rest.spans.map (MatchSpan.shiftBy span.nextCursor)⟩
termination_by input.length
decreasing_by
  have bounded := (search_sound L input span _found).1
  have positive : 0 < span.nextCursor := by
    simp only [MatchSpan.nextCursor]
    omega
  have nonempty : 0 < input.length := by
    by_contra h
    have _empty : input.length = 0 := by omega
    apply _finalEmpty
    simp only [MatchSpan.FinalEmpty]
    constructor <;> omega
  simp only [List.length_drop]
  omega

theorem replaceAll_of_search_none (template : ReplacementTemplate α) (input : List α)
    (absent : search L input = none) : replaceAll L template input = ⟨input, []⟩ := by
  rw [replaceAll, absent]

theorem replaceAll_of_finalEmpty (template : ReplacementTemplate α) (input : List α)
    (span : MatchSpan) (found : search L input = some span) (final : span.FinalEmpty input) :
    replaceAll L template input =
      ⟨input.take span.start ++ template.render (span.text input), [span]⟩ := by
  rw [replaceAll]
  split
  · rename_i absent
    simp [found] at absent
  · rename_i other matched
    have same : other = span := Option.some.inj (matched.symm.trans found)
    subst other
    split
    · rfl
    · contradiction

theorem replaceAll_step (template : ReplacementTemplate α) (input : List α) (span : MatchSpan)
    (found : search L input = some span) (nonfinal : ¬ span.FinalEmpty input) :
    replaceAll L template input =
      ⟨input.take span.start ++ template.render (span.text input) ++ span.emptyGap input ++
        (replaceAll L template (input.drop span.nextCursor)).output,
        span :: (replaceAll L template (input.drop span.nextCursor)).spans.map
          (MatchSpan.shiftBy span.nextCursor)⟩ := by
  rw [replaceAll]
  split
  · rename_i absent
    simp [found] at absent
  · rename_i other matched
    have same : other = span := Option.some.inj (matched.symm.trans found)
    subst other
    split
    · contradiction
    · rfl

theorem replaceAll_correct (template : ReplacementTemplate α) (input : List α) :
    ReplacementDerivation L template input (replaceAll L template input).output
      (replaceAll L template input).spans := by
  fun_induction replaceAll L template input with
  | case1 input absent =>
    simpa only [replaceAll, absent] using
      ReplacementDerivation.noMatch (L := L) (template := template) input
        ((search_none_iff L input).mp absent)
  | case2 input span found final =>
    simpa only [replaceAll, found, if_pos final] using
      ReplacementDerivation.finalEmpty (L := L) (template := template) input span
        ((search_some_iff L input span).mp found) final
  | case3 input span found nonfinal rest ih =>
    exact ReplacementDerivation.step (L := L) (template := template) input span
      rest.output rest.spans ((search_some_iff L input span).mp found) nonfinal ih

namespace ReplacementDerivation

omit [DecidablePred (· ∈ L)] in
theorem nextCursor_le (input : List α) (span : MatchSpan)
    (matched : SpanMatch L input span) (nonfinal : ¬ span.FinalEmpty input) :
    span.nextCursor ≤ input.length := by
  have bounded := matched.1
  by_cases empty : span.length = 0
  · have beforeEnd : span.start < input.length := by
      by_contra h
      exact nonfinal ⟨by omega, empty⟩
    simp only [MatchSpan.nextCursor, empty, max_eq_right (by omega : 0 ≤ 1)]
    omega
  · simp only [MatchSpan.nextCursor]
    omega

omit [DecidablePred (· ∈ L)] in
theorem spans_valid {template : ReplacementTemplate α} {input output : List α}
    {spans : List MatchSpan} (derivation : ReplacementDerivation L template input output spans) :
    ∀ span ∈ spans, SpanMatch L input span := by
  induction derivation with
  | noMatch input absent =>
    intro span member
    cases member
  | finalEmpty input span chosen final =>
    intro other member
    simp only [List.mem_singleton] at member
    subst other
    exact chosen.1
  | step input span output spans chosen nonfinal rest ih =>
    intro other member
    rcases List.mem_cons.mp member with same | later
    · subst other
      exact chosen.1
    · obtain ⟨relative, belongs, rfl⟩ := List.mem_map.mp later
      exact (spanMatch_shiftBy_iff L input span.nextCursor
        (nextCursor_le L input span chosen.1 nonfinal) relative).mpr (ih relative belongs)

omit [DecidablePred (· ∈ L)] in
theorem spans_nonoverlapping {template : ReplacementTemplate α} {input output : List α}
    {spans : List MatchSpan} (derivation : ReplacementDerivation L template input output spans) :
    spans.Pairwise (fun earlier later => earlier.nextCursor ≤ later.start) := by
  induction derivation with
  | noMatch => exact List.Pairwise.nil
  | finalEmpty => simp
  | step input span output spans chosen nonfinal rest ih =>
    rw [List.pairwise_cons]
    constructor
    · intro later member
      obtain ⟨relative, _, rfl⟩ := List.mem_map.mp member
      simp only [MatchSpan.shiftBy]
      omega
    · rw [List.pairwise_map]
      exact ih.imp (by
        intro earlier later ordered
        simp only [MatchSpan.shiftBy, MatchSpan.nextCursor] at ordered ⊢
        omega)

omit [DecidablePred (· ∈ L)] in
theorem span_count_le {template : ReplacementTemplate α} {input output : List α}
    {spans : List MatchSpan} (derivation : ReplacementDerivation L template input output spans) :
    spans.length ≤ input.length + 1 := by
  induction derivation with
  | noMatch => simp
  | finalEmpty => simp
  | step input span output spans chosen nonfinal rest ih =>
    have consumed := nextCursor_le L input span chosen.1 nonfinal
    have positive : 0 < span.nextCursor := by simp only [MatchSpan.nextCursor]; omega
    simp only [List.length_cons, List.length_map, List.length_drop] at ih ⊢
    omega

omit [DecidablePred (· ∈ L)] in
theorem unique {template : ReplacementTemplate α} {input output output' : List α}
    {spans spans' : List MatchSpan}
    (first : ReplacementDerivation L template input output spans)
    (second : ReplacementDerivation L template input output' spans') :
    output = output' ∧ spans = spans' := by
  induction first generalizing output' spans' with
  | noMatch input absent =>
    cases second with
    | noMatch => exact ⟨rfl, rfl⟩
    | finalEmpty _ span chosen _ => exact False.elim (absent span chosen.1)
    | step _ span _ _ chosen _ _ => exact False.elim (absent span chosen.1)
  | finalEmpty input span chosen final =>
    cases second with
    | noMatch _ absent => exact False.elim (absent span chosen.1)
    | finalEmpty _ other chosen' _ =>
      have same := leftmostLongest_unique L input chosen chosen'
      subst other
      exact ⟨rfl, rfl⟩
    | step _ other _ _ chosen' nonfinal _ =>
      have same := leftmostLongest_unique L input chosen chosen'
      subst other
      exact False.elim (nonfinal final)
  | step input span output spans chosen nonfinal rest ih =>
    cases second with
    | noMatch _ absent => exact False.elim (absent span chosen.1)
    | finalEmpty _ other chosen' final' =>
      have same := leftmostLongest_unique L input chosen chosen'
      subst other
      exact False.elim (nonfinal final')
    | step _ other _ _ chosen' _ rest' =>
      have same := leftmostLongest_unique L input chosen chosen'
      subst other
      obtain ⟨rfl, rfl⟩ := ih rest'
      exact ⟨rfl, rfl⟩

end ReplacementDerivation

theorem replaceAll_spans_valid (template : ReplacementTemplate α) (input : List α) :
    ∀ span ∈ (replaceAll L template input).spans, SpanMatch L input span :=
  ReplacementDerivation.spans_valid L (replaceAll_correct L template input)

theorem replaceAll_spans_nonoverlapping (template : ReplacementTemplate α) (input : List α) :
    (replaceAll L template input).spans.Pairwise
      (fun earlier later => earlier.nextCursor ≤ later.start) :=
  ReplacementDerivation.spans_nonoverlapping L (replaceAll_correct L template input)

theorem replaceAll_span_count_le (template : ReplacementTemplate α) (input : List α) :
    (replaceAll L template input).spans.length ≤ input.length + 1 :=
  ReplacementDerivation.span_count_le L (replaceAll_correct L template input)

theorem replaceAll_eq_iff (template : ReplacementTemplate α) (input output : List α)
    (spans : List MatchSpan) :
    replaceAll L template input = ⟨output, spans⟩ ↔
      ReplacementDerivation L template input output spans := by
  constructor
  · intro result
    have correct := replaceAll_correct L template input
    simpa only [result] using correct
  · intro derivation
    have unique := ReplacementDerivation.unique L (replaceAll_correct L template input) derivation
    cases found : replaceAll L template input with
    | mk actual actualSpans =>
      simpa only [found, ReplacementResult.output, ReplacementResult.spans,
        ReplacementResult.mk.injEq] using unique

/-- The first replacement's language specification and exact output. -/
theorem replaceFirst_spec (template : ReplacementTemplate α) (input : List α) :
    ((∀ span, ¬ SpanMatch L input span) ∧ replaceFirst L template input = ⟨input, []⟩) ∨
      ∃ span, LeftmostLongest L input span ∧
        replaceFirst L template input = ⟨input.take span.start ++
          template.render (span.text input) ++ input.drop (span.start + span.length), [span]⟩ := by
  cases found : search L input with
  | none => exact Or.inl ⟨(search_none_iff L input).mp found, by simp [replaceFirst, found]⟩
  | some span => exact Or.inr ⟨span, (search_some_iff L input span).mp found,
      by simp [replaceFirst, found]⟩

private theorem span_decompose (input : List α) (span : MatchSpan) :
    input.take span.start ++ span.text input ++ span.emptyGap input ++
      input.drop span.nextCursor = input := by
  by_cases empty : span.length = 0
  · simp only [MatchSpan.text, empty, List.take_zero, List.append_nil, MatchSpan.emptyGap,
      if_true, MatchSpan.nextCursor, max_eq_right (by omega : 0 ≤ 1)]
    have nextDrop : input.drop (span.start + 1) = (input.drop span.start).drop 1 :=
      List.drop_drop.symm
    rw [nextDrop, List.append_assoc, List.take_append_drop, List.take_append_drop]
  · have positive : 1 ≤ span.length := by omega
    simp only [MatchSpan.text, MatchSpan.emptyGap, if_neg empty, List.append_nil,
      MatchSpan.nextCursor, max_eq_left positive]
    rw [← List.take_add, List.take_append_drop]

namespace ReplacementDerivation

omit [DecidablePred (· ∈ L)] in
theorem whole_output {input output : List α} {spans : List MatchSpan}
    (derivation : ReplacementDerivation L ReplacementTemplate.whole input output spans) :
    output = input := by
  induction derivation with
  | noMatch => rfl
  | finalEmpty input span chosen final =>
    simp [ReplacementTemplate.render_whole, MatchSpan.text, final.1, final.2]
  | step input span output spans chosen nonfinal rest ih =>
    simpa only [ReplacementTemplate.render_whole, ih] using span_decompose input span

end ReplacementDerivation

/-- Replacing each match by itself preserves the input, including empty matches. -/
theorem replaceAll_whole (input : List α) :
    (replaceAll L ReplacementTemplate.whole input).output = input :=
  ReplacementDerivation.whole_output L (replaceAll_correct L ReplacementTemplate.whole input)

section Examples

private def epsilonWords : Language Char := fun word => word = []
private instance : DecidablePred (· ∈ epsilonWords) := fun _ => inferInstanceAs (Decidable (_ = []))

private def allA : Language Char := fun word => ∀ c ∈ word, c = 'a'
private instance : DecidablePred (· ∈ allA) := fun word => inferInstanceAs
  (Decidable (∀ c ∈ word, c = 'a'))

/-- The character predicate used below is exactly the language `a*`. -/
theorem allA_eq_literalStar : allA = ({['a']} : Language Char)∗ := by
  apply Language.ext
  intro word
  change (∀ c ∈ word, c = 'a') ↔ word ∈ ({['a']} : Language Char)∗
  rw [Language.mem_kstar]
  constructor
  · intro onlyA
    induction word with
    | nil => exact ⟨[], rfl, fun _ member => False.elim (List.not_mem_nil member)⟩
    | cons c word ih =>
      have head : c = 'a' := onlyA c List.mem_cons_self
      have tail : ∀ c ∈ word, c = 'a' := fun c hc => onlyA c (List.mem_cons_of_mem _ hc)
      obtain ⟨parts, reconstructed, members⟩ := ih tail
      refine ⟨['a'] :: parts, ?_, ?_⟩
      · simp [head, reconstructed]
      · intro part member
        rcases List.mem_cons.mp member with same | later
        · subst part
          rfl
        · exact members part later
  · rintro ⟨parts, rfl, members⟩ c member
    obtain ⟨part, hp, hc⟩ := List.mem_flatten.mp member
    have same : part = ['a'] := members part hp
    simpa [same] using hc

private def oneOrTwoA : Language Char := fun word => word = ['a'] ∨ word = ['a', 'a']
private instance : DecidablePred (· ∈ oneOrTwoA) := fun _ => inferInstanceAs
  (Decidable (_ = ['a'] ∨ _ = ['a', 'a']))

/-- Empty matching inserts at every boundary, including the final one. -/
theorem replaceAll_epsilon :
    replaceAll epsilonWords (.literal ['x']) ['a', 'b'] =
      ⟨['x', 'a', 'x', 'b', 'x'], [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩]⟩ := by
  have first : search epsilonWords ['a', 'b'] = some ⟨0, 0⟩ := by decide
  have second : search epsilonWords ['b'] = some ⟨0, 0⟩ := by decide
  have last : search epsilonWords [] = some ⟨0, 0⟩ := by decide
  simp [replaceAll_step _ _ _ _ first (by decide), replaceAll_step _ _ _ _ second (by decide),
    replaceAll_of_finalEmpty _ _ _ _ last (by decide), MatchSpan.nextCursor,
    MatchSpan.emptyGap, MatchSpan.shiftBy, ReplacementTemplate.render]

/-- The empty input has one boundary and receives one insertion. -/
theorem replaceAll_epsilon_empty :
    replaceAll epsilonWords (.literal ['x']) [] = ⟨['x'], [⟨0, 0⟩]⟩ := by
  have last : search epsilonWords [] = some ⟨0, 0⟩ := by decide
  simp [replaceAll_of_finalEmpty _ _ _ _ last (by decide), ReplacementTemplate.render]

/-- A nonempty longest match can be followed by the final empty match. -/
theorem replaceAll_allA :
    replaceAll allA (.literal ['x']) ['a'] = ⟨['x', 'x'], [⟨0, 1⟩, ⟨1, 0⟩]⟩ := by
  have first : search allA ['a'] = some ⟨0, 1⟩ := by decide
  have last : search allA [] = some ⟨0, 0⟩ := by decide
  simp [replaceAll_step _ _ _ _ first (by decide), replaceAll_of_finalEmpty _ _ _ _ last (by decide),
    MatchSpan.nextCursor,
    MatchSpan.emptyGap, MatchSpan.shiftBy, ReplacementTemplate.render]

theorem replaceAll_oneOrTwoA :
    replaceAll oneOrTwoA (.literal ['x']) ['a', 'a', 'b', 'a', 'a'] =
      ⟨['x', 'b', 'x'], [⟨0, 2⟩, ⟨3, 2⟩]⟩ := by
  have first : search oneOrTwoA ['a', 'a', 'b', 'a', 'a'] = some ⟨0, 2⟩ := by decide
  have second : search oneOrTwoA ['b', 'a', 'a'] = some ⟨1, 2⟩ := by decide
  have last : search oneOrTwoA [] = none := by decide
  simp [replaceAll_step _ _ _ _ first (by decide), replaceAll_step _ _ _ _ second (by decide),
    replaceAll_of_search_none _ _ _ last, MatchSpan.nextCursor,
    MatchSpan.emptyGap, MatchSpan.shiftBy, ReplacementTemplate.render]

/-- Inserted text is output, never another piece of input to be searched. -/
theorem replaceAll_does_not_rescan :
    replaceAll oneOrTwoA (.literal ['a', 'a']) ['a'] = ⟨['a', 'a'], [⟨0, 1⟩]⟩ := by
  have first : search oneOrTwoA ['a'] = some ⟨0, 1⟩ := by decide
  have last : search oneOrTwoA [] = none := by decide
  simp [replaceAll_step _ _ _ _ first (by decide), replaceAll_of_search_none _ _ _ last,
    MatchSpan.nextCursor,
    MatchSpan.emptyGap, ReplacementTemplate.render]

theorem replaceAll_rejection :
    replaceAll oneOrTwoA (.literal ['x']) ['b', 'b'] = ⟨['b', 'b'], []⟩ := by
  have absent : search oneOrTwoA ['b', 'b'] = none := by decide
  exact replaceAll_of_search_none _ _ _ absent

theorem replaceFirst_append_template :
    replaceFirst oneOrTwoA (.append (.literal ['x']) .whole) ['b', 'a', 'a'] =
      ⟨['b', 'x', 'a', 'a'], [⟨1, 2⟩]⟩ := by
  decide

end Examples

end Mettapedia.Computability.RegularLanguages
