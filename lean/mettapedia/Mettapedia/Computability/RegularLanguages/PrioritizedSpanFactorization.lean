import Mettapedia.Computability.RegularLanguages.PropertyAtoms
import Mettapedia.Computability.RegularLanguages.Utf8Spans
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Prioritized, span-aware matching factors through letters, assertions and byte boundaries

A matcher with priority semantics does not report a language. Given rules in
priority order, it reports which rule was selected, the tag of that rule, the
end of the first-priority match in scalars, and the same end in bytes. This is
the observation studied here (`Selected`, `observe`), together with the token
mode in which a rule is selected only when its first-priority match covers the
whole token (`tokenObserve`).

The matcher is one generic leftmost-first backtracking matcher (`ends`) over a
position oracle (`Probe`): the input length, class membership at a position and
assertion truth at a position. Alternatives are tried left first, sequences
compose in order, and a repetition is greedy or lazy; an iteration must consume
input and at most `length + 1` iterations are explored.

**Factorization.** On scalar input the observation is a function of four
lists (`Shadow`):

* the consumer letter of each scalar: its membership vector for the classes
  the rules use (`letterOf`), which is the property atom of
  `PropertyAtoms` projected to those labels (`letterOf_eq_profile`,
  `evaluate_letterOf_iff`);
* the word bit and the line-terminator bit of each scalar, from which the word
  and line assertions are computed;
* the UTF-8 width of each scalar, whose prefix sums are the byte boundaries
  (`byteOffset_eq_boundary`).

`observe_eq_observeShadow` and `observe_factors` state it; the token mode is
`tokenObserve_factors`. The byte end and the scalar end determine each other
(`byteStop_determines_stop`).

**What does not suffice.**

* Letters and assertion bits without widths: `a` and `λ` share a letter and
  both bits, and a match of one scalar ends at byte 1 or byte 2
  (`unsizedFiber`, `lettersOnlyFiber`).
* Letters and widths without assertion bits: `a\b` matches in `a ` and not in
  `ab` (`unassertedFiber`).
* Property atoms without the literal labels: a literal `a` splits the atom of a
  word class (`propertyAtomFiber`).
* Acceptance: `a|ab` and `ab|a` have the same end positions as sets, at every
  position of every input, yet select different ends on `ab`, and only the
  second covers the token `ab` (`ends_alt_perm`, `acceptanceFiber`).

**Relative minimality.** The consumer letter is the coarsest map through which
every class the rules use factors (`letterOf_coarsest`), and merging two
distinct letters breaks some class (`merge_breaks_label`). A merge beyond that
point is licensed only by preservation of the full observation: merging `a`
with `b` keeps acceptance of `a` against `[ab]` but changes the selected tag
(`mergeKeepsAcceptance`, `mergeChangesTag`), while in `.|a` the literal never
decides and erasing it keeps the observation on every input
(`dotOrA_factors_without_letters`).

**Domain.** The input is a list of Unicode scalars. A byte string that is not
UTF-8 has no such input (`no_scalar_input_encodes_0xFF`,
`no_scalar_input_encodes_continuation`), so a byte-level matcher must refuse it
before matching.

**Costs.** The number of candidate ends is work, not observation: `a|a` and `a`
select the same match with two candidates and one (`candidateCountFiber`).

**Boundary.** This is a reference semantics. A finite comparison against it
proves agreement on the compared domain only. Nothing here proves a table
generator, a compiler, a C matcher, its memory behaviour, or agreement with any
other regex engine.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.PrioritizedSpans

open Mettapedia.GSLT.Core.NonFactorization

/-! ## Patterns and the generic matcher -/

/-- Zero-width assertions. -/
inductive Assertion where
  | wordBoundary
  | notWordBoundary
  | lineStart
  | lineEnd
  | textStart
  | textEnd
  deriving DecidableEq, Repr

/-- Patterns over a type of classes, with ordered alternatives. -/
inductive Pattern (C : Type) where
  | fail
  | empty
  | cls (c : C)
  | assert (a : Assertion)
  | seq (p q : Pattern C)
  | alt (p q : Pattern C)
  | star (p : Pattern C) (greedy : Bool)

/-- Everything the matcher may read about its input. -/
structure Probe (C : Type) where
  length : Nat
  classAt : C → Nat → Bool
  assertAt : Assertion → Nat → Bool

/-- The ends of a repetition in priority order. Every iteration must consume
input, and at most `fuel` iterations are explored. -/
def starEnds (step : Nat → List Nat) (greedy : Bool) : Nat → Nat → List Nat
  | 0, i => [i]
  | fuel + 1, i =>
    let more := ((step i).filter fun j => decide (i < j)).flatMap (starEnds step greedy fuel)
    if greedy then more ++ [i] else i :: more

/-- The end positions of a pattern from a position, in priority order. -/
def ends {C : Type} (probe : Probe C) (fuel : Nat) : Pattern C → Nat → List Nat
  | .fail, _ => []
  | .empty, i => [i]
  | .cls c, i => if i < probe.length ∧ probe.classAt c i = true then [i + 1] else []
  | .assert a, i => if probe.assertAt a i = true then [i] else []
  | .seq p q, i => (ends probe fuel p i).flatMap (ends probe fuel q)
  | .alt p q, i => ends probe fuel p i ++ ends probe fuel q i
  | .star p greedy, i => starEnds (ends probe fuel p) greedy fuel i

/-- The end of the first-priority match. -/
def firstEnd {C : Type} (probe : Probe C) (p : Pattern C) (start : Nat) : Option Nat :=
  (ends probe (probe.length + 1) p start).head?

/-- The observation: rank of the selected rule, its tag, its end in scalars and
in bytes. -/
structure Selected (Tag : Type) where
  priority : Nat
  tag : Tag
  stop : Nat
  byteStop : Nat
  deriving DecidableEq, Repr

/-- The first rule, in priority order, whose first-priority end is accepted. -/
def selectFrom {C Tag : Type} (probe : Probe C) (byteAt : Nat → Nat) (accept : Nat → Bool)
    (start : Nat) : Nat → List (Tag × Pattern C) → Option (Selected Tag)
  | _, [] => none
  | rank, rule :: rest =>
    match firstEnd probe rule.2 start with
    | some stop =>
      if accept stop then some ⟨rank, rule.1, stop, byteAt stop⟩
      else selectFrom probe byteAt accept start (rank + 1) rest
    | none => selectFrom probe byteAt accept start (rank + 1) rest

/-! ## Bounds of end positions -/

theorem starEnds_bounds {len : Nat} {step : Nat → List Nat}
    (bounded : ∀ i, i ≤ len → ∀ j ∈ step i, i ≤ j ∧ j ≤ len) (greedy : Bool) :
    ∀ fuel i, i ≤ len → ∀ j ∈ starEnds step greedy fuel i, i ≤ j ∧ j ≤ len
  | 0, i, hi, j, hj => by
    simp only [starEnds, List.mem_singleton] at hj
    omega
  | fuel + 1, i, hi, j, hj => by
    have more : ∀ j ∈ ((step i).filter fun k => decide (i < k)).flatMap
        (starEnds step greedy fuel), i ≤ j ∧ j ≤ len := by
      intro j member
      obtain ⟨k, filtered, reached⟩ := List.mem_flatMap.mp member
      obtain ⟨stepped, later⟩ := List.mem_filter.mp filtered
      have first := bounded i hi k stepped
      have rest := starEnds_bounds bounded greedy fuel k first.2 j reached
      omega
    simp only [starEnds] at hj
    split at hj
    · rcases List.mem_append.mp hj with inner | final
      · exact more j inner
      · simp only [List.mem_singleton] at final
        omega
    · rcases List.mem_cons.mp hj with first | inner
      · omega
      · exact more j inner

/-- Ends lie between the start and the end of the input. -/
theorem ends_bounds {C : Type} (probe : Probe C) (fuel : Nat) :
    ∀ (p : Pattern C) (i : Nat), i ≤ probe.length →
      ∀ j ∈ ends probe fuel p i, i ≤ j ∧ j ≤ probe.length
  | .fail, i, _, j, hj => by simp [ends] at hj
  | .empty, i, hi, j, hj => by
    simp only [ends, List.mem_singleton] at hj
    omega
  | .cls c, i, hi, j, hj => by
    simp only [ends] at hj
    split at hj
    · rename_i inRange
      simp only [List.mem_singleton] at hj
      omega
    · simp at hj
  | .assert a, i, hi, j, hj => by
    simp only [ends] at hj
    split at hj
    · simp only [List.mem_singleton] at hj
      omega
    · simp at hj
  | .seq p q, i, hi, j, hj => by
    obtain ⟨k, first, second⟩ := List.mem_flatMap.mp hj
    have left := ends_bounds probe fuel p i hi k first
    have right := ends_bounds probe fuel q k left.2 j second
    omega
  | .alt p q, i, hi, j, hj => by
    rcases List.mem_append.mp hj with left | right
    · exact ends_bounds probe fuel p i hi j left
    · exact ends_bounds probe fuel q i hi j right
  | .star p greedy, i, hi, j, hj =>
    starEnds_bounds (fun k hk => ends_bounds probe fuel p k hk) greedy fuel i hi j hj

theorem firstEnd_bounds {C : Type} {probe : Probe C} {p : Pattern C} {start stop : Nat}
    (found : firstEnd probe p start = some stop) (inRange : start ≤ probe.length) :
    start ≤ stop ∧ stop ≤ probe.length := by
  unfold firstEnd at found
  cases listed : ends probe (probe.length + 1) p start with
  | nil => simp [listed] at found
  | cons head tail =>
    simp only [listed, List.head?_cons, Option.some.injEq] at found
    subst found
    exact ends_bounds probe (probe.length + 1) p start inRange head
      (by rw [listed]; exact List.mem_cons_self)

theorem selectFrom_some {C Tag : Type} {probe : Probe C} {byteAt : Nat → Nat}
    {accept : Nat → Bool} {start : Nat} :
    ∀ {rank : Nat} {rules : List (Tag × Pattern C)} {selected : Selected Tag},
      selectFrom probe byteAt accept start rank rules = some selected →
        selected.byteStop = byteAt selected.stop ∧ accept selected.stop = true ∧
          ∃ rule ∈ rules, firstEnd probe rule.2 start = some selected.stop
  | _, [], _, found => by simp [selectFrom] at found
  | rank, rule :: rest, selected, found => by
    simp only [selectFrom] at found
    split at found
    · rename_i stop firstFound
      split at found
      · rename_i accepted
        simp only [Option.some.injEq] at found
        subst found
        exact ⟨rfl, accepted, rule, List.mem_cons_self, firstFound⟩
      · obtain ⟨bytes, accepted, other, member, otherFound⟩ := selectFrom_some found
        exact ⟨bytes, accepted, other, List.mem_cons_of_mem _ member, otherFound⟩
    · obtain ⟨bytes, accepted, other, member, otherFound⟩ := selectFrom_some found
      exact ⟨bytes, accepted, other, List.mem_cons_of_mem _ member, otherFound⟩

/-! ## Scalar input -/

variable {m : Nat}

/-- The consumer letter of a scalar: its membership in each label the rules use. -/
def letterOf (labels : Fin m → Char → Bool) (x : Char) : Fin m → Bool := fun i => labels i x

/-- The labels as sets, for the independent meaning of `PropertyAtoms`. -/
def labelSets (labels : Fin m → Char → Bool) : Fin m → Set Char :=
  fun i => {x | labels i x = true}

/-- **The letter is the realized property atom of the labels.** -/
theorem letterOf_eq_profile (labels : Fin m → Char → Bool) (x : Char) :
    letterOf labels x = PropertyAtoms.profile (labelSets labels) x := by
  funext i
  unfold letterOf PropertyAtoms.profile labelSets
  by_cases h : labels i x = true <;> simp [h]

/-- **Class membership read from the letter is the independent pointwise meaning.** -/
theorem evaluate_letterOf_iff (labels : Fin m → Char → Bool) (e : PropertyAtoms.Expr m)
    (x : Char) :
    PropertyAtoms.evaluate e (letterOf labels x) = true ↔
      PropertyAtoms.Denote Set.univ (labelSets labels) e x := by
  rw [PropertyAtoms.denote_evaluate, letterOf_eq_profile]
  simp

/-- Consumer letters of selected labels are projections of the letters of all
labels. -/
theorem letterOf_select {n : Nat} (labels : Fin n → Char → Bool) (select : Fin m → Fin n)
    (x : Char) :
    letterOf (fun i => labels (select i)) x = fun i => letterOf labels x (select i) := rfl

/-- The predicates the assertions read. -/
structure Predicates where
  word : Char → Bool
  lineTerminator : Char → Bool

/-- A predicate of the scalar at a position; false past the end. -/
def scalarAt (p : Char → Bool) (input : List Char) (i : Nat) : Bool :=
  (input[i]?.map p).getD false

/-- A predicate of the scalar before a position; false at the start. -/
def scalarBefore (p : Char → Bool) (input : List Char) : Nat → Bool
  | 0 => false
  | k + 1 => scalarAt p input k

/-- Assertions read from the scalars themselves. -/
def scalarAssertion (preds : Predicates) (input : List Char) : Assertion → Nat → Bool
  | .wordBoundary, i => scalarBefore preds.word input i != scalarAt preds.word input i
  | .notWordBoundary, i => scalarBefore preds.word input i == scalarAt preds.word input i
  | .lineStart, i => i == 0 || scalarBefore preds.lineTerminator input i
  | .lineEnd, i => i == input.length || scalarAt preds.lineTerminator input i
  | .textStart, i => i == 0
  | .textEnd, i => i == input.length

/-- The oracle of a scalar input. -/
def scalarProbe (labels : Fin m → Char → Bool) (preds : Predicates) (input : List Char) :
    Probe (PropertyAtoms.Expr m) where
  length := input.length
  classAt e i := (input[i]?.map fun x => PropertyAtoms.evaluate e (letterOf labels x)).getD false
  assertAt := scalarAssertion preds input

/-- **The observation on scalar input**: the first rule with a match from
`start`, its rank, tag, scalar end and byte end. -/
def observe {Tag : Type} (labels : Fin m → Char → Bool) (preds : Predicates)
    (rules : List (Tag × Pattern (PropertyAtoms.Expr m))) (start : Nat) (input : List Char) :
    Option (Selected Tag) :=
  selectFrom (scalarProbe labels preds input) (byteOffset input) (fun _ => true) start 0 rules

/-- **Token mode**: the first rule whose first-priority match from the start
covers the whole token. -/
def tokenObserve {Tag : Type} (labels : Fin m → Char → Bool) (preds : Predicates)
    (rules : List (Tag × Pattern (PropertyAtoms.Expr m))) (input : List Char) :
    Option (Selected Tag) :=
  selectFrom (scalarProbe labels preds input) (byteOffset input)
    (fun stop => stop == input.length) 0 0 rules

/-! ## The shadow -/

/-- Letters, word bits, line-terminator bits and UTF-8 widths of the scalars. -/
structure Shadow (m : Nat) where
  letters : List (Fin m → Bool)
  word : List Bool
  line : List Bool
  widths : List Nat
  deriving DecidableEq

/-- The shadow of a scalar input. -/
def shadow (labels : Fin m → Char → Bool) (preds : Predicates) (input : List Char) : Shadow m :=
  ⟨input.map (letterOf labels), input.map preds.word, input.map preds.lineTerminator,
    input.map Char.utf8Size⟩

/-- Every letter of a shadow is a realized property atom. -/
theorem shadow_letters_realized (labels : Fin m → Char → Bool) (preds : Predicates)
    (input : List Char) :
    ∀ letter ∈ (shadow labels preds input).letters,
      ∃ x ∈ input, PropertyAtoms.profile (labelSets labels) x = letter := by
  intro letter member
  obtain ⟨x, present, rfl⟩ := List.mem_map.mp member
  exact ⟨x, present, (letterOf_eq_profile labels x).symm⟩

def bitAt (bits : List Bool) (i : Nat) : Bool := (bits[i]?).getD false

def bitBefore (bits : List Bool) : Nat → Bool
  | 0 => false
  | k + 1 => bitAt bits k

/-- Assertions read from the shadow's bits. -/
def shadowAssertion (s : Shadow m) : Assertion → Nat → Bool
  | .wordBoundary, i => bitBefore s.word i != bitAt s.word i
  | .notWordBoundary, i => bitBefore s.word i == bitAt s.word i
  | .lineStart, i => i == 0 || bitBefore s.line i
  | .lineEnd, i => i == s.letters.length || bitAt s.line i
  | .textStart, i => i == 0
  | .textEnd, i => i == s.letters.length

/-- The oracle of a shadow. -/
def shadowProbe (s : Shadow m) : Probe (PropertyAtoms.Expr m) where
  length := s.letters.length
  classAt e i := (s.letters[i]?.map (PropertyAtoms.evaluate e)).getD false
  assertAt := shadowAssertion s

/-- The byte boundary before a scalar position: a prefix sum of widths. -/
def boundary (s : Shadow m) (k : Nat) : Nat := (s.widths.take k).sum

/-- The observation computed from a shadow. -/
def observeShadow {Tag : Type} (rules : List (Tag × Pattern (PropertyAtoms.Expr m)))
    (start : Nat) (s : Shadow m) : Option (Selected Tag) :=
  selectFrom (shadowProbe s) (boundary s) (fun _ => true) start 0 rules

/-- The token observation computed from a shadow. -/
def tokenObserveShadow {Tag : Type} (rules : List (Tag × Pattern (PropertyAtoms.Expr m)))
    (s : Shadow m) : Option (Selected Tag) :=
  selectFrom (shadowProbe s) (boundary s) (fun stop => stop == s.letters.length) 0 0 rules

theorem scalarAt_eq_bitAt (p : Char → Bool) (input : List Char) (i : Nat) :
    scalarAt p input i = bitAt (input.map p) i := by
  simp [scalarAt, bitAt, List.getElem?_map]

theorem scalarBefore_eq_bitBefore (p : Char → Bool) (input : List Char) (i : Nat) :
    scalarBefore p input i = bitBefore (input.map p) i := by
  cases i with
  | zero => rfl
  | succ k => exact scalarAt_eq_bitAt p input k

/-- **The scalar oracle is the shadow oracle.** -/
theorem scalarProbe_eq_shadowProbe (labels : Fin m → Char → Bool) (preds : Predicates)
    (input : List Char) :
    scalarProbe labels preds input = shadowProbe (shadow labels preds input) := by
  unfold scalarProbe shadowProbe
  congr 1
  · simp [shadow]
  · funext e i
    simp [shadow, List.getElem?_map, Function.comp_def]
  · funext a i
    cases a <;>
      simp [scalarAssertion, shadowAssertion, shadow, scalarAt_eq_bitAt,
        scalarBefore_eq_bitBefore]

/-- **Byte boundaries are prefix sums of widths.** -/
theorem byteOffset_eq_boundary (labels : Fin m → Char → Bool) (preds : Predicates)
    (input : List Char) (k : Nat) :
    byteOffset input k = boundary (shadow labels preds input) k := by
  simp [byteOffset, utf8Length, boundary, shadow, List.map_take]

/-- **The observation factors through the shadow**, pointwise. -/
theorem observe_eq_observeShadow {Tag : Type} (labels : Fin m → Char → Bool)
    (preds : Predicates) (rules : List (Tag × Pattern (PropertyAtoms.Expr m))) (start : Nat)
    (input : List Char) :
    observe labels preds rules start input =
      observeShadow rules start (shadow labels preds input) := by
  unfold observe observeShadow
  rw [scalarProbe_eq_shadowProbe labels preds input]
  have bytes : byteOffset input = boundary (shadow labels preds input) :=
    funext (byteOffset_eq_boundary labels preds input)
  rw [bytes]

theorem tokenObserve_eq_tokenObserveShadow {Tag : Type} (labels : Fin m → Char → Bool)
    (preds : Predicates) (rules : List (Tag × Pattern (PropertyAtoms.Expr m)))
    (input : List Char) :
    tokenObserve labels preds rules input =
      tokenObserveShadow rules (shadow labels preds input) := by
  unfold tokenObserve tokenObserveShadow
  rw [scalarProbe_eq_shadowProbe labels preds input]
  have bytes : byteOffset input = boundary (shadow labels preds input) :=
    funext (byteOffset_eq_boundary labels preds input)
  have length : (shadow labels preds input).letters.length = input.length := by simp [shadow]
  rw [bytes, length]

/-- **Factorization**: selected rank, tag, scalar end and byte end are a function
of letters, assertion bits and widths. -/
theorem observe_factors {Tag : Type} (labels : Fin m → Char → Bool) (preds : Predicates)
    (rules : List (Tag × Pattern (PropertyAtoms.Expr m))) (start : Nat) :
    Factors (shadow labels preds) (observe labels preds rules start) :=
  ⟨observeShadow rules start, fun input =>
    (observe_eq_observeShadow labels preds rules start input).symm⟩

/-- **Factorization in token mode.** -/
theorem tokenObserve_factors {Tag : Type} (labels : Fin m → Char → Bool) (preds : Predicates)
    (rules : List (Tag × Pattern (PropertyAtoms.Expr m))) :
    Factors (shadow labels preds) (tokenObserve labels preds rules) :=
  ⟨tokenObserveShadow rules, fun input =>
    (tokenObserve_eq_tokenObserveShadow labels preds rules input).symm⟩

/-- A selected end lies in the input, and its byte end is its boundary. -/
theorem observe_some {Tag : Type} {labels : Fin m → Char → Bool} {preds : Predicates}
    {rules : List (Tag × Pattern (PropertyAtoms.Expr m))} {start : Nat} {input : List Char}
    {selected : Selected Tag} (found : observe labels preds rules start input = some selected)
    (inRange : start ≤ input.length) :
    start ≤ selected.stop ∧ selected.stop ≤ input.length ∧
      selected.byteStop = byteOffset input selected.stop := by
  obtain ⟨bytes, _, rule, _, firstFound⟩ := selectFrom_some found
  have bounds := firstEnd_bounds firstFound inRange
  exact ⟨bounds.1, bounds.2, bytes⟩

/-- **The byte end determines the scalar end**: two selections on one input, by
any rules, with one byte end have one scalar end. -/
theorem byteStop_determines_stop {Tag Tag' : Type} {labels : Fin m → Char → Bool}
    {preds : Predicates} {rules : List (Tag × Pattern (PropertyAtoms.Expr m))}
    {rules' : List (Tag' × Pattern (PropertyAtoms.Expr m))} {start start' : Nat}
    {input : List Char} {selected : Selected Tag} {selected' : Selected Tag'}
    (found : observe labels preds rules start input = some selected)
    (found' : observe labels preds rules' start' input = some selected')
    (inRange : start ≤ input.length) (inRange' : start' ≤ input.length)
    (sameBytes : selected.byteStop = selected'.byteStop) : selected.stop = selected'.stop := by
  obtain ⟨_, bound, bytes⟩ := observe_some found inRange
  obtain ⟨_, bound', bytes'⟩ := observe_some found' inRange'
  exact byteOffset_injective input bound bound' (bytes.symm.trans (sameBytes.trans bytes'))

/-! ## Priority is finer than the language -/

/-- Swapping alternatives permutes the ends. -/
theorem ends_alt_perm {C : Type} (probe : Probe C) (fuel : Nat) (p q : Pattern C) (i : Nat) :
    (ends probe fuel (.alt p q) i).Perm (ends probe fuel (.alt q p) i) :=
  List.perm_append_comm

/-- Hence every set observation of the ends agrees, in particular whole-input
acceptance. -/
theorem mem_ends_alt_comm {C : Type} (probe : Probe C) (fuel : Nat) (p q : Pattern C)
    (i k : Nat) : k ∈ ends probe fuel (.alt p q) i ↔ k ∈ ends probe fuel (.alt q p) i :=
  (ends_alt_perm probe fuel p q i).mem_iff

/-- An alternative with itself selects what its branch selects. -/
theorem firstEnd_alt_self {C : Type} (probe : Probe C) (p : Pattern C) (start : Nat) :
    firstEnd probe (.alt p p) start = firstEnd probe p start := by
  unfold firstEnd
  simp only [ends]
  cases ends probe (probe.length + 1) p start <;> rfl

/-! ## Relative minimality of the consumer alphabet -/

/-- Each label factors through the letter. -/
theorem label_factors_letterOf (labels : Fin m → Char → Bool) (i : Fin m) :
    Factors (letterOf labels) (labels i) :=
  ⟨fun letter => letter i, fun _ => rfl⟩

/-- **The letter is the coarsest map preserving the labels**: it factors through
every map through which each label factors. -/
theorem letterOf_coarsest {β : Type} (labels : Fin m → Char → Bool) (f : Char → β)
    (keeps : ∀ i, Factors f (labels i)) : Factors f (letterOf labels) := by
  choose recover recovers using keeps
  exact ⟨fun b i => recover i b, fun x => funext fun i => recovers i x⟩

/-- **A further merge breaks a label**: identifying two distinct letters gives a
non-trivial fibre for some label. -/
theorem merge_breaks_label {β : Type} (labels : Fin m → Char → Bool)
    (merge : (Fin m → Bool) → β) {x y : Char}
    (distinct : letterOf labels x ≠ letterOf labels y)
    (merged : merge (letterOf labels x) = merge (letterOf labels y)) :
    ∃ i, Nonempty (NonTrivialFiber (merge ∘ letterOf labels) (labels i)) := by
  obtain ⟨i, different⟩ := Function.ne_iff.mp distinct
  exact ⟨i, ⟨⟨x, y, merged, different⟩⟩⟩

/-! ## Domain: decoded scalar input -/

/-- **No scalar input has the byte `0xFF` as its encoding.** -/
theorem no_scalar_input_encodes_0xFF (word : List Char) : utf8Bytes word ≠ [0xFF] := by
  intro encoded
  have valid : ([0xFF] : List UInt8).toByteArray.IsValidUTF8 := by
    rw [← encoded, ← utf8Encode_eq_utf8Bytes]
    exact ByteArray.isValidUTF8_utf8Encode
  have first := valid.isUTF8FirstByte_getElem_zero (by decide)
  revert first
  decide

/-- **No scalar input begins with a continuation byte.** -/
theorem no_scalar_input_encodes_continuation (word : List Char) (rest : List UInt8) :
    utf8Bytes word ≠ 0x80 :: rest := by
  intro encoded
  have valid : (0x80 :: rest : List UInt8).toByteArray.IsValidUTF8 := by
    rw [← encoded, ← utf8Encode_eq_utf8Bytes]
    exact ByteArray.isValidUTF8_utf8Encode
  have first := valid.isUTF8FirstByte_getElem_zero (by simp)
  rw [List.getElem_toByteArray, List.getElem_cons_zero] at first
  revert first
  decide

/-- The standard decoder refuses the byte `0xFF`. -/
theorem fromUTF8_rejects_0xFF : String.fromUTF8? ([0xFF] : List UInt8).toByteArray = none := by
  have invalid : ¬ ([0xFF] : List UInt8).toByteArray.IsValidUTF8 := by
    intro valid
    have first := valid.isUTF8FirstByte_getElem_zero (by decide)
    revert first
    decide
  simp [String.fromUTF8?, invalid]

/-! ## Examples and controls -/

namespace Controls

/-- An example word predicate standing in for a Unicode word class: ASCII
letters, digits and underscore, and the Greek and Coptic block. -/
def exampleWord (x : Char) : Bool :=
  x.isAlphanum || x == '_' || (decide (0x370 ≤ x.val.toNat) && decide (x.val.toNat ≤ 0x3FF))

def examplePredicates : Predicates := ⟨exampleWord, fun x => x == '\n'⟩

/-- No labels: one letter for every scalar. -/
def noLabels : Fin 0 → Char → Bool := fun i => i.elim0

/-- The class of every scalar, `.`. -/
def anyScalar : Pattern (PropertyAtoms.Expr 0) := .cls .full

/-! ### Positive instances of the factorization -/

/-- `.` on `λx` from scalar 0 ends at scalar 1 and byte 2. -/
theorem any_on_lambda :
    observe noLabels examplePredicates [(0, anyScalar)] 0 "λx".toList =
      some ⟨0, 0, 1, 2⟩ := by decide

/-- The same value is computed from the shadow. -/
theorem any_on_lambda_shadow :
    observeShadow [(0, anyScalar)] 0 (shadow noLabels examplePredicates "λx".toList) =
      some ⟨0, 0, 1, 2⟩ := by decide

/-- A greedy and a lazy repetition of `.`: ends at bytes 3 and 2. -/
theorem greedy_and_lazy :
    observe noLabels examplePredicates [(0, .seq anyScalar (.star anyScalar true))] 0
        "λx".toList = some ⟨0, 0, 2, 3⟩ ∧
      observe noLabels examplePredicates [(0, .seq anyScalar (.star anyScalar false))] 0
        "λx".toList = some ⟨0, 0, 1, 2⟩ := by decide

/-! ### Letters (and assertion bits) without widths -/

/-- Letters, word bits and line bits, without widths. -/
def unsized (s : Shadow m) : List (Fin m → Bool) × List Bool × List Bool :=
  (s.letters, s.word, s.line)

/-- **`a` and `λ`**: one letter, both word scalars, neither a line terminator;
the match of one scalar ends at byte 1 or byte 2. -/
def unsizedFiber :
    NonTrivialFiber (fun input => unsized (shadow noLabels examplePredicates input))
      (observe noLabels examplePredicates [(0, anyScalar)] 0) where
  left := ['a']
  right := ['λ']
  sameShadow := by decide
  differentValue := by decide

/-- Hence letters alone do not determine the observation. -/
def lettersOnlyFiber :
    NonTrivialFiber (fun input => (shadow noLabels examplePredicates input).letters)
      (observe noLabels examplePredicates [(0, anyScalar)] 0) :=
  unsizedFiber.coarsen (coarsen := Prod.fst) (fun _ => rfl)

theorem not_factors_unsized :
    ¬ Factors (fun input => unsized (shadow noLabels examplePredicates input))
      (observe noLabels examplePredicates [(0, anyScalar)] 0) :=
  unsizedFiber.not_factors

theorem not_factors_letters :
    ¬ Factors (fun input => (shadow noLabels examplePredicates input).letters)
      (observe noLabels examplePredicates [(0, anyScalar)] 0) :=
  lettersOnlyFiber.not_factors

/-! ### Letters and widths without assertion bits -/

/-- One label: the literal `a`. -/
def literalA : Fin 1 → Char → Bool := fun _ x => x == 'a'

/-- `a\b`. -/
def aThenBoundary : Pattern (PropertyAtoms.Expr 1) :=
  .seq (.cls (.label 0)) (.assert .wordBoundary)

/-- Letters and widths, without assertion bits. -/
def unasserted (s : Shadow m) : List (Fin m → Bool) × List Nat := (s.letters, s.widths)

theorem aThenBoundary_positive :
    observe literalA examplePredicates [(0, aThenBoundary)] 0 "a ".toList =
        some ⟨0, 0, 1, 1⟩ ∧
      observe literalA examplePredicates [(0, aThenBoundary)] 0 "ab".toList = none := by decide

/-- **`a\b` on `a ` and on `ab`**: same letters and widths, different outcome. -/
def unassertedFiber :
    NonTrivialFiber (fun input => unasserted (shadow literalA examplePredicates input))
      (observe literalA examplePredicates [(0, aThenBoundary)] 0) where
  left := "a ".toList
  right := "ab".toList
  sameShadow := by decide
  differentValue := by decide

/-- The line assertion likewise: `a$` holds before a line terminator. -/
theorem line_end_reads_line_bits :
    observe literalA examplePredicates [(0, .seq (.cls (.label 0)) (.assert .lineEnd))] 0
        "a\n".toList = some ⟨0, 0, 1, 1⟩ ∧
      observe literalA examplePredicates [(0, .seq (.cls (.label 0)) (.assert .lineEnd))] 0
        "ab".toList = none := by decide

/-! ### A literal splits a property atom -/

/-- The property label: the word class. -/
def wordLabel : Fin 1 → Char → Bool := fun _ => exampleWord

/-- The consumer labels: the word class and the literal `a`. -/
def wordAndA : Fin 2 → Char → Bool := fun i x => if i = 0 then exampleWord x else x == 'a'

/-- The rule `a`, a class over the consumer labels. -/
def literalRule : List (Nat × Pattern (PropertyAtoms.Expr 2)) := [(0, .cls (.label 1))]

/-- The property atom is the projection of the consumer letter. -/
theorem property_letter_is_projection (x : Char) :
    letterOf wordLabel x = fun i => letterOf wordAndA x ((fun _ => 0 : Fin 1 → Fin 2) i) := by
  funext i
  simp [letterOf, wordLabel, wordAndA]

/-- **`a` and `b` share the property atom of the word class**, and the literal
separates them. -/
def propertyAtomFiber :
    NonTrivialFiber (shadow wordLabel examplePredicates)
      (observe wordAndA examplePredicates literalRule 0) where
  left := "a".toList
  right := "b".toList
  sameShadow := by decide
  differentValue := by decide

/-- With the literal among the consumer labels, the observation factors. -/
theorem literal_refines_and_factors :
    Factors (shadow wordAndA examplePredicates)
        (observe wordAndA examplePredicates literalRule 0) ∧
      ¬ Factors (shadow wordLabel examplePredicates)
        (observe wordAndA examplePredicates literalRule 0) :=
  ⟨observe_factors _ _ _ _, propertyAtomFiber.not_factors⟩

/-! ### Priority against acceptance: `a|ab` and `ab|a` -/

/-- Labels: the literals `a` and `b`. -/
def abLabels : Fin 2 → Char → Bool := fun i x => if i = 0 then x == 'a' else x == 'b'

def litA : Pattern (PropertyAtoms.Expr 2) := .cls (.label 0)
def litB : Pattern (PropertyAtoms.Expr 2) := .cls (.label 1)

def aOrAb : Pattern (PropertyAtoms.Expr 2) := .alt litA (.seq litA litB)
def abOrA : Pattern (PropertyAtoms.Expr 2) := .alt (.seq litA litB) litA

def abProbe : Probe (PropertyAtoms.Expr 2) := scalarProbe abLabels examplePredicates "ab".toList

/-- Same ends as sets, at every position of every input. -/
theorem aOrAb_abOrA_same_ends (input : List Char) (fuel i k : Nat) :
    k ∈ ends (scalarProbe abLabels examplePredicates input) fuel aOrAb i ↔
      k ∈ ends (scalarProbe abLabels examplePredicates input) fuel abOrA i :=
  mem_ends_alt_comm _ fuel litA (.seq litA litB) i k

/-- Both accept `a` and `ab` as whole words. -/
theorem both_accept :
    1 ∈ ends (scalarProbe abLabels examplePredicates "a".toList) 2 aOrAb 0 ∧
      1 ∈ ends (scalarProbe abLabels examplePredicates "a".toList) 2 abOrA 0 ∧
      2 ∈ ends abProbe 3 aOrAb 0 ∧ 2 ∈ ends abProbe 3 abOrA 0 := by decide

/-- **Different selected ends on `ab`**, and only `ab|a` covers the token. -/
theorem priority_selects_differently :
    firstEnd abProbe aOrAb 0 = some 1 ∧ firstEnd abProbe abOrA 0 = some 2 ∧
      tokenObserve abLabels examplePredicates [(0, aOrAb)] "ab".toList = none ∧
      tokenObserve abLabels examplePredicates [(0, abOrA)] "ab".toList = some ⟨0, 0, 2, 2⟩ := by
  decide

/-- **The acceptance set does not determine the selected end.** -/
def acceptanceFiber :
    NonTrivialFiber (fun p : Pattern (PropertyAtoms.Expr 2) =>
        fun k => decide (k ∈ ends abProbe 3 p 0))
      (fun p => firstEnd abProbe p 0) where
  left := aOrAb
  right := abOrA
  sameShadow := by
    funext k
    simp only [decide_eq_decide]
    exact mem_ends_alt_comm abProbe 3 litA (.seq litA litB) 0 k
  differentValue := by decide

/-! ### Merges beyond the consumer alphabet -/

/-- Two rules: `a` with tag 1 first, then `[ab]` with tag 2. -/
def taggedRules : List (Nat × Pattern (PropertyAtoms.Expr 2)) :=
  [(1, litA), (2, .cls (.union (.label 0) (.label 1)))]

/-- Merge the letters of `a` and `b`. -/
def mergeAB (s : Shadow 2) : List Bool × List Bool × List Bool × List Nat :=
  (s.letters.map fun letter => letter 0 || letter 1, s.word, s.line, s.widths)

/-- **The merge keeps acceptance**: whether some rule matches from the start
is a function of the merged shadow. -/
theorem mergeKeepsAcceptance :
    Factors (fun input => mergeAB (shadow abLabels examplePredicates input))
      (fun input => (observe abLabels examplePredicates taggedRules 0 input).isSome) := by
  refine ⟨fun merged => merged.1.head?.getD false, fun input => ?_⟩
  cases input with
  | nil => rfl
  | cons x rest =>
    by_cases isA : x = 'a'
    · subst isA
      simp [mergeAB, shadow, letterOf, abLabels, observe, taggedRules, selectFrom, firstEnd,
        ends, scalarProbe, litA, PropertyAtoms.evaluate]
    · by_cases isB : x = 'b'
      · subst isB
        simp [mergeAB, shadow, letterOf, abLabels, observe, taggedRules, selectFrom, firstEnd,
          ends, scalarProbe, litA, PropertyAtoms.evaluate]
      · simp [mergeAB, shadow, letterOf, abLabels, observe, taggedRules, selectFrom, firstEnd,
          ends, scalarProbe, litA, PropertyAtoms.evaluate, isA, isB]

/-- **The merge changes the selected tag.** -/
def mergeChangesTag :
    NonTrivialFiber (fun input => mergeAB (shadow abLabels examplePredicates input))
      (observe abLabels examplePredicates taggedRules 0) where
  left := "a".toList
  right := "b".toList
  sameShadow := by decide
  differentValue := by decide

/-- `.|a`: the literal never decides under leftmost-first priority. -/
def dotOrA : List (Nat × Pattern (PropertyAtoms.Expr 1)) :=
  [(0, .alt (.cls .full) (.cls (.label 0)))]

/-- Erase the letters entirely. -/
def eraseLetters (s : Shadow m) : List Bool × List Bool × List Nat := (s.word, s.line, s.widths)

/-- **A merge licensed by the full observation**: erasing every letter keeps the
observation of `.|a` on every input. -/
theorem dotOrA_factors_without_letters :
    Factors (fun input => eraseLetters (shadow literalA examplePredicates input))
      (observe literalA examplePredicates dotOrA 0) := by
  refine ⟨fun erased => erased.2.2.head?.map fun width => ⟨0, 0, 1, width⟩, fun input => ?_⟩
  cases input with
  | nil => rfl
  | cons x rest =>
    simp [eraseLetters, shadow, observe, dotOrA, selectFrom, firstEnd, ends, scalarProbe,
      PropertyAtoms.evaluate, byteOffset, utf8Length]

/-- The same erasure breaks the literal label, which the observation never needed. -/
def erasureBreaksLiteral :
    NonTrivialFiber (fun x : Char => eraseLetters (shadow literalA examplePredicates [x]))
      (fun x => literalA 0 x) where
  left := 'a'
  right := 'b'
  sameShadow := by decide
  differentValue := by decide

/-- The coarsest-map theorem needs its hypothesis: the literal does not factor
through the word class, and neither does the letter. -/
def wordClassMissesLiteral : NonTrivialFiber exampleWord (wordAndA 1) where
  left := 'a'
  right := 'b'
  sameShadow := by decide
  differentValue := by decide

theorem letter_not_coarser_than_word_class : ¬ Factors exampleWord (letterOf wordAndA) := by
  intro factors
  apply wordClassMissesLiteral.not_factors
  obtain ⟨recover, recovers⟩ := factors
  exact ⟨fun b => recover b 1, fun x => congrFun (recovers x) 1⟩

/-- Distinct letters exist for `wordAndA`, so any merge of `a` and `b` breaks a label. -/
theorem merging_a_b_breaks_a_label :
    ∃ i, Nonempty (NonTrivialFiber ((fun _ => ()) ∘ letterOf wordAndA) (wordAndA i)) :=
  merge_breaks_label wordAndA (fun _ => ()) (x := 'a') (y := 'b')
    (by intro same; have := congrFun same 1; revert this; decide) rfl

/-! ### Invalid UTF-8 -/

/-- The standard decoder rejects the byte `0xFF`, and `λ` encodes as two
bytes. -/
theorem decoder_controls :
    String.fromUTF8? ([0xFF] : List UInt8).toByteArray = none ∧
      utf8Bytes "λ".toList = [0xCE, 0xBB] := ⟨fromUTF8_rejects_0xFF, by decide⟩

/-! ### Cost is not observation -/

/-- `a|a` and `a` select alike on every input. -/
theorem duplicate_alternative_same_observation (input : List Char) :
    observe literalA examplePredicates [(0, .alt (.cls (.label 0)) (.cls (.label 0)))] 0 input =
      observe literalA examplePredicates [(0, .cls (.label 0))] 0 input := by
  simp only [observe, selectFrom, firstEnd_alt_self]

/-- **The number of candidate ends is not a function of the observation.** -/
def candidateCountFiber :
    NonTrivialFiber (fun p : Pattern (PropertyAtoms.Expr 1) =>
        observe literalA examplePredicates [(0, p)] 0 "a".toList)
      (fun p => (ends (scalarProbe literalA examplePredicates "a".toList) 2 p 0).length) where
  left := .alt (.cls (.label 0)) (.cls (.label 0))
  right := .cls (.label 0)
  sameShadow := duplicate_alternative_same_observation _
  differentValue := by decide

end Controls

#print axioms ends_bounds
#print axioms selectFrom_some
#print axioms letterOf_eq_profile
#print axioms evaluate_letterOf_iff
#print axioms scalarProbe_eq_shadowProbe
#print axioms byteOffset_eq_boundary
#print axioms observe_eq_observeShadow
#print axioms observe_factors
#print axioms tokenObserve_factors
#print axioms observe_some
#print axioms byteStop_determines_stop
#print axioms ends_alt_perm
#print axioms mem_ends_alt_comm
#print axioms firstEnd_alt_self
#print axioms label_factors_letterOf
#print axioms letterOf_coarsest
#print axioms merge_breaks_label
#print axioms no_scalar_input_encodes_0xFF
#print axioms no_scalar_input_encodes_continuation
#print axioms fromUTF8_rejects_0xFF
#print axioms Controls.not_factors_unsized
#print axioms Controls.not_factors_letters
#print axioms Controls.unassertedFiber
#print axioms Controls.literal_refines_and_factors
#print axioms Controls.priority_selects_differently
#print axioms Controls.acceptanceFiber
#print axioms Controls.mergeKeepsAcceptance
#print axioms Controls.mergeChangesTag
#print axioms Controls.dotOrA_factors_without_letters
#print axioms Controls.erasureBreaksLiteral
#print axioms Controls.letter_not_coarser_than_word_class
#print axioms Controls.merging_a_b_breaks_a_label
#print axioms Controls.candidateCountFiber

end Mettapedia.Computability.RegularLanguages.PrioritizedSpans
