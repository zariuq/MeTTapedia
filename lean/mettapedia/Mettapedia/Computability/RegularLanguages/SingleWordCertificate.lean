import Mettapedia.Computability.RegularLanguages.Utf8Spans

/-!
# Finite-path certificates for token selection

The source machine follows ordered graph edges on an input. A separate
compiler inspects only the graph and admits a finite path of literal and
unconditional epsilon edges ending at an accept. Its word can replace the
source machine's whole-token decision, but not its prefix-match interface.
Choices, assertions and non-singleton classes remain source operations.

The certificate preserves the accepting tag and the unconsumed suffix for
every input. Increasing the execution bound does not change an admitted
path. UTF-8 injectivity then licenses byte equality for whole-token selection.

This is a graph-operation model, not a verification of native pointer layout,
allocation, the graph construction algorithm or a regex dialect.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.SingleWordCertificate

universe u v w
variable {Symbol : Type u} {State : Type v} {Tag : Type w}

/-- Edges outside the certified fragment retain their source semantics. -/
inductive Node (Symbol : Type u) (State : Type v) (Tag : Type w) where
  | accept (tag : Tag)
  | epsilon (next : State)
  | literal (symbol : Symbol) (next : State)
  | characterClass (contains : Symbol → Bool) (next : State)
  | assertion (holds : List Symbol → Bool) (next : State)
  | choice (next : List State)

/-- All source results, in edge order, retaining tags and suffixes. -/
def execute [DecidableEq Symbol] (graph : State → Node Symbol State Tag) :
    Nat → State → List Symbol → List (Tag × List Symbol)
  | 0, _, _ => []
  | fuel + 1, state, input =>
      match graph state with
      | .accept tag => [(tag, input)]
      | .epsilon next => execute graph fuel next input
      | .literal symbol next =>
          match input with
          | [] => []
          | actual :: rest => if actual = symbol then execute graph fuel next rest else []
      | .characterClass contains next =>
          match input with
          | [] => []
          | actual :: rest => if contains actual then execute graph fuel next rest else []
      | .assertion holds next => if holds input then execute graph fuel next input else []
      | .choice next => next.flatMap (fun child => execute graph fuel child input)

/-- Graph inspection does not read the input, execute assertions or choose
among alternatives. A bound also rejects epsilon and literal cycles. -/
def certify (graph : State → Node Symbol State Tag) :
    Nat → State → Option (List Symbol × Tag)
  | 0, _ => none
  | fuel + 1, state =>
      match graph state with
      | .accept tag => some ([], tag)
      | .epsilon next => certify graph fuel next
      | .literal symbol next =>
          (certify graph fuel next).map (fun result => (symbol :: result.1, result.2))
      | .characterClass _ _ | .assertion _ _ | .choice _ => none

/-- An independent word recognizer returns the suffix, not a membership bit. -/
def stripPrefix [DecidableEq Symbol] : List Symbol → List Symbol → Option (List Symbol)
  | [], input => some input
  | _ :: _, [] => none
  | symbol :: word, actual :: rest =>
      if actual = symbol then stripPrefix word rest else none

def wordResults [DecidableEq Symbol] (word : List Symbol) (tag : Tag)
    (input : List Symbol) : List (Tag × List Symbol) :=
  match stripPrefix word input with
  | none => []
  | some rest => [(tag, rest)]

/-- Every successful certificate agrees with independent source execution,
including a proper prefix and the exact accepting tag. -/
theorem certify_execute [DecidableEq Symbol]
    (graph : State → Node Symbol State Tag) (fuel : Nat) :
    ∀ state word tag, certify graph fuel state = some (word, tag) →
      ∀ input, execute graph fuel state input = wordResults word tag input := by
  induction fuel with
  | zero => simp [certify]
  | succ fuel ih =>
      intro state word tag admitted input
      cases node : graph state with
      | accept found =>
          simp [certify, node] at admitted
          obtain ⟨rfl, rfl⟩ := admitted
          simp [execute, node, wordResults, stripPrefix]
      | epsilon next =>
          simp only [certify, node] at admitted
          simpa only [execute, node] using ih next word tag admitted input
      | literal symbol next =>
          cases tail : certify graph fuel next with
          | none => simp [certify, node, tail] at admitted
          | some result =>
              obtain ⟨rest, found⟩ := result
              simp only [certify, node, tail, Option.map_some, Option.some.injEq,
                Prod.mk.injEq] at admitted
              obtain ⟨rfl, rfl⟩ := admitted
              cases input with
              | nil => simp [execute, node, wordResults, stripPrefix]
              | cons actual input =>
                  by_cases same : actual = symbol
                  · simpa [execute, node, wordResults, stripPrefix, same] using
                      ih next rest found tail input
                  · simp [execute, node, wordResults, stripPrefix, same]
      | characterClass contains next => simp [certify, node] at admitted
      | assertion holds next => simp [certify, node] at admitted
      | choice next => simp [certify, node] at admitted

theorem certify_more (graph : State → Node Symbol State Tag) (fuel extra : Nat) :
    ∀ state word tag, certify graph fuel state = some (word, tag) →
      certify graph (fuel + extra) state = some (word, tag) := by
  induction fuel with
  | zero => simp [certify]
  | succ fuel ih =>
      intro state word tag admitted
      cases node : graph state with
      | accept found =>
          simpa [certify, node, Nat.succ_add] using admitted
      | epsilon next =>
          simpa [certify, node, Nat.succ_add] using
            ih next word tag (by simpa [certify, node] using admitted)
      | literal symbol next =>
          cases tail : certify graph fuel next with
          | none => simp [certify, node, tail] at admitted
          | some result =>
              obtain ⟨rest, found⟩ := result
              have later := ih next rest found tail
              simp only [certify, node, tail, Option.map_some, Option.some.injEq,
                Prod.mk.injEq] at admitted
              obtain ⟨rfl, rfl⟩ := admitted
              simp [certify, node, Nat.succ_add, later]
      | characterClass contains next => simp [certify, node] at admitted
      | assertion holds next => simp [certify, node] at admitted
      | choice next => simp [certify, node] at admitted

theorem admitted_execution_bound_independent [DecidableEq Symbol]
    (graph : State → Node Symbol State Tag) {fuel : Nat} {state : State}
    {word : List Symbol} {tag : Tag}
    (admitted : certify graph fuel state = some (word, tag))
    (extra : Nat) (input : List Symbol) :
    execute graph (fuel + extra) state input = execute graph fuel state input := by
  rw [certify_execute graph (fuel + extra) state word tag
    (certify_more graph fuel extra state word tag admitted),
    certify_execute graph fuel state word tag admitted]

theorem stripPrefix_some_iff [DecidableEq Symbol] (word input rest : List Symbol) :
    stripPrefix word input = some rest ↔ input = word ++ rest := by
  induction word generalizing input with
  | nil => simp [stripPrefix]
  | cons symbol word ih =>
      cases input with
      | nil => simp [stripPrefix]
      | cons actual input =>
          by_cases same : actual = symbol
          · subst actual
            simp [stripPrefix, ih]
          · simp [stripPrefix, same]

/-- A full-token decision examines the first result only. Later full matches
cannot supersede an earlier prefix. -/
def fullToken [DecidableEq Symbol] (results : List (Tag × List Symbol)) : Option Tag :=
  match results.head? with
  | some (tag, []) => some tag
  | _ => none

theorem word_fullToken [DecidableEq Symbol] (word input : List Symbol) (tag : Tag) :
    fullToken (wordResults word tag input) = if input = word then some tag else none := by
  cases foundPrefix : stripPrefix word input with
  | none =>
      have different : input ≠ word := by
        intro same
        have found := (stripPrefix_some_iff word input []).mpr (by simpa using same)
        simp [foundPrefix] at found
      simp [wordResults, foundPrefix, fullToken, different]
  | some rest =>
      have split := (stripPrefix_some_iff word input rest).mp foundPrefix
      cases rest with
      | nil =>
          have same : input = word := by simpa using split
          simp only [wordResults, foundPrefix, fullToken, List.head?_cons]
          simp [same]
      | cons symbol rest =>
          have different : input ≠ word := by
            intro same
            have lengths := congrArg List.length split
            simp [same] at lengths
          simp [wordResults, foundPrefix, fullToken, different]

theorem certified_fullToken [DecidableEq Symbol]
    (graph : State → Node Symbol State Tag) {fuel : Nat} {state : State}
    {word : List Symbol} {tag : Tag}
    (admitted : certify graph fuel state = some (word, tag)) (input : List Symbol) :
    fullToken (execute graph fuel state input) = if input = word then some tag else none := by
  rw [certify_execute graph fuel state word tag admitted, word_fullToken]

/-- Valid UTF-8 has a unique scalar spelling, including embedded NUL. -/
theorem utf8Bytes_injective : Function.Injective utf8Bytes := by
  intro first second same
  have encoded : first.utf8Encode = second.utf8Encode := congrArg List.toByteArray same
  have decoded := congrArg ByteArray.utf8Decode? encoded
  apply List.toArray_inj
  simpa only [List.utf8Decode?_utf8Encode, Option.some.injEq] using decoded

theorem certified_utf8_fullToken (graph : State → Node Char State Tag)
    {fuel : Nat} {state : State} {word : List Char} {tag : Tag}
    (admitted : certify graph fuel state = some (word, tag)) (input : List Char) :
    fullToken (execute graph fuel state input) =
      if utf8Bytes input = utf8Bytes word then some tag else none := by
  rw [certified_fullToken graph admitted]
  simp only [utf8Bytes_injective.eq_iff]

private def literalGraph : Nat → Node Char Nat Nat
  | 0 => .epsilon 1
  | 1 => .literal 'λ' 2
  | 2 => .literal '🦀' 3
  | _ => .accept 7

theorem nonAscii_certificate : certify literalGraph 4 0 = some ("λ🦀".toList, 7) := by decide

theorem nonAscii_fullToken :
    fullToken (execute literalGraph 4 0 "λ🦀".toList) = some 7 := by decide

theorem suffix_is_not_a_token :
    execute literalGraph 4 0 "λ🦀x".toList = [(7, ['x'])] ∧
      fullToken (execute literalGraph 4 0 "λ🦀x".toList) = none := by decide

theorem cycle_not_admitted (fuel : Nat) :
    certify (fun _ : Unit => Node.epsilon ()) fuel () = (none : Option (List Char × Nat)) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact ih

theorem assertion_not_admitted (holds : List Char → Bool) (fuel : Nat) :
    certify (fun _ : Unit => Node.assertion holds ()) (fuel + 1) () =
      (none : Option (List Char × Nat)) := rfl

theorem choice_not_admitted (fuel : Nat) :
    certify (fun _ : Unit => Node.choice [(), ()]) (fuel + 1) () =
      (none : Option (List Char × Nat)) := rfl

/-- Merely finding a later full match would change selected-match meaning. -/
theorem later_full_match_cannot_replace_prefix :
    fullToken ([(1, ['b']), (2, [])] : List (Nat × List Char)) = none ∧
      fullToken ([(2, []), (1, ['b'])] : List (Nat × List Char)) = some 2 := by decide

/-- Native tag/registration identity is not licensed by equality of words. -/
theorem equal_words_different_tags :
    fullToken (wordResults ['a'] (1 : Nat) ['a']) ≠
      fullToken (wordResults ['a'] (2 : Nat) ['a']) := by decide

#print axioms certify_execute
#print axioms certify_more
#print axioms admitted_execution_bound_independent
#print axioms stripPrefix_some_iff
#print axioms word_fullToken
#print axioms certified_fullToken
#print axioms utf8Bytes_injective
#print axioms certified_utf8_fullToken
#print axioms nonAscii_certificate
#print axioms nonAscii_fullToken
#print axioms suffix_is_not_a_token
#print axioms cycle_not_admitted
#print axioms assertion_not_admitted
#print axioms choice_not_admitted
#print axioms later_full_match_cannot_replace_prefix
#print axioms equal_words_different_tags

end Mettapedia.Computability.RegularLanguages.SingleWordCertificate
