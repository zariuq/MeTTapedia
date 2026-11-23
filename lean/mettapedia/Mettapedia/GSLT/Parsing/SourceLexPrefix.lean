import Mettapedia.GSLT.Parsing.SourceAccumulatorLex

/-! Executable prefix checks for the quoted lexer, preserving arbitrary following
characters and preceding tokens. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.SourceAccumulatorLex

open private tokenizeAux flushToken from Algorithms.MeTTa.Simple.Parser

/-- The continuing cases of the original lexer, with only the newly emitted
tokens in reverse order. A line comment closes the remaining input. -/
def step? (point : Point) (character : Char) : Option (Point × List String) :=
  if point.inString then
    let current := character :: point.currentRev
    if point.escaped then
      some (⟨true, false, current⟩, [])
    else if character = '\\' then
      some (⟨true, true, current⟩, [])
    else if character = '"' then
      some (initialPoint, flushToken current [])
    else
      some (⟨true, false, current⟩, [])
  else if character = ';' then
    none
  else
    let tokens := flushToken point.currentRev []
    if character.isWhitespace then
      some (initialPoint, tokens)
    else if character = '(' then
      some (initialPoint, "(" :: tokens)
    else if character = ')' then
      some (initialPoint, ")" :: tokens)
    else if character = '"' then
      some (⟨true, false, ['"']⟩, tokens)
    else
      some (⟨false, false, character :: point.currentRev⟩, [])

private theorem flush_append (current : List Char) (tokens : List String) :
    flushToken current [] ++ tokens = flushToken current tokens := by
  cases current <;> rfl

theorem run_cons_of_step {before after : Point} {character : Char} {emitted : List String}
    (advance : step? before character = some (after, emitted))
    (rest : List Char) (tokens : List String) :
    run before (character :: rest) tokens = run after rest (emitted ++ tokens) := by
  obtain ⟨quoted, escaping, current⟩ := before
  cases quoted with
  | false =>
      by_cases comment : character = ';'
      · simp [step?, comment] at advance
      by_cases whitespace : character.isWhitespace = true
      · simp [step?, comment, whitespace] at advance
        obtain ⟨rfl, rfl⟩ := advance
        simp [run, tokenizeAux, Ne.symm comment, whitespace, initialPoint, flush_append]
      by_cases opening : character = '('
      · simp [step?, opening] at advance
        obtain ⟨rfl, rfl⟩ := advance
        simp [run, tokenizeAux, opening, initialPoint, flush_append]
      by_cases closing : character = ')'
      · simp [step?, closing] at advance
        obtain ⟨rfl, rfl⟩ := advance
        simp [run, tokenizeAux, closing, initialPoint, flush_append]
      by_cases delimiter : character = '"'
      · simp [step?, delimiter] at advance
        obtain ⟨rfl, rfl⟩ := advance
        simp [run, tokenizeAux, delimiter, flush_append]
      · simp [step?, comment, whitespace, opening, closing, delimiter] at advance
        obtain ⟨rfl, rfl⟩ := advance
        simp [run, tokenizeAux, Ne.symm comment, whitespace, opening, closing, delimiter]
  | true =>
      cases escaping with
      | true =>
          obtain ⟨rfl, rfl⟩ := Option.some.inj advance
          rfl
      | false =>
          by_cases escape : character = '\\'
          · simp [step?, escape] at advance
            obtain ⟨rfl, rfl⟩ := advance
            simp [run, tokenizeAux, escape]
          by_cases delimiter : character = '"'
          · simp [step?, delimiter] at advance
            obtain ⟨rfl, rfl⟩ := advance
            simp [run, tokenizeAux, delimiter, initialPoint, flush_append]
          · simp [step?, escape, delimiter] at advance
            obtain ⟨rfl, rfl⟩ := advance
            simp [run, tokenizeAux, escape, delimiter]

theorem run_cons_of_comment {before : Point} {character : Char}
    (stops : step? before character = none) (rest : List Char) (tokens : List String) :
    run before (character :: rest) tokens = run before [] tokens := by
  obtain ⟨quoted, escaping, current⟩ := before
  cases quoted with
  | false =>
      by_cases comment : character = ';'
      · simp [run, tokenizeAux, comment]
      · simp [step?, comment] at stops
        split at stops
        · contradiction
        · split at stops
          · contradiction
          · split at stops
            · contradiction
            · split at stops <;> contradiction
  | true =>
      simp only [step?, if_true] at stops
      split at stops
      · contradiction
      · split at stops
        · contradiction
        · split at stops <;> contradiction

private def prefixAux (point : Point) (tokens : List String) :
    List Char → Option (Point × List String)
  | [] => some (point, tokens)
  | character :: rest => do
      let (next, emitted) ← step? point character
      prefixAux next (emitted ++ tokens) rest

private theorem prefixAux_sound (input : List Char) {before after : Point}
    {accumulated emitted : List String}
    (checked : prefixAux before accumulated input = some (after, emitted))
    (rest : List Char) (tokens : List String) :
    run before (input ++ rest) (accumulated ++ tokens) = run after rest (emitted ++ tokens) := by
  induction input generalizing before accumulated with
  | nil =>
      simp [prefixAux] at checked
      obtain ⟨rfl, rfl⟩ := checked
      rfl
  | cons character input ih =>
      cases advancement : step? before character with
      | none => simp [prefixAux, advancement] at checked
      | some step =>
          obtain ⟨next, produced⟩ := step
          simp only [prefixAux, advancement] at checked
          rw [List.cons_append, run_cons_of_step advancement, ← List.append_assoc]
          exact ih checked

/-- The boundary point and reverse of the tokens emitted while reading a prefix. -/
def prefix? (before : Point) (input : List Char) : Option (Point × List String) :=
  prefixAux before [] input

theorem agreement_of_prefix {before after : Point} {input : List Char} {emitted : List String}
    (checked : prefix? before input = some (after, emitted.reverse)) :
    Agreement before after input emitted := by
  intro rest tokens
  simpa only [List.nil_append] using prefixAux_sound input checked rest tokens

example : prefix? initialPoint ['"', ';'] = some (⟨true, false, [';', '"']⟩, []) :=
  by decide +kernel

example : prefix? initialPoint [';', 'a'] = none := by decide +kernel

end Mettapedia.GSLT.Parsing.SourceAccumulatorLex
