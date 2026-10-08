import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Ordered PeTTa answers

`Answers` is the list of Atom values observed by the whole-program judgment
and executable machine. Order and duplicate occurrences are part of the
observation. Empty answers, the value `False`, and a primitive fault have
different representations.

The former Pattern list algebra is in `PatternRewrite.Answers`, under the explicit
name `RewriteResults`. Its collection operation is a list operation; the
control forms `superpose` and `collapse` are specified in `DeclarativeSpec`.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Ordered, occurrence-preserving results of a completed evaluation. -/
abbrev Answers := List Atom

/-- A completed evaluation can return no answers. -/
def emptyAnswer : Answers := []

/-- One returned Atom value. -/
def pureAnswer (value : Atom) : Answers := [value]

@[simp] theorem emptyAnswer_eq : emptyAnswer = ([] : List Atom) := rfl

@[simp] theorem pureAnswer_eq (value : Atom) : pureAnswer value = [value] := rfl

/-- Concatenating observations keeps every occurrence in its original order. -/
theorem append_getElem_left (first second : Answers) (index : Nat)
    (before : index < first.length) :
    (first ++ second)[index]'(by simp; omega) = first[index] := by
  exact List.getElem_append_left before

/-- Two occurrences are not identified by the observation algebra. -/
theorem duplicate_answers_length (value : Atom) :
    (pureAnswer value ++ pureAnswer value).length = 2 := by
  simp

/-- Returning the Boolean False is different from returning no answers. -/
theorem false_answer_ne_empty :
    pureAnswer (.grounded (.bool false)) ≠ emptyAnswer := by
  simp

end Mettapedia.Languages.MeTTa.PeTTa
