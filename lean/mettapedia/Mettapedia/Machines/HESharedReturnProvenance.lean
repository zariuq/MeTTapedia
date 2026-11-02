import Mettapedia.Machines.HEInstructionCompletion
import Mettapedia.Languages.MeTTa.HE.EvaluatedValues.Calculus

/-!
# Completed constructor returns across a later program change

These laws use the maintained marked-term evaluator. A constructor completed
under the evaluated-values rule is held at its expression root. A later
program can rewrite the same unmarked syntax while the held value remains
unchanged. Atom-mode source returns and canonical Atom storage instead retain
raw syntax. C source-tail analysis and its carrier/ownership correspondence
remain native obligations; these theorems do not certify that analysis.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HESharedReturnProvenance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.EvaluatedValues

def box : Atom := .expression [.symbol "Box", .grounded (.int 1)]
def make : Atom := .expression [.symbol "make"]

def original : Program where
  equations := [(make, box)]
  decls := []

def changed : Program where
  equations := [(box, .grounded (.int 9))]
  decls := []

def atomRange : Program where
  equations := [(make, box)]
  decls := [⟨"make", [], .atom⟩]

/-- The output is completed by the actual constructor evaluation, not guessed
from its spelling at a later caller. -/
example : evalFuel .evaluatedValues original 12 (code make) =
    some [(code box).mark] := by rfl

/-- A held expression keeps its value under any replacement program. -/
theorem completed_survives_program_change (program : Program) (value : MAtom) :
    eval .evaluatedValues program value.mark = some [value.mark] :=
  eval_value rfl program (MAtom.isValue_mark value)

/-- The same observable Atom, still raw, is genuinely rewritten by the new
program. A universal mark-at-region-return would erase this observation. -/
example : evalFuel .evaluatedValues changed 12 (code box) =
    some [.grounded (.int 9)] := by rfl

/-- Result demand is part of the source boundary: an Atom range leaves the
same authored RHS raw, unlike ordinary interpreted constructor return. -/
example : evalFuel .evaluatedValues atomRange 12 (code make) =
    some [code box] := by rfl

/-- Persistent Atom images store the observable Atom; reconstructing its
syntax does not retain an interpreter's transient root mark. -/
example : code ((code box).mark.erase) = code box := by
  simp

end Mettapedia.Machines.HESharedReturnProvenance
