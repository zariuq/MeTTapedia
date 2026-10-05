import Mettapedia.Languages.MM0.Formats.MMB.Machine

/-!
# Controls for the MMB proof machine

A provable sort with two constants `p` and `q`, an axiom `⊢ p`, and a theorem
`p, q ⊢ p`.

* Equality is identity of allocation: reusing a saved `p` lets `Refl` close
  the obligation `p =?= p`, while two separately built copies of `p` do not.
* The unify stream of a statement lists the conclusion first and then the
  hypotheses from the last to the first; the stream in the opposite order is
  rejected.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Formats.MMB.Controls

open Mettapedia.Languages.MM0.Kernel (SortInfo)

def wff : SortInfo := { provable := true }

def constant (sort : Nat) : ExprType := ⟨sort, false, ∅⟩

def tables : Tables where
  sorts := [wff]
  terms := [⟨0, [], constant 0, none⟩, ⟨0, [], constant 0, none⟩]
  thms := [⟨[], [.term 0]⟩]

/-- The axiom `⊢ p` builds the expression `p`. -/
theorem axiom_checked : checkAssertion tables ⟨[], [.term 0]⟩ [.term 0] true = true := by
  decide

/-- **Identity**: the saved `p` is reused, so the obligation is `p =?= p` for
one allocation and `Refl` closes it. -/
theorem reused_refl_checked :
    checkAssertion tables ⟨[], [.term 0]⟩ [.termSave 0, .ref 0, .thm 0, .conv, .refl] false = true := by
  decide

/-- **Identity**: two separately built copies of `p` are different
allocations, and `Refl` fails, although the expressions are structurally
equal. -/
theorem copied_refl_rejected :
    checkAssertion tables ⟨[], [.term 0]⟩ [.term 0, .term 0, .thm 0, .conv, .refl] false = false := by
  decide

/-- The theorem `p, q ⊢ p` with its unify stream in the order the reference
verifiers read: conclusion, then the hypotheses from the last. -/
def hypothesesLastFirst : ThmEntry := ⟨[], [.term 0, .hyp, .term 1, .hyp, .term 0]⟩

/-- The same theorem with the hypotheses first, as the format description
states. -/
def hypothesesFirst : ThmEntry := ⟨[], [.hyp, .term 0, .hyp, .term 1, .term 0]⟩

/-- A proof of `p, q ⊢ p`: record both hypotheses, then use the first. -/
def useFirstHypothesis : List ProofCmd := [.term 0, .hyp, .term 1, .hyp, .ref 0]

theorem lastFirst_checked :
    checkAssertion tables hypothesesLastFirst useFirstHypothesis false = true := by
  decide

theorem hypothesesFirst_rejected :
    checkAssertion tables hypothesesFirst useFirstHypothesis false = false := by
  decide

end Mettapedia.Languages.MM0.Formats.MMB.Controls
