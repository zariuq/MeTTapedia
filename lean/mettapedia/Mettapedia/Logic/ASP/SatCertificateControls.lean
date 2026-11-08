import Mettapedia.GSLT.Logic.PropositionalLRATActions

/-!
# The C SAT personality's refutations under the verified LRAT checker

CeTTa's answer-set solver also solves clause sets (its SAT personality): the
clauses are its inputs, named from 1 in order, and a refutation is a list of
RUP steps over them, each with its hints, which is an LRAT proof.  The proof
below is the one the C solver emits for three pigeons and two holes, verbatim:

    10 -2 0 7 8 3 6 2 0
    11 0 10 1 4 5 3 9 2 0

DIMACS variable `v` is the native literal index `v - 1`.  The action-by-action
checker, whose acceptance is proved to refute the clause set, accepts it in the
kernel, so the clause set is unsatisfiable; the proof without its last step, the
same proof against a satisfiable clause set, and a proof whose hint names no
clause are refused.  The standard library's whole-proof checker gives the same
verdicts at run time (`verdicts`); its hash tables depend on the host word width,
so it is no kernel computation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.SatCertificateControls

open Mettapedia.GSLT.Logic
open Mettapedia.GSLT.Logic.PropositionalFormula
open Mettapedia.GSLT.Logic.PropositionalLRATActions
open Mettapedia.GSLT.Logic.PropositionalLRATActions.Controls (actions)

/-- Pigeon `i` in hole `j` is variable `2 i + j` (pigeons 0 to 2, holes 0 and 1):
each pigeon in some hole, no hole holding two pigeons. -/
def pigeons32 : CNF :=
  [[.pos 0, .pos 1], [.pos 2, .pos 3], [.pos 4, .pos 5],
   [.neg 0, .neg 2], [.neg 0, .neg 4], [.neg 2, .neg 4],
   [.neg 1, .neg 3], [.neg 1, .neg 5], [.neg 3, .neg 5]]

/-- The C solver's refutation of `pigeons32`. -/
def cProof : PropositionalLRAT.Proof :=
  #[.addRup 10 #[-2] #[7, 8, 3, 6, 2], .addEmpty 11 #[10, 1, 4, 5, 3, 9, 2]]

theorem cProof_accepted : check pigeons32 (actions cProof) = true := by decide

theorem pigeons32_unsat : PropositionalResolution.Unsat pigeons32 :=
  check_sound cProof_accepted

/-- Without the step deriving the empty clause, the proof refutes nothing. -/
theorem truncated_refused :
    check pigeons32 (actions #[.addRup 10 #[-2] #[7, 8, 3, 6, 2]]) = false := by
  decide

/-- Each pigeon in some hole with no exclusions: a clause set with a model
(every variable true), for which no proof is accepted, this one included. -/
def somewhere : CNF :=
  [[.pos 0, .pos 1], [.pos 2, .pos 3], [.pos 4, .pos 5]]

theorem satisfiable_refused (proof : List Action) : check somewhere proof = false := by
  cases accepted : check somewhere proof with
  | false => rfl
  | true =>
      have impossible := check_sound accepted (fun _ => true)
      simp [somewhere, CNF.sat, Clause.sat, Literal.sat] at impossible

/-- A hint naming no clause makes the step fail. -/
theorem unknown_hint_refused :
    check pigeons32
      (actions #[.addRup 10 #[-2] #[7, 8, 3, 6, 2], .addEmpty 11 #[10, 1, 4, 5, 3, 9, 42]]) =
      false := by
  decide

/-- Run-time comparison with the standard library's whole-proof checker. -/
def verdicts : List (String × Bool) :=
  [("C refutation", PropositionalLRAT.checker.check pigeons32 cProof),
   ("truncated", !(PropositionalLRAT.checker.check pigeons32 #[.addRup 10 #[-2] #[7, 8, 3, 6, 2]])),
   ("satisfiable", !(PropositionalLRAT.checker.check somewhere cProof)),
   ("unknown hint", !(PropositionalLRAT.checker.check pigeons32
      #[.addRup 10 #[-2] #[7, 8, 3, 6, 2], .addEmpty 11 #[10, 1, 4, 5, 3, 9, 42]]))]

end Mettapedia.Logic.ASP.SatCertificateControls
