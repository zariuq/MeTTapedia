import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceRuns

/-!
# Controls of the REFL correspondence at the name frame: the two interfaces and the readout

Closed quotes (the corrected semantics' REFL, `canonicalBag`) and named quotes (the literal REFL, the reduct as
written, represented by `predotU`) are two interfaces at the name frame `QN`. Here, what separates them:

* `closed_quote_misses`, `closed_quote_misses_example`: for every closed reduct with a variable, the corrected
  quote and the hosted made quote are different names modulo the name laws (H-REFL1's
  `canonicalBag_not_made_quote`, carried to `QN`); `ground_quotes_agree_example`: on a reduct without variables
  they are one name.
* `instantiated_partner_refused_name`: the hosting at `QN` refuses, at every opening, the partner quoting the
  instance of the made listener's binder, which the literal source meets
  (`ReflUniform.Controls.instantiated_partner_meets_in_source`) and the corrected executable refuses
  (`ReflUniform.Controls.corrected_refuses_guard_quotes`).
* `listener_canonical_form`: the corrected listener's quote is wrapped (`pPar [c]`), so it is not in the canonical
  form of the quotient (`bagCanon` unwraps); the name frame equates it with the unwrapped name, which the corrected
  semantics compares as written and tells apart.
* `two_reducts_two_names`, `dead_grandchild_two_steps`: the readout of a hosted state needs commit points and dead
  locations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero pPar nQuote tProc pReflect demoChan)
open MeTTaOperationsComm (psubst PSubst pvars psubst_pFor psubst_nQuote psubst_tProc psubst_pZero)
open MeTTaCalculus.Corrected (canonicalBag)
open OneFrame (embed)
open ReflQuotient (BagLaws bagCanon)
open ReflNames (NameLaws QN QNE nameLaws_tProc bagLaws_of_nameLaws nameLaws_of_eq commAtN comm_reads_name)
open ReflUniform (predotU canonicalBag_not_made_quote)
open ReflUniform.Controls (yv reductY reductZero rowsInstance)
open FiniteProgram (program)

/-! ## Closed against named quotes -/

/-- `tProc` is no bag node: modulo the bag laws it is related argument-wise. -/
theorem bagLaws_of_tProc {a b : Pattern} (h : BagLaws (tProc a) (tProc b)) : BagLaws a b := by
  rw [ReflQuotient.bagLaws_iff] at h ⊢
  simpa [tProc, ReflQuotient.bagCanon_apply] using h

/-- **Closed quotes miss the made quote at the name frame**: for every closed reduct with a variable, the corrected
REFL's quote and the hosted made quote are different names modulo the name laws. -/
theorem closed_quote_misses (R : Pattern) (closed : pvars (MeTTaCalculus.Corrected.close R) = []) {y : String}
    (binds : y ∈ pvars R) : ¬ NameLaws (tProc (canonicalBag R)) (tProc (predotU R)) :=
  fun h => canonicalBag_not_made_quote R closed binds (bagLaws_of_tProc (bagLaws_of_nameLaws h))

/-- Its instance: the reduct `for(y <- @0)y`. -/
theorem closed_quote_misses_example : ¬ NameLaws (tProc (canonicalBag reductY)) (tProc (predotU reductY)) :=
  closed_quote_misses reductY (by decide +kernel) (y := "y") (by decide +kernel)

/-- **On a reduct without variables both interfaces give one name**: `for(0 <- @0)0`. -/
theorem ground_quotes_agree_example : NameLaws (tProc (canonicalBag reductZero)) (tProc (predotU reductZero)) :=
  nameLaws_tProc (quote_closed_ground reductZero (by decide +kernel))

/-! ## Named quotes keep the instantiated-partner separation at the name frame -/

theorem bagLaws_pFor_body {t x k t' x' k' : Pattern} (h : BagLaws (pFor t x k) (pFor t' x' k')) : BagLaws k k' := by
  rw [ReflQuotient.bagLaws_iff] at h ⊢
  simp [pFor, ReflQuotient.bagCanon_apply] at h
  exact h.2.2

theorem nQuote_not_zero (p : Pattern) : ¬ BagLaws (nQuote p) pZero := by
  rw [ReflQuotient.bagLaws_iff]
  simp [nQuote, pZero, ReflQuotient.bagCanon_apply]

/-- **The hosting at the name frame refuses the instantiated partner**: the made listener `for(@(for(y <- @0)@y) <- @0)0`
and the partner `for(@(for(0 <- @0)0) <- @0)0` do not communicate at any opening: no solution makes the quoted
continuations `@y` and `0` one name. -/
theorem instantiated_partner_refused_name (ρ : PSubst) :
    ¬ (RuleSyntax.step QN ℕ QNE program).Admits (s := embed rowsInstance Comm.Controls.start) (commAtN ρ 0 1 2 3) := by
  intro admitted
  obtain ⟨_, σ, solved⟩ := ((RuleSyntax.admits_iff _).mp admitted).2.2.2.1
  obtain ⟨-, unify, -⟩ := comm_reads_name rowsInstance (tProc (pFor yv demoChan (nQuote yv))) (tProc reductZero)
    demoChan demoChan pZero pZero Comm.Controls.start 0 1 2 3
    (fun σ _ => nameLaws_of_eq (congrArg (psubst σ) (by decide +kernel :
      rowsInstance 0 = pFor (tProc (pFor yv demoChan (nQuote yv))) demoChan pZero)))
    (fun σ _ => nameLaws_of_eq (congrArg (psubst σ) (by decide +kernel :
      rowsInstance 1 = pFor (tProc reductZero) demoChan pZero)))
    (by decide) ρ solved
  have bag := bagLaws_of_nameLaws unify
  rw [psubst_tProc, psubst_tProc] at bag
  have inner : BagLaws (psubst σ (pFor yv demoChan (nQuote yv))) (psubst σ (pFor pZero demoChan pZero)) :=
    bagLaws_of_tProc bag
  rw [psubst_pFor, psubst_pFor] at inner
  have body := bagLaws_pFor_body inner
  rw [psubst_nQuote, psubst_pZero] at body
  exact nQuote_not_zero _ body

/-! ## The listener's canonical form -/

/-- **The corrected listener's quote is not in the quotient's canonical form**: `canonicalBag` wraps the one
component of `for(0 <- @0)0` and `bagCanon` unwraps it; the name frame equates the wrapped quote with the unwrapped
name, which differ as written. -/
theorem listener_canonical_form :
    canonicalBag reductZero = pPar [reductZero] ∧
      bagCanon (tProc (canonicalBag reductZero)) ≠ tProc (canonicalBag reductZero) ∧
      NameLaws (tProc (canonicalBag reductZero)) (tProc reductZero) ∧
      tProc (canonicalBag reductZero) ≠ tProc reductZero := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## The readout needs commit points and dead locations -/

/-- An input on `@@0` with the pattern `0`. -/
def inputOther : Pattern := pFor pZero (nQuote demoChan) pZero

/-- **Commit points**: `i | i | i' | i'` has two COMM reducts, `0 | 0 | i' | i'` and `i | i | 0 | 0`, whose quotes
are different names. Once the child has taken one, no second step is admitted at it
(`ReflLocatedStep.done_phase_step`); reading the reflection as unreduced after the commit would claim both. -/
theorem two_reducts_two_names :
    ¬ NameLaws (tProc (pPar [pZero, pZero, inputOther, inputOther]))
      (tProc (pPar [reductZero, reductZero, pZero, pZero])) := by
  decide +kernel

/-- A reflection inside the child: `@0?(i' | i')`. -/
def innerReflection : Pattern := pReflect demoChan (pPar [inputOther, inputOther])

/-- The listener of its one step: `for(@(0 | 0) <- @0) 0`. -/
def innerListener : Pattern := pFor (tProc (pPar [pZero, pZero])) demoChan pZero

/-- **Dead locations**: in `i | i | @0?(i' | i')` the COMM gives `0 | 0 | @0?(i' | i')` and the inner REFL gives
`i | i | for(@(0 | 0) <- @0) 0`. Reading the inner reflection through its child after the COMM committed would give
`0 | 0 | for(@(0 | 0) <- @0) 0`, a different name from both. -/
theorem dead_grandchild_two_steps :
    ¬ NameLaws (tProc (pPar [pZero, pZero, innerListener])) (tProc (pPar [pZero, pZero, innerReflection])) ∧
      ¬ NameLaws (tProc (pPar [pZero, pZero, innerListener]))
        (tProc (pPar [reductZero, reductZero, innerListener])) := by
  constructor <;> decide +kernel

#print axioms bagLaws_of_tProc
#print axioms closed_quote_misses
#print axioms closed_quote_misses_example
#print axioms ground_quotes_agree_example
#print axioms instantiated_partner_refused_name
#print axioms listener_canonical_form
#print axioms two_reducts_two_names
#print axioms dead_grandchild_two_steps

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence.Controls
