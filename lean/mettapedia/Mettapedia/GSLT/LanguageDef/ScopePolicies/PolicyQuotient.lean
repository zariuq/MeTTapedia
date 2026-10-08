import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.LanguageDef.ScopePolicies.Policies

/-!
# Presentation (B) is the quotient of presentation (A)

`GSLT.quotientBy` (`GSLT/Core/GSLTConstructions.lean`) is the existing
operation "same terms, same steps, coarser static equivalence"; its datum is a
`GSLT.Coarsening`.

## In general

Let `source` be a theory whose reduction is the reduction of its readings
along a map `read` into `target`, and whose static equivalence the map
respects.

* `GSLT.readCoarsening` — the static equivalence of the readings is a
  coarsening of `source`.
* `GSLT.quotientBy_readCoarsening` — the quotient of `source` by it is
  `target` read along the map.

## For a scope policy

* `policyCoarsening` — the coarsening of a policy's own theory on authored
  text (A) by "elaborates to statically equivalent core judgments".
* `policyRead_eq_quotient` — the quotient is the policy as an elaboration
  over the core (B), as theories and not only up to their reductions.
* `quotient_identifies_spellings` — positive: the quotient identifies
  `(new () s)` with `s`.
* `total_not_coarsening` — negative: no coarsening of (A) identifies every
  two authored terms, because a program steps and an observation does not.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Mettapedia.GSLT

namespace GSLT

universe u

/-- Two theories on one carrier with one static equivalence are equal when
their reductions hold of the same pairs. -/
private theorem mk_eq_mk {Term : Type u} {equations : Setoid Term}
    {first second : Term → Term → Prop} (same : ∀ term next, first term next ↔ second term next)
    (left : ∀ {t t' u}, equations.r t t' → first t u → ∃ u', first t' u' ∧ equations.r u u')
    (right : ∀ {t u u'}, first t u → equations.r u u' → first t u')
    (left' : ∀ {t t' u}, equations.r t t' → second t u → ∃ u', second t' u' ∧ equations.r u u')
    (right' : ∀ {t u u'}, second t u → equations.r u u' → second t u') :
    (GSLT.mk Term equations first left right) = GSLT.mk Term equations second left' right' := by
  obtain rfl : first = second := funext fun term => funext fun next => propext (same term next)
  rfl

variable {source target : GSLT.{u}}

/-- **The static equivalence of the readings, as a coarsening**: for a theory
whose reduction is the reduction of its readings along a map that respects its
static equivalence. -/
def readCoarsening (read : source.Term → target.Term)
    (respects : ∀ {first second : source.Term}, source.equations.r first second →
      target.equations.r (read first) (read second))
    (steps : ∀ term next : source.Term,
      source.rewrites term next ↔ target.rewrites (read term) (read next)) :
    source.Coarsening where
  setoid := Setoid.comap read target.equations
  coarser := fun equivalent => respects equivalent
  resp_left := by
    intro term term' next equivalent step
    obtain ⟨next', step', related⟩ :=
      target.rewrites_resp_left equivalent ((steps term next).mp step)
    exact ⟨next, (steps term' next).mpr
      (target.rewrites_resp_right step' (target.equations.iseqv.symm related)),
      (Setoid.comap read target.equations).iseqv.refl next⟩
  resp_right := fun step equivalent =>
    (steps _ _).mpr (target.rewrites_resp_right ((steps _ _).mp step) equivalent)

/-- **The quotient by the readings is the target read along the map.** -/
theorem quotientBy_readCoarsening (read : source.Term → target.Term)
    (respects : ∀ {first second : source.Term}, source.equations.r first second →
      target.equations.r (read first) (read second))
    (steps : ∀ term next : source.Term,
      source.rewrites term next ↔ target.rewrites (read term) (read next)) :
    source.quotientBy (readCoarsening read respects steps) = target.readAlong read :=
  mk_eq_mk steps (readCoarsening read respects steps).resp_left
    (readCoarsening read respects steps).resp_right (target.readAlong read).rewrites_resp_left
    (target.readAlong read).rewrites_resp_right

end GSLT

namespace LanguageDef.ScopePolicies

open Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
open Mettapedia.GSLT.LanguageDef.TemplateScope

universe u v

variable {S : Type u} {X : Type v} [DecidableEq X] [DecidableEq S]

/-- **The coarsening of a policy's own theory (A)** by "elaborates to
statically equivalent judgments of the core". -/
def policyCoarsening (c : Config) (u : X) (unit : S) : (policyGSLT c u unit).Coarsening :=
  GSLT.readCoarsening (source := policyGSLT c u unit) (target := coreGSLT S X) (elabState c u unit)
    (fun equivalent => policy_equations_read c u unit equivalent) (policy_rewrites_iff c u unit)

/-- **(B) is the quotient of (A).**  The policy as an elaboration over the core
is its own theory on authored text with the coarser static equivalence: the
same terms, the same reduction. -/
theorem policyRead_eq_quotient (c : Config) (u : X) (unit : S) :
    (policyGSLT c u unit).quotientBy (policyCoarsening c u unit) = policyRead c u unit :=
  GSLT.quotientBy_readCoarsening (source := policyGSLT c u unit) (target := coreGSLT S X)
    (elabState c u unit) (fun equivalent => policy_equations_read c u unit equivalent)
    (policy_rewrites_iff c u unit)

/-- Positive: the quotient identifies `(new () s)` with `s`, which (A) keeps
apart (`spellings_apart`). -/
theorem quotient_identifies_spellings (c : Config) (u : X) (unit : S) (s : S) :
    ((policyGSLT c u unit).quotientBy (policyCoarsening c u unit)).equations.r
      (.program (blockProgram s)) (.program (bareProgram s)) :=
  (policy_equations_strict c u unit s).1

/-- Negative: no coarsening of (A) identifies every two authored terms.  The
program `s` steps and an observation does not, and a coarsening carries a step
along the static equivalence. -/
theorem total_not_coarsening (c : Config) (u : X) (unit : S) (s : S)
    (coarsening : (policyGSLT c u unit).Coarsening) :
    ¬ ∀ first second : Authored S X, coarsening.setoid.r first second := by
  intro total
  obtain ⟨next, step, -⟩ := coarsening.resp_left
    (total (.program (bareProgram s)) (.done [])) (bareProgram_steps c u unit s)
  exact policy_rewrites_done c u unit [] next step

#print axioms GSLT.quotientBy_readCoarsening
#print axioms policyRead_eq_quotient
#print axioms quotient_identifies_spellings
#print axioms total_not_coarsening

end LanguageDef.ScopePolicies

end Mettapedia.GSLT
