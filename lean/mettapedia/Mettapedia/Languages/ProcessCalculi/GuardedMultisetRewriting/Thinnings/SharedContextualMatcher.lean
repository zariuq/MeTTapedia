import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualMatcher
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Matching
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Scope

/-!
# Contextual matching reads the existing shared store

Structural matching uses `matchR` and its canonical references. The enclosing
scope is checked from the support mask. Only captured subtrees enter contextual
recovery, whose results here are parameter bodies on the existing ABT carrier.
This is a store-reading refinement, not yet a reference-only implementation of
body recovery and grafting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type} [DecidableEq Head] [DecidableEq V]

def matchShared? (store : Store Head) (p : Pattern Head V)
    (assignment : Subst V (Term Head)) (source : Ref) : Option (Subst V (Term Head)) :=
  if Scope.check source p.scope then
    (matchR p.tree store (fun _ => none) source).bind fun targets =>
      reconcile (occurrences p.tree) (unfoldSubst store targets) assignment
  else none

/-- Exact agreement with contextual tree matching; no new execution relation is introduced. -/
theorem matchShared_spec {store : Store Head} (canonical : Canonical store)
    (p : Pattern Head V) (assignment : Subst V (Term Head)) {source : Ref}
    (valid : CanonRef store source) :
    matchShared? store p assignment source = match? p assignment (unfold store source) := by
  have structural := (matchR_spec p.tree store (fun _ => none) source canonical
    (by intro o r impossible; cases impossible) valid).2
  change (matchR p.tree store (fun _ => none) source).map (unfoldSubst store) =
    matchT p.tree (fun _ => none) (unfold store source) at structural
  unfold matchShared? match?
  rw [Scope.check_spec canonical valid]
  cases matched : matchR p.tree store (fun _ => none) source with
  | none =>
    have absent : matchT p.tree (fun _ => none) (unfold store source) = none := by
      simpa [matched] using structural.symm
    simp [absent]
  | some targets =>
    have found : matchT p.tree (fun _ => none) (unfold store source) =
        some (unfoldSubst store targets) := by simpa [matched] using structural.symm
    simp [found]

theorem matchShared_exact {store : Store Head} (canonical : Canonical store)
    {p : Pattern Head V} (input : p.Input) (assignment result : Subst V (Term Head))
    {source : Ref} (valid : CanonRef store source) :
    matchShared? store p assignment source = some result ↔
      layer.Step assignment p (unfold store source) result := by
  rw [matchShared_spec canonical p assignment valid, match_exact input]

/-- Appending canonical nodes cannot change a match of an existing reference. -/
theorem matchShared_prefix {store larger : Store Head} (canonical : Canonical store)
    (largerCanonical : Canonical larger) (grows : store <+: larger)
    (p : Pattern Head V) (assignment : Subst V (Term Head)) {source : Ref}
    (valid : CanonRef store source) :
    matchShared? larger p assignment source = matchShared? store p assignment source := by
  rw [matchShared_spec largerCanonical p assignment (valid.prefix grows),
    matchShared_spec canonical p assignment valid, unfold_prefix canonical.topo grows valid.valid]

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
