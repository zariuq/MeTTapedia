import Mettapedia.OSLF.MeTTaIL.CollectionGuardFragment
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionHandoff
import Mettapedia.OSLF.MeTTaIL.RecursiveCollectionTraceAccounting

/-!
# Source-firing coverage by prepared recursive collection matches

A source firing in a checked guard fragment supplies the ordinary matching witness.
Recursive matching at the canonical focus finds its canonical captures, and
preparation gives the ordinary replay used by the shared continuation. The
full premise history and the result's collection meaning are transported.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RecursiveCollectionFiringCoverage

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax RuleBinding ScopedRuleMatching CanonicalBags
open GeneralPremise RecursiveCollectionHandoff

def request (rule : RewriteRule) (spec : RuleBindingSpec) (bound : List TypeExpr) (source : Pattern) :
    RecursiveCollectionMachine.Request :=
  ⟨rule, spec, bound.length, .left, [], 0, [], rule.left, canon source⟩

/-- Coverage comes from an actual source firing and the independently proved
recursive matching theorem. Neither a found target nor a firing-coverage
certificate is supplied. -/
theorem firing_has_prepared_match {environment : Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} {rule : RewriteRule} {spec : RuleBindingSpec}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : Assignment}
    {history : List Event} {target : Pattern}
    (fired : RootFiring environment bound type source index trace captured completed history target)
    (selected : environment.language.rewrites[index]? = some rule)
    (specified : specification? environment index = some spec)
    (binderOk : BinderLawsFor [] environment.reflection rule)
    (increasing : IncreasingSpines rule spec)
    (guards : CollectionGuardFragment environment.provider ⟨index, rule, spec, bound, 0, 0⟩ rule.premises) :
    ∃ (work : Nat) (answer : RecursiveCollectionMachine.Answer) (prepared : Prepared)
        (target' : Pattern),
      answer ∈ (RecursiveCollectionMachine.run (request rule spec bound source) work
        (RecursiveCollectionMachine.start (request rule spec bound source))).answers ∧
      answer.assignment = canonAssignment captured ∧
      prepare (request rule spec bound source) answer = some prepared ∧
      prepared.Valid (request rule spec bound source) answer ∧
      RootFiring environment bound type prepared.source index prepared.ordinary.trace
        (canonAssignment captured) (canonAssignment completed) history target' ∧ Same target target' := by
  have original : GeneralScopedMatch.Matches rule spec bound.length .left [] 0 [] rule.left source captured := by
    cases fired with
    | @fire bound type source target index actualRule actualSpec trace captured completed history
        declared prescribed admitted sorted matched capturedTyped premises reduced targetTyped =>
      have ruleSame : actualRule = rule := Option.some.inj (declared.symm.trans selected)
      have specSame : actualSpec = spec := Option.some.inj (prescribed.symm.trans specified)
      cases ruleSame
      cases specSame
      exact matched.matching
  obtain ⟨work, finished⟩ := RecursiveCollectionMachine.finiteDrain (request rule spec bound source)
    (RecursiveCollectionMachine.start (request rule spec bound source))
  obtain ⟨answer, published, sameCapture⟩ := RecursiveCollectionMachine.completed_covers_presentation
    (request rule spec bound source) work finished increasing (by rfl) (by rfl) rfl original
  obtain ⟨prepared, computed, valid⟩ := prepare_published (request rule spec bound source) work published
  have sameSource : Same source prepared.source := by
    exact (show Same source (canon source) from (canon_idempotent source).symm).trans valid.source
  have replay : GeneralScopedMatchMachine.TracedMatches rule spec bound.length .left [] 0 [] rule.left
      prepared.source prepared.ordinary.trace (canonAssignment captured) := by
    rw [← sameCapture, ← valid.assignment]
    simpa only [request, GeneralScopedMatchMachine.Answer.Valid] using valid.matching
  obtain ⟨target', replayed, sameTarget⟩ :=
    fired.replay_collection_guards selected specified binderOk guards increasing sameSource replay
  exact ⟨work, answer, prepared, target', published, sameCapture, computed, valid, replayed, sameTarget⟩

end Mettapedia.OSLF.MeTTaIL.RecursiveCollectionFiringCoverage
