import Mettapedia.OSLF.MeTTaIL.RuleBinding

/-!
# Premise-local binder prefixes at authored occurrence sites

An occurrence path records constructor binders relative to its selected
pattern. An authored step premise may already have opened binders before that
path begins. These laws account for both contributions without reconstructing
scope from a metavariable's first occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.RuleBinding

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Starting the same occurrence path under an additional binder prefix adds
exactly that prefix to every successful depth result. -/
theorem occurrenceDepthAt?_add (pattern : Pattern) :
    ∀ (path : List Nat) (depth added : Nat),
      occurrenceDepthAt? pattern path (depth + added) =
        (occurrenceDepthAt? pattern path depth).map (· + added) := by
  intro path
  induction path generalizing pattern with
  | nil =>
      intro depth added
      cases pattern <;> simp [occurrenceDepthAt?]
  | cons index path inductionHypothesis =>
      intro depth added
      cases pattern with
      | bvar _ => simp [occurrenceDepthAt?]
      | fvar _ => simp [occurrenceDepthAt?]
      | apply _ arguments =>
          cases selected : arguments[index]? with
          | none => simp [occurrenceDepthAt?, selected]
          | some argument =>
              simpa [occurrenceDepthAt?, selected] using
                inductionHypothesis argument depth added
      | lambda _ body =>
          cases index with
          | zero =>
              simp only [occurrenceDepthAt?]
              rw [show depth + added + 1 = (depth + 1) + added by omega]
              exact inductionHypothesis body (depth + 1) added
          | succ _ => simp [occurrenceDepthAt?]
      | multiLambda arity _ body =>
          cases index with
          | zero =>
              simp only [occurrenceDepthAt?]
              rw [show depth + added + arity =
                (depth + arity) + added by omega]
              exact inductionHypothesis body (depth + arity) added
          | succ _ => simp [occurrenceDepthAt?]
      | subst body replacement =>
          cases index with
          | zero =>
              simp only [occurrenceDepthAt?]
              rw [show depth + added + 1 = (depth + 1) + added by omega]
              exact inductionHypothesis body (depth + 1) added
          | succ index =>
              cases index with
              | zero =>
                  simpa [occurrenceDepthAt?] using
                    inductionHypothesis replacement depth added
              | succ _ => simp [occurrenceDepthAt?]
      | collection _ elements rest =>
          by_cases inside : index < elements.length
          · simpa [occurrenceDepthAt?, inside] using
              inductionHypothesis (elements[index]) depth added
          · simp [occurrenceDepthAt?, inside, Nat.add_comm]

/-- The executable site depth combines the selected pattern's intrinsic
address depth with the binder prefix supplied by its authored premise. -/
theorem occurrenceDepthAtSite?_eq_map
    (rule : RewriteRule) (site : RulePatternSite) (path : List Nat)
    (pattern : Pattern) (localDepth : Nat)
    (selected : sitePattern? rule site = some pattern)
    (sitePrefix : siteBinderDepth? rule site = some localDepth) :
    occurrenceDepthAtSite? rule site path =
      (occurrenceDepthAt? pattern path 0).map (· + localDepth) := by
  simp only [occurrenceDepthAtSite?, selected, sitePrefix]
  simpa [Nat.add_comm] using
    occurrenceDepthAt?_add pattern path 0 localDepth

end Mettapedia.OSLF.MeTTaIL.RuleBinding
