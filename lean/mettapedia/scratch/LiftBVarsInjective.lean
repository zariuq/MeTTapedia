import Mettapedia.OSLF.MeTTaIL.Substitution

namespace Mettapedia.OSLF.MeTTaIL.Substitution

open Mettapedia.OSLF.MeTTaIL.Syntax

private def unliftBVars (cutoff shift : Nat) : Pattern → Pattern
  | .bvar index =>
      if cutoff + shift ≤ index then .bvar (index - shift) else .bvar index
  | .fvar name => .fvar name
  | .apply constructor arguments =>
      .apply constructor (arguments.map (unliftBVars cutoff shift))
  | .lambda name body =>
      .lambda name (unliftBVars (cutoff + 1) shift body)
  | .multiLambda arity names body =>
      .multiLambda arity names (unliftBVars (cutoff + arity) shift body)
  | .subst body replacement =>
      .subst (unliftBVars (cutoff + 1) shift body)
        (unliftBVars cutoff shift replacement)
  | .collection collectionType elements rest =>
      .collection collectionType (elements.map (unliftBVars cutoff shift)) rest
termination_by pattern => sizeOf pattern

private theorem unliftBVars_liftBVars (cutoff shift : Nat) :
    ∀ pattern, unliftBVars cutoff shift (liftBVars cutoff shift pattern) =
      pattern := by
  intro pattern
  induction pattern using Pattern.inductionOn generalizing cutoff with
  | hbvar index =>
      by_cases shifted : index ≥ cutoff
      · simp [liftBVars, shifted, unliftBVars]
      · have notRaised : ¬ cutoff + shift ≤ index := by omega
        simp [liftBVars, shifted, unliftBVars, notRaised]
  | hfvar name => simp [liftBVars, unliftBVars]
  | happly constructor arguments inductionHypothesis =>
      simp only [liftBVars, unliftBVars, List.map_map]
      congr 1
      calc
        List.map (unliftBVars cutoff shift ∘ liftBVars cutoff shift)
            arguments =
            List.map id arguments := List.map_congr_left (fun argument
              membership => inductionHypothesis argument membership cutoff)
        _ = arguments := List.map_id arguments
  | hlambda name body inductionHypothesis =>
      simp only [liftBVars, unliftBVars]
      exact congrArg (Pattern.lambda name)
        (inductionHypothesis (cutoff + 1))
  | hmultiLambda arity names body inductionHypothesis =>
      simp only [liftBVars, unliftBVars]
      exact congrArg (Pattern.multiLambda arity names)
        (inductionHypothesis (cutoff + arity))
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      simp only [liftBVars, unliftBVars]
      exact congrArg₂ Pattern.subst
        (bodyHypothesis (cutoff + 1))
        (replacementHypothesis cutoff)
  | hcollection collectionType elements rest inductionHypothesis =>
      simp only [liftBVars, unliftBVars, List.map_map]
      congr 1
      calc
        List.map (unliftBVars cutoff shift ∘ liftBVars cutoff shift)
            elements =
            List.map id elements := List.map_congr_left (fun element
              membership => inductionHypothesis element membership cutoff)
        _ = elements := List.map_id elements

theorem liftBVars_injective_canary (cutoff shift : Nat) :
    Function.Injective (liftBVars cutoff shift) := by
  intro left right equality
  have := congrArg (unliftBVars cutoff shift) equality
  simpa only [unliftBVars_liftBVars] using this

end Mettapedia.OSLF.MeTTaIL.Substitution
