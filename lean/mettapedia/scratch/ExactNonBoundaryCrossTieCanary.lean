import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

/-!
# Atom-shape dispatch for the nonboundary cross-tie inversion

The rigid-frame restoration inversion consumes, for every semantic atom, the
disjunction "restores rigidly at every depth" or "restores together with the
selected quote application".  This file proves that disjunction from the three
lawful value shapes the actual planner produces: a free variable, an
application with a disallowed head, or a closed selected-quote application
whose free variables are fixed by the assignment.  It also records why the
abstract bare-bound-variable counterexample normal can never satisfy the
certified closure invariant.
-/

namespace Mettapedia.GSLT.LanguageDef
namespace NonBoundaryCrossTie

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A closed assignment value is inserted unchanged at every depth. -/
theorem substituteAt_fvar_eq_assignment_of_scopedAtZero
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (name : String)
    (closed : (assignment name).isWellScopedAt 0 = true) (depth : Nat) :
    ReflectiveContextSupport.substituteAt profile support assignment depth
        (.fvar name) = assignment name := by
  simp only [ReflectiveContextSupport.substituteAt]
  exact Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_eq_self_of_isWellScopedAt
    closed

/-- Supported substitution fixes any pattern whose free variables the
assignment maps to themselves. -/
theorem substituteAt_eq_self_of_assignment_fixed
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment) (pattern : Pattern) :
    ∀ depth,
      (∀ name ∈ pattern.freeFvarNames, assignment name = .fvar name) →
      ReflectiveContextSupport.substituteAt profile support assignment depth
        pattern = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index =>
      intro depth _fixed
      simp [ReflectiveContextSupport.substituteAt]
  | hfvar name =>
      intro depth fixed
      simp only [ReflectiveContextSupport.substituteAt]
      rw [fixed name (by simp [Pattern.freeFvarNames])]
      simp [Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  | happly constructor arguments inductionHypothesis =>
      intro depth fixed
      simp only [ReflectiveContextSupport.substituteAt, Pattern.apply.injEq,
        true_and]
      conv_rhs => rw [← List.map_id arguments]
      refine List.map_congr_left ?_
      intro argument membership
      exact inductionHypothesis argument membership _ (fun name nameMembership =>
        fixed name (by
          simp only [Pattern.freeFvarNames, List.mem_flatMap]
          exact ⟨argument, membership, nameMembership⟩))
  | hlambda binder body inductionHypothesis =>
      intro depth fixed
      simp only [ReflectiveContextSupport.substituteAt, Pattern.lambda.injEq,
        true_and]
      exact inductionHypothesis _ (fun name nameMembership =>
        fixed name (by simpa [Pattern.freeFvarNames] using nameMembership))
  | hmultiLambda arity binders body inductionHypothesis =>
      intro depth fixed
      simp only [ReflectiveContextSupport.substituteAt,
        Pattern.multiLambda.injEq, true_and]
      exact inductionHypothesis _ (fun name nameMembership =>
        fixed name (by simpa [Pattern.freeFvarNames] using nameMembership))
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro depth fixed
      simp only [ReflectiveContextSupport.substituteAt, Pattern.subst.injEq]
      exact ⟨bodyHypothesis _ (fun name nameMembership =>
          fixed name (by
            simp only [Pattern.freeFvarNames, List.mem_append]
            exact Or.inl nameMembership)),
        replacementHypothesis _ (fun name nameMembership =>
          fixed name (by
            simp only [Pattern.freeFvarNames, List.mem_append]
            exact Or.inr nameMembership))⟩
  | hcollection collectionType elements rest inductionHypothesis =>
      intro depth fixed
      simp only [ReflectiveContextSupport.substituteAt,
        Pattern.collection.injEq, true_and, and_true]
      conv_rhs => rw [← List.map_id elements]
      refine List.map_congr_left ?_
      intro element membership
      exact inductionHypothesis element membership _ (fun name nameMembership =>
        fixed name (by
          simp only [Pattern.freeFvarNames, List.mem_append, List.mem_flatMap]
          exact Or.inl ⟨element, membership, nameMembership⟩))

/-- **Shape dispatch.**  The three lawful semantic-atom value shapes induce
the exact rigid-or-quote behaviour demanded by the rigid-frame restoration
inversion: either the restored atom is, at every depth, a free variable or an
application with a disallowed head, or the atom restores together with a
selected-quote application uniformly. -/
theorem atom_rigidOrQuote_of_assignment_shape
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (allowed : String → Prop) (quoteConstructor : String) (name : String)
    (shape :
      (∃ restoredName, assignment name = .fvar restoredName) ∨
      (∃ constructor arguments, ¬ allowed constructor ∧
        assignment name = .apply constructor arguments) ∨
      ((assignment name).isWellScopedAt 0 = true ∧
        (∀ inner ∈ (assignment name).freeFvarNames,
          assignment inner = .fvar inner) ∧
        ∃ arguments, assignment name = .apply quoteConstructor arguments)) :
    (∀ depth,
      (∃ restoredName,
          ReflectiveContextSupport.substituteAt profile support assignment
            depth (.fvar name) = .fvar restoredName) ∨
        ∃ constructor arguments,
          ¬ allowed constructor ∧
          ReflectiveContextSupport.substituteAt profile support assignment
            depth (.fvar name) = .apply constructor arguments) ∨
      ∃ arguments,
        ReflectiveContextSupport.RestoresTogether profile support assignment
          (.fvar name) (.apply quoteConstructor arguments) := by
  rcases shape with ⟨restoredName, valueFvar⟩ |
      ⟨constructor, arguments, outside, valueApply⟩ |
      ⟨closed, fixedInner, arguments, valueQuote⟩
  · left
    intro depth
    left
    exact ⟨restoredName, by
      simp [ReflectiveContextSupport.substituteAt, valueFvar,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]⟩
  · left
    intro depth
    right
    refine ⟨constructor, arguments.map
      (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
        (depth - (support name).length)), outside, ?_⟩
    simp [ReflectiveContextSupport.substituteAt, valueApply,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  · right
    refine ⟨arguments, ?_⟩
    intro depth
    rw [substituteAt_fvar_eq_assignment_of_scopedAtZero profile support
        assignment name closed depth, valueQuote,
      substituteAt_eq_self_of_assignment_fixed profile support assignment
        (.apply quoteConstructor arguments) depth
        (fun inner membership => fixedInner inner (by
          rw [valueQuote]; exact membership))]

/-- A profile-quote application restores identically at every depth: the
quote resets its children's available depth, so the ambient depth never
reaches them. -/
theorem substituteAt_applyQuote_constant
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    {quoteConstructor : String}
    (quoteIsQuote : ReflectiveContextSupport.isQuoteConstructor profile
      quoteConstructor = true)
    (arguments : List Pattern) (first second : Nat) :
    ReflectiveContextSupport.substituteAt profile support assignment first
        (.apply quoteConstructor arguments) =
      ReflectiveContextSupport.substituteAt profile support assignment second
        (.apply quoteConstructor arguments) := by
  simp [ReflectiveContextSupport.substituteAt, quoteIsQuote]

/-- **Fixed-quote dispatch.**  The three lawful semantic-atom value shapes —
without any free-variable side condition — induce a rigid-or-fixed-quote
behaviour: at every depth the restored atom is a free variable, an
application with a disallowed head, or one fixed selected-quote
application. -/
theorem atom_rigidOrFixedQuote_of_assignment_shape
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    (allowed : String → Prop) (quoteConstructor : String) (name : String)
    (shape :
      (∃ restoredName, assignment name = .fvar restoredName) ∨
      (∃ constructor arguments, ¬ allowed constructor ∧
        assignment name = .apply constructor arguments) ∨
      ((assignment name).isWellScopedAt 0 = true ∧
        ∃ arguments, assignment name = .apply quoteConstructor arguments)) :
    (∀ depth,
      (∃ restoredName,
          ReflectiveContextSupport.substituteAt profile support assignment
            depth (.fvar name) = .fvar restoredName) ∨
        ∃ constructor arguments,
          ¬ allowed constructor ∧
          ReflectiveContextSupport.substituteAt profile support assignment
            depth (.fvar name) = .apply constructor arguments) ∨
      ∃ arguments, ∀ depth,
        ReflectiveContextSupport.substituteAt profile support assignment
          depth (.fvar name) = .apply quoteConstructor arguments := by
  rcases shape with ⟨restoredName, valueFvar⟩ |
      ⟨constructor, arguments, outside, valueApply⟩ |
      ⟨closed, arguments, valueQuote⟩
  · left
    intro depth
    left
    exact ⟨restoredName, by
      simp [ReflectiveContextSupport.substituteAt, valueFvar,
        Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]⟩
  · left
    intro depth
    right
    refine ⟨constructor, arguments.map
      (Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars 0
        (depth - (support name).length)), outside, ?_⟩
    simp [ReflectiveContextSupport.substituteAt, valueApply,
      Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars]
  · right
    refine ⟨arguments, fun depth => ?_⟩
    rw [substituteAt_fvar_eq_assignment_of_scopedAtZero profile support
      assignment name closed depth, valueQuote]

/-- **The quote leaf of the inversion, fixedness-free.**  An atom restoring
to one fixed profile-quote application restores together with any pattern
whose substitution it meets at a single depth, provided that pattern is a
selected-quote application: both sides are depth-constant, so one meeting
point extends to all depths. -/
theorem restoresTogether_of_fixedQuoteAtom_of_eq_at_depth
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    {quoteConstructor : String}
    (quoteIsQuote : ReflectiveContextSupport.isQuoteConstructor profile
      quoteConstructor = true)
    {name : String} {atomArguments frameArguments : List Pattern}
    (fixedQuote : ∀ depth,
      ReflectiveContextSupport.substituteAt profile support assignment depth
        (.fvar name) = .apply quoteConstructor atomArguments)
    {keyDepth : Nat}
    (equalAt : ReflectiveContextSupport.substituteAt profile support
        assignment keyDepth (.fvar name) =
      ReflectiveContextSupport.substituteAt profile support assignment
        keyDepth (.apply quoteConstructor frameArguments)) :
    ReflectiveContextSupport.RestoresTogether profile support assignment
      (.fvar name) (.apply quoteConstructor frameArguments) := by
  intro depth
  rw [fixedQuote depth, ← fixedQuote keyDepth, equalAt]
  exact substituteAt_applyQuote_constant profile support assignment
    quoteIsQuote frameArguments keyDepth depth

/-- A fixed-quote atom meeting an application frame node at one depth forces
that node's head to be the quote constructor: supported substitution
preserves application heads. -/
theorem applyHead_eq_quote_of_fixedQuoteAtom_of_eq_at_depth
    (profile : Mettapedia.OSLF.MeTTaIL.Reflection.ReflectionProfile)
    (support : ContextSupport.Support)
    (assignment : ContextSupport.Assignment)
    {quoteConstructor : String} {name : String}
    {atomArguments : List Pattern}
    (fixedQuote : ∀ depth,
      ReflectiveContextSupport.substituteAt profile support assignment depth
        (.fvar name) = .apply quoteConstructor atomArguments)
    {frameConstructor : String} {frameArguments : List Pattern}
    {keyDepth : Nat}
    (equalAt : ReflectiveContextSupport.substituteAt profile support
        assignment keyDepth (.fvar name) =
      ReflectiveContextSupport.substituteAt profile support assignment
        keyDepth (.apply frameConstructor frameArguments)) :
    frameConstructor = quoteConstructor := by
  rw [fixedQuote keyDepth] at equalAt
  simp only [ReflectiveContextSupport.substituteAt] at equalAt
  exact ((Pattern.apply.inj equalAt).1).symm

/-- The bare bound-variable normal of the abstract support-mismatch
counterexample is not closed at depth zero, so it can never arise as the
normal of an actual certified name boundary, whose closure at zero is a
theorem. -/
theorem bvar_not_isWellScopedAt_zero (index : Nat) :
    (Pattern.bvar index).isWellScopedAt 0 = false := by
  simp [Pattern.isWellScopedAt]

end NonBoundaryCrossTie
end Mettapedia.GSLT.LanguageDef
