import Mettapedia.GSLT.Dynamics.ContextualDeltaHandlers
import Mettapedia.GSLT.Dynamics.TypedValueGeometry

/-!
# A surface-design discriminator for contextual control

Syntax is useful here because misleadingly similar forms can hide different
semantic phases.  This module is not a fixed MeTTa surface proposal.  It gives
an elaboration target against which candidate syntaxes can be judged.

Three branch-local forms operate after isolated exploration:

* retain every contextual world;
* select one occurrence and authorize only its delta and intents; or
* merge state deltas through an explicit order-invariant resolver.

Shared-state execution is deliberately a different form.  It cannot be a
post-hoc merge option because later reads may already have observed earlier
writes.  Candidate-local value advice is also separate from whole-bag
resolution: attaching priorities preserves every occurrence, while exact
maximum is an explicit observer.

Possible concrete spellings such as `imagine`, `witness`, `cooperate`,
`share`, `advise`, and `observe` should be evaluated by whether they preserve
these phase distinctions, not by these particular names.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ContextualControlSurface

universe uState uDelta uAnswer uIntent uCandidate uValue uPriority

variable {State : Type uState} {DeltaType : Type uDelta}
variable {Answer : Type uAnswer} {Intent : Type uIntent}
variable {Candidate : Type uCandidate} {ValueType : Type uValue}
variable {Priority : Type uPriority}

/-! ## Isolated exploration followed by an explicit observation -/

/-- What an observer asks to do with already isolated worlds. -/
inductive ResolutionPolicy (DeltaType : Type uDelta)
  | retain
  | select (index : Nat)
  | merge (resolver : ContextualDeltaHandlers.AlternativeMerge DeltaType)

/-- A request carries an ordinary contextual program, its parent state, and
an explicit observation policy. -/
structure ContextualRequest (State : Type uState) (DeltaType : Type uDelta)
    (Answer : Type uAnswer) (Intent : Type uIntent) where
  program : ContextualDeltaHandlers.Program State DeltaType Answer Intent
  parent : State
  policy : ResolutionPolicy DeltaType

/-- The result tag makes information loss visible. -/
inductive ContextualResult (State : Type uState) (DeltaType : Type uDelta)
    (Answer : Type uAnswer) (Intent : Type uIntent)
  | retained (worlds : List
      (ContextualDeltaHandlers.DeltaWorld State DeltaType Answer Intent))
  | selected (world : Option
      (ContextualDeltaHandlers.Selected State DeltaType Answer Intent))
  | merged (world : Option
      (ContextualDeltaHandlers.Merged State DeltaType Answer Intent))
deriving Repr

/-- Explore first, then apply exactly the authored observation. -/
def interpretContextual
    (algebra : ContextualDeltaHandlers.DeltaAlgebra State DeltaType)
    (request : ContextualRequest State DeltaType Answer Intent) :
    ContextualResult State DeltaType Answer Intent :=
  let worlds := ContextualDeltaHandlers.runWorlds
    algebra request.program request.parent
  match request.policy with
  | .retain => .retained worlds
  | .select index =>
      .selected (ContextualDeltaHandlers.selectCommit worlds index)
  | .merge resolver =>
      .merged (ContextualDeltaHandlers.mergeWorlds
        algebra request.parent resolver worlds)

/-! ## Shared execution is not a resolution policy -/

/-- Shared execution is separated at the type level because its reads and
writes interleave during exploration. -/
structure SharedRequest (State : Type uState) (Answer : Type uAnswer)
    (Intent : Type uIntent) where
  program : ContextualEffectHandlers.Program State Answer Intent
  initial : State

def interpretShared (request : SharedRequest State Answer Intent) :
    ContextualEffectHandlers.SharedResult State Answer Intent :=
  ContextualEffectHandlers.runShared request.program request.initial

/-! ## Candidate-local advice versus whole-bag choice -/

structure GuidedOccurrence (Candidate : Type uCandidate)
    (Priority : Type uPriority) where
  occurrence : Candidate
  priority : Priority
deriving DecidableEq, Repr

/-- Advice decorates each occurrence without selecting or filtering it. -/
def advise (guidance : TypedValueGeometry.Guidance Candidate ValueType Priority)
    (occurrences : List Candidate) :
    List (GuidedOccurrence Candidate Priority) :=
  occurrences.map fun occurrence =>
    { occurrence := occurrence, priority := guidance.priority occurrence }

@[simp] theorem erase_advise
    (guidance : TypedValueGeometry.Guidance Candidate ValueType Priority)
    (occurrences : List Candidate) :
    (advise guidance occurrences).map GuidedOccurrence.occurrence = occurrences := by
  simp [advise, Function.comp_def]

/-- Exact maximum is intentionally named as an observation over the whole
bag, not as candidate-local advice. -/
noncomputable def observeMax
    (guidance : TypedValueGeometry.Guidance Candidate ValueType Nat)
    (occurrences : Multiset Candidate) : Multiset Candidate :=
  guidance.resolveMax occurrences

theorem observeMax_not_candidateLocalizable
    (guidance : TypedValueGeometry.Guidance Candidate ValueType Nat)
    {low high : Candidate} (outweighed : guidance.priority low < guidance.priority high) :
    ¬ Mettapedia.GSLT.Dynamics.CandidateLocalResolution.CandidateLocalizable
        (observeMax guidance) := by
  exact guidance.resolveMax_not_candidateLocalizable outweighed

/-! ## Positive and negative controls -/

namespace Canary

open ContextualDeltaHandlers.Canary

def retainFacts :
    ContextualRequest (Finset Nat) (Finset Nat) Bool Bool where
  program := twoFacts
  parent := {0}
  policy := .retain

def selectFact :
    ContextualRequest (Finset Nat) (Finset Nat) Bool Bool where
  program := twoFacts
  parent := {0}
  policy := .select 0

def mergeFacts :
    ContextualRequest (Finset Nat) (Finset Nat) Bool Bool where
  program := twoFacts
  parent := {0}
  policy := .merge (ContextualDeltaHandlers.joinMerge (Finset Nat))

/-- Retention exposes both contextual worlds without authorizing a commit. -/
theorem retain_keeps_both_worlds :
    interpretContextual factAlgebra retainFacts =
      .retained factWorlds :=
  rfl

/-- Selection exposes exactly the selected occurrence. -/
theorem selection_is_not_merge :
    interpretContextual factAlgebra selectFact =
      .selected (ContextualDeltaHandlers.selectCommit factWorlds 0) :=
  rfl

/-- Monotone merge retains all worlds while joining their state deltas. -/
theorem merge_keeps_answers_and_joins_state :
    interpretContextual factAlgebra mergeFacts = .merged joinedFacts ∧
      joinedFacts.map ContextualDeltaHandlers.Merged.state =
        some ({0, 1, 2} : Finset Nat) ∧
      factWorlds.map ContextualDeltaHandlers.DeltaWorld.answer =
        [false, true] := by
  constructor
  · rfl
  · exact disjoint_alternatives_merge_without_erasure

def sharedCounter :
    ContextualEffectHandlers.Program Nat (String × Nat) PUnit :=
  .choose
    (.read fun seen => .write (seen + 1) (.pure ("left", seen)))
    (.read fun seen => .write (seen + 1) (.pure ("right", seen)))

/-- Negative control: shared execution lets the second branch observe the
first branch's write, unlike isolated exploration. -/
theorem shared_reads_are_interleaved :
    (interpretShared
      ({ program := sharedCounter, initial := 0 } :
        SharedRequest Nat (String × Nat) PUnit)).answers =
      [("left", 0), ("right", 1)] := by
  decide

def boolGuidance : TypedValueGeometry.Guidance Bool Nat Nat where
  value candidate := if candidate then some 7 else none
  priorityOf := id
  fallback _ := 0

/-- Advice preserves multiplicity and order even when only one occurrence
has a value. -/
theorem advice_does_not_choose :
    (advise boolGuidance [false, true, false]).map
      GuidedOccurrence.occurrence = [false, true, false] := by
  exact erase_advise _ _

end Canary

/-! ## Axiom audit -/

#print axioms erase_advise
#print axioms observeMax_not_candidateLocalizable
#print axioms Canary.retain_keeps_both_worlds
#print axioms Canary.merge_keeps_answers_and_joins_state
#print axioms Canary.shared_reads_are_interleaved
#print axioms Canary.advice_does_not_choose

end Mettapedia.GSLT.Dynamics.ContextualControlSurface
