import Mettapedia.OSLF.Syntax.ScopedOperationalFreeModel

/-!
# Reading histories from the free scoped operational algebra

Each free constructor contains an authored rule index and an ordered premise
skeleton. Its recursive children supply the histories used to reconstruct
the selected premise events. A free tree with missing or extra event data
does not decode. Decoding alone does not certify oracle selection; that is a
separate correspondence with the executable relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedOperationalHistory

open Mettapedia.TypeTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation

/-- Interpret one constructor whose children have already been assigned
optional histories. The finite premise list fixes their position order. -/
def decodeLayer (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment)
    (shape : (presentation relEnv lang).polynomial.Shape () judgment)
    (children : (position :
      (presentation relEnv lang).polynomial.Position shape) →
        Option RuleHistory) : Option RuleHistory :=
  match judgment with
  | ⟨0, _, _, _⟩ => nomatch shape
  | ⟨_ + 1, _, _, _⟩ =>
      ((List.ofFn children).mapM id).bind fun childHistories =>
        (shape.premises.materializeEvents? childHistories).map
          (.fire shape.ruleIndex)

/-- The free rule tree determines at most one retained runtime-history
candidate. The result may be absent when its premise-event arity fails. -/
noncomputable def decodeHistory? (relEnv : RelationEnv)
    (lang : LanguageDef) :
    ∀ judgment,
      (presentation relEnv lang).Derivation () judgment →
        Option RuleHistory :=
  IndexedPolynomial.Fix.fold (presentation relEnv lang).polynomial
    (fun _ judgment layer =>
      decodeLayer relEnv lang judgment layer.1 layer.2) ()

/-- Decoding a free constructor reads its children first, then reconstructs
the parent's ordered event list from its stored premise skeleton. -/
theorem decodeHistory?_roll (relEnv : RelationEnv)
    (lang : LanguageDef) (judgment : Judgment)
    (shape : (presentation relEnv lang).polynomial.Shape () judgment)
    (children : (position :
      (presentation relEnv lang).polynomial.Position shape) →
        (presentation relEnv lang).Derivation ()
          ((presentation relEnv lang).polynomial.next shape position)) :
    decodeHistory? relEnv lang judgment
        (IndexedPolynomial.Fix.roll shape children) =
      decodeLayer relEnv lang judgment shape
        (fun position => decodeHistory? relEnv lang _ (children position)) := by
  simp [decodeHistory?, IndexedPolynomial.Fix.fold_roll]

private theorem mapM_selected_histories
    (requests : List (ChildRequest RuleHistory)) :
    ((requests.map fun child => some child.evidence).mapM id) =
      some (requests.map ChildRequest.evidence) := by
  induction requests with
  | nil => rfl
  | cons request rest inductionHypothesis =>
      simp [inductionHypothesis]

/-- If recursive children decode to the exact selected request histories in
order, the fixed constructor decodes to the executor's exact parent history.
The hypothesis is positional; equal child judgments cannot exchange events. -/
theorem decodeLayer_selected_rule
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (rule : RewriteRule) (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (source : Pattern) (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient rule source firing)
    (children : (position :
      (presentation relEnv lang).polynomial.Position
        (base := ())
        (index := ⟨fuel + 1, ambient, source, firing.target⟩)
        (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)) →
          Option RuleHistory)
    (aligned : List.ofFn children =
      (RuleConstructorFrame.childRequests frame).map fun child =>
        some child.evidence) :
    decodeLayer relEnv lang
      ⟨fuel + 1, ambient, source, firing.target⟩
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)
      children = some (.fire ruleIndex firing.history) := by
  change ((List.ofFn children).mapM id).bind
      (fun childHistories =>
        ((RuleConstructorFrame.toSkeleton ruleIndex listedRule frame).premises
          |>.materializeEvents? childHistories).map
            (RuleHistory.fire ruleIndex)) =
              some (RuleHistory.fire ruleIndex firing.history)
  rw [aligned, mapM_selected_histories]
  simp [RuleConstructorFrame.materializeEvents_selected
    ruleIndex listedRule frame]
  exact (finish?_history rule frame.spec ambient frame.captured
    frame.completed frame.history firing frame.finished).symm

/-- A selected recursive request viewed as the smaller-fuel indexed
judgment at which the executor supplies its child history. -/
def childJudgment (fuel : Nat) (request : ChildRequest RuleHistory) :
    Judgment :=
  ⟨fuel, request.ambient, request.source, request.target⟩

/-- The polynomial's ordered positions are exactly the executable frame's
selected recursive requests, including duplicate endpoint judgments. -/
theorem presentation_premises_eq_requests
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (rule : RewriteRule) (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (source : Pattern) (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient rule source firing) :
    (presentation relEnv lang).premises ()
      ⟨fuel + 1, ambient, source, firing.target⟩
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame) =
        (RuleConstructorFrame.childRequests frame).map
          (childJudgment fuel) := by
  simp [presentation, childJudgment,
    RuleConstructorFrame.toSkeleton_children_eq_requests
      ruleIndex listedRule frame]

/-- Select the exact executable child request at one finite constructor
position; repeated equal judgments remain different positions. -/
def requestAt (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (rule : RewriteRule) (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (source : Pattern) (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient rule source firing)
    (position : (presentation relEnv lang).polynomial.Position
      (base := ())
      (index := ⟨fuel + 1, ambient, source, firing.target⟩)
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)) :
    ChildRequest RuleHistory :=
  let requests := RuleConstructorFrame.childRequests frame
  requests[position.val]'(by
    have bounded : position.val <
        ((presentation relEnv lang).premises ()
          ⟨fuel + 1, ambient, source, firing.target⟩
          (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)).length :=
      position.isLt
    have sameLength :
        ((presentation relEnv lang).premises ()
          ⟨fuel + 1, ambient, source, firing.target⟩
          (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)).length =
            requests.length := by
      rw [presentation_premises_eq_requests relEnv lang fuel ambient
        rule ruleIndex listedRule source firing frame]
      simp [requests]
    calc
      position.val <
          ((presentation relEnv lang).premises ()
            ⟨fuel + 1, ambient, source, firing.target⟩
            (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)).length :=
        bounded
      _ = requests.length := sameLength)

/-- The polynomial's child index at a position is exactly the smaller-fuel
judgment of the selected request at that same position. -/
theorem next_eq_requestAt
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (rule : RewriteRule) (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (source : Pattern) (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient rule source firing)
    (position : (presentation relEnv lang).polynomial.Position
      (base := ())
      (index := ⟨fuel + 1, ambient, source, firing.target⟩)
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)) :
    (presentation relEnv lang).polynomial.next
      (base := ())
      (index := ⟨fuel + 1, ambient, source, firing.target⟩)
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)
      position =
        childJudgment fuel
          (requestAt relEnv lang fuel ambient rule ruleIndex
            listedRule source firing frame position) := by
  let shape := RuleConstructorFrame.toSkeleton ruleIndex listedRule frame
  let requests := RuleConstructorFrame.childRequests frame
  have premiseEq := presentation_premises_eq_requests relEnv lang
    fuel ambient rule ruleIndex listedRule source firing frame
  have requestBound : position.val < requests.length := by
    have lengthEq := congrArg List.length premiseEq
    have bounded : position.val <
        ((presentation relEnv lang).premises ()
          ⟨fuel + 1, ambient, source, firing.target⟩ shape).length :=
      position.isLt
    calc
      position.val <
          ((presentation relEnv lang).premises ()
            ⟨fuel + 1, ambient, source, firing.target⟩ shape).length :=
        bounded
      _ = requests.length := by simpa using lengthEq
  have mappedBound : position.val <
      (requests.map (childJudgment fuel)).length := by
    simpa using requestBound
  change ((presentation relEnv lang).premises ()
      ⟨fuel + 1, ambient, source, firing.target⟩ shape).get position =
        childJudgment fuel
          (requestAt relEnv lang fuel ambient rule ruleIndex
            listedRule source firing frame position)
  calc
    ((presentation relEnv lang).premises ()
        ⟨fuel + 1, ambient, source, firing.target⟩ shape).get position =
      (requests.map (childJudgment fuel))[position.val]'mappedBound :=
        List.getElem_of_eq premiseEq position.isLt
    _ = childJudgment fuel (requests[position.val]'requestBound) :=
      List.getElem_map (childJudgment fuel)
    _ = childJudgment fuel
        (requestAt relEnv lang fuel ambient rule ruleIndex
          listedRule source firing frame position) := rfl

/-- The request at a particular constructor position is a selected oracle
occurrence at precisely its recorded result-list ordinal. -/
theorem requestAt_selected
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (rule : RewriteRule) (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (source : Pattern) (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient rule source firing)
    (position : (presentation relEnv lang).polynomial.Position
      (base := ())
      (index := ⟨fuel + 1, ambient, source, firing.target⟩)
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)) :
    let request := requestAt relEnv lang fuel ambient rule ruleIndex
      listedRule source firing frame position
    ((request.evidence, request.target), request.ordinal) ∈
      (rewriteAt relEnv lang fuel request.ambient request.source).zipIdx := by
  apply RunFrame.childRequests_selected frame.premises
  unfold requestAt
  exact List.getElem_mem _

/-- Forgetting an oracle-list ordinal leaves an actual recursive execution
at the selected request's own context and endpoints. -/
theorem requestAt_executes
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (rule : RewriteRule) (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (source : Pattern) (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient rule source firing)
    (position : (presentation relEnv lang).polynomial.Position
      (base := ())
      (index := ⟨fuel + 1, ambient, source, firing.target⟩)
      (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame)) :
    let request := requestAt relEnv lang fuel ambient rule ruleIndex
      listedRule source firing frame position
    (request.evidence, request.target) ∈
      rewriteAt relEnv lang fuel request.ambient request.source := by
  let request := requestAt relEnv lang fuel ambient rule ruleIndex
    listedRule source firing frame position
  change (request.evidence, request.target) ∈
    rewriteAt relEnv lang fuel request.ambient request.source
  obtain ⟨bound, equality⟩ := List.mem_zipIdx'
    (requestAt_selected relEnv lang fuel ambient rule ruleIndex
      listedRule source firing frame position)
  rw [equality]
  exact List.getElem_mem bound

/-- Reading the selected evidence at each polynomial position gives exactly
the original ordered list, not merely a permutation of matching endpoints. -/
theorem selected_histories_order
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (rule : RewriteRule) (ruleIndex : Nat)
    (listedRule : (rule, ruleIndex) ∈ lang.rewrites.zipIdx)
    (source : Pattern) (firing : RuleFiring RuleHistory)
    (frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient rule source firing) :
    List.ofFn (fun position :
      (presentation relEnv lang).polynomial.Position
        (base := ())
        (index := ⟨fuel + 1, ambient, source, firing.target⟩)
        (RuleConstructorFrame.toSkeleton ruleIndex listedRule frame) =>
      some (requestAt relEnv lang fuel ambient rule ruleIndex
        listedRule source firing frame position).evidence) =
      (RuleConstructorFrame.childRequests frame).map fun request =>
        some request.evidence := by
  let shape := RuleConstructorFrame.toSkeleton ruleIndex listedRule frame
  let requests := RuleConstructorFrame.childRequests frame
  have sameLength := congrArg List.length
    (presentation_premises_eq_requests relEnv lang fuel ambient
      rule ruleIndex listedRule source firing frame)
  have premiseLength :
      ((presentation relEnv lang).premises ()
        ⟨fuel + 1, ambient, source, firing.target⟩ shape).length =
        requests.length := by
    simpa [shape, requests] using sameLength
  change List.ofFn (fun position : Fin
    (((presentation relEnv lang).premises ()
      ⟨fuel + 1, ambient, source, firing.target⟩ shape).length) =>
      some (requestAt relEnv lang fuel ambient rule ruleIndex
        listedRule source firing frame position).evidence) =
    requests.map fun request => some request.evidence
  conv_lhs => rw [List.ofFn_congr premiseLength]
  simpa only [requestAt, requests, Fin.val_cast] using
    (List.ofFn_getElem_eq_map requests
      (fun request => some request.evidence))

/-- Every bounded execution has a free derivation whose positional decoder
recovers the exact retained firing history. In particular, two premise
results with equal endpoints cannot exchange their evidence or ordinals. -/
theorem runtime_to_free_with_history
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern)
    (history : RuleHistory)
    (executed : (history, target) ∈
      rewriteAt relEnv lang fuel ambient source) :
    ∃ tree : (presentation relEnv lang).Derivation ()
        ⟨fuel, ambient, source, target⟩,
      decodeHistory? relEnv lang _ tree = some history := by
  classical
  induction fuel generalizing ambient source target history with
  | zero =>
      simp [rewriteAt] at executed
  | succ previous inductionHypothesis =>
      obtain ⟨rule, ruleIndex, listedRule, firing, ⟨frame⟩,
          historyEq, targetEq⟩ :=
        (mem_rewriteAt_succ_iff_frames relEnv lang previous ambient
          source target history).mp executed
      subst target
      subst history
      let shape := RuleConstructorFrame.toSkeleton ruleIndex
        listedRule frame
      let branch (position : (presentation relEnv lang).polynomial.Position
          (base := ())
          (index := ⟨previous + 1, ambient, source, firing.target⟩)
          shape) :
          {tree : (presentation relEnv lang).Derivation ()
            ((presentation relEnv lang).polynomial.next
              (base := ())
              (index := ⟨previous + 1, ambient, source, firing.target⟩)
              shape position) //
              decodeHistory? relEnv lang _ tree =
                some (requestAt relEnv lang previous ambient rule
                  ruleIndex listedRule source firing frame position).evidence} :=
        Classical.choice (by
          let request := requestAt relEnv lang previous ambient rule
            ruleIndex listedRule source firing frame position
          have childExecuted := requestAt_executes relEnv lang previous
            ambient rule ruleIndex listedRule source firing frame position
          obtain ⟨tree, decoded⟩ := inductionHypothesis request.ambient
            request.source request.target request.evidence childExecuted
          rw [next_eq_requestAt relEnv lang previous ambient rule
            ruleIndex listedRule source firing frame position]
          exact ⟨⟨tree, decoded⟩⟩)
      refine ⟨IndexedPolynomial.Fix.roll shape
        (fun position => (branch position).1), ?_⟩
      rw [decodeHistory?_roll relEnv lang
        ⟨previous + 1, ambient, source, firing.target⟩ shape
          (fun position => (branch position).1)]
      apply decodeLayer_selected_rule relEnv lang previous ambient rule
        ruleIndex listedRule source firing frame
      calc
        List.ofFn (fun position =>
          decodeHistory? relEnv lang _ (branch position).1) =
            List.ofFn (fun position =>
              some (requestAt relEnv lang previous ambient rule
                ruleIndex listedRule source firing frame position).evidence) := by
                  congr 1
                  funext position
                  exact (branch position).2
        _ = (RuleConstructorFrame.childRequests frame).map
              (fun request => some request.evidence) :=
          selected_histories_order relEnv lang previous ambient rule
            ruleIndex listedRule source firing frame

end Mettapedia.OSLF.Binding.ScopedOperationalHistory
