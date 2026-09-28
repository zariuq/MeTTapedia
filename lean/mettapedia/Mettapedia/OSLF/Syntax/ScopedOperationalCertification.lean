import Mettapedia.OSLF.Syntax.ScopedOperationalHistory

/-!
# Oracle certification of fixed scoped operational shapes

A freely generated rule tree retains admissible step shapes but need not have
selected its child histories from the evaluator's oracle. Certification adds
precisely that missing occurrence condition. It keeps the distinction between
free rule syntax and actually executed firings explicit.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedOperationalCertification

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (Assignment)
open Mettapedia.OSLF.Binding.ScopedStepShapes
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame
open Mettapedia.OSLF.Binding.ScopedPremiseFrameLists
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.OSLF.Binding.ScopedRuleConstructorFrame
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.ScopedOperationalHistory
open Mettapedia.TypeTheory

/-- A premise skeleton accepts a proposed child history exactly when its
stored occurrence ordinal selects that history and endpoint from the oracle.
A nonrecursive premise must receive no child history; its own base result was
already certified when the skeleton was formed. -/
def PremiseSkeleton.Selected
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premise : Premise}
    {initial final : Assignment}
    (oracle : StepOracle RuleHistory)
    (shape : PremiseSkeleton RuleHistory relEnv lang rule spec ambient
      index premise initial final)
    (childHistory : Option RuleHistory) : Prop :=
  match shape, childHistory with
  | .scopedStep _ ordinal stepShape, some evidence =>
      ((evidence, stepShape.childTarget), ordinal) ∈
        (oracle (stepShape.childJudgment.1) stepShape.childSource).zipIdx
  | .congruence ordinal stepShape, some evidence =>
      ((evidence, stepShape.childTarget), ordinal) ∈
        (oracle (stepShape.childJudgment.1) stepShape.childSource).zipIdx
  | .freshness _ _, none | .relationQuery _ _, none |
      .forAll _ _, none => True
  | _, _ => False

/-- A selected premise skeleton reconstructs an actual premise result and
frame. This is the local reverse of projecting an executable frame to a
fixed constructor; the only extra hypothesis is the exact oracle selection. -/
theorem selected_premise_has_frame
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premise : Premise}
    {initial final : Assignment}
    (oracle : StepOracle RuleHistory)
    (shape : PremiseSkeleton RuleHistory relEnv lang rule spec ambient
      index premise initial final)
    (childHistory : Option RuleHistory)
    (selected : PremiseSkeleton.Selected oracle shape childHistory) :
    ∃ event : PremiseEvent RuleHistory,
      shape.materializeEvent? childHistory = some event ∧
      Nonempty (PremiseFrame oracle relEnv lang rule spec ambient
        index premise initial final event) := by
  cases shape with
  | scopedStep wellScoped ordinal stepShape =>
      cases childHistory with
      | none => simp [PremiseSkeleton.Selected] at selected
      | some evidence =>
          refine ⟨.step index ordinal evidence, rfl, ?_⟩
          apply (premiseFrame_nonempty_iff oracle relEnv lang rule spec
            ambient index _ initial final _).mpr
          simp only [premiseResults, wellScoped, if_true]
          apply (mem_stepResults_iff_shape_selection oracle rule spec
            ambient index _ _ _ initial final _).mpr
          exact ⟨stepShape, ⟨evidence, ordinal, selected⟩, rfl⟩
  | congruence ordinal stepShape =>
      cases childHistory with
      | none => simp [PremiseSkeleton.Selected] at selected
      | some evidence =>
          refine ⟨.step index ordinal evidence, rfl, ?_⟩
          apply (premiseFrame_nonempty_iff oracle relEnv lang rule spec
            ambient index _ initial final _).mpr
          change (.step index ordinal evidence, final) ∈
            stepResults oracle rule spec ambient index 0 _ _ initial
          apply (mem_stepResults_iff_shape_selection oracle rule spec
            ambient index 0 _ _ initial final _).mpr
          exact ⟨stepShape, ⟨evidence, ordinal, selected⟩, rfl⟩
  | freshness event baseSelected =>
      exact ⟨event, rfl, ⟨.freshness baseSelected⟩⟩
  | relationQuery event baseSelected =>
      exact ⟨event, rfl, ⟨.relationQuery baseSelected⟩⟩
  | forAll event baseSelected =>
      exact ⟨event, rfl, ⟨.forAll baseSelected⟩⟩

/-- Certification of the entire ordered premise run. The recursive history
list has one entry per step premise, in author order; every such entry must
occur at the ordinal stored by its premise skeleton. -/
def RunSkeleton.Selected
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premises : List Premise}
    {initial final : Assignment}
    (oracle : StepOracle RuleHistory)
    (run : RunSkeleton RuleHistory relEnv lang rule spec ambient
      index premises initial final)
    (childHistories : List RuleHistory) : Prop :=
  match run with
  | .nil => childHistories = []
  | .cons head tail =>
      match head.child?, childHistories with
      | some _, child :: rest =>
          PremiseSkeleton.Selected oracle head (some child) ∧
            RunSkeleton.Selected oracle tail rest
      | none, _ =>
          PremiseSkeleton.Selected oracle head none ∧
            RunSkeleton.Selected oracle tail childHistories
      | some _, [] => False

/-- A certified ordered premise skeleton reconstructs a genuine evaluator
premise run with exactly its materialized events and intermediate assignments.
The result is proof relevant: repeated child endpoints retain their selected
occurrence ordinals. -/
theorem selected_run_has_frame
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premises : List Premise}
    {initial final : Assignment}
    (oracle : StepOracle RuleHistory)
    (run : RunSkeleton RuleHistory relEnv lang rule spec ambient
      index premises initial final)
    (childHistories : List RuleHistory)
    (selected : RunSkeleton.Selected oracle run childHistories) :
    ∃ events : List (PremiseEvent RuleHistory),
      run.materializeEvents? childHistories = some events ∧
      Nonempty (RunFrame oracle relEnv lang rule spec ambient
        index premises initial final events) := by
  induction run generalizing childHistories with
  | nil =>
      subst childHistories
      exact ⟨[], rfl, ⟨.nil⟩⟩
  | cons head tail inductionHypothesis =>
      cases head with
      | scopedStep wellScoped ordinal stepShape =>
          cases childHistories with
          | nil =>
              simp [RunSkeleton.Selected, PremiseSkeleton.child?] at selected
          | cons child rest =>
              obtain ⟨headSelected, tailSelected⟩ := selected
              obtain ⟨event, headEvent, ⟨headFrame⟩⟩ :=
                selected_premise_has_frame oracle
                  (.scopedStep wellScoped ordinal stepShape)
                  (some child) headSelected
              obtain ⟨events, tailEvents, ⟨tailFrame⟩⟩ :=
                inductionHypothesis rest tailSelected
              have eventEq : PremiseEvent.step _ ordinal child = event :=
                Option.some.inj headEvent
              subst event
              exact ⟨.step _ ordinal child :: events, by
                simp [RunSkeleton.materializeEvents?, tailEvents],
                  ⟨.cons headFrame tailFrame⟩⟩
      | congruence ordinal stepShape =>
          cases childHistories with
          | nil =>
              simp [RunSkeleton.Selected, PremiseSkeleton.child?] at selected
          | cons child rest =>
              obtain ⟨headSelected, tailSelected⟩ := selected
              obtain ⟨event, headEvent, ⟨headFrame⟩⟩ :=
                selected_premise_has_frame oracle
                  (.congruence ordinal stepShape)
                  (some child) headSelected
              obtain ⟨events, tailEvents, ⟨tailFrame⟩⟩ :=
                inductionHypothesis rest tailSelected
              have eventEq : PremiseEvent.step _ ordinal child = event :=
                Option.some.inj headEvent
              subst event
              exact ⟨.step _ ordinal child :: events, by
                simp [RunSkeleton.materializeEvents?, tailEvents],
                  ⟨.cons headFrame tailFrame⟩⟩
      | freshness event baseSelected =>
          obtain ⟨_, tailSelected⟩ := selected
          obtain ⟨events, tailEvents, ⟨tailFrame⟩⟩ :=
            inductionHypothesis childHistories tailSelected
          exact ⟨event :: events, by
            simp [RunSkeleton.materializeEvents?, tailEvents],
              ⟨.cons (.freshness baseSelected) tailFrame⟩⟩
      | relationQuery event baseSelected =>
          obtain ⟨_, tailSelected⟩ := selected
          obtain ⟨events, tailEvents, ⟨tailFrame⟩⟩ :=
            inductionHypothesis childHistories tailSelected
          exact ⟨event :: events, by
            simp [RunSkeleton.materializeEvents?, tailEvents],
              ⟨.cons (.relationQuery baseSelected) tailFrame⟩⟩
      | forAll event baseSelected =>
          obtain ⟨_, tailSelected⟩ := selected
          obtain ⟨events, tailEvents, ⟨tailFrame⟩⟩ :=
            inductionHypothesis childHistories tailSelected
          exact ⟨event :: events, by
            simp [RunSkeleton.materializeEvents?, tailEvents],
              ⟨.cons (.forAll baseSelected) tailFrame⟩⟩

/-- A fixed whole-rule constructor whose recursive histories pass the exact
oracle-occurrence test is an actual firing of the authored bounded executor.
This is the converse at one polynomial layer; recursive child execution is
supplied by the chosen lower-fuel oracle. -/
theorem selected_rule_executes
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern)
    (shape : RuleSkeleton RuleHistory relEnv lang ambient source target)
    (childHistories : List RuleHistory)
    (selected : RunSkeleton.Selected (rewriteAt relEnv lang fuel)
      shape.premises childHistories) :
    ∃ events : List (PremiseEvent RuleHistory),
      shape.premises.materializeEvents? childHistories = some events ∧
      (.fire shape.ruleIndex events, target) ∈
        rewriteAt relEnv lang (fuel + 1) ambient source := by
  obtain ⟨events, materialized, ⟨premiseFrame⟩⟩ :=
    selected_run_has_frame (rewriteAt relEnv lang fuel)
      shape.premises childHistories selected
  let firing : RuleFiring RuleHistory :=
    { captured := shape.captured, completed := shape.completed,
      history := events, target := target }
  have finished :
      finish? shape.rule shape.spec ambient shape.captured
        shape.completed events = some firing := by
    simp [finish?, shape.reduct, shape.resultScoped, firing]
  let frame : RuleConstructorFrame (rewriteAt relEnv lang fuel)
      relEnv lang ambient shape.rule source firing :=
    { spec := shape.spec, declared := shape.declared,
      admitted := shape.admitted, captured := shape.captured,
      selected := shape.selected, completed := shape.completed,
      history := events, premises := premiseFrame, finished := finished }
  exact ⟨events, materialized,
    (mem_rewriteAt_succ_iff_frames relEnv lang fuel ambient
      source target (.fire shape.ruleIndex events)).mpr
        ⟨shape.rule, shape.ruleIndex, shape.listed, firing,
          ⟨frame⟩, rfl, rfl⟩⟩

/-- A free tree is executable when every recursive subtree is executable and
the ordered histories decoded from those subtrees are exactly the results
selected by its root skeleton's oracle ordinals. This condition is stronger
than mere existence of a free derivation. -/
inductive CertifiedTree (relEnv : RelationEnv) (lang : LanguageDef) :
    (judgment : Judgment) →
    (presentation relEnv lang).Derivation () judgment → Prop where
  | roll {fuel ambient : Nat} {source target : Pattern}
      (shape : RuleSkeleton RuleHistory relEnv lang ambient source target)
      (children : (position : (presentation relEnv lang).polynomial.Position
        (base := ())
        (index := ⟨fuel + 1, ambient, source, target⟩) shape) →
          (presentation relEnv lang).Derivation ()
            ((presentation relEnv lang).polynomial.next
              (base := ())
              (index := ⟨fuel + 1, ambient, source, target⟩)
              shape position))
      (childCertified : ∀ position,
        CertifiedTree relEnv lang _ (children position))
      (histories : List RuleHistory)
      (decoded : List.ofFn (fun position =>
          decodeHistory? relEnv lang _ (children position)) =
            histories.map some)
      (selected : RunSkeleton.Selected (rewriteAt relEnv lang fuel)
        shape.premises histories) :
      CertifiedTree relEnv lang
        ⟨fuel + 1, ambient, source, target⟩
        (IndexedPolynomial.Fix.roll shape children)

private theorem mapM_some_histories (histories : List RuleHistory) :
    ((histories.map some).mapM id) = some histories := by
  induction histories with
  | nil => rfl
  | cons history rest inductionHypothesis =>
      simp [inductionHypothesis]

/-- An oracle-certified free tree decodes to a real authored bounded
execution. The certificate checks each child recursively and preserves the
root premise ordinals and event order. -/
theorem certified_tree_executes
    (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment)
    (tree : (presentation relEnv lang).Derivation () judgment)
    (certified : CertifiedTree relEnv lang judgment tree) :
    ∃ history : RuleHistory,
      decodeHistory? relEnv lang judgment tree = some history ∧
      (history, judgment.target) ∈
        rewriteAt relEnv lang judgment.fuel judgment.ambient
          judgment.source := by
  cases certified with
  | roll shape children childCertified histories decoded selected =>
      rename_i fuel ambient source target
      obtain ⟨events, materialized, executed⟩ :=
        selected_rule_executes relEnv lang fuel ambient source target
          shape histories selected
      refine ⟨.fire shape.ruleIndex events, ?_, executed⟩
      rw [decodeHistory?_roll relEnv lang
        ⟨fuel + 1, ambient, source, target⟩ shape children]
      change ((List.ofFn (fun position =>
        decodeHistory? relEnv lang _ (children position))).mapM id).bind
          (fun childHistories =>
            (shape.premises.materializeEvents? childHistories).map
              (RuleHistory.fire shape.ruleIndex)) =
                some (RuleHistory.fire shape.ruleIndex events)
      rw [decoded, mapM_some_histories]
      simp [materialized]

/-- The shape projected from an actual child retains its endpoint and local
context, so its stored ordinal selects the same oracle occurrence. -/
theorem shapeOfAdmitted_selected
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index localDepth : Nat} {source target : Pattern}
    {initial final : Assignment} {event : PremiseEvent RuleHistory}
    {child : ChildRequest RuleHistory}
    (oracle : StepOracle RuleHistory)
    (admitted : AdmittedChild oracle rule spec ambient index localDepth
      source target initial final event child) :
    ((child.evidence, (shapeOfAdmitted admitted).childTarget),
        child.ordinal) ∈
      (oracle (localDepth + ambient)
        (shapeOfAdmitted admitted).childSource).zipIdx := by
  rcases child with ⟨childAmbient, childSource, childTarget,
    ordinal, evidence⟩
  rcases admitted with ⟨context, instantiated, sourceScoped,
    selected, targetScoped, matched, eventEq⟩
  dsimp at context selected
  subst childAmbient
  simpa [shapeOfAdmitted] using selected

/-- Projecting an actual ordered premise run to its fixed skeleton retains
exactly the oracle selection proofs required by the certification predicate. -/
theorem selected_projected_run
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premises : List Premise}
    {initial final : Assignment}
    {history : List (PremiseEvent RuleHistory)}
    (oracle : StepOracle RuleHistory)
    (run : RunFrame oracle relEnv lang rule spec ambient
      index premises initial final history) :
    RunSkeleton.Selected oracle (RunFrame.toSkeleton run)
      ((RunFrame.childRequests run).map ChildRequest.evidence) := by
  induction run with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases head with
      | scopedStep wellScoped child admitted =>
          simp only [RunFrame.toSkeleton, RunFrame.childRequests,
            PremiseFrame.toSkeleton, PremiseFrame.childRequest?,
            Option.toList_some, List.singleton_append, List.map_cons,
            RunSkeleton.Selected, PremiseSkeleton.child?]
          exact ⟨by simpa [PremiseSkeleton.Selected,
            StepShape.childJudgment] using
              shapeOfAdmitted_selected oracle admitted,
            inductionHypothesis⟩
      | congruence child admitted =>
          simp only [RunFrame.toSkeleton, RunFrame.childRequests,
            PremiseFrame.toSkeleton, PremiseFrame.childRequest?,
            Option.toList_some, List.singleton_append, List.map_cons,
            RunSkeleton.Selected, PremiseSkeleton.child?]
          exact ⟨by simpa [PremiseSkeleton.Selected,
            StepShape.childJudgment] using
              shapeOfAdmitted_selected oracle admitted,
            inductionHypothesis⟩
      | freshness selected =>
          simpa [RunFrame.toSkeleton, RunFrame.childRequests,
            PremiseFrame.toSkeleton, PremiseFrame.childRequest?,
            RunSkeleton.Selected, PremiseSkeleton.child?,
            PremiseSkeleton.Selected] using
            inductionHypothesis
      | relationQuery selected =>
          simpa [RunFrame.toSkeleton, RunFrame.childRequests,
            PremiseFrame.toSkeleton, PremiseFrame.childRequest?,
            RunSkeleton.Selected, PremiseSkeleton.child?,
            PremiseSkeleton.Selected] using
            inductionHypothesis
      | forAll selected =>
          simpa [RunFrame.toSkeleton, RunFrame.childRequests,
            PremiseFrame.toSkeleton, PremiseFrame.childRequest?,
            RunSkeleton.Selected, PremiseSkeleton.child?,
            PremiseSkeleton.Selected] using
            inductionHypothesis

/-- Every real bounded authored execution supplies a recursively certified
free tree, not just a free tree with the same endpoints. Its decoder returns
the exact retained history, including selected premise ordinals. -/
theorem runtime_to_certified_tree
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern)
    (history : RuleHistory)
    (executed : (history, target) ∈
      rewriteAt relEnv lang fuel ambient source) :
    ∃ tree : (presentation relEnv lang).Derivation ()
        ⟨fuel, ambient, source, target⟩,
      CertifiedTree relEnv lang _ tree ∧
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
              CertifiedTree relEnv lang _ tree ∧
                decodeHistory? relEnv lang _ tree =
                  some (requestAt relEnv lang previous ambient rule
                    ruleIndex listedRule source firing frame position).evidence} :=
        Classical.choice (by
          let request := requestAt relEnv lang previous ambient rule
            ruleIndex listedRule source firing frame position
          have childExecuted := requestAt_executes relEnv lang previous
            ambient rule ruleIndex listedRule source firing frame position
          obtain ⟨tree, certified, decoded⟩ :=
            inductionHypothesis request.ambient request.source
              request.target request.evidence childExecuted
          rw [next_eq_requestAt relEnv lang previous ambient rule
            ruleIndex listedRule source firing frame position]
          exact ⟨⟨tree, certified, decoded⟩⟩)
      let children (position : (presentation relEnv lang).polynomial.Position
          (base := ())
          (index := ⟨previous + 1, ambient, source, firing.target⟩)
          shape) := (branch position).1
      have aligned :
          List.ofFn (fun position =>
            decodeHistory? relEnv lang _ (children position)) =
              (RuleConstructorFrame.childRequests frame).map
                (fun request => some request.evidence) := by
        calc
          List.ofFn (fun position =>
            decodeHistory? relEnv lang _ (children position)) =
              List.ofFn (fun position =>
                some (requestAt relEnv lang previous ambient rule
                  ruleIndex listedRule source firing frame position).evidence) := by
                    congr 1
                    funext position
                    exact (branch position).2.2
          _ = (RuleConstructorFrame.childRequests frame).map
                (fun request => some request.evidence) :=
            selected_histories_order relEnv lang previous ambient rule
              ruleIndex listedRule source firing frame
      have selected : RunSkeleton.Selected (rewriteAt relEnv lang previous)
          shape.premises
          ((RuleConstructorFrame.childRequests frame).map
            ChildRequest.evidence) := by
        simpa [shape, RuleConstructorFrame.toSkeleton,
          RuleConstructorFrame.childRequests] using
            selected_projected_run (rewriteAt relEnv lang previous)
              frame.premises
      have certified : CertifiedTree relEnv lang
          ⟨previous + 1, ambient, source, firing.target⟩
          (IndexedPolynomial.Fix.roll shape children) :=
        .roll shape children (fun position => (branch position).2.1)
          ((RuleConstructorFrame.childRequests frame).map
            ChildRequest.evidence)
          (by simpa [List.map_map, Function.comp_def] using aligned)
          selected
      refine ⟨IndexedPolynomial.Fix.roll shape children,
        certified, ?_⟩
      rw [decodeHistory?_roll relEnv lang
        ⟨previous + 1, ambient, source, firing.target⟩ shape children]
      exact decodeLayer_selected_rule relEnv lang previous ambient rule
        ruleIndex listedRule source firing frame _ aligned

/-- Exact characterization of bounded authored execution by the certified
fragment of the free scoped operational model. The certificate retains
recursive binding contexts, premise order, histories and oracle ordinals. -/
theorem certified_tree_iff_execution
    (relEnv : RelationEnv) (lang : LanguageDef)
    (fuel ambient : Nat) (source target : Pattern)
    (history : RuleHistory) :
    (∃ tree : (presentation relEnv lang).Derivation ()
        ⟨fuel, ambient, source, target⟩,
      CertifiedTree relEnv lang _ tree ∧
        decodeHistory? relEnv lang _ tree = some history) ↔
      (history, target) ∈ rewriteAt relEnv lang fuel ambient source := by
  constructor
  · rintro ⟨tree, certified, decoded⟩
    obtain ⟨actualHistory, actualDecoded, executed⟩ :=
      certified_tree_executes relEnv lang
        ⟨fuel, ambient, source, target⟩ tree certified
    have sameHistory : actualHistory = history :=
      Option.some.inj (actualDecoded.symm.trans decoded)
    subst actualHistory
    exact executed
  · exact runtime_to_certified_tree relEnv lang fuel ambient
      source target history

end Mettapedia.OSLF.Binding.ScopedOperationalCertification
