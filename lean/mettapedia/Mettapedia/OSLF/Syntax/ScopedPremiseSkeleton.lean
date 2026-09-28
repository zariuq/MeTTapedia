import Mettapedia.OSLF.Syntax.ScopedPremiseFrameLists
import Mettapedia.OSLF.Syntax.ScopedStepShapes

/-!
# Oracle-independent signatures of conditional premise lists

The recursive evidence used by an executor is not part of a rule shape.
Each admissible premise contributes at most one child judgment; root premises
retain their selected base evidence. A recursive premise retains its ordinal,
which distinguishes repeated oracle occurrences with equal endpoints. A whole
ordered skeleton records the intermediate assignments and finite child list.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedPremiseSkeleton

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedStepShapes
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame
open Mettapedia.OSLF.Binding.ScopedPremiseFrameLists

/-- One admissible premise stripped of its recursive evidence. Scoped and
congruence premises store the exact child shape and selected ordinal. Base
premises retain the selected root result and its result-list ordinal. -/
inductive PremiseSkeleton (Evidence : Type)
    (relEnv : RelationEnv) (lang : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient index : Nat) :
    Premise → Assignment → Assignment → Type where
  | scopedStep {step initial final}
      (wellScoped : step.isWellScopedAt ambient = true)
      (ordinal : Nat)
      (shape : StepShape rule spec ambient index step.binders.length
        step.source step.target initial final) :
      PremiseSkeleton Evidence relEnv lang rule spec ambient index
        (.scopedStep step) initial final
  | congruence {source target initial final}
      (ordinal : Nat)
      (shape : StepShape rule spec ambient index 0
        source target initial final) :
      PremiseSkeleton Evidence relEnv lang rule spec ambient index
        (.congruence source target) initial final
  | freshness {condition initial final}
      (event : PremiseEvent Evidence)
      (selected : (event, final) ∈
        rootResults relEnv lang spec ambient index
          (.freshness condition) initial) :
      PremiseSkeleton Evidence relEnv lang rule spec ambient index
        (.freshness condition) initial final
  | relationQuery {relation arguments initial final}
      (event : PremiseEvent Evidence)
      (selected : (event, final) ∈
        rootResults relEnv lang spec ambient index
          (.relationQuery relation arguments) initial) :
      PremiseSkeleton Evidence relEnv lang rule spec ambient index
        (.relationQuery relation arguments) initial final
  | forAll {collection parameter body initial final}
      (event : PremiseEvent Evidence)
      (selected : (event, final) ∈
        rootResults relEnv lang spec ambient index
          (.forAll collection parameter body) initial) :
      PremiseSkeleton Evidence relEnv lang rule spec ambient index
        (.forAll collection parameter body) initial final

/-- The optional recursive judgment requested by one premise shape. -/
def PremiseSkeleton.child? {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premise : Premise}
    {initial final : Assignment}
    (shape : PremiseSkeleton Evidence relEnv lang rule spec ambient index
      premise initial final) : Option (Nat × Pattern × Pattern) :=
  match shape with
  | .scopedStep _ _ stepShape => some stepShape.childJudgment
  | .congruence _ stepShape => some stepShape.childJudgment
  | .freshness _ _ | .relationQuery _ _ | .forAll _ _ => none

/-- The position of a selected recursive result is part of its constructor
label. A target model may use it to retain multiplicity at equal endpoints. -/
def PremiseSkeleton.selectedOrdinal? {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premise : Premise}
    {initial final : Assignment}
    (shape : PremiseSkeleton Evidence relEnv lang rule spec ambient index
      premise initial final) : Option Nat :=
  match shape with
  | .scopedStep _ ordinal _ => some ordinal
  | .congruence ordinal _ => some ordinal
  | .freshness _ _ | .relationQuery _ _ | .forAll _ _ => none

/-- Two selections at distinct positions remain distinct constructors,
even when their source, target, and matching assignment coincide. -/
theorem PremiseSkeleton.scopedStep_ordinals_distinct {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {step : ScopedStepPremise}
    {initial final : Assignment}
    (wellScoped : step.isWellScopedAt ambient = true)
    (shape : StepShape rule spec ambient index step.binders.length
      step.source step.target initial final)
    {first second : Nat} (distinct : first ≠ second) :
    (PremiseSkeleton.scopedStep (Evidence := Evidence) (relEnv := relEnv)
      (lang := lang) wellScoped first shape) ≠
    (PremiseSkeleton.scopedStep wellScoped second shape) := by
  intro equal
  have ordinalEqual := congrArg PremiseSkeleton.selectedOrdinal? equal
  exact distinct (Option.some.inj ordinalEqual)

/-- A scoped child's context is exactly the caller's context extended by
the premise-local binders, independently of recursive evidence. -/
theorem scoped_child_context {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {step : ScopedStepPremise}
    {initial final : Assignment}
    (shape : PremiseSkeleton Evidence relEnv lang rule spec ambient index
      (.scopedStep step) initial final) :
    ∃ source target,
      shape.child? = some (step.binders.length + ambient, source, target) := by
  cases shape with
  | scopedStep _ _ stepShape =>
      exact ⟨stepShape.childSource, stepShape.childTarget, rfl⟩

/-- Forget the recursive oracle selection while preserving a real
premise's admissible shape and base evidence. -/
noncomputable def PremiseFrame.toSkeleton {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premise : Premise} {initial final : Assignment}
    {event : PremiseEvent Evidence}
    (frame : PremiseFrame oracle relEnv lang rule spec ambient index
      premise initial final event) :
    PremiseSkeleton Evidence relEnv lang rule spec ambient index
      premise initial final :=
  match frame with
  | .scopedStep wellScoped child admitted =>
      .scopedStep wellScoped child.ordinal (shapeOfAdmitted admitted)
  | .congruence child admitted =>
      .congruence child.ordinal (shapeOfAdmitted admitted)
  | .freshness selected => .freshness _ selected
  | .relationQuery selected => .relationQuery _ selected
  | .forAll selected => .forAll _ selected

/-- The selected recursive request of one actual premise, if any. Its
evidence and ordinal are retained in addition to its scoped endpoints. -/
def PremiseFrame.childRequest? {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premise : Premise} {initial final : Assignment}
    {event : PremiseEvent Evidence}
    (frame : PremiseFrame oracle relEnv lang rule spec ambient index
      premise initial final event) : Option (ChildRequest Evidence) :=
  match frame with
  | .scopedStep _ child _ | .congruence child _ => some child
  | .freshness _ | .relationQuery _ | .forAll _ => none

/-- Projecting a selected child to its judgment agrees exactly with the
oracle-independent skeleton projection. -/
theorem PremiseFrame.toSkeleton_childRequest {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premise : Premise} {initial final : Assignment}
    {event : PremiseEvent Evidence}
    (frame : PremiseFrame oracle relEnv lang rule spec ambient index
      premise initial final event) :
    (PremiseFrame.toSkeleton frame).child? =
      (PremiseFrame.childRequest? frame).map fun child =>
        (child.ambient, child.source, child.target) := by
  cases frame with
  | scopedStep _ child admitted =>
      rcases child with ⟨childAmbient, childSource, childTarget,
        ordinal, evidence⟩
      rcases admitted with ⟨context, _, _, _, _, _, _⟩
      dsimp at context
      subst childAmbient
      simp [PremiseFrame.toSkeleton, PremiseFrame.childRequest?,
        PremiseSkeleton.child?, shapeOfAdmitted,
        StepShape.childJudgment]
  | congruence child admitted =>
      rcases child with ⟨childAmbient, childSource, childTarget,
        ordinal, evidence⟩
      rcases admitted with ⟨context, _, _, _, _, _, _⟩
      dsimp at context
      subst childAmbient
      simp [PremiseFrame.toSkeleton, PremiseFrame.childRequest?,
        PremiseSkeleton.child?, shapeOfAdmitted,
        StepShape.childJudgment]
  | freshness _ => rfl
  | relationQuery _ => rfl
  | forAll _ => rfl

/-- The exact selected request, not merely some result with equal endpoints,
occurs in the oracle list at its recorded ordinal. -/
theorem PremiseFrame.childRequest_selected {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premise : Premise} {initial final : Assignment}
    {event : PremiseEvent Evidence}
    (frame : PremiseFrame oracle relEnv lang rule spec ambient index
      premise initial final event)
    (child : ChildRequest Evidence)
    (listed : child ∈ (PremiseFrame.childRequest? frame).toList) :
    ((child.evidence, child.target), child.ordinal) ∈
      (oracle child.ambient child.source).zipIdx := by
  cases frame with
  | scopedStep _ request admitted =>
      simp [PremiseFrame.childRequest?] at listed
      subst child
      exact admitted.2.2.2.1
  | congruence request admitted =>
      simp [PremiseFrame.childRequest?] at listed
      subst child
      exact admitted.2.2.2.1
  | freshness _ => simp [PremiseFrame.childRequest?] at listed
  | relationQuery _ => simp [PremiseFrame.childRequest?] at listed
  | forAll _ => simp [PremiseFrame.childRequest?] at listed

private theorem member_of_zipIdx {Value : Type}
    {values : List Value} {value : Value} {ordinal : Nat}
    (selected : (value, ordinal) ∈ values.zipIdx) : value ∈ values := by
  obtain ⟨bound, equality⟩ := List.mem_zipIdx' selected
  rw [equality]
  exact List.getElem_mem bound

/-- Each recursive child of a projected premise skeleton is an actual
selected result of the oracle at exactly that child's scoped judgment. -/
theorem PremiseFrame.toSkeleton_child_selected {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premise : Premise} {initial final : Assignment}
    {event : PremiseEvent Evidence}
    (frame : PremiseFrame oracle relEnv lang rule spec ambient index
      premise initial final event)
    (requested : Nat × Pattern × Pattern)
    (listed : requested ∈ (PremiseFrame.toSkeleton frame).child?.toList) :
    ∃ evidence,
      (evidence, requested.2.2) ∈
        oracle requested.1 requested.2.1 := by
  cases frame with
  | scopedStep _ child admitted =>
      rcases child with ⟨childAmbient, childSource, childTarget,
        ordinal, evidence⟩
      rcases admitted with ⟨context, _, _, selected, _, _, _⟩
      dsimp at context selected
      subst childAmbient
      simp [PremiseFrame.toSkeleton, PremiseSkeleton.child?,
        shapeOfAdmitted, StepShape.childJudgment] at listed
      subst requested
      exact ⟨evidence, by simpa using member_of_zipIdx selected⟩
  | congruence child admitted =>
      rcases child with ⟨childAmbient, childSource, childTarget,
        ordinal, evidence⟩
      rcases admitted with ⟨context, _, _, selected, _, _, _⟩
      dsimp at context selected
      subst childAmbient
      simp [PremiseFrame.toSkeleton, PremiseSkeleton.child?,
        shapeOfAdmitted, StepShape.childJudgment] at listed
      subst requested
      exact ⟨evidence, by simpa using member_of_zipIdx selected⟩
  | freshness _ => simp [PremiseFrame.toSkeleton,
      PremiseSkeleton.child?] at listed
  | relationQuery _ => simp [PremiseFrame.toSkeleton,
      PremiseSkeleton.child?] at listed
  | forAll _ => simp [PremiseFrame.toSkeleton,
      PremiseSkeleton.child?] at listed

/-- An ordered list of premise shapes retains every intermediate assignment
but none of the recursive child evidence. -/
inductive RunSkeleton (Evidence : Type)
    (relEnv : RelationEnv) (lang : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (ambient : Nat) :
    Nat → List Premise → Assignment → Assignment → Type where
  | nil {index initial} :
      RunSkeleton Evidence relEnv lang rule spec ambient index [] initial initial
  | cons {index premise rest initial intermediate final}
      (head : PremiseSkeleton Evidence relEnv lang rule spec ambient index
        premise initial intermediate)
      (tail : RunSkeleton Evidence relEnv lang rule spec ambient
        (index + 1) rest intermediate final) :
      RunSkeleton Evidence relEnv lang rule spec ambient index
        (premise :: rest) initial final

/-- The finite ordered list of recursive child judgments. Repeated child
endpoints occupy separate list positions. -/
def RunSkeleton.children {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
    {premises : List Premise} {initial final : Assignment}
    (run : RunSkeleton Evidence relEnv lang rule spec ambient index
      premises initial final) : List (Nat × Pattern × Pattern) :=
  match run with
  | .nil => []
  | .cons head tail => head.child?.toList ++ tail.children

/-- Reconstruct one premise event from its constructor and, in a recursive
case, the precise history of its selected child. -/
def PremiseSkeleton.materializeEvent?
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premise : Premise}
    {initial final : Assignment}
    (shape : PremiseSkeleton RuleHistory relEnv lang rule spec
      ambient index premise initial final)
    (childHistory : Option RuleHistory) : Option (PremiseEvent RuleHistory) :=
  match shape with
  | .scopedStep _ ordinal _ =>
      childHistory.map (.step index ordinal)
  | .congruence ordinal _ =>
      childHistory.map (.step index ordinal)
  | .freshness event _ | .relationQuery event _ | .forAll event _ =>
      some event

/-- Reconstruct the ordered event list from a skeleton and histories at its
ordered recursive positions. The function rejects a missing or extra child;
it does not consult an oracle. -/
def RunSkeleton.materializeEvents?
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premises : List Premise}
    {initial final : Assignment}
    (run : RunSkeleton RuleHistory relEnv lang rule spec ambient
      index premises initial final)
    (childHistories : List RuleHistory) :
    Option (List (PremiseEvent RuleHistory)) :=
  match run, childHistories with
  | .nil, [] => some []
  | .nil, _ :: _ => none
  | .cons head tail, histories =>
      match head with
      | .scopedStep _ ordinal _ =>
          match histories with
          | [] => none
          | childHistory :: restHistories => do
              let rest ← tail.materializeEvents? restHistories
              some (.step index ordinal childHistory :: rest)
      | .congruence ordinal _ =>
          match histories with
          | [] => none
          | childHistory :: restHistories => do
              let rest ← tail.materializeEvents? restHistories
              some (.step index ordinal childHistory :: rest)
      | .freshness event _ | .relationQuery event _ | .forAll event _ => do
          let rest ← tail.materializeEvents? histories
          some (event :: rest)

/-- A single scoped step contributes exactly one recursive judgment in its
declared local binder extension. -/
theorem RunSkeleton.single_scoped_child {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {step : ScopedStepPremise}
    {initial final : Assignment}
    (run : RunSkeleton Evidence relEnv lang rule spec ambient index
      [.scopedStep step] initial final) :
    ∃ source target,
      run.children = [(step.binders.length + ambient, source, target)] := by
  cases run with
  | cons head tail =>
      cases tail
      obtain ⟨source, target, childEq⟩ :=
        scoped_child_context head
      exact ⟨source, target, by
        simp [RunSkeleton.children, childEq]⟩

/-- The single-premise law also applies when the list is obtained from an
authored rule declaration rather than written literally in the index. -/
theorem RunSkeleton.single_scoped_child_of_eq {Evidence : Type}
    {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {ambient index : Nat} {premises : List Premise}
    {initial final : Assignment}
    (run : RunSkeleton Evidence relEnv lang rule spec ambient index
      premises initial final) {step : ScopedStepPremise}
    (single : premises = [.scopedStep step]) :
    ∃ source target,
      run.children = [(step.binders.length + ambient, source, target)] := by
  subst premises
  exact RunSkeleton.single_scoped_child run

/-- At most one recursive child is requested by each authored premise. -/
theorem RunSkeleton.children_length_le {Evidence : Type}
    {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premises : List Premise} {initial final : Assignment}
    (run : RunSkeleton Evidence relEnv lang rule spec ambient index
      premises initial final) :
    run.children.length ≤ premises.length := by
  induction run with
  | nil => simp [children]
  | cons head tail ih =>
      simp only [children, List.length_append, List.length_cons]
      have headBound : head.child?.toList.length ≤ 1 := by
        cases head.child? <;> simp
      omega

/-- Every actual ordered premise run projects to an oracle-independent
skeleton with the same assignments and authored premise order. -/
noncomputable def RunFrame.toSkeleton {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premises : List Premise} {initial final : Assignment}
    {history : List (PremiseEvent Evidence)}
    (run : RunFrame oracle relEnv lang rule spec ambient
      index premises initial final history) :
    RunSkeleton Evidence relEnv lang rule spec ambient
      index premises initial final :=
  match run with
  | .nil => .nil
  | .cons head tail =>
      .cons (PremiseFrame.toSkeleton head) (RunFrame.toSkeleton tail)

/-- The ordered recursive requests selected by a complete actual premise
run, retaining each request's history and oracle ordinal. -/
def RunFrame.childRequests {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premises : List Premise} {initial final : Assignment}
    {history : List (PremiseEvent Evidence)}
    (run : RunFrame oracle relEnv lang rule spec ambient
      index premises initial final history) : List (ChildRequest Evidence) :=
  match run with
  | .nil => []
  | .cons head tail =>
      (PremiseFrame.childRequest? head).toList ++
        RunFrame.childRequests tail

/-- Forgetting selected evidence maps the requests in their original order
to precisely the child positions of the fixed rule skeleton. -/
theorem RunFrame.toSkeleton_children_eq_requests {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premises : List Premise} {initial final : Assignment}
    {history : List (PremiseEvent Evidence)}
    (run : RunFrame oracle relEnv lang rule spec ambient
      index premises initial final history) :
    (RunFrame.toSkeleton run).children =
      (RunFrame.childRequests run).map fun child =>
        (child.ambient, child.source, child.target) := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
      simp only [RunFrame.toSkeleton, RunSkeleton.children,
        RunFrame.childRequests, List.map_append]
      rw [PremiseFrame.toSkeleton_childRequest]
      simp [Option.toList_map, ih]

/-- Every retained recursive request is selected at its exact ordinal in
the oracle list, even when other requests have the same endpoints. -/
theorem RunFrame.childRequests_selected {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premises : List Premise} {initial final : Assignment}
    {history : List (PremiseEvent Evidence)}
    (run : RunFrame oracle relEnv lang rule spec ambient
      index premises initial final history)
    (child : ChildRequest Evidence)
    (listed : child ∈ RunFrame.childRequests run) :
    ((child.evidence, child.target), child.ordinal) ∈
      (oracle child.ambient child.source).zipIdx := by
  induction run with
  | nil => simp [RunFrame.childRequests] at listed
  | cons head tail ih =>
      simp only [RunFrame.childRequests, List.mem_append] at listed
      rcases listed with first | rest
      · exact PremiseFrame.childRequest_selected head child first
      · exact ih rest

/-- A whole actual premise run is reconstructed exactly from its fixed
constructor skeleton and the selected child histories in their positions.
This retains premise order, result ordinals and root-result events. -/
theorem RunFrame.materializeEvents_selected
    {oracle : StepOracle RuleHistory} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premises : List Premise} {initial final : Assignment}
    {history : List (PremiseEvent RuleHistory)}
    (run : RunFrame oracle relEnv lang rule spec ambient
      index premises initial final history) :
    (RunFrame.toSkeleton run).materializeEvents?
      ((RunFrame.childRequests run).map ChildRequest.evidence) =
        some history := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | scopedStep wellScoped child admitted =>
          rcases admitted with ⟨_, _, _, _, _, _, eventEq⟩
          simp [RunFrame.toSkeleton, PremiseFrame.toSkeleton,
            RunFrame.childRequests, PremiseFrame.childRequest?,
            RunSkeleton.materializeEvents?, eventEq, ih]
      | congruence child admitted =>
          rcases admitted with ⟨_, _, _, _, _, _, eventEq⟩
          simp [RunFrame.toSkeleton, PremiseFrame.toSkeleton,
            RunFrame.childRequests, PremiseFrame.childRequest?,
            RunSkeleton.materializeEvents?, eventEq, ih]
      | freshness selected =>
          simp [RunFrame.toSkeleton, PremiseFrame.toSkeleton,
            RunFrame.childRequests, PremiseFrame.childRequest?,
            RunSkeleton.materializeEvents?, ih]
      | relationQuery selected =>
          simp [RunFrame.toSkeleton, PremiseFrame.toSkeleton,
            RunFrame.childRequests, PremiseFrame.childRequest?,
            RunSkeleton.materializeEvents?, ih]
      | forAll selected =>
          simp [RunFrame.toSkeleton, PremiseFrame.toSkeleton,
            RunFrame.childRequests, PremiseFrame.childRequest?,
            RunSkeleton.materializeEvents?, ih]

/-- Every recursive child listed by a projected ordered run was selected by
its step oracle. This retains the exact premise-local context and endpoints. -/
theorem RunFrame.toSkeleton_children_selected {Evidence : Type}
    {oracle : StepOracle Evidence} {relEnv : RelationEnv}
    {lang : LanguageDef} {rule : RewriteRule}
    {spec : RuleBindingSpec} {ambient index : Nat}
    {premises : List Premise} {initial final : Assignment}
    {history : List (PremiseEvent Evidence)}
    (run : RunFrame oracle relEnv lang rule spec ambient
      index premises initial final history)
    (requested : Nat × Pattern × Pattern)
    (listed : requested ∈ (RunFrame.toSkeleton run).children) :
    ∃ evidence,
      (evidence, requested.2.2) ∈
        oracle requested.1 requested.2.1 := by
  induction run with
  | nil =>
      simp [RunFrame.toSkeleton, RunSkeleton.children] at listed
  | cons head tail ih =>
      simp only [RunFrame.toSkeleton, RunSkeleton.children,
        List.mem_append] at listed
      rcases listed with first | rest
      · exact PremiseFrame.toSkeleton_child_selected head requested first
      · exact ih rest

/-- A successful executable conditional run determines a finite,
oracle-independent premise skeleton with at most one child per premise. -/
theorem runPremises_hasSkeleton {Evidence : Type}
    (oracle : StepOracle Evidence) (relEnv : RelationEnv)
    (lang : LanguageDef) (rule : RewriteRule)
    (spec : RuleBindingSpec) (ambient index : Nat)
    (premises : List Premise) (initial final : Assignment)
    (history : List (PremiseEvent Evidence))
    (executed : (final, history) ∈
      runPremises oracle relEnv lang rule spec ambient index
        premises initial) :
    ∃ shape : RunSkeleton Evidence relEnv lang rule spec ambient
      index premises initial final,
      shape.children.length ≤ premises.length := by
  obtain ⟨run⟩ :=
    (runFrame_nonempty_iff oracle relEnv lang rule spec ambient
      index premises initial final history).mpr executed
  exact ⟨RunFrame.toSkeleton run,
    (RunFrame.toSkeleton run).children_length_le⟩

end Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
