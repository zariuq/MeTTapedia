import Mettapedia.Languages.MeTTa.HE.ArgumentResult
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
import Mettapedia.Languages.MeTTa.HE.Spec.Match.ModelTheory
import Mettapedia.Machines.OrderedProtocol
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Parameterized HE evaluation judgments

The single mutually recursive, fuel-free rule block carries a complete binding
frame: raw constraints plus either the historical materializer or a certified
finite table shared by every operand in that retained activation. Raw public
calls explicitly inject the historical instance. The judgments share the full typed result
continuation with raw/minimal invocation and function completion. The embedded
`metta` fragment includes Atom demand, syntactic errors, and non-error full
results. General embedded-metta failure-priority completeness is not asserted:
its negative all-alternatives test cannot be placed inside an inductive family.
The type, unify, switch, matcher, merger, alpha-renaming, and
equation-query premises are the independent relations from the preceding
modules.  Grounded operations remain an explicitly parameterized host
relation.

Type collection and its enumeration are distinct contracts. The historical
default of the older possibility judgments is explicitly `storageTypeService`;
it is one list-storage profile, not a specified order of HE spaces. Other
complete enumerations enter through `enumeratedTypeService`. The completed
source judgments and contextual machine take their lookup as a parameter.

The mutual block presents individual raw possibilities, including in recursive
child premises. `EvalRel` below adds only outer success priority. It is not
recursively published HE evaluation: filtering a child before its caller
resumes cannot in general be delayed to the outer boundary. The concrete
nested-error obstruction is proved in `FirstSuccessSourceExecution`.
Completed finite-phase publication is stated independently in
`Machines.OrderedProtocol.Completion`; complete recursive source coverage remains separate.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Match.Merge
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.BindingTheory
open Spec.Eval.Steps

/-! ## Retained binding readout -/

/-- Historical materialization remains a distinct exact instance. A selected
readout carries executable finite data and its independent certificate. -/
inductive BindingReadout (bindings : Bindings) : Type where
  | historical
  | selected (table : TypeSubst) (certified : ReadoutCertificate bindings table)

structure BindingFrame where
  bindings : Bindings
  readout : BindingReadout bindings

abbrev FrameResult := Atom × BindingFrame

namespace BindingFrame

open Spec.Type.RuntimeRefinement

def historical (bindings : Bindings) : BindingFrame := ⟨bindings, .historical⟩
def selected (bindings : Bindings) (table : TypeSubst)
    (certified : ReadoutCertificate bindings table) : BindingFrame :=
  ⟨bindings, .selected table certified⟩

theorem selected_congr {left right : Bindings} {first second : TypeSubst}
    {leftCertificate : ReadoutCertificate left first}
    {rightCertificate : ReadoutCertificate right second}
    (rows : left = right) (tables : first = second) :
    selected left first leftCertificate = selected right second rightCertificate := by
  cases rows
  cases tables
  rfl

def rawResult (result : FrameResult) : ResultPair := (result.1, result.2.bindings)
def historicalResult (result : ResultPair) : FrameResult :=
  (result.1, historical result.2)

instance : Coe BindingFrame Bindings := ⟨BindingFrame.bindings⟩
instance : Coe FrameResult ResultPair := ⟨rawResult⟩

/-- Raw public calls retain the historical readout explicitly. A selected
representation is admitted only by supplying its table and certificate. -/
instance : Coe Bindings BindingFrame := ⟨historical⟩
instance : Coe ResultPair FrameResult := ⟨historicalResult⟩

@[simp] theorem historical_bindings (bindings : Bindings) :
    (historical bindings).bindings = bindings := rfl
@[simp] theorem raw_historicalResult (result : ResultPair) :
    rawResult (historicalResult result) = result := by cases result; rfl


theorem historicalResult_injective : Function.Injective historicalResult := by
  intro left right same
  simpa only [raw_historicalResult] using congrArg rawResult same

@[simp] theorem historicalResult_inj {left right : ResultPair} :
    historicalResult left = historicalResult right ↔ left = right :=
  historicalResult_injective.eq_iff

@[simp] theorem historicalResult_pair (value : Atom) (bindings : Bindings) :
    historicalResult (value, bindings) = (value, historical bindings) := rfl

/-- Persistence and real operation re-entry are distinct. A new activation
may reselect its representation even when its raw constraints happen to agree. -/
inductive TransitionKind where
  | retain
  | renew

/-- Renewal evidence is consumed only alongside the actual cast, query or merge
premise in the evaluator. Pure rules retain the whole input frame directly. -/
inductive Update : TransitionKind → BindingFrame → BindingFrame → Prop where
  | same (kind : TransitionKind) (frame : BindingFrame) : Update kind frame frame
  | historical (before after : Bindings) :
      Update .renew (historical before) (historical after)
  | selected {before after : Bindings} {earlier later : TypeSubst}
      (old : ReadoutCertificate before earlier) (next : ReadoutCertificate after later) :
      Update .renew (BindingFrame.selected before earlier old)
        (BindingFrame.selected after later next)

theorem Update.retained_eq {before after : BindingFrame}
    (updated : Update .retain before after) : before = after := by
  cases updated
  rfl

theorem Update.historical_output {before : Bindings} {after : BindingFrame}
    {kind : TransitionKind}
    (updated : Update kind (BindingFrame.historical before) after) :
    after = BindingFrame.historical after.bindings := by
  cases updated <;> rfl

/-- Historical frames cannot acquire a selected representation silently. -/
theorem Update.preserves_historical {before after : BindingFrame} {kind : TransitionKind}
    (updated : Update kind before after)
    (historicalBefore : before = BindingFrame.historical before.bindings) :
    after = BindingFrame.historical after.bindings := by
  rw [historicalBefore] at updated
  exact updated.historical_output

/-- The selected table is shared by all operand reads in this frame. -/
def Materialization (frame : BindingFrame) (raw normalized : Atom) : Prop :=
  match frame.readout with
  | .historical => BindingMaterializationRel frame.bindings raw normalized
  | .selected table _ => normalized = table.apply raw

@[simp] theorem materialization_historical (bindings : Bindings) (raw value : Atom) :
    Materialization (historical bindings) raw value ↔
      BindingMaterializationRel bindings raw value := Iff.rfl

@[simp] theorem materialization_selected (bindings : Bindings) (table : TypeSubst)
    (certified : ReadoutCertificate bindings table) (raw value : Atom) :
    Materialization (selected bindings table certified) raw value ↔
      value = table.apply raw := Iff.rfl

theorem Materialization.output_eq {frame : BindingFrame} {raw left right : Atom}
    (first : Materialization frame raw left) (second : Materialization frame raw right) :
    left = right := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.output_eq first second
  | selected table certified => exact first.trans second.symm

/-- Closed syntax is unchanged by either retained readout profile. -/
theorem Materialization.closed_result {frame : BindingFrame} {raw normalized : Atom}
    (materialized : frame.Materialization raw normalized)
    (closed : TypeSubst.typeVars raw = []) : normalized = raw := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.closed_result materialized closed
  | selected table certified =>
      change normalized = table.apply raw at materialized
      rw [materialized]
      apply TypeSubst.apply_eq_self_of_variables_not_keys
      intro name member
      simp [closed] at member

/-- Both readout profiles preserve every model of the complete raw record. -/
theorem Materialization.preserves_model {frame : BindingFrame} {raw normalized : Atom}
    (materialized : Materialization frame raw normalized) (valuation : String → Atom)
    (satisfied : Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation frame.bindings) :
    Spec.Type.RuntimeRefinement.applyTypeValuation valuation normalized =
      Spec.Type.RuntimeRefinement.applyTypeValuation valuation raw := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.preserves_model materialized valuation satisfied
  | selected table certified =>
    change normalized = table.apply raw at materialized
    rw [materialized]
    exact certified.preserves_model valuation satisfied raw

theorem Materialization.of_historical {frame : BindingFrame} {raw normalized : Atom}
    (materialized : Materialization frame raw normalized)
    (historicalFrame : frame = historical frame.bindings) :
    BindingMaterializationRel frame.bindings raw normalized := by
  rw [historicalFrame] at materialized
  exact materialized

theorem Update.no_reselect {bindings : Bindings} {old next : TypeSubst}
    (oldCertificate : ReadoutCertificate bindings old)
    (nextCertificate : ReadoutCertificate bindings next) (different : old ≠ next) :
    ¬Update .retain (BindingFrame.selected bindings old oldCertificate)
      (BindingFrame.selected bindings next nextCertificate) := by
  intro updated
  have equal := updated.retained_eq
  cases equal
  exact different rfl

/-- Raw serialization is admitted only for the historical instance until the
host carries the selected representation as part of its saved payload. -/
def Historical (frame : BindingFrame) : Prop := frame = historical frame.bindings


theorem Historical.result {result : FrameResult} (historicalFrame : result.2.Historical) :
    historicalResult (rawResult result) = result := by
  rcases result with ⟨value, frame⟩
  change (value, historical frame.bindings) = (value, frame)
  rw [← historicalFrame]

/-- The same selected readout is reused when a continuation observes its
already materialized operand. -/
theorem Materialization.reapply {frame : BindingFrame} {raw normalized : Atom}
    (materialized : frame.Materialization raw normalized) :
    frame.Materialization normalized normalized := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical =>
    obtain ⟨table, folded, rfl⟩ := materialized
    exact BindingMaterializationRel.reapply_same_presentation folded raw
  | selected table certified =>
    change normalized = table.apply raw at materialized
    change normalized = table.apply normalized
    rw [materialized, certified.absorbs certified (fun _ model => model)]

theorem Materialization.satisfiable {frame : BindingFrame} {raw normalized : Atom}
    (materialized : frame.Materialization raw normalized) :
    ∃ valuation, TypeBindingSatisfied valuation frame.bindings := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.satisfiable materialized
  | selected table certified => exact certified.satisfiable

/-- Literal instruction heads survive both admitted readout profiles. -/
theorem Materialization.symbol_head_iff (frame : BindingFrame) (head : String)
    (raw normalized : Atom) :
    frame.Materialization (.expression [.symbol head, raw]) normalized ↔
      ∃ value, frame.Materialization raw value ∧
        normalized = .expression [.symbol head, value] := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical =>
    constructor
    · rintro ⟨table, folded, same⟩
      exact ⟨table.apply raw, ⟨table, folded, rfl⟩,
        by simpa only [TypeSubst.apply, List.map_cons, List.map_nil] using same⟩
    · rintro ⟨value, ⟨table, folded, rfl⟩, rfl⟩
      exact ⟨table, folded, by simp only [TypeSubst.apply, List.map_cons, List.map_nil]⟩
  | selected table certified =>
    change normalized = table.apply (.expression [.symbol head, raw]) ↔
      ∃ value, value = table.apply raw ∧ normalized = .expression [.symbol head, value]
    simp only [TypeSubst.apply, List.map_cons, List.map_nil, exists_eq_left]

/-- One action renames the entire retained record and finite table together. -/
def rename (permutation : Equiv.Perm String) (frame : BindingFrame) : BindingFrame where
  bindings := Spec.Bindings.ScopeObservation.renameBindings permutation frame.bindings
  readout := match frame.readout with
    | .historical => .historical
    | .selected table certified =>
        .selected (table.renameVars permutation) (certified.rename permutation)

@[simp] theorem rename_bindings (permutation : Equiv.Perm String) (frame : BindingFrame) :
    (rename permutation frame).bindings =
      Spec.Bindings.ScopeObservation.renameBindings permutation frame.bindings := rfl

@[simp] theorem rename_historical (permutation : Equiv.Perm String) (bindings : Bindings) :
    rename permutation (historical bindings) =
      historical (Spec.Bindings.ScopeObservation.renameBindings permutation bindings) := rfl

@[simp] theorem rename_inverse (permutation : Equiv.Perm String) (frame : BindingFrame) :
    rename permutation.symm (rename permutation frame) = frame := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical =>
    change historical _ = historical bindings
    apply congrArg historical
    simp
  | selected table certified =>
    apply selected_congr
    · simp
    · simp

@[simp] theorem rename_inverse_reverse (permutation : Equiv.Perm String) (frame : BindingFrame) :
    rename permutation (rename permutation.symm frame) = frame := rename_inverse permutation.symm frame

theorem Historical.rename {frame : BindingFrame} (historicalFrame : frame.Historical)
    (permutation : Equiv.Perm String) : (rename permutation frame).Historical := by
  rw [historicalFrame]
  rfl

theorem Update.rename {kind : TransitionKind} {before after : BindingFrame}
    (updated : Update kind before after) (permutation : Equiv.Perm String) :
    Update kind (rename permutation before) (rename permutation after) := by
  cases updated with
  | same => exact .same _ _
  | historical => exact .historical _ _
  | selected old next => exact .selected (old.rename permutation) (next.rename permutation)

theorem Materialization.rename {frame : BindingFrame} {raw normalized : Atom}
    (materialized : Materialization frame raw normalized) (permutation : Equiv.Perm String) :
    (rename permutation frame).Materialization (renameTypeVars permutation raw)
      (renameTypeVars permutation normalized) := by
  rcases frame with ⟨bindings, readout⟩
  cases readout with
  | historical => exact BindingMaterializationRel.rename permutation materialized
  | selected table certified =>
    change normalized = table.apply raw at materialized
    change renameTypeVars permutation normalized =
      (table.renameVars permutation).apply (renameTypeVars permutation raw)
    rw [materialized, TypeSubst.apply_renameVars]

end BindingFrame


/-! ## Syntax and host boundaries -/

/-- Intrinsic meta-type, stated relationally. -/
inductive MetaTypeRel : Atom → Atom → Prop where
  | symbol (name : String) :
      MetaTypeRel (.symbol name) Atom.symbolType
  | variable (name : String) :
      MetaTypeRel (.var name) Atom.variableType
  | grounded (value : GroundedValue) :
      MetaTypeRel (.grounded value) Atom.groundedType
  | expression (atoms : List Atom) :
      MetaTypeRel (.expression atoms) Atom.expressionType

/-- Intrinsic meta-types are functional.  Evaluator constructor inversions
use this boundary lemma instead of repeating an atom-constructor case split. -/
theorem MetaTypeRel.eq {atom left right : Atom}
    (leftType : MetaTypeRel atom left) (rightType : MetaTypeRel atom right) :
    left = right := by
  cases leftType <;> cases rightType <;> rfl

/-- Syntactic error atom.  The published `(Error ...)` pattern recognizes
every expression headed by `Error`, independently of its tail shape. -/
def IsErrorRel (atom : Atom) : Prop :=
  ∃ tail, atom = .expression (.symbol "Error" :: tail)

/-- Empty or syntactic error atom. -/
def IsEmptyOrErrorRel (atom : Atom) : Prop :=
  atom = Atom.empty ∨ IsErrorRel atom

/-! ## Evaluation entry and publication policy

The status belongs to the occurrence entering this boundary. It is not a
normal-form claim about its printed atom. A nested value representation must
additionally preserve its children's statuses through binding readout and
rebuilding; this entry view does not prescribe that representation.
-/

namespace Entry

inductive Status where
  | active
  | held
  deriving DecidableEq, Repr

inductive ReentryPolicy where
  | reuse
  | reinterpret
  deriving DecidableEq, Repr

inductive Action where
  | deliver
  | cast
  | interpret
  deriving DecidableEq, Repr

/-- The ordered entry cases of full evaluation. An implementation supplies
only the occurrence status, not an evaluator callback. -/
inductive Rel (policy : ReentryPolicy) (status : Status) : Atom → Atom → Action → Prop where
  | stopped {atom expected} : IsEmptyOrErrorRel atom → Rel policy status atom expected .deliver
  | pass {atom expected metaType} :
      ¬IsEmptyOrErrorRel atom → MetaTypeRel atom metaType →
      (expected = Atom.atomType ∨ expected = metaType ∨ metaType = Atom.variableType) →
      Rel policy status atom expected .deliver
  | held {atoms expected} :
      ¬IsEmptyOrErrorRel (.expression atoms) →
      ¬(expected = Atom.atomType ∨ expected = Atom.expressionType ∨
        Atom.expressionType = Atom.variableType) →
      policy = .reuse → status = .held → Rel policy status (.expression atoms) expected .deliver
  | cast {atom expected metaType} :
      ¬IsEmptyOrErrorRel atom → MetaTypeRel atom metaType →
      ¬(expected = Atom.atomType ∨ expected = metaType ∨ metaType = Atom.variableType) →
      ((∃ name, atom = .symbol name) ∨ (∃ value, atom = .grounded value) ∨ atom = Atom.unit) →
      (atom = Atom.unit → policy = .reinterpret ∨ status = .active) →
      Rel policy status atom expected .cast
  | expression {head tail expected} :
      ¬IsEmptyOrErrorRel (.expression (head :: tail)) →
      ¬(expected = Atom.atomType ∨ expected = Atom.expressionType ∨
        Atom.expressionType = Atom.variableType) →
      (policy = .reinterpret ∨ status = .active) →
      Rel policy status (.expression (head :: tail)) expected .interpret

private theorem intrinsic (atom : Atom) : MetaTypeRel atom (getMetaType atom) := by
  cases atom with
  | symbol name => exact .symbol name
  | var name => exact .variable name
  | grounded value => exact .grounded value
  | expression atoms => exact .expression atoms

/-- Entry classification is total without assuming evaluation terminates. -/
theorem total (policy : ReentryPolicy) (status : Status) (atom expected : Atom) :
    ∃ action, Rel policy status atom expected action := by
  classical
  by_cases stopped : IsEmptyOrErrorRel atom
  · exact ⟨.deliver,.stopped stopped⟩
  by_cases raw : expected = Atom.atomType ∨ expected = getMetaType atom ∨
      getMetaType atom = Atom.variableType
  · exact ⟨.deliver,.pass stopped (intrinsic atom) raw⟩
  cases atom with
  | symbol name => exact ⟨.cast,.cast stopped (.symbol name) raw (Or.inl ⟨name,rfl⟩)
      (by intro impossible; cases impossible)⟩
  | grounded value => exact ⟨.cast,.cast stopped (.grounded value) raw
      (Or.inr (Or.inl ⟨value,rfl⟩)) (by intro impossible; cases impossible)⟩
  | var name => exact (raw (Or.inr (Or.inr rfl))).elim
  | expression atoms =>
      change ¬(expected = Atom.atomType ∨ expected = Atom.expressionType ∨
        Atom.expressionType = Atom.variableType) at raw
      by_cases reused : policy = .reuse ∧ status = .held
      · exact ⟨.deliver,.held stopped raw reused.1 reused.2⟩
      have active : policy = .reinterpret ∨ status = .active := by
        cases policy <;> cases status <;> simp_all
      cases atoms with
      | nil => exact ⟨.cast,.cast stopped (.expression []) raw (Or.inr (Or.inr rfl))
          (fun _ => active)⟩
      | cons head tail => exact ⟨.interpret,.expression stopped raw active⟩

/-- Atom demand licenses delivery for arbitrary source syntax and status. -/
theorem atom_demand (policy : ReentryPolicy) (status : Status) (atom : Atom) :
    Rel policy status atom Atom.atomType .deliver := by
  classical
  by_cases stopped : IsEmptyOrErrorRel atom
  · exact .stopped stopped
  · exact .pass stopped (intrinsic atom) (Or.inl rfl)

/-- The cases are disjoint even when a held atom is syntactically reducible. -/
theorem functional {policy : ReentryPolicy} {status : Status} {atom expected : Atom}
    {first second : Action} (left : Rel policy status atom expected first)
    (right : Rel policy status atom expected second) : first = second := by
  cases left <;> cases right <;> try rfl
  all_goals repeat' (first | cases ‹MetaTypeRel _ _›)
  all_goals simp_all [Atom.unit]

/-- Fresh entries use the same control cases under either reentry policy. -/
theorem active_policy {first second : ReentryPolicy} {atom expected : Atom} {action : Action}
    (entry : Rel first .active atom expected action) : Rel second .active atom expected action := by
  cases entry with
  | stopped stopped => exact .stopped stopped
  | pass clean typed raw => exact .pass clean typed raw
  | held _ _ _ impossible => cases impossible
  | cast clean typed raw scalar _ => exact .cast clean typed raw scalar (fun _ => Or.inr rfl)
  | expression clean raw _ => exact .expression clean raw (Or.inr rfl)

/-- Held expressions are delivered under reuse, independently of the
expected type or the current space. In particular they cannot query again. -/
theorem held_expression_exact {atoms : List Atom} {expected : Atom} {action : Action}
    (entry : Rel .reuse .held (.expression atoms) expected action) : action = .deliver := by
  cases entry with
  | stopped => rfl
  | pass => rfl
  | held => rfl
  | cast _ typed _ scalar active =>
      rcases scalar with ⟨_,impossible⟩ | ⟨_,impossible⟩ | unit
      · cases impossible
      · cases impossible
      · have impossible := active unit
        simp at impossible
  | expression _ _ active => simp at active

theorem Rel.interpret_shape {policy : ReentryPolicy} {status : Status} {atom expected : Atom}
    (entered : Rel policy status atom expected .interpret) :
    ∃ head tail, atom = .expression (head::tail) := by
  cases entered with
  | expression => exact ⟨_,_,rfl⟩

inductive MarkPolicy where
  | successes
  | unchanged
  | unchangedPreserving
  | none
  deriving DecidableEq, Repr

/-- One occurrence at a publication/entry boundary, retaining its entire
binding frame. Child statuses are a separate value-representation obligation. -/
structure Occurrence where
  result : FrameResult
  status : Status

/-- Publication changes only the permission to reinterpret an occurrence.
Historical policies clear error marks. The preserving policy keeps inherited
expression marks unless an unchanged successful expression is newly marked. -/
def publish (policy : MarkPolicy) (original : Atom) (result : FrameResult)
    (inherited : Status := .active) : Occurrence :=
  ⟨result, match result.1 with
    | .expression _ =>
        match policy with
        | .successes => if isErrorAtom result.1 then .active else .held
        | .unchanged => if isErrorAtom result.1 then .active else if result.1 == original then .held else .active
        | .unchangedPreserving => if isErrorAtom result.1 then inherited else if result.1 == original then .held else inherited
        | .none => .active
    | _ => .active⟩

@[simp] theorem publish_result (policy : MarkPolicy) (original : Atom) (result : FrameResult)
    (inherited : Status := .active) :
    (publish policy original result inherited).result = result := rfl

/-- Successful expression publication followed by reuse delivers the value
under every demand. Reentry does not require the expression to be normal in
the current space. -/
theorem successes_publish_no_reentry (original expected : Atom) (atoms : List Atom)
    (frame : BindingFrame) (successful : isErrorAtom (.expression atoms) = false) :
    Rel .reuse (publish .successes original (.expression atoms,frame)).status
      (.expression atoms) expected .deliver := by
  simp only [publish,successful,Bool.false_eq_true,↓reduceIte]
  obtain ⟨action,entry⟩ := total .reuse .held (.expression atoms) expected
  have same := held_expression_exact entry
  cases same
  exact entry

/-- Erasing entry status preserves every result occurrence and its binding
frame, including duplicate atoms and distinct frames for the same atom. -/
theorem publish_readout (policy : MarkPolicy) (original : Atom) (results : List FrameResult) :
    (results.map (fun result => publish policy original result)).map Occurrence.result = results := by
  simp [Function.comp_def]

/-- Success-priority classification transports across publication. This law
does not claim that reinterpretation under different policies is equivalent. -/
theorem publish_priority {raw selected : List FrameResult}
    (priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel (fun row : FrameResult => isErrorAtom row.1)
      raw selected) (policy : MarkPolicy) (original : Atom) :
    Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel (fun row : Occurrence => isErrorAtom row.result.1)
      (raw.map (fun result => publish policy original result)) (selected.map (fun result => publish policy original result)) :=
  priority.map (fun result => publish policy original result) (fun _ => rfl)

private def pending : Atom := .expression [.symbol "pending"]

/-- Equal printed atoms can require different actions at the same demand. -/
theorem active_and_held_are_distinct :
    Rel .reuse .active pending Atom.undefinedType .interpret ∧
    Rel .reuse .held pending Atom.undefinedType .deliver := by
  constructor
  · exact .expression (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty])
      (by decide) (Or.inr rfl)
  · exact .held (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty])
      (by decide) rfl rfl

/-- An atom-only dispatcher cannot implement both occurrence entry cases. -/
theorem erasing_status_cannot_classify :
    ¬∃ classify : Atom → Action, ∀ status,
      Rel .reuse status pending Atom.undefinedType (classify pending) := by
  rintro ⟨classify,correct⟩
  have active := functional (correct .active) active_and_held_are_distinct.1
  have held := functional (correct .held) active_and_held_are_distinct.2
  exact Action.noConfusion (active.symm.trans held)

/-- The two expression-marking policies agree on an unchanged success but
separate a changed success. Payload and binding frame remain identical. -/
theorem marking_policy_separation (frame : BindingFrame) :
    (publish .successes pending (pending,frame)).status = .held ∧
    (publish .unchanged pending (pending,frame)).status = .held ∧
    (publish .successes (.symbol "earlier") (pending,frame)).status = .held ∧
    (publish .unchanged (.symbol "earlier") (pending,frame)).status = .active := by
  simp [publish,pending,isErrorAtom]

/-! ## Nested values and substitution

Entry status is retained at every expression occurrence. Bindings may carry
these values without converting them back to syntax. Rebuilding a parent is
a separate policy; neither policy below asserts upstream dialect conformance.
-/

inductive Value where
  | symbol (name : String)
  | var (name : String)
  | grounded (value : GroundedValue)
  | expression (status : Status) (children : List Value)
  deriving Repr, Inhabited

inductive RebuildPolicy where
  | preserve
  | reopenChanged
  deriving DecidableEq, Repr

namespace Value

open Spec.Type.RuntimeRefinement Spec.Type.Presentation

def erase : Value → Atom
  | .symbol name => .symbol name
  | .var name => .var name
  | .grounded value => .grounded value
  | .expression _ children => .expression (children.map erase)

def ofAtom : Atom → Value
  | .symbol name => .symbol name
  | .var name => .var name
  | .grounded value => .grounded value
  | .expression children => .expression .active (children.map ofAtom)

def status : Value → Status
  | .expression readiness _ => readiness
  | _ => .active

def withStatus (value : Value) (readiness : Status) : Value :=
  match value with
  | .expression _ children => .expression readiness children
  | _ => value

def rebuildStatus (policy : RebuildPolicy) (previous : Status) (before after : Atom) : Status :=
  match policy with
  | .preserve => previous
  | .reopenChanged => if before == after then previous else .active

/-- Simultaneous substitution transfers the entire bound value. The parent
policy is applied only to expressions actually rebuilt by this traversal. -/
def substitute (policy : RebuildPolicy) (environment : String → Value) : Value → Value
  | .symbol name => .symbol name
  | .var name => environment name
  | .grounded value => .grounded value
  | .expression previous children =>
      let next := children.map (substitute policy environment)
      .expression (rebuildStatus policy previous
        (.expression (children.map erase)) (.expression (next.map erase))) next

/-- A contextual value with no variables is unchanged by every environment
and rebuilding policy. Nested evaluation marks are retained as well. -/
theorem substitute_variable_free (policy : RebuildPolicy) (environment : String → Value)
    (value : Value) (closed : ∀ name, ¬Spec.Match.Merge.AtomOccurs value.erase name) :
    substitute policy environment value = value := by
  induction value using Value.rec
      (motive_2 := fun values =>
        (∀ value ∈ values, ∀ name, ¬Spec.Match.Merge.AtomOccurs value.erase name) →
          values.map (substitute policy environment) = values) with
  | symbol => simp [substitute]
  | var name =>
      apply (closed name).elim
      simpa only [erase] using Spec.Match.Merge.AtomOccurs.var name
  | grounded => simp [substitute]
  | expression readiness children ih =>
      simp only [erase] at closed
      have same := ih (fun child member name occurs =>
        closed name (.expression (List.mem_map.mpr ⟨child,member,rfl⟩) occurs))
      cases policy <;> simp [substitute,same,rebuildStatus]
  | nil _closed => rfl
  | cons head tail first rest allClosed =>
      exact congrArg₂ List.cons (first (allClosed head List.mem_cons_self))
        (rest (fun value member => allClosed value (List.mem_cons_of_mem _ member)))

def compose (policy : RebuildPolicy) (first second : String → Value) : String → Value :=
  fun name => substitute policy second (first name)

/-- Finite environments retain first-hit lookup, including statuses and all
children of a stored value. -/
abbrev Environment := List (String × Value)

def resolve (environment : Environment) (name : String) : Value :=
  (environment.lookup name).getD (.var name)

def eraseEnvironment (environment : Environment) : TypeSubst :=
  environment.map fun row => (row.1,row.2.erase)

@[simp] theorem erase_withStatus (value : Value) (readiness : Status) :
    (value.withStatus readiness).erase = value.erase := by
  cases value <;> simp only [withStatus,erase]

@[simp] theorem erase_ofAtom (atom : Atom) : (ofAtom atom).erase = atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
    (atoms.map ofAtom).map erase = atoms) with
  | symbol => simp only [ofAtom,erase]
  | var => simp only [ofAtom,erase]
  | grounded => simp only [ofAtom,erase]
  | expression atoms ih => simpa only [ofAtom,erase] using congrArg Atom.expression ih
  | nil => rfl
  | cons atom atoms first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

/-- The internal successful-arguments packet retains whole child values. -/
def argumentPacket (values : List Value) : Value :=
  .expression .active [.symbol "Ok",.expression .active values]

def unpackArguments : Value → Option (List Value)
  | .expression _ [.symbol tag,.expression _ values] =>
      if tag = "Ok" then some values else none
  | _ => none

@[simp] theorem erase_argumentPacket (values : List Value) :
    (argumentPacket values).erase = HE.argumentPacket (values.map erase) := by
  simp [argumentPacket,erase,HE.argumentPacket]

@[simp] theorem unpackArguments_packet (values : List Value) :
    unpackArguments (argumentPacket values) = some values := by
  simp [unpackArguments,argumentPacket]

theorem unpackArguments_erases (value : Value) :
    (unpackArguments value).map (List.map erase) = HE.unpackArguments value.erase := by
  cases value with
  | expression readiness values =>
      rcases values with _ | ⟨head,tail⟩
      · simp [unpackArguments,erase,HE.unpackArguments]
      rcases tail with _ | ⟨payload,tail⟩
      · simp [unpackArguments,erase,HE.unpackArguments]
      rcases tail with _ | ⟨extra,rest⟩
      · cases head <;> cases payload <;> simp [unpackArguments,erase,HE.unpackArguments]
      · simp [unpackArguments,erase,HE.unpackArguments]
  | symbol | var | grounded => simp [unpackArguments,erase,HE.unpackArguments]

theorem unpackArguments_error {value : Value} (failed : IsEmptyOrErrorRel value.erase) :
    unpackArguments value = none := by
  cases decoded : unpackArguments value with
  | none => rfl
  | some values =>
      have encoded : HE.unpackArguments value.erase = some (values.map erase) := by
        rw [←unpackArguments_erases,decoded]
        rfl
      have shaped := HE.unpackArguments_iff.mp encoded
      rw [shaped] at failed
      simp [HE.argumentPacket,IsEmptyOrErrorRel,IsErrorRel,Atom.empty] at failed

/-- Every rebuilding policy has the same syntactic substitution readout.
This equality deliberately does not identify the resulting entry statuses. -/
theorem erase_substitute (policy : RebuildPolicy) (environment : String → Value) (value : Value) :
    (substitute policy environment value).erase =
      applyTypeValuation (fun name => (environment name).erase) value.erase := by
  induction value using Value.rec (motive_2 := fun values =>
    (values.map (substitute policy environment)).map erase =
      (values.map erase).map (applyTypeValuation (fun name => (environment name).erase))) with
  | symbol => simp only [substitute,erase,applyTypeValuation]
  | var => simp only [substitute,erase,applyTypeValuation]
  | grounded => simp only [substitute,erase,applyTypeValuation]
  | expression previous children ih =>
      simpa only [substitute,erase,applyTypeValuation] using congrArg Atom.expression ih
  | nil => rfl
  | cons value values first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

theorem erase_resolve (environment : Environment) (name : String) :
    (resolve environment name).erase =
      ((eraseEnvironment environment).lookup name).getD (.var name) := by
  induction environment with
  | nil => simp [resolve,eraseEnvironment,erase]
  | cons row rest ih =>
      rcases row with ⟨key,value⟩
      by_cases same : name = key
      · subst key
        simp [resolve,eraseEnvironment,List.lookup,TypeSubst.lookup]
      · have different : (name == key) = false := by simp [same]
        simpa [resolve,eraseEnvironment,List.lookup,TypeSubst.lookup,same,different] using ih

theorem erase_substitute_environment (policy : RebuildPolicy) (environment : Environment)
    (value : Value) :
    (substitute policy (resolve environment) value).erase =
      (eraseEnvironment environment).apply value.erase := by
  rw [erase_substitute]
  induction value.erase using Atom.rec (motive_2 := fun atoms =>
    atoms.map (applyTypeValuation (fun name => (resolve environment name).erase)) =
      atoms.map (TypeSubst.apply (eraseEnvironment environment))) with
  | symbol => simp only [applyTypeValuation,TypeSubst.apply]
  | var name => simpa only [applyTypeValuation,TypeSubst.apply] using erase_resolve environment name
  | grounded => simp only [applyTypeValuation,TypeSubst.apply]
  | expression atoms ih =>
      simpa only [applyTypeValuation,TypeSubst.apply] using congrArg Atom.expression ih
  | nil => rfl
  | cons atom atoms first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

/-- One certificate for the erased finite environment earns the existing
source-frame materialization. The returned annotated value is constructed,
not supplied as a desired decoder result. -/
theorem selected_materialization (policy : RebuildPolicy) (environment : Environment)
    (bindings : Bindings)
    (certificate : ReadoutCertificate bindings (eraseEnvironment environment)) (value : Value) :
    BindingFrame.Materialization (.selected bindings (eraseEnvironment environment) certificate)
      value.erase (substitute policy (resolve environment) value).erase :=
  erase_substitute_environment policy environment value

/-- Variable readout retains a held expression and its nested statuses
exactly; it never reconstructs that value from its printed atom. -/
theorem assigned_value_exact (policy : RebuildPolicy) (environment : Environment)
    (name : String) (value : Value) (stored : environment.lookup name = some value) :
    substitute policy (resolve environment) (.var name) = value := by
  simp [substitute,resolve,stored]

/-- Actual finite readout of a held expression both materializes in the
selected logical frame and enters through delivery, at every demand. -/
theorem selected_held_variable_entry (policy : RebuildPolicy) (environment : Environment)
    (bindings : Bindings) (name : String) (children : List Value)
    (certificate : ReadoutCertificate bindings (eraseEnvironment environment))
    (stored : environment.lookup name = some (.expression .held children)) (expected : Atom) :
    BindingFrame.Materialization (.selected bindings (eraseEnvironment environment) certificate)
      (.var name) (.expression (children.map erase)) ∧
    Entry.Rel .reuse (substitute policy (resolve environment) (.var name)).status
      (substitute policy (resolve environment) (.var name)).erase expected .deliver := by
  have exactValue := assigned_value_exact policy environment name _ stored
  constructor
  · have materialized := selected_materialization policy environment bindings certificate (.var name)
    simpa only [exactValue,erase] using materialized
  · rw [exactValue]
    simp only [status,erase]
    obtain ⟨action,entry⟩ := Entry.total .reuse .held (.expression (children.map erase)) expected
    have same := Entry.held_expression_exact entry
    cases same
    exact entry

/-- Fusion is valid for the policy which preserves expression readiness. -/
theorem preserve_compose (first second : String → Value) (value : Value) :
    substitute .preserve second (substitute .preserve first value) =
      substitute .preserve (compose .preserve first second) value := by
  induction value using Value.rec (motive_2 := fun values =>
    (values.map (substitute .preserve first)).map (substitute .preserve second) =
      values.map (substitute .preserve (compose .preserve first second))) with
  | symbol => simp only [substitute]
  | var => simp only [substitute,compose]
  | grounded => simp only [substitute]
  | expression previous children ih =>
      simpa only [substitute,rebuildStatus] using congrArg (Value.expression previous) ih
  | nil => rfl
  | cons value values first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

/-- An identity read changes no expression or nested entry status under
either rebuilding policy. -/
theorem substitute_identity (policy : RebuildPolicy) (value : Value) :
    substitute policy Value.var value = value := by
  induction value using Value.rec (motive_2 := fun values =>
    values.map (substitute policy Value.var) = values) with
  | symbol => simp only [substitute]
  | var => simp only [substitute]
  | grounded => simp only [substitute]
  | expression previous children ih =>
      simp only [substitute,ih]
      cases policy <;> simp [rebuildStatus]
  | nil => rfl
  | cons value values first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

/-- An environment fixing the variables used by a value fixes that whole
annotated value. Open variables and nested readiness marks are retained. -/
theorem substitute_of_fixed_variables (policy : RebuildPolicy) (environment : String → Value)
    (value : Value)
    (fixed : ∀ name ∈ TypeSubst.typeVars value.erase, environment name = .var name) :
    substitute policy environment value = value := by
  induction value using Value.rec
      (motive_2 := fun values =>
        (∀ value ∈ values, ∀ name ∈ TypeSubst.typeVars value.erase,
          environment name = .var name) →
        values.map (substitute policy environment) = values) with
  | symbol => simp only [substitute]
  | grounded => simp only [substitute]
  | var name =>
      simpa only [substitute] using fixed name (by simp [erase,TypeSubst.typeVars])
  | expression previous children ih =>
      have same := ih (fun child member name used => fixed name (by
        simpa only [erase,TypeSubst.typeVars] using
          (Freshness.typeVars_mem_typeVarsList_of_mem
            (List.mem_map.mpr ⟨child,member,rfl⟩) name used)))
      cases policy <;> simp [substitute,same,rebuildStatus]
  | nil _ => rfl
  | cons head tail first rest fixed =>
      exact congrArg₂ List.cons (first (fixed head List.mem_cons_self))
        (rest (fun value member => fixed value (List.mem_cons_of_mem _ member)))

/-- An absent environment key resolves to the original open variable. -/
theorem resolve_of_not_mem_keys (environment : Environment) (name : String) :
    name ∉ (eraseEnvironment environment).keys → resolve environment name = .var name := by
  induction environment with
  | nil => intro _; rfl
  | cons row rest ih =>
      rcases row with ⟨key,value⟩
      intro absent
      have omitted : name ≠ key ∧ name ∉ (eraseEnvironment rest).keys := by
        simpa [eraseEnvironment,TypeSubst.keys] using absent
      have different : (name == key) = false := by simp [omitted.1]
      simpa [resolve,List.lookup,different] using ih omitted.2

theorem preserve_identity (value : Value) :
    substitute .preserve Value.var value = value := substitute_identity .preserve value

/-- Retaining pending substitution work preserves intermediate readiness
changes. The entries are environments, not nested evaluators. -/
def substituteAll (policy : RebuildPolicy) (pending : List (String → Value)) (value : Value) : Value :=
  pending.foldl (fun current environment => substitute policy environment current) value

/-- A pause between environments retains the reached value and the exact
suffix. This law is valid for both rebuilding policies. -/
theorem substituteAll_append (policy : RebuildPolicy)
    (earlier remaining : List (String → Value)) (value : Value) :
    substituteAll policy (earlier ++ remaining) value =
      substituteAll policy remaining (substituteAll policy earlier value) := by
  exact List.foldl_append

def fusePreserving : List (String → Value) → String → Value
  | [] => Value.var
  | first :: remaining => compose .preserve first (fusePreserving remaining)

/-- The stable-data policy can compact its pending environments without
losing any nested readiness. The reopening policy requires a different law. -/
theorem preserve_fuse (pending : List (String → Value)) (value : Value) :
    substituteAll .preserve pending value =
      substitute .preserve (fusePreserving pending) value := by
  induction pending generalizing value with
  | nil => exact (preserve_identity value).symm
  | cons first rest ih =>
      change substituteAll .preserve rest (substitute .preserve first value) = _
      rw [ih,preserve_compose]
      rfl

/-- Scope renaming preserves evaluation statuses, independently of the
separate policy for instantiating a parent with changed children. -/
def rename (names : String → String) (value : Value) : Value :=
  substitute .preserve (fun name => .var (names name)) value

theorem rename_erase (names : String → String) (value : Value) :
    (rename names value).erase = renameTypeVars names value.erase := by
  rw [rename,erase_substitute]
  induction value.erase using Atom.rec (motive_2 := fun atoms =>
    atoms.map (applyTypeValuation (fun name => (Value.var (names name)).erase)) =
      atoms.map (renameTypeVars names)) with
  | symbol => simp only [applyTypeValuation,renameTypeVars]
  | var => simp only [applyTypeValuation,renameTypeVars,erase]
  | grounded => simp only [applyTypeValuation,renameTypeVars]
  | expression atoms ih => simpa only [applyTypeValuation,renameTypeVars] using congrArg Atom.expression ih
  | nil => rfl
  | cons atom atoms first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

/-- Fresh syntax and simultaneous variable renaming commute, preserving the
active status of every expression introduced by source loading. -/
theorem rename_ofAtom (names : String → String) (atom : Atom) :
    rename names (ofAtom atom) = ofAtom (renameTypeVars names atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      atoms.map (fun atom => rename names (ofAtom atom)) =
        atoms.map (fun atom => ofAtom (renameTypeVars names atom))) with
  | symbol | var | grounded => simp only [rename,ofAtom,substitute,renameTypeVars]
  | expression atoms ih =>
      simp only [ofAtom,rename,substitute,rebuildStatus,renameTypeVars,List.map_map]
      exact congrArg (Value.expression .active)
        (by simpa only [rename,Function.comp_def] using ih)
  | nil => rfl
  | cons atom atoms first rest =>
      simpa only [List.map_cons] using congrArg₂ List.cons first rest

theorem rename_status (names : String → String) (value : Value) :
    (rename names value).status = value.status := by
  cases value <;> simp only [rename,substitute,rebuildStatus,status]

theorem rename_comp (outer inner : String → String) (value : Value) :
    rename outer (rename inner value) = rename (outer ∘ inner) value := by
  unfold rename
  rw [preserve_compose]
  apply congrArg (fun environment => substitute .preserve environment value)
  funext name
  simp only [compose,substitute,Function.comp_apply]

@[simp] theorem rename_id (value : Value) : rename id value = value :=
  preserve_identity value

/-- Inverse freshening restores the whole value, including every nested
status, rather than only restoring its syntax. -/
theorem rename_cancel (names : Equiv.Perm String) (value : Value) :
    rename names.symm (rename names value) = value := by
  rw [rename_comp]
  have identity : ((names.symm : String → String) ∘ names) = id := by
    funext name
    exact names.symm_apply_apply name
  rw [identity,rename_id]

/-- Publication changes only the selected parent's status. -/
def publish (policy : MarkPolicy) (original : Atom) (frame : BindingFrame) (value : Value) : Value :=
  value.withStatus (Entry.publish policy original (value.erase,frame) value.status).status

@[simp] theorem erase_publish (policy : MarkPolicy) (original : Atom)
    (frame : BindingFrame) (value : Value) :
    (publish policy original frame value).erase = value.erase := erase_withStatus _ _

theorem publish_children (policy : MarkPolicy) (original : Atom) (frame : BindingFrame)
    (previous : Status) (children : List Value) :
    publish policy original frame (.expression previous children) =
      .expression (Entry.publish policy original
        ((.expression previous children : Value).erase,frame) previous).status children := rfl

/-! ## Ordinary unification with contextual values

The finite presentation unifier below compares erased syntax and transfers
whole values at assignments. It has no gradual-type wildcard or grounded
custom-matcher case. Its projection is the existing ordinary presentation
relation; expression readiness is governed only by the rebuilding policy.
-/

/-- Resolve the assigned value and propagate this assignment through older
values. Both traversals retain their annotated children. -/
def bind (policy : RebuildPolicy) (environment : Environment) (name : String)
    (value : Value) : Environment :=
  let resolved := substitute policy (resolve environment) value
  (name,resolved) ::
    (environment.filter (fun row => row.1 != name)).map fun row =>
      (row.1,substitute policy (resolve [(name,resolved)]) row.2)

theorem erase_bind (policy : RebuildPolicy) (environment : Environment) (name : String)
    (value : Value) :
    eraseEnvironment (bind policy environment name value) =
      (eraseEnvironment environment).bind name value.erase := by
  have filtered : eraseEnvironment (environment.filter (fun row => row.1 != name)) =
      (eraseEnvironment environment).erase name := by
    induction environment with
    | nil => rfl
    | cons row rest ih =>
        by_cases same : row.1 = name
        · simpa [eraseEnvironment,TypeSubst.erase,same] using ih
        · simpa [eraseEnvironment,TypeSubst.erase,same] using congrArg (List.cons (row.1,row.2.erase)) ih
  let resolved := substitute policy (resolve environment) value
  have resolvedErase : resolved.erase = (eraseEnvironment environment).apply value.erase :=
    erase_substitute_environment policy environment value
  have propagated :
      eraseEnvironment ((environment.filter (fun row => row.1 != name)).map
        (fun row => (row.1,substitute policy (resolve [(name,resolved)]) row.2))) =
      (eraseEnvironment (environment.filter (fun row => row.1 != name))).map
        (fun row => (row.1,TypeSubst.apply [(name,resolved.erase)] row.2)) := by
    simp only [eraseEnvironment,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro row _
    exact congrArg (Prod.mk row.1) (by
      simpa only [eraseEnvironment,List.map_cons,List.map_nil] using
        erase_substitute_environment policy [(name,resolved)] row.2)
  change (name,resolved.erase) ::
    eraseEnvironment ((environment.filter (fun row => row.1 != name)).map
      (fun row => (row.1,substitute policy (resolve [(name,resolved)]) row.2))) = _
  rw [propagated,filtered,resolvedErase]
  rfl

mutual

/-- An ordinary unification step on already materialized contextual values.
Readiness is not an extra equality constraint. -/
inductive AppliedUnifyRel (policy : RebuildPolicy) :
    Environment → Value → Value → Environment → Prop where
  | identical {environment left right} : left.erase = right.erase →
      AppliedUnifyRel policy environment left right environment
  | bindLeft {environment name right} :
      name ∉ TypeSubst.typeVars right.erase →
      AppliedUnifyRel policy environment (.var name) right (bind policy environment name right)
  | bindRight {environment left name} :
      (∀ other, left.erase ≠ .var other) → name ∉ TypeSubst.typeVars left.erase →
      AppliedUnifyRel policy environment left (.var name) (bind policy environment name left)
  | expression {environment output left right earlier later} :
      UnifyListRel policy environment left right output →
      AppliedUnifyRel policy environment (.expression earlier left) (.expression later right) output

/-- Every child sees the environment actually reached by the preceding
children. Materialization transfers the stored values, including readiness. -/
inductive UnifyRel (policy : RebuildPolicy) :
    Environment → Value → Value → Environment → Prop where
  | ordinary {environment output left right} :
      AppliedUnifyRel policy environment
        (substitute policy (resolve environment) left)
        (substitute policy (resolve environment) right) output →
      UnifyRel policy environment left right output

inductive UnifyListRel (policy : RebuildPolicy) :
    Environment → List Value → List Value → Environment → Prop where
  | nil (environment) : UnifyListRel policy environment [] [] environment
  | cons {environment next output left right lefts rights} :
      UnifyRel policy environment left right next →
      UnifyListRel policy next lefts rights output →
      UnifyListRel policy environment (left :: lefts) (right :: rights) output

end

private theorem unification_erasure (policy : RebuildPolicy) :
    (∀ {environment output left right}, AppliedUnifyRel policy environment left right output →
      AppliedReducedTypeMatchRel (eraseEnvironment environment) left.erase right.erase
        (eraseEnvironment output)) ∧
    (∀ {environment output left right}, UnifyRel policy environment left right output →
      AppliedTypePresentationMatchRel (eraseEnvironment environment) left.erase right.erase
        (eraseEnvironment output)) ∧
    (∀ {environment output left right}, UnifyListRel policy environment left right output →
      AppliedReducedTypeListMatchRel (eraseEnvironment environment) (left.map erase) (right.map erase)
        (eraseEnvironment output)) := by
  let applied := fun environment left right output (_ : AppliedUnifyRel policy environment left right output) =>
    AppliedReducedTypeMatchRel (eraseEnvironment environment) left.erase right.erase (eraseEnvironment output)
  let ordinary := fun environment left right output (_ : UnifyRel policy environment left right output) =>
    AppliedTypePresentationMatchRel (eraseEnvironment environment) left.erase right.erase (eraseEnvironment output)
  let many := fun environment left right output (_ : UnifyListRel policy environment left right output) =>
    AppliedReducedTypeListMatchRel (eraseEnvironment environment) (left.map erase) (right.map erase)
      (eraseEnvironment output)
  have identical {environment left right} (same : left.erase = right.erase) :
      applied environment left right environment (.identical same) := by
    dsimp [applied]
    rw [same]
    exact .identical _ _
  have bindLeft {environment name right} (absent : name ∉ TypeSubst.typeVars right.erase) :
      applied environment (.var name) right (bind policy environment name right) (.bindLeft absent) := by
    dsimp [applied]
    rw [erase_bind]
    simpa only [erase] using AppliedReducedTypeMatchRel.bindLeft
      (substitution := eraseEnvironment environment) absent
  have bindRight {environment left name} (nonvar : ∀ other, left.erase ≠ .var other)
      (absent : name ∉ TypeSubst.typeVars left.erase) :
      applied environment left (.var name) (bind policy environment name left) (.bindRight nonvar absent) := by
    dsimp [applied]
    rw [erase_bind]
    simpa only [erase] using AppliedReducedTypeMatchRel.bindRight
      (substitution := eraseEnvironment environment) nonvar absent
  have expression {environment output left right earlier later}
      (children : UnifyListRel policy environment left right output)
      (ih : many environment left right output children) :
      applied environment (.expression earlier left) (.expression later right) output (.expression children) := by
    simpa only [applied,erase] using AppliedReducedTypeMatchRel.expression ih
  have materialized {environment output left right}
      (derived : AppliedUnifyRel policy environment
        (substitute policy (resolve environment) left) (substitute policy (resolve environment) right) output)
      (ih : applied environment _ _ output derived) :
      ordinary environment left right output (.ordinary derived) := by
    exact .ordinary (erase_substitute_environment policy environment left).symm
      (erase_substitute_environment policy environment right).symm ih
  have nil (environment) : many environment [] [] environment (.nil environment) := .nil _
  have cons {environment next output left right lefts rights}
      (head : UnifyRel policy environment left right next)
      (tail : UnifyListRel policy next lefts rights output)
      (ih : ordinary environment left right next head) (it : many next lefts rights output tail) :
      many environment (left :: lefts) (right :: rights) output (.cons head tail) := .cons ih it
  exact ⟨fun derived => AppliedUnifyRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => UnifyRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => UnifyListRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived⟩

theorem AppliedUnifyRel.erases {policy environment output left right}
    (derived : AppliedUnifyRel policy environment left right output) :
    AppliedReducedTypeMatchRel (eraseEnvironment environment) left.erase right.erase
      (eraseEnvironment output) := (unification_erasure policy).1 derived

theorem UnifyRel.erases {policy environment output left right}
    (derived : UnifyRel policy environment left right output) :
    AppliedTypePresentationMatchRel (eraseEnvironment environment) left.erase right.erase
      (eraseEnvironment output) := (unification_erasure policy).2.1 derived

/-- Annotated unification inherits capture avoidance from the source finite
presentation matcher, including variables retained in assignment values. -/
theorem UnifyRel.avoids {policy environment output left right forbidden}
    (derived : UnifyRel policy environment left right output)
    (incoming : (eraseEnvironment environment).Avoids forbidden)
    (leftFresh : Freshness.AtomAvoids left.erase forbidden)
    (rightFresh : Freshness.AtomAvoids right.erase forbidden) :
    (eraseEnvironment output).Avoids forbidden :=
  Freshness.appliedTypePresentationMatch_output_avoids derived.erases incoming leftFresh rightFresh

theorem UnifyListRel.erases {policy environment output left right}
    (derived : UnifyListRel policy environment left right output) :
    AppliedReducedTypeListMatchRel (eraseEnvironment environment) (left.map erase) (right.map erase)
      (eraseEnvironment output) := (unification_erasure policy).2.2 derived

private theorem variable_of_erasure {value : Value} {name : String}
    (same : value.erase = .var name) : value = .var name := by
  cases value <;> simp_all [erase]

private theorem expression_of_erasure {value : Value} {atoms : List Atom}
    (same : value.erase = .expression atoms) :
    ∃ readiness children, value = .expression readiness children ∧ children.map erase = atoms := by
  cases value with
  | expression readiness children =>
      exact ⟨readiness,children,rfl,Atom.expression.inj (by simpa only [erase] using same)⟩
  | symbol | var | grounded => simp [erase] at same

/-- Lift the actual ordinary unification derivation, rather than choosing an
arbitrary annotation of its final table. Every binding step transfers the
value selected at that step, and every sibling uses its reached environment. -/
private theorem unification_lifting (policy : RebuildPolicy) :
    (∀ {incoming output left right}, AppliedReducedTypeMatchRel incoming left right output →
      ∀ (environment : Environment) (first second : Value),
        eraseEnvironment environment = incoming → first.erase = left → second.erase = right →
        ∃ after, AppliedUnifyRel policy environment first second after ∧ eraseEnvironment after = output) ∧
    (∀ {incoming output left right}, AppliedTypePresentationMatchRel incoming left right output →
      ∀ (environment : Environment) (first second : Value),
        eraseEnvironment environment = incoming → first.erase = left → second.erase = right →
        ∃ after, UnifyRel policy environment first second after ∧ eraseEnvironment after = output) ∧
    (∀ {incoming output left right}, AppliedReducedTypeListMatchRel incoming left right output →
      ∀ (environment : Environment) (first second : List Value),
        eraseEnvironment environment = incoming → first.map erase = left → second.map erase = right →
        ∃ after, UnifyListRel policy environment first second after ∧ eraseEnvironment after = output) := by
  let applied := fun incoming left right output (_ : AppliedReducedTypeMatchRel incoming left right output) =>
    ∀ (environment : Environment) (first second : Value),
      eraseEnvironment environment = incoming → first.erase = left → second.erase = right →
      ∃ after, AppliedUnifyRel policy environment first second after ∧ eraseEnvironment after = output
  let ordinary := fun incoming left right output (_ : AppliedTypePresentationMatchRel incoming left right output) =>
    ∀ (environment : Environment) (first second : Value),
      eraseEnvironment environment = incoming → first.erase = left → second.erase = right →
      ∃ after, UnifyRel policy environment first second after ∧ eraseEnvironment after = output
  let many := fun incoming left right output (_ : AppliedReducedTypeListMatchRel incoming left right output) =>
    ∀ (environment : Environment) (first second : List Value),
      eraseEnvironment environment = incoming → first.map erase = left → second.map erase = right →
      ∃ after, UnifyListRel policy environment first second after ∧ eraseEnvironment after = output
  have identical (incoming : TypeSubst) (atom : Atom) :
      applied incoming atom atom incoming (.identical incoming atom) := by
    intro environment first second incomingRead firstRead secondRead
    exact ⟨environment,.identical (firstRead.trans secondRead.symm),incomingRead⟩
  have bindLeft {incoming name right} (absent : name ∉ TypeSubst.typeVars right) :
      applied incoming (.var name) right (incoming.bind name right) (.bindLeft absent) := by
    intro environment first second incomingRead firstRead secondRead
    obtain rfl := variable_of_erasure firstRead
    refine ⟨bind policy environment name second,.bindLeft (by simpa only [secondRead] using absent),?_⟩
    rw [erase_bind,incomingRead,secondRead]
  have bindRight {incoming left name} (nonvar : ∀ other, left ≠ .var other)
      (absent : name ∉ TypeSubst.typeVars left) :
      applied incoming left (.var name) (incoming.bind name left) (.bindRight nonvar absent) := by
    intro environment first second incomingRead firstRead secondRead
    obtain rfl := variable_of_erasure secondRead
    refine ⟨bind policy environment name first,.bindRight
      (by simpa only [firstRead] using nonvar) (by simpa only [firstRead] using absent),?_⟩
    rw [erase_bind,incomingRead,firstRead]
  have expression {incoming output left right}
      (children : AppliedReducedTypeListMatchRel incoming left right output)
      (ih : many incoming left right output children) :
      applied incoming (.expression left) (.expression right) output (.expression children) := by
    intro environment first second incomingRead firstRead secondRead
    obtain ⟨earlier,firsts,rfl,firstsRead⟩ := expression_of_erasure firstRead
    obtain ⟨later,seconds,rfl,secondsRead⟩ := expression_of_erasure secondRead
    obtain ⟨after,derived,afterRead⟩ := ih environment firsts seconds incomingRead firstsRead secondsRead
    exact ⟨after,.expression derived,afterRead⟩
  have materialized {incoming output left right resolvedLeft resolvedRight}
      (leftRead : incoming.apply left = resolvedLeft) (rightRead : incoming.apply right = resolvedRight)
      (derived : AppliedReducedTypeMatchRel incoming resolvedLeft resolvedRight output)
      (ih : applied incoming resolvedLeft resolvedRight output derived) :
      ordinary incoming left right output (.ordinary leftRead rightRead derived) := by
    intro environment first second incomingRead firstRead secondRead
    have leftValue : (substitute policy (resolve environment) first).erase = resolvedLeft := by
      rw [erase_substitute_environment,incomingRead,firstRead,leftRead]
    have rightValue : (substitute policy (resolve environment) second).erase = resolvedRight := by
      rw [erase_substitute_environment,incomingRead,secondRead,rightRead]
    obtain ⟨after,matched,afterRead⟩ := ih environment _ _ incomingRead leftValue rightValue
    exact ⟨after,.ordinary matched,afterRead⟩
  have nil (incoming : TypeSubst) : many incoming [] [] incoming (.nil incoming) := by
    intro environment first second incomingRead firstRead secondRead
    have firstNil : first = [] := List.map_eq_nil_iff.mp firstRead
    have secondNil : second = [] := List.map_eq_nil_iff.mp secondRead
    subst first
    subst second
    exact ⟨environment,.nil _,incomingRead⟩
  have cons {incoming next output left right lefts rights}
      (head : AppliedTypePresentationMatchRel incoming left right next)
      (tail : AppliedReducedTypeListMatchRel next lefts rights output)
      (ih : ordinary incoming left right next head) (it : many next lefts rights output tail) :
      many incoming (left :: lefts) (right :: rights) output (.cons head tail) := by
    intro environment first second incomingRead firstRead secondRead
    cases first with
    | nil => simp at firstRead
    | cons first firsts =>
        cases second with
        | nil => simp at secondRead
        | cons second seconds =>
            obtain ⟨firstRead,firstsRead⟩ := List.cons.inj firstRead
            obtain ⟨secondRead,secondsRead⟩ := List.cons.inj secondRead
            obtain ⟨middle,matched,middleRead⟩ := ih environment first second incomingRead firstRead secondRead
            obtain ⟨after,remaining,afterRead⟩ := it middle firsts seconds middleRead firstsRead secondsRead
            exact ⟨after,.cons matched remaining,afterRead⟩
  exact ⟨fun derived => AppliedReducedTypeMatchRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => AppliedTypePresentationMatchRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => AppliedReducedTypeListMatchRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived⟩

/-- Every successful ordinary presentation derivation has a contextual lift,
for either rebuilding policy and for every annotation of both operands. -/
theorem UnifyRel.lift {policy environment left right output}
    (derived : AppliedTypePresentationMatchRel (eraseEnvironment environment) left.erase right.erase output) :
    ∃ after, UnifyRel policy environment left right after ∧ eraseEnvironment after = output :=
  (unification_lifting policy).2.1 derived environment left right rfl rfl rfl

theorem UnifyRel.output_normal {policy environment left right output}
    (derived : UnifyRel policy environment left right output)
    (normal : (eraseEnvironment environment).Normal) : (eraseEnvironment output).Normal :=
  derived.erases.output_normal normal

/-- Contextual matching presents precisely the old binding theory and the
new syntactic equation. Readiness does not create or discard its solutions. -/
theorem UnifyRel.solutions {policy environment left right output}
    (derived : UnifyRel policy environment left right output)
    (normal : (eraseEnvironment environment).Normal) (valuation : String → Atom) :
    Theory.TypeSubstSatisfied valuation (eraseEnvironment output) ↔
      Theory.TypeSubstSatisfied valuation (eraseEnvironment environment) ∧
      applyTypeValuation valuation left.erase = applyTypeValuation valuation right.erase :=
  Spec.Type.Presentation.MatchSolutionTheory.AppliedTypePresentationMatchRel.solutions
    derived.erases normal valuation

theorem UnifyRel.exists_iff {policy environment left right} :
    (∃ output, UnifyRel policy environment left right output) ↔
      ∃ output, AppliedTypePresentationMatchRel (eraseEnvironment environment) left.erase right.erase output := by
  constructor
  · rintro ⟨output,derived⟩
    exact ⟨eraseEnvironment output,derived.erases⟩
  · rintro ⟨output,derived⟩
    obtain ⟨after,lifted,_⟩ := UnifyRel.lift (policy := policy) derived
    exact ⟨after,lifted⟩

/-- The reached contextual table earns a readout certificate for the actual
source-selected output constraints. No annotated table is reconstructed from
those constraints, and no future evaluation is assumed correct. -/
theorem UnifyRel.certifies {policy environment left right after} {incoming output : Bindings}
    (derived : UnifyRel policy environment left right after)
    (certified : ReadoutCertificate incoming (eraseEnvironment environment))
    (selected : UnifyCandidateRel left.erase right.erase incoming output) :
    ReadoutCertificate output (eraseEnvironment after) := by
  apply ReadoutCertificate.of_normal_theory (derived.output_normal certified.normal)
  intro valuation
  rw [derived.solutions certified.normal valuation,certified.theory valuation,selected.solutions valuation]
  exact and_comm

/-- Every surviving source candidate admits a contextual unification trace
and a certified reached table. Aliases and open operands are permitted; only
the ordinary equality-grounded source profile is used. -/
theorem UnifyRel.of_source_candidate {policy environment left right} {incoming output : Bindings}
    (certified : ReadoutCertificate incoming (eraseEnvironment environment))
    (selected : UnifyCandidateRel left.erase right.erase incoming output) :
    ∃ after, UnifyRel policy environment left right after ∧
      ReadoutCertificate output (eraseEnvironment after) := by
  obtain ⟨matched,matching,merged⟩ := selected
  obtain ⟨valuation,model⟩ := merged.2
  have premises := (UnifyCandidateRel.solutions ⟨matched,matching,merged⟩ valuation).mp model
  obtain ⟨table,ordinary,_normal,_satisfied⟩ :=
    Spec.Type.Presentation.Completeness.AppliedTypePresentationMatchRel.exists_of_satisfied
      certified.normal ((certified.theory valuation).mpr premises.2) left.erase right.erase premises.1
  obtain ⟨after,derived,_readout⟩ := UnifyRel.lift (policy := policy) ordinary
  exact ⟨after,derived,derived.certifies certified ⟨matched,matching,merged⟩⟩

/-- All physical work items in an independently completed source frontier
admit contextual binding traces. The paired list keeps its source order and
separate occurrences; equivalent unifiers are not new answer alternatives. -/
theorem UnifyRel.equation_frontier {policy environment query} {incoming : Bindings}
    {space : Space} {live : List Atom} {works : List EquationWork}
    (certified : ReadoutCertificate incoming (eraseEnvironment environment))
    (frontier : EquationFrontierRel space live query.erase incoming works) :
    ∃ environments, List.Forall₂ (fun work after =>
      UnifyRel policy environment query (ofAtom work.pattern) after ∧
      ReadoutCertificate work.bindings (eraseEnvironment after)) works environments := by
  have each : ∀ work ∈ works, ∃ after,
      UnifyRel policy environment query (ofAtom work.pattern) after ∧
      ReadoutCertificate work.bindings (eraseEnvironment after) := by
    intro work present
    obtain ⟨matched,occurrence⟩ := frontier.occurrence present
    apply UnifyRel.of_source_candidate certified
    simpa only [erase_ofAtom] using
      (show UnifyCandidateRel query.erase work.pattern incoming work.bindings from
        ⟨matched,occurrence.selected.2,occurrence.result.1⟩)
  suffices ∀ (items : List EquationWork),
      (∀ work ∈ items, ∃ after,
        UnifyRel policy environment query (ofAtom work.pattern) after ∧
        ReadoutCertificate work.bindings (eraseEnvironment after)) →
      ∃ environments, List.Forall₂ (fun work after =>
        UnifyRel policy environment query (ofAtom work.pattern) after ∧
        ReadoutCertificate work.bindings (eraseEnvironment after)) items environments from this works each
  intro items
  induction items with
  | nil => intro _; exact ⟨[],.nil⟩
  | cons work rest ih =>
      intro available
      obtain ⟨after,derived,certificate⟩ := available work List.mem_cons_self
      obtain ⟨remaining,paired⟩ := ih (fun work present => available work (List.mem_cons_of_mem _ present))
      exact ⟨after :: remaining,.cons ⟨derived,certificate⟩ paired⟩

/-- An already active root stays active under unmarked publication;
its children and binding frame are retained. -/
theorem publish_none_active (original : Atom) (frame : BindingFrame) (value : Value)
    (active : value.status = .active) : publish .none original frame value = value := by
  cases value <;> simp_all [publish,withStatus,Entry.publish,status,erase]

private def swap (name : String) : Value :=
  if name = "x" then .var "y" else if name = "y" then .var "x" else .var name

private def openHeld : Value := .expression .held [.var "x"]

/-- Reopening after an intermediate change fails the usual substitution
fusion law, even when both final syntaxes are identical. -/
theorem reopen_composition_separation :
    (substitute .reopenChanged swap (substitute .reopenChanged swap openHeld)).erase =
      (substitute .reopenChanged (compose .reopenChanged swap swap) openHeld).erase ∧
    substitute .reopenChanged swap (substitute .reopenChanged swap openHeld) ≠
      substitute .reopenChanged (compose .reopenChanged swap swap) openHeld := by
  constructor
  · simp [substitute,swap,openHeld,rebuildStatus,compose,erase]
  · intro same
    have statuses := congrArg status same
    simp [substitute,swap,openHeld,rebuildStatus,compose,erase,status] at statuses

/-- The same environment fusion does preserve the complete value under the
stable-data policy, rather than just its erased syntax. -/
theorem preserve_swaps_exact :
    substitute .preserve swap (substitute .preserve swap openHeld) = openHeld := by
  simp [substitute,swap,openHeld,rebuildStatus]

namespace Controls

def heldNested : Value := .expression .held
  [.symbol "Outer",.expression .held [.symbol "Inner"]]
def environment : Environment := [("x",heldNested)]
def bindings : Bindings := ⟨[("x",heldNested.erase)],[]⟩

theorem certificate : ReadoutCertificate bindings (eraseEnvironment environment) := by
  apply ReadoutCertificate.of_normal_theory
  · simp [eraseEnvironment,environment,heldNested,erase,
      TypeSubst.Normal,TypeSubst.keys,TypeSubst.typeVars,TypeSubst.typeVarsList]
  · intro valuation
    simp [Spec.Type.Presentation.Theory.TypeSubstSatisfied,TypeBindingSatisfied,
      bindings,eraseEnvironment,environment]

/-- A nonempty source environment delivers a nested held value under either
parent-rebuilding policy, with its certified materialization unchanged. -/
theorem nonempty_readout_delivers (policy : RebuildPolicy) (expected : Atom) :
    BindingFrame.Materialization (.selected bindings (eraseEnvironment environment) certificate)
      (.var "x") heldNested.erase ∧
    Entry.Rel .reuse (substitute policy (resolve environment) (.var "x")).status
      (substitute policy (resolve environment) (.var "x")).erase expected .deliver := by
  simpa only [heldNested,erase] using
    selected_held_variable_entry policy environment bindings "x"
      [.symbol "Outer",.expression .held [.symbol "Inner"]] certificate
      (by simp [environment,heldNested]) expected

theorem nested_statuses_retained (policy : RebuildPolicy) :
    substitute policy (resolve environment) (.var "x") = heldNested := by
  exact assigned_value_exact policy environment "x" heldNested (by simp [environment])

def activeEnvironment : Environment := [("x",heldNested.withStatus .active)]

/-- The same certified constraint readout admits different occurrence
statuses. A contextual-value refinement must retain more than that readout. -/
theorem constraint_certificate_does_not_determine_status :
    eraseEnvironment activeEnvironment = eraseEnvironment environment ∧
    ReadoutCertificate bindings (eraseEnvironment activeEnvironment) ∧
    (resolve activeEnvironment "x").status ≠ (resolve environment "x").status := by
  have same : eraseEnvironment activeEnvironment = eraseEnvironment environment := by
    simp [eraseEnvironment,activeEnvironment,environment]
  refine ⟨same,?_,?_⟩
  · rw [same]
    exact certificate
  · simp [resolve,activeEnvironment,environment,heldNested,withStatus,status]

def aliasEnvironment : Environment := [("x",.var "y")]
def aliasBindings : Bindings := ⟨[("x",.var "y")],[]⟩
def openHeldValue : Value := .expression .held
  [.symbol "F",.var "z",.expression .held [.var "z"]]
def unifiedEnvironment (policy : RebuildPolicy) : Environment :=
  bind policy aliasEnvironment "y" openHeldValue

theorem alias_certificate : ReadoutCertificate aliasBindings (eraseEnvironment aliasEnvironment) := by
  apply ReadoutCertificate.of_normal_theory
  · simp [aliasEnvironment,eraseEnvironment,erase,
      TypeSubst.Normal,TypeSubst.keys,TypeSubst.typeVars]
  · intro valuation
    simp [Theory.TypeSubstSatisfied,TypeBindingSatisfied,aliasBindings,aliasEnvironment,eraseEnvironment,erase]

/-- A nonempty alias is reconciled with an open, already-held value. The
trace is constructed for each policy, not inferred from a desired result. -/
theorem open_alias_unification (policy : RebuildPolicy) :
    UnifyRel policy aliasEnvironment (.var "y") openHeldValue (unifiedEnvironment policy) := by
  have first : substitute policy (resolve aliasEnvironment) (.var "y") = .var "y" := by
    simp [substitute,resolve,aliasEnvironment,List.lookup]
  have second : substitute policy (resolve aliasEnvironment) openHeldValue = openHeldValue := by
    cases policy <;> simp [substitute,resolve,aliasEnvironment,List.lookup,openHeldValue,rebuildStatus,erase]
  apply UnifyRel.ordinary
  rw [first,second]
  exact .bindLeft (by simp [openHeldValue,erase,TypeSubst.typeVars,TypeSubst.typeVarsList])

theorem open_alias_readout (policy : RebuildPolicy) :
    unifiedEnvironment policy = [("y",openHeldValue),("x",openHeldValue)] := by
  cases policy <;> simp [unifiedEnvironment,bind,aliasEnvironment,resolve,List.lookup,
    substitute,openHeldValue,rebuildStatus,erase]

/-- Every use of the old alias and the new binding retains the same whole
open value, including its nested held child. The free z remains unresolved. -/
theorem open_alias_shared_uses (policy : RebuildPolicy) :
    substitute policy (resolve (unifiedEnvironment policy))
      (.expression .active [.symbol "Pair",.var "x",.var "y",.var "x"]) =
      .expression .active [.symbol "Pair",openHeldValue,openHeldValue,openHeldValue] := by
  rw [open_alias_readout]
  cases policy <;> simp [substitute,resolve,List.lookup,rebuildStatus]

/-- Filling a genuinely free child illustrates the local policy boundary:
the final syntax agrees while readiness follows the chosen rebuilding rule. -/
theorem open_alias_policy_separation :
    let stable := resolve (bind .preserve (unifiedEnvironment .preserve) "z" (.symbol "Z")) "x"
    let reopened := resolve (bind .reopenChanged (unifiedEnvironment .reopenChanged) "z" (.symbol "Z")) "x"
    stable.erase = reopened.erase ∧ stable.status = .held ∧ reopened.status = .active := by
  dsimp only
  rw [open_alias_readout,open_alias_readout]
  simp [bind,resolve,List.lookup,substitute,openHeldValue,rebuildStatus,erase,status]

def matchedAlias : Bindings := Bindings.empty.assign "y" openHeldValue.erase
def sourceAliasOutput : Bindings :=
  ⟨matchedAlias.assignments ++ aliasBindings.assignments,
    matchedAlias.equalities ++ aliasBindings.equalities⟩

/-- The same open-alias example is independently admitted by the source
matcher and logical merger, with its whole incoming constraint retained. -/
theorem open_alias_source_candidate :
    UnifyCandidateRel (.var "y") openHeldValue.erase aliasBindings sourceAliasOutput := by
  have matching : Spec.Match.Merge.MatchRel Spec.Match.Merge.equalityGroundedSemantic
      (.var "y") openHeldValue.erase matchedAlias := by
    apply Spec.Match.Merge.MatchRel.varNonVar
    · simp [Spec.Match.Merge.isVariableB,openHeldValue,erase]
    · apply Spec.Match.Merge.semanticLoopFree_single_assignment
      rw [←Spec.Match.Merge.mem_vars_iff_atomOccurs]
      simp [openHeldValue,erase,Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars,
        Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars.varsList]
  refine ⟨matchedAlias,matching,Spec.Bindings.ScopeObservation.LogicalMergeRel.append_of_common_model ?_⟩
  let valuation : String → Atom := fun name => if name = "z" then .symbol "Z" else
    .expression [.symbol "F",.symbol "Z",.expression [.symbol "Z"]]
  refine ⟨valuation,?_,?_⟩
  · simp [TypeBindingSatisfied,matchedAlias,Bindings.empty,Bindings.assign,Bindings.isBound,
      Bindings.lookup,openHeldValue,erase,applyTypeValuation,valuation]
  · simp [TypeBindingSatisfied,aliasBindings,applyTypeValuation,valuation]

theorem open_alias_source_certificate (policy : RebuildPolicy) :
    ReadoutCertificate sourceAliasOutput (eraseEnvironment (unifiedEnvironment policy)) := by
  exact (open_alias_unification policy).certifies alias_certificate (by
    simpa only [erase] using open_alias_source_candidate)

/-- Different symbols remain incompatible under either annotation policy. -/
theorem different_symbols_refused (policy : RebuildPolicy) :
    ¬∃ after, UnifyRel policy [] (.symbol "A") (.symbol "B") after := by
  rintro ⟨after,derived⟩
  have raw := derived.erases
  cases raw with
  | ordinary leftRead rightRead matched =>
      simp only [eraseEnvironment,erase,List.map_nil,TypeSubst.apply] at leftRead rightRead
      subst leftRead
      subst rightRead
      exact AppliedReducedTypeMatchRel.no_distinct_symbols (by decide) matched

end Controls

end Value

end Entry

namespace Minimal

/-- Host representations used only by the minimal-instruction layer.  The
carrier contains data; injectivity and other properties are separate laws. -/
structure Services where
  /-- Opaque grounded representation of a complete binding set. -/
  bindingPayload : Bindings → GroundedValue
  /-- Opaque grounded handle for the current context space. -/
  contextPayload : Space → GroundedValue
  /-- Behavior of the internal `call-native` instruction. -/
  nativeCall : Atom → Atom → Atom → Bindings → ResultPair → Prop

/-- An ordered enumeration profile for the fuel-free evaluator.  `EvalRel`
describes which individual results are semantically possible; this relation
separately records the order and multiplicity exposed by `collapse-bind`.

The carrier is relational because the published semantics need not choose one
global scheduler.  A concrete operational profile may nevertheless be
functional. -/
structure Enumeration where
  results : Space → Atom → Atom → Bindings → ResultSet → Prop
  /-- Minimal execution has a different result boundary from full typed
  interpretation. Its semantic law is stated after `MinimalResultRel`. -/
  minimalResults : Space → Atom → Bindings → ResultSet → Prop

/-- Representation and ordered collection services configured at the host boundary. -/
structure HostPackage where
  services : Services
  enumeration : Enumeration

end Minimal

/-- Producer provenance distinguishes an ordinary emission from a value
whose interpretation has already completed. It is not inferred from syntax. -/
inductive NativeValueProvenance where
  | emitted
  | completed
  deriving DecidableEq, Repr

/-- A producer's binding boundary is separate from whether it has already
completed interpretation. Raw delivery retains the authored atom; materialized
delivery resolves its binding equations before dispatching the result. -/
inductive NativeBindingMode where
  | raw
  | materialized
  deriving DecidableEq, Repr

/-- Host-grounded operations are genuinely external to the MeTTa semantics.
The evaluator sees only an executable predicate and a relation of possible
host outcomes. -/
structure GroundedDispatch where
  executable : Atom → Prop
  outcome : Atom → List Atom → GroundedResult → Prop
  /-- Opaque minimal services are optional; core instructions do not require them. -/
  minimal : Option Minimal.HostPackage := none
  /-- The producer's completion boundary, shared by raw and full invocation. -/
  valueProvenance : Atom → List Atom → NativeValueProvenance := fun _ _ => .emitted
  /-- Binding resolution promised by this producer, before its result is read. -/
  bindingMode : Atom → List Atom → NativeBindingMode := fun _ _ => .raw
  /-- Presentation text for malformed primitive calls. The error subject and
  classification remain structural; a renderer may expose variable spelling. -/
  unifyBadArityMessage : Atom → String := HE.unifyBadArityMessage

/-- Native producer provenance is retained separately from materialization. -/
inductive NativeEmissionRel (dispatch : GroundedDispatch) (operator : Atom)
    (arguments : List Atom) (frame : BindingFrame) (raw : Atom) : Atom → Prop where
  | raw : dispatch.bindingMode operator arguments = .raw →
      NativeEmissionRel dispatch operator arguments frame raw raw
  | materialized {value : Atom} :
      dispatch.bindingMode operator arguments = .materialized →
      frame.Materialization raw value →
      NativeEmissionRel dispatch operator arguments frame raw value

theorem NativeEmissionRel.raw_iff {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom} {bindings : BindingFrame} {raw value : Atom}
    (mode : dispatch.bindingMode operator arguments = .raw) :
    NativeEmissionRel dispatch operator arguments bindings raw value ↔ value = raw := by
  constructor
  · intro emitted
    cases emitted with
    | raw => rfl
    | materialized opposite _ => simp [mode] at opposite
  · rintro rfl
    exact .raw mode

theorem NativeEmissionRel.materialized_iff {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom} {bindings : BindingFrame} {raw value : Atom}
    (mode : dispatch.bindingMode operator arguments = .materialized) :
    NativeEmissionRel dispatch operator arguments bindings raw value ↔
      bindings.Materialization raw value := by
  constructor
  · intro emitted
    cases emitted with
    | raw opposite => simp [mode] at opposite
    | materialized _ resolved => exact resolved
  · exact .materialized mode

/-- The exact producer contract retains the complete binding observation
without allowing it to substitute for the operational result syntax. -/
theorem NativeEmissionRel.preserves_model {dispatch : GroundedDispatch} {operator : Atom}
    {arguments : List Atom} {bindings : BindingFrame} {raw value : Atom}
    (emitted : NativeEmissionRel dispatch operator arguments bindings raw value)
    (valuation : String → Atom)
    (satisfied : Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation bindings) :
    Spec.Type.RuntimeRefinement.applyTypeValuation valuation value =
      Spec.Type.RuntimeRefinement.applyTypeValuation valuation raw := by
  cases emitted with
  | raw => rfl
  | materialized _ resolved => exact resolved.preserves_model valuation satisfied

namespace Minimal

/-- Encode one semantic result in the exact pair shape consumed by
`superpose-bind`. -/
def encodeResult (services : Services) (result : ResultPair) : Atom :=
  .expression [result.1, .grounded (services.bindingPayload result.2)]

/-- Encode an ordered list of results without changing order or multiplicity. -/
def encodeResults (services : Services) (results : ResultSet) : Atom :=
  .expression (results.map (encodeResult services))

/-- Embedded instructions are interpreted by the minimal machine, not by
ordinary argument evaluation. `return` is a function-body delimiter rather
than an executable instruction. -/
def embeddedInstruction : Atom → Bool
  | .expression (.symbol head :: _) =>
      head ∈ ["eval", "evalc", "chain", "unify", "cons-atom", "decons-atom",
        "function", "collapse-bind", "superpose-bind", "metta",
        "context-space", "call-native"]
  | _ => false

/-- Observation of a materialized, noninstruction function-body terminal.
The nearest saved caller supplies the NoReturn subject; an outermost function
instead reports its terminal. This boundary does not execute a body or
materialize its syntax. -/
def functionTerminalResult (caller : Option Atom) (terminal : Atom) : Atom :=
  match terminal with
  | .expression [.symbol "return", value] => value
  | _ => Atom.error (caller.getD terminal) (.symbol "NoReturn")


def IsChain (atom : Atom) : Prop :=
  ∃ tail, atom = .expression (.symbol "chain" :: tail)

def IsFunction (atom : Atom) : Prop :=
  ∃ body, atom = .expression [.symbol "function", body]

def HostCall (dispatch : GroundedDispatch) (atom : Atom) : Prop :=
  ∃ operator arguments, atom = .expression (operator :: arguments) ∧
    dispatch.executable operator

/-- Structural substitution of the explicit chain binder. Other caller
variables remain in the carried binding frame. No fixed depth bound is used. -/
def substituteName (name : String) (replacement : Atom) : Atom → Atom
  | .symbol symbol => .symbol symbol
  | .grounded value => .grounded value
  | .var varName => if varName = name then replacement else .var varName
  | .expression atoms => .expression (atoms.map (substituteName name replacement))

/-- Install a concrete minimal host package without changing native dispatch. -/
def withHost (dispatch : GroundedDispatch) (services : Services)
    (enumeration : Enumeration) : GroundedDispatch :=
  { dispatch with minimal := some ⟨services, enumeration⟩ }

end Minimal

/-- The equation-query lane applies only when neither native dispatch nor
minimal instruction dispatch owns the invocation. Authored library operations
use this lane through their actual stored equations. -/
def NonGroundedCallRel (dispatch : GroundedDispatch) (atom : Atom) : Prop :=
  ¬Minimal.HostCall dispatch atom ∧ Minimal.embeddedInstruction atom = false

/-! ## Type-service boundary and ordered candidate selection -/

/-- One selected function-type policy.  The proof field keeps the argument
and return projections tied to the same arrow presentation; downstream
consumers never reconstruct them independently. -/
structure SelectedTypePolicy where
  functionType : Atom
  argumentTypes : List Atom
  returnType : Atom
  isFunction : FunctionTypeRel functionType argumentTypes returnType

/-- One fresh whole-arrow instance protects every domain position together. -/
theorem SelectedTypePolicy.argumentTypes_avoid (selected : SelectedTypePolicy)
    {forbidden : List String}
    (fresh : Freshness.AtomAvoids selected.functionType forbidden) :
    Freshness.AtomsAvoid selected.argumentTypes forbidden :=
  fun name member => fresh name (selected.isFunction.argumentVars_subset name member)

theorem SelectedTypePolicy.returnType_avoids (selected : SelectedTypePolicy)
    {forbidden : List String}
    (fresh : Freshness.AtomAvoids selected.functionType forbidden) :
    Freshness.AtomAvoids selected.returnType forbidden :=
  fun name member => fresh name (selected.isFunction.returnVars_subset name member)

/-- One candidate's applicability result.  A successful candidate supplies
the exact policy that later evaluation consumes as well as the bindings
produced by the applicability check. -/
inductive SelectedTypeApplicabilityOutcome where
  | success (policy : SelectedTypePolicy) (bindings : Bindings)
  | error (errors : List Atom)

/-- Result of the published left-to-right function-candidate scan.  Success
stops the scan immediately and carries one coherent selected policy plus the
bindings produced by applicability.  Exhaustion retains every ordered error
block from every failed function candidate and records whether a non-function
candidate made tuple fallback eligible. -/
inductive FunctionCandidateScanOutcome where
  | success (policy : SelectedTypePolicy) (bindings : Bindings)
  | exhausted (errors : List Atom) (tupleEligible : Bool)

/-- Literal transcription of the candidate loop in `interpret_expression`
(`Specs/he_metta_official_specs.md:172-210`): non-functions enable tuple
fallback, failed functions accumulate errors, and the first applicable
function stops the scan. -/
inductive FunctionCandidateScanRel
    (applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop)
    (space : Space)
    (expression expectedType : Atom) (bindings : Bindings) :
    List Atom → FunctionCandidateScanOutcome → Prop where
  | nil :
      FunctionCandidateScanRel applicability space expression expectedType bindings
        [] (.exhausted [] false)
  | nonFunctionSuccess {candidate : Atom} {candidates : List Atom}
      {policy : SelectedTypePolicy} {output : Bindings} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | nonFunctionExhausted {candidate : Atom} {candidates errors : List Atom}
      {tupleEligible : Bool} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.exhausted errors tupleEligible) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.exhausted errors true)
  | functionSuccess {candidate : Atom} {candidates argumentTypes : List Atom}
      {returnType : Atom} {policy : SelectedTypePolicy}
      {output : Bindings} :
      FunctionTypeRel candidate argumentTypes returnType →
      applicability space expression candidate expectedType bindings
        (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | functionFailureThenSuccess
      {candidate : Atom} {candidates argumentTypes : List Atom}
      {candidateReturn : Atom} {candidateErrors : List Atom}
      {policy : SelectedTypePolicy}
      {output : Bindings} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ candidatePolicy candidateBindings,
        ¬applicability space expression candidate expectedType bindings
          (.success candidatePolicy candidateBindings)) →
      applicability space expression candidate expectedType bindings
        (.error candidateErrors) →
      candidateErrors ≠ [] →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | functionFailureExhausted
      {candidate : Atom} {candidates argumentTypes errors : List Atom}
      {candidateReturn : Atom} {candidateErrors : List Atom}
      {tupleEligible : Bool} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ candidatePolicy candidateBindings,
        ¬applicability space expression candidate expectedType bindings
          (.success candidatePolicy candidateBindings)) →
      applicability space expression candidate expectedType bindings
        (.error candidateErrors) →
      candidateErrors ≠ [] →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.exhausted errors tupleEligible) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates)
        (.exhausted (candidateErrors ++ errors) tupleEligible)

/-! ### Scan boundary algebra -/

/-- Every successful ordered scan is justified by one candidate in the
original list.  Downstream conformance proofs consume this theorem instead of
unfolding the scan recursion. -/
theorem FunctionCandidateScanRel.success_candidate
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {policy : SelectedTypePolicy}
    {output : Bindings}
    (scan : FunctionCandidateScanRel applicability space expression
      expectedType bindings candidates (.success policy output)) :
    ∃ candidate ∈ candidates,
      applicability space expression candidate expectedType bindings
        (.success policy output) := by
  generalize outcomeEq :
      (.success policy output : FunctionCandidateScanOutcome) = outcome at scan
  revert policy output
  induction scan with
  | nil =>
      intro policy output outcomeEq
      cases outcomeEq
  | nonFunctionSuccess _ tail ih =>
      intro policy output outcomeEq
      cases outcomeEq
      obtain ⟨candidate, member, applicable⟩ := ih rfl
      exact ⟨candidate, by simp [member], applicable⟩
  | nonFunctionExhausted =>
      intro policy output outcomeEq
      cases outcomeEq
  | functionSuccess _ applicable =>
      intro policy output outcomeEq
      cases outcomeEq
      exact ⟨_, by simp, applicable⟩
  | functionFailureThenSuccess _ _ _ _ tail ih =>
      intro policy output outcomeEq
      cases outcomeEq
      obtain ⟨candidate, member, applicable⟩ := ih rfl
      exact ⟨candidate, by simp [member], applicable⟩
  | functionFailureExhausted =>
      intro policy output outcomeEq
      cases outcomeEq

/-- An exhausted scan has no successful applicability derivation for any
function candidate in the scanned list.  This is the exact negative boundary
used by tuple fallback and error rules. -/
theorem FunctionCandidateScanRel.exhausted_no_function_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates errors : List Atom} {tupleEligible : Bool}
    (scan : FunctionCandidateScanRel applicability space expression
      expectedType bindings candidates (.exhausted errors tupleEligible)) :
    ∀ candidate ∈ candidates,
      (∃ argumentTypes returnType,
        FunctionTypeRel candidate argumentTypes returnType) →
      ∀ policy output,
        ¬applicability space expression candidate expectedType bindings
          (.success policy output) := by
  generalize outcomeEq :
      (.exhausted errors tupleEligible : FunctionCandidateScanOutcome) =
        outcome at scan
  revert errors tupleEligible
  induction scan with
  | nil =>
      intro errors tupleEligible outcomeEq candidate member
      simp at member
  | nonFunctionSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | nonFunctionExhausted notFunction _ ih =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
      intro candidate member isFunction policy output applicable
      rcases List.mem_cons.mp member with candidateEq | member
      · subst candidate
        exact notFunction isFunction
      · exact ih rfl candidate member isFunction policy output applicable

  | functionSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | functionFailureThenSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | functionFailureExhausted _ noSuccess _ _ _ ih =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
      intro candidate member isFunction policy output applicable
      rcases List.mem_cons.mp member with candidateEq | member
      · subst candidate
        exact noSuccess policy output applicable
      · exact ih rfl candidate member isFunction policy output applicable

/-! ### Generic exact-scan assembly

The concrete runtime bridge supplies one exact classification per candidate.
The two lemmas below are the only place that classification is threaded into
the published left-to-right scan.  Runtime-specific conformance modules never
reimplement the scan induction. -/

/-- Exact evidence for one candidate that did not stop the scan.  A
non-function enables tuple fallback without contributing an error; a failed
function contributes one nonempty ordered error block and includes the
negative success fact required by `FunctionCandidateScanRel`. -/
inductive FunctionCandidateFailureRel
    (applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop)
    (space : Space) (expression expectedType : Atom)
    (bindings : Bindings) : Atom → (List Atom × Bool) → Prop where
  | nonFunction {candidate : Atom} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateFailureRel applicability space expression expectedType
        bindings candidate ([], true)
  | functionFailure {candidate : Atom} {argumentTypes : List Atom}
      {candidateReturn : Atom} {errors : List Atom} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ policy output,
        ¬applicability space expression candidate expectedType bindings
          (.success policy output)) →
      applicability space expression candidate expectedType bindings
        (.error errors) →
      errors ≠ [] →
      FunctionCandidateFailureRel applicability space expression expectedType
        bindings candidate (errors, false)

/-- Errors contributed by a list of exact failed-candidate summaries, in
source order. -/
def functionCandidateFailureErrors :
    List (List Atom × Bool) → List Atom
  | [] => []
  | (errors, _) :: summaries =>
      errors ++ functionCandidateFailureErrors summaries

/-- The recursive failure readout is exactly row-major flattening of the
per-candidate error blocks. -/
theorem functionCandidateFailureErrors_eq_flatten_map_fst
    (summaries : List (List Atom × Bool)) :
    functionCandidateFailureErrors summaries =
      (summaries.map Prod.fst).flatten := by
  induction summaries with
  | nil => rfl
  | cons summary summaries inductionHypothesis =>
      rcases summary with ⟨errors, eligible⟩
      simp [functionCandidateFailureErrors, inductionHypothesis]

/-- Whether any exact failed-candidate summary enables tuple fallback. -/
def functionCandidateFailureTupleEligible :
    List (List Atom × Bool) → Bool
  | [] => false
  | (_, eligible) :: summaries =>
      eligible || functionCandidateFailureTupleEligible summaries

/-- A pointwise exact failure classification reconstructs the complete
exhausted scan, including error order and tuple eligibility. -/
theorem FunctionCandidateScanRel.of_all_failures
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {summaries : List (List Atom × Bool)}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) candidates summaries) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings candidates
      (.exhausted (functionCandidateFailureErrors summaries)
        (functionCandidateFailureTupleEligible summaries)) := by
  induction failures with
  | nil => exact .nil
  | @cons candidate summary candidates summaries failure _ ih =>
      cases failure with
      | nonFunction notFunction =>
          simpa [functionCandidateFailureErrors,
            functionCandidateFailureTupleEligible] using
            (FunctionCandidateScanRel.nonFunctionExhausted
              notFunction ih)
      | functionFailure isFunction noSuccess errors nonempty =>
          simpa [functionCandidateFailureErrors,
            functionCandidateFailureTupleEligible] using
            (FunctionCandidateScanRel.functionFailureExhausted
              isFunction noSuccess errors nonempty ih)

/-- Exact failures preceding an already-derived success may be prepended
without reopening the scan proof. -/
theorem FunctionCandidateScanRel.prepend_failures_to_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {failedCandidates tail : List Atom}
    {summaries : List (List Atom × Bool)}
    {policy : SelectedTypePolicy} {output : Bindings}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) failedCandidates summaries)
    (tailSuccess : FunctionCandidateScanRel applicability space expression
      expectedType bindings tail (.success policy output)) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings (failedCandidates ++ tail) (.success policy output) := by
  induction failures with
  | nil => simpa using tailSuccess
  | @cons candidate summary candidates summaries failure _ ih =>
      cases failure with
      | nonFunction notFunction =>
          simpa using FunctionCandidateScanRel.nonFunctionSuccess
            notFunction ih
      | functionFailure isFunction noSuccess errors nonempty =>
          simpa using FunctionCandidateScanRel.functionFailureThenSuccess
            isFunction noSuccess errors nonempty ih

/-- Generic first-success assembly: a list of exact failures followed by one
exact successful candidate yields the published ordered-scan result; the
uninspected suffix is intentionally irrelevant. -/
theorem FunctionCandidateScanRel.of_first_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {failedCandidates suffix : List Atom}
    {summaries : List (List Atom × Bool)}
    {candidate : Atom} {argumentTypes : List Atom} {returnType : Atom}
    {policy : SelectedTypePolicy} {output : Bindings}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) failedCandidates summaries)
    (isFunction : FunctionTypeRel candidate argumentTypes returnType)
    (success : applicability space expression candidate expectedType bindings
      (.success policy output)) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings (failedCandidates ++ candidate :: suffix)
        (.success policy output) := by
  apply FunctionCandidateScanRel.prepend_failures_to_success failures
  exact FunctionCandidateScanRel.functionSuccess isFunction success

/-- The exact type interface consumed by the six evaluator judgments.  One
service supplies both positive and negative premises; mixing a permissive
positive layer with a different negative candidate set is unrepresentable.

`candidateScan` is deliberately a single ordered relation rather than a bare
applicability predicate: first-success and all-failed outcomes must quantify
over the same exact candidate sequence.

Complete enumeration is supplied separately from storage. Concrete ordered
runtime profiles are defined downstream and must name that choice. -/
structure EvalTypeService where
  typesOf : Space → Atom → List Atom → Prop
  typeCast : List String → Space → Atom → Atom → Bindings → ResultPair → Prop
  instantiateTypes : List String → List Atom → List Atom → Prop :=
    fun _ raw selected => selected = raw
  candidateScan :
    List String → Space → Atom → Atom → Bindings →
      List Atom → FunctionCandidateScanOutcome → Prop

/-- Lift one singular published applicability fact into the block-valued
policy-carrying scan interface.  Error blocks assembled from the complete
published argument/return traversal are supplied by the exact service
instance; this constructor remains the reusable singleton brick. -/
inductive PublishedCandidateApplicabilityRel
    (space : Space) (expression candidate expectedType : Atom)
    (bindings : Bindings) : SelectedTypeApplicabilityOutcome →
      (lookup : TypeLookupRel := rawTypeLookupRel space) → Prop where
  | success {argumentTypes : List Atom} {returnType : Atom}
      {output : Bindings}
      (isFunction : FunctionTypeRel candidate argumentTypes returnType)
      (applicable : ApplicabilityRel space (lookup := lookup) expression candidate expectedType
        bindings (.success output)) :
      PublishedCandidateApplicabilityRel space (lookup := lookup) expression candidate
        expectedType bindings
        (.success ⟨candidate, argumentTypes, returnType, isFunction⟩ output)
  | error {errorAtom : Atom}
      (applicable : ApplicabilityRel space (lookup := lookup) expression candidate expectedType
        bindings (.error errorAtom)) :
      PublishedCandidateApplicabilityRel space (lookup := lookup) expression candidate
        expectedType bindings (.error [errorAtom])

/-- Published-scan success exposes the exact selected arrow and the
spec-threaded applicability bindings.  In particular, the policy witness and
the binding output cannot originate from different candidates. -/
theorem published_scan_success_selected
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {policy : SelectedTypePolicy}
    {output : Bindings} {lookup : TypeLookupRel}
    (scan : FunctionCandidateScanRel
      (fun context subject candidate demand incoming outcome =>
        PublishedCandidateApplicabilityRel context subject candidate demand incoming outcome (lookup := lookup))
      space expression expectedType bindings candidates
        (.success policy output)) :
    policy.functionType ∈ candidates ∧
      ApplicabilityRel space expression policy.functionType expectedType (lookup := lookup)
        bindings (.success output) := by
  obtain ⟨candidate, member, applicable⟩ := scan.success_candidate
  cases applicable with
  | success _ applicability => exact ⟨member, applicability⟩

/-- Evaluation services for an explicitly chosen complete enumeration.
Neither first-success boundary identifies it with physical storage order. -/
def enumeratedTypeService (enumeration : TypeEnumeration) : EvalTypeService where
  typesOf := enumeration.query
  typeCast := fun _ space => TypeCastRel space (lookup := enumerationLookup enumeration space)
  candidateScan := fun _ => FunctionCandidateScanRel
    (fun space expression candidate expected bindings outcome =>
      PublishedCandidateApplicabilityRel space expression candidate expected bindings outcome
        (lookup := enumerationLookup enumeration space))

/-- The historical list-storage instance of the type-service interface.
Its ordered correspondences do not assert language-level storage order. -/
def storageTypeService : EvalTypeService where
  typesOf := StorageTypesRel
  typeCast := fun _ => TypeCastRel
  candidateScan := fun _ => FunctionCandidateScanRel PublishedCandidateApplicabilityRel

private def scanFailureType : Atom :=
  .expression [.symbol "->", .symbol "A"]

private def scanSuccessType : Atom :=
  .expression [.symbol "->", .symbol "B"]

private def scanSuccessPolicy : SelectedTypePolicy :=
  ⟨scanSuccessType, [], .symbol "B", rfl⟩

private def scanExpression : Atom :=
  .expression [.symbol "scan-target"]

private def scanFailure : Atom :=
  mkError scanExpression (.badType Atom.undefinedType (.symbol "A"))

private def orderedScanCanaryApplicability
    (_space : Space) (_expression functionType _expectedType : Atom)
    (_bindings : Bindings)
  (outcome : SelectedTypeApplicabilityOutcome) : Prop :=
  (functionType = scanFailureType ∧ outcome = .error [scanFailure]) ∨
  (functionType = scanSuccessType ∧
    outcome = .success scanSuccessPolicy Bindings.empty)

/-- Positive order canary: a failed first function candidate is recorded and
the second successful candidate is selected. -/
theorem ordered_scan_skips_failed_candidate :
    FunctionCandidateScanRel orderedScanCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      [scanFailureType, scanSuccessType]
      (.success scanSuccessPolicy Bindings.empty) := by
  apply FunctionCandidateScanRel.functionFailureThenSuccess
      (argumentTypes := []) (candidateReturn := .symbol "A")
      (candidateErrors := [scanFailure])
  · rfl
  · intro candidatePolicy candidateBindings hsuccess
    simp [orderedScanCanaryApplicability, scanFailureType, scanSuccessType,
      scanSuccessPolicy]
      at hsuccess
  · simp [orderedScanCanaryApplicability]
  · simp
  · apply FunctionCandidateScanRel.functionSuccess
        (argumentTypes := []) (returnType := .symbol "B")
        (policy := scanSuccessPolicy) (output := Bindings.empty)
    · rfl
    · exact Or.inr ⟨rfl, rfl⟩

/-- Negative order canary: once the head function candidate succeeds, the
same candidate list cannot be presented as exhausted, so tuple fallback and
all-failed errors are unavailable. -/
theorem ordered_scan_first_success_excludes_exhaustion
    (candidates errors : List Atom) (tupleEligible : Bool) :
    ¬FunctionCandidateScanRel orderedScanCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      (scanSuccessType :: candidates) (.exhausted errors tupleEligible) := by
  intro hscan
  cases hscan with
  | nonFunctionExhausted hnot _ =>
      exact hnot ⟨[], .symbol "B", rfl⟩
  | functionFailureExhausted _ hnoSuccess _ _ _ =>
      exact hnoSuccess scanSuccessPolicy Bindings.empty (by
        simp [orderedScanCanaryApplicability, scanSuccessPolicy])

private def scanArityFailure : Atom :=
  mkError scanExpression .incorrectNumberOfArguments

private def scanArgumentFailure : Atom :=
  mkError scanExpression
    (.badArgType 1 (.symbol "B") (.symbol "C"))

private def orderedBlockCanaryApplicability
    (_space : Space) (_expression functionType _expectedType : Atom)
    (_bindings : Bindings)
    (outcome : SelectedTypeApplicabilityOutcome) : Prop :=
  (functionType = scanFailureType ∧
    outcome = .error [scanArityFailure]) ∨
  (functionType = scanSuccessType ∧
    outcome = .error [scanArgumentFailure])

/-- W16 order canary: complete failed-candidate blocks are concatenated in
function-candidate scan order and remain contiguous.  This is the
cross-candidate order observed at the HE reference revision used by the
conformance suite. -/
theorem ordered_scan_concatenates_candidate_error_blocks :
    FunctionCandidateScanRel orderedBlockCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      [scanFailureType, scanSuccessType]
      (.exhausted [scanArityFailure, scanArgumentFailure] false) := by
  apply FunctionCandidateScanRel.functionFailureExhausted
      (argumentTypes := []) (candidateReturn := .symbol "A")
      (candidateErrors := [scanArityFailure])
  · rfl
  · intro policy output success
    simp [orderedBlockCanaryApplicability] at success
  · exact Or.inl ⟨rfl, rfl⟩
  · simp
  · apply FunctionCandidateScanRel.functionFailureExhausted
        (argumentTypes := []) (candidateReturn := .symbol "B")
        (candidateErrors := [scanArgumentFailure])
    · rfl
    · intro policy output success
      simp [orderedBlockCanaryApplicability] at success
    · exact Or.inr ⟨rfl, rfl⟩
    · simp
    · exact .nil

/-! ## Shared full/minimal evaluator judgments -/

/-- Variables of the complete expected application that remain public while
its operator head is evaluated.  A type service may introduce fresh private
names, but none may collide with this enclosing scope. -/
def expectedApplicationScope (expression expectedType : Atom) : List String :=
  (TypeSubst.typeVars expectedType ++ TypeSubst.typeVars expression).eraseDups

/-- Names protected at a typed use: inherited saved scope, live syntax,
complete subject and demand, and every current constraint name. -/
def invocationTypeScope (protectedScope : List String) (live : List Atom)
    (subject expected : Atom) (bindings : Bindings) : List String :=
  protectedScope ++ TypeSubst.typeVarsList (live ++ [subject, expected]) ++
    Spec.Bindings.ScopeObservation.specBindingVars bindings

/-- Re-entering the same query protects the same name set. List duplication
does not add a semantic freshness obligation. A different nested demand may
still introduce additional names and must be protected at its own use. -/
theorem invocationTypeScope_idempotent_mem (protectedScope : List String) (live : List Atom)
    (subject expected : Atom) (bindings : Bindings) (name : String) :
    name ∈ invocationTypeScope
      (invocationTypeScope protectedScope live subject expected bindings) [] subject expected bindings ↔
    name ∈ invocationTypeScope protectedScope live subject expected bindings := by
  have localIncluded : name ∈ TypeSubst.typeVarsList [subject, expected] →
      name ∈ TypeSubst.typeVarsList (live ++ [subject, expected]) := by
    induction live with
    | nil => exact id
    | cons head tail ih =>
        exact fun member => List.mem_append_right _ (ih member)
  simp only [invocationTypeScope, List.nil_append, List.mem_append]
  tauto

/-- Scope-aware lookup for any complete enumeration. Fresh instantiation
does not choose the enumeration or identify it with storage order. -/
def scopedEnumerationTypeLookup (enumeration : TypeEnumeration)
    (protectedScope : List String) (space : Space) : TypeLookupRel :=
  fun bindings subject expected candidates =>
    ∃ raw, enumeration.query space subject raw ∧
      ArgumentAlphaVariantsRel (invocationTypeScope protectedScope [] subject expected bindings)
        raw candidates

/-- The historical scoped list-storage profile. -/
def scopedTypeLookup (protectedScope : List String) (space : Space) : TypeLookupRel :=
  fun bindings subject expected candidates =>
    ∃ raw, StorageTypesRel space subject raw ∧
      ArgumentAlphaVariantsRel (invocationTypeScope protectedScope [] subject expected bindings)
        raw candidates

/-- A scoped query's complete fresh family avoids every retained name in
its protected scope, independently of the chosen coherent enumeration. -/
theorem scopedEnumerationTypeLookup_fresh
    {enumeration : TypeEnumeration} {protectedScope : List String} {space : Space}
    {bindings : Bindings} {subject expected : Atom} {candidates : List Atom}
    (queried : scopedEnumerationTypeLookup enumeration protectedScope space bindings subject expected candidates) :
    Freshness.AtomsAvoid candidates protectedScope := by
  obtain ⟨_,_,variants⟩ := queried
  intro name used forbidden
  exact variants.target_vars_fresh name used
    (by simp [invocationTypeScope,forbidden])

theorem scopedTypeLookup_fresh
    {protectedScope : List String} {space : Space} {bindings : Bindings}
    {subject expected : Atom} {candidates : List Atom}
    (queried : scopedTypeLookup protectedScope space bindings subject expected candidates) :
    Freshness.AtomsAvoid candidates protectedScope := by
  exact scopedEnumerationTypeLookup_fresh (enumeration := TypeEnumeration.storage) queried

/-- A fixed enumeration and fixed syntactic query depend on protected-name
membership, rather than the order or representative orientation of the binding
record. This law does not identify queries on different materialized subjects. -/
theorem scopedEnumerationTypeLookup_congr
    (enumeration : TypeEnumeration) (space : Space)
    {firstScope secondScope : List String} {first second : Bindings}
    (scopes : ∀ name, name ∈ firstScope ↔ name ∈ secondScope)
    (agreement : BindingSourceAgreement first second)
    (subject expected : Atom) (candidates : List Atom) :
    scopedEnumerationTypeLookup enumeration firstScope space first subject expected candidates ↔
      scopedEnumerationTypeLookup enumeration secondScope space second subject expected candidates := by
  have scopeEq : ∀ name,
      name ∈ invocationTypeScope firstScope [] subject expected first ↔
      name ∈ invocationTypeScope secondScope [] subject expected second := by
    intro name
    simp only [invocationTypeScope, List.mem_append]
    rw [scopes name, agreement.support name]
  constructor
  · rintro ⟨raw, queried, variants⟩
    exact ⟨raw, queried, variants.restrict (fun name member => (scopeEq name).mpr member)⟩
  · rintro ⟨raw, queried, variants⟩
    exact ⟨raw, queried, variants.restrict (fun name member => (scopeEq name).mp member)⟩

/-- A scope-aware evaluator service for an explicitly chosen enumeration. -/
def scopedEnumeratedTypeService (enumeration : TypeEnumeration) : EvalTypeService where
  typesOf := enumeration.query
  instantiateTypes := ArgumentAlphaVariantsRel
  typeCast := fun scope space subject expected bindings result =>
    TypeCastRel space subject expected bindings result
      (lookup := scopedEnumerationTypeLookup enumeration scope space)
  candidateScan := fun scope space expression expected bindings candidates selected =>
    FunctionCandidateScanRel
      (fun context subject candidate demand incoming outcome =>
        PublishedCandidateApplicabilityRel context subject candidate demand incoming outcome
          (lookup := scopedEnumerationTypeLookup enumeration scope context))
      space expression expected bindings candidates selected

/-- The explicit scope-aware list-storage service. Its alpha witnesses
specify legal local instances, not native fresh-ID text. -/
def scopedStorageTypeService : EvalTypeService where
  typesOf := StorageTypesRel
  instantiateTypes := ArgumentAlphaVariantsRel
  typeCast := fun scope space subject expected bindings result =>
    TypeCastRel space subject expected bindings result (lookup := scopedTypeLookup scope space)
  candidateScan := fun scope space expression expected bindings candidates selected =>
    FunctionCandidateScanRel
      (fun context subject candidate demand incoming outcome =>
        PublishedCandidateApplicabilityRel context subject candidate demand incoming outcome
          (lookup := scopedTypeLookup scope context))
      space expression expected bindings candidates selected

/-- Completed values are held for Undefined demand as well as the ordinary
intrinsic passthrough cases. No call or function syntax is activated here. -/
def CompletedNativeKeepRel (value expectedType : Atom) : Prop :=
  IsEmptyOrErrorRel value ∨ expectedType = Atom.undefinedType ∨
    expectedType = Atom.atomType ∨
    ∃ metaType, MetaTypeRel value metaType ∧
      (expectedType = metaType ∨ metaType = Atom.variableType)

/-- The return judgment for producer-completed values. A required cast is
the existing type service, not recursive interpretation of the value. -/
inductive CompletedNativeReturnRel
    (space : Space) (typing : EvalTypeService) (value expectedType : Atom)
    (frame : BindingFrame) : FrameResult →
      (protectedScope : List String := []) → Prop where
  | keep : CompletedNativeKeepRel value expectedType →
      CompletedNativeReturnRel space typing value expectedType frame (protectedScope := protectedScope) (value, frame)
  | cast {result : FrameResult} :
      ¬CompletedNativeKeepRel value expectedType →
      typing.typeCast protectedScope space value expectedType frame.bindings (BindingFrame.rawResult result) →
      BindingFrame.Update .renew frame result.2 →
      CompletedNativeReturnRel space typing value expectedType frame (protectedScope := protectedScope) result


open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

mutual

/-- Evaluate one atom to one raw result. -/
inductive EvalAtomRawRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) → Prop where
  | emptyOrError (atom expectedType : Atom) (bindings : BindingFrame) :
      IsEmptyOrErrorRel atom →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (atom, bindings)
  | typePass (atom expectedType metaType : Atom) (bindings : BindingFrame) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      (expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (atom, bindings)
  | cast (atom expectedType metaType : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      ((∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) →
      typing.typeCast (invocationTypeScope protectedScope live atom expectedType bindings)
        space atom expectedType bindings result →
      BindingFrame.Update .renew bindings result.2 →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result
  | interpretSuccess (atom expectedType metaType : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      (∃ head tail, atom = .expression (head :: tail)) →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result →
      ¬IsErrorRel result.1 →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result
  | interpretError (atom expectedType metaType : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      (∃ head tail, atom = .expression (head :: tail)) →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result →
      IsErrorRel result.1 →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings result

/-- Interpret an expression through a function type, tuple fallback, or
operator-type error. -/
inductive InterpretExpressionRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) → Prop where
  | functionPath (expression expectedType operator : Atom)
      (arguments rawTypes types : List Atom)
      (policy : SelectedTypePolicy) (callType : Atom)
      (bindings applicableBindings : BindingFrame)
      (interpreted callResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator rawTypes →
      typing.instantiateTypes
        (invocationTypeScope protectedScope live expression expectedType bindings) rawTypes types →
      typing.candidateScan (invocationTypeScope protectedScope live expression expectedType bindings)
        space expression expectedType bindings
        types (.success policy applicableBindings) →
      BindingFrame.Update .renew bindings applicableBindings →
      callType = (if policy.returnType = Atom.expressionType
        then Atom.undefinedType else policy.returnType) →
      InterpretFunctionRel space dispatch (callType :: live) (protectedScope := protectedScope) (typing := typing)
        expression policy.functionType expectedType
          applicableBindings interpreted →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        interpreted.1 callType interpreted.2 callResult →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression expectedType bindings callResult
  | tuplePath (expression expectedType operator : Atom)
      (arguments rawTypes types errors : List Atom) (bindings : BindingFrame)
      (tupleResult callResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator rawTypes →
      typing.instantiateTypes
        (invocationTypeScope protectedScope live expression expectedType bindings) rawTypes types →
      typing.candidateScan (invocationTypeScope protectedScope live expression expectedType bindings)
        space expression expectedType bindings
        types (.exhausted errors true) →
      InterpretTupleRel space dispatch (expectedType :: live) (protectedScope := protectedScope) (typing := typing)
        expression bindings tupleResult →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        tupleResult.1 expectedType tupleResult.2 callResult →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression expectedType bindings callResult
  | functionError (expression expectedType operator errorAtom : Atom)
      (arguments rawTypes types errors : List Atom) (tupleEligible : Bool)
      (bindings : BindingFrame) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator rawTypes →
      typing.instantiateTypes
        (invocationTypeScope protectedScope live expression expectedType bindings) rawTypes types →
      typing.candidateScan (invocationTypeScope protectedScope live expression expectedType bindings)
        space expression expectedType bindings
        types (.exhausted errors tupleEligible) →
      errorAtom ∈ errors →
      InterpretExpressionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression expectedType bindings (errorAtom, bindings)

/-- Evaluate a function head, then its arguments. -/
inductive InterpretFunctionRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) → Prop where
  | headError (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : BindingFrame)
      (headResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch (functionType :: arguments ++ live)
        (protectedScope := protectedScope ++ expectedApplicationScope expression returnType) (typing := typing)
        operator functionType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      InterpretFunctionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression functionType
        returnType bindings headResult
  | tailError (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : BindingFrame)
      (headResult tailResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch (functionType :: arguments ++ live)
        (protectedScope := protectedScope ++ expectedApplicationScope expression returnType) (typing := typing)
        operator functionType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretArgsRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        arguments argumentTypes
        headResult.2 tailResult →
      (∀ values, tailResult.1 ≠ argumentPacket values) →
      InterpretFunctionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression functionType
        returnType bindings tailResult
  | success (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : BindingFrame)
      (headResult tailResult : FrameResult) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch (functionType :: arguments ++ live)
        (protectedScope := protectedScope ++ expectedApplicationScope expression returnType) (typing := typing)
        operator functionType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretArgsRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        arguments argumentTypes
        headResult.2 tailResult →
      (∃ values, tailResult.1 = argumentPacket values) →
      InterpretFunctionRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        expression functionType
        returnType bindings
        (.expression (headResult.1 :: argumentValues tailResult.1), tailResult.2)

/-- Evaluate argument lists left to right. -/
inductive InterpretArgsRel :
    Space → GroundedDispatch → List Atom →
    List Atom → List Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) → Prop where
  | nil (bindings : BindingFrame) :
      InterpretArgsRel space dispatch live (protectedScope := protectedScope) (typing := typing) [] [] bindings
        (argumentPacket [], bindings)
  | headChangedError (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : BindingFrame) (headResult : FrameResult) :
      EvalAtomRawRel space dispatch (arguments ++ expectedTypes ++ live) (protectedScope := protectedScope) (typing := typing)
        argument expectedType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      headResult.1 ≠ argument →
      InterpretArgsRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings headResult
  | tailError (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : BindingFrame) (headResult tailResult : FrameResult) :
      EvalAtomRawRel space dispatch (arguments ++ expectedTypes ++ live) (protectedScope := protectedScope) (typing := typing)
        argument expectedType bindings
        headResult →
      (¬IsEmptyOrErrorRel headResult.1 ∨ headResult.1 = argument) →
      InterpretArgsRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        arguments expectedTypes
        headResult.2 tailResult →
      (∀ values, tailResult.1 ≠ argumentPacket values) →
      InterpretArgsRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings tailResult
  | success (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : BindingFrame) (headResult tailResult : FrameResult) :
      EvalAtomRawRel space dispatch (arguments ++ expectedTypes ++ live) (protectedScope := protectedScope) (typing := typing)
        argument expectedType bindings
        headResult →
      (¬IsEmptyOrErrorRel headResult.1 ∨ headResult.1 = argument) →
      InterpretArgsRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        arguments expectedTypes
        headResult.2 tailResult →
      (∃ values, tailResult.1 = argumentPacket values) →
      InterpretArgsRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes) bindings
        (argumentPacket (headResult.1 :: argumentValues tailResult.1), tailResult.2)

/-- Evaluate tuple elements left to right. -/
inductive InterpretTupleRel :
    Space → GroundedDispatch → List Atom →
    Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) → Prop where
  | nil (bindings : BindingFrame) :
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        Atom.unit bindings (Atom.unit, bindings)
  | singleton (atom : Atom) (bindings : BindingFrame) (result : FrameResult) :
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom Atom.undefinedType bindings result →
      ¬IsEmptyOrErrorRel result.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression [atom]) bindings (.expression [result.1], result.2)
  | singletonError (atom : Atom) (bindings : BindingFrame) (result : FrameResult) :
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom Atom.undefinedType bindings result →
      IsEmptyOrErrorRel result.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression [atom]) bindings result
  | headError (head : Atom) (tail : List Atom) (bindings : BindingFrame)
      (headResult : FrameResult) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch (.expression tail :: live) (protectedScope := protectedScope) (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression (head :: tail))
        bindings headResult
  | tailError (head : Atom) (tail : List Atom) (bindings : BindingFrame)
      (headResult tailResult : FrameResult) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch (.expression tail :: live) (protectedScope := protectedScope) (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        (.expression tail)
        headResult.2 tailResult →
      IsEmptyOrErrorRel tailResult.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression (head :: tail))
        bindings tailResult
  | success (head : Atom) (tail : List Atom) (bindings : BindingFrame)
      (headResult tailResult : FrameResult) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch (.expression tail :: live) (protectedScope := protectedScope) (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch (headResult.1 :: live) (protectedScope := protectedScope) (typing := typing)
        (.expression tail)
        headResult.2 tailResult →
      ¬IsEmptyOrErrorRel tailResult.1 →
      InterpretTupleRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (.expression (head :: tail))
        bindings
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression atoms => atoms | atom => [atom]), tailResult.2)

/-- Ordinary call completion interprets the raw invocation protocol before
resuming typed evaluation. `original` is the invocation assembled after
argument evaluation. It is restored on `NotReducible`; stopped values retain
both their syntax and reached bindings. Explicit producer-completed values
use `CompletedNativeReturnRel` instead. -/
inductive CallReturnRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) → Prop where
  | notReducible (original expectedType : Atom) (bindings : BindingFrame) :
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        original expectedType Atom.notReducible bindings (original, bindings)
  | stopped (original expectedType value : Atom) (bindings : BindingFrame) :
      IsEmptyOrErrorRel value →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        original expectedType value bindings (value, bindings)
  | evaluate (original expectedType value : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      value ≠ Atom.notReducible →
      ¬IsEmptyOrErrorRel value →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        value expectedType bindings result →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        original expectedType value bindings result

/-- Perform one MeTTa call step, completing raw host or equation results
through the ordinary return protocol before recursive typed evaluation.
Invocation completion saves the assembled call as the diagnostic origin. -/
inductive CallRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) → Prop where
  | errorPassthrough (atom expectedType : Atom) (bindings : BindingFrame) :
      IsErrorRel atom →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (atom, bindings)
  | embedded (atom expectedType : Atom) (bindings : BindingFrame)
      (raw result : FrameResult) :
      ¬IsErrorRel atom →
      ¬Minimal.HostCall dispatch atom →
      Minimal.embeddedInstruction atom = true →
      Minimal.CoreInvocationRel space dispatch (expectedType :: live) (protectedScope := protectedScope) (typing := typing)
        atom bindings raw →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType raw.1 raw.2 result →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings result
  | groundedSuccess (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame)
      (nativeResults : ResultSet) (nativeResult : ResultPair) (finalResult : FrameResult)
      (merged : BindingFrame) (emitted : Atom) (completed : FrameResult) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .emitted →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok nativeResults) →
      nativeResult ∈ nativeResults →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      NativeEmissionRel dispatch operator arguments merged nativeResult.1 emitted →
      Minimal.CoreInvocationResultRel space dispatch (expectedType :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some atom)
        emitted merged completed →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType completed.1 completed.2 finalResult →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings finalResult
  | groundedCompletedSuccess (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame)
      (nativeResults : ResultSet) (nativeResult : ResultPair) (finalResult : FrameResult)
      (merged : BindingFrame) (emitted : Atom) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .completed →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok nativeResults) →
      nativeResult ∈ nativeResults →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      NativeEmissionRel dispatch operator arguments merged nativeResult.1 emitted →
      CompletedNativeReturnRel space typing emitted expectedType merged finalResult
        (protectedScope := invocationTypeScope protectedScope live atom expectedType merged) →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings finalResult
  | groundedRuntimeError (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) (message : String) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.runtimeError message) →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (Atom.error atom (.symbol message), bindings)
  | groundedNoReduce (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments .noReduce →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings (atom, bindings)
  | groundedIncorrectArgument (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments .incorrectArgument →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings (atom, bindings)
  | groundedEmpty (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok []) →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (Atom.empty, bindings)
  | equation (atom expectedType emitted materialized : Atom) (bindings merged : BindingFrame)
      (finalResult completed : FrameResult) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryCandidateRel space (expectedType :: live) atom bindings emitted merged →
      BindingFrame.Update .renew bindings merged →
      BindingFrame.Materialization merged emitted materialized →
      Minimal.CoreInvocationResultRel space dispatch (expectedType :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some atom)
        materialized merged completed →
      CallReturnRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType completed.1 completed.2 finalResult →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings finalResult
  | noEquation (atom expectedType : Atom) (bindings : BindingFrame) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryNoMatchRel space (expectedType :: live) atom bindings →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        atom expectedType bindings (atom, bindings)
  | allEquationsFiltered (atom expectedType : Atom) (bindings : BindingFrame) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryAllFilteredRel space (expectedType :: live) atom bindings →
      CallRel space dispatch live (protectedScope := protectedScope) (typing := typing) atom expectedType bindings
        (atom, bindings)


/-- One state-free minimal-instruction step.  The context space is read-only;
the state-writing extension is specified separately by `Machines.OrderedProtocol.Completion`.

`live` is the protected equation-query scope threaded by `EvalRel`, not
the equation table. This minimal profile retains the full syntax of entered
chain/function frames in that scope. `caller` names the nearest saved frame
for observable diagnostics; it stays raw when a terminal is materialized.
Backends with placeholder frame syntax or different scope retention need
their own representation adapter. Its `eval` operand invokes one raw
native/equation operation. Full typed interpretation is explicit in the
separate `metta` instruction. -/
inductive Minimal.CoreStepRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) →
      (caller : Option Atom := none) → Prop where
  | eval (space : Space) (atom materialized : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      BindingFrame.Materialization bindings atom materialized →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        materialized bindings result →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "eval", atom]) bindings result
  | evalc (space context : Space) (atom materialized : Atom) (bindings : BindingFrame)
      (result : FrameResult) (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      BindingFrame.Materialization bindings atom materialized →
      Minimal.CoreInvocationRel context dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        materialized bindings result →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "evalc", atom,
          .grounded (services.contextPayload context)]) bindings result
  | chain (space : Space) (atom : Atom) (name : String) (template : Atom)
      (bindings : BindingFrame) (result : FrameResult) (materialized : Atom) :
      Minimal.CoreRunRel space dispatch
        (.expression [.symbol "chain", atom, .var name, template] :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some (.expression [.symbol "chain", atom, .var name, template]))
        atom bindings result →
      BindingFrame.Materialization result.2 result.1 materialized →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "chain", atom, .var name, template]) bindings
        (substituteName name materialized template, result.2)
  | unifySuccess (space : Space) (target pattern thenBranch elseBranch result : Atom)
      (bindings output : BindingFrame) :
      UnifyCandidateRel target pattern bindings output →
      BindingFrame.Update .renew bindings output →
      BindingFrame.Materialization output thenBranch result →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        bindings (result, output)
  | unifyNoMatch (space : Space) (target pattern thenBranch elseBranch : Atom)
      (bindings : BindingFrame) :
      UnifyNoMatchRel target pattern bindings →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        bindings (elseBranch, bindings)
  | unifyBadArity (space : Space) (tail : List Atom)
      (bindings : BindingFrame) :
      tail.length ≠ 4 →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (.symbol "unify" :: tail)) bindings
        (mkErrorMessage (.expression (.symbol "unify" :: tail))
          (dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail))), bindings)
  | consAtom (space : Space) (head : Atom) (tail : List Atom)
      (bindings : BindingFrame) :
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "cons-atom", head, .expression tail]) bindings
        (.expression (head :: tail), bindings)
  | deconsAtom (space : Space) (head : Atom) (tail : List Atom)
      (bindings : BindingFrame) :
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "decons-atom", .expression (head :: tail)])
        bindings (.expression [head, .expression tail], bindings)
  | collapseBind (space : Space) (atom : Atom) (bindings : BindingFrame)
      (results : ResultSet) (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      BindingFrame.Historical bindings →
      enumeration.minimalResults space atom bindings results →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "collapse-bind", atom]) bindings
        (encodeResults services results, bindings)
  | superposeBind (space : Space) (results : ResultSet)
      (stored : ResultPair) (bindings merged : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      BindingFrame.Historical bindings →
      stored ∈ results →
      MergeRel equalityGroundedSemantic stored.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "superpose-bind", encodeResults services results])
        bindings (stored.1, merged)
  | functionReturn (space : Space) (body returned : Atom)
      (bindings output : BindingFrame) :
      (∃ atoms, body = .expression atoms) →
      Minimal.CoreFunctionBodyRel space dispatch
        (.expression [.symbol "function", body] :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some (.expression [.symbol "function", body]))
        body bindings (.expression [.symbol "return", returned], output) →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "function", body]) bindings (returned, output)
  | functionNoReturn (space : Space) (body result : Atom)
      (bindings output : BindingFrame) :
      (∃ atoms, body = .expression atoms) →
      Minimal.CoreFunctionBodyRel space dispatch
        (.expression [.symbol "function", body] :: live) (protectedScope := protectedScope) (typing := typing)
        (caller := some (.expression [.symbol "function", body]))
        body bindings (result, output) →
      (∀ returned, result ≠ .expression [.symbol "return", returned]) →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "function", body]) bindings
        (functionTerminalResult caller result, output)
  | metta (space context : Space) (atom expectedType : Atom)
      (bindings : BindingFrame) (result : FrameResult)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      EvalAtomRawRel context dispatch live atom expectedType bindings result
        (protectedScope := protectedScope) (typing := typing) →
      ¬IsErrorRel result.1 →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "metta", atom, expectedType,
          .grounded (services.contextPayload context)]) bindings result
  | mettaAtom (space context : Space) (atom : Atom) (bindings : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "metta", atom, Atom.atomType,
          .grounded (services.contextPayload context)]) bindings (atom, bindings)
  | mettaError (space context : Space) (atom expectedType : Atom) (bindings : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      IsErrorRel atom →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "metta", atom, expectedType,
          .grounded (services.contextPayload context)]) bindings (atom, bindings)
  | contextSpace (space : Space) (bindings : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "context-space"]) bindings
        (.grounded (services.contextPayload space), bindings)
  | callNative (space : Space) (name function arguments : Atom)
      (bindings : BindingFrame) (result : ResultPair) (merged : BindingFrame)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      services.nativeCall name function arguments bindings result →
      MergeRel equalityGroundedSemantic result.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "call-native", name, function, arguments])
        bindings (result.1, merged)

/-- Raw native/equation invocation: bindings are merged, but the emitted
ordinary atom is not recursively interpreted. An embedded operand is executed
by the minimal machine; an emitted `function` block has its own return frame. -/
inductive Minimal.CoreInvocationRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) →
      (caller : Option Atom := none) → Prop where
  | embedded (space : Space) (atom : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = true →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result
  | grounded (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings merged : BindingFrame) (results : ResultSet)
      (nativeResult : ResultPair) (result : FrameResult) (emitted : Atom) :
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .emitted →
      dispatch.outcome operator arguments (.ok results) →
      nativeResult ∈ results →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      (∃ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation merged) →
      NativeEmissionRel dispatch operator arguments merged nativeResult.1 emitted →
      Minimal.CoreInvocationResultRel space dispatch live (protectedScope := protectedScope) (typing := typing)
        (caller := some (.expression (operator :: arguments)))
        emitted merged result →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings result
  | completedGrounded (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings merged : BindingFrame) (results : ResultSet)
      (nativeResult : ResultPair) (emitted : Atom) :
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .completed →
      dispatch.outcome operator arguments (.ok results) →
      nativeResult ∈ results →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      BindingFrame.Update .renew bindings merged →
      (∃ valuation, Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation merged) →
      NativeEmissionRel dispatch operator arguments merged nativeResult.1 emitted →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings (emitted, merged)
  | groundedEmpty (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : BindingFrame) :
      dispatch.executable operator →
      dispatch.outcome operator arguments (.ok []) →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings (Atom.empty, bindings)
  | groundedError (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : BindingFrame) (message : String) :
      dispatch.executable operator →
      dispatch.outcome operator arguments (.runtimeError message) →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings
        (Atom.error (.expression (operator :: arguments)) (.symbol message), bindings)
  | groundedNoReduce (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : BindingFrame) :
      dispatch.executable operator →
      dispatch.outcome operator arguments .noReduce →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings
        (Atom.notReducible, bindings)
  | groundedIncorrectArgument (space : Space) (operator : Atom)
      (arguments : List Atom) (bindings : BindingFrame) :
      dispatch.executable operator →
      dispatch.outcome operator arguments .incorrectArgument →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression (operator :: arguments)) bindings
        (Atom.notReducible, bindings)
  | equation (space : Space) (atom emitted materialized : Atom)
      (bindings merged : BindingFrame) (result : FrameResult) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryCandidateRel space live atom bindings emitted merged →
      BindingFrame.Update .renew bindings merged →
      BindingFrame.Materialization merged emitted materialized →
      Minimal.CoreInvocationResultRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := some atom)
        materialized merged result →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result
  | noEquation (space : Space) (atom : Atom) (bindings : BindingFrame) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryNoMatchRel space live atom bindings →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (Atom.notReducible, bindings)
  | allEquationsFiltered (space : Space) (atom : Atom) (bindings : BindingFrame) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryAllFilteredRel space live atom bindings →
      Minimal.CoreInvocationRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (Atom.notReducible, bindings)

/-- Completing a raw invocation interprets only an authored `function`
block. Other emitted expressions, including callable-looking data, remain
raw. The invocation rules supply their actual call as the nearest saved
caller; embedded instructions keep their surrounding continuation. This is
independent of the ordinary typed result continuation. -/
inductive Minimal.CoreInvocationResultRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) →
      (caller : Option Atom := none) → Prop where
  | raw (space : Space) (atom : Atom) (bindings : BindingFrame) :
      ¬IsFunction atom →
      Minimal.CoreInvocationResultRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (atom, bindings)
  | function (space : Space) (body : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "function", body]) bindings result →
      Minimal.CoreInvocationResultRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        (.expression [.symbol "function", body]) bindings result

/-- Completed raw minimal execution. `chain` schedules the substituted
template; other instruction outputs are returned raw. The reference minimal
machine carries Empty and NotReducible through chain as ordinary sentinel
atoms; final observation, not this continuation, removes Empty. -/
inductive Minimal.CoreRunRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) →
      (caller : Option Atom := none) → Prop where
  | data (space : Space) (atom : Atom) (bindings : BindingFrame) :
      embeddedInstruction atom = false →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (atom, bindings)
  | instruction (space : Space) (atom : Atom) (bindings : BindingFrame)
      (result : FrameResult) :
      embeddedInstruction atom = true →
      ¬IsChain atom →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result
  | chain (space : Space) (atom : Atom) (bindings : BindingFrame)
      (selected result : FrameResult) :
      IsChain atom →
      Minimal.CoreStepRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings selected →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        selected.1 selected.2 result →
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result

/-- A function body resumes embedded instructions until a noninstruction
terminal is reached. A terminal without `return` produces NoReturn, including
an internal Empty sentinel reached by a valid expression-shaped body. -/
inductive Minimal.CoreFunctionBodyRel :
    Space → GroundedDispatch → List Atom → Atom → BindingFrame → FrameResult →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := storageTypeService) →
      (caller : Option Atom := none) → Prop where
  | terminal (space : Space) (atom : Atom) (bindings : BindingFrame)
      (raw : FrameResult) (materialized : Atom) :
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings raw →
      BindingFrame.Materialization raw.2 raw.1 materialized →
      embeddedInstruction materialized = false →
      Minimal.CoreFunctionBodyRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings (materialized, raw.2)
  | resume (space : Space) (atom : Atom) (bindings : BindingFrame)
      (raw : FrameResult) (materialized : Atom) (result : FrameResult) :
      Minimal.CoreRunRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings raw →
      BindingFrame.Materialization raw.2 raw.1 materialized →
      embeddedInstruction materialized = true →
      Minimal.CoreFunctionBodyRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        materialized raw.2 result →
      Minimal.CoreFunctionBodyRel space dispatch live (protectedScope := protectedScope) (typing := typing) (caller := caller)
        atom bindings result

end


/-- A raw refusal restores exactly the assembled invocation and the binding
frame reached by that invocation; the protocol atom cannot escape this gate. -/
theorem CallReturnRel.notReducible_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {protectedScope : List String} {original expectedType : Atom}
    {bindings : BindingFrame} {result : FrameResult} :
    CallReturnRel space dispatch live original expectedType Atom.notReducible
      bindings result (protectedScope := protectedScope) (typing := typing) ↔ result = (original, bindings) := by
  constructor
  · intro returned
    cases returned <;>
      simp_all [IsEmptyOrErrorRel, IsErrorRel, Atom.notReducible, Atom.empty]
  · rintro rfl
    exact .notReducible _ _ _

/-- Empty and error replies stop at ordinary call completion, independently
of the expected type. -/
theorem CallReturnRel.stopped_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {protectedScope : List String} {original expectedType value : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (stopped : IsEmptyOrErrorRel value) :
    CallReturnRel space dispatch live original expectedType value bindings result
      (protectedScope := protectedScope) (typing := typing) ↔ result = (value, bindings) := by
  constructor
  · intro returned
    cases returned <;>
      simp_all [IsEmptyOrErrorRel, IsErrorRel, Atom.notReducible, Atom.empty]
  · rintro rfl
    exact .stopped _ _ _ _ stopped

/-- Every non-protocol, non-stopped reply resumes the existing raw typed
judgment without changing its scope, demand, or reached frame. -/
theorem CallReturnRel.evaluate_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {typing : EvalTypeService} {protectedScope : List String} {original expectedType value : Atom}
    {bindings : BindingFrame} {result : FrameResult}
    (notRefusal : value ≠ Atom.notReducible)
    (notStopped : ¬IsEmptyOrErrorRel value) :
    CallReturnRel space dispatch live original expectedType value bindings result
      (protectedScope := protectedScope) (typing := typing) ↔
      EvalAtomRawRel space dispatch live value expectedType bindings result
        (protectedScope := protectedScope) (typing := typing) := by
  constructor
  · intro returned
    cases returned <;> simp_all
  · exact .evaluate _ _ _ _ _ notRefusal notStopped

/-- A completed empty source query restores an ordinary invocation exactly.
It covers both genuine mismatch and matches rejected by caller constraints;
the source frontier, rather than a runtime empty-list test, rules out hidden
successful equations. The reached frame is retained. -/
theorem CallRel.completed_empty_query_iff
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {result : FrameResult}
    {typing : EvalTypeService} {protectedScope : List String}
    (ordinary : NonGroundedCallRel dispatch atom) (clean : ¬IsErrorRel atom)
    (completed : EquationFrontierRel space (expected::live) atom bindings.bindings []) :
    CallRel space dispatch live atom expected bindings result
      (protectedScope := protectedScope) (typing := typing) ↔ result = (atom,bindings) := by
  have absent := completed.empty_iff_no_candidate.mp rfl
  constructor
  · intro derived
    cases derived <;> first
      | rfl
      | (exfalso; apply ordinary.1; exact ⟨_,_,by assumption,by assumption⟩)
      | (exfalso; exact absent _ _ (by assumption))
      | simp_all [NonGroundedCallRel]
  · rintro rfl
    by_cases matching : ∃ pattern body matched,
        EquationRuleMatchRel space (expected::live) atom bindings.bindings pattern body matched
    · exact .allEquationsFiltered _ _ _ clean ordinary ⟨matching,absent⟩
    · exact .noEquation _ _ _ clean ordinary (by
        intro pattern body matched selected
        exact matching ⟨pattern,body,matched,selected⟩)

/-! ## Public success-priority boundary -/

/-- Completed mismatch preserves arbitrary caller constraints and either
retained readout mode, under every type service and surrounding live scope. -/
theorem completed_mismatch_retains_frame
    (dispatch : GroundedDispatch) (live : List Atom) (expected : Atom)
    (bindings : BindingFrame) (result : FrameResult)
    (typing : EvalTypeService := storageTypeService) (protectedScope : List String := []) :
    CallRel (Space.ofList [FrontierControls.missedRule]) dispatch live (.symbol "a") expected
      bindings result (typing := typing) (protectedScope := protectedScope) ↔
      result = (.symbol "a",bindings) := by
  apply CallRel.completed_empty_query_iff
  · simp [NonGroundedCallRel,Minimal.HostCall,Minimal.embeddedInstruction]
  · simp [IsErrorRel]
  · exact FrontierControls.complete_miss _ _

/-- Outer publication over raw possibilities: successes are admitted directly;
an error requires absence of raw successes. Recursive premises remain raw, so
this is not the completed nested HE judgment. -/
def EvalRel
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : BindingFrame) (result : FrameResult)
    (typing : EvalTypeService := storageTypeService)
    (protectedScope : List String := []) : Prop :=
  EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
      atom expectedType bindings result ∧
    (IsErrorRel result.1 →
      ∀ candidate,
        EvalAtomRawRel space dispatch live (protectedScope := protectedScope) (typing := typing)
          atom expectedType bindings candidate →
          IsErrorRel candidate.1)

/-- An all-error observation that omits one raw result cannot cover this
outer-only publication judgment. If any raw success exists it is itself
published and contradicts the observation; otherwise the omitted error is
published. This exposes a misplaced nested publication boundary without
assuming that the other raw derivations have been exhaustively classified. -/
theorem EvalRel.not_covered_by_errors
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom expectedType : Atom} {bindings : BindingFrame} {typing : EvalTypeService}
    {protectedScope : List String} {result : FrameResult} {observed : List Atom}
    (raw : EvalAtomRawRel space dispatch live atom expectedType bindings result
      (protectedScope := protectedScope) (typing := typing))
    (errors : ∀ value ∈ observed, IsErrorRel value)
    (omitted : result.1 ∉ observed) :
    ¬(∀ candidate, EvalRel space dispatch live atom expectedType bindings candidate
      (protectedScope := protectedScope) (typing := typing) → candidate.1 ∈ observed) := by
  intro covers
  have allErrors : ∀ candidate,
      EvalAtomRawRel space dispatch live atom expectedType bindings candidate
        (protectedScope := protectedScope) (typing := typing) → IsErrorRel candidate.1 := by
    intro candidate derived
    by_contra notError
    exact notError (errors candidate.1 (covers candidate
      ⟨derived, fun error => False.elim (notError error)⟩))
  exact omitted (covers result ⟨raw, fun _ => allErrors⟩)

/-! ## Boundary examples -/

private def noHostDispatch : GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

/-- Positive error-shape canary: the published ellipsis permits an empty
tail after the `Error` head. -/
example : IsErrorRel (.expression [.symbol "Error"]) :=
  ⟨[], rfl⟩

/-- Negative error-shape canary: the bare `Error` symbol is data, not an
error expression. -/
example : ¬IsErrorRel (.symbol "Error") := by
  rintro ⟨tail, h⟩
  cases h

/-- Positive: `Empty` passes through unchanged. -/
example : EvalRel Space.empty noHostDispatch []
    Atom.empty Atom.undefinedType Bindings.empty
    (Atom.empty, Bindings.empty) := by
  constructor
  · exact EvalAtomRawRel.emptyOrError _ _ _ (Or.inl rfl)
  · intro herror
    exact (by rcases herror with ⟨tail, h⟩; cases h)

private theorem variablePassRaw (name : String) (expectedType : Atom)
    (protectedScope : List String := []) {live : List Atom} :
    EvalAtomRawRel Space.empty noHostDispatch live
    (.var name) expectedType Bindings.empty
    (.var name, Bindings.empty) protectedScope := by
  apply EvalAtomRawRel.typePass (.var name) expectedType
      Atom.variableType Bindings.empty
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.variable name
  · exact Or.inr (Or.inr rfl)

/-- Positive tuple recursion: a singleton tuple retains its wrapper. -/
example : InterpretTupleRel Space.empty noHostDispatch []
    (.expression [.var "x"]) Bindings.empty
    (.expression [.var "x"], Bindings.empty) := by
  apply InterpretTupleRel.singleton (.var "x") Bindings.empty
    (.var "x", Bindings.empty) (variablePassRaw "x" Atom.undefinedType)
  simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]

private def unaryWantedType : Atom :=
  .expression [.symbol "->", .symbol "Wanted", .symbol "Wanted"]

private theorem variableArgumentRaw {live : List Atom} :
    InterpretArgsRel Space.empty noHostDispatch live
      [.var "x"] [.symbol "Wanted"] Bindings.empty
      (argumentPacket [.var "x"], Bindings.empty) := by
  apply InterpretArgsRel.success
      (.var "x") [] (.symbol "Wanted") [] Bindings.empty
      (.var "x", Bindings.empty) (argumentPacket [], Bindings.empty)
  · exact variablePassRaw "x" (.symbol "Wanted")
  · exact Or.inr rfl
  · exact InterpretArgsRel.nil Bindings.empty
  · exact ⟨[], rfl⟩

/-- Positive function recursion: variables pass the declared unary function
and argument types, producing the interpreted call expression. -/
example : InterpretFunctionRel Space.empty noHostDispatch []
    (.expression [.var "f", .var "x"])
    unaryWantedType (.symbol "Wanted") Bindings.empty
    (.expression [.var "f", .var "x"], Bindings.empty) := by
  apply InterpretFunctionRel.success
      (.expression [.var "f", .var "x"])
      unaryWantedType (.symbol "Wanted") (.var "f")
      (.symbol "Wanted")
      [.var "x"] [.symbol "Wanted"] Bindings.empty
      (.var "f", Bindings.empty)
      (argumentPacket [.var "x"], Bindings.empty)
  · rfl
  · rfl
  · exact variablePassRaw "f" unaryWantedType
      (expectedApplicationScope
        (.expression [.var "f", .var "x"]) (.symbol "Wanted"))
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact variableArgumentRaw
  · exact ⟨[.var "x"], rfl⟩

/-- Positive type-cast path: an unannotated symbol has `%Undefined%`, which
matches any expected type. -/
example : EvalAtomRawRel Space.empty noHostDispatch []
    (.symbol "x") (.symbol "Wanted") Bindings.empty
    (.symbol "x", Bindings.empty) := by
  apply EvalAtomRawRel.cast
      (.symbol "x") (.symbol "Wanted") Atom.symbolType Bindings.empty
      (.symbol "x", Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.symbol "x"
  · simp [Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨"x", rfl⟩
  · apply TypeCastRel.success
        (types := [Atom.undefinedType]) (earlierTypes := [])
        (laterTypes := []) (actualType := Atom.undefinedType)
    · exact StorageTypesRel.symbolUndefined AnnotationTypesRel.nil
    · rfl
    · simp
    · exact TypeMatchRel.undefinedRight (.symbol "Wanted") Bindings.empty
  · exact .historical _ _

/-- A raw minimal unify step selects the else atom after a symbol mismatch. -/
example : Minimal.CoreStepRel Space.empty noHostDispatch []
    (.expression [.symbol "unify", .symbol "a", .symbol "b",
      .symbol "then", .symbol "else"])
    Bindings.empty (.symbol "else", Bindings.empty) := by
  apply Minimal.CoreStepRel.unifyNoMatch
  intro output hcandidate
  obtain ⟨matched, hmatch, _⟩ := hcandidate
  exact symbol_mismatch_not_match (by decide) matched hmatch

/-- The switch scanner returns Empty on an empty branch list. Ordinary
invocation of the authored switch library is a separate equation boundary. -/
example : SwitchStep (.symbol "a") [] Bindings.empty Atom.empty Bindings.empty :=
  SwitchStep.noMatch SwitchRawRel.nil

/-- Negative equation-query branch: an empty space returns the atom unchanged. -/
example : CallRel Space.empty noHostDispatch []
    (.symbol "unreduced") Atom.undefinedType Bindings.empty
    (.symbol "unreduced", Bindings.empty) := by
  apply CallRel.noEquation
  · rintro ⟨tail, hError⟩
    cases hError
  · simp [NonGroundedCallRel, Minimal.HostCall, Minimal.embeddedInstruction]
  · intro freshPattern freshRhs matched hmatch
    obtain ⟨rawLhs, rawRhs, hmem, _⟩ := hmatch
    simp [Space.empty] at hmem

private def noReduceDispatch : GroundedDispatch where
  executable := fun operator => operator = .symbol "native"
  outcome := fun operator _ result =>
    operator = .symbol "native" ∧ result = .noReduce

/-- Positive grounded boundary: a host `NoReduce` outcome preserves the call
unchanged without importing an executable dispatcher. -/
example : CallRel Space.empty noReduceDispatch []
    (.expression [.symbol "native", .symbol "argument"])
    Atom.undefinedType Bindings.empty
    (.expression [.symbol "native", .symbol "argument"], Bindings.empty) := by
  apply CallRel.groundedNoReduce
      (.expression [.symbol "native", .symbol "argument"])
      Atom.undefinedType (.symbol "native") [.symbol "argument"]
      Bindings.empty rfl
  · rfl
  · simp [IsErrorRel]
  · exact ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Eval

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement

/-! Generic dispatch classifiers used by the source transport below. -/

/-- Renaming variable leaves preserves and reflects every literal symbolic
expression head, without a restriction on its arity. -/
theorem symbolHead_renameTypeVars_iff
    (rename : String → String) (source : Atom) (head : String) (tail : List Atom) :
    renameTypeVars rename source = .expression (.symbol head :: tail) ↔
      ∃ sourceTail, source = .expression (.symbol head :: sourceTail) ∧
        tail = sourceTail.map (renameTypeVars rename) := by
  constructor
  · intro equation
    cases source with
    | symbol | var | grounded => simp [renameTypeVars] at equation
    | expression atoms =>
        simp only [renameTypeVars, Atom.expression.injEq] at equation
        obtain ⟨sourceHead, sourceTail, sourceShape, headEquation, tailEquation⟩ :=
          List.map_eq_cons_iff.mp equation
        have headShape : sourceHead = .symbol head := by
          cases sourceHead <;> simp [renameTypeVars] at headEquation ⊢
          exact headEquation
        subst sourceHead
        exact ⟨sourceTail, congrArg Atom.expression sourceShape, tailEquation.symm⟩
  · rintro ⟨sourceTail, rfl, rfl⟩
    simp [renameTypeVars]

/-- Exact unary function wrappers retain the renamed body, rather than just
the truth of a classification predicate. -/
theorem functionBody_renameTypeVars_iff
    (rename : String → String) (source body : Atom) :
    renameTypeVars rename source = .expression [.symbol "function", body] ↔
      ∃ sourceBody, source = .expression [.symbol "function", sourceBody] ∧
        body = renameTypeVars rename sourceBody := by
  constructor
  · intro equation
    obtain ⟨sourceTail, sourceShape, tailEquation⟩ :=
      (symbolHead_renameTypeVars_iff rename source "function" [body]).mp equation
    obtain ⟨sourceBody, tailShape, bodyEquation⟩ :=
      List.map_eq_singleton_iff.mp tailEquation.symm
    exact ⟨sourceBody, by simpa [tailShape] using sourceShape, bodyEquation.symm⟩
  · rintro ⟨sourceBody, rfl, rfl⟩
    simp [renameTypeVars]

/-- The source's exact-arity function classifier is invariant under variable
renaming. This does not identify it with a function-head test at any arity. -/
theorem isFunction_renameTypeVars_iff (rename : String → String) (source : Atom) :
    IsFunction (renameTypeVars rename source) ↔ IsFunction source := by
  constructor
  · rintro ⟨body, equation⟩
    obtain ⟨sourceBody, sourceShape, _⟩ :=
      (functionBody_renameTypeVars_iff rename source body).mp equation
    exact ⟨sourceBody, sourceShape⟩
  · rintro ⟨body, rfl⟩
    exact ⟨renameTypeVars rename body, by simp [renameTypeVars]⟩

/-- Literal symbolic-head classification, at any arity, is invariant under
variable renaming. -/
theorem symbolicHead_renameTypeVars_iff
    (rename : String → String) (source : Atom) (head : String) :
    (∃ tail, renameTypeVars rename source = .expression (.symbol head :: tail)) ↔
      ∃ tail, source = .expression (.symbol head :: tail) := by
  constructor
  · rintro ⟨tail, equation⟩
    obtain ⟨sourceTail, sourceShape, _⟩ :=
      (symbolHead_renameTypeVars_iff rename source head tail).mp equation
    exact ⟨sourceTail, sourceShape⟩
  · rintro ⟨tail, rfl⟩
    exact ⟨tail.map (renameTypeVars rename), by simp [renameTypeVars]⟩

/-- Minimal instruction dispatch depends on literal heads, never on the
spelling of variable leaves or on a binding model for those variables. -/
theorem embeddedInstruction_renameTypeVars (rename : String → String) (source : Atom) :
    embeddedInstruction (renameTypeVars rename source) = embeddedInstruction source := by
  cases source with
  | symbol | var | grounded => simp [renameTypeVars, embeddedInstruction]
  | expression atoms =>
      cases atoms with
      | nil => simp [renameTypeVars, embeddedInstruction]
      | cons head tail => cases head <;> simp [renameTypeVars, embeddedInstruction]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

/-! ## Renaming the complete source configuration

These laws simultaneously transport the equation table, live continuation,
binding record, typing service and grounded service. In particular, diagnostic
renderers are transported explicitly: the laws do not assert that an arbitrary
unchanged service or name-rendering policy is equivariant.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation Spec.Bindings.ScopeObservation

@[simp] theorem error_iff (permutation : Equiv.Perm String) (atom : Atom) :
    IsErrorRel (renameTypeVars permutation atom) ↔ IsErrorRel atom :=
  Minimal.symbolicHead_renameTypeVars_iff permutation atom "Error"

@[simp] theorem stopped_iff (permutation : Equiv.Perm String) (atom : Atom) :
    IsEmptyOrErrorRel (renameTypeVars permutation atom) ↔ IsEmptyOrErrorRel atom := by
  simp only [IsEmptyOrErrorRel, Atom.empty, atom_eq_symbol, error_iff]

@[simp] theorem atom_error (permutation : Equiv.Perm String) (subject message : Atom) :
    renameTypeVars permutation (Atom.error subject message) =
      Atom.error (renameTypeVars permutation subject) (renameTypeVars permutation message) := by
  simp [Atom.error]

@[simp] theorem packet (permutation : Equiv.Perm String) (atoms : List Atom) :
    renameTypeVars permutation (argumentPacket atoms) =
      argumentPacket (atoms.map (renameTypeVars permutation)) := by simp [argumentPacket]

theorem isPacket_iff (permutation : Equiv.Perm String) (atom : Atom) :
    (∃ atoms,renameTypeVars permutation atom=argumentPacket atoms) ↔
      ∃ atoms,atom=argumentPacket atoms := by
  constructor
  · rintro ⟨atoms,same⟩
    refine ⟨atoms.map (renameTypeVars permutation.symm),?_⟩
    simpa only [renameTypeVars_perm_inverse,packet] using congrArg (renameTypeVars permutation.symm) same
  · rintro ⟨atoms,rfl⟩
    exact ⟨_,packet permutation atoms⟩

@[simp] theorem metaType_iff (permutation : Equiv.Perm String) (atom type : Atom) :
    MetaTypeRel (renameTypeVars permutation atom) type ↔ MetaTypeRel atom type := by
  cases atom <;> simp only [atom_symbol, atom_var, atom_grounded, atom_expr] <;>
    constructor <;> intro h <;> cases h <;> constructor

theorem metaType_fixed {atom type : Atom} (h : MetaTypeRel atom type)
    (permutation : Equiv.Perm String) : renameTypeVars permutation type=type := by
  cases h <;> simp [Atom.symbolType,Atom.variableType,Atom.groundedType,Atom.expressionType]

theorem metaType (permutation : Equiv.Perm String) {atom type : Atom}
    (h : MetaTypeRel atom type) :
    MetaTypeRel (renameTypeVars permutation atom) (renameTypeVars permutation type) := by
  rw [metaType_fixed h permutation,metaType_iff]
  exact h

@[simp] theorem functionType_iff (permutation : Equiv.Perm String)
    (type : Atom) (arguments : List Atom) (returned : Atom) :
    FunctionTypeRel (renameTypeVars permutation type)
      (arguments.map (renameTypeVars permutation)) (renameTypeVars permutation returned) ↔
      FunctionTypeRel type arguments returned := by
  unfold FunctionTypeRel
  simpa only [renameTypeVars,List.map_cons,List.map_append,List.map_nil,List.cons_append] using
    (renameTypeVars_perm_injective permutation).eq_iff (a:=type)
      (b:=.expression (.symbol "->" :: arguments ++ [returned]))


private theorem filter_ne (permutation : Equiv.Perm String) (names : List String) (name : String) :
    (names.map permutation).filter (fun candidate=> !(candidate == permutation name)) =
      (names.filter (fun candidate=> !(candidate == name))).map permutation := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : first=name
    · subst first
      simp [ih]
    · have mapped : permutation first ≠ permutation name := fun equal=>same (permutation.injective equal)
      simp [same,mapped,ih]

theorem names_eraseDups (permutation : Equiv.Perm String) (names : List String) :
    (names.map permutation).eraseDups = names.eraseDups.map permutation := by
  cases names with
  | nil => rfl
  | cons first rest =>
    rw [List.map_cons,List.eraseDups_cons,List.eraseDups_cons,List.map_cons,filter_ne,
      names_eraseDups]
termination_by names.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

@[simp] theorem scope (permutation : Equiv.Perm String) (expression expected : Atom) :
    expectedApplicationScope (renameTypeVars permutation expression) (renameTypeVars permutation expected) =
      (expectedApplicationScope expression expected).map permutation := by
  simp only [expectedApplicationScope,typeVars_renameTypeVars,←List.map_append,names_eraseDups]

@[simp] theorem unpack (permutation : Equiv.Perm String) (atom : Atom) :
    unpackArguments (renameTypeVars permutation atom) =
      (unpackArguments atom).map (List.map (renameTypeVars permutation)) := by
  cases h : unpackArguments atom with
  | none =>
    cases found : unpackArguments (renameTypeVars permutation atom) with
    | none => rfl
    | some atoms =>
      obtain ⟨original,rfl⟩ := (isPacket_iff permutation atom).mp
        ⟨atoms,unpackArguments_iff.mp found⟩
      simp at h
  | some atoms =>
    have shape := unpackArguments_iff.mp h
    simp only [shape,packet,unpackArguments_packet,Option.map_some]

@[simp] theorem values (permutation : Equiv.Perm String) (atom : Atom) :
    argumentValues (renameTypeVars permutation atom) =
      (argumentValues atom).map (renameTypeVars permutation) := by
  unfold argumentValues
  rw [unpack]
  cases unpackArguments atom <;> rfl

@[simp] theorem substitute (permutation : Equiv.Perm String) (name : String) (value : Atom) (atom : Atom) :
    renameTypeVars permutation (Minimal.substituteName name value atom) =
      Minimal.substituteName (permutation name) (renameTypeVars permutation value)
        (renameTypeVars permutation atom) := by
  induction atom using Atom.rec
    (motive_2:=fun atoms=>
      (atoms.map (Minimal.substituteName name value)).map (renameTypeVars permutation) =
      (atoms.map (renameTypeVars permutation)).map
        (Minimal.substituteName (permutation name) (renameTypeVars permutation value))) with
  | symbol => simp [Minimal.substituteName]
  | var varName =>
    by_cases same : varName=name
    · subst varName
      simp [Minimal.substituteName]
    · have mapped : permutation varName≠permutation name := fun eq=>same (permutation.injective eq)
      simp [Minimal.substituteName,same,mapped]
  | grounded => simp [Minimal.substituteName]
  | expression atoms ih => simpa [Minimal.substituteName] using congrArg Atom.expression ih
  | nil => rfl
  | cons atom atoms first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

@[simp] theorem chain_iff (permutation : Equiv.Perm String) (atom : Atom) :
    Minimal.IsChain (renameTypeVars permutation atom) ↔ Minimal.IsChain atom :=
  Minimal.symbolicHead_renameTypeVars_iff permutation atom "chain"

@[simp] theorem function_iff (permutation : Equiv.Perm String) (atom : Atom) :
    Minimal.IsFunction (renameTypeVars permutation atom) ↔ Minimal.IsFunction atom :=
  Minimal.isFunction_renameTypeVars_iff permutation atom

@[simp] theorem embedded (permutation : Equiv.Perm String) (atom : Atom) :
    Minimal.embeddedInstruction (renameTypeVars permutation atom) = Minimal.embeddedInstruction atom :=
  Minimal.embeddedInstruction_renameTypeVars permutation atom

@[simp] theorem terminal (permutation : Equiv.Perm String) (caller : Option Atom) (atom : Atom) :
    renameTypeVars permutation (Minimal.functionTerminalResult caller atom) =
      Minimal.functionTerminalResult (caller.map (renameTypeVars permutation)) (renameTypeVars permutation atom) := by
  cases atom with
  | symbol => cases caller <;> simp [Minimal.functionTerminalResult]
  | var => cases caller <;> simp [Minimal.functionTerminalResult]
  | grounded => cases caller <;> simp [Minimal.functionTerminalResult]
  | expression atoms =>
    cases atoms with
    | nil => cases caller <;> simp [Minimal.functionTerminalResult]
    | cons head tail =>
      cases head with
      | symbol tag =>
        cases tail with
        | nil => cases caller <;> simp [Minimal.functionTerminalResult]
        | cons first rest =>
          cases rest with
          | nil => by_cases h : tag="return" <;> cases caller <;> simp [Minimal.functionTerminalResult,h]
          | cons => cases caller <;> simp [Minimal.functionTerminalResult]
      | var => cases caller <;> simp [Minimal.functionTerminalResult]
      | grounded => cases caller <;> simp [Minimal.functionTerminalResult]
      | expression => cases caller <;> simp [Minimal.functionTerminalResult]


@[simp] theorem atoms_equal (permutation : Equiv.Perm String) (left right : Atom) :
    renameTypeVars permutation left=renameTypeVars permutation right ↔ left=right :=
  (renameTypeVars_perm_injective permutation).eq_iff

@[simp] theorem pass_type (permutation : Equiv.Perm String) (expected intrinsic : Atom) :
    (renameTypeVars permutation expected=Atom.atomType ∨
      renameTypeVars permutation expected=renameTypeVars permutation intrinsic ∨
      renameTypeVars permutation intrinsic=Atom.variableType) ↔
      (expected=Atom.atomType ∨ expected=intrinsic ∨ intrinsic=Atom.variableType) := by
  simp only [Atom.atomType,Atom.variableType,atom_eq_symbol,atoms_equal]

theorem cast_shape (permutation : Equiv.Perm String) {atom : Atom}
    (shape : (∃ name,atom=.symbol name) ∨ (∃ value,atom=.grounded value) ∨ atom=Atom.unit) :
    (∃ name,renameTypeVars permutation atom=.symbol name) ∨
      (∃ value,renameTypeVars permutation atom=.grounded value) ∨
      renameTypeVars permutation atom=Atom.unit := by
  rcases shape with ⟨name,rfl⟩ | ⟨value,rfl⟩ | rfl
  · exact Or.inl ⟨name,by simp⟩
  · exact Or.inr (Or.inl ⟨value,by simp⟩)
  · exact Or.inr (Or.inr (by simp [Atom.unit]))

theorem nonempty_expression (permutation : Equiv.Perm String) {atom : Atom}
    (shape : ∃ head tail,atom=.expression (head::tail)) :
    ∃ head tail,renameTypeVars permutation atom=.expression (head::tail) := by
  obtain ⟨head,tail,rfl⟩ := shape
  exact ⟨renameTypeVars permutation head,tail.map (renameTypeVars permutation),by simp⟩

@[simp] theorem not_packet (permutation : Equiv.Perm String) (atom : Atom) :
    (∀ values,renameTypeVars permutation atom≠argumentPacket values) ↔
      ∀ values,atom≠argumentPacket values := by
  simpa only [not_exists] using not_congr (isPacket_iff permutation atom)

@[simp] theorem elements (permutation : Equiv.Perm String) (atom : Atom) :
    (match renameTypeVars permutation atom with | .expression atoms=>atoms | other=>[other]) =
      (match atom with | .expression atoms=>atoms | other=>[other]).map (renameTypeVars permutation) := by
  cases atom <;> simp

@[simp] theorem not_return (permutation : Equiv.Perm String) (atom : Atom) :
    (∀ value,renameTypeVars permutation atom≠.expression [.symbol "return",value]) ↔
      ∀ value,atom≠.expression [.symbol "return",value] := by
  constructor
  · intro missing value same
    apply missing (renameTypeVars permutation value)
    simp [same]
  · intro missing value same
    apply missing (renameTypeVars permutation.symm value)
    simpa using congrArg (renameTypeVars permutation.symm) same

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation

/-- One action on a full result preserves its syntax and complete binding rows. -/
def result (permutation : Equiv.Perm String) (source : ResultPair) : ResultPair :=
  (renameTypeVars permutation source.1,renameBindings permutation source.2)

def results (permutation : Equiv.Perm String) (source : ResultSet) : ResultSet :=
  source.map (result permutation)

@[simp] theorem result_inverse (permutation : Equiv.Perm String) (source : ResultPair) :
    result permutation.symm (result permutation source) = source := by
  cases source
  simp [result]

@[simp] theorem result_inverse_reverse (permutation : Equiv.Perm String) (source : ResultPair) :
    result permutation (result permutation.symm source) = source := result_inverse permutation.symm source

@[simp] theorem results_inverse (permutation : Equiv.Perm String) (source : ResultSet) :
    results permutation.symm (results permutation source) = source := by
  simp only [results,List.map_map,Function.comp_def,result_inverse]
  exact List.map_id source

@[simp] theorem results_inverse_reverse (permutation : Equiv.Perm String) (source : ResultSet) :
    results permutation (results permutation.symm source) = source := results_inverse permutation.symm source

/-- The same action carries the retained representation as well as its raw rows. -/
def frameResult (permutation : Equiv.Perm String) (source : FrameResult) : FrameResult :=
  (renameTypeVars permutation source.1, BindingFrame.rename permutation source.2)

@[simp] theorem frameResult_inverse (permutation : Equiv.Perm String) (source : FrameResult) :
    frameResult permutation.symm (frameResult permutation source) = source := by
  cases source
  simp [frameResult]

@[simp] theorem frameResult_inverse_reverse (permutation : Equiv.Perm String) (source : FrameResult) :
    frameResult permutation (frameResult permutation.symm source) = source :=
  frameResult_inverse permutation.symm source

@[simp] theorem frameResult_raw (permutation : Equiv.Perm String) (source : FrameResult) :
    BindingFrame.rawResult (frameResult permutation source) =
      result permutation (BindingFrame.rawResult source) := rfl

/-- Protocol cases and physical result multiplicity are retained. -/
def grounded (permutation : Equiv.Perm String) : GroundedResult → GroundedResult
  | .ok values => .ok (results permutation values)
  | .runtimeError message => .runtimeError message
  | .noReduce => .noReduce
  | .incorrectArgument => .incorrectArgument

@[simp] theorem grounded_inverse (permutation : Equiv.Perm String) (source : GroundedResult) :
    grounded permutation.symm (grounded permutation source) = source := by
  cases source <;> simp [grounded]

/-- The selected argument and return policy is transported as one object. -/
def policy (permutation : Equiv.Perm String) (source : SelectedTypePolicy) : SelectedTypePolicy where
  functionType := renameTypeVars permutation source.functionType
  argumentTypes := source.argumentTypes.map (renameTypeVars permutation)
  returnType := renameTypeVars permutation source.returnType
  isFunction := (functionType_iff permutation _ _ _).mpr source.isFunction

@[simp] theorem policy_inverse (permutation : Equiv.Perm String) (source : SelectedTypePolicy) :
    policy permutation.symm (policy permutation source) = source := by
  cases source
  simp [policy,Function.comp_def]

/-- A failed scan keeps each diagnostic occurrence and the tuple decision. -/
def scanOutcome (permutation : Equiv.Perm String) : FunctionCandidateScanOutcome → FunctionCandidateScanOutcome
  | .success selected bindings => .success (policy permutation selected) (renameBindings permutation bindings)
  | .exhausted errors eligible => .exhausted (errors.map (renameTypeVars permutation)) eligible

@[simp] theorem scanOutcome_inverse (permutation : Equiv.Perm String) (source : FunctionCandidateScanOutcome) :
    scanOutcome permutation.symm (scanOutcome permutation source) = source := by
  cases source <;> simp [scanOutcome,Function.comp_def]

/-- Transport opaque encoders by inverse reindexing of their semantic input.
The grounded payload itself is unchanged by syntactic variable renaming. -/
def services (permutation : Equiv.Perm String) (source : Minimal.Services) : Minimal.Services where
  bindingPayload := fun bindings=>source.bindingPayload (renameBindings permutation.symm bindings)
  contextPayload := fun context=>source.contextPayload (space permutation.symm context)
  nativeCall := fun name function arguments bindings returned=>
    source.nativeCall (renameTypeVars permutation.symm name) (renameTypeVars permutation.symm function)
      (renameTypeVars permutation.symm arguments) (renameBindings permutation.symm bindings)
      (result permutation.symm returned)

def enumeration (permutation : Equiv.Perm String) (source : Minimal.Enumeration) : Minimal.Enumeration where
  results := fun context atom expected bindings returned=>
    source.results (space permutation.symm context) (renameTypeVars permutation.symm atom)
      (renameTypeVars permutation.symm expected) (renameBindings permutation.symm bindings)
      (results permutation.symm returned)
  minimalResults := fun context atom bindings returned=>
    source.minimalResults (space permutation.symm context) (renameTypeVars permutation.symm atom)
      (renameBindings permutation.symm bindings) (results permutation.symm returned)

def host (permutation : Equiv.Perm String) (source : Minimal.HostPackage) : Minimal.HostPackage :=
  ⟨services permutation source.services,enumeration permutation source.enumeration⟩

/-- A transported foreign service is explicit. This construction makes no
claim that an arbitrary unchanged service is insensitive to variable names. -/
def dispatch (permutation : Equiv.Perm String) (source : GroundedDispatch) : GroundedDispatch where
  executable := fun operator=>source.executable (renameTypeVars permutation.symm operator)
  outcome := fun operator arguments returned=>
    source.outcome (renameTypeVars permutation.symm operator)
      (arguments.map (renameTypeVars permutation.symm)) (grounded permutation.symm returned)
  minimal := source.minimal.map (host permutation)
  valueProvenance := fun operator arguments=>source.valueProvenance
    (renameTypeVars permutation.symm operator) (arguments.map (renameTypeVars permutation.symm))
  bindingMode := fun operator arguments=>source.bindingMode
    (renameTypeVars permutation.symm operator) (arguments.map (renameTypeVars permutation.symm))
  unifyBadArityMessage := fun atom=>source.unifyBadArityMessage (renameTypeVars permutation.symm atom)

/-- Type inference, casting and selection retain their actual external
relations; only the simultaneous naming convention changes. -/
def typing (permutation : Equiv.Perm String) (source : EvalTypeService) : EvalTypeService where
  typesOf := fun context atom types=>source.typesOf (space permutation.symm context)
    (renameTypeVars permutation.symm atom) (types.map (renameTypeVars permutation.symm))
  typeCast := fun scope context atom expected bindings returned=>
    source.typeCast (scope.map permutation.symm) (space permutation.symm context)
      (renameTypeVars permutation.symm atom) (renameTypeVars permutation.symm expected)
      (renameBindings permutation.symm bindings) (result permutation.symm returned)
  instantiateTypes := fun scope raw selected =>
    source.instantiateTypes (scope.map permutation.symm)
      (raw.map (renameTypeVars permutation.symm))
      (selected.map (renameTypeVars permutation.symm))
  candidateScan := fun scope context expression expected bindings candidates selected=>
    source.candidateScan (scope.map permutation.symm) (space permutation.symm context) (renameTypeVars permutation.symm expression)
      (renameTypeVars permutation.symm expected) (renameBindings permutation.symm bindings)
      (candidates.map (renameTypeVars permutation.symm)) (scanOutcome permutation.symm selected)

@[simp] theorem typed_types (permutation : Equiv.Perm String) (source : EvalTypeService)
    (context : Space) (atom : Atom) (types : List Atom) :
    (typing permutation source).typesOf (space permutation context)
      (renameTypeVars permutation atom) (types.map (renameTypeVars permutation)) ↔
      source.typesOf context atom types := by simp [typing,Function.comp_def]

@[simp] theorem typed_cast (permutation : Equiv.Perm String) (source : EvalTypeService)
    (scope : List String) (context : Space) (atom expected : Atom) (bindings : Bindings) (returned : ResultPair) :
    (typing permutation source).typeCast (scope.map permutation) (space permutation context)
      (renameTypeVars permutation atom) (renameTypeVars permutation expected)
      (renameBindings permutation bindings) (result permutation returned) ↔
      source.typeCast scope context atom expected bindings returned := by
  simp [typing,List.map_map,Function.comp_def]

@[simp] theorem typed_instances (permutation : Equiv.Perm String) (source : EvalTypeService)
    (scope : List String) (raw selected : List Atom) :
    (typing permutation source).instantiateTypes (scope.map permutation)
      (raw.map (renameTypeVars permutation)) (selected.map (renameTypeVars permutation)) ↔
      source.instantiateTypes scope raw selected := by
  simp [typing, List.map_map, Function.comp_def]

@[simp] theorem typed_scan (permutation : Equiv.Perm String) (source : EvalTypeService)
    (scope : List String) (context : Space) (atom expected : Atom) (bindings : Bindings) (candidates : List Atom)
    (selected : FunctionCandidateScanOutcome) :
    (typing permutation source).candidateScan (scope.map permutation) (space permutation context)
      (renameTypeVars permutation atom) (renameTypeVars permutation expected)
      (renameBindings permutation bindings) (candidates.map (renameTypeVars permutation))
      (scanOutcome permutation selected) ↔
      source.candidateScan scope context atom expected bindings candidates selected := by
  simp [typing,List.map_map,Function.comp_def]

@[simp] theorem dispatch_executable (permutation : Equiv.Perm String) (source : GroundedDispatch) (operator : Atom) :
    (dispatch permutation source).executable (renameTypeVars permutation operator) ↔
      source.executable operator := by simp [dispatch]

@[simp] theorem dispatch_outcome (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (operator : Atom) (arguments : List Atom) (returned : GroundedResult) :
    (dispatch permutation source).outcome (renameTypeVars permutation operator)
      (arguments.map (renameTypeVars permutation)) (grounded permutation returned) ↔
      source.outcome operator arguments returned := by simp [dispatch,Function.comp_def]

@[simp] theorem dispatch_provenance (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (operator : Atom) (arguments : List Atom) :
    (dispatch permutation source).valueProvenance (renameTypeVars permutation operator)
      (arguments.map (renameTypeVars permutation)) = source.valueProvenance operator arguments := by
  simp [dispatch,Function.comp_def]

@[simp] theorem dispatch_bindingMode (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (operator : Atom) (arguments : List Atom) :
    (dispatch permutation source).bindingMode (renameTypeVars permutation operator)
      (arguments.map (renameTypeVars permutation)) = source.bindingMode operator arguments := by
  simp [dispatch,Function.comp_def]

@[simp] theorem encoded_result (permutation : Equiv.Perm String) (source : Minimal.Services) (returned : ResultPair) :
    Minimal.encodeResult (services permutation source) (result permutation returned) =
      renameTypeVars permutation (Minimal.encodeResult source returned) := by
  simp [Minimal.encodeResult,services,result]

@[simp] theorem encoded_results (permutation : Equiv.Perm String) (source : Minimal.Services) (returned : ResultSet) :
    Minimal.encodeResults (services permutation source) (results permutation returned) =
      renameTypeVars permutation (Minimal.encodeResults source returned) := by
  simp [Minimal.encodeResults,results,List.map_map,Function.comp_def]


@[simp] theorem services_inverse (permutation : Equiv.Perm String) (source : Minimal.Services) :
    services permutation.symm (services permutation source) = source := by
  cases source
  simp [services]

@[simp] theorem enumeration_inverse (permutation : Equiv.Perm String) (source : Minimal.Enumeration) :
    enumeration permutation.symm (enumeration permutation source) = source := by
  cases source
  simp [enumeration]

@[simp] theorem host_inverse (permutation : Equiv.Perm String) (source : Minimal.HostPackage) :
    host permutation.symm (host permutation source) = source := by
  cases source
  simp [host]

@[simp] theorem dispatch_inverse (permutation : Equiv.Perm String) (source : GroundedDispatch) :
    dispatch permutation.symm (dispatch permutation source) = source := by
  cases source
  simp [dispatch,Function.comp_def,Option.map_map]

@[simp] theorem typing_inverse (permutation : Equiv.Perm String) (source : EvalTypeService) :
    typing permutation.symm (typing permutation source) = source := by
  cases source
  simp [typing,Function.comp_def,List.map_map]

@[simp] theorem host_call (permutation : Equiv.Perm String) (source : GroundedDispatch) (atom : Atom) :
    Minimal.HostCall (dispatch permutation source) (renameTypeVars permutation atom) ↔
      Minimal.HostCall source atom := by
  cases atom with
  | symbol | var | grounded => simp [Minimal.HostCall]
  | expression atoms =>
    cases atoms with
    | nil => simp [Minimal.HostCall]
    | cons first rest => simp [Minimal.HostCall]

@[simp] theorem nonGrounded_call (permutation : Equiv.Perm String) (source : GroundedDispatch) (atom : Atom) :
    NonGroundedCallRel (dispatch permutation source) (renameTypeVars permutation atom) ↔
      NonGroundedCallRel source atom := by
  simp only [NonGroundedCallRel, host_call, Minimal.embeddedInstruction_renameTypeVars]

@[simp] theorem completed_keep (permutation : Equiv.Perm String) (value expected : Atom) :
    CompletedNativeKeepRel (renameTypeVars permutation value) (renameTypeVars permutation expected) ↔
      CompletedNativeKeepRel value expected := by
  unfold CompletedNativeKeepRel
  simp only [stopped_iff,Atom.undefinedType,Atom.atomType,atom_eq_symbol,metaType_iff]
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨intrinsic,isMeta,passes⟩
    refine ⟨intrinsic,isMeta,?_⟩
    rcases passes with same | variableCase
    · exact Or.inl ((renameTypeVars_perm_injective permutation) (same.trans (metaType_fixed isMeta permutation).symm))
    · exact Or.inr variableCase
  · rintro ⟨intrinsic,isMeta,passes⟩
    refine ⟨intrinsic,isMeta,?_⟩
    rcases passes with rfl | variableCase
    · exact Or.inl (metaType_fixed isMeta permutation)
    · exact Or.inr variableCase

theorem completed_return (permutation : Equiv.Perm String)
    {context : Space} {types : EvalTypeService} {value expected : Atom}
    {protectedNames : List String} {bindings : BindingFrame} {returned : FrameResult}
    (derived : CompletedNativeReturnRel context types value expected bindings returned (protectedScope := protectedNames)) :
    CompletedNativeReturnRel (space permutation context) (typing permutation types)
      (renameTypeVars permutation value) (renameTypeVars permutation expected)
      (BindingFrame.rename permutation bindings) (frameResult permutation returned)
      (protectedScope := protectedNames.map permutation) := by
  cases derived with
  | keep keep => exact .keep ((completed_keep permutation value expected).mpr keep)
  | cast notKeep cast updated =>
    exact .cast (by simpa using notKeep) ((typed_cast permutation types protectedNames _ _ _ _ _).mpr cast) (updated.rename permutation)

@[simp] theorem minimal_host (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (provided : Minimal.HostPackage) (same : source.minimal=some provided) :
    (dispatch permutation source).minimal = some (host permutation provided) := by
  simp [dispatch,same]

@[simp] theorem native_call (permutation : Equiv.Perm String) (source : Minimal.Services)
    (name function arguments : Atom) (bindings : Bindings) (returned : ResultPair) :
    (services permutation source).nativeCall (renameTypeVars permutation name)
      (renameTypeVars permutation function) (renameTypeVars permutation arguments)
      (renameBindings permutation bindings) (result permutation returned) ↔
      source.nativeCall name function arguments bindings returned := by simp [services]

@[simp] theorem minimal_enumeration (permutation : Equiv.Perm String) (source : Minimal.Enumeration)
    (context : Space) (atom : Atom) (bindings : Bindings) (returned : ResultSet) :
    (enumeration permutation source).minimalResults (space permutation context)
      (renameTypeVars permutation atom) (renameBindings permutation bindings)
      (results permutation returned) ↔ source.minimalResults context atom bindings returned := by
  simp [enumeration]

@[simp] theorem context_payload (permutation : Equiv.Perm String) (source : Minimal.Services) (context : Space) :
    (services permutation source).contextPayload (space permutation context) = source.contextPayload context := by
  simp [services]


theorem native_emission (permutation : Equiv.Perm String)
    {source : GroundedDispatch} {operator raw value : Atom} {arguments : List Atom} {bindings : BindingFrame}
    (derived : NativeEmissionRel source operator arguments bindings raw value) :
    NativeEmissionRel (dispatch permutation source) (renameTypeVars permutation operator)
      (arguments.map (renameTypeVars permutation)) (BindingFrame.rename permutation bindings)
      (renameTypeVars permutation raw) (renameTypeVars permutation value) := by
  cases derived with
  | raw mode => exact .raw (by simpa using mode)
  | materialized mode materialized =>
    exact .materialized (by simpa using mode) (materialized.rename permutation)


/-- Rendering is an explicit service; its strings are not variable syntax. -/
@[simp] theorem diagnostic_message (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (atom : Atom) :
    (dispatch permutation source).unifyBadArityMessage (renameTypeVars permutation atom) =
      source.unifyBadArityMessage atom := by simp [dispatch]

theorem malformed_call_error (permutation : Equiv.Perm String) (source : GroundedDispatch)
    (atom : Atom) :
    mkErrorMessage (renameTypeVars permutation atom)
        ((dispatch permutation source).unifyBadArityMessage (renameTypeVars permutation atom)) =
      renameTypeVars permutation (mkErrorMessage atom (source.unifyBadArityMessage atom)) := by
  simp [mkErrorMessage]


theorem type_model (p : Equiv.Perm String) {bindings : Bindings}
    (model : ∃ valuation,TypeBindingSatisfied valuation bindings) :
    ∃ valuation,TypeBindingSatisfied valuation (renameBindings p bindings) := by
  obtain ⟨valuation,satisfied⟩ := model
  refine ⟨valuation ∘ p.symm,(renameBindings_typeBindingSatisfied _ _ _).mpr ?_⟩
  simpa [Function.comp_def] using satisfied

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Eval.Steps Spec.Match.Merge

open Spec.Type.Presentation.ScopeObservation

theorem type_candidate_variant (p : Equiv.Perm String) {scope : List String}
    {original instantiated : Atom}
    (variant : Exact.TypeCandidateAlphaVariantRel scope original instantiated) :
    Exact.TypeCandidateAlphaVariantRel (scope.map p)
      (renameTypeVars p original) (renameTypeVars p instantiated) := by
  obtain ⟨rename, injective, rfl, fresh⟩ := variant
  refine ⟨fun name => p (rename (p.symm name)),
    p.injective.comp (injective.comp p.symm.injective), ?_, ?_⟩
  · simp only [renameTypeVars_comp]
    apply renameTypeVars_congr_on_typeVars
    intro name _
    simp
  · intro name member
    rw [typeVars_renameTypeVars] at member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    simpa using fresh old oldMember

theorem argument_variants (p : Equiv.Perm String) {scope : List String}
    {original instantiated : List Atom}
    (variants : Exact.ArgumentAlphaVariantsRel scope original instantiated) :
    Exact.ArgumentAlphaVariantsRel (scope.map p)
      (original.map (renameTypeVars p)) (instantiated.map (renameTypeVars p)) := by
  induction variants with
  | nil => exact .nil _
  | cons variant _rest ih =>
      exact .cons (type_candidate_variant p variant)
        (by simpa only [List.map_append, typeVars_renameTypeVars] using ih)

@[simp] theorem invocation_scope (p : Equiv.Perm String) (protectedNames : List String)
    (live : List Atom) (subject expected : Atom) (bindings : Bindings) :
    invocationTypeScope (protectedNames.map p) (live.map (renameTypeVars p))
      (renameTypeVars p subject) (renameTypeVars p expected) (renameBindings p bindings) =
      (invocationTypeScope protectedNames live subject expected bindings).map p := by
  simp only [invocationTypeScope, List.map_append, List.map_cons, List.map_nil,
    ← typeVarsList_renameTypeVars, specBindingVars_renameBindings]

mutual

theorem eval_atom (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult}
    {protectedNames : List String} {types : EvalTypeService}
    (derived : EvalAtomRawRel context service live atom expected bindings returned
      (protectedScope := protectedNames) (typing := types)) :
    EvalAtomRawRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .emptyOrError atom expected bindings stopped => by exact .emptyOrError _ _ _ (by simpa using stopped)
  | .typePass atom expected intrinsic bindings nonstopped intrinsicType pass => by
    exact .typePass _ _ (renameTypeVars p intrinsic) _ (by simpa using nonstopped)
      (metaType p intrinsicType) ((pass_type p _ _).mpr pass)
  | .cast atom expected intrinsic bindings returned nonstopped intrinsicType noPass shape cast updated => by
    exact .cast _ _ (renameTypeVars p intrinsic) _ _ (by simpa using nonstopped)
      (metaType p intrinsicType) ((not_congr (pass_type p _ _)).mpr noPass) (cast_shape p shape)
      (by simpa only [invocation_scope, BindingFrame.rename, frameResult_raw] using
        (typed_cast p _ _ _ _ _ _ _).mpr cast) (updated.rename p)
  | .interpretSuccess atom expected intrinsic bindings returned nonstopped intrinsicType noPass shape interpreted nonerror => by
    exact .interpretSuccess _ _ (renameTypeVars p intrinsic) _ _ (by simpa using nonstopped)
      (metaType p intrinsicType) ((not_congr (pass_type p _ _)).mpr noPass) (nonempty_expression p shape)
      (interpret_expression p interpreted) (by simpa [frameResult] using nonerror)
  | .interpretError atom expected intrinsic bindings returned nonstopped intrinsicType noPass shape interpreted error => by
    exact .interpretError _ _ (renameTypeVars p intrinsic) _ _ (by simpa using nonstopped)
      (metaType p intrinsicType) ((not_congr (pass_type p _ _)).mpr noPass) (nonempty_expression p shape)
      (interpret_expression p interpreted) (by simpa [frameResult] using error)
termination_by structural derived

theorem interpret_expression (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : InterpretExpressionRel context service live atom expected bindings returned (protectedScope := protectedNames) (typing := types)) :
    InterpretExpressionRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .functionPath expression expected operator arguments rawTypes candidates selected callType bindings applicable interpreted called
      shape inferred instantiated scanned updated callTypeEq functionDerivation callDerivation => by
    refine .functionPath _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      (rawTypes.map (renameTypeVars p)) (candidates.map (renameTypeVars p)) (policy p selected) (renameTypeVars p callType)
      _ (BindingFrame.rename p applicable) (frameResult p interpreted) _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · simp [shape]
    · exact (typed_types p _ _ _ _).mpr inferred
    · simpa only [invocation_scope, BindingFrame.rename] using (typed_instances p _ _ _ _).mpr instantiated
    · simpa only [invocation_scope, BindingFrame.rename, scanOutcome] using (typed_scan p _ _ _ _ _ _ _ _).mpr scanned
    · exact updated.rename p
    · by_cases isExpression : selected.returnType = .symbol "Expression"
      <;> simp [policy,callTypeEq,Atom.expressionType,Atom.undefinedType,isExpression]
    · simpa only [List.map_cons,policy] using interpret_function p functionDerivation
    · exact call p callDerivation
  | .tuplePath expression expected operator arguments rawTypes candidates errors bindings tuple called
      shape inferred instantiated scanned tupleDerivation callDerivation => by
    refine .tuplePath _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      (rawTypes.map (renameTypeVars p)) (candidates.map (renameTypeVars p)) (errors.map (renameTypeVars p)) _ (frameResult p tuple) _
      (by simp [shape]) ((typed_types p _ _ _ _).mpr inferred)
      (by simpa only [invocation_scope, BindingFrame.rename] using (typed_instances p _ _ _ _).mpr instantiated) ?_ ?_ (call p callDerivation)
    · simpa only [invocation_scope, BindingFrame.rename, scanOutcome] using (typed_scan p _ _ _ _ _ _ _ _).mpr scanned
    · simpa only [List.map_cons] using interpret_tuple p tupleDerivation
  | .functionError expression expected operator error arguments rawTypes candidates errors eligible bindings
      shape inferred instantiated scanned present => by
    exact .functionError _ _ (renameTypeVars p operator) (renameTypeVars p error)
      (arguments.map (renameTypeVars p)) (rawTypes.map (renameTypeVars p)) (candidates.map (renameTypeVars p))
      (errors.map (renameTypeVars p)) eligible _ (by simp [shape])
      ((typed_types p _ _ _ _).mpr inferred)
      (by simpa only [invocation_scope, BindingFrame.rename] using (typed_instances p _ _ _ _).mpr instantiated) (by simpa only [invocation_scope, BindingFrame.rename, scanOutcome] using (typed_scan p _ _ _ _ _ _ _ _).mpr scanned)
      (List.mem_map.mpr ⟨error,present,rfl⟩)
termination_by structural derived

theorem interpret_function (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {expression functionType expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : InterpretFunctionRel context service live expression functionType expected bindings returned (protectedScope := protectedNames) (typing := types)) :
    InterpretFunctionRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p expression) (renameTypeVars p functionType) (renameTypeVars p expected)
      (BindingFrame.rename p bindings) (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .headError expression functionType expected operator declaredReturn arguments argumentTypes bindings head
      shape functionShape headDerivation stopped => by
    refine .headError _ _ _ (renameTypeVars p operator) (renameTypeVars p declaredReturn)
      (arguments.map (renameTypeVars p)) (argumentTypes.map (renameTypeVars p)) _ _
      (by simp [shape]) ((functionType_iff p _ _ _).mpr functionShape) ?_ (by simpa [frameResult] using stopped)
    simpa only [List.map_cons,List.map_append,scope] using eval_atom p headDerivation
  | .tailError expression functionType expected operator declaredReturn arguments argumentTypes bindings head tail
      shape functionShape headDerivation nonstopped tailDerivation noPacket => by
    refine .tailError _ _ _ (renameTypeVars p operator) (renameTypeVars p declaredReturn)
      (arguments.map (renameTypeVars p)) (argumentTypes.map (renameTypeVars p)) _ (frameResult p head) _
      (by simp [shape]) ((functionType_iff p _ _ _).mpr functionShape) ?_
      (by simpa [frameResult] using nonstopped) ?_ (by simpa [frameResult] using noPacket)
    · simpa only [List.map_cons,List.map_append,scope] using eval_atom p headDerivation
    · simpa only [List.map_cons,frameResult] using interpret_args p tailDerivation
  | .success expression functionType expected operator declaredReturn arguments argumentTypes bindings head tail
      shape functionShape headDerivation nonstopped tailDerivation packetShape => by
    simpa only [frameResult,atom_expr,List.map_cons,values] using
      InterpretFunctionRel.success (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p expression) (renameTypeVars p functionType) (renameTypeVars p expected)
        (renameTypeVars p operator) (renameTypeVars p declaredReturn)
        (arguments.map (renameTypeVars p)) (argumentTypes.map (renameTypeVars p))
        (BindingFrame.rename p bindings) (frameResult p head) (frameResult p tail)
        (by simp [shape]) ((functionType_iff p _ _ _).mpr functionShape)
        (by simpa only [List.map_cons,List.map_append,scope] using eval_atom p headDerivation)
        (by simpa [frameResult] using nonstopped)
        (by simpa only [List.map_cons,frameResult] using interpret_args p tailDerivation)
        ((isPacket_iff p _).mpr packetShape)
termination_by structural derived

theorem interpret_args (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {arguments expected : List Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : InterpretArgsRel context service live arguments expected bindings returned (protectedScope := protectedNames) (typing := types)) :
    InterpretArgsRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (arguments.map (renameTypeVars p)) (expected.map (renameTypeVars p)) (BindingFrame.rename p bindings)
      (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .nil bindings => by
    simpa [frameResult] using InterpretArgsRel.nil
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (BindingFrame.rename p bindings)
  | .headChangedError argument arguments expected expecteds bindings head headDerivation stopped changed => by
    exact .headChangedError _ _ _ _ _ _
      (by simpa only [List.map_append,List.map_nil] using eval_atom p headDerivation)
      (by simpa [frameResult] using stopped) (by simpa [frameResult] using changed)
  | .tailError argument arguments expected expecteds bindings head tail headDerivation eligible tailDerivation noPacket => by
    exact .tailError _ _ _ _ _ (frameResult p head) _
      (by simpa only [List.map_append,List.map_nil] using eval_atom p headDerivation)
      (by simpa [frameResult] using eligible)
      (by simpa only [List.map_cons,frameResult] using interpret_args p tailDerivation)
      (by simpa [frameResult] using noPacket)
  | .success argument arguments expected expecteds bindings head tail headDerivation eligible tailDerivation packetShape => by
    simpa only [frameResult,packet,List.map_cons,values] using
      InterpretArgsRel.success (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p argument) (arguments.map (renameTypeVars p))
        (renameTypeVars p expected) (expecteds.map (renameTypeVars p))
        (BindingFrame.rename p bindings) (frameResult p head) (frameResult p tail)
        (by simpa only [List.map_append,List.map_nil] using eval_atom p headDerivation)
        (by simpa [frameResult] using eligible)
        (by simpa only [List.map_cons,frameResult] using interpret_args p tailDerivation)
        ((isPacket_iff p _).mpr packetShape)
termination_by structural derived

theorem interpret_tuple (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {expression : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : InterpretTupleRel context service live expression bindings returned (protectedScope := protectedNames) (typing := types)) :
    InterpretTupleRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p expression) (BindingFrame.rename p bindings) (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .nil bindings => by
    simpa [frameResult,Atom.unit] using InterpretTupleRel.nil
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (BindingFrame.rename p bindings)
  | .singleton atom bindings returned headDerivation nonstopped => by
    simpa [frameResult] using InterpretTupleRel.singleton
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation) (by simpa [frameResult] using nonstopped)
  | .singletonError atom bindings returned headDerivation stopped => by
    simpa [frameResult] using InterpretTupleRel.singletonError
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation) (by simpa [frameResult] using stopped)
  | .headError head tail bindings returned nonempty headDerivation stopped => by
    simpa [frameResult] using InterpretTupleRel.headError
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p head) (tail.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (frameResult p returned) (by simpa using nonempty)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation) (by simpa [frameResult] using stopped)
  | .tailError head tail bindings first rest nonempty headDerivation nonstopped tailDerivation stopped => by
    simpa [frameResult] using InterpretTupleRel.tailError
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p head) (tail.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (frameResult p first) (frameResult p rest) (by simpa using nonempty)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation)
      (by simpa [frameResult] using nonstopped)
      (by simpa [frameResult] using interpret_tuple p tailDerivation) (by simpa [frameResult] using stopped)
  | .success head tail bindings first rest nonempty headDerivation nonstopped tailDerivation restNonstopped => by
    have transported := InterpretTupleRel.success
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p head) (tail.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (frameResult p first) (frameResult p rest) (by simpa using nonempty)
      (by simpa [Atom.undefinedType] using eval_atom p headDerivation)
      (by simpa [frameResult] using nonstopped)
      (by simpa [frameResult] using interpret_tuple p tailDerivation) (by simpa [frameResult] using restNonstopped)
    cases valueEq : rest.1 <;> simpa [frameResult,valueEq,renameTypeVars] using transported
termination_by structural derived

theorem call_return (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {original expected value : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : CallReturnRel context service live original expected value bindings returned (protectedScope := protectedNames) (typing := types)) :
    CallReturnRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p original) (renameTypeVars p expected) (renameTypeVars p value)
      (BindingFrame.rename p bindings) (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .notReducible original expected bindings => by
    simpa [frameResult] using CallReturnRel.notReducible
      (space:=space p context) (dispatch:=dispatch p service) (live:=live.map (renameTypeVars p))
      (typing:=typing p types) (renameTypeVars p original) (renameTypeVars p expected) (BindingFrame.rename p bindings)
  | .stopped original expected value bindings stopped => by exact .stopped _ _ _ _ (by simpa using stopped)
  | .evaluate original expected value bindings returned notNR nonstopped evaluated => by
    exact .evaluate _ _ _ _ _ (by simpa [Atom.notReducible] using notNR)
      (by simpa using nonstopped) (by simpa only [List.map_nil] using eval_atom p evaluated)
termination_by structural derived

theorem call (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : CallRel context service live atom expected bindings returned (protectedScope := protectedNames) (typing := types)) :
    CallRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) :=
  match derived with
  | .errorPassthrough atom expected bindings error => by exact .errorPassthrough _ _ _ (by simpa using error)
  | .embedded atom expected bindings raw returned nonerror noHost embedded invoked completed => by
    exact .embedded _ _ _ (frameResult p raw) _
      (by simpa using nonerror) (by simpa using noHost) (by simpa using embedded)
      (by simpa only [List.map_cons, Option.map_none] using core_invocation p invoked)
      (by simpa only [frameResult] using call_return p completed)
  | .groundedSuccess atom expected operator arguments bindings nativeResults nativeResult finalResult merged emitted completed
      shape executable provenance nonerror produced present merge updated emission invoked returned => by
    refine .groundedSuccess _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      _ (results p nativeResults) (result p nativeResult) _ (BindingFrame.rename p merged)
      (renameTypeVars p emitted) (frameResult p completed) (by simp [shape])
      (by simpa using executable) (by simpa using provenance)
      (by simpa using nonerror) ?_ ?_ (merge_rename p merge) (updated.rename p)
      (native_emission p emission) ?_ (call_return p returned)
    · simpa only [←dispatch_outcome p service operator arguments (.ok nativeResults),grounded] using produced
    · exact List.mem_map.mpr ⟨nativeResult,present,rfl⟩
    · simpa only [List.map_cons,Option.map_some] using core_result p invoked
  | .groundedCompletedSuccess atom expected operator arguments bindings nativeResults nativeResult finalResult merged emitted
      shape executable provenance nonerror produced present merge updated emission returned => by
    refine .groundedCompletedSuccess _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      _ (results p nativeResults) (result p nativeResult) _ (BindingFrame.rename p merged)
      (renameTypeVars p emitted) (by simp [shape]) (by simpa using executable)
      (by simpa using provenance)
      (by simpa using nonerror) ?_ ?_ (merge_rename p merge) (updated.rename p) (native_emission p emission)
      (by simpa only [invocation_scope, BindingFrame.rename] using completed_return p returned)
    · simpa only [←dispatch_outcome p service operator arguments (.ok nativeResults),grounded] using produced
    · exact List.mem_map.mpr ⟨nativeResult,present,rfl⟩
  | .groundedRuntimeError atom expected operator arguments bindings message shape executable nonerror produced => by
    simpa only [frameResult,atom_error,atom_symbol] using
      CallRel.groundedRuntimeError (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p atom) (renameTypeVars p expected) (renameTypeVars p operator)
        (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings) message
        (by simp [shape]) (by simpa using executable)
        (by simpa using nonerror)
        (by simpa only [←dispatch_outcome p service operator arguments (.runtimeError message),grounded] using produced)
  | .groundedNoReduce atom expected operator arguments bindings shape executable nonerror produced => by
    exact .groundedNoReduce _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p)) _
      (by simp [shape]) (by simpa using executable)
      (by simpa using nonerror)
      (by simpa only [←dispatch_outcome p service operator arguments .noReduce,grounded] using produced)
  | .groundedIncorrectArgument atom expected operator arguments bindings shape executable nonerror produced => by
    exact .groundedIncorrectArgument _ _ (renameTypeVars p operator) (arguments.map (renameTypeVars p)) _
      (by simp [shape]) (by simpa using executable)
      (by simpa using nonerror)
      (by simpa only [←dispatch_outcome p service operator arguments .incorrectArgument,grounded] using produced)
  | .groundedEmpty atom expected operator arguments bindings shape executable nonerror produced => by
    simpa only [frameResult,atom_empty] using
      CallRel.groundedEmpty (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p atom) (renameTypeVars p expected) (renameTypeVars p operator)
        (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings)
        (by simp [shape]) (by simpa using executable)
        (by simpa using nonerror)
        (by simpa only [←dispatch_outcome p service operator arguments (.ok []),grounded,results,List.map_nil] using produced)
  | .equation atom expected emitted materialized bindings merged finalResult completed
      nonerror nongrounded selected updated materialization invoked returned => by
    exact .equation _ _ (renameTypeVars p emitted) (renameTypeVars p materialized) _
      (BindingFrame.rename p merged) _ (frameResult p completed) (by simpa using nonerror)
      (by simpa using nongrounded) (by simpa only [List.map_cons, BindingFrame.rename] using query_candidate p selected) (updated.rename p)
      (materialization.rename p) (by simpa only [List.map_cons,Option.map_some] using core_result p invoked)
      (call_return p returned)
  | .noEquation atom expected bindings nonerror nongrounded noMatch => by
    exact .noEquation _ _ _ (by simpa using nonerror) (by simpa using nongrounded)
        (by simpa only [List.map_cons, BindingFrame.rename] using query_no_match p noMatch)
  | .allEquationsFiltered atom expected bindings nonerror nongrounded filtered => by
    simpa only [frameResult,atom_empty] using
      CallRel.allEquationsFiltered (space:=space p context) (dispatch:=dispatch p service)
        (live:=live.map (renameTypeVars p)) (typing:=typing p types)
        (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
        (by simpa using nonerror) (by simpa using nongrounded)
        (by simpa only [List.map_cons, BindingFrame.rename] using query_filtered p filtered)
termination_by structural derived

theorem core_step (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult}
    {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreStepRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreStepRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .eval context atom materialized bindings returned materialization invoked => by
    simpa [frameResult] using Minimal.CoreStepRel.eval (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (renameTypeVars p materialized) (BindingFrame.rename p bindings)
      (frameResult p returned) (materialization.rename p) (core_invocation p invoked)
  | .evalc context selected atom materialized bindings returned hostServices hostEnumeration provided materialization invoked => by
    simpa [frameResult] using Minimal.CoreStepRel.evalc (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (space p selected) (renameTypeVars p atom) (renameTypeVars p materialized)
      (BindingFrame.rename p bindings) (frameResult p returned) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided) (materialization.rename p) (core_invocation p invoked)
  | .chain context atom name template bindings returned materialized ran materialization => by
    simpa [frameResult,substitute] using Minimal.CoreStepRel.chain (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (p name) (renameTypeVars p template)
      (BindingFrame.rename p bindings) (frameResult p returned) (renameTypeVars p materialized)
      (by simpa using core_run p ran) (materialization.rename p)
  | .unifySuccess context target pattern thenBranch elseBranch emitted bindings output matched updated materialized => by
    simpa [frameResult] using Minimal.CoreStepRel.unifySuccess (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p target) (renameTypeVars p pattern)
      (renameTypeVars p thenBranch) (renameTypeVars p elseBranch) (renameTypeVars p emitted)
      (BindingFrame.rename p bindings) (BindingFrame.rename p output)
      (unify_candidate p matched) (updated.rename p) (materialized.rename p)
  | .unifyNoMatch context target pattern thenBranch elseBranch bindings missing => by
    simpa [frameResult] using Minimal.CoreStepRel.unifyNoMatch (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p target) (renameTypeVars p pattern)
      (renameTypeVars p thenBranch) (renameTypeVars p elseBranch)
      (BindingFrame.rename p bindings) (unify_no_match p missing)
  | .unifyBadArity context tail bindings wrong => by
    simpa only [frameResult, ←malformed_call_error, atom_expr, List.map_cons,
      atom_symbol] using
      Minimal.CoreStepRel.unifyBadArity (dispatch := dispatch p service)
        (live := live.map (renameTypeVars p)) (typing := typing p types)
        (caller := caller.map (renameTypeVars p))
        (space p context) (tail.map (renameTypeVars p)) (BindingFrame.rename p bindings)
        (by simpa using wrong)
  | .consAtom context head tail bindings => by
    simpa [frameResult] using Minimal.CoreStepRel.consAtom (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p head) (tail.map (renameTypeVars p)) (BindingFrame.rename p bindings)
  | .deconsAtom context head tail bindings => by
    simpa [frameResult] using Minimal.CoreStepRel.deconsAtom (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p head) (tail.map (renameTypeVars p)) (BindingFrame.rename p bindings)
  | .collapseBind context atom bindings collected hostServices hostEnumeration provided historicalFrame collectedDerivation => by
    simpa [frameResult] using Minimal.CoreStepRel.collapseBind (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (BindingFrame.rename p bindings) (results p collected)
      (services p hostServices) (enumeration p hostEnumeration) (minimal_host p service _ provided)
      (historicalFrame.rename p) ((minimal_enumeration p hostEnumeration _ _ _ _).mpr collectedDerivation)
  | .superposeBind context collected stored bindings merged hostServices hostEnumeration provided historicalFrame present merge updated => by
    simpa [frameResult, result] using Minimal.CoreStepRel.superposeBind (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (results p collected) (result p stored) (BindingFrame.rename p bindings)
      (BindingFrame.rename p merged) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided) (historicalFrame.rename p)
      (List.mem_map.mpr ⟨stored,present,rfl⟩) (merge_rename p merge) (updated.rename p)
  | .functionReturn context body returned bindings output shaped finished => by
    simpa [frameResult] using Minimal.CoreStepRel.functionReturn (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p body) (renameTypeVars p returned) (BindingFrame.rename p bindings)
      (BindingFrame.rename p output) (by obtain ⟨atoms,rfl⟩:=shaped; exact ⟨atoms.map (renameTypeVars p),atom_expr p atoms⟩)
      (by simpa [frameResult] using core_body p finished)
  | .functionNoReturn context body returned bindings output shaped finished missing => by
    simpa [frameResult,terminal] using Minimal.CoreStepRel.functionNoReturn (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p body) (renameTypeVars p returned) (BindingFrame.rename p bindings)
      (BindingFrame.rename p output) (by obtain ⟨atoms,rfl⟩:=shaped; exact ⟨atoms.map (renameTypeVars p),atom_expr p atoms⟩)
      (by simpa [frameResult] using core_body p finished) ((not_return p _).mpr missing)
  | .metta context selected atom expected bindings returned hostServices hostEnumeration provided evaluated nonerror => by
    simpa [frameResult] using Minimal.CoreStepRel.metta (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (space p selected) (renameTypeVars p atom) (renameTypeVars p expected)
      (BindingFrame.rename p bindings) (frameResult p returned) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided) (by simpa only [List.map_nil] using eval_atom p evaluated)
      (by simpa [frameResult] using nonerror)
  | .mettaAtom context selected atom bindings hostServices hostEnumeration provided => by
    simpa [frameResult,Atom.atomType] using Minimal.CoreStepRel.mettaAtom (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (space p selected) (renameTypeVars p atom) (BindingFrame.rename p bindings)
      (services p hostServices) (enumeration p hostEnumeration) (minimal_host p service _ provided)
  | .mettaError context selected atom expected bindings hostServices hostEnumeration provided error => by
    simpa [frameResult] using Minimal.CoreStepRel.mettaError (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (space p selected) (renameTypeVars p atom) (renameTypeVars p expected)
      (BindingFrame.rename p bindings) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided) (by simpa using error)
  | .contextSpace context bindings hostServices hostEnumeration provided => by
    simpa [frameResult] using Minimal.CoreStepRel.contextSpace (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (BindingFrame.rename p bindings) (services p hostServices) (enumeration p hostEnumeration)
      (minimal_host p service _ provided)
  | .callNative context name function arguments bindings returned merged hostServices hostEnumeration provided native merge updated => by
    simpa [frameResult, result] using Minimal.CoreStepRel.callNative (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p name) (renameTypeVars p function) (renameTypeVars p arguments)
      (BindingFrame.rename p bindings) (result p returned) (BindingFrame.rename p merged)
      (services p hostServices) (enumeration p hostEnumeration) (minimal_host p service _ provided)
      ((native_call p hostServices _ _ _ _ _).mpr native) (merge_rename p merge) (updated.rename p)
termination_by structural derived

theorem core_invocation (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreInvocationRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreInvocationRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .embedded context atom bindings returned nonhost instruction ran => by
    exact .embedded _ _ _ _ (by simpa using nonhost) (by simpa using instruction) (core_run p ran)
  | .grounded context operator arguments bindings merged nativeResults nativeResult returned emitted
      executable provenance produced present merge updated model emission invoked => by
    simpa [frameResult] using Minimal.CoreInvocationRel.grounded (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (BindingFrame.rename p merged) (results p nativeResults)
      (result p nativeResult) (frameResult p returned) (renameTypeVars p emitted)
      (by simpa using executable) (by simpa using provenance)
      (by simpa only [←dispatch_outcome p service operator arguments (.ok nativeResults),grounded] using produced)
      (List.mem_map.mpr ⟨nativeResult,present,rfl⟩) (merge_rename p merge) (updated.rename p) (type_model p model)
      (native_emission p emission)
      (by simpa only [Option.map_some, renameTypeVars, List.map_cons] using core_result p invoked)
  | .completedGrounded context operator arguments bindings merged nativeResults nativeResult emitted
      executable provenance produced present merge updated model emission => by
    simpa [frameResult] using Minimal.CoreInvocationRel.completedGrounded (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p))
      (BindingFrame.rename p bindings) (BindingFrame.rename p merged) (results p nativeResults)
      (result p nativeResult) (renameTypeVars p emitted)
      (by simpa using executable) (by simpa using provenance)
      (by simpa only [←dispatch_outcome p service operator arguments (.ok nativeResults),grounded] using produced)
      (List.mem_map.mpr ⟨nativeResult,present,rfl⟩) (merge_rename p merge) (updated.rename p) (type_model p model)
      (native_emission p emission)
  | .groundedEmpty context operator arguments bindings executable produced => by
    simpa [frameResult] using Minimal.CoreInvocationRel.groundedEmpty (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings)
      (by simpa using executable)
      (by simpa only [←dispatch_outcome p service operator arguments (.ok []),grounded,results,List.map_nil] using produced)
  | .groundedError context operator arguments bindings message executable produced => by
    simpa [frameResult] using Minimal.CoreInvocationRel.groundedError (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings) message
      (by simpa using executable)
      (by simpa only [←dispatch_outcome p service operator arguments (.runtimeError message),grounded] using produced)
  | .groundedNoReduce context operator arguments bindings executable produced => by
    simpa [frameResult] using Minimal.CoreInvocationRel.groundedNoReduce (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings)
      (by simpa using executable)
      (by simpa only [←dispatch_outcome p service operator arguments .noReduce,grounded] using produced)
  | .groundedIncorrectArgument context operator arguments bindings executable produced => by
    simpa [frameResult] using Minimal.CoreInvocationRel.groundedIncorrectArgument (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p operator) (arguments.map (renameTypeVars p)) (BindingFrame.rename p bindings)
      (by simpa using executable)
      (by simpa only [←dispatch_outcome p service operator arguments .incorrectArgument,grounded] using produced)
  | .equation context atom emitted materialized bindings merged returned nonhost notInstruction selected updated materialization invoked => by
    exact .equation _ _ (renameTypeVars p emitted) (renameTypeVars p materialized) _ (BindingFrame.rename p merged) _
      (by simpa using nonhost) (by simpa using notInstruction) (query_candidate p selected)
      (updated.rename p) (materialization.rename p) (core_result p invoked)
  | .noEquation context atom bindings nonhost notInstruction noMatch => by
    simpa [frameResult] using Minimal.CoreInvocationRel.noEquation (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (BindingFrame.rename p bindings)
      (by simpa using nonhost) (by simpa using notInstruction) (query_no_match p noMatch)
  | .allEquationsFiltered context atom bindings nonhost notInstruction filtered => by
    simpa [frameResult] using Minimal.CoreInvocationRel.allEquationsFiltered (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p atom) (BindingFrame.rename p bindings)
      (by simpa using nonhost) (by simpa using notInstruction) (query_filtered p filtered)
termination_by structural derived

theorem core_result (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreInvocationResultRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreInvocationResultRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .raw context atom bindings nonfunction => by exact .raw _ _ _ (by simpa using nonfunction)
  | .function context body bindings returned stepped => by
    simpa using Minimal.CoreInvocationResultRel.function (dispatch:=dispatch p service)
      (live:=live.map (renameTypeVars p)) (typing:=typing p types) (caller:=caller.map (renameTypeVars p))
      (space p context) (renameTypeVars p body) (BindingFrame.rename p bindings) (frameResult p returned)
      (by simpa using core_step p stepped)
termination_by structural derived

theorem core_run (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreRunRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreRunRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .data context atom bindings data => by exact .data _ _ _ (by simpa using data)
  | .instruction context atom bindings returned instruction nonchain stepped => by
    exact .instruction _ _ _ _ (by simpa using instruction) (by simpa using nonchain) (core_step p stepped)
  | .chain context atom bindings selected returned chainShape stepped resumed => by
    exact .chain _ _ _ (frameResult p selected) _ (by simpa using chainShape) (core_step p stepped) (core_run p resumed)
termination_by structural derived

theorem core_body (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom}
    (derived : Minimal.CoreFunctionBodyRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller)) :
    Minimal.CoreFunctionBodyRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) :=
  match derived with
  | .terminal context atom bindings raw materialized ran materialization noninstruction => by
    exact .terminal _ _ _ (frameResult p raw) (renameTypeVars p materialized)
      (core_run p ran) (materialization.rename p) (by simpa using noninstruction)
  | .resume context atom bindings raw materialized returned ran materialization instruction resumed => by
    exact .resume _ _ _ (frameResult p raw) (renameTypeVars p materialized) _
      (core_run p ran) (materialization.rename p) (by simpa using instruction) (core_body p resumed)
termination_by structural derived

end

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation

/-- The inverse action reflects raw derivations, including their complete
protected scope and reached result record. -/
theorem eval_atom_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult}
    {protectedNames : List String} {types : EvalTypeService} :
    EvalAtomRawRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) ↔
    EvalAtomRawRel context service live atom expected bindings returned
      (protectedScope := protectedNames) (typing := types) := by
  constructor
  · intro derived
    simpa [List.map_map,Function.comp_def] using eval_atom p.symm derived
  · exact eval_atom p

theorem call_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} :
    CallRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) ↔
    CallRel context service live atom expected bindings returned (protectedScope := protectedNames) (typing := types) := by
  constructor
  · intro derived
    simpa [Function.comp_def,List.map_map] using call p.symm derived
  · exact call p

theorem call_return_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {original expected value : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} :
    CallReturnRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p original) (renameTypeVars p expected) (renameTypeVars p value)
      (BindingFrame.rename p bindings) (frameResult p returned) (protectedScope := protectedNames.map p) (typing := typing p types) ↔
    CallReturnRel context service live original expected value bindings returned (protectedScope := protectedNames) (typing := types) := by
  constructor
  · intro derived
    simpa [Function.comp_def,List.map_map] using call_return p.symm derived
  · exact call_return p

theorem core_run_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom} :
    Minimal.CoreRunRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) ↔
    Minimal.CoreRunRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller) := by
  constructor
  · intro derived
    simpa [Option.map_map,Function.comp_def,List.map_map] using core_run p.symm derived
  · exact core_run p

theorem core_step_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} {caller : Option Atom} :
    Minimal.CoreStepRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (BindingFrame.rename p bindings) (frameResult p returned)
      (protectedScope := protectedNames.map p) (typing := typing p types) (caller := caller.map (renameTypeVars p)) ↔
    Minimal.CoreStepRel context service live atom bindings returned (protectedScope := protectedNames) (typing := types) (caller := caller) := by
  constructor
  · intro derived
    simpa [Option.map_map,Function.comp_def,List.map_map] using core_step p.symm derived
  · exact core_step p

/-- Success priority is transported as well: an error is published only
when all actual raw alternatives are errors on both sides. -/
theorem eval (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String}
    (derived : EvalRel context service live atom expected bindings returned types protectedNames) :
    EvalRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (typing p types) (protectedNames.map p) := by
  refine ⟨by simpa using eval_atom p derived.1, ?_⟩
  intro error candidate raw
  have sourceRaw : EvalAtomRawRel context service live atom expected bindings
      (frameResult p.symm candidate) (protectedScope := protectedNames) (typing := types) := by
    simpa [Function.comp_def,List.map_map] using eval_atom p.symm raw
  have sourceError := derived.2 (by simpa [frameResult] using error) _ sourceRaw
  simpa [frameResult] using sourceError

theorem eval_iff (p : Equiv.Perm String)
    {context : Space} {service : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {returned : FrameResult} {types : EvalTypeService} {protectedNames : List String} :
    EvalRel (space p context) (dispatch p service) (live.map (renameTypeVars p))
      (renameTypeVars p atom) (renameTypeVars p expected) (BindingFrame.rename p bindings)
      (frameResult p returned) (typing p types) (protectedNames.map p) ↔
    EvalRel context service live atom expected bindings returned types protectedNames := by
  constructor
  · intro derived
    simpa [Function.comp_def,List.map_map] using eval p.symm derived
  · exact eval p

/-- Exact physical list positions are retained by the output action. This is
a law of a chosen enumeration, not an enumeration-order requirement on HE. -/
theorem results_position (p : Equiv.Perm String) (produced : ResultSet) (position : Nat) :
    (results p produced)[position]? = produced[position]?.map (result p) := by
  simp only [results,List.getElem?_map]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming


/-! ## Simultaneous renaming of the concrete published type service -/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation
open Spec.Eval.Renaming
open Spec.Match.Merge

theorem AnnotationTypesRel.rename (p : Equiv.Perm String)
    {target : Atom} {atoms types : List Atom}
    (derivation : AnnotationTypesRel target atoms types) :
    AnnotationTypesRel (renameTypeVars p target)
      (atoms.map (renameTypeVars p)) (types.map (renameTypeVars p)) := by
  induction derivation with
  | nil => exact .nil
  | hit _tail ih =>
      simpa only [List.map_cons, atom_expr, atom_symbol, List.map_nil] using
        AnnotationTypesRel.hit ih
  | skip noAnnotation _tail ih =>
      apply AnnotationTypesRel.skip _ ih
      intro type same
      apply noAnnotation (renameTypeVars p.symm type)
      simpa only [atom_expr, List.map_cons, List.map_nil, atom_symbol, renameTypeVars_perm_inverse] using
        congrArg (renameTypeVars p.symm) same

theorem IntrinsicGroundedTypeRel.renamed (p : Equiv.Perm String)
    {value : OSLFCore.GroundedValue} {type : Atom}
    (derivation : IntrinsicGroundedTypeRel value type) :
    IntrinsicGroundedTypeRel value (renameTypeVars p type) := by
  cases derivation <;> simp only [atom_symbol] <;> constructor

theorem StorageTypesRel.rename (p : Equiv.Perm String)
    {context : Space} {atom : Atom} {types : List Atom}
    (derivation : StorageTypesRel context atom types) :
    StorageTypesRel (space p context) (renameTypeVars p atom)
      (types.map (renameTypeVars p)) := by
  cases derivation with
  | «variable» name =>
      simpa only [atom_var, List.map_cons, List.map_nil, Atom.undefinedType, atom_symbol] using
        StorageTypesRel.variable (space p context) (p name)
  | groundedKnown intrinsic notUndefined =>
      simpa only [atom_grounded, List.map_cons, List.map_nil] using
        StorageTypesRel.groundedKnown (intrinsic.renamed p)
          (by
            intro same
            exact notUndefined ((atom_eq_symbol p _ _).mp same))
  | groundedUndefined intrinsic =>
      simpa only [atom_grounded, List.map_cons, List.map_nil, Atom.undefinedType, atom_symbol] using
        StorageTypesRel.groundedUndefined (space := space p _) intrinsic
  | symbolKnown annotations nonempty =>
      simp only [atom_symbol]
      apply StorageTypesRel.symbolKnown
      · simpa only [space, atom_symbol] using annotations.rename p
      · exact fun empty => nonempty (List.map_eq_nil_iff.mp empty)
  | symbolUndefined annotations =>
      simpa only [atom_symbol, List.map_cons, List.map_nil, Atom.undefinedType] using
        StorageTypesRel.symbolUndefined
          (space := space p context)
          (by simpa only [space, atom_symbol, List.map_nil] using annotations.rename p)
  | unit =>
      simpa only [atom_expr, List.map_nil, List.map_cons, Atom.undefinedType, atom_symbol] using
        StorageTypesRel.unit (space p context)
  | expressionKnown annotations nonempty =>
      simp only [atom_expr, List.map_cons]
      apply StorageTypesRel.expressionKnown
      · simpa only [space, atom_expr, List.map_cons] using annotations.rename p
      · exact fun empty => nonempty (List.map_eq_nil_iff.mp empty)
  | expressionUndefined annotations =>
      simpa only [atom_expr, List.map_cons, List.map_nil, Atom.undefinedType, atom_symbol] using
        StorageTypesRel.expressionUndefined (space := space p context)
          (by simpa only [space, atom_expr, List.map_cons, List.map_nil] using annotations.rename p)

theorem StorageTypesRel.rename_iff (p : Equiv.Perm String)
    (context : Space) (atom : Atom) (types : List Atom) :
    StorageTypesRel (space p context) (renameTypeVars p atom) (types.map (renameTypeVars p)) ↔
      StorageTypesRel context atom types := by
  constructor
  · intro derivation
    simpa only [space_inverse, renameTypeVars_perm_inverse, atoms_inverse] using derivation.rename p.symm
  · exact fun derivation => derivation.rename p

/-- Source type collections are equivariant without choosing a storage order. -/
theorem TypeOccurrencesRel.rename (p : Equiv.Perm String)
    {context : Space} {atom : Atom} {types : Multiset Atom}
    (collected : TypeOccurrencesRel (context.atoms : Multiset Atom) atom types) :
    TypeOccurrencesRel ((space p context).atoms : Multiset Atom) (renameTypeVars p atom)
      (types.map (renameTypeVars p)) := by
  obtain ⟨stored, queried⟩ := StorageTypesRel.total context atom
  have same : types = (stored : Multiset Atom) := collected.unique queried.occurrences
  rw [same]
  simpa only [Multiset.map_coe] using (queried.rename p).occurrences

theorem TypeOfRel.rename (p : Equiv.Perm String)
    {context : Space} {atom type : Atom} (derivation : TypeOfRel context atom type) :
    TypeOfRel (space p context) (renameTypeVars p atom) (renameTypeVars p type) := by
  obtain ⟨types, inferred, member⟩ := derivation
  exact ⟨types.map (renameTypeVars p), inferred.rename p, List.mem_map.mpr ⟨type, member, rfl⟩⟩

theorem TypeMatchRel.rename (p : Equiv.Perm String)
    {left right : Atom} {bindings output : Bindings}
    (derivation : TypeMatchRel left right bindings output) :
    TypeMatchRel (renameTypeVars p left) (renameTypeVars p right)
      (renameBindings p bindings) (renameBindings p output) := by
  cases derivation with
  | undefinedLeft => simpa only [Atom.undefinedType, atom_symbol] using TypeMatchRel.undefinedLeft _ _
  | atomLeft => simpa only [Atom.atomType, atom_symbol] using TypeMatchRel.atomLeft _ _
  | undefinedRight => simpa only [Atom.undefinedType, atom_symbol] using TypeMatchRel.undefinedRight _ _
  | atomRight => simpa only [Atom.atomType, atom_symbol] using TypeMatchRel.atomRight _ _
  | structural leftU leftA rightU rightA matched merged =>
      apply TypeMatchRel.structural
      · exact fun same => leftU ((atom_eq_symbol p _ _).mp same)
      · exact fun same => leftA ((atom_eq_symbol p _ _).mp same)
      · exact fun same => rightU ((atom_eq_symbol p _ _).mp same)
      · exact fun same => rightA ((atom_eq_symbol p _ _).mp same)
      · simpa only [Parameters.rename_equalityGroundedSemantic] using matched.rename p
      · simpa only [Parameters.rename_equalityGroundedSemantic] using merged.rename p

theorem TypeMatchRel.rename_iff (p : Equiv.Perm String) (left right : Atom)
    (bindings output : Bindings) :
    TypeMatchRel (renameTypeVars p left) (renameTypeVars p right)
        (renameBindings p bindings) (renameBindings p output) ↔
      TypeMatchRel left right bindings output := by
  constructor
  · intro derivation
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using derivation.rename p.symm
  · exact fun derivation => derivation.rename p

@[simp] theorem renamed_badType (p : Equiv.Perm String) (atom expected actual : Atom) :
    renameTypeVars p (mkError atom (.badType expected actual)) =
      mkError (renameTypeVars p atom) (.badType (renameTypeVars p expected) (renameTypeVars p actual)) := by
  simp [mkError, ErrorCode.toAtom]

theorem TypeCastRel.rename (p : Equiv.Perm String)
    {context : Space} {atom expected : Atom} {bindings : Bindings} {returned : ResultPair}
    (derivation : TypeCastRel context atom expected bindings returned) :
    TypeCastRel (space p context) (renameTypeVars p atom) (renameTypeVars p expected)
      (renameBindings p bindings) (result p returned) := by
  cases derivation with
  | success inferred order noEarlier matched =>
      change StorageTypesRel _ _ _ at inferred
      apply TypeCastRel.success (inferred.rename p)
      · simpa only [List.map_append, List.map_cons] using congrArg (List.map (renameTypeVars p)) order
      · rintro earlier member candidate matchEarlier
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        apply noEarlier original originalMember (renameBindings p.symm candidate)
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using matchEarlier.rename p.symm
      · exact matched.rename p
  | failure inferred actual noMatch =>
      change StorageTypesRel _ _ _ at inferred
      simpa only [result, renamed_badType] using TypeCastRel.failure
        (inferred.rename p) (List.mem_map.mpr ⟨_, actual, rfl⟩)
        (by
          rintro candidateType member candidate matchCandidate
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          apply noMatch original originalMember (renameBindings p.symm candidate)
          simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using matchCandidate.rename p.symm)

theorem TypeCastRel.rename_iff (p : Equiv.Perm String)
    (context : Space) (atom expected : Atom) (bindings : Bindings) (returned : ResultPair) :
    TypeCastRel (space p context) (renameTypeVars p atom) (renameTypeVars p expected)
      (renameBindings p bindings) (result p returned) ↔
    TypeCastRel context atom expected bindings returned := by
  constructor
  · intro derivation
    have reversed := derivation.rename p.symm
    rw [space_inverse] at reversed
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse,
      result_inverse] using reversed
  · exact fun derivation => derivation.rename p

theorem ArgumentsApplicableRel.rename (p : Equiv.Perm String)
    {context : Space} {arguments expected : List Atom} {bindings output : Bindings}
    (derivation : ArgumentsApplicableRel context arguments expected bindings output) :
    ArgumentsApplicableRel (space p context) (arguments.map (renameTypeVars p))
      (expected.map (renameTypeVars p)) (renameBindings p bindings) (renameBindings p output) := by
  induction arguments generalizing expected bindings output with
  | nil =>
      cases derivation
      exact .nil _
  | cons argument arguments ih =>
      cases derivation with
      | cons typed matched rest =>
          change TypeOfRel context argument _ at typed
          exact .cons (typed.rename p) (matched.rename p) (ih rest)

theorem ApplicationSuccessRel.rename (p : Equiv.Perm String)
    {context : Space} {expression functionType expected : Atom} {bindings output : Bindings}
    (derivation : ApplicationSuccessRel context expression functionType expected bindings output) :
    ApplicationSuccessRel (space p context) (renameTypeVars p expression)
      (renameTypeVars p functionType) (renameTypeVars p expected)
      (renameBindings p bindings) (renameBindings p output) := by
  cases derivation with
  | mk shape function arguments returned =>
      rename_i operator returnType actualArguments argumentTypes afterArguments
      refine .mk (operator := renameTypeVars p operator) ?_ ((functionType_iff p _ _ _).mpr function)
        (arguments.rename p) (returned.rename p)
      simpa only [atom_expr, List.map_cons] using congrArg (renameTypeVars p) shape

def ApplicabilityOutcome.rename (p : Equiv.Perm String) : ApplicabilityOutcome → ApplicabilityOutcome
  | .success output => .success (renameBindings p output)
  | .error atom => .error (renameTypeVars p atom)

@[simp] theorem ApplicabilityOutcome.rename_inverse (p : Equiv.Perm String)
    (outcome : ApplicabilityOutcome) :
    (outcome.rename p).rename p.symm = outcome := by
  cases outcome <;> simp [ApplicabilityOutcome.rename]

@[simp] theorem renamed_badArgType (p : Equiv.Perm String) (atom : Atom)
    (index : Nat) (expected actual : Atom) :
    renameTypeVars p (mkError atom (.badArgType index expected actual)) =
      mkError (renameTypeVars p atom)
        (.badArgType index (renameTypeVars p expected) (renameTypeVars p actual)) := by
  simp [mkError, ErrorCode.toAtom]

@[simp] theorem renamed_wrongArity (p : Equiv.Perm String) (atom : Atom) :
    renameTypeVars p (mkError atom .incorrectNumberOfArguments) =
      mkError (renameTypeVars p atom) .incorrectNumberOfArguments := by
  simp [mkError, ErrorCode.toAtom]

theorem ApplicabilityRel.rename (p : Equiv.Perm String)
    {context : Space} {expression functionType expected : Atom}
    {bindings : Bindings} {outcome : ApplicabilityOutcome}
    (derivation : ApplicabilityRel context expression functionType expected bindings outcome) :
    ApplicabilityRel (space p context) (renameTypeVars p expression)
      (renameTypeVars p functionType) (renameTypeVars p expected)
      (renameBindings p bindings) (outcome.rename p) := by
  cases derivation with
  | success success => exact .success (success.rename p)
  | wrongArity shape function arity =>
      rename_i operator returnType actualArguments argumentTypes
      simp only [ApplicabilityOutcome.rename, renamed_wrongArity]
      refine .wrongArity (operator := renameTypeVars p operator)
        (arguments := actualArguments.map (renameTypeVars p))
        ?_ ((functionType_iff p _ _ _).mpr function) ?_
      · simpa only [atom_expr, List.map_cons] using congrArg (renameTypeVars p) shape
      · simpa only [List.length_map] using arity
  | badArgument shape function sameArity arguments typed noMatch noSuccess =>
      rename_i operator returnType argumentsBefore argumentsAfter typesBefore typesAfter
        badArgument expectedArgument actualType beforeBad
      change TypeOfRel context badArgument actualType at typed
      simp only [ApplicabilityOutcome.rename, renamed_badArgType]
      have first : (argumentsBefore.map (renameTypeVars p)).length = argumentsBefore.length :=
        List.length_map _
      rw [← first]
      refine .badArgument (operator := renameTypeVars p operator)
        (returnType := renameTypeVars p returnType)
        (argumentsAfter := argumentsAfter.map (renameTypeVars p))
        (typesAfter := typesAfter.map (renameTypeVars p))
        ?_ ?_ ?_ (arguments.rename p) (typed.rename p) ?_ ?_
      · simpa only [atom_expr, List.map_cons, List.map_append] using
          congrArg (renameTypeVars p) shape
      · simpa only [List.map_append, List.map_cons] using
          (functionType_iff p _ _ _).mpr function
      · simpa only [List.length_map] using sameArity
      · intro candidate matched
        apply noMatch (renameBindings p.symm candidate)
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using
          matched.rename p.symm
      · intro candidate success
        apply noSuccess (renameBindings p.symm candidate)
        have reversed := success.rename p.symm
        rw [space_inverse] at reversed
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using reversed
  | badReturn shape function arguments noMatch noSuccess =>
      rename_i operator returnType actualArguments argumentTypes afterArguments
      simp only [ApplicabilityOutcome.rename, renamed_badType]
      refine .badReturn (operator := renameTypeVars p operator)
        ?_ ((functionType_iff p _ _ _).mpr function) (arguments.rename p) ?_ ?_
      · simpa only [atom_expr, List.map_cons] using congrArg (renameTypeVars p) shape
      · intro candidate matched
        apply noMatch (renameBindings p.symm candidate)
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using
          matched.rename p.symm
      · intro candidate success
        apply noSuccess (renameBindings p.symm candidate)
        have reversed := success.rename p.symm
        rw [space_inverse] at reversed
        simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using reversed

end Mettapedia.Languages.MeTTa.HE.Spec.Type

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation Renaming

def SelectedTypeApplicabilityOutcome.rename (p : Equiv.Perm String) :
    SelectedTypeApplicabilityOutcome → SelectedTypeApplicabilityOutcome
  | .success selected bindings => .success (policy p selected) (renameBindings p bindings)
  | .error errors => .error (errors.map (renameTypeVars p))

@[simp] theorem SelectedTypeApplicabilityOutcome.rename_inverse
    (p : Equiv.Perm String) (outcome : SelectedTypeApplicabilityOutcome) :
    (outcome.rename p).rename p.symm = outcome := by
  cases outcome <;> simp [SelectedTypeApplicabilityOutcome.rename, Function.comp_def]

theorem PublishedCandidateApplicabilityRel.rename (p : Equiv.Perm String)
    {context : Space} {expression candidate expected : Atom} {bindings : Bindings}
    {outcome : SelectedTypeApplicabilityOutcome}
    (derivation : PublishedCandidateApplicabilityRel context expression candidate expected bindings outcome) :
    PublishedCandidateApplicabilityRel (space p context) (renameTypeVars p expression)
      (renameTypeVars p candidate) (renameTypeVars p expected) (renameBindings p bindings)
      (outcome.rename p) := by
  cases derivation with
  | success function applicable =>
      exact .success ((functionType_iff p _ _ _).mpr function) (applicable.rename p)
  | error applicable =>
      exact .error (applicable.rename p)

theorem PublishedCandidateApplicabilityRel.rename_iff (p : Equiv.Perm String)
    (context : Space) (expression candidate expected : Atom) (bindings : Bindings)
    (outcome : SelectedTypeApplicabilityOutcome) :
    PublishedCandidateApplicabilityRel (space p context) (renameTypeVars p expression)
      (renameTypeVars p candidate) (renameTypeVars p expected) (renameBindings p bindings)
      (outcome.rename p) ↔
    PublishedCandidateApplicabilityRel context expression candidate expected bindings outcome := by
  constructor
  · intro derivation
    have reversed := derivation.rename p.symm
    rw [space_inverse] at reversed
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse,
      SelectedTypeApplicabilityOutcome.rename_inverse] using reversed
  · exact fun derivation => derivation.rename p

theorem FunctionCandidateScanRel.rename (p : Equiv.Perm String)
    {context : Space} {expression expected : Atom} {bindings : Bindings}
    {candidates : List Atom} {selected : FunctionCandidateScanOutcome}
    (derivation : FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      context expression expected bindings candidates selected) :
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel (space p context)
      (renameTypeVars p expression) (renameTypeVars p expected) (renameBindings p bindings)
      (candidates.map (renameTypeVars p)) (scanOutcome p selected) := by
  have notFunction {candidate : Atom}
      (original : ¬∃ args returned, FunctionTypeRel candidate args returned) :
      ¬∃ args returned, FunctionTypeRel (renameTypeVars p candidate) args returned := by
    rintro ⟨args, returned, function⟩
    apply original
    refine ⟨args.map (renameTypeVars p.symm), renameTypeVars p.symm returned, ?_⟩
    simpa only [renameTypeVars_perm_inverse] using
      (functionType_iff p.symm _ _ _).mpr function
  have notSuccess {candidate : Atom}
      (original : ∀ candidatePolicy candidateBindings,
        ¬PublishedCandidateApplicabilityRel context expression candidate expected bindings
          (.success candidatePolicy candidateBindings)) :
      ∀ candidatePolicy candidateBindings,
        ¬PublishedCandidateApplicabilityRel (space p context) (renameTypeVars p expression)
          (renameTypeVars p candidate) (renameTypeVars p expected) (renameBindings p bindings)
          (.success candidatePolicy candidateBindings) := by
    intro candidatePolicy candidateBindings applicable
    apply original (policy p.symm candidatePolicy) (renameBindings p.symm candidateBindings)
    have reversed := applicable.rename p.symm
    rw [space_inverse] at reversed
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse,
      SelectedTypeApplicabilityOutcome.rename] using reversed
  induction derivation with
  | nil => exact .nil
  | nonFunctionSuccess absent _tail ih =>
      exact .nonFunctionSuccess (notFunction absent) ih
  | nonFunctionExhausted absent _tail ih =>
      exact .nonFunctionExhausted (notFunction absent) ih
  | functionSuccess function applicable =>
      exact .functionSuccess ((functionType_iff p _ _ _).mpr function) (applicable.rename p)
  | functionFailureThenSuccess function absent failed nonempty _tail ih =>
      exact .functionFailureThenSuccess ((functionType_iff p _ _ _).mpr function)
        (notSuccess absent) (failed.rename p)
        (fun empty => nonempty (List.map_eq_nil_iff.mp empty)) ih
  | functionFailureExhausted function absent failed nonempty _tail ih =>
      simpa only [scanOutcome, List.map_append, List.map_cons] using
        FunctionCandidateScanRel.functionFailureExhausted
          ((functionType_iff p _ _ _).mpr function) (notSuccess absent) (failed.rename p)
          (fun empty => nonempty (List.map_eq_nil_iff.mp empty)) ih

theorem FunctionCandidateScanRel.rename_iff (p : Equiv.Perm String)
    (context : Space) (expression expected : Atom) (bindings : Bindings)
    (candidates : List Atom) (selected : FunctionCandidateScanOutcome) :
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel (space p context)
      (renameTypeVars p expression) (renameTypeVars p expected) (renameBindings p bindings)
      (candidates.map (renameTypeVars p)) (scanOutcome p selected) ↔
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      context expression expected bindings candidates selected := by
  constructor
  · intro derivation
    simpa only [rawTypeLookupRel, space_inverse, renameTypeVars_perm_inverse, renameBindings_perm_inverse,
      atoms_inverse, scanOutcome_inverse] using derivation.rename p.symm
  · exact fun derivation => derivation.rename p

/-- The concrete published service is invariant under simultaneous renaming.
This is a theorem about its independent type judgments, not an assertion about
an arbitrary runtime type service or foreign diagnostic renderer. -/
theorem storageTypeService_renaming (p : Equiv.Perm String) :
    typing p storageTypeService = storageTypeService := by
  unfold typing storageTypeService
  congr 1
  · funext context atom types
    exact propext (StorageTypesRel.rename_iff p.symm context atom types)
  · funext scope context atom expected bindings returned
    exact propext (TypeCastRel.rename_iff p.symm context atom expected bindings returned)
  · funext scope raw selected
    apply propext
    constructor
    · intro same
      exact (List.map_injective_iff.mpr (renameTypeVars_perm_injective p.symm)) same
    · exact congrArg (List.map (renameTypeVars p.symm))
  · funext scope context expression expected bindings candidates selected
    exact propext (FunctionCandidateScanRel.rename_iff p.symm context expression expected bindings candidates selected)

end Mettapedia.Languages.MeTTa.HE.Spec.Eval

/-! ## Historical readout mode is closed under source execution -/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type

/-- A completed native result preserves the historical readout mode through
its actual cast/update, including an unchanged binding record. -/
theorem CompletedNativeReturnRel.preserves_historical
    {space : Space} {typing : EvalTypeService} {protectedScope : List String} {value expected : Atom}
    {frame : BindingFrame} {result : FrameResult}
    (derived : CompletedNativeReturnRel space typing value expected frame result (protectedScope := protectedScope))
    (historical : frame.Historical) : result.2.Historical := by
  cases derived with
  | keep held => exact historical
  | cast required cast updated => exact updated.preserves_historical historical

mutual


theorem EvalAtomRawRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : EvalAtomRawRel space dispatch live atom expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .emptyOrError atom expectedType bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .typePass atom expectedType metaType bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
  | .cast atom expectedType metaType bindings result h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have historical5 := h5.preserves_historical (by solve_by_elim)
    solve_by_elim
  | .interpretSuccess atom expectedType metaType bindings result h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have child4 := InterpretExpressionRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
  | .interpretError atom expectedType metaType bindings result h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have child4 := InterpretExpressionRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem InterpretExpressionRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : InterpretExpressionRel space dispatch live atom expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .functionPath expression expectedType operator arguments rawTypes types policy callType bindings applicableBindings interpreted callResult h0 h1 instanceTypes h2 h3 h4 h5 h6 => by
    intro historicalFrame
    have historical3 := h3.preserves_historical (by solve_by_elim)
    have child5 := InterpretFunctionRel.preserves_historical h5 (by solve_by_elim)
    have child6 := CallRel.preserves_historical h6 (by solve_by_elim)
    solve_by_elim
  | .tuplePath expression expectedType operator arguments rawTypes types errors bindings tupleResult callResult h0 h1 instanceTypes h2 h3 h4 => by
    intro historicalFrame
    have child3 := InterpretTupleRel.preserves_historical h3 (by solve_by_elim)
    have child4 := CallRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
  | .functionError expression expectedType operator errorAtom arguments rawTypes types errors tupleEligible bindings h0 h1 instanceTypes h2 h3 => by
    intro historicalFrame
    solve_by_elim
termination_by structural derived


theorem InterpretFunctionRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom functionType expected : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : InterpretFunctionRel space dispatch live atom functionType expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .headError expression functionType returnType operator declaredReturnType arguments argumentTypes bindings headResult h0 h1 h2 h3 => by
    intro historicalFrame
    have child2 := EvalAtomRawRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .tailError expression functionType returnType operator declaredReturnType arguments argumentTypes bindings headResult tailResult h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have child2 := EvalAtomRawRel.preserves_historical h2 (by solve_by_elim)
    have child4 := InterpretArgsRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
  | .success expression functionType returnType operator declaredReturnType arguments argumentTypes bindings headResult tailResult h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have child2 := EvalAtomRawRel.preserves_historical h2 (by solve_by_elim)
    have child4 := InterpretArgsRel.preserves_historical h4 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem InterpretArgsRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atoms expected : List Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : InterpretArgsRel space dispatch live atoms expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .nil bindings => by
    intro historicalFrame
    solve_by_elim
  | .headChangedError argument arguments expectedType expectedTypes bindings headResult h0 h1 h2 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .tailError argument arguments expectedType expectedTypes bindings headResult tailResult h0 h1 h2 h3 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    have child2 := InterpretArgsRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .success argument arguments expectedType expectedTypes bindings headResult tailResult h0 h1 h2 h3 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    have child2 := InterpretArgsRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem InterpretTupleRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : InterpretTupleRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .nil bindings => by
    intro historicalFrame
    solve_by_elim
  | .singleton atom bindings result h0 h1 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .singletonError atom bindings result h0 h1 => by
    intro historicalFrame
    have child0 := EvalAtomRawRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .headError head tail bindings headResult h0 h1 h2 => by
    intro historicalFrame
    have child1 := EvalAtomRawRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .tailError head tail bindings headResult tailResult h0 h1 h2 h3 h4 => by
    intro historicalFrame
    have child1 := EvalAtomRawRel.preserves_historical h1 (by solve_by_elim)
    have child3 := InterpretTupleRel.preserves_historical h3 (by solve_by_elim)
    solve_by_elim
  | .success head tail bindings headResult tailResult h0 h1 h2 h3 h4 => by
    intro historicalFrame
    have child1 := EvalAtomRawRel.preserves_historical h1 (by solve_by_elim)
    have child3 := InterpretTupleRel.preserves_historical h3 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem CallReturnRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {original expected atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : CallReturnRel space dispatch live original expected atom bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .notReducible original expectedType bindings => by
    intro historicalFrame
    solve_by_elim
  | .stopped original expectedType value bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .evaluate original expectedType value bindings result h0 h1 h2 => by
    intro historicalFrame
    have child2 := EvalAtomRawRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem CallRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom expected : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String}
    (derived : CallRel space dispatch live atom expected bindings result
      (protectedScope := protectedScope) (typing := typing)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .errorPassthrough atom expectedType bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .embedded atom expectedType bindings raw result h0 h1 h2 h3 h4 => by
    intro historicalFrame
    have rawHistorical := Minimal.CoreInvocationRel.preserves_historical h3 historicalFrame
    exact CallReturnRel.preserves_historical h4 rawHistorical
  | .groundedSuccess atom expectedType operator arguments bindings nativeResults nativeResult finalResult merged emitted completed h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
    intro historicalFrame
    have historical7 := h7.preserves_historical (by solve_by_elim)
    have child9 := Minimal.CoreInvocationResultRel.preserves_historical h9 (by solve_by_elim)
    have child10 := CallReturnRel.preserves_historical h10 (by solve_by_elim)
    solve_by_elim
  | .groundedCompletedSuccess atom expectedType operator arguments bindings nativeResults nativeResult finalResult merged emitted h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    intro historicalFrame
    have historical7 := h7.preserves_historical (by solve_by_elim)
    have child9 := CompletedNativeReturnRel.preserves_historical h9 (by solve_by_elim)
    solve_by_elim
  | .groundedRuntimeError atom expectedType operator arguments bindings message h0 h1 h2 h3 => by
    intro historicalFrame
    solve_by_elim
  | .groundedNoReduce atom expectedType operator arguments bindings h0 h1 h2 h3 => by
    intro historicalFrame
    solve_by_elim
  | .groundedIncorrectArgument atom expectedType operator arguments bindings h0 h1 h2 h3 => by
    intro historicalFrame
    solve_by_elim
  | .groundedEmpty atom expectedType operator arguments bindings h0 h1 h2 h3 => by
    intro historicalFrame
    solve_by_elim
  | .equation atom expectedType emitted materialized bindings merged finalResult completed h0 h1 h2 h3 h4 h5 h6 => by
    intro historicalFrame
    have historical3 := h3.preserves_historical (by solve_by_elim)
    have child5 := Minimal.CoreInvocationResultRel.preserves_historical h5 (by solve_by_elim)
    have child6 := CallReturnRel.preserves_historical h6 (by solve_by_elim)
    solve_by_elim
  | .noEquation atom expectedType bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
  | .allEquationsFiltered atom expectedType bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreStepRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreStepRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .eval space atom materialized bindings result h0 h1 => by
    intro historicalFrame
    have child1 := Minimal.CoreInvocationRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .evalc space context atom materialized bindings result services enumeration h0 h1 h2 => by
    intro historicalFrame
    have child2 := Minimal.CoreInvocationRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .chain space atom name template bindings result materialized h0 h1 => by
    intro historicalFrame
    have child0 := Minimal.CoreRunRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .unifySuccess space target pattern thenBranch elseBranch result bindings output h0 h1 h2 => by
    intro historicalFrame
    exact h1.preserves_historical historicalFrame
  | .unifyNoMatch space target pattern thenBranch elseBranch bindings missing => by
    intro historicalFrame
    exact historicalFrame
  | .unifyBadArity space tail bindings wrong => by
    intro historicalFrame
    exact historicalFrame
  | .consAtom space head tail bindings => by
    intro historicalFrame
    solve_by_elim
  | .deconsAtom space head tail bindings => by
    intro historicalFrame
    solve_by_elim
  | .collapseBind space atom bindings results services enumeration h0 _h1 h2 => by
    intro historicalFrame
    solve_by_elim
  | .superposeBind space results stored bindings merged services enumeration h0 _h1 h2 h3 h4 => by
    intro historicalFrame
    have historical4 := h4.preserves_historical (by solve_by_elim)
    solve_by_elim
  | .functionReturn space body returned bindings output h0 h1 => by
    intro historicalFrame
    have child1 := Minimal.CoreFunctionBodyRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .functionNoReturn space body result bindings output h0 h1 h2 => by
    intro historicalFrame
    have child1 := Minimal.CoreFunctionBodyRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .metta space context atom expectedType bindings result services enumeration h0 h1 h2 => by
    intro historicalFrame
    have child1 := EvalAtomRawRel.preserves_historical h1 (by solve_by_elim)
    solve_by_elim
  | .mettaAtom space context atom bindings services enumeration h0 => by
    intro historicalFrame
    solve_by_elim
  | .mettaError space context atom expectedType bindings services enumeration h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .contextSpace space bindings services enumeration h0 => by
    intro historicalFrame
    solve_by_elim
  | .callNative space name function arguments bindings result merged services enumeration h0 h1 h2 h3 => by
    intro historicalFrame
    have historical3 := h3.preserves_historical (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreInvocationRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreInvocationRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .embedded space atom bindings result h0 h1 h2 => by
    intro historicalFrame
    have child2 := Minimal.CoreRunRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .grounded space operator arguments bindings merged results nativeResult result emitted h0 h1 h2 h3 h4 h5 h6 h7 h8 => by
    intro historicalFrame
    have historical5 := h5.preserves_historical (by solve_by_elim)
    have child8 := Minimal.CoreInvocationResultRel.preserves_historical h8 (by solve_by_elim)
    solve_by_elim
  | .completedGrounded space operator arguments bindings merged results nativeResult emitted h0 h1 h2 h3 h4 h5 h6 h7 => by
    intro historicalFrame
    have historical5 := h5.preserves_historical (by solve_by_elim)
    solve_by_elim
  | .groundedEmpty space operator arguments bindings h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .groundedError space operator arguments bindings message h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .groundedNoReduce space operator arguments bindings h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .groundedIncorrectArgument space operator arguments bindings h0 h1 => by
    intro historicalFrame
    solve_by_elim
  | .equation space atom emitted materialized bindings merged result h0 h1 h2 h3 h4 h5 => by
    intro historicalFrame
    have historical3 := h3.preserves_historical (by solve_by_elim)
    have child5 := Minimal.CoreInvocationResultRel.preserves_historical h5 (by solve_by_elim)
    solve_by_elim
  | .noEquation space atom bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
  | .allEquationsFiltered space atom bindings h0 h1 h2 => by
    intro historicalFrame
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreInvocationResultRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreInvocationResultRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .raw space atom bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .function space body bindings result h0 => by
    intro historicalFrame
    have child0 := Minimal.CoreStepRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreRunRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreRunRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .data space atom bindings h0 => by
    intro historicalFrame
    solve_by_elim
  | .instruction space atom bindings result h0 h1 h2 => by
    intro historicalFrame
    have child2 := Minimal.CoreStepRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
  | .chain space atom bindings selected result h0 h1 h2 => by
    intro historicalFrame
    have child1 := Minimal.CoreStepRel.preserves_historical h1 (by solve_by_elim)
    have child2 := Minimal.CoreRunRel.preserves_historical h2 (by solve_by_elim)
    solve_by_elim
termination_by structural derived


theorem Minimal.CoreFunctionBodyRel.preserves_historical
    {space : Space} {dispatch : GroundedDispatch} {live : List Atom}
    {atom : Atom} {bindings : BindingFrame} {result : FrameResult} {typing : EvalTypeService} {protectedScope : List String} {caller : Option Atom}
    (derived : Minimal.CoreFunctionBodyRel space dispatch live atom bindings result
      (protectedScope := protectedScope) (typing := typing) (caller := caller)) :
    bindings.Historical → result.2.Historical :=
  match derived with
  | .terminal space atom bindings raw materialized h0 h1 h2 => by
    intro historicalFrame
    have child0 := Minimal.CoreRunRel.preserves_historical h0 (by solve_by_elim)
    solve_by_elim
  | .resume space atom bindings raw materialized result h0 h1 h2 h3 => by
    intro historicalFrame
    have child0 := Minimal.CoreRunRel.preserves_historical h0 (by solve_by_elim)
    have child3 := Minimal.CoreFunctionBodyRel.preserves_historical h3 (by solve_by_elim)
    solve_by_elim
termination_by structural derived

end

end Mettapedia.Languages.MeTTa.HE.Spec.Eval

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.BindingFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared MetavariableFrameStore.Snapshot
open Spec.Type Spec.Type.RuntimeRefinement Spec.Type.Presentation
open Spec.Type.Presentation.BindingTheory Spec.Type.Presentation.BindingTheory.CurrentStore

/-- Filling an actual open slot reconstructs the independently certified source
frame. The same source materialization relation reads the full old pending tuple
under the renewed table; it does not retain a stale table after a binding write. -/
theorem selected_open_write_renewal {globals : List String}
    {image next : ImageOf ContextualOperand} {raw : RowOf ContextualOperand}
    {payload : ContextualOperand} {atom : Atom} {operands : List ContextualOperand}
    {snapshot : List CurrentStore.Row} {qualified : List Atom} {rank : String → Nat}
    (written : image.write? raw.reference (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (payloadScope : operandScope globals image payload = true)
    (prepared : prepareScoped? globals image operands = some (snapshot, qualified))
    (ranked : Ranked rank (assignments snapshot))
    (read : readRow? image raw.reference = some raw) (unbound : raw.observed.value = none)
    (below : ∀ name ∈ TypeSubst.typeVars atom, rank name < rank (referenceName raw.reference)) :
    let updated := snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))
    ∃ certificate : ReadoutCertificate ⟨assignments updated, []⟩ (normalize (assignments updated)),
      prepareScoped? globals next operands = some (updated, qualified) ∧
      Update .renew
        (selected ⟨assignments snapshot, []⟩ (normalize (assignments snapshot))
          (prepareScoped?_certified prepared ranked))
        (selected ⟨assignments updated, []⟩ (normalize (assignments updated)) certificate) ∧
      ∀ pending : List Atom,
        List.Forall₂
          (selected ⟨assignments updated, []⟩ (normalize (assignments updated)) certificate).Materialization
          (pending.map (normalize (assignments snapshot)).apply)
          (pending.map (normalize (assignments updated)).apply) := by
  dsimp only
  have success := (prepare?_components (prepareScoped?_success prepared)).1
  let certificate := open_write_certified written qualifiedPayload success ranked read unbound below
  refine ⟨certificate, prepareScoped?_write written qualifiedPayload payloadScope prepared,
    Update.selected _ certificate, ?_⟩
  intro pending
  induction pending with
  | nil => exact .nil
  | cons term rest ih =>
    apply List.Forall₂.cons ?_ ih
    change (normalize (assignments (snapshot.map
      (RowOf.afterWrite next.writeClock raw.reference (some atom))))).apply term = _
    exact ((prepareScoped?_certified prepared ranked).absorbs certificate
      (fun valuation model => (open_write_models success read unbound next.writeClock atom valuation).mp model |>.1)
      term).symm

/-- The source renewal is earned from the two actual loop checks. No fixed
ordering of variable names, slots, or stored equations is prescribed. -/
theorem selected_open_write_renewal_of_noLoop {globals : List String}
    {image next : ImageOf ContextualOperand} {raw : RowOf ContextualOperand}
    {payload : ContextualOperand} {atom : Atom} {operands : List ContextualOperand}
    {snapshot : List CurrentStore.Row} {qualified : List Atom}
    (written : image.write? raw.reference (some payload) = some next)
    (qualifiedPayload : qualify? image payload = some atom)
    (payloadScope : operandScope globals image payload = true)
    (prepared : prepareScoped? globals image operands = some (snapshot, qualified))
    (beforeChecked : Bindings.hasLoop ⟨assignments snapshot, []⟩ = false)
    (afterChecked : Bindings.hasLoop
      ⟨assignments (snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))), []⟩ = false)
    (read : readRow? image raw.reference = some raw) (unbound : raw.observed.value = none) :
    let updated := snapshot.map (RowOf.afterWrite next.writeClock raw.reference (some atom))
    ∃ certificate : ReadoutCertificate ⟨assignments updated, []⟩ (normalize (assignments updated)),
      prepareScoped? globals next operands = some (updated, qualified) ∧
      Update .renew
        (selected ⟨assignments snapshot, []⟩ (normalize (assignments snapshot))
          (prepareScoped?_certified_of_noLoop prepared beforeChecked))
        (selected ⟨assignments updated, []⟩ (normalize (assignments updated)) certificate) ∧
      ∀ pending : List Atom,
        List.Forall₂
          (selected ⟨assignments updated, []⟩ (normalize (assignments updated)) certificate).Materialization
          (pending.map (normalize (assignments snapshot)).apply)
          (pending.map (normalize (assignments updated)).apply) := by
  dsimp only
  have success := (prepare?_components (prepareScoped?_success prepared)).1
  let certificate := write_certified_of_noLoop written qualifiedPayload success afterChecked
  refine ⟨certificate, prepareScoped?_write written qualifiedPayload payloadScope prepared,
    Update.selected _ certificate, ?_⟩
  intro pending
  induction pending with
  | nil => exact .nil
  | cons term rest ih =>
    apply List.Forall₂.cons ?_ ih
    change (normalize (assignments (snapshot.map
      (RowOf.afterWrite next.writeClock raw.reference (some atom))))).apply term = _
    exact ((prepareScoped?_certified_of_noLoop prepared beforeChecked).absorbs certificate
      (fun valuation model => (open_write_models success read unbound next.writeClock atom valuation).mp model |>.1)
      term).symm

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.BindingFrame

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore.WriteSourceControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.BindingFrame
open WriteControls

def beforeFrame : BindingFrame :=
  selected ⟨assignments beforeRows, []⟩ (normalize (assignments beforeRows))
    (prepareScoped?_certified before_prepared before_ranked)

def afterFrame : BindingFrame :=
  selected ⟨assignments afterRows, []⟩ (normalize (assignments afterRows)) after_certificate

theorem actual_open_write_renews_source_frame : Update .renew beforeFrame afterFrame := by
  obtain ⟨_certificate, _prepared, renewed, _pending⟩ := selected_open_write_renewal
    actual_write payload_qualified payload_scoped before_prepared before_ranked
    target_open.1 target_open.2 (by simp [TypeSubst.typeVars])
  exact renewed

theorem actual_pending_source_materializations :
    List.Forall₂ afterFrame.Materialization
      (qualified.map (normalize (assignments beforeRows)).apply)
      (qualified.map (normalize (assignments afterRows)).apply) := by
  obtain ⟨_certificate, _prepared, _renewed, pending⟩ := selected_open_write_renewal
    actual_write payload_qualified payload_scoped before_prepared before_ranked
    target_open.1 target_open.2 (by simp [TypeSubst.typeVars])
  exact pending qualified

theorem changed_binding_is_not_pure_frame_retention : ¬ Update .retain beforeFrame afterFrame := by
  intro retained
  have same := congrArg (fun frame : BindingFrame => frame.bindings.assignments.length)
    retained.retained_eq
  change (assignments beforeRows).length = (assignments afterRows).length at same
  rw [before_assignments, after_assignments] at same
  cases same

theorem actual_before_loop_check : Bindings.hasLoop ⟨assignments beforeRows, []⟩ = false := by
  rw [before_assignments]
  decide +kernel

theorem actual_after_loop_check : Bindings.hasLoop ⟨assignments afterRows, []⟩ = false := by
  rw [after_assignments]
  decide +kernel

theorem actual_loop_checks_renew_source_frame : Update .renew beforeFrame afterFrame := by
  obtain ⟨_certificate, _prepared, renewed, _pending⟩ := selected_open_write_renewal_of_noLoop
    (raw := openRow) (atom := .symbol "A") (snapshot := beforeRows) (qualified := qualified)
    actual_write payload_qualified payload_scoped before_prepared actual_before_loop_check
    actual_after_loop_check target_open.1 target_open.2
  exact renewed

theorem actual_loop_checks_preserve_pending_materializations :
    List.Forall₂ afterFrame.Materialization
      (qualified.map (normalize (assignments beforeRows)).apply)
      (qualified.map (normalize (assignments afterRows)).apply) := by
  obtain ⟨_certificate, _prepared, _renewed, pending⟩ := selected_open_write_renewal_of_noLoop
    (raw := openRow) (atom := .symbol "A") (snapshot := beforeRows) (qualified := qualified)
    actual_write payload_qualified payload_scoped before_prepared actual_before_loop_check
    actual_after_loop_check target_open.1 target_open.2
  exact pending qualified

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.CurrentStore.WriteSourceControls

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Eval.Steps
open Mettapedia.Machines.OrderedProtocol.Completion

/-!
## Completed recursive source phases

These positive, fuel-free judgments describe read-only typed and minimal
evaluation, including explicit context changes. Complete static applicability
checks retain every queried type occurrence and its reached logical frame.
Each child supplies its complete published batch
before its caller continues. Physical equation coverage comes from the
independent frontier judgment, never from executable query output. Casts use
their complete ordered source query. Grounded hosts, world effects and
captured binding collections require further constructors and their
correspondence; they are not admitted as opaque evaluation services here.
The existing recursive family carries contextual values and certified frames.
Entry reads the reached environment; reentry, publication and rebuilding use
explicit local policies. The unmarked profile remains a separate instance,
not a claim that every HE program reinterprets its ready values.

List traversals retain one derivation per occurrence. Equal child
results can therefore have separately derived continuations; a function from
result values to continuations would inadvertently identify those uses.
-/

abbrev CastLookup := List String → Space → TypeLookupRel

/-- The completed source and contextual machine can use any complete
enumeration without changing their control or continuation definitions. -/
def enumerationLookup (enumeration : TypeEnumeration) : CastLookup :=
  scopedEnumerationTypeLookup enumeration

/-- Complete literal queries leave schema instantiation to the caller's
separately chosen policy. In particular this embeds the historical raw
profile without prescribing its enumeration to the language. -/
def literalEnumerationLookup (enumeration : TypeEnumeration) : CastLookup :=
  fun _ space => Spec.Type.enumerationLookup enumeration space

def rawLookup : CastLookup := fun _ space => rawTypeLookupRel space
def scopedLookup : CastLookup := scopedTypeLookup

open Spec.Type.Presentation.BindingTheory

/-- A local choice of type-match admissibility. Finite matching checks the
conjunction at candidate selection, before deciding which type is first. -/
inductive TypeMatchingPolicy where
  | raw
  | finite
  deriving DecidableEq

def TypeMatchingPolicy.Rel (policy : TypeMatchingPolicy)
    (expected actual : Atom) (before after : Bindings) : Prop :=
  match policy with
  | .raw => TypeMatchRel expected actual before after
  | .finite => TypeMatchRel expected actual before after ∧
      ∃ valuation : String → Atom,
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation after

theorem TypeMatchingPolicy.Rel.source {policy expected actual before after}
    (matched : Rel policy expected actual before after) :
    TypeMatchRel expected actual before after := by
  cases policy with
  | raw => exact matched
  | finite => exact matched.1

/-- On queries whose raw candidates all have finite models, adding the
finite guard preserves the complete cast, including its first-success rule. -/
theorem TypeMatchingPolicy.raw_finite_cast_iff
    {space : Space} {lookup : TypeLookupRel} {value expected : Atom}
    {before : Bindings} {results : ResultSet}
    (admissible : ∀ types, lookup before value expected types →
      ∀ actual ∈ types, ∀ output, TypeMatchRel expected actual before output →
        ∃ valuation : String → Atom,
          Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation output) :
    TypeCastBatchRel space value expected before results (lookup := lookup) (matching := Rel .raw) ↔
      TypeCastBatchRel space value expected before results (lookup := lookup) (matching := Rel .finite) := by
  apply TypeCastBatchRel.matching_iff
  intro types queried actual present output
  exact ⟨fun matched => ⟨matched,admissible types queried actual present output matched⟩,
    fun matched => matched.1⟩

/-- Explicit full-versus-raw type readout. This choice alone does not model
HE's scoped publication of pending instructions. -/
inductive OperandDemandPolicy where
  | raw
  | retained
  deriving DecidableEq

/-- Local evaluation choices. Raw argument requests remain explicit;
scoped instruction publication is distinct from full type readout. -/
structure Policy where
  reentry : Entry.ReentryPolicy
  marking : Entry.MarkPolicy
  rebuilding : Entry.RebuildPolicy
  matching : TypeMatchingPolicy
  operandDemand : OperandDemandPolicy := .raw

namespace Policy

def unmarked : Policy := ⟨.reinterpret,.none,.preserve,.raw,.raw⟩
def ready : Policy := ⟨.reuse,.successes,.preserve,.raw,.raw⟩

/-- Reuse unchanged successful expressions; substitution reopens an ancestor
whose erased syntax changes. This names the local rules, not an assertion of
whole-engine compatibility. -/
def unchangedReady : Policy := ⟨.reuse,.unchanged,.reopenChanged,.raw,.raw⟩

/-- Mark unchanged successful expressions and preserve inherited marks.
Rebuilding remains an explicit choice. This does not prescribe a blanket
materialization of authored operand demands or whole-engine correspondence. -/
def unchangedPreservingReady (rebuilding : Entry.RebuildPolicy) : Policy :=
  ⟨.reuse,.unchangedPreserving,rebuilding,.raw,.raw⟩

/-- Explicit finite-type candidate; reentry, marking and rebuilding remain
those of the ready-value profile. This is not an HE compatibility default. -/
def finiteTypes : Policy := { ready with matching := .finite }

end Policy

/-- A logical activation retains its whole contextual readout. Its finite
certificate is independent of concrete binding or continuation storage. -/
structure Frame where
  bindings : Bindings
  environment : Entry.Value.Environment
  certified : ReadoutCertificate bindings (Entry.Value.eraseEnvironment environment)

namespace Frame

def source (frame : Frame) : BindingFrame :=
  .selected frame.bindings (Entry.Value.eraseEnvironment frame.environment) frame.certified

def read (policy : Policy) (frame : Frame) (value : Entry.Value) : Entry.Value :=
  Entry.Value.substitute policy.rebuilding (Entry.Value.resolve frame.environment) value

/-- An explicit full type-readout projection, not the scoped materialization
of emitted instructions. Closed Symbol demands are definitionally unchanged.
The argument execution rules do not apply this indiscriminately. -/
def argumentDemand (policy : Policy) (frame : Frame) (formal : Atom) : Atom :=
  match formal with
  | .symbol name => .symbol name
  | .grounded value => .grounded value
  | .var name => match policy.operandDemand with
      | .raw => .var name
      | .retained => (Entry.Value.resolve frame.environment name).erase
  | .expression children =>
      Spec.Type.RuntimeRefinement.applyTypeValuation (fun name => match policy.operandDemand with
        | .raw => .var name
        | .retained => (Entry.Value.resolve frame.environment name).erase) (.expression children)

theorem argumentDemand_eq_valuation (policy : Policy) (frame : Frame) (formal : Atom) :
    frame.argumentDemand policy formal = Spec.Type.RuntimeRefinement.applyTypeValuation
      (fun name => match policy.operandDemand with
        | .raw => .var name
        | .retained => (Entry.Value.resolve frame.environment name).erase) formal := by
  cases formal <;> simp only [argumentDemand, Spec.Type.RuntimeRefinement.applyTypeValuation]

@[simp] theorem argumentDemand_symbol (policy : Policy) (frame : Frame) (name : String) :
    frame.argumentDemand policy (.symbol name) = .symbol name := rfl

@[simp] theorem argumentDemand_grounded (policy : Policy) (frame : Frame) (value : OSLFCore.GroundedValue) :
    frame.argumentDemand policy (.grounded value) = .grounded value := rfl

@[simp] theorem argumentDemand_var (policy : Policy) (frame : Frame) (name : String) :
    frame.argumentDemand policy (.var name) = match policy.operandDemand with
      | .raw => .var name
      | .retained => (Entry.Value.resolve frame.environment name).erase := rfl

theorem argumentDemand_raw (policy : Policy) (frame : Frame) (formal : Atom)
    (raw : policy.operandDemand = .raw) : frame.argumentDemand policy formal = formal := by
  have unchanged := congrArg Entry.Value.erase (Entry.Value.substitute_identity policy.rebuilding (Entry.Value.ofAtom formal))
  rw [Entry.Value.erase_substitute, Entry.Value.erase_ofAtom] at unchanged
  simpa only [argumentDemand_eq_valuation, raw, Entry.Value.erase] using unchanged

theorem argumentDemand_retained (policy : Policy) (frame : Frame) (formal : Atom)
    (retained : policy.operandDemand = .retained) :
    frame.argumentDemand policy formal = (frame.read policy (Entry.Value.ofAtom formal)).erase := by
  simp only [argumentDemand_eq_valuation, retained, read, Entry.Value.erase_substitute, Entry.Value.erase_ofAtom]

theorem argumentDemand_retained_table (policy : Policy) (frame : Frame) (formal : Atom)
    (retained : policy.operandDemand = .retained) :
    frame.argumentDemand policy formal = (Entry.Value.eraseEnvironment frame.environment).apply formal := by
  rw [argumentDemand_retained policy frame formal retained]
  simp only [read, Entry.Value.erase_substitute_environment, Entry.Value.erase_ofAtom]

theorem argumentDemand_closed (policy : Policy) (frame : Frame) (formal : Atom)
    (closed : Spec.Type.Presentation.TypeSubst.typeVars formal = []) :
    frame.argumentDemand policy formal = formal := by
  cases mode : policy.operandDemand with
  | raw => exact argumentDemand_raw policy frame formal mode
  | retained =>
      rw [argumentDemand_retained policy frame formal mode]
      have fixed := Entry.Value.substitute_of_fixed_variables policy.rebuilding (Entry.Value.resolve frame.environment)
        (Entry.Value.ofAtom formal) (by
          intro name present
          simp only [Entry.Value.erase_ofAtom, closed, List.not_mem_nil] at present)
      simp only [read, fixed, Entry.Value.erase_ofAtom]

/-- Resolved-away formal variables remain protected by the incoming binding
support. Demand interpretation does not shrink the fresh-name inventory. -/
theorem argumentDemand_support (policy : Policy) (frame : Frame) (formal : Atom) (name : String) :
    (name ∈ Spec.Bindings.ScopeObservation.specBindingVars frame.bindings ∨
      name ∈ Spec.Type.Presentation.TypeSubst.typeVars (frame.argumentDemand policy formal)) ↔
    name ∈ Spec.Bindings.ScopeObservation.specBindingVars frame.bindings ∨
      name ∈ Spec.Type.Presentation.TypeSubst.typeVars formal := by
  cases mode : policy.operandDemand with
  | raw => rw [argumentDemand_raw policy frame formal mode]
  | retained =>
      rw [argumentDemand_retained_table policy frame formal mode]
      exact frame.certified.support_union_apply formal name

theorem argumentDemand_scope (policy : Policy) (frame : Frame) (formal subject : Atom)
    (live : List Atom) (scope : List String) (name : String) :
    name ∈ invocationTypeScope scope live subject (frame.argumentDemand policy formal) frame.bindings ↔
      name ∈ invocationTypeScope scope live subject formal frame.bindings := by
  have supported := argumentDemand_support policy frame formal name
  simp only [invocationTypeScope, Spec.Type.Presentation.TypeSubst.typeVarsList_append,
    Spec.Type.Presentation.TypeSubst.typeVarsList, List.mem_append, List.not_mem_nil, or_false] at ⊢
  tauto

/-- Change the constraint-record presentation while retaining the exact
annotated environment. Its new certificate follows from the complete model
agreement, rather than a supplied materializer or a new readiness choice.
Support agreement also protects subsequent fresh-instance allocation. -/
def represent (frame : Frame) (bindings : Bindings)
    (agreement : BindingSourceAgreement frame.bindings bindings) : Frame where
  bindings := bindings
  environment := frame.environment
  certified := ReadoutCertificate.of_normal_theory frame.certified.normal
    (fun model => (frame.certified.theory model).trans (agreement.solutions model))

@[simp] theorem represent_bindings (frame : Frame) (bindings : Bindings)
    (agreement : BindingSourceAgreement frame.bindings bindings) :
    (frame.represent bindings agreement).bindings = bindings := rfl

@[simp] theorem represent_environment (frame : Frame) (bindings : Bindings)
    (agreement : BindingSourceAgreement frame.bindings bindings) :
    (frame.represent bindings agreement).environment = frame.environment := rfl

/-- The whole annotated result, including every nested readiness mark,
survives this representation change for every rebuilding policy. -/
@[simp] theorem represent_read (frame : Frame) (bindings : Bindings)
    (agreement : BindingSourceAgreement frame.bindings bindings)
    (policy : Policy) (value : Entry.Value) :
    (frame.represent bindings agreement).read policy value = frame.read policy value := rfl

@[simp] theorem argumentDemand_represent (frame : Frame) (bindings : Bindings)
    (agreement : BindingSourceAgreement frame.bindings bindings) (policy : Policy) (formal : Atom) :
    (frame.represent bindings agreement).argumentDemand policy formal = frame.argumentDemand policy formal := rfl

theorem represent_self (frame : Frame) :
    frame.represent frame.bindings (.refl _) = frame := by
  cases frame
  rfl

theorem represent_trans (frame : Frame) (middle final : Bindings)
    (first : BindingSourceAgreement frame.bindings middle)
    (second : BindingSourceAgreement middle final) :
    (frame.represent middle first).represent final second =
      frame.represent final (first.trans second) := rfl

/-- A changed record preserves the complete invocation scope as a set of
protected names. Record order need not remain the same. -/
theorem represent_invocation_scope_iff (frame : Frame) (bindings : Bindings)
    (agreement : BindingSourceAgreement frame.bindings bindings)
    (protectedScope : List String) (live : List Atom) (subject expected : Atom) (name : String) :
    name ∈ invocationTypeScope protectedScope live subject expected
        (frame.represent bindings agreement).bindings ↔
      name ∈ invocationTypeScope protectedScope live subject expected frame.bindings := by
  simp only [invocationTypeScope, represent_bindings, List.mem_append]
  rw [← agreement.support name]

theorem read_source (policy : Policy) (frame : Frame) (value : Entry.Value) :
    frame.source.Materialization value.erase (frame.read policy value).erase :=
  Entry.Value.selected_materialization policy.rebuilding frame.environment frame.bindings frame.certified value

def empty : Frame := ⟨Bindings.empty,[],ReadoutCertificate.of_fold (.nil [])⟩

@[simp] theorem read_empty (policy : Policy) (value : Entry.Value) :
    empty.read policy value = value := by
  exact Entry.Value.substitute_identity policy.rebuilding value

/-- Ground contextual data is independent of the retained binding storage.
The whole annotated value, including its nested readiness, is preserved. -/
theorem read_variable_free (policy : Policy) (frame : Frame) (value : Entry.Value)
    (closed : ∀ name, ¬Spec.Match.Merge.AtomOccurs value.erase name) :
    frame.read policy value = value :=
  Entry.Value.substitute_variable_free policy.rebuilding _ value closed

@[simp] theorem read_return_symbol (policy : Policy) (frame : Frame) (name : String) :
    frame.read policy (.expression .active [.symbol "return",.symbol name]) =
      .expression .active [.symbol "return",.symbol name] := by
  cases rebuild : policy.rebuilding <;>
    simp [read,Entry.Value.substitute,Entry.Value.rebuildStatus,rebuild]

/-- A cast either retains the exact frame or follows the selected source
comparison. Transport uses its expected and actual operands, independently
of the output constraint record's presentation. -/
inductive CastRenewRel (policy : Policy) (lookup : TypeLookupRel)
    (original expected : Atom) : Frame → Frame → Prop where
  | same (frame : Frame) : CastRenewRel policy lookup original expected frame frame
  | matched {before after : Frame} {types earlier later : List Atom} {actual : Atom} :
      lookup before.bindings original expected types →
      types = earlier ++ actual :: later →
      (∀ earlierType ∈ earlier, ∀ candidate,
        ¬policy.matching.Rel expected earlierType before.bindings candidate) →
      policy.matching.Rel expected actual before.bindings after.bindings →
      Entry.Value.UnifyRel policy.rebuilding before.environment
        (Entry.Value.ofAtom expected) (Entry.Value.ofAtom actual) after.environment →
      CastRenewRel policy lookup original expected before after

/-- Changing the allowed enumeration does not replace the selected type,
unifier, reached bindings or contextual environment of this actual cast. -/
theorem CastRenewRel.change_lookup
    {policy : Policy} {first second : TypeLookupRel} {original expected : Atom}
    {before after : Frame} (renewed : CastRenewRel policy first original expected before after)
    (queries : ∀ bindings subject demand types, first bindings subject demand types →
      second bindings subject demand types) :
    CastRenewRel policy second original expected before after := by
  cases renewed with
  | same => exact .same _
  | matched queried selected rejected matched unified =>
      exact .matched (queries _ _ _ _ queried) selected rejected matched unified

/-- A selected source type match with a finite model earns its contextual
activation. Wildcards retain the whole frame; structural matching lifts the
actual match/merge candidate, without replaying the output constraint record.
Bare source merging alone does not establish the model premise. -/
theorem CastRenewRel.of_modelled_source_match
    {policy : Policy} {lookup : TypeLookupRel} {original expected actual : Atom}
    (before : Frame) {types earlier later : List Atom} {output : Bindings}
    (queried : lookup before.bindings original expected types)
    (selected : types = earlier ++ actual :: later)
    (rejected : ∀ prior ∈ earlier, ∀ candidate,
      ¬policy.matching.Rel expected prior before.bindings candidate)
    (matched : policy.matching.Rel expected actual before.bindings output)
    (model : ∃ valuation : String → Atom,
      Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation output) :
    ∃ after : Frame, after.bindings = output ∧
      CastRenewRel policy lookup original expected before after := by
  cases matched.source with
  | undefinedLeft => exact ⟨before,rfl,.same _⟩
  | atomLeft => exact ⟨before,rfl,.same _⟩
  | undefinedRight => exact ⟨before,rfl,.same _⟩
  | atomRight => exact ⟨before,rfl,.same _⟩
  | structural leftUndefined leftAtom rightUndefined rightAtom matching merged =>
      have candidate : UnifyCandidateRel (Entry.Value.ofAtom expected).erase
          (Entry.Value.ofAtom actual).erase before.bindings output := by
        simpa only [Entry.Value.erase_ofAtom] using
          (show UnifyCandidateRel expected actual before.bindings output from
            ⟨_,matching,(Spec.Bindings.ScopeObservation.LogicalMergeRel.comm
              (merged.logicalMerge model))⟩)
      obtain ⟨environment,unified,certified⟩ :=
        Entry.Value.UnifyRel.of_source_candidate (policy := policy.rebuilding) before.certified candidate
      refine ⟨⟨output,environment,certified⟩,rfl,?_⟩
      exact .matched queried selected rejected matched unified

/-- A selected cast cannot capture a protected sibling when its incoming
presentation and both matched types avoid that sibling's variables. -/
theorem CastRenewRel.avoids
    {policy : Policy} {lookup : TypeLookupRel} {original expected : Atom}
    {before after : Frame} {forbidden : List String}
    (renewed : CastRenewRel policy lookup original expected before after)
    (incoming : (Entry.Value.eraseEnvironment before.environment).Avoids forbidden)
    (expectedFresh : Spec.Type.Presentation.Freshness.AtomAvoids expected forbidden)
    (queriesFresh : ∀ types, lookup before.bindings original expected types →
      ∀ actual ∈ types, Spec.Type.Presentation.Freshness.AtomAvoids actual forbidden) :
    (Entry.Value.eraseEnvironment after.environment).Avoids forbidden := by
  cases renewed with
  | same => exact incoming
  | matched queried selected _ _ unified =>
      apply unified.avoids incoming
      · simpa only [Entry.Value.erase_ofAtom] using expectedFresh
      · apply queriesFresh _ queried
        rw [selected]
        simp

end Frame

/-- A pending value mentions no variable assigned by its retained frame.
This permits arbitrary free variables and is independent of reentry policy.
Unlike `TypeSubst.Avoids`, it does not exclude names in stored values; reading
an alias may expose exactly such a still-free name. -/
def FrameUnassignedOn (frame : Frame) (value : Atom) : Prop :=
  ∀ name ∈ Spec.Type.Presentation.TypeSubst.typeVars value, name ∉ (Entry.Value.eraseEnvironment frame.environment).keys

theorem FrameUnassignedOn.empty (value : Atom) : FrameUnassignedOn Frame.empty value := by
  intro name _
  simp [Frame.empty,Entry.Value.eraseEnvironment,Spec.Type.Presentation.TypeSubst.keys]

/-- Full avoidance supplies read stability for every pending operand in the
protected scope. Its values clause remains available for later casts. -/
theorem FrameUnassignedOn.of_avoids {frame : Frame} {value : Atom}
    {forbidden : List String}
    (avoids : (Entry.Value.eraseEnvironment frame.environment).Avoids forbidden)
    (protectedNames : ∀ name ∈ Spec.Type.Presentation.TypeSubst.typeVars value, name ∈ forbidden) :
    FrameUnassignedOn frame value :=
  fun name used assigned => avoids.keys name assigned (protectedNames name used)

/-- No substitution occurs at this entry, so the complete annotated value is
fixed under either rebuilding policy, including all nested statuses. -/
theorem FrameUnassignedOn.read_eq {frame : Frame} {value : Entry.Value}
    (unassigned : FrameUnassignedOn frame value.erase) (policy : Policy) :
    frame.read policy value = value :=
  Entry.Value.substitute_of_fixed_variables policy.rebuilding _ value
    (fun name used => Entry.Value.resolve_of_not_mem_keys _ name (unassigned name used))

/-- A private cast preserves both the strong invariant for further casts
and every protected sibling's complete annotated read. The output footprint
is derived from the source unifier rather than supplied as a premise. -/
theorem Frame.CastRenewRel.pending_reads
    {policy : Policy} {lookup : TypeLookupRel} {original expected : Atom}
    {before after : Frame} {forbidden : List String}
    (renewed : Frame.CastRenewRel policy lookup original expected before after)
    (incoming : (Entry.Value.eraseEnvironment before.environment).Avoids forbidden)
    (expectedFresh : Spec.Type.Presentation.Freshness.AtomAvoids expected forbidden)
    (queriesFresh : ∀ types, lookup before.bindings original expected types →
      ∀ actual ∈ types, Spec.Type.Presentation.Freshness.AtomAvoids actual forbidden) :
    (Entry.Value.eraseEnvironment after.environment).Avoids forbidden ∧
    ∀ value : Entry.Value,
      (∀ name ∈ Spec.Type.Presentation.TypeSubst.typeVars value.erase, name ∈ forbidden) →
      after.read policy value = value := by
  have avoided := renewed.avoids incoming expectedFresh queriesFresh
  exact ⟨avoided,fun _ protectedNames =>
    (FrameUnassignedOn.of_avoids avoided protectedNames).read_eq policy⟩

/-- Certified normal substitution removes its assigned keys from every
materialized result, including results that still contain free variables. -/
theorem FrameUnassignedOn.after_read (policy : Policy) (frame : Frame) (value : Entry.Value) :
    FrameUnassignedOn frame (frame.read policy value).erase := by
  intro name used
  rw [Frame.read,Entry.Value.erase_substitute_environment] at used
  exact frame.certified.normal.apply_variable_not_key value.erase name used

/-- Materialization is idempotent on annotated values, rather than only on
their erased syntax. This is separate from whether evaluation reuses a value. -/
theorem Frame.read_idempotent (policy : Policy) (frame : Frame) (value : Entry.Value) :
    frame.read policy (frame.read policy value) = frame.read policy value :=
  (FrameUnassignedOn.after_read policy frame value).read_eq policy

/-- A component that writes only private keys preserves a pending operand
whose variables avoid those keys. The key-footprint law is required explicitly;
freshness of a type candidate alone does not prove it for an arbitrary cast. -/
theorem FrameUnassignedOn.private_update
    {before after : Frame} {value : Atom} (unassigned : FrameUnassignedOn before value)
    (privateKeys : List String)
    (footprint : ∀ name ∈ (Entry.Value.eraseEnvironment after.environment).keys,
      name ∈ (Entry.Value.eraseEnvironment before.environment).keys ∨ name ∈ privateKeys)
    (fresh : ∀ name ∈ Spec.Type.Presentation.TypeSubst.typeVars value, name ∉ privateKeys) :
    FrameUnassignedOn after value := by
  intro name used assigned
  rcases footprint name assigned with old | privateName
  · exact unassigned name used old
  · exact fresh name used privateName

/-- A privately instantiated type protects every operand in its declared
avoidance scope. A cast with the stated private-write footprint therefore
preserves unassigned open siblings. -/
theorem FrameUnassignedOn.private_type_cast
    {before after : Frame} {value raw candidate : Atom} {avoid : List String}
    (unassigned : FrameUnassignedOn before value)
    (variant : Spec.Type.Presentation.Exact.TypeCandidateAlphaVariantRel avoid raw candidate)
    (protectedNames : ∀ name ∈ Spec.Type.Presentation.TypeSubst.typeVars value, name ∈ avoid)
    (footprint : ∀ name ∈ (Entry.Value.eraseEnvironment after.environment).keys,
      name ∈ (Entry.Value.eraseEnvironment before.environment).keys ∨
        name ∈ Spec.Type.Presentation.TypeSubst.typeVars candidate) :
    FrameUnassignedOn after value := by
  apply unassigned.private_update (Spec.Type.Presentation.TypeSubst.typeVars candidate) footprint
  intro name used inCandidate
  obtain ⟨rename,_,shape,fresh⟩ := variant
  rw [shape,Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars] at inCandidate
  obtain ⟨original,occurs,rfl⟩ := List.mem_map.mp inCandidate
  exact fresh original occurs (protectedNames _ used)

/-- The retained caller's annotated assignment values form a finite
constraint packet without reconstructing them from erased bindings. -/
def Frame.leftPacket (frame : Frame) : Entry.Value :=
  .expression .active (frame.environment.map fun row => .var row.1)

def Frame.rightPacket (frame : Frame) : Entry.Value :=
  .expression .active (frame.environment.map Prod.snd)

theorem Frame.packet_theory (frame : Frame) (valuation : String → Atom) :
    Spec.Type.RuntimeRefinement.applyTypeValuation valuation frame.leftPacket.erase =
      Spec.Type.RuntimeRefinement.applyTypeValuation valuation frame.rightPacket.erase ↔
    Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation frame.bindings := by
  have packet := bindingPacket_equation_iff valuation ⟨Entry.Value.eraseEnvironment frame.environment,[]⟩
  have table : Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation
      ⟨Entry.Value.eraseEnvironment frame.environment,[]⟩ ↔
      Spec.Type.Presentation.Theory.TypeSubstSatisfied valuation (Entry.Value.eraseEnvironment frame.environment) := by
    simp [Spec.Type.RuntimeRefinement.TypeBindingSatisfied,Spec.Type.Presentation.Theory.TypeSubstSatisfied]
  apply Iff.trans ?_ (table.trans (frame.certified.theory valuation))
  simpa only [leftPacket,rightPacket,Entry.Value.erase,Entry.Value.eraseEnvironment,bindingLeftPacket,
    bindingRightPacket,bindingAtomEquations,List.map_nil,List.append_nil,List.map_map,Function.comp_def] using packet

/-- Restoring a snapshot starts from its retained annotated environment and
conjoins the caller's actual annotated equations. The captured bindings are
not replaced by an arbitrary presentation of their erased constraints. -/
inductive Frame.SnapshotMergeRel (policy : Policy) : Frame → Frame → Frame → Prop where
  | merged {captured caller output} :
      Spec.Bindings.ScopeObservation.LogicalMergeRel captured.bindings caller.bindings output.bindings →
      Entry.Value.UnifyRel policy.rebuilding captured.environment caller.leftPacket caller.rightPacket output.environment →
      SnapshotMergeRel policy captured caller output

theorem Frame.SnapshotMergeRel.of_logical_merge {policy : Policy} (captured caller : Frame) {output : Bindings}
    (merged : Spec.Bindings.ScopeObservation.LogicalMergeRel captured.bindings caller.bindings output) :
    ∃ after : Frame, after.bindings = output ∧ SnapshotMergeRel policy captured caller after := by
  obtain ⟨valuation,capturedModel,callerModel⟩ := merged.common_model
  obtain ⟨table,ordinary,_normal,_model⟩ :=
    Spec.Type.Presentation.Completeness.AppliedTypePresentationMatchRel.exists_of_satisfied
      captured.certified.normal ((captured.certified.theory valuation).mpr capturedModel)
      caller.leftPacket.erase caller.rightPacket.erase ((caller.packet_theory valuation).mpr callerModel)
  obtain ⟨environment,unified,_erased⟩ := Entry.Value.UnifyRel.lift (policy := policy.rebuilding) ordinary
  have certified : ReadoutCertificate output (Entry.Value.eraseEnvironment environment) := by
    apply ReadoutCertificate.of_normal_theory (unified.output_normal captured.certified.normal)
    intro observer
    rw [unified.solutions captured.certified.normal observer,captured.certified.theory observer,
      caller.packet_theory observer,merged.solutions observer]
  exact ⟨⟨output,environment,certified⟩,rfl,.merged merged unified⟩

theorem Frame.SnapshotMergeRel.emptyCaller (policy : Policy) (captured : Frame) :
    SnapshotMergeRel policy captured Frame.empty captured := by
  have merged : Spec.Bindings.ScopeObservation.LogicalMergeRel Bindings.empty captured.bindings captured.bindings :=
    ⟨BindingSourceAgreement.refl _,captured.certified.satisfiable⟩
  exact .merged merged.comm (.ordinary (.identical rfl))

/-- Restoring a captured annotated environment is independent of either
input constraint-record presentation. The output frame and unifier are
retained exactly; logical conjunction supplies the input transport. -/
theorem Frame.SnapshotMergeRel.represent_inputs_iff
    {policy : Policy} {captured caller output : Frame}
    {capturedBindings callerBindings : Bindings}
    (capturedAgreement : BindingSourceAgreement captured.bindings capturedBindings)
    (callerAgreement : BindingSourceAgreement caller.bindings callerBindings) :
    SnapshotMergeRel policy
        (captured.represent capturedBindings capturedAgreement)
        (caller.represent callerBindings callerAgreement) output ↔
      SnapshotMergeRel policy captured caller output := by
  constructor
  · intro restored
    cases restored with
    | merged conjoined unified =>
        exact .merged
          ((Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
            capturedAgreement callerAgreement).mpr conjoined) unified
  · intro restored
    cases restored with
    | merged conjoined unified =>
        exact .merged
          ((Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
            capturedAgreement callerAgreement).mp conjoined) unified

/-- Native bindings conjoin constraints with the caller and run the same
annotated unifier used by equation/type instances. Existing ready subvalues
travel through those binding operations rather than being re-annotated. -/
inductive Frame.NativeRenewRel (policy : Policy) (native : Bindings) : Frame → Frame → Prop where
  | merged {before after} :
      Spec.Bindings.ScopeObservation.LogicalMergeRel native before.bindings after.bindings →
      Entry.Value.UnifyRel policy.rebuilding before.environment
        (Entry.Value.ofAtom (bindingLeftPacket native))
        (Entry.Value.ofAtom (bindingRightPacket native)) after.environment →
      NativeRenewRel policy native before after

/-- A surviving logical native merge earns its actual contextual table.
Neither the output readout nor a whole evaluation theorem is assumed. -/
theorem Frame.NativeRenewRel.of_logical_merge {policy : Policy} {native output : Bindings}
    (before : Frame) (merged : Spec.Bindings.ScopeObservation.LogicalMergeRel native before.bindings output) :
    ∃ after : Frame, after.bindings = output ∧ NativeRenewRel policy native before after := by
  obtain ⟨valuation,nativeModel,callerModel⟩ := merged.common_model
  obtain ⟨table,ordinary,_normal,_model⟩ :=
    Spec.Type.Presentation.Completeness.AppliedTypePresentationMatchRel.exists_of_satisfied
      before.certified.normal ((before.certified.theory valuation).mpr callerModel)
      (bindingLeftPacket native) (bindingRightPacket native)
      ((bindingPacket_equation_iff valuation native).mpr nativeModel)
  have matched : Spec.Type.Presentation.AppliedTypePresentationMatchRel
      (Entry.Value.eraseEnvironment before.environment)
      (Entry.Value.ofAtom (bindingLeftPacket native)).erase
      (Entry.Value.ofAtom (bindingRightPacket native)).erase table := by
    simpa only [Entry.Value.erase_ofAtom] using ordinary
  obtain ⟨environment,unified,_erased⟩ := Entry.Value.UnifyRel.lift (policy := policy.rebuilding) matched
  have certified : ReadoutCertificate output (Entry.Value.eraseEnvironment environment) := by
    apply ReadoutCertificate.of_normal_theory (unified.output_normal before.certified.normal)
    intro observer
    rw [unified.solutions before.certified.normal observer,before.certified.theory observer,
      Entry.Value.erase_ofAtom,Entry.Value.erase_ofAtom,bindingPacket_equation_iff,merged.solutions observer]
    exact and_comm
  exact ⟨⟨output,environment,certified⟩,rfl,.merged merged unified⟩

theorem Frame.NativeRenewRel.empty (policy : Policy) (before : Frame) :
    NativeRenewRel policy Bindings.empty before before := by
  apply NativeRenewRel.merged
  · exact ⟨BindingSourceAgreement.refl _,before.certified.satisfiable⟩
  · exact .ordinary (.identical rfl)

/-- Future native binding conjunctions use the same annotated unifier and
reach the same output frame after an input record is represented differently.
This is a local operation law, independent of host execution or authority. -/
theorem Frame.NativeRenewRel.represent_before_iff
    {policy : Policy} {native : Bindings} {before after : Frame} {bindings : Bindings}
    (agreement : BindingSourceAgreement before.bindings bindings) :
    NativeRenewRel policy native (before.represent bindings agreement) after ↔
      NativeRenewRel policy native before after := by
  constructor
  · intro renewed
    cases renewed with
    | merged conjoined unified =>
        exact .merged
          ((Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
            (BindingSourceAgreement.refl native) agreement).mpr conjoined) unified
  · intro renewed
    cases renewed with
    | merged conjoined unified =>
        exact .merged
          ((Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
            (BindingSourceAgreement.refl native) agreement).mp conjoined) unified

/-- One primitive type constraint transports the reached logical frame.
Unchanged constraints retain its contextual values; a changed constraint uses
the existing contextual unifier. No recursive evaluation occurs here. -/
inductive Frame.TypeRenewRel (policy : Policy) (expected actual : Atom) : Frame → Frame → Prop where
  | unchanged {frame : Frame} :
      policy.matching.Rel expected actual frame.bindings frame.bindings →
      TypeRenewRel policy expected actual frame frame
  | unified {before after : Frame} :
      policy.matching.Rel expected actual before.bindings after.bindings →
      Entry.Value.UnifyRel policy.rebuilding before.environment
        (Entry.Value.ofAtom expected) (Entry.Value.ofAtom actual) after.environment →
      TypeRenewRel policy expected actual before after

theorem Frame.preserved_type_match (policy : Policy) (frame : Frame) {expected actual : Atom}
    (matched : TypeMatchRel expected actual frame.bindings frame.bindings) :
    policy.matching.Rel expected actual frame.bindings frame.bindings := by
  cases policy.matching with
  | raw => exact matched
  | finite => exact ⟨matched,frame.certified.satisfiable⟩

/-- Both matching policies preserve the complete singleton cast under an
undefined demand. The finite profile earns its model from the actual caller
certificate; no evaluator result or desired output frame is assumed. -/
theorem Frame.undefined_cast_batch_exact {space : Space} {atom : Atom} {policy : Policy}
    (frame : Frame) {results : ResultSet}
    (source : TypeCastBatchRel space atom Atom.undefinedType frame.bindings results
      (matching := policy.matching.Rel)) : results = [(atom,frame.bindings)] := by
  have ordinary : TypeCastBatchRel space atom Atom.undefinedType frame.bindings results :=
    source.change_matching (fun _types _queried actual _present output => by
      constructor
      · intro matched; exact matched.source
      · intro matched
        cases policy.matching with
        | raw => exact matched
        | finite =>
            exact ⟨matched,by rw [matched.undefined_output]; exact frame.certified.satisfiable⟩)
  exact ordinary.undefined_exact

theorem Frame.TypeRenewRel.source {policy expected actual before after}
    (renewed : TypeRenewRel policy expected actual before after) :
    TypeMatchRel expected actual before.bindings after.bindings := by
  cases renewed with
  | unchanged matched => exact matched.source
  | unified matched _ => exact matched.source

/-- Applicability unification preserves the same strong private-scope
invariant as a selected cast, rather than only the absence of assigned keys. -/
theorem Frame.TypeRenewRel.avoids
    {policy : Policy} {expected actual : Atom} {before after : Frame}
    {forbidden : List String}
    (renewed : TypeRenewRel policy expected actual before after)
    (incoming : (Entry.Value.eraseEnvironment before.environment).Avoids forbidden)
    (expectedFresh : Spec.Type.Presentation.Freshness.AtomAvoids expected forbidden)
    (actualFresh : Spec.Type.Presentation.Freshness.AtomAvoids actual forbidden) :
    (Entry.Value.eraseEnvironment after.environment).Avoids forbidden := by
  cases renewed with
  | unchanged => exact incoming
  | unified _ unified =>
      exact unified.avoids incoming
        (by simpa only [Entry.Value.erase_ofAtom] using expectedFresh)
        (by simpa only [Entry.Value.erase_ofAtom] using actualFresh)

/-- A finite selected type constraint constructs its contextual output;
the caller supplies neither a readout table nor an evaluator theorem. -/
theorem Frame.TypeRenewRel.of_modelled_match
    {policy : Policy} {expected actual : Atom} (before : Frame) {output : Bindings}
    (matched : policy.matching.Rel expected actual before.bindings output)
    (model : ∃ valuation : String → Atom,
      Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation output) :
    ∃ after : Frame, after.bindings = output ∧ TypeRenewRel policy expected actual before after := by
  cases matched.source with
  | undefinedLeft => exact ⟨before,rfl,.unchanged matched⟩
  | atomLeft => exact ⟨before,rfl,.unchanged matched⟩
  | undefinedRight => exact ⟨before,rfl,.unchanged matched⟩
  | atomRight => exact ⟨before,rfl,.unchanged matched⟩
  | structural _ _ _ _ matching merged =>
      have candidate : UnifyCandidateRel (Entry.Value.ofAtom expected).erase
          (Entry.Value.ofAtom actual).erase before.bindings output := by
        simpa only [Entry.Value.erase_ofAtom] using
          (show UnifyCandidateRel expected actual before.bindings output from
            ⟨_,matching,(Spec.Bindings.ScopeObservation.LogicalMergeRel.comm (merged.logicalMerge model))⟩)
      obtain ⟨environment,unified,certified⟩ :=
        Entry.Value.UnifyRel.of_source_candidate (policy := policy.rebuilding) before.certified candidate
      exact ⟨⟨output,environment,certified⟩,rfl,.unified matched unified⟩

/-- A complete finite type-query occurrence is accepted or rejected. Query
copies remain separate even when their type syntax and output frames agree. -/
inductive TypeCheckRel (policy : Policy) (expected : Atom) (before : Frame) :
    Atom → Sum Atom Frame → Prop where
  | accepted {actual after} : Frame.TypeRenewRel policy expected actual before after →
      TypeCheckRel policy expected before actual (.inr after)
  | rejected {actual} :
      (∀ output, ¬policy.matching.Rel expected actual before.bindings output) →
      TypeCheckRel policy expected before actual (.inl actual)

def checkedFrames (checks : List (Sum Atom Frame)) : List Frame :=
  checks.filterMap fun | .inl _ => none | .inr frame => some frame

def checkedFailures (checks : List (Sum Atom Frame)) : List Atom :=
  checks.filterMap fun | .inl actual => some actual | .inr _ => none

theorem TypeCheckRel.finite_total {policy expected before actual}
    (finite : policy.matching = .finite) :
    ∃ check, TypeCheckRel policy expected before actual check := by
  classical
  by_cases existsMatch : ∃ output, policy.matching.Rel expected actual before.bindings output
  · obtain ⟨output,matched⟩ := existsMatch
    have model : ∃ valuation : String → Atom,
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation output := by
      rw [finite] at matched
      exact matched.2
    obtain ⟨after,_,renewed⟩ := Frame.TypeRenewRel.of_modelled_match before matched model
    exact ⟨.inr after,.accepted renewed⟩
  · exact ⟨.inl actual,.rejected (fun output matched => existsMatch ⟨output,matched⟩)⟩

/-- A raw argument still visits every declared actual-type occurrence.
Wildcard acceptance cannot be reclassified as failure to discard a copy. -/
theorem TypeCheckRel.raw_count {policy before actuals checks}
    (paired : List.Forall₂ (TypeCheckRel policy Atom.atomType before) actuals checks) :
    (checkedFrames checks).length = actuals.length := by
  induction paired with
  | nil => rfl
  | cons related _ ih =>
      cases related with
      | accepted => simpa only [checkedFrames,List.filterMap_cons,List.length_cons] using congrArg Nat.succ ih
      | rejected absent => exact (absent _ (before.preserved_type_match policy (.atomLeft _ _))).elim

/-- Every accepted query occurrence has an independently justified type
match; this projection does not identify repeated type occurrences. -/
theorem TypeCheckRel.source_member {policy expected before actuals checks after}
    (paired : List.Forall₂ (TypeCheckRel policy expected before) actuals checks)
    (present : after ∈ checkedFrames checks) :
    ∃ actual ∈ actuals, TypeMatchRel expected actual before.bindings after.bindings := by
  induction paired with
  | nil => cases present
  | @cons actual check actuals checks related rest ih =>
      cases related with
      | accepted renewed =>
          rcases List.mem_cons.mp present with rfl | member
          · exact ⟨actual,by simp,renewed.source⟩
          · obtain ⟨candidate,member,matched⟩ := ih member
            exact ⟨candidate,by simp [member],matched⟩
      | rejected _ =>
          obtain ⟨candidate,member,matched⟩ := ih present
          exact ⟨candidate,by simp [member],matched⟩

theorem TypeCheckRel.return_source_member {policy expected actual frames checks after}
    (paired : List.Forall₂ (fun frame check => TypeCheckRel policy expected frame actual check) frames checks)
    (present : after ∈ checkedFrames checks) :
    ∃ before ∈ frames, TypeMatchRel expected actual before.bindings after.bindings := by
  induction paired with
  | nil => cases present
  | @cons before check frames checks related rest ih =>
      cases related with
      | accepted renewed =>
          rcases List.mem_cons.mp present with rfl | member
          · exact ⟨before,by simp,renewed.source⟩
          · obtain ⟨frame,member,matched⟩ := ih member
            exact ⟨frame,by simp [member],matched⟩
      | rejected _ =>
          obtain ⟨frame,member,matched⟩ := ih present
          exact ⟨frame,by simp [member],matched⟩

/-- Static applicability visits every incoming binding occurrence at the
current argument position, using that occurrence's actual complete query. -/
inductive ArgumentChecksRel (space : Space) (lookup : TypeLookupRel) (policy : Policy)
    (expression argument expected : Atom) (position : Nat) :
    List Frame → List Frame → List Atom → Prop where
  | nil : ArgumentChecksRel space lookup policy expression argument expected position [] [] []
  | cons {before rest actuals checks outputs errors} :
      lookup before.bindings argument expected actuals →
      List.Forall₂ (TypeCheckRel policy expected before) actuals checks →
      ArgumentChecksRel space lookup policy expression argument expected position rest outputs errors →
      ArgumentChecksRel space lookup policy expression argument expected position (before :: rest)
        (checkedFrames checks ++ outputs)
        ((checkedFailures checks).map (fun actual => mkError expression (.badArgType position expected actual)) ++ errors)

inductive ApplicabilityArgumentsRel (space : Space) (lookup : TypeLookupRel) (policy : Policy) :
    Atom → Nat → List Atom → List Atom → List Frame → List Frame → List Atom → Prop where
  | nil {expression position frames} :
      ApplicabilityArgumentsRel space lookup policy expression position [] [] frames frames []
  | cons {expression position argument arguments expected expecteds before next after errors later} :
      ArgumentChecksRel space lookup policy expression argument expected position before next errors →
      ApplicabilityArgumentsRel space lookup policy expression (position + 1) arguments expecteds next after later →
      ApplicabilityArgumentsRel space lookup policy expression position
        (argument :: arguments) (expected :: expecteds) before after (errors ++ later)

theorem ArgumentChecksRel.source_member
    {space lookup policy expression argument expected position frames outputs errors after}
    (checked : ArgumentChecksRel space lookup policy expression argument expected position frames outputs errors)
    (present : after ∈ outputs) :
    ∃ before ∈ frames, ∃ actual,
      TypeAtRel lookup before.bindings argument expected actual ∧
      TypeMatchRel expected actual before.bindings after.bindings := by
  induction checked with
  | nil => cases present
  | @cons before rest actuals checks outputs errors queried paired remaining ih =>
      rcases List.mem_append.mp present with member | member
      · obtain ⟨actual,member,matched⟩ := TypeCheckRel.source_member paired member
        exact ⟨before,by simp,actual,⟨actuals,queried,member⟩,matched⟩
      · obtain ⟨frame,member,actual,queried,matched⟩ := ih member
        exact ⟨frame,by simp [member],actual,queried,matched⟩

theorem ApplicabilityArgumentsRel.source_member
    {space lookup policy expression position arguments types frames outputs errors after}
    (checked : ApplicabilityArgumentsRel space lookup policy expression position arguments types frames outputs errors)
    (present : after ∈ outputs) :
    ∃ before ∈ frames,
      ArgumentsApplicableRel space (lookup := lookup) arguments types before.bindings after.bindings := by
  induction checked with
  | nil => exact ⟨after,present,.nil _⟩
  | cons head _ ih =>
      obtain ⟨next,member,tail⟩ := ih present
      obtain ⟨before,member,actual,queried,matched⟩ := head.source_member member
      exact ⟨before,member,.cons queried matched tail⟩

theorem ApplicabilityArgumentsRel.length_eq
    {space lookup policy expression position arguments types frames outputs errors}
    (checked : ApplicabilityArgumentsRel space lookup policy expression position arguments types frames outputs errors) :
    arguments.length = types.length := by
  induction checked with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons,ih]

/-- All applicability branches of one arrow, followed by its return check.
This finite source operation does not evaluate the head or any argument. -/
inductive ApplicationChecksRel (space : Space) (lookup : TypeLookupRel) (policy : Policy)
    (expression expected : Atom) (selected : SelectedTypePolicy) (before : Frame) :
    List Frame → List Atom → Prop where
  | wrongArity {operator arguments} :
      expression = .expression (operator :: arguments) →
      arguments.length ≠ selected.argumentTypes.length →
      ApplicationChecksRel space lookup policy expression expected selected before []
        [mkError expression .incorrectNumberOfArguments]
  | checked {operator arguments afterArguments errors returnChecks} :
      expression = .expression (operator :: arguments) →
      ApplicabilityArgumentsRel space lookup policy expression 1 arguments selected.argumentTypes
        [before] afterArguments errors →
      List.Forall₂ (fun frame check => TypeCheckRel policy expected frame selected.returnType check)
        afterArguments returnChecks →
      ApplicationChecksRel space lookup policy expression expected selected before
        (checkedFrames returnChecks)
        (errors ++ (checkedFailures returnChecks).map (fun actual => mkError expression (.badType expected actual)))

theorem ApplicationChecksRel.source_member {space lookup policy expression expected selected before frames errors after}
    (checked : ApplicationChecksRel space lookup policy expression expected selected before frames errors)
    (present : after ∈ frames) :
    ApplicationSuccessRel space (lookup := lookup) expression selected.functionType expected before.bindings after.bindings := by
  cases checked with
  | wrongArity => cases present
  | checked shaped arguments returned =>
      obtain ⟨afterArguments,member,matched⟩ := TypeCheckRel.return_source_member returned present
      obtain ⟨initial,member,applicable⟩ := arguments.source_member member
      obtain rfl := List.mem_singleton.mp member
      exact .mk shaped selected.isFunction applicable matched

inductive InvocationSelection where
  | selected (signature : SelectedTypePolicy) (frames : List Frame)
  | exhausted (errors : List Atom) (tupleEligible : Bool)

/-- Complete ordered signature selection. Every type-query copy is visited
until the first arrow with a nonempty complete applicability batch. Earlier
diagnostics are discarded on success; exhaustion retains their full blocks. -/
inductive InvocationScanRel (space : Space) (lookup : TypeLookupRel) (policy : Policy)
    (expression expected : Atom) (before : Frame) : List Atom → InvocationSelection → Prop where
  | nil : InvocationScanRel space lookup policy expression expected before [] (.exhausted [] false)
  | nonFunction {candidate candidates outcome} :
      (¬∃ domains returned, FunctionTypeRel candidate domains returned) →
      InvocationScanRel space lookup policy expression expected before candidates outcome →
      InvocationScanRel space lookup policy expression expected before (candidate :: candidates)
        (match outcome with
          | .selected signature frames => .selected signature frames
          | .exhausted errors _ => .exhausted errors true)
  | selected {signature : SelectedTypePolicy} {candidates frames errors} :
      ApplicationChecksRel space lookup policy expression expected signature before frames errors →
      frames ≠ [] →
      InvocationScanRel space lookup policy expression expected before (signature.functionType :: candidates)
        (.selected signature frames)
  | rejected {signature : SelectedTypePolicy} {candidates errors outcome} :
      ApplicationChecksRel space lookup policy expression expected signature before [] errors →
      InvocationScanRel space lookup policy expression expected before candidates outcome →
      InvocationScanRel space lookup policy expression expected before (signature.functionType :: candidates)
        (match outcome with
          | .selected signature frames => .selected signature frames
          | .exhausted later tupleEligible => .exhausted (errors ++ later) tupleEligible)

/-- A complete list of non-arrow declarations licenses precisely tuple
fallback, without diagnostics or a selected function activation. -/
theorem InvocationScanRel.nonfunctions_exact
    {space : Space} {lookup : TypeLookupRel} {policy : Policy} {expression expected : Atom}
    {before : Frame} {candidates : List Atom} {outcome : InvocationSelection}
    (source : InvocationScanRel space lookup policy expression expected before candidates outcome)
    (nonfunctions : ∀ candidate ∈ candidates,
      ¬∃ domains returned, FunctionTypeRel candidate domains returned) :
    outcome = .exhausted [] (!candidates.isEmpty) := by
  revert nonfunctions
  induction source with
  | nil => intro _none; rfl
  | @nonFunction candidate candidates outcome _none _rest ih =>
      intro none
      have later := ih (fun value member => none value (List.mem_cons_of_mem _ member))
      rw [later]
      rfl
  | @selected signature candidates frames errors _checked _nonempty =>
      intro none
      exact (none _ List.mem_cons_self ⟨signature.argumentTypes,signature.returnType,signature.isFunction⟩).elim
  | @rejected signature candidates errors outcome _checked _rest _ih =>
      intro none
      exact (none _ List.mem_cons_self ⟨signature.argumentTypes,signature.returnType,signature.isFunction⟩).elim

/-- A selected signature is one actual query occurrence. Rejected earlier
signatures do not create a new signature or replace its type variables. -/
theorem InvocationScanRel.selected_origin
    {space : Space} {lookup : TypeLookupRel} {policy : Policy}
    {expression expected : Atom} {before : Frame} {candidates : List Atom}
    {outcome : InvocationSelection}
    (source : InvocationScanRel space lookup policy expression expected before candidates outcome) :
    ∀ signature frames, outcome = .selected signature frames → signature.functionType ∈ candidates := by
  induction source with
  | nil => intro _ _ same; cases same
  | @nonFunction candidate candidates outcome _ _ ih =>
      intro signature frames same
      cases outcome with
      | selected _ _ => exact List.mem_cons_of_mem _ (ih _ _ same)
      | exhausted _ _ => cases same
  | selected _ _ =>
      intro signature frames same
      cases same
      exact List.mem_cons_self
  | @rejected signature candidates errors outcome _ _ ih =>
      intro selected frames same
      cases outcome with
      | selected _ _ => exact List.mem_cons_of_mem _ (ih _ _ same)
      | exhausted _ _ => cases same

/-- The same scope-aware lookup supplies operator declarations and the
argument checks of their ordered scan. -/
def InvocationSelectionRel (space : Space) (lookup : CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (expression operator expected : Atom)
    (before : Frame) (outcome : InvocationSelection) : Prop :=
  ∃ candidates,
    lookup (invocationTypeScope scope live expression expected before.bindings) space
      before.bindings operator Atom.undefinedType candidates ∧
    InvocationScanRel space
      (lookup (invocationTypeScope scope live expression expected before.bindings) space)
      policy expression expected before candidates outcome

/-- Invocation selection earns freshness of the whole selected arrow and
all its domain/return positions from the actual scoped query. The protected
scope contains the complete call, its pending operands and caller bindings. -/
theorem InvocationSelectionRel.selected_fresh
    {enumeration : TypeEnumeration} {space : Space} {policy : Policy}
    {live : List Atom} {scope : List String} {expression operator expected : Atom}
    {before : Frame} {signature : SelectedTypePolicy} {frames : List Frame}
    (source : InvocationSelectionRel space (enumerationLookup enumeration) policy
      live scope expression operator expected before (.selected signature frames)) :
    let protectedNames := invocationTypeScope scope live expression expected before.bindings
    Spec.Type.Presentation.Freshness.AtomAvoids signature.functionType protectedNames ∧
    Spec.Type.Presentation.Freshness.AtomsAvoid signature.argumentTypes protectedNames ∧
    Spec.Type.Presentation.Freshness.AtomAvoids signature.returnType protectedNames := by
  obtain ⟨candidates,queried,scanned⟩ := source
  have member := scanned.selected_origin signature frames rfl
  have fresh := Spec.Type.Presentation.Freshness.AtomsAvoid.atom
    (scopedEnumerationTypeLookup_fresh queried) member
  exact ⟨fresh,signature.argumentTypes_avoid fresh,signature.returnType_avoids fresh⟩

/-- A complete singleton query forces the empty non-function scan. This
local query law is independent of storage and of the chosen enumeration. -/
theorem InvocationSelectionRel.undefined_exact_of_query
    {space : Space} {lookup : CastLookup} {policy : Policy} {live : List Atom} {scope : List String}
    {expression operator expected : Atom} {before : Frame} {outcome : InvocationSelection}
    (onlyUndefined : ∀ candidates,
      lookup (invocationTypeScope scope live expression expected before.bindings) space
        before.bindings operator Atom.undefinedType candidates → candidates = [Atom.undefinedType])
    (source : InvocationSelectionRel space lookup policy live scope expression operator expected before outcome) :
    outcome = .exhausted [] true := by
  obtain ⟨candidates,queried,scanned⟩ := source
  rw [onlyUndefined candidates queried] at scanned
  have none : ∀ candidate ∈ [Atom.undefinedType], ¬∃ domains returned, FunctionTypeRel candidate domains returned := by
    intro candidate member
    obtain rfl := List.mem_singleton.mp member
    rintro ⟨domains,returned,arrow⟩
    simp [FunctionTypeRel,Atom.undefinedType] at arrow
  exact scanned.nonfunctions_exact none

/-- Every complete literal enumeration has the same singleton-undefined
fallback, even when it orders nontrivial type collections differently. -/
theorem InvocationSelectionRel.undefined_exact_of_enumeration
    {enumeration : TypeEnumeration} {space : Space} {policy : Policy}
    {live : List Atom} {scope : List String} {expression operator expected : Atom}
    {before : Frame} {outcome : InvocationSelection}
    (undefined : TypeOccurrencesRel (space.atoms : Multiset Atom) operator {Atom.undefinedType})
    (source : InvocationSelectionRel space (literalEnumerationLookup enumeration) policy
      live scope expression operator expected before outcome) :
    outcome = .exhausted [] true := by
  apply source.undefined_exact_of_query
  intro candidates queried
  exact enumeration.unique queried ((enumeration.undefined_iff_occurrences space operator).mpr undefined)

/-- The historical list-storage case is one instance of the general query law. -/
theorem InvocationSelectionRel.undefined_exact
    {space : Space} {policy : Policy} {live : List Atom} {scope : List String}
    {expression operator expected : Atom} {before : Frame} {outcome : InvocationSelection}
    (undefined : StorageTypesRel space operator [Atom.undefinedType])
    (source : InvocationSelectionRel space rawLookup policy live scope expression operator expected before outcome) :
    outcome = .exhausted [] true := by
  apply source.undefined_exact_of_query
  intro candidates queried
  exact (undefined.unique queried).symm

abbrev Result := Entry.Value × Frame

def rawResult (result : Result) : ResultPair := (result.1.erase,result.2.bindings)
def sourceResult (result : Result) : FrameResult := (result.1.erase,result.2.source)

def readResult (policy : Policy) (result : Result) : Result :=
  (result.2.read policy result.1,result.2)

def publishResult (policy : Policy) (original : Atom) (result : Result) : Result :=
  (Entry.Value.publish policy.marking original result.2.source result.1,result.2)

@[simp] theorem publishResult_source (policy : Policy) (original : Atom) (result : Result) :
    sourceResult (publishResult policy original result) = sourceResult result := by
  simp [sourceResult,publishResult]

structure CastResultRel (policy : Policy) (lookup : TypeLookupRel)
    (before : Frame) (original : Entry.Value) (expected : Atom)
    (raw : ResultPair) (result : Result) : Prop where
  readout : raw = rawResult result
  renewed : Frame.CastRenewRel policy lookup original.erase expected before result.2
  payload : result.1 = if raw.1 == original.erase then original else Entry.Value.ofAtom raw.1

theorem CastResultRel.change_lookup
    {policy : Policy} {first second : TypeLookupRel} {before : Frame}
    {original : Entry.Value} {expected : Atom} {raw : ResultPair} {result : Result}
    (related : CastResultRel policy first before original expected raw result)
    (queries : ∀ bindings subject demand types, first bindings subject demand types →
      second bindings subject demand types) :
    CastResultRel policy second before original expected raw result :=
  ⟨related.readout, related.renewed.change_lookup queries, related.payload⟩

theorem CastResultRel.model
    {policy : Policy} {lookup : TypeLookupRel} {before : Frame}
    {original : Entry.Value} {expected : Atom} {raw : ResultPair} {result : Result}
    (related : CastResultRel policy lookup before original expected raw result) :
    ∃ valuation : String → Atom,
      Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation raw.2 := by
  rw [related.readout]
  exact result.2.certified.satisfiable

theorem CastResultRel.readouts
    {policy : Policy} {lookup : TypeLookupRel} {before : Frame}
    {original : Entry.Value} {expected : Atom} {raw : ResultSet} {results : List Result}
    (paired : List.Forall₂ (CastResultRel policy lookup before original expected) raw results) :
    results.map rawResult = raw := by
  have mapped : List.Forall₂ Eq raw (results.map rawResult) :=
    List.forall₂_map_right_iff.mpr (paired.imp (fun _ _ evidence => evidence.readout))
  have same : raw = results.map rawResult := by
    simpa only [List.forall₂_eq_eq_eq] using mapped
  exact same.symm

/-- A cast transports the whole original value when its syntax is unchanged.
New diagnostics use fresh syntax, while the reached activation is retained. -/
def castResult (original : Entry.Value) (atom : Atom) (after : Frame) : Result :=
  (if atom == original.erase then original else Entry.Value.ofAtom atom,after)

@[simp] theorem raw_castResult (original : Entry.Value) (atom : Atom) (after : Frame) :
    rawResult (castResult original atom after) = (atom,after.bindings) := by
  unfold rawResult castResult
  split
  · rename_i same
    rw [beq_iff_eq] at same
    exact congrArg (fun value => (value,after.bindings)) same.symm
  · simp only [Entry.Value.erase_ofAtom]

/-- A completed source cast with modelled outputs receives earned contextual
frames and payloads. Failure keeps duplicate type-query occurrences separate. -/
theorem CastResultRel.lift_modelled_batch
    {space : Space} {policy : Policy} {lookup : TypeLookupRel}
    {before : Frame} {original : Entry.Value} {expected : Atom} {raw : ResultSet}
    (source : TypeCastBatchRel space original.erase expected before.bindings raw (lookup := lookup)
      (matching := policy.matching.Rel))
    (models : ∀ result ∈ raw, ∃ valuation : String → Atom,
      Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation result.2) :
    ∃ results, List.Forall₂ (CastResultRel policy lookup before original expected) raw results := by
  cases source with
  | @success _ _ types earlier later actual output queried selected rejected matched =>
      obtain ⟨after,reached,renewed⟩ :=
        Frame.CastRenewRel.of_modelled_source_match (policy := policy) before queried selected rejected matched
          (models (original.erase,output) (by simp))
      have related : CastResultRel policy lookup before original expected
          (original.erase,output) (castResult original original.erase after) :=
        ⟨by simp only [raw_castResult,reached],renewed,rfl⟩
      exact ⟨[castResult original original.erase after],.cons related .nil⟩
  | @failure _ _ types queried rejected =>
      refine ⟨types.map (fun actual => castResult original
        (mkError original.erase (.badType expected actual)) before),?_⟩
      clear queried rejected models
      induction types with
      | nil => exact .nil
      | cons actual types ih =>
          refine .cons ⟨?_,.same _,rfl⟩ ih
          simp only [raw_castResult]

/-- Finite-model existence is exactly the missing admission condition for
transporting a completed raw cast into contextual activation frames. -/
theorem CastResultRel.lift_iff_models
    {space : Space} {policy : Policy} {lookup : TypeLookupRel}
    {before : Frame} {original : Entry.Value} {expected : Atom} {raw : ResultSet}
    (source : TypeCastBatchRel space original.erase expected before.bindings raw (lookup := lookup)
      (matching := policy.matching.Rel)) :
    (∃ results, List.Forall₂ (CastResultRel policy lookup before original expected) raw results) ↔
      (∀ result ∈ raw, ∃ valuation : String → Atom,
        Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation result.2) := by
  constructor
  · clear source
    rintro ⟨results,paired⟩
    induction paired with
    | nil => intro result present; cases present
    | cons related paired ih =>
        intro item present
        rcases List.mem_cons.mp present with rfl | present
        · exact related.model
        · exact ih item present
  · exact CastResultRel.lift_modelled_batch source

/-- Finite matching earns every reached activation without an additional
model hypothesis supplied by an evaluator or caller. Candidate rejection
happens inside the source scan, so later admissible types remain available. -/
theorem CastResultRel.lift_finite_batch
    {space : Space} {policy : Policy} {lookup : TypeLookupRel}
    {before : Frame} {original : Entry.Value} {expected : Atom} {raw : ResultSet}
    (finite : policy.matching = .finite)
    (source : TypeCastBatchRel space original.erase expected before.bindings raw (lookup := lookup)
      (matching := policy.matching.Rel)) :
    ∃ results, List.Forall₂ (CastResultRel policy lookup before original expected) raw results := by
  apply CastResultRel.lift_modelled_batch source
  cases source with
  | success queried selected rejected matched =>
      intro result present
      obtain rfl := List.mem_singleton.mp present
      rw [finite] at matched
      exact matched.2
  | failure queried rejected =>
      intro result present
      obtain ⟨actual,member,rfl⟩ := List.mem_map.mp present
      exact before.certified.satisfiable

/-- Active function syntax requires its instruction-body semantics. Held
function-shaped data is reusable under the reuse policy. -/
def FunctionPending (policy : Policy) (value : Entry.Value) : Prop :=
  Minimal.IsFunction value.erase ∧ (policy.reentry = .reinterpret ∨ value.status = .active)

theorem held_function_not_pending {policy : Policy} (children : List Entry.Value)
    (reuses : policy.reentry = .reuse) :
    ¬FunctionPending policy (.expression .held children) := by
  simp [FunctionPending,reuses,Entry.Value.status]

def tupleSingleton (result : Result) : Result :=
  if isEmptyOrError result.1.erase then result else
    (.expression .active [result.1],result.2)

def tuplePrepend (head : Entry.Value) (result : Result) : Result :=
  if isEmptyOrError result.1.erase then result else
    (.expression .active (head :: match result.1 with
      | .expression _ values => values
      | value => [value]),result.2)

@[simp] theorem tuplePrepend_frame (head : Entry.Value) (result : Result) :
    (tuplePrepend head result).2 = result.2 := by
  unfold tuplePrepend
  split <;> rfl

/-- Producer materialization transports the supplied annotated value through
its reached frame. Raw results retain their original occurrence metadata. -/
def nativeValue (policy : Policy) (dispatch : GroundedDispatch) (operator : Atom) (arguments : List Atom)
    (frame : Frame) (value : Entry.Value) : Entry.Value :=
  match dispatch.bindingMode operator arguments with
  | .raw => value
  | .materialized => frame.read policy value

theorem nativeValue_source (policy : Policy) (dispatch : GroundedDispatch) (operator : Atom)
    (arguments : List Atom) (frame : Frame) (value : Entry.Value) :
    NativeEmissionRel dispatch operator arguments frame.source value.erase
      (nativeValue policy dispatch operator arguments frame value).erase := by
  cases mode : dispatch.bindingMode operator arguments with
  | raw => simpa only [nativeValue,mode] using NativeEmissionRel.raw (raw := value.erase) mode
  | materialized =>
      simpa only [nativeValue,mode] using NativeEmissionRel.materialized mode (frame.read_source policy value)

/-- Every physical native result is kept after its finite binding conjunction
or rejected by a complete finite-model inconsistency test. Equivalent copies stay separate. -/
inductive NativeRowsRel (policy : Policy) (dispatch : GroundedDispatch) (operator : Atom)
    (arguments : List Atom) (before : Frame) : List (Entry.Value × Bindings) → List Result → Prop where
  | nil : NativeRowsRel policy dispatch operator arguments before [] []
  | cons {head heads after rest} :
      Frame.NativeRenewRel policy head.2 before after →
      NativeRowsRel policy dispatch operator arguments before heads rest →
      NativeRowsRel policy dispatch operator arguments before (head :: heads)
        ((nativeValue policy dispatch operator arguments after head.1,after) :: rest)
  | rejected {head heads rest} :
      (¬∃ output, Spec.Bindings.ScopeObservation.LogicalMergeRel head.2 before.bindings output) →
      NativeRowsRel policy dispatch operator arguments before heads rest →
      NativeRowsRel policy dispatch operator arguments before (head :: heads) rest

/-- Re-presenting the caller's constraint record preserves the entire batch
of already returned producer rows. Successful occurrences retain their exact
annotated values and reached frames; inconsistency rejects the same rows.
This does not impose a representation contract on the host callback itself. -/
theorem NativeRowsRel.represent_before_iff
    {policy dispatch operator arguments before rows results} {bindings : Bindings}
    (agreement : BindingSourceAgreement before.bindings bindings) :
    NativeRowsRel policy dispatch operator arguments
        (before.represent bindings agreement) rows results ↔
      NativeRowsRel policy dispatch operator arguments before rows results := by
  constructor
  · intro source
    induction source with
    | nil => exact .nil
    | cons renewed _ ih =>
        exact .cons ((Frame.NativeRenewRel.represent_before_iff agreement).mp renewed) ih
    | rejected impossible _ ih =>
        refine .rejected (fun ⟨output,merged⟩ => impossible ⟨output,?_⟩) ih
        exact (Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
          (BindingSourceAgreement.refl _) agreement).mp merged
  · intro source
    induction source with
    | nil => exact .nil
    | cons renewed _ ih =>
        exact .cons ((Frame.NativeRenewRel.represent_before_iff agreement).mpr renewed) ih
    | rejected impossible _ ih =>
        refine .rejected (fun ⟨output,merged⟩ => impossible ⟨output,?_⟩) ih
        exact (Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
          (BindingSourceAgreement.refl _) agreement).mpr merged

theorem NativeRowsRel.total (policy : Policy) (dispatch : GroundedDispatch) (operator : Atom)
    (arguments : List Atom) (before : Frame) (rows : List (Entry.Value × Bindings)) :
    ∃ results, NativeRowsRel policy dispatch operator arguments before rows results := by
  classical
  induction rows with
  | nil => exact ⟨[],.nil⟩
  | cons head heads ih =>
      obtain ⟨rest,continued⟩ := ih
      by_cases possible : ∃ output, Spec.Bindings.ScopeObservation.LogicalMergeRel head.2 before.bindings output
      · obtain ⟨output,merged⟩ := possible
        obtain ⟨after,_same,renewed⟩ := Frame.NativeRenewRel.of_logical_merge (policy := policy) before merged
        exact ⟨_,.cons renewed continued⟩
      · exact ⟨rest,.rejected possible continued⟩

theorem NativeRowsRel.length_le {policy dispatch operator arguments before rows results}
    (source : NativeRowsRel policy dispatch operator arguments before rows results) :
    results.length ≤ rows.length := by
  induction source with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => simpa only [List.length_cons] using Nat.succ_le_succ ih
  | rejected _ _ ih => exact ih.trans (Nat.le_succ _)

/-- If every native binding is compatible, every physical producer copy
survives once. This counts occurrences even when their values are equal. -/
theorem NativeRowsRel.length_eq_of_compatible {policy dispatch operator arguments before rows results}
    (source : NativeRowsRel policy dispatch operator arguments before rows results)
    (compatible : ∀ row ∈ rows,
      ∃ output, Spec.Bindings.ScopeObservation.LogicalMergeRel row.2 before.bindings output) :
    results.length = rows.length := by
  induction source with
  | nil => rfl
  | cons renewed _ ih =>
      simp only [List.length_cons]
      exact congrArg Nat.succ (ih (fun row present => compatible row (List.mem_cons_of_mem _ present)))
  | rejected impossible _ _ => exact False.elim (impossible (compatible _ List.mem_cons_self))

/-- Only successful producer rows require a continuation. A refusal restores
the original full call or returns the raw minimal refusal sentinel. -/
inductive NativeReplyPlan where
  | done (results : List Result)
  | resume (rows : List Result)

inductive NativeOutcomeRel (policy : Policy) (dispatch : GroundedDispatch) (operator : Atom)
    (arguments : List Atom) (original : Entry.Value) (expected : Option Atom) (frame : Frame) :
    GroundedResult Entry.Value → NativeReplyPlan → Prop where
  | success {head tail rows} :
      NativeRowsRel policy dispatch operator arguments frame (head :: tail) rows →
      NativeOutcomeRel policy dispatch operator arguments original expected frame (.ok (head :: tail)) (.resume rows)
  | empty : NativeOutcomeRel policy dispatch operator arguments original expected frame (.ok [])
      (.done [(Entry.Value.ofAtom Atom.empty,frame)])
  | runtimeError (message) :
      NativeOutcomeRel policy dispatch operator arguments original expected frame (.runtimeError message)
        (.done [(Entry.Value.ofAtom (Atom.error original.erase (.symbol message)),frame)])
  | noReduce : NativeOutcomeRel policy dispatch operator arguments original expected frame .noReduce
      (.done [(if expected.isSome then original else Entry.Value.ofAtom Atom.notReducible,frame)])
  | incorrectArgument : NativeOutcomeRel policy dispatch operator arguments original expected frame .incorrectArgument
      (.done [(if expected.isSome then original else Entry.Value.ofAtom Atom.notReducible,frame)])

theorem NativeOutcomeRel.total (policy : Policy) (dispatch : GroundedDispatch) (operator : Atom)
    (arguments : List Atom) (original : Entry.Value) (expected : Option Atom) (frame : Frame)
    (outcome : GroundedResult Entry.Value) :
    ∃ plan, NativeOutcomeRel policy dispatch operator arguments original expected frame outcome plan := by
  cases outcome with
  | ok rows =>
      cases rows with
      | nil => exact ⟨_,.empty⟩
      | cons head tail =>
          obtain ⟨results,prepared⟩ := NativeRowsRel.total policy dispatch operator arguments frame (head :: tail)
          exact ⟨_,.success prepared⟩
  | runtimeError message => exact ⟨_,.runtimeError message⟩
  | noReduce => exact ⟨_,.noReduce⟩
  | incorrectArgument => exact ⟨_,.incorrectArgument⟩

/-- Producer-completed values use a pure return/type gate, independent of
reentry policy. Function-shaped completed data is never activated here. -/
inductive NativeCompletedReturnRel (space : Space) (lookup : TypeLookupRel) (policy : Policy)
    (value : Entry.Value) (expected : Atom) (frame : Frame) : List Result → Prop where
  | keep : CompletedNativeKeepRel value.erase expected →
      NativeCompletedReturnRel space lookup policy value expected frame [(value,frame)]
  | cast {raw results} :
      ¬CompletedNativeKeepRel value.erase expected →
      TypeCastBatchRel space value.erase expected frame.bindings raw
        (lookup := lookup) (matching := policy.matching.Rel) →
      List.Forall₂ (CastResultRel policy lookup frame value expected) raw results →
      NativeCompletedReturnRel space lookup policy value expected frame results

abbrev ArgumentRequest := Entry.Value × Atom

/-- Pending source operands and declared demands both remain live. -/
def argumentScope (requests : List ArgumentRequest) : List Atom :=
  requests.flatMap fun request => [request.1.erase,request.2]

/-- Only an error changed by argument evaluation stops this path. A literal
unchanged error remains argument data, as in the published argument rule. -/
def ArgumentStopped (original : Entry.Value) (result : Result) : Prop :=
  IsEmptyOrErrorRel result.1.erase ∧ result.1.erase ≠ original.erase

def argumentPrepend (head : Entry.Value) (result : Result) : Result :=
  match result.1.unpackArguments with
  | some values => (Entry.Value.argumentPacket (head :: values),result.2)
  | none => result

def functionAssemble (head : Entry.Value) (result : Result) : Result :=
  match result.1.unpackArguments with
  | some arguments => (.expression .active (head :: arguments),result.2)
  | none => result

def invocationReturnType (signature : SelectedTypePolicy) : Atom :=
  if signature.returnType = Atom.expressionType then Atom.undefinedType else signature.returnType

def diagnosticResults (errors : List Atom) (frame : Frame) : List Result :=
  errors.map fun error => (Entry.Value.ofAtom error,frame)

@[simp] theorem argumentPrepend_packet (head : Entry.Value) (values : List Entry.Value) (frame : Frame) :
    argumentPrepend head (Entry.Value.argumentPacket values,frame) =
      (Entry.Value.argumentPacket (head :: values),frame) := by
  simp [argumentPrepend]

theorem argumentPrepend_error (head : Entry.Value) (result : Result)
    (failed : IsEmptyOrErrorRel result.1.erase) : argumentPrepend head result = result := by
  simp only [argumentPrepend,Entry.Value.unpackArguments_error failed]

@[simp] theorem publishResult_erase (policy : Policy) (original : Atom) (result : Result) :
    (publishResult policy original result).1.erase = result.1.erase := by
  simp [publishResult]

/-- Minimal instructions license these distinct uses of a completed child.
The saved caller remains raw diagnostic syntax, independently of readout. -/
inductive Boundary where
  | chain (name : String) (template : Entry.Value)
  | body
  | functionDone
  | producer
  | returned (original : Entry.Value) (expected : Atom)
  | native (original : Entry.Value) (expected : Option Atom) (provenance : NativeValueProvenance)

/-- Chain substitutes its local operand without writing a caller binding.
The substituted value retains its whole contextual representation. -/
def substituteBinder (policy : Policy) (name : String) (value template : Entry.Value) : Entry.Value :=
  Entry.Value.substitute policy.rebuilding (fun key => if key = name then value else .var key) template

theorem substituteBinder_erase (policy : Policy) (name : String) (value template : Entry.Value) :
    (substituteBinder policy name value template).erase =
      Minimal.substituteName name value.erase template.erase := by
  induction template using Entry.Value.rec (motive_2 := fun values =>
      (values.map (Entry.Value.substitute policy.rebuilding (fun key => if key = name then value else .var key))).map
          Entry.Value.erase =
        (values.map Entry.Value.erase).map (Minimal.substituteName name value.erase)) with
  | symbol => simp only [substituteBinder,Entry.Value.substitute,Entry.Value.erase,Minimal.substituteName]
  | var key =>
      by_cases same : key = name <;> simp [substituteBinder,Entry.Value.substitute,Entry.Value.erase,Minimal.substituteName,same]
  | grounded => simp only [substituteBinder,Entry.Value.substitute,Entry.Value.erase,Minimal.substituteName]
  | expression readiness children ih =>
      simpa only [substituteBinder,Entry.Value.substitute,Entry.Value.erase,Minimal.substituteName] using
        congrArg Atom.expression ih
  | nil => rfl
  | cons _ _ first rest => simpa only [List.map_cons,substituteBinder] using congrArg₂ List.cons first rest

@[simp] theorem substituteBinder_return (policy : Policy) (name : String) (value : Entry.Value) :
    substituteBinder policy name value (.expression .active [.symbol "return",.var name]) =
      .expression .active [.symbol "return",value] := by
  cases rebuild : policy.rebuilding <;>
    simp [substituteBinder,Entry.Value.substitute,Entry.Value.rebuildStatus,rebuild]

@[simp] theorem substituteBinder_superpose (policy : Policy) (name : String) (value : Entry.Value) :
    substituteBinder policy name value (.expression .active [.symbol "superpose-bind",.var name]) =
      .expression .active [.symbol "superpose-bind",value] := by
  cases rebuild : policy.rebuilding <;>
    simp [substituteBinder,Entry.Value.substitute,Entry.Value.rebuildStatus,rebuild]

/-- Collect a completed minimal computation and resume its captured rows. -/
def collectionReplay (operand : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "chain",.expression .active [.symbol "collapse-bind",operand],
    .var "collected",.expression .active [.symbol "superpose-bind",.var "collected"]]

mutual
/-- A full boundary first reads the reached environment. Child publication
is complete before the caller resumes. Only completed interpreted expressions
enter the marking boundary. -/
inductive AtomRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → Entry.Value → Atom → Frame → List Result →
      (policy : Policy := Policy.unmarked) → Prop where
  | delivered {live scope value expected frame policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .deliver →
      AtomRel space dispatch lookup live scope value expected frame
        [(frame.read policy value,frame)] (policy := policy)
  | cast {live scope value expected frame raw results policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .cast →
      TypeCastBatchRel space (frame.read policy value).erase expected frame.bindings raw
        (lookup := lookup (invocationTypeScope scope live
          (frame.read policy value).erase expected frame.bindings) space)
        (matching := policy.matching.Rel) →
      List.Forall₂ (CastResultRel policy
        (lookup (invocationTypeScope scope live (frame.read policy value).erase expected frame.bindings) space)
        frame (frame.read policy value) expected) raw results →
      AtomRel space dispatch lookup live scope value expected frame results (policy := policy)
  | tuple {live scope value expected frame readiness operator arguments rows raw selected policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .interpret →
      frame.read policy value = .expression readiness (operator :: arguments) →
      TypeOccurrencesRel (space.atoms : Multiset Atom) operator.erase {Atom.undefinedType} →
      TupleRel space dispatch lookup (expected :: live) scope (operator :: arguments) frame rows
        (policy := policy) →
      CallsRel space dispatch lookup live scope expected rows raw (policy := policy) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (readResult policy)) selected →
      AtomRel space dispatch lookup live scope value expected frame
        (selected.map (publishResult policy (frame.read policy value).erase)) (policy := policy)
  | function {live scope value expected frame readiness operator arguments signature frames raw selected policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .interpret →
      frame.read policy value = .expression readiness (operator :: arguments) →
      InvocationSelectionRel space lookup policy live scope (frame.read policy value).erase operator.erase
        expected frame (.selected signature frames) →
      InvocationsRel space dispatch lookup live scope expected signature operator arguments frames raw (policy := policy) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (readResult policy)) selected →
      AtomRel space dispatch lookup live scope value expected frame
        (selected.map (publishResult policy (frame.read policy value).erase)) (policy := policy)
  | fallback {live scope value expected frame readiness operator arguments errors rows raw selected policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .interpret →
      frame.read policy value = .expression readiness (operator :: arguments) →
      InvocationSelectionRel space lookup policy live scope (frame.read policy value).erase operator.erase
        expected frame (.exhausted errors true) →
      TupleRel space dispatch lookup (expected :: live) scope (operator :: arguments) frame rows (policy := policy) →
      CallsRel space dispatch lookup live scope expected rows raw (policy := policy) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        ((raw ++ diagnosticResults errors frame).map (readResult policy)) selected →
      AtomRel space dispatch lookup live scope value expected frame
        (selected.map (publishResult policy (frame.read policy value).erase)) (policy := policy)
  | selectionFailed {live scope value expected frame readiness operator arguments errors selected policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .interpret →
      frame.read policy value = .expression readiness (operator :: arguments) →
      InvocationSelectionRel space lookup policy live scope (frame.read policy value).erase operator.erase
        expected frame (.exhausted errors false) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        ((diagnosticResults errors frame).map (readResult policy)) selected →
      AtomRel space dispatch lookup live scope value expected frame
        (selected.map (publishResult policy (frame.read policy value).erase)) (policy := policy)

/-- Tuple control retains child values rather than reconstructing them from
their erased atoms. Each head occurrence receives its own tail completion. -/
inductive TupleRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → List Entry.Value → Frame → List Result →
      (policy : Policy := Policy.unmarked) → Prop where
  | nil {live scope frame policy} :
      TupleRel space dispatch lookup live scope [] frame
        [(.expression .active [],frame)] (policy := policy)
  | singleton {live scope value frame heads policy} :
      AtomRel space dispatch lookup live scope value Atom.undefinedType frame heads (policy := policy) →
      TupleRel space dispatch lookup live scope [value] frame
        (heads.map tupleSingleton) (policy := policy)
  | cons {live scope head second remaining frame heads results policy} :
      AtomRel space dispatch lookup
        (.expression ((second :: remaining).map Entry.Value.erase) :: live) scope
        head Atom.undefinedType frame heads (policy := policy) →
      TupleBranchesRel space dispatch lookup live scope (second :: remaining) heads results (policy := policy) →
      TupleRel space dispatch lookup live scope (head :: second :: remaining) frame results (policy := policy)

inductive TupleBranchesRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → List Entry.Value → List Result → List Result →
      (policy : Policy := Policy.unmarked) → Prop where
  | nil {live scope tail policy} :
      TupleBranchesRel space dispatch lookup live scope tail [] [] (policy := policy)
  | stopped {live scope tail head heads rest policy} :
      IsEmptyOrErrorRel head.1.erase →
      TupleBranchesRel space dispatch lookup live scope tail heads rest (policy := policy) →
      TupleBranchesRel space dispatch lookup live scope tail (head :: heads) (head :: rest) (policy := policy)
  | continuing {live scope tail head heads children rest policy} :
      ¬IsEmptyOrErrorRel head.1.erase →
      TupleRel space dispatch lookup (head.1.erase :: live) scope tail head.2 children (policy := policy) →
      TupleBranchesRel space dispatch lookup live scope tail heads rest (policy := policy) →
      TupleBranchesRel space dispatch lookup live scope tail (head :: heads)
        (children.map (tuplePrepend head.1) ++ rest) (policy := policy)

/-- Declared argument demands are paired with their source values. Every
child receives the frame reached by the preceding selected occurrence. -/
inductive ArgumentsRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → List ArgumentRequest → Frame → List Result →
      (policy : Policy := Policy.unmarked) → Prop where
  | nil {live scope frame policy} :
      ArgumentsRel space dispatch lookup live scope [] frame
        [(Entry.Value.argumentPacket [],frame)] (policy := policy)
  | cons {live scope request requests frame heads results policy} :
      AtomRel space dispatch lookup (argumentScope requests ++ live) scope
        request.1 request.2 frame heads (policy := policy) →
      ArgumentBranchesRel space dispatch lookup live scope request.1 requests heads results (policy := policy) →
      ArgumentsRel space dispatch lookup live scope (request :: requests) frame results (policy := policy)

inductive ArgumentBranchesRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → Entry.Value → List ArgumentRequest → List Result → List Result →
      (policy : Policy := Policy.unmarked) → Prop where
  | nil {live scope original requests policy} :
      ArgumentBranchesRel space dispatch lookup live scope original requests [] [] (policy := policy)
  | stopped {live scope original requests head heads rest policy} :
      ArgumentStopped original head →
      ArgumentBranchesRel space dispatch lookup live scope original requests heads rest (policy := policy) →
      ArgumentBranchesRel space dispatch lookup live scope original requests (head :: heads)
        (head :: rest) (policy := policy)
  | continuing {live scope original requests head heads children rest policy} :
      ¬ArgumentStopped original head →
      ArgumentsRel space dispatch lookup (head.1.erase :: live) scope requests head.2 children (policy := policy) →
      ArgumentBranchesRel space dispatch lookup live scope original requests heads rest (policy := policy) →
      ArgumentBranchesRel space dispatch lookup live scope original requests (head :: heads)
        (children.map (argumentPrepend head.1) ++ rest) (policy := policy)

/-- A selected function evaluates its head at the selected arrow, then its
arguments at their declared demands. Arity is checked before zipping. -/
inductive FunctionRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → Atom → SelectedTypePolicy → Entry.Value → List Entry.Value →
      Frame → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | evaluated {live scope expected signature operator arguments frame heads results policy} :
      arguments.length = signature.argumentTypes.length →
      AtomRel space dispatch lookup (signature.functionType :: arguments.map Entry.Value.erase ++ live)
        (scope ++ expectedApplicationScope (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
        operator signature.functionType frame heads (policy := policy) →
      FunctionBranchesRel space dispatch lookup live scope
        (arguments.zip signature.argumentTypes) heads results (policy := policy) →
      FunctionRel space dispatch lookup live scope expected signature operator arguments frame results (policy := policy)

inductive FunctionBranchesRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → List ArgumentRequest → List Result → List Result →
      (policy : Policy := Policy.unmarked) → Prop where
  | nil {live scope requests policy} :
      FunctionBranchesRel space dispatch lookup live scope requests [] [] (policy := policy)
  | stopped {live scope requests head heads rest policy} :
      IsEmptyOrErrorRel head.1.erase →
      FunctionBranchesRel space dispatch lookup live scope requests heads rest (policy := policy) →
      FunctionBranchesRel space dispatch lookup live scope requests (head :: heads) (head :: rest) (policy := policy)
  | continuing {live scope requests head heads children rest policy} :
      ¬IsEmptyOrErrorRel head.1.erase →
      ArgumentsRel space dispatch lookup (head.1.erase :: live) scope requests head.2 children (policy := policy) →
      FunctionBranchesRel space dispatch lookup live scope requests heads rest (policy := policy) →
      FunctionBranchesRel space dispatch lookup live scope requests (head :: heads)
        (children.map (functionAssemble head.1) ++ rest) (policy := policy)

/-- Every applicability occurrence completes the head, arguments and return
gate before the next applicability occurrence begins. -/
inductive InvocationsRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → Atom → SelectedTypePolicy → Entry.Value → List Entry.Value →
      List Frame → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | nil {live scope expected signature operator arguments policy} :
      InvocationsRel space dispatch lookup live scope expected signature operator arguments [] [] (policy := policy)
  | cons {live scope expected signature operator arguments frame frames interpreted called rest policy} :
      FunctionRel space dispatch lookup (invocationReturnType signature :: live) scope expected signature operator
        arguments frame interpreted (policy := policy) →
      CallsRel space dispatch lookup live scope (invocationReturnType signature) interpreted called (policy := policy) →
      InvocationsRel space dispatch lookup live scope expected signature operator arguments frames rest (policy := policy) →
      InvocationsRel space dispatch lookup live scope expected signature operator arguments (frame :: frames)
        (called ++ rest) (policy := policy)

/-- Every returned occurrence resumes its caller before the next occurrence. -/
inductive CallsRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → Atom → List Result → List Result →
      (policy : Policy := Policy.unmarked) → Prop where
  | nil {live scope expected policy} :
      CallsRel space dispatch lookup live scope expected [] [] (policy := policy)
  | cons {live scope expected head heads children rest policy} :
      CallRel space dispatch lookup live scope head.1 expected head.2 children (policy := policy) →
      CallsRel space dispatch lookup live scope expected heads rest (policy := policy) →
      CallsRel space dispatch lookup live scope expected (head :: heads) (children ++ rest) (policy := policy)

inductive CallRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → Entry.Value → Atom → Frame → List Result →
      (policy : Policy := Policy.unmarked) → Prop where
  | error {live scope value expected frame policy} :
      IsErrorRel value.erase →
      CallRel space dispatch lookup live scope value expected frame [(value,frame)] (policy := policy)
  | embedded {space dispatch lookup live scope value expected frame raw results policy} :
      ¬IsErrorRel value.erase → ¬Minimal.HostCall dispatch value.erase →
      Minimal.embeddedInstruction value.erase = true →
      InvocationRel space dispatch lookup (expected :: live) scope none value frame raw (policy := policy) →
      BoundaryBatchRel space dispatch lookup live scope none (.returned value expected) raw results (policy := policy) →
      CallRel space dispatch lookup live scope value expected frame results (policy := policy)
  | absent {live scope value expected frame policy} :
      ¬IsErrorRel value.erase → NonGroundedCallRel dispatch value.erase →
      EquationFrontierRel space (expected :: live) value.erase frame.bindings [] →
      CallRel space dispatch lookup live scope value expected frame [(value,frame)] (policy := policy)
  | equations {live scope value expected frame works results policy} :
      ¬IsErrorRel value.erase → NonGroundedCallRel dispatch value.erase →
      EquationFrontierRel space (expected :: live) value.erase frame.bindings works →
      works ≠ [] →
      EquationBodiesRel space dispatch lookup live scope value expected frame works results (policy := policy) →
      CallRel space dispatch lookup live scope value expected frame results (policy := policy)

/-- Equation instantiation consumes the contextual unifier's reached frame.
The body is fresh syntax; assigned subvalues retain their evaluation status. -/
inductive EquationBodiesRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → Entry.Value → Atom → Frame →
      List EquationWork → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | nil {live scope original expected frame policy} :
      EquationBodiesRel space dispatch lookup live scope original expected frame [] [] (policy := policy)
  | cons {live scope original expected frame work works output children rest policy} :
      output.bindings = work.bindings →
      Entry.Value.UnifyRel policy.rebuilding frame.environment original (Entry.Value.ofAtom work.pattern)
        output.environment →
      BoundaryRel space dispatch lookup (expected :: live) scope (some original.erase) .producer
        (output.read policy (Entry.Value.ofAtom work.body)) output produced (policy := policy) →
      BoundaryBatchRel space dispatch lookup live scope none (.returned original expected) produced children (policy := policy) →
      EquationBodiesRel space dispatch lookup live scope original expected frame works rest (policy := policy) →
      EquationBodiesRel space dispatch lookup live scope original expected frame (work :: works)
        (children ++ rest) (policy := policy)

/-- A refusal restores the saved call. Other producer values enter another
completed phase, where the reentry policy decides whether they run again. -/
inductive ReturnRel : Space → GroundedDispatch → CastLookup →
    List Atom → List String → Entry.Value → Atom → Entry.Value → Frame →
      List Result → (policy : Policy := Policy.unmarked) → Prop where
  | notReducible {live scope original expected value frame policy} :
      value.erase = Atom.notReducible →
      ReturnRel space dispatch lookup live scope original expected value frame [(original,frame)] (policy := policy)
  | stopped {live scope original expected value frame policy} :
      IsEmptyOrErrorRel value.erase →
      ReturnRel space dispatch lookup live scope original expected value frame [(value,frame)] (policy := policy)
  | evaluate {live scope original expected value frame results policy} :
      value.erase ≠ Atom.notReducible → ¬IsEmptyOrErrorRel value.erase →
      AtomRel space dispatch lookup live scope value expected frame results (policy := policy) →
      ReturnRel space dispatch lookup live scope original expected value frame results (policy := policy)

/-- Completed minimal execution returns ordinary primitive outputs raw.
Only chain schedules its substituted template. Function body iteration is
an independent boundary, rather than implicit evaluation of returned data. -/
inductive MinimalRel : Space → GroundedDispatch → CastLookup → List Atom → List String → Option Atom →
    Entry.Value → Frame → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | data {space dispatch lookup live scope caller value frame policy} :
      Minimal.embeddedInstruction value.erase = false →
      MinimalRel space dispatch lookup live scope caller value frame [(value,frame)] (policy := policy)
  | eval {space dispatch lookup live scope caller readiness operand frame results policy} :
      InvocationRel space dispatch lookup live scope caller (frame.read policy operand) frame results (policy := policy) →
      MinimalRel space dispatch lookup live scope caller (.expression readiness [.symbol "eval",operand]) frame results (policy := policy)
  | evalc {space context dispatch lookup live scope caller readiness operand frame results services enumeration policy} :
      dispatch.minimal = some ⟨services,enumeration⟩ →
      InvocationRel context dispatch lookup live scope caller (frame.read policy operand) frame results (policy := policy) →
      MinimalRel space dispatch lookup live scope caller
        (.expression readiness [.symbol "evalc",operand,.grounded (services.contextPayload context)]) frame results (policy := policy)
  | chain {space dispatch lookup live scope caller readiness operand name template frame selected results policy} :
      MinimalRel space dispatch lookup
        ((.expression [.symbol "chain",operand.erase,.var name,template.erase]) :: live) scope
        (some (.expression [.symbol "chain",operand.erase,.var name,template.erase])) operand frame selected (policy := policy) →
      BoundaryBatchRel space dispatch lookup live scope caller (.chain name template) selected results (policy := policy) →
      MinimalRel space dispatch lookup live scope caller
        (.expression readiness [.symbol "chain",operand,.var name,template]) frame results (policy := policy)
  | unifyYes {space dispatch lookup live scope caller readiness target pattern yes no frame output policy} :
      UnifyCandidateRel target.erase pattern.erase frame.bindings output.bindings →
      Entry.Value.UnifyRel policy.rebuilding frame.environment target pattern output.environment →
      MinimalRel space dispatch lookup live scope caller
        (.expression readiness [.symbol "unify",target,pattern,yes,no]) frame
        [(output.read policy yes,output)] (policy := policy)
  | unifyNo {space dispatch lookup live scope caller readiness target pattern yes no frame policy} :
      UnifyNoMatchRel target.erase pattern.erase frame.bindings →
      MinimalRel space dispatch lookup live scope caller
        (.expression readiness [.symbol "unify",target,pattern,yes,no]) frame [(no,frame)] (policy := policy)
  | unifyBadArity {space dispatch lookup live scope caller readiness tail frame policy} :
      tail.length ≠ 4 →
      MinimalRel space dispatch lookup live scope caller (.expression readiness (.symbol "unify" :: tail)) frame
        [(Entry.Value.ofAtom (mkErrorMessage (.expression (.symbol "unify" :: tail.map Entry.Value.erase))
          (dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail.map Entry.Value.erase)))),frame)] (policy := policy)
  | consAtom {space dispatch lookup live scope caller readiness tailReadiness head tail frame policy} :
      MinimalRel space dispatch lookup live scope caller
        (.expression readiness [.symbol "cons-atom",head,.expression tailReadiness tail]) frame
        [(.expression .active (head :: tail),frame)] (policy := policy)
  | deconsAtom {space dispatch lookup live scope caller readiness valueReadiness head tail frame policy} :
      MinimalRel space dispatch lookup live scope caller
        (.expression readiness [.symbol "decons-atom",.expression valueReadiness (head :: tail)]) frame
        [(.expression .active [head,.expression .active tail],frame)] (policy := policy)
  | function {space dispatch lookup live scope caller readiness body bodyReadiness children frame raw results policy} :
      body = .expression bodyReadiness children →
      BodyRel space dispatch lookup ((.expression [.symbol "function",body.erase]) :: live) scope
        (some (.expression [.symbol "function",body.erase])) body frame raw (policy := policy) →
      BoundaryBatchRel space dispatch lookup live scope caller .functionDone raw results (policy := policy) →
      MinimalRel space dispatch lookup live scope caller (.expression readiness [.symbol "function",body]) frame results (policy := policy)
  | metta {space context dispatch lookup live scope caller readiness operand expected frame results services enumeration policy} :
      dispatch.minimal = some ⟨services,enumeration⟩ →
      AtomRel context dispatch lookup live scope operand expected.erase frame results (policy := policy) →
      MinimalRel space dispatch lookup live scope caller
        (.expression readiness [.symbol "metta",operand,expected,.grounded (services.contextPayload context)]) frame results (policy := policy)
  | contextSpace {space dispatch lookup live scope caller readiness frame services enumeration policy} :
      dispatch.minimal = some ⟨services,enumeration⟩ →
      MinimalRel space dispatch lookup live scope caller (.expression readiness [.symbol "context-space"]) frame
        [(.grounded (services.contextPayload space),frame)] (policy := policy)

inductive BodyRel : Space → GroundedDispatch → CastLookup → List Atom → List String → Option Atom →
    Entry.Value → Frame → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | run {space dispatch lookup live scope caller value frame raw results policy} :
      MinimalRel space dispatch lookup live scope caller value frame raw (policy := policy) →
      BoundaryBatchRel space dispatch lookup live scope caller .body raw results (policy := policy) →
      BodyRel space dispatch lookup live scope caller value frame results (policy := policy)

/-- One explicit eval invokes equations or entered minimal work, completing
an authored function wrapper once. Ordinary equation data is left raw. -/
inductive InvocationRel : Space → GroundedDispatch → CastLookup → List Atom → List String → Option Atom →
    Entry.Value → Frame → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | embedded {space dispatch lookup live scope caller value frame results policy} :
      ¬Minimal.HostCall dispatch value.erase → Minimal.embeddedInstruction value.erase = true →
      MinimalRel space dispatch lookup live scope caller value frame results (policy := policy) →
      InvocationRel space dispatch lookup live scope caller value frame results (policy := policy)
  | absent {space dispatch lookup live scope caller value frame policy} :
      NonGroundedCallRel dispatch value.erase →
      EquationFrontierRel space live value.erase frame.bindings [] →
      InvocationRel space dispatch lookup live scope caller value frame [(.symbol "NotReducible",frame)] (policy := policy)
  | equations {space dispatch lookup live scope caller value frame works results policy} :
      NonGroundedCallRel dispatch value.erase →
      EquationFrontierRel space live value.erase frame.bindings works → works ≠ [] →
      InvocationEquationsRel space dispatch lookup live scope value frame works results (policy := policy) →
      InvocationRel space dispatch lookup live scope caller value frame results (policy := policy)

inductive InvocationEquationsRel : Space → GroundedDispatch → CastLookup → List Atom → List String →
    Entry.Value → Frame → List EquationWork → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | nil {space dispatch lookup live scope original frame policy} :
      InvocationEquationsRel space dispatch lookup live scope original frame [] [] (policy := policy)
  | cons {space dispatch lookup live scope original frame work works output children rest policy} :
      output.bindings = work.bindings →
      Entry.Value.UnifyRel policy.rebuilding frame.environment original (Entry.Value.ofAtom work.pattern) output.environment →
      BoundaryRel space dispatch lookup live scope (some original.erase) .producer
        (output.read policy (Entry.Value.ofAtom work.body)) output children (policy := policy) →
      InvocationEquationsRel space dispatch lookup live scope original frame works rest (policy := policy) →
      InvocationEquationsRel space dispatch lookup live scope original frame (work :: works) (children ++ rest) (policy := policy)

/-- Licensed uses of one completed child occurrence. None of these rules
exports a chain binder into the caller's constraint record. -/
inductive BoundaryRel : Space → GroundedDispatch → CastLookup → List Atom → List String → Option Atom →
    Boundary → Entry.Value → Frame → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | chain {space dispatch lookup live scope caller name template value frame results policy} :
      MinimalRel space dispatch lookup live scope caller
        (substituteBinder policy name (frame.read policy value) template) frame results (policy := policy) →
      BoundaryRel space dispatch lookup live scope caller (.chain name template) value frame results (policy := policy)
  | bodyTerminal {space dispatch lookup live scope caller value frame policy} :
      Minimal.embeddedInstruction (frame.read policy value).erase = false →
      BoundaryRel space dispatch lookup live scope caller .body value frame [(frame.read policy value,frame)] (policy := policy)
  | bodyResume {space dispatch lookup live scope caller value frame results policy} :
      Minimal.embeddedInstruction (frame.read policy value).erase = true →
      BodyRel space dispatch lookup live scope caller (frame.read policy value) frame results (policy := policy) →
      BoundaryRel space dispatch lookup live scope caller .body value frame results (policy := policy)
  | functionReturn {space dispatch lookup live scope caller readiness returned frame policy} :
      BoundaryRel space dispatch lookup live scope caller .functionDone
        (.expression readiness [.symbol "return",returned]) frame [(returned,frame)] (policy := policy)
  | functionNoReturn {space dispatch lookup live scope caller value frame policy} :
      (∀ returned, value.erase ≠ .expression [.symbol "return",returned]) →
      BoundaryRel space dispatch lookup live scope caller .functionDone value frame
        [(Entry.Value.ofAtom (Minimal.functionTerminalResult caller value.erase),frame)] (policy := policy)
  | producerRaw {space dispatch lookup live scope caller value frame policy} :
      ¬FunctionPending policy value →
      BoundaryRel space dispatch lookup live scope caller .producer value frame [(value,frame)] (policy := policy)
  | producerFunction {space dispatch lookup live scope caller value frame results policy} :
      FunctionPending policy value →
      MinimalRel space dispatch lookup live scope caller value frame results (policy := policy) →
      BoundaryRel space dispatch lookup live scope caller .producer value frame results (policy := policy)
  | returned {space dispatch lookup live scope caller original expected value frame results policy} :
      ReturnRel space dispatch lookup live scope original expected value frame results (policy := policy) →
      BoundaryRel space dispatch lookup live scope caller (.returned original expected) value frame results (policy := policy)
  | nativeEmittedRaw {space dispatch lookup live scope caller original value frame results policy} :
      BoundaryRel space dispatch lookup live scope (some original.erase) .producer value frame results (policy := policy) →
      BoundaryRel space dispatch lookup live scope caller (.native original none .emitted) value frame results (policy := policy)
  | nativeEmittedReturn {space dispatch lookup live scope caller original expected value frame produced results policy} :
      BoundaryRel space dispatch lookup (expected :: live) scope (some original.erase) .producer value frame produced (policy := policy) →
      BoundaryBatchRel space dispatch lookup live scope caller (.returned original expected) produced results (policy := policy) →
      BoundaryRel space dispatch lookup live scope caller (.native original (some expected) .emitted) value frame results (policy := policy)
  | nativeCompletedRaw {space dispatch lookup live scope caller original value frame policy} :
      BoundaryRel space dispatch lookup live scope caller (.native original none .completed) value frame [(value,frame)] (policy := policy)
  | nativeCompletedReturn {space dispatch lookup live scope caller original expected value frame results policy} :
      NativeCompletedReturnRel space
        (lookup (invocationTypeScope scope live original.erase expected frame.bindings) space)
        policy value expected frame results →
      BoundaryRel space dispatch lookup live scope caller (.native original (some expected) .completed) value frame results (policy := policy)

inductive BoundaryBatchRel : Space → GroundedDispatch → CastLookup → List Atom → List String → Option Atom →
    Boundary → List Result → List Result → (policy : Policy := Policy.unmarked) → Prop where
  | nil {space dispatch lookup live scope caller boundary policy} :
      BoundaryBatchRel space dispatch lookup live scope caller boundary [] [] (policy := policy)
  | cons {space dispatch lookup live scope caller boundary head heads children rest policy} :
      BoundaryRel space dispatch lookup live scope caller boundary head.1 head.2 children (policy := policy) →
      BoundaryBatchRel space dispatch lookup live scope caller boundary heads rest (policy := policy) →
      BoundaryBatchRel space dispatch lookup live scope caller boundary (head :: heads) (children ++ rest) (policy := policy)
end

/-- Full evaluation dispatch depends on the value read in the reached frame.
This retains readiness as well as syntax; equality of erased atoms alone does
not suffice for a policy which reuses completed values. -/
theorem AtomRel.input_read_eq
    {space dispatch lookup live scope left right expected frame results policy}
    (derived : AtomRel space dispatch lookup live scope left expected frame results (policy := policy))
    (same : frame.read policy left = frame.read policy right) :
    AtomRel space dispatch lookup live scope right expected frame results (policy := policy) := by
  cases derived with
  | delivered entered =>
    simp only [same] at *
    exact .delivered entered
  | cast entered checked related =>
    simp only [same] at *
    exact .cast entered checked related
  | tuple entered read types tuples calls selected =>
    simp only [same] at *
    exact .tuple entered read types tuples calls selected
  | function entered read chosen invoked selected =>
    simp only [same] at *
    exact .function entered read chosen invoked selected
  | fallback entered read chosen tuples calls selected =>
    simp only [same] at *
    exact .fallback entered read chosen tuples calls selected
  | selectionFailed entered read chosen selected =>
    simp only [same] at *
    exact .selectionFailed entered read chosen selected

theorem BoundaryBatchRel.returned_single
    {space dispatch lookup live scope caller original expected value frame results policy}
    (returned : ReturnRel space dispatch lookup live scope original expected value frame results (policy := policy)) :
    BoundaryBatchRel space dispatch lookup live scope caller (.returned original expected) [(value,frame)] results (policy := policy) := by
  simpa only [List.append_nil] using BoundaryBatchRel.cons (.returned returned) .nil

theorem BoundaryBatchRel.single
    {space dispatch lookup live scope caller site value frame results policy}
    (batch : BoundaryBatchRel space dispatch lookup live scope caller site [(value,frame)] results (policy := policy)) :
    BoundaryRel space dispatch lookup live scope caller site value frame results (policy := policy) := by
  cases batch with
  | cons child tail =>
      cases tail
      simpa only [List.append_nil] using child

/-- An ordinary minimal terminal neither reinterprets data nor changes its
frame. This law is independent of the equation space and ready-value policy. -/
theorem MinimalRel.data_exact
    {space dispatch lookup live scope caller value frame results policy}
    (completed : MinimalRel space dispatch lookup live scope caller value frame results (policy := policy))
    (terminal : Minimal.embeddedInstruction value.erase = false) : results = [(value,frame)] := by
  cases completed <;> simp_all [Minimal.embeddedInstruction,Entry.Value.erase]

theorem BoundaryRel.chain_data_exact
    {space dispatch lookup live scope caller name template value frame results policy}
    (completed : BoundaryRel space dispatch lookup live scope caller (.chain name template) value frame results (policy := policy))
    (terminal : Minimal.embeddedInstruction (substituteBinder policy name (frame.read policy value) template).erase = false) :
    results = [(substituteBinder policy name (frame.read policy value) template,frame)] := by
  cases completed with
  | chain child => exact child.data_exact terminal

theorem BoundaryRel.body_terminal_exact
    {space dispatch lookup live scope caller value frame results policy}
    (completed : BoundaryRel space dispatch lookup live scope caller .body value frame results (policy := policy))
    (terminal : Minimal.embeddedInstruction (frame.read policy value).erase = false) :
    results = [(frame.read policy value,frame)] := by
  cases completed with
  | bodyTerminal => rfl
  | bodyResume entered _ => rw [terminal] at entered; cases entered

theorem BodyRel.data_exact
    {space dispatch lookup live scope caller value frame results policy}
    (completed : BodyRel space dispatch lookup live scope caller value frame results (policy := policy))
    (rawTerminal : Minimal.embeddedInstruction value.erase = false)
    (readTerminal : Minimal.embeddedInstruction (frame.read policy value).erase = false) :
    results = [(frame.read policy value,frame)] := by
  cases completed with
  | run raw followed =>
      have exactRaw := raw.data_exact rawTerminal
      subst exactRaw
      exact followed.single.body_terminal_exact readTerminal

/-- A function return transfers its payload once. Callable-looking and
held payloads are equally raw at this boundary. -/
theorem MinimalRel.immediate_function_exact
    {space dispatch lookup live scope caller value results policy}
    (completed : MinimalRel space dispatch lookup live scope caller
      (.expression .active [.symbol "function",.expression .active [.symbol "return",value]])
      Frame.empty results (policy := policy)) : results = [(value,Frame.empty)] := by
  generalize inputEq : (Entry.Value.expression .active [.symbol "function",.expression .active [.symbol "return",value]]) = input at completed
  cases completed with
  | data terminal => rw [←inputEq] at terminal; simp [Entry.Value.erase,Minimal.embeddedInstruction] at terminal
  | function _ body followed =>
      cases inputEq
      have returned := body.data_exact (by simp [Entry.Value.erase,Minimal.embeddedInstruction])
        (by simp [Frame.read_empty,Entry.Value.erase,Minimal.embeddedInstruction])
      simp only [Frame.read_empty] at returned
      rw [returned] at followed
      have terminal := followed.single
      cases terminal with
      | functionReturn => rfl
      | functionNoReturn impossible =>
          exact (impossible value.erase (by simp [Entry.Value.erase])).elim
  | eval => simp at inputEq
  | evalc => simp at inputEq
  | chain => simp at inputEq
  | unifyYes => simp at inputEq
  | unifyNo => simp at inputEq
  | unifyBadArity => simp at inputEq
  | consAtom => simp at inputEq
  | deconsAtom => simp at inputEq
  | metta => simp at inputEq
  | contextSpace => simp at inputEq

/-- Ordinary equation production is the raw producer boundary followed by
the typed return gate. Function wrappers use the same constructor. -/
theorem EquationBodiesRel.ordinary_cons
    {space dispatch lookup live scope original expected frame work works output children rest policy}
    (reached : output.bindings = work.bindings)
    (unified : Entry.Value.UnifyRel policy.rebuilding frame.environment original
      (Entry.Value.ofAtom work.pattern) output.environment)
    (ordinary : ¬FunctionPending policy (output.read policy (Entry.Value.ofAtom work.body)))
    (child : ReturnRel space dispatch lookup live scope original expected
      (output.read policy (Entry.Value.ofAtom work.body)) output children (policy := policy))
    (tail : EquationBodiesRel space dispatch lookup live scope original expected frame works rest (policy := policy)) :
    EquationBodiesRel space dispatch lookup live scope original expected frame (work :: works) (children ++ rest) (policy := policy) :=
  .cons reached unified (.producerRaw ordinary) (BoundaryBatchRel.returned_single child) tail

mutual

/-- Successful argument packets and propagated failures are disjoint
protocol cases, even when a packet's payload begins with `Error`. -/
theorem ArgumentsRel.packet_or_error
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live scope requests frame results policy}
    (source : ArgumentsRel space dispatch lookup live scope requests frame results (policy := policy))
    {result : Result} (present : result ∈ results) :
    IsEmptyOrErrorRel result.1.erase ∨ ∃ values, result.1 = Entry.Value.argumentPacket values :=
  match source with
  | .nil => by
      obtain rfl := List.mem_singleton.mp present
      exact Or.inr ⟨[],rfl⟩
  | .cons _ branches => ArgumentBranchesRel.packet_or_error branches present
termination_by structural source

theorem ArgumentBranchesRel.packet_or_error
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live scope original requests heads results policy}
    (source : ArgumentBranchesRel space dispatch lookup live scope original requests heads results
      (policy := policy)) {result : Result} (present : result ∈ results) :
    IsEmptyOrErrorRel result.1.erase ∨ ∃ values, result.1 = Entry.Value.argumentPacket values :=
  match source with
  | .nil => by cases present
  | .stopped stopped rest => by
      rcases List.mem_cons.mp present with rfl | present
      · exact Or.inl stopped.1
      · exact ArgumentBranchesRel.packet_or_error rest present
  | .continuing _ children rest => by
      rcases List.mem_append.mp present with selected | present
      · obtain ⟨child,member,rfl⟩ := List.mem_map.mp selected
        rcases ArgumentsRel.packet_or_error children member with failed | ⟨values,shaped⟩
        · left
          simpa only [argumentPrepend_error _ _ failed] using failed
        · right
          have same : child = (Entry.Value.argumentPacket values,child.2) := Prod.ext shaped rfl
          rw [same,argumentPrepend_packet]
          exact ⟨_,rfl⟩
      · exact ArgumentBranchesRel.packet_or_error rest present
termination_by structural source

end

/-- Every finite-policy source cast has a completed contextual phase with
exactly its raw result occurrences. The caller supplies no readout witnesses. -/
theorem AtomRel.finite_cast
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {value : Entry.Value} {expected : Atom}
    {frame : Frame} {raw : ResultSet} {policy : Policy}
    (finite : policy.matching = .finite)
    (entry : Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase expected .cast)
    (source : TypeCastBatchRel space (frame.read policy value).erase expected frame.bindings raw
      (lookup := lookup (invocationTypeScope scope live (frame.read policy value).erase
        expected frame.bindings) space) (matching := policy.matching.Rel)) :
    ∃ results, AtomRel space dispatch lookup live scope value expected frame results (policy := policy) ∧
      results.map rawResult = raw := by
  obtain ⟨results,paired⟩ := CastResultRel.lift_finite_batch finite source
  exact ⟨results,.cast entry source paired,CastResultRel.readouts paired⟩

/-- Error priority is an observation-boundary law, independent of which
expression control produced the complete raw batch. -/
theorem publication_no_mixed_errors {policy : Policy} {original : Atom} {raw selected : List Result}
    (priority : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      (raw.map (readResult policy)) selected)
    {good result : Result} (presentGood : good ∈ selected.map (publishResult policy original))
    (accepted : isErrorAtom good.1.erase = false)
    (present : result ∈ selected.map (publishResult policy original)) :
    isErrorAtom result.1.erase = false := by
  obtain ⟨before,presentBefore,rfl⟩ := List.mem_map.mp presentGood
  obtain ⟨after,presentAfter,rfl⟩ := List.mem_map.mp present
  simp only [publishResult_erase] at accepted ⊢
  have goodRaw := (priority.mem_iff before).mp presentBefore
  have resultRaw := (priority.mem_iff after).mp presentAfter
  cases failed : isErrorAtom after.1.erase with
  | false => rfl
  | true =>
      have impossible := (resultRaw.2 failed) before goodRaw.1
      rw [accepted] at impossible
      cases impossible

/-- Complete publication cannot expose an error alongside a non-error.
The law holds for every policy and every contextual child derivation. -/
theorem AtomRel.no_mixed_errors
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {value : Entry.Value} {expected : Atom}
    {frame : Frame} {results : List Result} {policy : Policy}
    (completed : AtomRel space dispatch lookup live scope value expected frame results (policy := policy))
    {good result : Result} (presentGood : good ∈ results)
    (accepted : isErrorAtom good.1.erase = false) (present : result ∈ results) :
    isErrorAtom result.1.erase = false := by
  cases completed with
  | delivered =>
      obtain rfl := List.mem_singleton.mp presentGood
      obtain rfl := List.mem_singleton.mp present
      exact accepted
  | @cast _ _ _ _ _ _ _ _ raw _ _ _ casted related =>
      have same : raw = results.map rawResult := (CastResultRel.readouts related).symm
      have goodRaw : rawResult good ∈ raw := by
        rw [same]
        exact List.mem_map.mpr ⟨good,presentGood,rfl⟩
      have resultRaw : rawResult result ∈ raw := by
        rw [same]
        exact List.mem_map.mpr ⟨result,present,rfl⟩
      exact casted.no_mixed_errors goodRaw accepted resultRaw
  | tuple _ _ _ _ _ priority =>
      exact publication_no_mixed_errors priority presentGood accepted present
  | function _ _ _ _ priority =>
      exact publication_no_mixed_errors priority presentGood accepted present
  | fallback _ _ _ _ _ priority =>
      exact publication_no_mixed_errors priority presentGood accepted present
  | selectionFailed _ _ _ priority =>
      exact publication_no_mixed_errors priority presentGood accepted present

/-- Reading a value and classifying delivery does not enter a child phase. -/
theorem AtomRel.delivery_exact
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {value : Entry.Value} {expected : Atom}
    {frame : Frame} {results : List Result} {policy : Policy}
    (completed : AtomRel space dispatch lookup live scope value expected frame results (policy := policy))
    (entry : Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase expected .deliver) :
    results = [(frame.read policy value,frame)] := by
  cases completed with
  | delivered => rfl
  | cast entered _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
  | tuple entered _ _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
  | function entered _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
  | fallback entered _ _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)
  | selectionFailed entered _ _ _ => exact Entry.Action.noConfusion (Entry.functional entered entry)

/-- Stopped values retain their reached readout and full frame. -/
theorem AtomRel.stopped_exact
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {value : Entry.Value} {expected : Atom}
    {frame : Frame} {results : List Result} {policy : Policy}
    (completed : AtomRel space dispatch lookup live scope value expected frame results (policy := policy))
    (stopped : IsEmptyOrErrorRel (frame.read policy value).erase) :
    results = [(frame.read policy value,frame)] :=
  completed.delivery_exact (.stopped stopped)

private theorem held_entry {policy : Policy} {frame : Frame} {value : Entry.Value}
    {children : List Entry.Value} {expected : Atom}
    (read : frame.read policy value = .expression .held children)
    (reuses : policy.reentry = .reuse) :
    Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase expected .deliver := by
  obtain ⟨action,entry⟩ := Entry.total .reuse .held
    (.expression (children.map Entry.Value.erase)) expected
  have delivered := Entry.held_expression_exact entry
  cases delivered
  simpa only [read,reuses,Entry.Value.status,Entry.Value.erase] using entry

/-- An undefined demand accepts the first type occurrence without renewing
the certified frame or reconstructing its contextual payload. -/
theorem AtomRel.undefined_cast
    {space dispatch lookup live scope value frame policy actual later}
    (entered : Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase Atom.undefinedType .cast)
    (queried : lookup (invocationTypeScope scope live
        (frame.read policy value).erase Atom.undefinedType frame.bindings) space
      frame.bindings (frame.read policy value).erase Atom.undefinedType (actual::later)) :
    AtomRel space dispatch lookup live scope value Atom.undefinedType frame
      [(frame.read policy value,frame)] (policy := policy) := by
  have matched : policy.matching.Rel Atom.undefinedType actual frame.bindings frame.bindings := by
    cases policy.matching with
    | raw => exact Spec.Type.TypeMatchRel.undefinedLeft _ _
    | finite => exact ⟨Spec.Type.TypeMatchRel.undefinedLeft _ _,frame.certified.satisfiable⟩
  apply AtomRel.cast entered
    (raw := [((frame.read policy value).erase,frame.bindings)])
  · exact .success (earlierTypes := []) queried rfl (by simp) matched
  · exact .cons ⟨rfl,.same _,by simp⟩ .nil

/-- Every completed undefined cast retains the original annotated payload
and caller constraints. Its contextual environment may have a different
representation, so the conclusion does not identify whole frame records. -/
theorem AtomRel.undefined_cast_exact
    {space dispatch live scope value frame policy results}
    (completed : AtomRel space dispatch rawLookup live scope value Atom.undefinedType frame results (policy := policy))
    (entered : Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase Atom.undefinedType .cast) :
    ∃ after : Frame, after.bindings = frame.bindings ∧ results = [(frame.read policy value,after)] := by
  cases completed with
  | delivered actual => exact Entry.Action.noConfusion (Entry.functional actual entered)
  | cast _actual source paired =>
      have exactRaw := frame.undefined_cast_batch_exact (by simpa only [rawLookup] using source)
      rw [exactRaw] at paired
      cases paired with
      | cons related rest =>
          cases rest
          have sameBindings := (congrArg Prod.snd related.readout).symm
          have sameValue := related.payload
          simp only [beq_self_eq_true,↓reduceIte] at sameValue
          exact ⟨_,sameBindings,congrArg (fun result => [result]) (Prod.ext sameValue rfl)⟩
  | tuple actual _ _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional actual entered)
  | function actual _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional actual entered)
  | fallback actual _ _ _ _ _ => exact Entry.Action.noConfusion (Entry.functional actual entered)
  | selectionFailed actual _ _ _ => exact Entry.Action.noConfusion (Entry.functional actual entered)

/-- An undefined operator type leaves only tuple interpretation. The direct
tuple and exhausted-selection presentations expose the same completed phases. -/
theorem AtomRel.undefined_operator_phases
    {space dispatch live scope value expected frame policy results readiness operator arguments}
    (completed : AtomRel space dispatch rawLookup live scope value expected frame results (policy := policy))
    (entered : Entry.Rel policy.reentry (frame.read policy value).status
      (frame.read policy value).erase expected .interpret)
    (read : frame.read policy value = .expression readiness (operator::arguments))
    (undefined : StorageTypesRel space operator.erase [Atom.undefinedType]) :
    ∃ rows raw selected,
      TupleRel space dispatch rawLookup (expected::live) scope (operator::arguments) frame rows (policy := policy) ∧
      CallsRel space dispatch rawLookup live scope expected rows raw (policy := policy) ∧
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (readResult policy)) selected ∧
      results = selected.map (publishResult policy (frame.read policy value).erase) := by
  cases completed with
  | delivered actual => exact Entry.Action.noConfusion (Entry.functional actual entered)
  | cast actual _ _ => exact Entry.Action.noConfusion (Entry.functional actual entered)
  | tuple _ materialized _ tuple calls priority =>
      rw [read] at materialized
      cases materialized
      exact ⟨_,_,_,tuple,calls,priority,rfl⟩
  | function _ materialized selected _ _ =>
      rw [read] at materialized
      cases materialized
      have impossible := selected.undefined_exact undefined
      cases impossible
  | fallback _ materialized selected tuple calls priority =>
      rw [read] at materialized
      cases materialized
      have exhausted := selected.undefined_exact undefined
      have noErrors := (InvocationSelection.exhausted.inj exhausted).1
      subst noErrors
      exact ⟨_,_,_,tuple,calls,by simpa only [diagnosticResults,List.map_nil,List.append_nil] using priority,rfl⟩
  | selectionFailed _ materialized selected _ =>
      rw [read] at materialized
      cases materialized
      have impossible := selected.undefined_exact undefined
      have boolean := (InvocationSelection.exhausted.inj impossible).2
      cases boolean

/-- Reuse completes a held read without running another child phase,
independently of the space, dispatch or demand. -/
theorem AtomRel.reuse_expression
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {value : Entry.Value} {expected : Atom}
    {frame : Frame} {children : List Entry.Value} {policy : Policy}
    (read : frame.read policy value = .expression .held children)
    (reuses : policy.reentry = .reuse) :
    AtomRel space dispatch lookup live scope value expected frame
      [(frame.read policy value,frame)] (policy := policy) :=
  .delivered (held_entry read reuses)

theorem AtomRel.reuse_expression_exact
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {value : Entry.Value} {expected : Atom}
    {frame : Frame} {children : List Entry.Value} {results : List Result} {policy : Policy}
    (completed : AtomRel space dispatch lookup live scope value expected frame results (policy := policy))
    (read : frame.read policy value = .expression .held children)
    (reuses : policy.reentry = .reuse) : results = [(frame.read policy value,frame)] :=
  completed.delivery_exact (held_entry read reuses)

theorem CallRel.error_exact
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {value : Entry.Value} {expected : Atom}
    {frame : Frame} {results : List Result} {policy : Policy}
    (completed : CallRel space dispatch lookup live scope value expected frame results (policy := policy))
    (failed : IsErrorRel value.erase) : results = [(value,frame)] := by
  cases completed with
  | error => rfl
  | embedded clean _ _ _ _ => exact (clean failed).elim
  | absent clean _ _ => exact (clean failed).elim
  | equations clean _ _ _ _ => exact (clean failed).elim

theorem CallsRel.append
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {expected : Atom} {policy : Policy}
    {left right first second : List Result}
    (before : CallsRel space dispatch lookup live scope expected left first (policy := policy))
    (after : CallsRel space dispatch lookup live scope expected right second (policy := policy)) :
    CallsRel space dispatch lookup live scope expected (left ++ right) (first ++ second) (policy := policy) := by
  induction left generalizing first with
  | nil => cases before; exact after
  | cons head tail ih =>
      cases before with
      | cons child remaining =>
          simpa only [List.cons_append,List.append_assoc] using
            CallsRel.cons child (ih remaining)

theorem CallsRel.split
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {expected : Atom} {policy : Policy}
    (left right : List Result) {results : List Result}
    (completed : CallsRel space dispatch lookup live scope expected (left ++ right) results (policy := policy)) :
    ∃ first second, results = first ++ second ∧
      CallsRel space dispatch lookup live scope expected left first (policy := policy) ∧
      CallsRel space dispatch lookup live scope expected right second (policy := policy) := by
  induction left generalizing results with
  | nil => exact ⟨[],results,rfl,.nil,completed⟩
  | cons head tail ih =>
      cases completed with
      | cons child remaining =>
          obtain ⟨first,second,rfl,earlier,suffix⟩ := ih remaining
          exact ⟨_,second,(List.append_assoc _ _ _).symm,.cons child earlier,suffix⟩

theorem CallsRel.errors_exact
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {expected : Atom} {policy : Policy}
    {sources results : List Result}
    (completed : CallsRel space dispatch lookup live scope expected sources results (policy := policy))
    (failed : ∀ source ∈ sources, IsErrorRel source.1.erase) : results = sources := by
  induction sources generalizing results with
  | nil => cases completed; rfl
  | cons head tail ih =>
      cases completed with
      | cons child remaining =>
          rw [child.error_exact (failed head (by simp)),
            ih remaining (fun source present => failed source (List.mem_cons_of_mem _ present))]
          rfl

theorem CallsRel.error_prefix
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {expected : Atom} {policy : Policy}
    (earlier remaining : List Result) {results : List Result}
    (completed : CallsRel space dispatch lookup live scope expected (earlier ++ remaining) results (policy := policy))
    (failed : ∀ source ∈ earlier, IsErrorRel source.1.erase) :
    ∃ suffix, results = earlier ++ suffix ∧
      CallsRel space dispatch lookup live scope expected remaining suffix (policy := policy) := by
  obtain ⟨first,suffix,same,before,later⟩ := CallsRel.split earlier remaining completed
  exact ⟨suffix,same.trans (congrArg (· ++ suffix) (before.errors_exact failed)),later⟩

/-- Equal errors keep separate contextual frames and occurrences. -/
theorem repeated_error_occurrences
    (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (live : List Atom) (scope : List String) (expected : Atom) (error : Entry.Value)
    (first second : Frame) (failed : IsErrorRel error.erase)
    (policy : Policy := Policy.unmarked) :
    CallsRel space dispatch lookup live scope expected [(error,first),(error,second)]
      [(error,first),(error,second)] (policy := policy) :=
  .cons (.error failed) (.cons (.error failed) .nil)

theorem lost_error_occurrence_refused
    (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (live : List Atom) (scope : List String) (expected : Atom) (error : Entry.Value)
    (first second result : Frame) (failed : IsErrorRel error.erase)
    (policy : Policy := Policy.unmarked) :
    ¬CallsRel space dispatch lookup live scope expected [(error,first),(error,second)]
      [(error,result)] (policy := policy) := by
  intro completed
  have same := completed.errors_exact (by
    intro source present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl <;> exact failed)
  have count := congrArg List.length same
  simp at count

namespace Controls

/-- This activation has a real nonempty constraint record and a nested held
value, rather than an assumed result of a decoder. -/
def heldFrame : Frame :=
  ⟨Entry.Value.Controls.bindings,Entry.Value.Controls.environment,Entry.Value.Controls.certificate⟩

open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Match.Merge

def rawSignature : SelectedTypePolicy :=
  ⟨.expression [.symbol "->",Atom.atomType,Atom.atomType],[Atom.atomType],Atom.atomType,rfl⟩

def typedInvocationSpace : Space := ⟨[
  .expression [.symbol ":",.symbol "hold",rawSignature.functionType],
  .expression [.symbol ":",.symbol "datum",.symbol "D"],
  .expression [.symbol ":",.symbol "datum",.symbol "D"]]⟩

def typedInvocation : Entry.Value := .expression .active [.symbol "hold",.symbol "datum"]

theorem typed_operator_query : StorageTypesRel typedInvocationSpace (.symbol "hold") [rawSignature.functionType] := by
  apply StorageTypesRel.symbolKnown
  · exact .hit (.skip (by intro type; simp) (.skip (by intro type; simp) .nil))
  · simp

theorem duplicated_argument_query : StorageTypesRel typedInvocationSpace (.symbol "datum") [.symbol "D",.symbol "D"] := by
  apply StorageTypesRel.symbolKnown
  · exact .skip (by intro type; simp) (.hit (.hit .nil))
  · simp

private theorem empty_type_merge : MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
  .mk (by simp [constraints,Bindings.empty]) .nil

theorem typed_operator_match : TypeMatchRel rawSignature.functionType rawSignature.functionType
    Bindings.empty Bindings.empty := by
  refine .structural (by decide) (by decide) (by decide) (by decide) ?_ empty_type_merge
  exact .expression
    (.cons (.symSym "->" semanticLoopFree_empty) empty_type_merge
      (.cons (.symSym "Atom" semanticLoopFree_empty) empty_type_merge
        (.cons (.symSym "Atom" semanticLoopFree_empty) empty_type_merge .nil))) semanticLoopFree_empty

theorem duplicated_applicability (policy : Policy) :
    ApplicationChecksRel typedInvocationSpace (rawTypeLookupRel typedInvocationSpace) policy
      typedInvocation.erase Atom.undefinedType rawSignature Frame.empty [Frame.empty,Frame.empty] [] := by
  have accepted : TypeCheckRel policy Atom.atomType Frame.empty (.symbol "D") (.inr Frame.empty) :=
    .accepted (.unchanged (Frame.empty.preserved_type_match policy (.atomLeft _ _)))
  have checked : ArgumentChecksRel typedInvocationSpace (rawTypeLookupRel typedInvocationSpace) policy
      typedInvocation.erase (.symbol "datum") Atom.atomType 1 [Frame.empty] [Frame.empty,Frame.empty] [] := by
    simpa [checkedFrames,checkedFailures] using
      (ArgumentChecksRel.cons (expression := typedInvocation.erase) (position := 1) duplicated_argument_query
        (.cons accepted (.cons accepted .nil)) .nil)
  have returned : TypeCheckRel policy Atom.undefinedType Frame.empty Atom.atomType (.inr Frame.empty) :=
    .accepted (.unchanged (Frame.empty.preserved_type_match policy (.undefinedLeft _ _)))
  simpa [checkedFrames,checkedFailures] using
    (ApplicationChecksRel.checked (selected := rawSignature) (expected := Atom.undefinedType)
      (before := Frame.empty) (show typedInvocation.erase = .expression [.symbol "hold",.symbol "datum"] by
        simp [typedInvocation,Entry.Value.erase])
      (.cons checked .nil) (.cons returned (.cons returned .nil)))

theorem typed_invocation_selection (policy : Policy) (live : List Atom) (scope : List String) :
    InvocationSelectionRel typedInvocationSpace rawLookup policy live scope typedInvocation.erase
      (.symbol "hold") Atom.undefinedType Frame.empty (.selected rawSignature [Frame.empty,Frame.empty]) :=
  ⟨[rawSignature.functionType],typed_operator_query,.selected (duplicated_applicability policy) (by simp)⟩

theorem typed_operator_phase (dispatch : GroundedDispatch) (policy : Policy) (live : List Atom) (scope : List String) :
    AtomRel typedInvocationSpace dispatch rawLookup live scope (.symbol "hold") rawSignature.functionType
      Frame.empty [(.symbol "hold",Frame.empty)] (policy := policy) := by
  apply AtomRel.cast (raw := [(.symbol "hold",Bindings.empty)])
  · simpa only [Frame.read_empty,Entry.Value.erase,Entry.Value.status] using
      (Entry.Rel.cast (policy := policy.reentry) (status := .active)
        (atom := .symbol "hold") (expected := rawSignature.functionType)
        (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) (.symbol "hold") (by decide)
        (Or.inl ⟨"hold",rfl⟩) (by intro impossible; cases impossible))
  · have casted : TypeCastBatchRel typedInvocationSpace (.symbol "hold") rawSignature.functionType
        Frame.empty.bindings [(.symbol "hold",Bindings.empty)]
        (lookup := rawTypeLookupRel typedInvocationSpace) (matching := policy.matching.Rel) :=
      .success (earlierTypes := []) (laterTypes := []) typed_operator_query rfl (by simp)
        (Frame.empty.preserved_type_match policy typed_operator_match)
    simpa only [Frame.read_empty,Entry.Value.erase,rawLookup] using casted
  · exact .cons ⟨by simp [rawResult,Entry.Value.erase,Frame.empty],.same _,by simp [Entry.Value.erase]⟩ .nil

def typedDispatch : GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

theorem typed_invocation_frontier (live : List Atom) :
    EquationFrontierRel typedInvocationSpace live typedInvocation.erase Bindings.empty [] := by
  apply EquationFrontierRel.completed (blocks := [[],[],[]])
  refine .cons (.irrelevant _ _ ?_) (.cons (.irrelevant _ _ ?_) (.cons (.irrelevant _ _ ?_) .nil))
  all_goals
    intro left right impossible
    have head := (List.cons.inj (Atom.expression.inj impossible)).1
    simp at head

theorem typed_invocation_call (policy : Policy) (live : List Atom) (scope : List String) :
    CallRel typedInvocationSpace typedDispatch rawLookup live scope typedInvocation Atom.atomType Frame.empty
      [(typedInvocation,Frame.empty)] (policy := policy) := by
  apply CallRel.absent
  · simp [typedInvocation,Entry.Value.erase,IsErrorRel]
  · simp [NonGroundedCallRel,Minimal.HostCall,typedDispatch,typedInvocation,
      Entry.Value.erase,Minimal.embeddedInstruction]
  · exact typed_invocation_frontier _

theorem immediate_minimal_function (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom) (value : Entry.Value) :
    MinimalRel space dispatch lookup live scope caller
      (.expression .active [.symbol "function",.expression .active [.symbol "return",value]])
      Frame.empty [(value,Frame.empty)] (policy := policy) := by
  apply MinimalRel.function (raw := [(.expression .active [.symbol "return",value],Frame.empty)]) rfl
  · apply BodyRel.run (raw := [(.expression .active [.symbol "return",value],Frame.empty)])
    · exact .data (by simp [Entry.Value.erase,Minimal.embeddedInstruction])
    · simpa only [List.append_nil,Frame.read_empty] using
        (BoundaryBatchRel.cons (head := (.expression .active [.symbol "return",value],Frame.empty))
          (BoundaryRel.bodyTerminal (value := .expression .active [.symbol "return",value]) (frame := Frame.empty) (policy := policy)
          (by simp [Frame.read_empty,Entry.Value.erase,Minimal.embeddedInstruction])) .nil)
  · simpa only [List.append_nil] using
      (BoundaryBatchRel.cons (BoundaryRel.functionReturn (readiness := .active) (returned := value)) .nil)

theorem minimal_data (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (value : Entry.Value) (frame : Frame) (terminal : Minimal.embeddedInstruction value.erase = false) :
    MinimalRel space dispatch lookup live scope caller value frame [(value,frame)] (policy := policy) := .data terminal

theorem chain_return_preserves_frame (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom)
    (name : String) (value : Entry.Value) (frame : Frame) :
    BoundaryRel space dispatch lookup live scope caller (.chain name (.expression .active [.symbol "return",.var name]))
      value frame [(.expression .active [.symbol "return",frame.read policy value],frame)] (policy := policy) := by
  apply BoundaryRel.chain
  rw [substituteBinder_return]
  exact .data (by simp [Entry.Value.erase,Minimal.embeddedInstruction])

theorem chain_return_cannot_write_binding
    {space dispatch lookup policy live scope caller name value frame results}
    (completed : BoundaryRel space dispatch lookup live scope caller
      (.chain name (.expression .active [.symbol "return",.var name])) value frame results (policy := policy)) :
    results = [(.expression .active [.symbol "return",frame.read policy value],frame)] := by
  have exactResult := completed.chain_data_exact (by
    rw [substituteBinder_return]; simp [Entry.Value.erase,Minimal.embeddedInstruction])
  simpa only [substituteBinder_return] using exactResult

theorem saved_caller_no_return (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (live : List Atom) (scope : List String) (actual : Atom) :
    MinimalRel space dispatch lookup live scope (some actual)
      (.expression .active [.symbol "function",.expression .active [.symbol "halt"]]) Frame.empty
      [(Entry.Value.ofAtom (Atom.error actual (.symbol "NoReturn")),Frame.empty)] (policy := policy) := by
  apply MinimalRel.function (raw := [(.expression .active [.symbol "halt"],Frame.empty)]) rfl
  · apply BodyRel.run (raw := [(.expression .active [.symbol "halt"],Frame.empty)])
    · exact .data (by simp [Entry.Value.erase,Minimal.embeddedInstruction])
    · simpa only [List.append_nil,Frame.read_empty] using
        (BoundaryBatchRel.cons (head := (.expression .active [.symbol "halt"],Frame.empty))
          (BoundaryRel.bodyTerminal (value := .expression .active [.symbol "halt"]) (frame := Frame.empty) (policy := policy)
            (by simp [Frame.read_empty,Entry.Value.erase,Minimal.embeddedInstruction])) .nil)
  · simpa [Entry.Value.erase,Minimal.functionTerminalResult] using
      (BoundaryBatchRel.cons (head := (.expression .active [.symbol "halt"],Frame.empty))
        (BoundaryRel.functionNoReturn (caller := some actual) (value := .expression .active [.symbol "halt"])
          (frame := Frame.empty) (policy := policy) (by intro returned; simp [Entry.Value.erase])) .nil)

/-- Context services are primitive profile data. Recursive work remains in
the source and AM; these fields do not implement a recursive evaluator. -/
def contextualDispatch (services : Minimal.Services) (enumeration : Minimal.Enumeration) : GroundedDispatch :=
  { typedDispatch with minimal := some ⟨services,enumeration⟩ }

theorem context_space_invocation (services : Minimal.Services) (enumeration : Minimal.Enumeration)
    (context : Space) (lookup : CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    InvocationRel context (contextualDispatch services enumeration) lookup live scope caller
      (.expression .active [.symbol "context-space"]) Frame.empty
      [(.grounded (services.contextPayload context),Frame.empty)] (policy := policy) :=
  .embedded (by simp [Minimal.HostCall,contextualDispatch,typedDispatch,Entry.Value.erase])
    (by simp [Minimal.embeddedInstruction,Entry.Value.erase]) (.contextSpace rfl)

theorem evalc_context_read (services : Minimal.Services) (enumeration : Minimal.Enumeration)
    (space context : Space) (lookup : CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    MinimalRel space (contextualDispatch services enumeration) lookup live scope caller
      (.expression .active [.symbol "evalc",.expression .active [.symbol "context-space"],
        .grounded (services.contextPayload context)]) Frame.empty
      [(.grounded (services.contextPayload context),Frame.empty)] (policy := policy) := by
  exact .evalc rfl (by simpa only [Frame.read_empty] using
    context_space_invocation services enumeration context lookup policy live scope caller)

theorem metta_raw_child (services : Minimal.Services) (enumeration : Minimal.Enumeration)
    (space context : Space) (lookup : CastLookup) (policy : Policy)
    (live : List Atom) (scope : List String) (caller : Option Atom) (value : Entry.Value) :
    MinimalRel space (contextualDispatch services enumeration) lookup live scope caller
      (.expression .active [.symbol "metta",value,Entry.Value.ofAtom Atom.atomType,
        .grounded (services.contextPayload context)]) Frame.empty [(value,Frame.empty)] (policy := policy) := by
  apply MinimalRel.metta rfl
  have child := AtomRel.delivered (space := context) (dispatch := contextualDispatch services enumeration)
    (lookup := lookup) (live := live) (scope := scope) (value := value) (expected := Atom.atomType)
    (frame := Frame.empty) (policy := policy) (Entry.atom_demand policy.reentry _ _)
  simpa only [Entry.Value.erase_ofAtom,Frame.read_empty] using child

/-- Raw demands deliver arbitrary open values and preserve nested statuses.
Literal errors are unchanged data, and so enter the successful packet. -/
theorem raw_arguments (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (values : List Entry.Value) (live : List Atom) (scope : List String) :
    ArgumentsRel space dispatch lookup live scope
      (values.map fun value => (value,Atom.atomType)) Frame.empty
      [(Entry.Value.argumentPacket values,Frame.empty)] (policy := policy) := by
  induction values generalizing live with
  | nil => exact .nil
  | cons value values ih =>
      have child : AtomRel space dispatch lookup
          (argumentScope (values.map fun value => (value,Atom.atomType)) ++ live) scope
          value Atom.atomType Frame.empty [(value,Frame.empty)] (policy := policy) := by
        simpa only [Frame.read_empty] using
          (AtomRel.delivered (space := space) (dispatch := dispatch) (lookup := lookup)
            (live := argumentScope (values.map fun value => (value,Atom.atomType)) ++ live)
            (scope := scope) (value := value) (frame := Frame.empty) (policy := policy)
            (Entry.atom_demand policy.reentry _ _))
      have rest : ArgumentBranchesRel space dispatch lookup live scope value
          (values.map fun value => (value,Atom.atomType)) [] [] (policy := policy) := .nil
      have branches := ArgumentBranchesRel.continuing
        (head := (value,Frame.empty)) (by simp [ArgumentStopped]) (ih (value.erase :: live)) rest
      apply ArgumentsRel.cons child
      simpa only [List.map_cons,List.map_nil,List.append_nil,argumentPrepend_packet] using branches

theorem typed_function_phase (policy : Policy) (live : List Atom) (scope : List String) :
    FunctionRel typedInvocationSpace typedDispatch rawLookup live scope Atom.undefinedType rawSignature
      (.symbol "hold") [.symbol "datum"] Frame.empty [(typedInvocation,Frame.empty)] (policy := policy) := by
  apply FunctionRel.evaluated rfl (typed_operator_phase typedDispatch policy _ _)
  have tail : ArgumentsRel typedInvocationSpace typedDispatch rawLookup
      (.symbol "hold" :: live) scope [(.symbol "datum",Atom.atomType)] Frame.empty
      [(Entry.Value.argumentPacket [.symbol "datum"],Frame.empty)] (policy := policy) :=
    raw_arguments _ _ _ _ [.symbol "datum"] _ _
  have selectedTail : ArgumentsRel typedInvocationSpace typedDispatch rawLookup
      ((Entry.Value.symbol "hold").erase :: live) scope [(.symbol "datum",Atom.atomType)] Frame.empty
      [(Entry.Value.argumentPacket [.symbol "datum"],Frame.empty)] (policy := policy) := by
    simpa only [Entry.Value.erase] using tail
  simpa [rawSignature,functionAssemble,typedInvocation] using
    (FunctionBranchesRel.continuing (space := typedInvocationSpace) (dispatch := typedDispatch)
      (lookup := rawLookup) (live := live) (scope := scope) (policy := policy)
      (requests := [(.symbol "datum",Atom.atomType)]) (head := (.symbol "hold",Frame.empty))
      (by simp [Entry.Value.erase,IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) selectedTail .nil)

/-- Repeated declared types produce repeated applicability and evaluation
occurrences, through selection, head/arguments, return and publication. -/
theorem duplicated_typed_invocation (policy : Policy) (live : List Atom) (scope : List String) :
    AtomRel typedInvocationSpace typedDispatch rawLookup live scope typedInvocation Atom.undefinedType Frame.empty
      ([ (typedInvocation,Frame.empty),(typedInvocation,Frame.empty) ].map
        (publishResult policy typedInvocation.erase)) (policy := policy) := by
  have entered : Entry.Rel policy.reentry (Frame.empty.read policy typedInvocation).status
      (Frame.empty.read policy typedInvocation).erase Atom.undefinedType .interpret := by
    simpa only [Frame.read_empty,typedInvocation,Entry.Value.status,Entry.Value.erase,List.map_cons,List.map_nil] using
      (Entry.Rel.expression (policy := policy.reentry) (status := .active)
        (head := .symbol "hold") (tail := [.symbol "datum"]) (expected := Atom.undefinedType)
        (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) (by decide) (Or.inr rfl))
  have invoked : InvocationsRel typedInvocationSpace typedDispatch rawLookup live scope Atom.undefinedType rawSignature
      (.symbol "hold") [.symbol "datum"] [Frame.empty,Frame.empty]
      [(typedInvocation,Frame.empty),(typedInvocation,Frame.empty)] (policy := policy) := by
    have interpreted := typed_function_phase policy (invocationReturnType rawSignature :: live) scope
    have called : CallsRel typedInvocationSpace typedDispatch rawLookup live scope (invocationReturnType rawSignature)
        [(typedInvocation,Frame.empty)] [(typedInvocation,Frame.empty)] (policy := policy) := by
      simpa [invocationReturnType,rawSignature,Atom.atomType,Atom.expressionType] using
        (CallsRel.cons (head := (typedInvocation,Frame.empty)) (typed_invocation_call policy live scope) .nil)
    simpa using InvocationsRel.cons interpreted called (InvocationsRel.cons interpreted called .nil)
  have prioritized : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ([(typedInvocation,Frame.empty),(typedInvocation,Frame.empty)].map (readResult policy))
      [(typedInvocation,Frame.empty),(typedInvocation,Frame.empty)] := by
    have priority : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        [(typedInvocation,Frame.empty),(typedInvocation,Frame.empty)]
        [(typedInvocation,Frame.empty),(typedInvocation,Frame.empty)] := by
      simpa [typedInvocation,Entry.Value.erase,isErrorAtom] using
        (SuccessPriorityRel.successes (isError := fun result : Result => isErrorAtom result.1.erase)
          (raw := [(typedInvocation,Frame.empty),(typedInvocation,Frame.empty)])
          (by exact ⟨(typedInvocation,Frame.empty),by simp,by simp [typedInvocation,Entry.Value.erase,isErrorAtom]⟩))
    simpa only [List.map_cons,List.map_nil,readResult,Frame.read_empty] using priority
  simpa only [Frame.read_empty] using
    (AtomRel.function (value := typedInvocation) entered (Frame.read_empty _ _)
      (by simpa only [Frame.read_empty,Entry.Value.erase] using typed_invocation_selection policy live scope)
      invoked prioritized)

def wrongArityInvocation : Entry.Value := .expression .active [.symbol "hold"]

def wrongArityError : Atom := mkError wrongArityInvocation.erase .incorrectNumberOfArguments

theorem failed_typed_selection (policy : Policy) (live : List Atom) (scope : List String) :
    AtomRel typedInvocationSpace typedDispatch rawLookup live scope wrongArityInvocation Atom.undefinedType Frame.empty
      ((diagnosticResults [wrongArityError] Frame.empty).map
        (publishResult policy wrongArityInvocation.erase)) (policy := policy) := by
  have entered : Entry.Rel policy.reentry (Frame.empty.read policy wrongArityInvocation).status
      (Frame.empty.read policy wrongArityInvocation).erase Atom.undefinedType .interpret := by
    simpa only [Frame.read_empty,wrongArityInvocation,Entry.Value.status,Entry.Value.erase,List.map_cons,List.map_nil] using
      (Entry.Rel.expression (policy := policy.reentry) (status := .active)
        (head := .symbol "hold") (tail := []) (expected := Atom.undefinedType)
        (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) (by decide) (Or.inr rfl))
  have selected : InvocationSelectionRel typedInvocationSpace rawLookup policy live scope
      (Frame.empty.read policy wrongArityInvocation).erase (.symbol "hold") Atom.undefinedType Frame.empty
      (.exhausted [wrongArityError] false) := by
    refine ⟨[rawSignature.functionType],typed_operator_query,?_⟩
    simpa only [Frame.read_empty,wrongArityError,List.append_nil] using
      (InvocationScanRel.rejected (signature := rawSignature)
        (ApplicationChecksRel.wrongArity (operator := .symbol "hold") (arguments := [])
          (by simp [wrongArityInvocation,Entry.Value.erase]) (by decide)) InvocationScanRel.nil)
  have priority : SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
      ((diagnosticResults [wrongArityError] Frame.empty).map (readResult policy))
      (diagnosticResults [wrongArityError] Frame.empty) := by
    simpa only [List.map_cons,List.map_nil,diagnosticResults,readResult,Frame.read_empty] using
      (SuccessPriorityRel.allErrors (isError := fun result : Result => isErrorAtom result.1.erase)
        (raw := diagnosticResults [wrongArityError] Frame.empty) (by
          intro result present
          obtain rfl := List.mem_singleton.mp present
          simp [wrongArityError,mkError,Entry.Value.erase_ofAtom,isErrorAtom,Atom.error]))
  simpa only [Frame.read_empty] using
    (AtomRel.selectionFailed (value := wrongArityInvocation) entered (Frame.read_empty _ _)
      (by simpa only [Entry.Value.erase] using selected) priority)

theorem first_applicable_discards_prior_errors (policy : Policy) :
    InvocationScanRel typedInvocationSpace (rawTypeLookupRel typedInvocationSpace) policy
      typedInvocation.erase Atom.undefinedType Frame.empty
      [ .expression [.symbol "->",Atom.atomType,Atom.atomType,Atom.atomType],rawSignature.functionType ]
      (.selected rawSignature [Frame.empty,Frame.empty]) := by
  let earlier : SelectedTypePolicy :=
    ⟨.expression [.symbol "->",Atom.atomType,Atom.atomType,Atom.atomType],
      [Atom.atomType,Atom.atomType],Atom.atomType,rfl⟩
  exact InvocationScanRel.rejected (signature := earlier)
    (ApplicationChecksRel.wrongArity (operator := .symbol "hold") (arguments := [.symbol "datum"])
      (by simp [typedInvocation,Entry.Value.erase]) (by decide))
    (.selected (duplicated_applicability policy) (by simp))

theorem duplicated_raw_type_occurrence_not_dropped (policy : Policy) :
    ¬∃ checks, List.Forall₂ (TypeCheckRel policy Atom.atomType Frame.empty)
        [.symbol "D",.symbol "D"] checks ∧ (checkedFrames checks).length = 1 := by
  rintro ⟨checks,paired,dropped⟩
  have count := paired |> TypeCheckRel.raw_count
  simp only [List.length_cons,List.length_nil] at count
  omega

theorem raw_arguments_exact
    {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}
    {values : List Entry.Value} {live : List Atom} {scope : List String} {results : List Result}
    (source : ArgumentsRel space dispatch lookup live scope
      (values.map fun value => (value,Atom.atomType)) Frame.empty results (policy := policy)) :
    results = [(Entry.Value.argumentPacket values,Frame.empty)] := by
  induction values generalizing live results with
  | nil => cases source; rfl
  | cons value values ih =>
      cases source with
      | cons child branches =>
          have same := child.delivery_exact (Entry.atom_demand policy.reentry _ _)
          simp only [Frame.read_empty] at same
          rw [same] at branches
          cases branches with
          | stopped stopped rest => exact (stopped.2 rfl).elim
          | continuing _ children rest =>
              have selected := ih children
              cases rest
              simp only [selected,List.map_cons,List.map_nil,List.append_nil,argumentPrepend_packet]

def argumentError : Entry.Value :=
  .expression .active [.symbol "Error",.symbol "Argument",.symbol "Failed"]

def argumentErrorEnvironment : Entry.Value.Environment := [("x",argumentError)]
def argumentErrorBindings : Bindings := ⟨[("x",argumentError.erase)],[]⟩

theorem argument_error_certificate :
    ReadoutCertificate argumentErrorBindings (Entry.Value.eraseEnvironment argumentErrorEnvironment) := by
  apply ReadoutCertificate.of_normal_theory
  · simp [argumentErrorEnvironment,argumentError,Entry.Value.eraseEnvironment,Entry.Value.erase,
      TypeSubst.Normal,TypeSubst.keys,TypeSubst.typeVars,TypeSubst.typeVarsList]
  · intro valuation
    simp [Theory.TypeSubstSatisfied,Spec.Type.RuntimeRefinement.TypeBindingSatisfied,
      argumentErrorBindings,argumentErrorEnvironment,Entry.Value.eraseEnvironment]

def argumentErrorFrame : Frame :=
  ⟨argumentErrorBindings,argumentErrorEnvironment,argument_error_certificate⟩

/-- Reading a bound variable produces a changed error, so later requests on
this occurrence are skipped. No evaluation premise for those requests exists. -/
theorem bound_argument_failure (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (requests : List ArgumentRequest) (live : List Atom) (scope : List String) :
    ArgumentsRel space dispatch lookup live scope ((.var "x",Atom.atomType) :: requests)
      argumentErrorFrame [(argumentError,argumentErrorFrame)] (policy := policy) := by
  have read : argumentErrorFrame.read policy (.var "x") = argumentError := by
    simp [Frame.read,Entry.Value.substitute,Entry.Value.resolve,argumentErrorFrame,
      argumentErrorEnvironment,List.lookup]
  have failed : IsEmptyOrErrorRel argumentError.erase := by
    simp [argumentError,Entry.Value.erase,IsEmptyOrErrorRel,IsErrorRel]
  apply ArgumentsRel.cons (heads := [(argumentError,argumentErrorFrame)])
  · simpa only [read] using
      (AtomRel.delivered (space := space) (dispatch := dispatch) (lookup := lookup)
        (live := argumentScope requests ++ live) (scope := scope) (value := .var "x")
        (expected := Atom.atomType) (frame := argumentErrorFrame) (policy := policy)
        (Entry.Rel.stopped (by simpa only [read] using failed)))
  · exact .stopped ⟨failed,by simp [argumentError,Entry.Value.erase]⟩ .nil

/-- A failed head skips its arguments, including arbitrary pending values.
The head is read through a real nonempty activation. -/
theorem bound_function_head_failure (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (argument : Entry.Value) (live : List Atom) (scope : List String) :
    FunctionRel space dispatch lookup live scope Atom.undefinedType rawSignature
      (.var "x") [argument] argumentErrorFrame [(argumentError,argumentErrorFrame)] (policy := policy) := by
  have read : argumentErrorFrame.read policy (.var "x") = argumentError := by
    simp [Frame.read,Entry.Value.substitute,Entry.Value.resolve,argumentErrorFrame,
      argumentErrorEnvironment,List.lookup]
  have failed : IsEmptyOrErrorRel argumentError.erase := by
    simp [argumentError,Entry.Value.erase,IsEmptyOrErrorRel,IsErrorRel]
  apply FunctionRel.evaluated (heads := [(argumentError,argumentErrorFrame)]) rfl
  · simpa only [read] using
      (AtomRel.delivered (space := space) (dispatch := dispatch) (lookup := lookup) (policy := policy)
        (value := .var "x") (frame := argumentErrorFrame)
        (live := rawSignature.functionType :: [argument].map Entry.Value.erase ++ live)
        (scope := scope ++ expectedApplicationScope
          (.expression ((Entry.Value.var "x" :: [argument]).map Entry.Value.erase)) Atom.undefinedType)
        (by simpa only [read] using (Entry.Rel.stopped
          (policy := policy.reentry) (status := argumentError.status) (expected := rawSignature.functionType) failed)))
  · exact FunctionBranchesRel.stopped failed .nil

def argumentAliasFrame : Frame :=
  ⟨Entry.Value.Controls.aliasBindings,Entry.Value.Controls.aliasEnvironment,Entry.Value.Controls.alias_certificate⟩

def argumentCastEnvironment : Entry.Value.Environment := [("y",.symbol "T"),("x",.symbol "T")]
def argumentCastBindings : Bindings := Entry.Value.Controls.aliasBindings.assign "y" (.symbol "T")

theorem argument_cast_match :
    TypeMatchRel (.var "y") (.symbol "T") argumentAliasFrame.bindings argumentCastBindings := by
  refine .structural (matched := Bindings.empty.assign "y" (.symbol "T"))
    (by decide) (by decide) (by decide) (by decide) ?_ ?_
  · apply Spec.Match.Merge.MatchRel.varNonVar rfl
    apply Spec.Match.Merge.semanticLoopFree_single_assignment
    intro occurs
    cases occurs
  · apply Spec.Match.Merge.MergeRel.mk
      (order := [Spec.Match.Merge.Constraint.value "y" (.symbol "T")])
    · change List.Perm [Spec.Match.Merge.Constraint.value "y" (.symbol "T")]
        ([Spec.Match.Merge.Constraint.value "y" (.symbol "T")]).eraseDups
      decide
    · apply Spec.Match.Merge.MergeConstraintsRel.value
      · apply Spec.Match.Merge.AddVarBindingRel.fresh
        simp [argumentAliasFrame,Entry.Value.Controls.aliasBindings,Bindings.classValues,
          Bindings.eqClassOrdered,Bindings.eqVarsInOrder,Bindings.eqClass,Bindings.eqClassAux,
          Bindings.eqStep,Bindings.lookup]
      · exact .nil

theorem argument_cast_unification (rebuilding : Entry.RebuildPolicy) :
    Entry.Value.UnifyRel rebuilding argumentAliasFrame.environment (.var "y") (.symbol "T")
      argumentCastEnvironment := by
  apply Entry.Value.UnifyRel.ordinary
  have first : Entry.Value.substitute rebuilding (Entry.Value.resolve argumentAliasFrame.environment)
      (.var "y") = .var "y" := by
    simp [argumentAliasFrame,Entry.Value.Controls.aliasEnvironment,Entry.Value.substitute,
      Entry.Value.resolve,List.lookup]
  have second : Entry.Value.substitute rebuilding (Entry.Value.resolve argumentAliasFrame.environment)
      (.symbol "T") = .symbol "T" := by simp [Entry.Value.substitute]
  rw [first,second]
  have step := Entry.Value.AppliedUnifyRel.bindLeft (policy := rebuilding)
    (environment := argumentAliasFrame.environment) (name := "y") (right := .symbol "T")
    (by simp [Entry.Value.erase,TypeSubst.typeVars])
  simpa [Entry.Value.bind,argumentAliasFrame,argumentCastEnvironment,
    Entry.Value.Controls.aliasEnvironment,Entry.Value.substitute,Entry.Value.resolve,List.lookup] using step

theorem argument_cast_model :
    ∃ valuation : String → Atom, TypeBindingSatisfied valuation argumentCastBindings := by
  refine ⟨fun _ => .symbol "T",?_,?_⟩
  · intro name value present
    simp [argumentCastBindings,Entry.Value.Controls.aliasBindings,Bindings.assign,
      Bindings.isBound,Bindings.lookup] at present
    rcases present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [applyTypeValuation]
  · intro left right present
    simp [argumentCastBindings,Entry.Value.Controls.aliasBindings,Bindings.assign,
      Bindings.isBound,Bindings.lookup] at present

/-- The reached contextual unification earns the exact source certificate. -/
theorem argument_cast_certificate :
    ReadoutCertificate argumentCastBindings (Entry.Value.eraseEnvironment argumentCastEnvironment) := by
  obtain ⟨matched,matching,merged⟩ := TypeMatchRel.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide) argument_cast_match
  have candidate : UnifyCandidateRel (Entry.Value.var "y").erase (Entry.Value.symbol "T").erase
      argumentAliasFrame.bindings argumentCastBindings := by
    simpa only [Entry.Value.erase] using
      (show UnifyCandidateRel (.var "y") (.symbol "T") argumentAliasFrame.bindings argumentCastBindings from
        ⟨matched,matching,Spec.Bindings.ScopeObservation.LogicalMergeRel.comm
          (merged.logicalMerge argument_cast_model)⟩)
  exact (argument_cast_unification .preserve).certifies argumentAliasFrame.certified candidate

def argumentCastFrame : Frame :=
  ⟨argumentCastBindings,argumentCastEnvironment,argument_cast_certificate⟩

def argumentTypeSpace : Space := ⟨[.expression [.symbol ":",.symbol "datum",.symbol "T"]]⟩

theorem argument_cast_phase (dispatch : GroundedDispatch) (policy : Policy) (live : List Atom) (scope : List String) :
    AtomRel argumentTypeSpace dispatch rawLookup live scope (.symbol "datum") (.var "y") argumentAliasFrame
      [(.symbol "datum",argumentCastFrame)] (policy := policy) := by
  have queried : rawTypeLookupRel argumentTypeSpace argumentAliasFrame.bindings (.symbol "datum")
      (.var "y") [.symbol "T"] := StorageTypesRel.symbolKnown (.hit .nil) (by decide)
  have matched : policy.matching.Rel (.var "y") (.symbol "T")
      argumentAliasFrame.bindings argumentCastFrame.bindings := by
    cases selected : policy.matching with
    | raw => exact argument_cast_match
    | finite => exact ⟨argument_cast_match,argument_cast_certificate.satisfiable⟩
  have read : argumentAliasFrame.read policy (.symbol "datum") = .symbol "datum" := by
    simp [Frame.read,Entry.Value.substitute]
  have renewed : Frame.CastRenewRel policy (rawTypeLookupRel argumentTypeSpace)
      (.symbol "datum") (.var "y") argumentAliasFrame argumentCastFrame :=
    .matched (earlier := []) (later := []) queried rfl (by simp) matched
      (by simpa only [Entry.Value.ofAtom,argumentCastFrame] using argument_cast_unification policy.rebuilding)
  apply AtomRel.cast (raw := [(.symbol "datum",argumentCastFrame.bindings)])
  · simpa only [read,Entry.Value.erase,Entry.Value.status] using
      (Entry.Rel.cast (policy := policy.reentry) (status := .active)
        (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) (.symbol "datum") (by decide)
        (Or.inl ⟨"datum",rfl⟩) (by intro impossible; cases impossible))
  · simp only [Frame.read,Entry.Value.substitute,Entry.Value.erase,rawLookup]
    exact .success (earlierTypes := []) (laterTypes := []) queried rfl (by simp) matched
  · simp only [read,rawLookup]
    refine .cons ⟨?_,?_,?_⟩ .nil
    · simp [rawResult,Entry.Value.erase]
    · simpa only [Entry.Value.erase] using renewed
    · simp [Entry.Value.erase]

theorem argument_cast_changes_readout (policy : Policy) :
    argumentAliasFrame.read policy (.var "x") = .var "y" ∧
    argumentCastFrame.read policy (.var "x") = .symbol "T" := by
  simp [Frame.read,Entry.Value.substitute,Entry.Value.resolve,argumentAliasFrame,argumentCastFrame,
    Entry.Value.Controls.aliasEnvironment,argumentCastEnvironment,List.lookup]

/-- The same alias theory uses an equality edge instead of a variable-valued
assignment, with its direction reversed. Its stored data is different. -/
def representedAliasBindings : Bindings := ⟨[], [("y", "x")]⟩

theorem alias_representation_agreement :
    BindingSourceAgreement argumentAliasFrame.bindings representedAliasBindings := by
  constructor
  · intro model
    simp [argumentAliasFrame, Entry.Value.Controls.aliasBindings, representedAliasBindings,
      TypeBindingSatisfied, applyTypeValuation, eq_comm]
  · intro name
    simp [argumentAliasFrame, Entry.Value.Controls.aliasBindings, representedAliasBindings,
      Spec.Bindings.ScopeObservation.specBindingVars, TypeSubst.typeVars, or_comm]

def representedAliasFrame : Frame :=
  argumentAliasFrame.represent representedAliasBindings alias_representation_agreement

theorem alias_representation_changes_record : representedAliasFrame ≠ argumentAliasFrame := by
  intro equal
  have assignments := congrArg (fun frame : Frame => frame.bindings.assignments) equal
  change [] = [("x", Atom.var "y")] at assignments
  cases assignments

/-- Even a held expression containing repeated aliases retains its complete
annotated read under every policy; erasure alone is not the claimed result. -/
theorem alias_representation_reads_whole_values (policy : Policy) (value : Entry.Value) :
    representedAliasFrame.read policy value = argumentAliasFrame.read policy value :=
  argumentAliasFrame.represent_read _ _ policy value

/-- Both future operations construct their reached frames from the source
conjunction. Restoring the annotated snapshot and adding raw native bindings
remain different operations, each independent of the input record format. -/
theorem alias_representation_future_operations (policy : Policy) :
    ∃ nativeAfter snapshotAfter : Frame,
      Frame.NativeRenewRel policy heldFrame.bindings argumentAliasFrame nativeAfter ∧
      Frame.NativeRenewRel policy heldFrame.bindings representedAliasFrame nativeAfter ∧
      Frame.SnapshotMergeRel policy argumentAliasFrame heldFrame snapshotAfter ∧
      Frame.SnapshotMergeRel policy representedAliasFrame heldFrame snapshotAfter := by
  let model : String → Atom := fun _ => Entry.Value.Controls.heldNested.erase
  have aliasModel : TypeBindingSatisfied model argumentAliasFrame.bindings := by
    simp [model, argumentAliasFrame, Entry.Value.Controls.aliasBindings,
      TypeBindingSatisfied, applyTypeValuation]
  have heldModel : TypeBindingSatisfied model heldFrame.bindings := by
    simp [model, heldFrame, Entry.Value.Controls.bindings, Entry.Value.Controls.heldNested,
      TypeBindingSatisfied, applyTypeValuation, Entry.Value.erase]
  have merged := Spec.Bindings.ScopeObservation.LogicalMergeRel.append_of_common_model
    ⟨model, aliasModel, heldModel⟩
  obtain ⟨nativeAfter, _, renewed⟩ :=
    Frame.NativeRenewRel.of_logical_merge (policy := policy) argumentAliasFrame merged.comm
  obtain ⟨snapshotAfter, _, restored⟩ :=
    Frame.SnapshotMergeRel.of_logical_merge (policy := policy) argumentAliasFrame heldFrame merged
  refine ⟨nativeAfter, snapshotAfter, renewed, ?_, restored, ?_⟩
  · exact (Frame.NativeRenewRel.represent_before_iff alias_representation_agreement).mpr renewed
  · have transported := (Frame.SnapshotMergeRel.represent_inputs_iff
      alias_representation_agreement (BindingSourceAgreement.refl heldFrame.bindings)).mpr restored
    simpa only [Frame.represent_self, representedAliasFrame] using transported

/-- Equal producer copies survive separately on both sides of the record
change. The inconsistent middle row is rejected by the source conjunction,
not by deduplicating or by treating unfinished work as failure. -/
theorem alias_representation_native_batch (policy : Policy) (dispatch : GroundedDispatch)
    (operator : Atom) (arguments : List Atom) (value : Entry.Value) :
    ∃ after : Frame,
      let incompatible : Bindings := ⟨[("x",.symbol "A"),("x",.symbol "B")],[]⟩
      let rows := [(value,heldFrame.bindings),(value,incompatible),(value,heldFrame.bindings)]
      let result : Result := (nativeValue policy dispatch operator arguments after value,after)
      NativeRowsRel policy dispatch operator arguments argumentAliasFrame rows [result,result] ∧
      NativeRowsRel policy dispatch operator arguments representedAliasFrame rows [result,result] := by
  obtain ⟨after,_snapshotAfter,renewed,_nativeTransport,_snapshot,_snapshotTransport⟩ :=
    alias_representation_future_operations policy
  let incompatible : Bindings := ⟨[("x",.symbol "A"),("x",.symbol "B")],[]⟩
  have impossible : ¬∃ output, Spec.Bindings.ScopeObservation.LogicalMergeRel
      incompatible argumentAliasFrame.bindings output := by
    rintro ⟨output,merged⟩
    obtain ⟨model,invalid,_callerModel⟩ := merged.common_model
    have first := invalid.1 "x" (.symbol "A") (by simp [incompatible])
    have second := invalid.1 "x" (.symbol "B") (by simp [incompatible])
    have distinct : Atom.symbol "A" = .symbol "B" := by
      simpa only [applyTypeValuation] using first.symm.trans second
    exact (by decide : ("A" : String) ≠ "B") (Atom.symbol.inj distinct)
  have source : NativeRowsRel policy dispatch operator arguments argumentAliasFrame
      [(value,heldFrame.bindings),(value,incompatible),(value,heldFrame.bindings)]
      [(nativeValue policy dispatch operator arguments after value,after),
        (nativeValue policy dispatch operator arguments after value,after)] :=
    .cons renewed (.rejected impossible (.cons renewed .nil))
  exact ⟨after,source,(NativeRowsRel.represent_before_iff alias_representation_agreement).mpr source⟩

/-- Equivalent erased tables do not permit replacing the annotated
environment: these two certified frames really have different read statuses. -/
theorem constraint_agreement_alone_does_not_preserve_readiness (policy : Policy) :
    ∃ activeFrame : Frame,
      BindingSourceAgreement heldFrame.bindings activeFrame.bindings ∧
      Entry.Value.eraseEnvironment heldFrame.environment =
        Entry.Value.eraseEnvironment activeFrame.environment ∧
      (heldFrame.read policy (.var "x")).status ≠ (activeFrame.read policy (.var "x")).status := by
  obtain ⟨same, certified, different⟩ := Entry.Value.Controls.constraint_certificate_does_not_determine_status
  let activeFrame : Frame := ⟨Entry.Value.Controls.bindings, Entry.Value.Controls.activeEnvironment, certified⟩
  refine ⟨activeFrame, .refl _, same.symm, ?_⟩
  simpa only [Frame.read, Entry.Value.substitute, heldFrame, activeFrame] using different.symm

theorem binding_changing_arguments (dispatch : GroundedDispatch) (policy : Policy) (live : List Atom) (scope : List String) :
    ArgumentsRel argumentTypeSpace dispatch rawLookup live scope
      [(.symbol "datum",.var "y"),(.var "x",Atom.atomType)] argumentAliasFrame
      [(Entry.Value.argumentPacket [.symbol "datum",.symbol "T"],argumentCastFrame)]
      (policy := policy) := by
  have tailChild : AtomRel argumentTypeSpace dispatch rawLookup (.symbol "datum" :: live) scope
      (.var "x") Atom.atomType argumentCastFrame [(.symbol "T",argumentCastFrame)] (policy := policy) := by
    have child := AtomRel.delivered (space := argumentTypeSpace) (dispatch := dispatch) (lookup := rawLookup)
      (live := .symbol "datum" :: live) (scope := scope) (value := .var "x") (expected := Atom.atomType)
      (frame := argumentCastFrame) (policy := policy)
      (Entry.atom_demand policy.reentry _ _)
    simpa only [(argument_cast_changes_readout policy).2] using child
  have tail : ArgumentsRel argumentTypeSpace dispatch rawLookup (.symbol "datum" :: live) scope
      [(.var "x",Atom.atomType)] argumentCastFrame
      [(Entry.Value.argumentPacket [.symbol "T"],argumentCastFrame)] (policy := policy) := by
    apply ArgumentsRel.cons tailChild
    have branches := ArgumentBranchesRel.continuing (live := .symbol "datum" :: live) (scope := scope)
      (original := .var "x") (requests := []) (heads := []) (policy := policy)
      (head := (.symbol "T",argumentCastFrame))
      (by simp [ArgumentStopped,IsEmptyOrErrorRel,IsErrorRel,Entry.Value.erase,Atom.empty])
      (ArgumentsRel.nil (space := argumentTypeSpace) (dispatch := dispatch) (lookup := rawLookup)
        (live := (Entry.Value.symbol "T").erase :: .symbol "datum" :: live) (scope := scope)
        (frame := argumentCastFrame) (policy := policy)) ArgumentBranchesRel.nil
    simpa only [List.map_cons,List.map_nil,List.append_nil,argumentPrepend_packet] using branches
  apply ArgumentsRel.cons (argument_cast_phase dispatch policy _ scope)
  have selectedTail : ArgumentsRel argumentTypeSpace dispatch rawLookup
      ((Entry.Value.symbol "datum").erase :: live) scope [(.var "x",Atom.atomType)] argumentCastFrame
      [(Entry.Value.argumentPacket [.symbol "T"],argumentCastFrame)] (policy := policy) := by
    simpa only [Entry.Value.erase] using tail
  have branches := ArgumentBranchesRel.continuing (live := live) (scope := scope)
    (original := .symbol "datum") (requests := [(.var "x",Atom.atomType)]) (heads := [])
    (policy := policy) (head := (.symbol "datum",argumentCastFrame))
    (by simp [ArgumentStopped]) selectedTail ArgumentBranchesRel.nil
  simpa only [List.map_cons,List.map_nil,List.append_nil,argumentPrepend_packet] using branches

def bindingChangingSignature : SelectedTypePolicy :=
  ⟨.expression [.symbol "->",.var "y",Atom.atomType,Atom.atomType],[.var "y",Atom.atomType],Atom.atomType,rfl⟩

/-- The typed function's assembly uses the frame reached by its arguments,
including an alias constrained by the first argument and read by the second. -/
theorem binding_changing_function (dispatch : GroundedDispatch) (policy : Policy) (live : List Atom) (scope : List String) :
    FunctionRel argumentTypeSpace dispatch rawLookup live scope Atom.undefinedType bindingChangingSignature
      (.var "op") [.symbol "datum",.var "x"] argumentAliasFrame
      [(.expression .active [.var "op",.symbol "datum",.symbol "T"],argumentCastFrame)] (policy := policy) := by
  have read : argumentAliasFrame.read policy (.var "op") = .var "op" := by
    simp [argumentAliasFrame,Frame.read,Entry.Value.substitute,Entry.Value.resolve,
      Entry.Value.Controls.aliasEnvironment,List.lookup]
  apply FunctionRel.evaluated (heads := [(.var "op",argumentAliasFrame)]) rfl
  · have child := AtomRel.delivered (space := argumentTypeSpace) (dispatch := dispatch) (lookup := rawLookup)
      (live := bindingChangingSignature.functionType :: [.symbol "datum",Entry.Value.var "x"].map Entry.Value.erase ++ live)
      (scope := scope ++ expectedApplicationScope
        (.expression ([Entry.Value.var "op",.symbol "datum",.var "x"].map Entry.Value.erase)) Atom.undefinedType)
      (value := .var "op") (frame := argumentAliasFrame) (policy := policy)
      (expected := bindingChangingSignature.functionType) (by
        rw [read]
        simpa only [Entry.Value.status,Entry.Value.erase] using
          (Entry.Rel.pass (policy := policy.reentry) (status := .active) (expected := bindingChangingSignature.functionType)
            (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) (.variable "op") (Or.inr (Or.inr rfl))))
    simpa only [read] using child
  · have tail := binding_changing_arguments dispatch policy ((Entry.Value.var "op").erase :: live) scope
    simpa [bindingChangingSignature,functionAssemble] using
      (FunctionBranchesRel.continuing (space := argumentTypeSpace) (dispatch := dispatch)
        (lookup := rawLookup) (live := live) (scope := scope) (policy := policy)
        (requests := [(.symbol "datum",.var "y"),(.var "x",Atom.atomType)])
        (head := (.var "op",argumentAliasFrame))
        (by simp [Entry.Value.erase,IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) tail .nil)

theorem argument_unify_candidate : UnifyCandidateRel (.var "y") (.symbol "T")
    argumentAliasFrame.bindings argumentCastFrame.bindings := by
  obtain ⟨_,matching,merged⟩ := argument_cast_match.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨_,matching,Spec.Bindings.ScopeObservation.LogicalMergeRel.comm (merged.logicalMerge argument_cast_model)⟩

def bindingChainBody : Entry.Value := .expression .active [
  .symbol "chain",.expression .active [.symbol "unify",.var "y",.symbol "T",.symbol "B",.symbol "refused"],
  .var "x",.expression .active [.symbol "return",.var "x"]]

theorem binding_chain_result (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom) :
    MinimalRel space dispatch lookup live scope caller bindingChainBody argumentAliasFrame
      [(.expression .active [.symbol "return",.symbol "B"],argumentCastFrame)] (policy := policy) := by
  apply MinimalRel.chain (selected := [(.symbol "B",argumentCastFrame)])
  · simpa only [Frame.read,Entry.Value.substitute] using
      (MinimalRel.unifyYes (space := space) (dispatch := dispatch) (lookup := lookup)
        (live := (.expression [.symbol "chain",
          (Entry.Value.expression .active [.symbol "unify",.var "y",.symbol "T",.symbol "B",.symbol "refused"]).erase,
          .var "x",(Entry.Value.expression .active [.symbol "return",.var "x"]).erase]) :: live)
        (scope := scope) (caller := some (.expression [.symbol "chain",
          (Entry.Value.expression .active [.symbol "unify",.var "y",.symbol "T",.symbol "B",.symbol "refused"]).erase,
          .var "x",(Entry.Value.expression .active [.symbol "return",.var "x"]).erase]))
        (readiness := .active) (target := .var "y") (pattern := .symbol "T")
        (frame := argumentAliasFrame) (output := argumentCastFrame)
        (yes := .symbol "B") (no := .symbol "refused") (policy := policy)
        (by simpa only [Entry.Value.erase] using argument_unify_candidate) (argument_cast_unification policy.rebuilding))
  · simpa only [List.append_nil,Frame.read,Entry.Value.substitute] using
      (BoundaryBatchRel.cons (head := (.symbol "B",argumentCastFrame))
        (chain_return_preserves_frame space dispatch lookup policy live scope caller "x" (.symbol "B") argumentCastFrame) .nil)

theorem binding_chain_function (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (policy : Policy) (live : List Atom) (scope : List String) (caller : Option Atom) :
    MinimalRel space dispatch lookup live scope caller (.expression .active [.symbol "function",bindingChainBody])
      argumentAliasFrame [(.symbol "B",argumentCastFrame)] (policy := policy) := by
  apply MinimalRel.function (raw := [(.expression .active [.symbol "return",.symbol "B"],argumentCastFrame)]) rfl
  · apply BodyRel.run (raw := [(.expression .active [.symbol "return",.symbol "B"],argumentCastFrame)])
    · exact binding_chain_result _ _ _ _ _ _ _
    · simpa only [List.append_nil,Frame.read_return_symbol] using
        (BoundaryBatchRel.cons (head := (.expression .active [.symbol "return",.symbol "B"],argumentCastFrame))
          (BoundaryRel.bodyTerminal (value := .expression .active [.symbol "return",.symbol "B"])
            (frame := argumentCastFrame) (policy := policy)
            (by simp [Frame.read_return_symbol,Entry.Value.erase,Minimal.embeddedInstruction])) .nil)
  · simpa only [List.append_nil] using
      (BoundaryBatchRel.cons (head := (.expression .active [.symbol "return",.symbol "B"],argumentCastFrame))
        (BoundaryRel.functionReturn (readiness := .active) (returned := .symbol "B") (frame := argumentCastFrame)) .nil)

theorem chain_caller_binding_survives (policy : Policy) :
    argumentCastFrame.read policy (.var "x") = .symbol "T" ∧
      argumentCastFrame.read policy (.var "x") ≠ .symbol "B" := by
  rw [(argument_cast_changes_readout policy).2]
  exact ⟨rfl,by intro impossible; have same := congrArg Entry.Value.erase impossible; simp [Entry.Value.erase] at same⟩

theorem held_variable_read : heldFrame.read .ready (.var "x") = Entry.Value.Controls.heldNested :=
  Entry.Value.Controls.nested_statuses_retained .preserve

/-- An actual full phase reads the bound value before choosing delivery.
No observation of the current world can reinterpret its held expression. -/
theorem held_variable_phase (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (live : List Atom) (scope : List String) (expected : Atom) :
    AtomRel space dispatch lookup live scope (.var "x") expected heldFrame
      [(Entry.Value.Controls.heldNested,heldFrame)] (policy := .ready) := by
  have completed := AtomRel.reuse_expression (space := space) (dispatch := dispatch) (lookup := lookup)
    (live := live) (scope := scope) (value := .var "x") (expected := expected)
    (frame := heldFrame) (policy := .ready)
    (children := [.symbol "Outer",.expression .held [.symbol "Inner"]])
    (by simpa only [Entry.Value.Controls.heldNested] using held_variable_read) rfl
  simpa only [held_variable_read] using completed

theorem held_variable_exact {space : Space} {dispatch : GroundedDispatch} {lookup : CastLookup}
    {live : List Atom} {scope : List String} {expected : Atom} {results : List Result}
    (completed : AtomRel space dispatch lookup live scope (.var "x") expected heldFrame results
      (policy := .ready)) : results = [(Entry.Value.Controls.heldNested,heldFrame)] := by
  have same := completed.reuse_expression_exact
    (children := [.symbol "Outer",.expression .held [.symbol "Inner"]])
    (by simpa only [Entry.Value.Controls.heldNested] using held_variable_read) rfl
  simpa only [held_variable_read] using same

/-- A complete ready-value phase cannot replace the held result with a
newly computed symbol, even if the world contains such a rewrite. -/
theorem held_variable_cannot_reinterpret (space : Space) (dispatch : GroundedDispatch) (lookup : CastLookup)
    (live : List Atom) (scope : List String) (expected : Atom) :
    ¬AtomRel space dispatch lookup live scope (.var "x") expected heldFrame
      [(.symbol "Restarted",heldFrame)] (policy := .ready) := by
  intro completed
  have same := held_variable_exact completed
  have heads := List.cons.inj same
  have values := congrArg (fun result : Result => result.1) heads.1
  cases values

/-! A raw type match can merge two independently consistent constraints into
an inconsistent cycle. This is a source-contract counterexample; no runtime
or binding-store representation is involved. -/

open Spec.Match.Merge Spec.Match.ModelTheory Spec.Type.RuntimeRefinement Spec.Type.Presentation

def cyclicInputEnvironment : Entry.Value.Environment :=
  [("x",.expression .active [.var "y"])]

theorem cyclic_input_certificate :
    ReadoutCertificate cyclicMergeLeft (Entry.Value.eraseEnvironment cyclicInputEnvironment) := by
  apply ReadoutCertificate.of_normal_theory
  · simp [cyclicInputEnvironment,Entry.Value.eraseEnvironment,Entry.Value.erase,
      TypeSubst.Normal,TypeSubst.keys,TypeSubst.typeVars,TypeSubst.typeVarsList]
  · intro valuation
    simp [Theory.TypeSubstSatisfied,TypeBindingSatisfied,cyclicMergeLeft,
      Bindings.empty,Bindings.assign,Bindings.isBound,Bindings.lookup,
      cyclicInputEnvironment,Entry.Value.eraseEnvironment,Entry.Value.erase]

def cyclicInputFrame : Frame :=
  ⟨cyclicMergeLeft,cyclicInputEnvironment,cyclic_input_certificate⟩

theorem cyclic_type_match :
    TypeMatchRel (.var "y") (.expression [.var "x"]) cyclicMergeLeft cyclicMergeOut := by
  refine .structural (by decide) (by decide) (by decide) (by decide) ?_ cyclicMerge_rel
  apply MatchRel.varNonVar rfl
  apply semanticLoopFree_single_assignment
  rw [atomOccurs_iff_mem_translated_vars]
  simp [Spec.Match.SolutionTheory.encodeModelAtom,Metta.Atom.vars]

theorem cyclic_output_has_no_finite_model :
    ¬∃ valuation : String → Atom, TypeBindingSatisfied valuation cyclicMergeOut := by
  rintro ⟨valuation,satisfied⟩
  exact cyclicMergeOut_has_no_model
    ⟨_,Spec.Bindings.ScopeObservation.ModelTransport.heBindingSatisfied_of_specTypeBindingSatisfied satisfied⟩

theorem cyclic_equation_has_no_common_model :
    ¬∃ valuation : String → Atom,
      TypeBindingSatisfied valuation cyclicMergeLeft ∧
      applyTypeValuation valuation (.var "y") =
        applyTypeValuation valuation (.expression [.var "x"]) := by
  rintro ⟨valuation,incoming,equation⟩
  apply cyclic_output_has_no_finite_model
  refine ⟨valuation,?_,?_⟩
  · intro name value present
    simp [cyclicMergeOut,cyclicMergeLeft,Bindings.empty,Bindings.assign,
      Bindings.isBound,Bindings.lookup] at present
    rcases present with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact incoming.1 _ _ (by
        simp [cyclicMergeLeft,Bindings.empty,Bindings.assign,Bindings.isBound,Bindings.lookup])
    · simpa only [applyTypeValuation] using equation
  · intro left right present
    simp [cyclicMergeOut,cyclicMergeLeft,Bindings.empty,Bindings.assign] at present

/-- Logical conjunction rejects every presentation of the cyclic success,
not just the particular raw merge record used by the counterexample. -/
theorem cyclic_logical_unification_rejected :
    ¬∃ output, UnifyCandidateRel (.var "y") (.expression [.var "x"])
      cyclicMergeLeft output := by
  rintro ⟨output,candidate⟩
  obtain ⟨matched,matching,merged⟩ := candidate
  obtain ⟨valuation,model⟩ := merged.2
  have constraints := (UnifyCandidateRel.solutions ⟨matched,matching,merged⟩ valuation).mp model
  exact cyclic_equation_has_no_common_model ⟨valuation,constraints.2,constraints.1⟩

theorem cyclic_unify_selects_else (thenBranch elseBranch : Atom) :
    UnifyStep (.var "y") (.expression [.var "x"]) thenBranch elseBranch
      cyclicMergeLeft elseBranch cyclicMergeLeft :=
  .noMatch (fun output candidate => cyclic_logical_unification_rejected ⟨output,candidate⟩)

/-- Adding the finite-model guard to raw type matching eliminates the whole
cyclic case, independently of representative spelling or merge chronology. -/
theorem cyclic_modelled_type_match_rejected :
    ¬∃ output, TypeMatchRel (.var "y") (.expression [.var "x"]) cyclicMergeLeft output ∧
      ∃ valuation : String → Atom, TypeBindingSatisfied valuation output := by
  rintro ⟨output,matched,model⟩
  obtain ⟨bindings,matching,merged⟩ := TypeMatchRel.structural_of_nonWildcard
    (by decide) (by decide) (by decide) (by decide) matched
  exact cyclic_logical_unification_rejected
    ⟨output,bindings,matching,Spec.Bindings.ScopeObservation.LogicalMergeRel.comm
      (merged.logicalMerge model)⟩

def cyclicTypeSpace : Space :=
  ⟨[.expression [.symbol ":",.symbol "datum",.expression [.var "x"]]]⟩

theorem cyclic_raw_cast :
    TypeCastBatchRel cyclicTypeSpace (.symbol "datum") (.var "y") cyclicInputFrame.bindings
      [(.symbol "datum",cyclicMergeOut)] := by
  apply TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
  · exact StorageTypesRel.symbolKnown (.hit .nil) (by decide)
  · rfl
  · simp
  · exact cyclic_type_match

theorem cyclic_cast_has_no_contextual_lift (policy : Policy) :
    ¬∃ results, List.Forall₂
      (CastResultRel policy (rawTypeLookupRel cyclicTypeSpace)
        cyclicInputFrame (.symbol "datum") (.var "y"))
      [(.symbol "datum",cyclicMergeOut)] results := by
  rintro ⟨results,paired⟩
  cases paired with
  | cons related rest => exact cyclic_output_has_no_finite_model related.model

/-- Wildcard casting remains valid in the very same nonempty activation.
The constraint, contextual payload and selected frame are all retained. -/
theorem wildcard_cast_retains_nonempty_frame (policy : Policy) :
    TypeCastBatchRel cyclicTypeSpace (.symbol "datum") Atom.undefinedType cyclicInputFrame.bindings
      [(.symbol "datum",cyclicInputFrame.bindings)] ∧
    List.Forall₂
      (CastResultRel policy (rawTypeLookupRel cyclicTypeSpace)
        cyclicInputFrame (.symbol "datum") Atom.undefinedType)
      [(.symbol "datum",cyclicInputFrame.bindings)] [(.symbol "datum",cyclicInputFrame)] := by
  constructor
  · apply TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
    · exact StorageTypesRel.symbolKnown (.hit .nil) (by decide)
    · rfl
    · simp
    · exact .undefinedLeft _ _
  · exact .cons ⟨by simp only [rawResult,Entry.Value.erase],.same _,
      by simp [Entry.Value.erase]⟩ .nil

def fallbackTypeSpace : Space :=
  ⟨cyclicTypeSpace.atoms ++ [.expression [.symbol ":",.symbol "datum",Atom.undefinedType]]⟩

/-- The raw profile commits to the first syntactically successful type,
even though its constraint record has no finite model. -/
theorem raw_cast_selects_cyclic_first :
    TypeCastBatchRel fallbackTypeSpace (.symbol "datum") (.var "y") cyclicInputFrame.bindings
      [(.symbol "datum",cyclicMergeOut)] := by
  apply TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [Atom.undefinedType])
  · exact StorageTypesRel.symbolKnown (.hit (.hit .nil)) (by decide)
  · rfl
  · simp
  · exact cyclic_type_match

/-- The finite profile rejects the cyclic first candidate and selects the
later wildcard in the same query, preserving the incoming activation. -/
theorem finite_cast_skips_cyclic_first :
    TypeCastBatchRel fallbackTypeSpace (.symbol "datum") (.var "y") cyclicInputFrame.bindings
      [(.symbol "datum",cyclicInputFrame.bindings)] (matching := TypeMatchingPolicy.Rel .finite) := by
  apply TypeCastBatchRel.success (earlierTypes := [.expression [.var "x"]]) (laterTypes := [])
  · exact StorageTypesRel.symbolKnown (.hit (.hit .nil)) (by decide)
  · rfl
  · intro actual present output matched
    obtain rfl := List.mem_singleton.mp present
    exact cyclic_modelled_type_match_rejected ⟨output,matched⟩
  · exact ⟨.undefinedRight _ _,cyclic_input_certificate.satisfiable⟩

theorem finite_cast_phase (dispatch : GroundedDispatch) (live : List Atom) (scope : List String) :
    AtomRel fallbackTypeSpace dispatch rawLookup live scope (.symbol "datum") (.var "y") cyclicInputFrame
      [(.symbol "datum",cyclicInputFrame)] (policy := .finiteTypes) := by
  have read : cyclicInputFrame.read .finiteTypes (.symbol "datum") = .symbol "datum" := by
    simp [Frame.read,Entry.Value.substitute]
  apply AtomRel.cast (raw := [(.symbol "datum",cyclicInputFrame.bindings)])
  · simpa only [read,Entry.Value.erase,Entry.Value.status] using
      (Entry.Rel.cast (policy := Policy.finiteTypes.reentry) (status := .active)
        (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) (.symbol "datum") (by decide)
        (Or.inl ⟨"datum",rfl⟩) (by intro impossible; cases impossible))
  · simpa only [Frame.read,Entry.Value.substitute,Entry.Value.erase,rawLookup,
      Policy.finiteTypes,Policy.ready]
      using finite_cast_skips_cyclic_first
  · exact .cons ⟨by simp only [rawResult,Entry.Value.erase],.same _,
      by simp [read,Entry.Value.erase]⟩ .nil

end Controls

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed


namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type Spec.Eval.Steps
open Mettapedia.Machines.OrderedProtocol.Completion

set_option autoImplicit false

/-- Primitive snapshot storage and lookup preserve complete logical frames.
They receive no child evaluator or continuation. Their representation and
lifetime laws are separate profile/realization obligations. -/
structure SnapshotServices (Context World : Type) where
  capture : Context → World → Frame → GroundedValue → World → Prop
  restore : Context → World → GroundedValue → Frame → Prop

/-- Laws of an immutable snapshot service. Capturing a new frame keeps older
handles valid; capture does not restore the world's former program state. -/
structure SnapshotServices.Laws {Context World : Type} (services : SnapshotServices Context World) : Prop where
  roundtrip : ∀ {label world frame payload afterWorld}, services.capture label world frame payload afterWorld →
    services.restore label afterWorld payload frame
  functional : ∀ {label world payload first second}, services.restore label world payload first →
    services.restore label world payload second → first = second
  persistent : ∀ {label world frame payload afterWorld}, services.capture label world frame payload afterWorld →
    ∀ {other token captured}, services.restore other world token captured → services.restore other afterWorld token captured

/-- A mathematical snapshot instance keeps the program world separate from
an append-only list of immutable full frames. No native layout is prescribed. -/
def SnapshotServices.appendModel (Context Base : Type) : SnapshotServices Context (Base × List Frame) where
  capture _ before frame payload after :=
    payload = .int before.2.length ∧ after = (before.1,before.2 ++ [frame])
  restore _ world payload frame :=
    ∃ index : Nat, payload = .int index ∧ world.2[index]? = some frame

theorem SnapshotServices.appendModel_laws (Context Base : Type) : Laws (appendModel Context Base) := by
  constructor
  · intro label before frame payload after captured
    obtain ⟨rfl,rfl⟩ := captured
    refine ⟨before.2.length,rfl,?_⟩
    rw [List.getElem?_append_right (Nat.le_refl _)]
    simp
  · intro label world payload first second left right
    obtain ⟨i,firstPayload,firstRead⟩ := left
    obtain ⟨j,secondPayload,secondRead⟩ := right
    have same : i = j := by simpa using GroundedValue.int.inj (firstPayload.symm.trans secondPayload)
    cases same
    exact Option.some.inj (firstRead.symm.trans secondRead)
  · intro label before frame payload after captured other token saved earlier
    obtain ⟨_payload,rfl⟩ := captured
    obtain ⟨index,encoded,read⟩ := earlier
    obtain ⟨bound,_value⟩ := List.getElem?_eq_some_iff.mp read
    exact ⟨index,encoded,by simpa only [List.getElem?_append_left bound] using read⟩

theorem SnapshotServices.appendModel_total (Context Base : Type) (label : Context)
    (before : Base × List Frame) (frame : Frame) :
    ∃ payload after, (appendModel Context Base).capture label before frame payload after :=
  ⟨.int before.2.length,(before.1,before.2 ++ [frame]),rfl,rfl⟩

theorem SnapshotServices.appendModel_preserves_base {Context Base : Type}
    {label : Context} {before after : Base × List Frame} {frame payload}
    (captured : (appendModel Context Base).capture label before frame payload after) : after.1 = before.1 := by
  obtain ⟨_payload,rfl⟩ := captured
  rfl

/-- Finite capture retains its reversed encoded prefix at every cut. Only
final Empty occurrences are omitted; errors and duplicate values survive. -/
inductive CaptureRowsRel {Context World : Type} (services : SnapshotServices Context World) (label : Context) :
    World → List Result → List Entry.Value → Entry.Value → World → Prop where
  | nil {world saved} : CaptureRowsRel services label world [] saved (.expression .active saved.reverse) world
  | empty {world head tail saved packed afterWorld} : head.1.erase = Atom.empty →
      CaptureRowsRel services label world tail saved packed afterWorld →
      CaptureRowsRel services label world (head :: tail) saved packed afterWorld
  | cons {world nextWorld afterWorld head tail payload saved packed} : head.1.erase ≠ Atom.empty →
      services.capture label world head.2 payload nextWorld →
      CaptureRowsRel services label nextWorld tail (.expression .active [head.1,.grounded payload] :: saved) packed afterWorld →
      CaptureRowsRel services label world (head :: tail) saved packed afterWorld

theorem CaptureRowsRel.preserves {Context World : Type} {services : SnapshotServices Context World}
    (laws : services.Laws) {label world rows saved packed afterWorld other token captured}
    (source : CaptureRowsRel services label world rows saved packed afterWorld)
    (earlier : services.restore other world token captured) : services.restore other afterWorld token captured := by
  revert earlier
  induction source with
  | nil => exact fun earlier => earlier
  | empty _ _ ih => exact ih
  | cons _ stored _ ih => exact fun earlier => ih (laws.persistent stored earlier)

/-- A capture traversal is total whenever its local snapshot primitive is
available for every frame. Its input is a completed child batch; termination
of the child evaluation remains a separate source premise. -/
theorem CaptureRowsRel.total {Context World : Type} (services : SnapshotServices Context World)
    (available : ∀ label world frame, ∃ payload after, services.capture label world frame payload after)
    (label : Context) (world : World) (rows : List Result) (saved : List Entry.Value) :
    ∃ packed after, CaptureRowsRel services label world rows saved packed after := by
  classical
  induction rows generalizing world saved with
  | nil => exact ⟨_,world,.nil⟩
  | cons head tail ih =>
      by_cases missing : head.1.erase = Atom.empty
      · obtain ⟨packed,after,rest⟩ := ih world saved
        exact ⟨packed,after,.empty missing rest⟩
      · obtain ⟨payload,next,stored⟩ := available label world head.2
        obtain ⟨packed,after,rest⟩ := ih next (.expression .active [head.1,.grounded payload] :: saved)
        exact ⟨packed,after,.cons missing stored rest⟩

theorem CaptureRowsRel.appendModel_preserves_base {Context Base : Type} {label : Context}
    {before after : Base × List Frame} {rows saved packed}
    (source : CaptureRowsRel (SnapshotServices.appendModel Context Base) label before rows saved packed after) :
    after.1 = before.1 := by
  induction source with
  | nil => rfl
  | empty _ _ ih => exact ih
  | cons _ stored _ ih => exact ih.trans (SnapshotServices.appendModel_preserves_base stored)

def survivingRows (rows : List Result) : List Result :=
  rows.filter (fun row => row.1.erase != Atom.empty)

/-- A stored pair keeps the exact annotated value and restores its complete
logical frame at the reached world. -/
def StoredPairRel {Context World : Type} (services : SnapshotServices Context World) (label : Context)
    (world : World) (row : Result) (pair : Entry.Value) : Prop :=
  ∃ payload, pair = .expression .active [row.1,.grounded payload] ∧ services.restore label world payload row.2

/-- Capture represents each surviving physical occurrence once. The saved
prefix is retained in order, and later allocations keep earlier rows valid. -/
theorem CaptureRowsRel.encoded {Context World : Type} {services : SnapshotServices Context World}
    (laws : services.Laws) {label world rows saved packed afterWorld}
    (source : CaptureRowsRel services label world rows saved packed afterWorld) :
    ∃ pairs, packed = .expression .active (saved.reverse ++ pairs) ∧
      List.Forall₂ (StoredPairRel services label afterWorld) (survivingRows rows) pairs := by
  induction source with
  | nil => exact ⟨[],by simp,List.Forall₂.nil⟩
  | empty missing _ ih =>
      obtain ⟨pairs,shaped,paired⟩ := ih
      exact ⟨pairs,shaped,by simpa [survivingRows,missing] using paired⟩
  | @cons world nextWorld afterWorld head tail payload saved packed present stored rest ih =>
      obtain ⟨pairs,shaped,paired⟩ := ih
      refine ⟨.expression .active [head.1,.grounded payload] :: pairs,?_,?_⟩
      · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using shaped
      · simpa [survivingRows,present] using
          (List.Forall₂.cons
            (show StoredPairRel services label afterWorld head (.expression .active [head.1,.grounded payload]) from
              ⟨payload,rfl,rest.preserves laws (laws.roundtrip stored)⟩) paired)

theorem CaptureRowsRel.occurrences {Context World : Type} {services : SnapshotServices Context World}
    (laws : services.Laws) {label world rows packed afterWorld}
    (source : CaptureRowsRel services label world rows [] packed afterWorld) :
    ∃ pairs, packed = .expression .active pairs ∧ pairs.length = (survivingRows rows).length := by
  obtain ⟨pairs,shaped,paired⟩ := source.encoded laws
  exact ⟨pairs,by simpa only [List.reverse_nil,List.nil_append] using shaped,paired.length_eq.symm⟩

/-- Restore every encoded occurrence before returning the primitive batch.
An incompatible finite binding conjunction drops only that occurrence. -/
inductive RestoreRowsRel {Context World : Type} (services : SnapshotServices Context World) (label : Context)
    (world : World) (policy : Policy) (caller : Frame) : List Entry.Value → List Result → List Result → Prop where
  | nil {saved} : RestoreRowsRel services label world policy caller [] saved saved.reverse
  | cons {readiness value payload captured output tail saved results} :
      services.restore label world payload captured → Frame.SnapshotMergeRel policy captured caller output →
      RestoreRowsRel services label world policy caller tail ((value,output) :: saved) results →
      RestoreRowsRel services label world policy caller
        (.expression readiness [value,.grounded payload] :: tail) saved results
  | rejected {readiness value payload captured tail saved results} :
      services.restore label world payload captured →
      (¬∃ output, Spec.Bindings.ScopeObservation.LogicalMergeRel captured.bindings caller.bindings output) →
      RestoreRowsRel services label world policy caller tail saved results →
      RestoreRowsRel services label world policy caller
        (.expression readiness [value,.grounded payload] :: tail) saved results

/-- The caller's annotated environment, rather than a particular constraint
record orientation, determines finite snapshot restoration. Payload lookup,
the saved prefix, duplicate occurrences and every reached frame are retained. -/
theorem RestoreRowsRel.represent_caller_iff
    {Context World : Type} {services : SnapshotServices Context World}
    {label world policy caller pairs saved results} {bindings : Bindings}
    (agreement : BindingSourceAgreement caller.bindings bindings) :
    RestoreRowsRel services label world policy
        (caller.represent bindings agreement) pairs saved results ↔
      RestoreRowsRel services label world policy caller pairs saved results := by
  have merge_iff (captured output : Frame) :
      Frame.SnapshotMergeRel policy captured (caller.represent bindings agreement) output ↔
        Frame.SnapshotMergeRel policy captured caller output := by
    simpa only [Frame.represent_self] using
      (Frame.SnapshotMergeRel.represent_inputs_iff
        (BindingSourceAgreement.refl captured.bindings) agreement (output := output))
  constructor
  · intro source
    induction source with
    | nil => exact .nil
    | cons loaded merged _ ih => exact .cons loaded ((merge_iff _ _).mp merged) ih
    | rejected loaded impossible _ ih =>
        refine .rejected loaded (fun ⟨output,merged⟩ => impossible ⟨output,?_⟩) ih
        exact (Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
          (BindingSourceAgreement.refl _) agreement).mp merged
  · intro source
    induction source with
    | nil => exact .nil
    | cons loaded merged _ ih => exact .cons loaded ((merge_iff _ _).mpr merged) ih
    | rejected loaded impossible _ ih =>
        refine .rejected loaded (fun ⟨output,merged⟩ => impossible ⟨output,?_⟩) ih
        exact (Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
          (BindingSourceAgreement.refl _) agreement).mpr merged

/-- Restoring into an empty caller reconstructs every stored row exactly,
including annotations and aliases. This is a genuine traversal of the encoded
pair list, not a decoder supplied with the desired result. -/
theorem RestoreRowsRel.of_stored_empty {Context World : Type} {services : SnapshotServices Context World}
    {label world policy rows pairs saved}
    (paired : List.Forall₂ (StoredPairRel services label world) rows pairs) :
    RestoreRowsRel services label world policy Frame.empty pairs saved (saved.reverse ++ rows) := by
  induction paired generalizing saved with
  | nil => simpa only [List.append_nil] using (RestoreRowsRel.nil (saved := saved))
  | cons relation _ ih =>
      obtain ⟨payload,rfl,loaded⟩ := relation
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
        RestoreRowsRel.cons loaded (Frame.SnapshotMergeRel.emptyCaller policy _) (ih (saved := _ :: saved))

theorem CaptureRowsRel.restore_roundtrip {Context World : Type} {services : SnapshotServices Context World}
    (laws : services.Laws) {label world rows packed afterWorld policy}
    (source : CaptureRowsRel services label world rows [] packed afterWorld) :
    ∃ pairs, packed = .expression .active pairs ∧
      RestoreRowsRel services label afterWorld policy Frame.empty pairs [] (survivingRows rows) := by
  obtain ⟨pairs,shaped,paired⟩ := source.encoded laws
  exact ⟨pairs,by simpa only [List.reverse_nil,List.nil_append] using shaped,
    by simpa only [List.reverse_nil,List.nil_append] using RestoreRowsRel.of_stored_empty (saved := []) paired⟩

/-- Decoding a captured pair list constructs the complete finite restore
traversal for any caller, retaining or rejecting every binding conjunction. -/
theorem RestoreRowsRel.total {Context World : Type} {services : SnapshotServices Context World}
    {label world rows pairs} (paired : List.Forall₂ (StoredPairRel services label world) rows pairs)
    (policy : Policy) (caller : Frame) (saved : List Result) :
    ∃ results, RestoreRowsRel services label world policy caller pairs saved results := by
  classical
  induction paired generalizing saved with
  | nil => exact ⟨saved.reverse,.nil⟩
  | @cons row pair rows pairs relation paired ih =>
      obtain ⟨payload,rfl,loaded⟩ := relation
      by_cases possible : ∃ output,
          Spec.Bindings.ScopeObservation.LogicalMergeRel row.2.bindings caller.bindings output
      · obtain ⟨output,merged⟩ := possible
        obtain ⟨after,_same,renewed⟩ := Frame.SnapshotMergeRel.of_logical_merge row.2 caller merged
        obtain ⟨results,rest⟩ := ih ((row.1,after) :: saved)
        exact ⟨results,.cons loaded renewed rest⟩
      · obtain ⟨results,rest⟩ := ih saved
        exact ⟨results,.rejected loaded possible rest⟩

/-- A compatible snapshot cannot be silently rejected or lose a duplicate.
The codec's functional law identifies the actual frame loaded by each step. -/
theorem RestoreRowsRel.length_eq_of_compatible {Context World : Type} {services : SnapshotServices Context World}
    (laws : services.Laws) {label world rows pairs policy caller saved results}
    (paired : List.Forall₂ (StoredPairRel services label world) rows pairs)
    (compatible : ∀ row ∈ rows,
      ∃ output, Spec.Bindings.ScopeObservation.LogicalMergeRel row.2.bindings caller.bindings output)
    (source : RestoreRowsRel services label world policy caller pairs saved results) :
    results.length = saved.length + rows.length := by
  induction paired generalizing saved results with
  | nil => cases source; simp
  | @cons row pair rows pairs relation paired ih =>
      obtain ⟨payload,rfl,stored⟩ := relation
      cases source with
      | cons loaded merged rest =>
          have length := ih (fun row member => compatible row (List.mem_cons_of_mem _ member)) rest
          simp only [List.length_cons] at length ⊢
          omega
      | rejected loaded impossible rest =>
          have same := laws.functional stored loaded
          cases same
          exact False.elim (impossible (compatible _ List.mem_cons_self))

/-- Host data and the local completed-operation contract. The contract sees
one native invocation and its logical activation, not the evaluator's control
or caller stack. Executing or refining that host service is a separate law. -/
structure WorldServices (Context World : Type) where
  contextPayload : Context → GroundedValue
  nativeCall : Context → World → Atom → Atom → Atom → Frame → List Result → World → Prop
  snapshots : Option (SnapshotServices Context World) := none
  /-- One annotated grounded application and its primitive outcome. The
  contract receives no caller stack or expected return type. Binding renewal,
  function completion and caller return remain language work. -/
  groundedCall : Context → World → Entry.Value → GroundedResult Entry.Value → World → Prop :=
    fun _ _ _ _ _ => False
  /-- A generative local host may additionally use the logical activation
  and protected syntax to earn freshness of emitted code. It receives no
  caller stack, expected return type, or recursive evaluator. -/
  scopedGroundedCall : Option (Context → World → List Atom → List String → Frame →
    Entry.Value → GroundedResult Entry.Value → World → Prop) := none

/-- Late method fallback preserves record updates to the original service.
No default callback captures a prior value of groundedCall. -/
abbrev WorldServices.groundedAt {Context World : Type} (services : WorldServices Context World)
    (label : Context) (world : World) (live : List Atom) (scope : List String) (frame : Frame)
    (call : Entry.Value) (outcome : GroundedResult Entry.Value) (after : World) : Prop :=
  match services.scopedGroundedCall with
  | none => services.groundedCall label world call outcome after
  | some scopedCall => scopedCall label world live scope frame call outcome after

/-- The old read-only profile has no completed native-operation rule. Its
context payload still uses the supplied snapshot service. -/
def WorldServices.readOnly (services : Spec.Eval.Minimal.Services) : WorldServices Space Unit where
  contextPayload := services.contextPayload
  nativeCall := fun _ _ _ _ _ _ _ _ => False

/-- Fresh-syntax read-only producers instantiate the annotated primitive
contract from the existing bare-atom dispatch. Other hosts may preserve
annotations of arguments they return. -/
def WorldServices.readOnlyGrounded (services : Minimal.Services) (dispatch : GroundedDispatch) :
    WorldServices Space Unit :=
  { WorldServices.readOnly services with
    groundedCall := fun _ _ call outcome _ =>
      ∃ operator arguments raw, call.erase = .expression (operator :: arguments) ∧
        dispatch.outcome operator arguments raw ∧ outcome = raw.map Entry.Value.ofAtom }

theorem groundedResult_erase_ofAtom (result : GroundedResult) :
    (result.map Entry.Value.ofAtom).map Entry.Value.erase = result := by
  rw [GroundedResult.map_comp]
  have inverse : Entry.Value.erase ∘ Entry.Value.ofAtom = id := funext Entry.Value.erase_ofAtom
  rw [inverse,GroundedResult.map_id]

/-- Erasing the fresh-syntax producer recovers its exact original outcome,
including bindings, failures and duplicate positions. -/
theorem WorldServices.readOnlyGrounded_erasure {services : Minimal.Services} {dispatch : GroundedDispatch}
    {label world call outcome afterWorld}
    (produced : (WorldServices.readOnlyGrounded services dispatch).groundedCall label world call outcome afterWorld) :
    ∃ operator arguments, call.erase = .expression (operator :: arguments) ∧
      dispatch.outcome operator arguments (outcome.map Entry.Value.erase) := by
  obtain ⟨operator,arguments,raw,shaped,executed,rfl⟩ := produced
  exact ⟨operator,arguments,shaped,by simpa only [groundedResult_erase_ofAtom] using executed⟩

/-- One applicability operand is checked without evaluating it. The role
receives the reached frame and the independent inferred-type lookup; it may
earn a kind cut without demanding that lookup. This is not a value cast. -/
abbrev ArgumentAdmission := Space → TypeLookupRel → Policy →
  Atom → Atom → Atom → Nat → Frame → List Frame → List Atom → Prop

/-- Visit every incoming occurrence, retaining its admission/error block. -/
inductive AdmissionFramesRel (admit : ArgumentAdmission) (space : Space)
    (lookup : TypeLookupRel) (policy : Policy) (expression argument expected : Atom)
    (position : Nat) : List Frame → List Frame → List Atom → Prop where
  | nil : AdmissionFramesRel admit space lookup policy expression argument expected position [] [] []
  | cons {before rest selected outputs errors later} :
      admit space lookup policy expression argument expected position before selected errors →
      AdmissionFramesRel admit space lookup policy expression argument expected position rest outputs later →
      AdmissionFramesRel admit space lookup policy expression argument expected position (before :: rest)
        (selected ++ outputs) (errors ++ later)

inductive AdmissionArgumentsRel (admit : ArgumentAdmission) (space : Space)
    (lookup : TypeLookupRel) (policy : Policy) :
    Atom → Nat → List Atom → List Atom → List Frame → List Frame → List Atom → Prop where
  | nil {expression position frames} :
      AdmissionArgumentsRel admit space lookup policy expression position [] [] frames frames []
  | cons {expression position argument arguments expected expecteds before next after errors later} :
      AdmissionFramesRel admit space lookup policy expression argument expected position before next errors →
      AdmissionArgumentsRel admit space lookup policy expression (position + 1) arguments expecteds next after later →
      AdmissionArgumentsRel admit space lookup policy expression position
        (argument :: arguments) (expected :: expecteds) before after (errors ++ later)

/-- Argument admission is replaceable; the reached return-type check is the
same contextual check as in the historical source profile. -/
inductive AdmissionApplicationRel (admit : ArgumentAdmission) (space : Space)
    (lookup : TypeLookupRel) (policy : Policy) (expression expected : Atom)
    (selected : SelectedTypePolicy) (before : Frame) : List Frame → List Atom → Prop where
  | wrongArity {operator arguments} :
      expression = .expression (operator :: arguments) →
      arguments.length ≠ selected.argumentTypes.length →
      AdmissionApplicationRel admit space lookup policy expression expected selected before []
        [mkError expression .incorrectNumberOfArguments]
  | checked {operator arguments afterArguments errors returnChecks} :
      expression = .expression (operator :: arguments) →
      AdmissionArgumentsRel admit space lookup policy expression 1 arguments selected.argumentTypes
        [before] afterArguments errors →
      List.Forall₂ (fun frame check => TypeCheckRel policy expected frame selected.returnType check)
        afterArguments returnChecks →
      AdmissionApplicationRel admit space lookup policy expression expected selected before
        (checkedFrames returnChecks)
        (errors ++ (checkedFailures returnChecks).map (fun actual => mkError expression (.badType expected actual)))

inductive AdmissionScanRel (admit : ArgumentAdmission) (space : Space)
    (lookup : TypeLookupRel) (policy : Policy) (expression expected : Atom)
    (before : Frame) : List Atom → InvocationSelection → Prop where
  | nil : AdmissionScanRel admit space lookup policy expression expected before [] (.exhausted [] false)
  | nonFunction {candidate candidates outcome} :
      (¬∃ domains returned, FunctionTypeRel candidate domains returned) →
      AdmissionScanRel admit space lookup policy expression expected before candidates outcome →
      AdmissionScanRel admit space lookup policy expression expected before (candidate :: candidates)
        (match outcome with
          | .selected signature frames => .selected signature frames
          | .exhausted errors _ => .exhausted errors true)
  | selected {signature : SelectedTypePolicy} {candidates frames errors} :
      AdmissionApplicationRel admit space lookup policy expression expected signature before frames errors →
      frames ≠ [] →
      AdmissionScanRel admit space lookup policy expression expected before (signature.functionType :: candidates)
        (.selected signature frames)
  | rejected {signature : SelectedTypePolicy} {candidates errors outcome} :
      AdmissionApplicationRel admit space lookup policy expression expected signature before [] errors →
      AdmissionScanRel admit space lookup policy expression expected before candidates outcome →
      AdmissionScanRel admit space lookup policy expression expected before (signature.functionType :: candidates)
        (match outcome with
          | .selected signature frames => .selected signature frames
          | .exhausted later tupleEligible => .exhausted (errors ++ later) tupleEligible)

/-- The historical complete-query profile remains an explicit instance.
An operand-role profile changes only static applicability, not value casts,
operator queries, recursive evaluation, or the continuation machine. -/
inductive ArgumentService where
  | historical
  | role (admit : ArgumentAdmission)

abbrev ArgumentService.selection (service : ArgumentService) (space : Space)
    (lookup : CastLookup) (policy : Policy) (live : List Atom) (scope : List String)
    (expression operator expected : Atom) (before : Frame) (outcome : InvocationSelection) : Prop :=
  match service with
  | .historical => InvocationSelectionRel space lookup policy live scope expression operator expected before outcome
  | .role admit => ∃ candidates,
      lookup (invocationTypeScope scope live expression expected before.bindings) space
        before.bindings operator Atom.undefinedType candidates ∧
      AdmissionScanRel admit space
        (lookup (invocationTypeScope scope live expression expected before.bindings) space)
        policy expression expected before candidates outcome

/-- A context identifies a mutable space. Its current contents come from the
reached world. Only local host operations may change that world; neither
bindings nor saved alternatives contain a private copy of it. -/
structure WorldEnvironment (Context World : Type) where
  view : World → Context → Space
  services : WorldServices Context World
  dispatch : GroundedDispatch
  lookup : CastLookup
  arguments : ArgumentService := .historical

/-- The existing read-only source profile is a world instance with no
native operation and with space values as context labels. -/
def WorldEnvironment.readOnly (services : Minimal.Services) (dispatch : GroundedDispatch)
    (lookup : CastLookup) : WorldEnvironment Space Unit where
  view := fun _ => id
  services := WorldServices.readOnly services
  dispatch := dispatch
  lookup := lookup

/-! Completed source evaluation threads one world through children in
exploration order. Equation frontiers are captured at invocation; their
remaining occurrences are not re-queried after a child changes the world.
The pure entry, unification, type, readout and publication judgments above
are reused without any dependency on machine control. -/
namespace Stateful

variable {Context World : Type}

mutual
inductive AtomRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → Entry.Value → Atom → Frame → List Result →
      World → (policy : Policy := Policy.unmarked) → Prop where
  | delivered {label world0 live scope value expected frame policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .deliver →
      AtomRel environment label world0 live scope value expected frame
        [(frame.read policy value,frame)] world0 (policy := policy)
  | cast {label world0 live scope value expected frame raw results policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .cast →
      TypeCastBatchRel (environment.view world0 label) (frame.read policy value).erase expected frame.bindings raw
        (lookup := environment.lookup (invocationTypeScope scope live
          (frame.read policy value).erase expected frame.bindings) (environment.view world0 label))
        (matching := policy.matching.Rel) →
      List.Forall₂ (CastResultRel policy
        (environment.lookup (invocationTypeScope scope live (frame.read policy value).erase expected frame.bindings) (environment.view world0 label))
        frame (frame.read policy value) expected) raw results →
      AtomRel environment label world0 live scope value expected frame results world0 (policy := policy)
  | tuple {label world0 world1 world2 live scope value expected frame readiness operator arguments rows raw selected policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .interpret →
      frame.read policy value = .expression readiness (operator :: arguments) →
      TypeOccurrencesRel ((environment.view world0 label).atoms : Multiset Atom)
        operator.erase {Atom.undefinedType} →
      TupleRel environment label world0 (expected :: live) scope (operator :: arguments) frame rows
        world1 (policy := policy) →
      CallsRel environment label world1 live scope expected rows raw world2 (policy := policy) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (readResult policy)) selected →
      AtomRel environment label world0 live scope value expected frame
        (selected.map (publishResult policy (frame.read policy value).erase)) world2 (policy := policy)
  | function {label world0 world1 live scope value expected frame readiness operator arguments signature frames raw selected policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .interpret →
      frame.read policy value = .expression readiness (operator :: arguments) →
      environment.arguments.selection (environment.view world0 label) environment.lookup policy live scope (frame.read policy value).erase operator.erase
        expected frame (.selected signature frames) →
      InvocationsRel environment label world0 live scope expected signature operator arguments frames raw world1 (policy := policy) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (readResult policy)) selected →
      AtomRel environment label world0 live scope value expected frame
        (selected.map (publishResult policy (frame.read policy value).erase)) world1 (policy := policy)
  | fallback {label world0 world1 world2 live scope value expected frame readiness operator arguments errors rows raw selected policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .interpret →
      frame.read policy value = .expression readiness (operator :: arguments) →
      environment.arguments.selection (environment.view world0 label) environment.lookup policy live scope (frame.read policy value).erase operator.erase
        expected frame (.exhausted errors true) →
      TupleRel environment label world0 (expected :: live) scope (operator :: arguments) frame rows world1 (policy := policy) →
      CallsRel environment label world1 live scope expected rows raw world2 (policy := policy) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        ((raw ++ diagnosticResults errors frame).map (readResult policy)) selected →
      AtomRel environment label world0 live scope value expected frame
        (selected.map (publishResult policy (frame.read policy value).erase)) world2 (policy := policy)
  | selectionFailed {label world0 live scope value expected frame readiness operator arguments errors selected policy} :
      Entry.Rel policy.reentry (frame.read policy value).status
        (frame.read policy value).erase expected .interpret →
      frame.read policy value = .expression readiness (operator :: arguments) →
      environment.arguments.selection (environment.view world0 label) environment.lookup policy live scope (frame.read policy value).erase operator.erase
        expected frame (.exhausted errors false) →
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        ((diagnosticResults errors frame).map (readResult policy)) selected →
      AtomRel environment label world0 live scope value expected frame
        (selected.map (publishResult policy (frame.read policy value).erase)) world0 (policy := policy)

inductive TupleRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → List Entry.Value → Frame → List Result →
      World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope frame policy} :
      TupleRel environment label world0 live scope [] frame
        [(.expression .active [],frame)] world0 (policy := policy)
  | singleton {label world0 world1 live scope value frame heads policy} :
      AtomRel environment label world0 live scope value Atom.undefinedType frame heads world1 (policy := policy) →
      TupleRel environment label world0 live scope [value] frame
        (heads.map tupleSingleton) world1 (policy := policy)
  | cons {label world0 world1 world2 live scope head second remaining frame heads results policy} :
      AtomRel environment label world0
        (.expression ((second :: remaining).map Entry.Value.erase) :: live) scope
        head Atom.undefinedType frame heads world1 (policy := policy) →
      TupleBranchesRel environment label world1 live scope (second :: remaining) heads results world2 (policy := policy) →
      TupleRel environment label world0 live scope (head :: second :: remaining) frame results world2 (policy := policy)

inductive TupleBranchesRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → List Entry.Value → List Result → List Result →
      World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope tail policy} :
      TupleBranchesRel environment label world0 live scope tail [] [] world0 (policy := policy)
  | stopped {label world0 world1 live scope tail head heads rest policy} :
      IsEmptyOrErrorRel head.1.erase →
      TupleBranchesRel environment label world0 live scope tail heads rest world1 (policy := policy) →
      TupleBranchesRel environment label world0 live scope tail (head :: heads) (head :: rest) world1 (policy := policy)
  | continuing {label world0 world1 world2 live scope tail head heads children rest policy} :
      ¬IsEmptyOrErrorRel head.1.erase →
      TupleRel environment label world0 (head.1.erase :: live) scope tail head.2 children world1 (policy := policy) →
      TupleBranchesRel environment label world1 live scope tail heads rest world2 (policy := policy) →
      TupleBranchesRel environment label world0 live scope tail (head :: heads)
        (children.map (tuplePrepend head.1) ++ rest) world2 (policy := policy)

inductive ArgumentsRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → List ArgumentRequest → Frame → List Result →
      World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope frame policy} :
      ArgumentsRel environment label world0 live scope [] frame
        [(Entry.Value.argumentPacket [],frame)] world0 (policy := policy)
  | cons {label world0 world1 world2 live scope request requests frame heads results policy} :
      AtomRel environment label world0 (argumentScope requests ++ live) scope
        request.1 request.2 frame heads world1 (policy := policy) →
      ArgumentBranchesRel environment label world1 live scope request.1 requests heads results world2 (policy := policy) →
      ArgumentsRel environment label world0 live scope (request :: requests) frame results world2 (policy := policy)

inductive ArgumentBranchesRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → Entry.Value → List ArgumentRequest → List Result → List Result →
      World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope original requests policy} :
      ArgumentBranchesRel environment label world0 live scope original requests [] [] world0 (policy := policy)
  | stopped {label world0 world1 live scope original requests head heads rest policy} :
      ArgumentStopped original head →
      ArgumentBranchesRel environment label world0 live scope original requests heads rest world1 (policy := policy) →
      ArgumentBranchesRel environment label world0 live scope original requests (head :: heads)
        (head :: rest) world1 (policy := policy)
  | continuing {label world0 world1 world2 live scope original requests head heads children rest policy} :
      ¬ArgumentStopped original head →
      ArgumentsRel environment label world0 (head.1.erase :: live) scope requests head.2 children world1 (policy := policy) →
      ArgumentBranchesRel environment label world1 live scope original requests heads rest world2 (policy := policy) →
      ArgumentBranchesRel environment label world0 live scope original requests (head :: heads)
        (children.map (argumentPrepend head.1) ++ rest) world2 (policy := policy)

inductive FunctionRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → Atom → SelectedTypePolicy → Entry.Value → List Entry.Value →
      Frame → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | evaluated {label world0 world1 world2 live scope expected signature operator arguments frame heads results policy} :
      arguments.length = signature.argumentTypes.length →
      AtomRel environment label world0 (signature.functionType :: arguments.map Entry.Value.erase ++ live)
        (scope ++ expectedApplicationScope (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
        operator signature.functionType frame heads world1 (policy := policy) →
      FunctionBranchesRel environment label world1 live scope
        (arguments.zip signature.argumentTypes) heads results world2 (policy := policy) →
      FunctionRel environment label world0 live scope expected signature operator arguments frame results world2 (policy := policy)

inductive FunctionBranchesRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → List ArgumentRequest → List Result → List Result →
      World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope requests policy} :
      FunctionBranchesRel environment label world0 live scope requests [] [] world0 (policy := policy)
  | stopped {label world0 world1 live scope requests head heads rest policy} :
      IsEmptyOrErrorRel head.1.erase →
      FunctionBranchesRel environment label world0 live scope requests heads rest world1 (policy := policy) →
      FunctionBranchesRel environment label world0 live scope requests (head :: heads) (head :: rest) world1 (policy := policy)
  | continuing {label world0 world1 world2 live scope requests head heads children rest policy} :
      ¬IsEmptyOrErrorRel head.1.erase →
      ArgumentsRel environment label world0 (head.1.erase :: live) scope requests head.2 children world1 (policy := policy) →
      FunctionBranchesRel environment label world1 live scope requests heads rest world2 (policy := policy) →
      FunctionBranchesRel environment label world0 live scope requests (head :: heads)
        (children.map (functionAssemble head.1) ++ rest) world2 (policy := policy)

inductive InvocationsRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → Atom → SelectedTypePolicy → Entry.Value → List Entry.Value →
      List Frame → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope expected signature operator arguments policy} :
      InvocationsRel environment label world0 live scope expected signature operator arguments [] [] world0 (policy := policy)
  | cons {label world0 world1 world2 world3 live scope expected signature operator arguments frame frames interpreted called rest policy} :
      FunctionRel environment label world0 (invocationReturnType signature :: live) scope expected signature operator
        arguments frame interpreted world1 (policy := policy) →
      CallsRel environment label world1 live scope (invocationReturnType signature) interpreted called world2 (policy := policy) →
      InvocationsRel environment label world2 live scope expected signature operator arguments frames rest world3 (policy := policy) →
      InvocationsRel environment label world0 live scope expected signature operator arguments (frame :: frames)
        (called ++ rest) world3 (policy := policy)

inductive CallsRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → Atom → List Result → List Result →
      World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope expected policy} :
      CallsRel environment label world0 live scope expected [] [] world0 (policy := policy)
  | cons {label world0 world1 world2 live scope expected head heads children rest policy} :
      CallRel environment label world0 live scope head.1 expected head.2 children world1 (policy := policy) →
      CallsRel environment label world1 live scope expected heads rest world2 (policy := policy) →
      CallsRel environment label world0 live scope expected (head :: heads) (children ++ rest) world2 (policy := policy)

inductive CallRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → Entry.Value → Atom → Frame → List Result →
      World → (policy : Policy := Policy.unmarked) → Prop where
  | error {label world0 live scope value expected frame policy} :
      IsErrorRel value.erase →
      CallRel environment label world0 live scope value expected frame [(value,frame)] world0 (policy := policy)
  | embedded {label world0 world1 world2 live scope value expected frame raw results policy} :
      ¬IsErrorRel value.erase →
      ¬Minimal.HostCall environment.dispatch value.erase →
      Minimal.embeddedInstruction value.erase = true →
      InvocationRel environment label world0 (expected :: live) scope none value frame raw world1 (policy := policy) →
      BoundaryBatchRel environment label world1 live scope none (.returned value expected) raw results world2 (policy := policy) →
      CallRel environment label world0 live scope value expected frame results world2 (policy := policy)
  | absent {label world0 live scope value expected frame policy} :
      ¬IsErrorRel value.erase →
      NonGroundedCallRel environment.dispatch value.erase →
      EquationFrontierRel (environment.view world0 label) (expected :: live) value.erase frame.bindings [] →
      CallRel environment label world0 live scope value expected frame [(value,frame)] world0 (policy := policy)
  | equations {label world0 world1 live scope value expected frame works results policy} :
      ¬IsErrorRel value.erase →
      NonGroundedCallRel environment.dispatch value.erase →
      EquationFrontierRel (environment.view world0 label) (expected :: live) value.erase frame.bindings works →
      works ≠ [] →
      EquationBodiesRel environment label world0 live scope value expected frame works results world1 (policy := policy) →
      CallRel environment label world0 live scope value expected frame results world1 (policy := policy)
  | groundedDone {label world0 world1 live scope value expected frame operator arguments outcome results policy} :
      value.erase = .expression (operator :: arguments) → environment.dispatch.executable operator →
      ¬IsErrorRel value.erase →
      environment.services.groundedAt label world0 live scope frame value outcome world1 →
      NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) frame outcome (.done results) →
      CallRel environment label world0 live scope value expected frame results world1 (policy := policy)
  | groundedResume {label world0 world1 world2 live scope value expected frame operator arguments outcome rows results policy} :
      value.erase = .expression (operator :: arguments) → environment.dispatch.executable operator →
      ¬IsErrorRel value.erase →
      environment.services.groundedAt label world0 live scope frame value outcome world1 →
      NativeOutcomeRel policy environment.dispatch operator arguments value (some expected) frame outcome (.resume rows) →
      BoundaryBatchRel environment label world1 live scope none
        (.native value (some expected) (environment.dispatch.valueProvenance operator arguments)) rows results world2 (policy := policy) →
      CallRel environment label world0 live scope value expected frame results world2 (policy := policy)

inductive EquationBodiesRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → Entry.Value → Atom → Frame →
      List EquationWork → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope original expected frame policy} :
      EquationBodiesRel environment label world0 live scope original expected frame [] [] world0 (policy := policy)
  | cons {label world0 world1 world2 world3 live scope original expected frame work works output children rest policy produced} :
      output.bindings = work.bindings →
      Entry.Value.UnifyRel policy.rebuilding frame.environment original (Entry.Value.ofAtom work.pattern)
        output.environment →
      BoundaryRel environment label world0 (expected :: live) scope (some original.erase) .producer
        (output.read policy (Entry.Value.ofAtom work.body)) output produced world1 (policy := policy) →
      BoundaryBatchRel environment label world1 live scope none (.returned original expected) produced children world2 (policy := policy) →
      EquationBodiesRel environment label world2 live scope original expected frame works rest world3 (policy := policy) →
      EquationBodiesRel environment label world0 live scope original expected frame (work :: works)
        (children ++ rest) world3 (policy := policy)

inductive ReturnRel (environment : WorldEnvironment Context World) : Context → World →
    List Atom → List String → Entry.Value → Atom → Entry.Value → Frame →
      List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | notReducible {label world0 live scope original expected value frame policy} :
      value.erase = Atom.notReducible →
      ReturnRel environment label world0 live scope original expected value frame [(original,frame)] world0 (policy := policy)
  | stopped {label world0 live scope original expected value frame policy} :
      IsEmptyOrErrorRel value.erase →
      ReturnRel environment label world0 live scope original expected value frame [(value,frame)] world0 (policy := policy)
  | evaluate {label world0 world1 live scope original expected value frame results policy} :
      value.erase ≠ Atom.notReducible →
      ¬IsEmptyOrErrorRel value.erase →
      AtomRel environment label world0 live scope value expected frame results world1 (policy := policy) →
      ReturnRel environment label world0 live scope original expected value frame results world1 (policy := policy)

inductive MinimalRel (environment : WorldEnvironment Context World) : Context → World → List Atom → List String → Option Atom →
    Entry.Value → Frame → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | data {label world0 live scope caller value frame policy} :
      Minimal.embeddedInstruction value.erase = false →
      MinimalRel environment label world0 live scope caller value frame [(value,frame)] world0 (policy := policy)
  | eval {label world0 world1 live scope caller readiness operand frame results policy} :
      InvocationRel environment label world0 live scope caller (frame.read policy operand) frame results world1 (policy := policy) →
      MinimalRel environment label world0 live scope caller (.expression readiness [.symbol "eval",operand]) frame results world1 (policy := policy)
  | chain {label world0 world1 world2 live scope caller readiness operand name template frame selected results policy} :
      MinimalRel environment label world0
        ((.expression [.symbol "chain",operand.erase,.var name,template.erase]) :: live) scope
        (some (.expression [.symbol "chain",operand.erase,.var name,template.erase])) operand frame selected world1 (policy := policy) →
      BoundaryBatchRel environment label world1 live scope caller (.chain name template) selected results world2 (policy := policy) →
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "chain",operand,.var name,template]) frame results world2 (policy := policy)
  | unifyYes {label world0 live scope caller readiness target pattern yes no frame output policy} :
      UnifyCandidateRel target.erase pattern.erase frame.bindings output.bindings →
      Entry.Value.UnifyRel policy.rebuilding frame.environment target pattern output.environment →
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "unify",target,pattern,yes,no]) frame
        [(output.read policy yes,output)] world0 (policy := policy)
  | unifyNo {label world0 live scope caller readiness target pattern yes no frame policy} :
      UnifyNoMatchRel target.erase pattern.erase frame.bindings →
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "unify",target,pattern,yes,no]) frame [(no,frame)] world0 (policy := policy)
  | unifyBadArity {label world0 live scope caller readiness tail frame policy} :
      tail.length ≠ 4 →
      MinimalRel environment label world0 live scope caller (.expression readiness (.symbol "unify" :: tail)) frame
        [(Entry.Value.ofAtom (mkErrorMessage (.expression (.symbol "unify" :: tail.map Entry.Value.erase))
          (environment.dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail.map Entry.Value.erase)))),frame)] world0 (policy := policy)
  | consAtom {label world0 live scope caller readiness tailReadiness head tail frame policy} :
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "cons-atom",head,.expression tailReadiness tail]) frame
        [(.expression .active (head :: tail),frame)] world0 (policy := policy)
  | deconsAtom {label world0 live scope caller readiness valueReadiness head tail frame policy} :
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "decons-atom",.expression valueReadiness (head :: tail)]) frame
        [(.expression .active [head,.expression .active tail],frame)] world0 (policy := policy)
  | function {label world0 world1 world2 live scope caller readiness body bodyReadiness children frame raw results policy} :
      body = .expression bodyReadiness children →
      BodyRel environment label world0 ((.expression [.symbol "function",body.erase]) :: live) scope
        (some (.expression [.symbol "function",body.erase])) body frame raw world1 (policy := policy) →
      BoundaryBatchRel environment label world1 live scope caller .functionDone raw results world2 (policy := policy) →
      MinimalRel environment label world0 live scope caller (.expression readiness [.symbol "function",body]) frame results world2 (policy := policy)
  | evalc {label childLabel world0 world1 live scope caller readiness operand frame results policy} :
      InvocationRel environment childLabel world0 live scope caller
        (frame.read policy operand) frame results world1 (policy := policy) →
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "evalc",operand,.grounded (environment.services.contextPayload childLabel)])
        frame results world1 (policy := policy)
  | metta {label childLabel world0 world1 live scope caller readiness operand expected frame results policy} :
      AtomRel environment childLabel world0 live scope operand expected.erase frame results world1 (policy := policy) →
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "metta",operand,expected,.grounded (environment.services.contextPayload childLabel)])
        frame results world1 (policy := policy)
  | contextSpace {label world0 live scope caller readiness frame policy} :
      MinimalRel environment label world0 live scope caller (.expression readiness [.symbol "context-space"])
        frame [(.grounded (environment.services.contextPayload label),frame)] world0 (policy := policy)
  | native {label world0 world1 live scope caller readiness name function arguments frame results policy} :
      environment.services.nativeCall label world0 name.erase function.erase arguments.erase frame results world1 →
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "call-native",name,function,arguments]) frame results world1 (policy := policy)
  | collapseBind {label world0 world1 world2 live scope caller readiness operand frame children packed snapshots policy} :
      environment.services.snapshots = some snapshots →
      MinimalRel environment label world0 live scope caller operand frame children world1 (policy := policy) →
      CaptureRowsRel snapshots label world1 children [] packed world2 →
      MinimalRel environment label world0 live scope caller (.expression readiness [.symbol "collapse-bind",operand])
        frame [(packed,frame)] world2 (policy := policy)
  | superposeBind {label world0 live scope caller readiness tupleReadiness pairs frame results snapshots policy} :
      environment.services.snapshots = some snapshots →
      RestoreRowsRel snapshots label world0 policy frame pairs [] results →
      MinimalRel environment label world0 live scope caller
        (.expression readiness [.symbol "superpose-bind",.expression tupleReadiness pairs]) frame results world0 (policy := policy)

inductive BodyRel (environment : WorldEnvironment Context World) : Context → World → List Atom → List String → Option Atom →
    Entry.Value → Frame → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | run {label world0 world1 world2 live scope caller value frame raw results policy} :
      MinimalRel environment label world0 live scope caller value frame raw world1 (policy := policy) →
      BoundaryBatchRel environment label world1 live scope caller .body raw results world2 (policy := policy) →
      BodyRel environment label world0 live scope caller value frame results world2 (policy := policy)

inductive InvocationRel (environment : WorldEnvironment Context World) : Context → World → List Atom → List String → Option Atom →
    Entry.Value → Frame → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | embedded {label world0 world1 live scope caller value frame results policy} :
      ¬Minimal.HostCall environment.dispatch value.erase →
      Minimal.embeddedInstruction value.erase = true →
      MinimalRel environment label world0 live scope caller value frame results world1 (policy := policy) →
      InvocationRel environment label world0 live scope caller value frame results world1 (policy := policy)
  | absent {label world0 live scope caller value frame policy} :
      NonGroundedCallRel environment.dispatch value.erase →
      EquationFrontierRel (environment.view world0 label) live value.erase frame.bindings [] →
      InvocationRel environment label world0 live scope caller value frame [(.symbol "NotReducible",frame)] world0 (policy := policy)
  | equations {label world0 world1 live scope caller value frame works results policy} :
      NonGroundedCallRel environment.dispatch value.erase →
      EquationFrontierRel (environment.view world0 label) live value.erase frame.bindings works →
      works ≠ [] →
      InvocationEquationsRel environment label world0 live scope value frame works results world1 (policy := policy) →
      InvocationRel environment label world0 live scope caller value frame results world1 (policy := policy)
  | groundedDone {label world0 world1 live scope caller value frame operator arguments outcome results policy} :
      value.erase = .expression (operator :: arguments) → environment.dispatch.executable operator →
      environment.services.groundedAt label world0 live scope frame value outcome world1 →
      NativeOutcomeRel policy environment.dispatch operator arguments value none frame outcome (.done results) →
      InvocationRel environment label world0 live scope caller value frame results world1 (policy := policy)
  | groundedResume {label world0 world1 world2 live scope caller value frame operator arguments outcome rows results policy} :
      value.erase = .expression (operator :: arguments) → environment.dispatch.executable operator →
      environment.services.groundedAt label world0 live scope frame value outcome world1 →
      NativeOutcomeRel policy environment.dispatch operator arguments value none frame outcome (.resume rows) →
      BoundaryBatchRel environment label world1 live scope caller
        (.native value none (environment.dispatch.valueProvenance operator arguments)) rows results world2 (policy := policy) →
      InvocationRel environment label world0 live scope caller value frame results world2 (policy := policy)

inductive InvocationEquationsRel (environment : WorldEnvironment Context World) : Context → World → List Atom → List String →
    Entry.Value → Frame → List EquationWork → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope original frame policy} :
      InvocationEquationsRel environment label world0 live scope original frame [] [] world0 (policy := policy)
  | cons {label world0 world1 world2 live scope original frame work works output children rest policy} :
      output.bindings = work.bindings →
      Entry.Value.UnifyRel policy.rebuilding frame.environment original (Entry.Value.ofAtom work.pattern) output.environment →
      BoundaryRel environment label world0 live scope (some original.erase) .producer
        (output.read policy (Entry.Value.ofAtom work.body)) output children world1 (policy := policy) →
      InvocationEquationsRel environment label world1 live scope original frame works rest world2 (policy := policy) →
      InvocationEquationsRel environment label world0 live scope original frame (work :: works) (children ++ rest) world2 (policy := policy)

inductive BoundaryRel (environment : WorldEnvironment Context World) : Context → World → List Atom → List String → Option Atom →
    Boundary → Entry.Value → Frame → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | chain {label world0 world1 live scope caller name template value frame results policy} :
      MinimalRel environment label world0 live scope caller
        (substituteBinder policy name (frame.read policy value) template) frame results world1 (policy := policy) →
      BoundaryRel environment label world0 live scope caller (.chain name template) value frame results world1 (policy := policy)
  | bodyTerminal {label world0 live scope caller value frame policy} :
      Minimal.embeddedInstruction (frame.read policy value).erase = false →
      BoundaryRel environment label world0 live scope caller .body value frame [(frame.read policy value,frame)] world0 (policy := policy)
  | bodyResume {label world0 world1 live scope caller value frame results policy} :
      Minimal.embeddedInstruction (frame.read policy value).erase = true →
      BodyRel environment label world0 live scope caller (frame.read policy value) frame results world1 (policy := policy) →
      BoundaryRel environment label world0 live scope caller .body value frame results world1 (policy := policy)
  | functionReturn {label world0 live scope caller readiness returned frame policy} :
      BoundaryRel environment label world0 live scope caller .functionDone
        (.expression readiness [.symbol "return",returned]) frame [(returned,frame)] world0 (policy := policy)
  | functionNoReturn {label world0 live scope caller value frame policy} :
      (∀ returned, value.erase ≠ .expression [.symbol "return",returned]) →
      BoundaryRel environment label world0 live scope caller .functionDone value frame
        [(Entry.Value.ofAtom (Minimal.functionTerminalResult caller value.erase),frame)] world0 (policy := policy)
  | producerRaw {label world0 live scope caller value frame policy} :
      ¬FunctionPending policy value →
      BoundaryRel environment label world0 live scope caller .producer value frame [(value,frame)] world0 (policy := policy)
  | producerFunction {label world0 world1 live scope caller value frame results policy} :
      FunctionPending policy value →
      MinimalRel environment label world0 live scope caller value frame results world1 (policy := policy) →
      BoundaryRel environment label world0 live scope caller .producer value frame results world1 (policy := policy)
  | returned {label world0 world1 live scope caller original expected value frame results policy} :
      ReturnRel environment label world0 live scope original expected value frame results world1 (policy := policy) →
      BoundaryRel environment label world0 live scope caller (.returned original expected) value frame results world1 (policy := policy)
  | nativeEmittedRaw {label world0 world1 live scope caller original value frame results policy} :
      BoundaryRel environment label world0 live scope (some original.erase) .producer value frame results world1 (policy := policy) →
      BoundaryRel environment label world0 live scope caller (.native original none .emitted) value frame results world1 (policy := policy)
  | nativeEmittedReturn {label world0 world1 world2 live scope caller original expected value frame produced results policy} :
      BoundaryRel environment label world0 (expected :: live) scope (some original.erase) .producer value frame produced world1 (policy := policy) →
      BoundaryBatchRel environment label world1 live scope caller (.returned original expected) produced results world2 (policy := policy) →
      BoundaryRel environment label world0 live scope caller (.native original (some expected) .emitted) value frame results world2 (policy := policy)
  | nativeCompletedRaw {label world0 live scope caller original value frame policy} :
      BoundaryRel environment label world0 live scope caller (.native original none .completed) value frame [(value,frame)] world0 (policy := policy)
  | nativeCompletedReturn {label world0 live scope caller original expected value frame results policy} :
      NativeCompletedReturnRel (environment.view world0 label)
        (environment.lookup (invocationTypeScope scope live original.erase expected frame.bindings) (environment.view world0 label))
        policy value expected frame results →
      BoundaryRel environment label world0 live scope caller (.native original (some expected) .completed) value frame results world0 (policy := policy)

inductive BoundaryBatchRel (environment : WorldEnvironment Context World) : Context → World → List Atom → List String → Option Atom →
    Boundary → List Result → List Result → World → (policy : Policy := Policy.unmarked) → Prop where
  | nil {label world0 live scope caller boundary policy} :
      BoundaryBatchRel environment label world0 live scope caller boundary [] [] world0 (policy := policy)
  | cons {label world0 world1 world2 live scope caller boundary head heads children rest policy} :
      BoundaryRel environment label world0 live scope caller boundary head.1 head.2 children world1 (policy := policy) →
      BoundaryBatchRel environment label world1 live scope caller boundary heads rest world2 (policy := policy) →
      BoundaryBatchRel environment label world0 live scope caller boundary (head :: heads) (children ++ rest) world2 (policy := policy)

end

theorem BoundaryBatchRel.single_iff {Context World : Type} {environment : WorldEnvironment Context World}
    {label world live scope caller site value frame results afterWorld policy} :
    BoundaryBatchRel environment label world live scope caller site [(value,frame)] results afterWorld (policy := policy) ↔
      BoundaryRel environment label world live scope caller site value frame results afterWorld (policy := policy) := by
  constructor
  · intro source
    cases source with
    | cons child tail =>
        cases tail
        simpa only [List.append_nil] using child
  · intro child
    simpa only [List.append_nil] using BoundaryBatchRel.cons child .nil

/-- The actual chain/collapse/superpose program restores every surviving
child occurrence with its full frame. It resumes in the reached world. -/
theorem MinimalRel.collection_roundtrip {Context World : Type} {environment : WorldEnvironment Context World}
    {snapshots : SnapshotServices Context World} (provided : environment.services.snapshots = some snapshots)
    (laws : snapshots.Laws) {label world childWorld afterWorld live scope caller operand rows packed policy}
    (child : MinimalRel environment label world ((collectionReplay operand).erase :: live) scope
      (some (collectionReplay operand).erase) operand Frame.empty rows childWorld (policy := policy))
    (captured : CaptureRowsRel snapshots label childWorld rows [] packed afterWorld) :
    MinimalRel environment label world live scope caller (collectionReplay operand) Frame.empty
      (survivingRows rows) afterWorld (policy := policy) := by
  obtain ⟨pairs,rfl,restored⟩ := captured.restore_roundtrip laws
  refine .chain (world1 := afterWorld) (selected := [(.expression .active pairs,Frame.empty)])
    (.collapseBind provided (by simpa [collectionReplay,Entry.Value.erase] using child) captured) ?_
  apply BoundaryBatchRel.single_iff.mpr
  apply BoundaryRel.chain
  simpa only [Frame.read_empty,substituteBinder_superpose] using
    (MinimalRel.superposeBind (environment := environment) (policy := policy)
      (readiness := .active) provided restored)

end Stateful

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed


namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Controls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type

/-- A local model operation supplies arbitrary rows and increments only the
program counter. Snapshot storage is an independent logical service. -/
def snapshotRowsServices (rows : List Result) : WorldServices Unit (Nat × List Frame) where
  contextPayload _ := .int 0
  nativeCall _ before name function arguments _ output after :=
    name = .symbol "rows" ∧ function = .symbol "emit" ∧ arguments = .expression [] ∧
      output = rows ∧ after = (before.1 + 1,before.2)
  snapshots := some (SnapshotServices.appendModel Unit Nat)

def snapshotRowsEnvironment (rows : List Result) : WorldEnvironment Unit (Nat × List Frame) :=
  ⟨fun _ _ => Space.empty,snapshotRowsServices rows,typedDispatch,rawLookup,.historical⟩

def snapshotRowsCall : Entry.Value :=
  .expression .active [.symbol "call-native",.symbol "rows",.symbol "emit",.expression .active []]

theorem collection_source (policy : Policy) (world : Nat × List Frame) (rows : List Result)
    (live : List Atom) (scope : List String) (caller : Option Atom) :
    ∃ after, Stateful.MinimalRel (snapshotRowsEnvironment rows) () world live scope caller
      (collectionReplay snapshotRowsCall) Frame.empty (survivingRows rows) after (policy := policy) ∧
      after.1 = world.1 + 1 := by
  obtain ⟨packed,after,captured⟩ := CaptureRowsRel.total (SnapshotServices.appendModel Unit Nat)
    (SnapshotServices.appendModel_total Unit Nat) () (world.1 + 1,world.2) rows []
  refine ⟨after,Stateful.MinimalRel.collection_roundtrip rfl
    (SnapshotServices.appendModel_laws Unit Nat) ?_ captured,captured.appendModel_preserves_base⟩
  exact .native (by simp [snapshotRowsEnvironment,snapshotRowsServices,Entry.Value.erase])

theorem collection_duplicates (policy : Policy) (world : Nat × List Frame) (value : Entry.Value)
    (frame : Frame) (present : value.erase ≠ Atom.empty) :
    ∃ after, Stateful.MinimalRel (snapshotRowsEnvironment [(value,frame),(value,frame)]) () world [] [] none
      (collectionReplay snapshotRowsCall) Frame.empty [(value,frame),(value,frame)] after (policy := policy) ∧
      after.1 = world.1 + 1 := by
  simpa [survivingRows,present] using collection_source policy world [(value,frame),(value,frame)] [] [] none

/-- An invalid lookup is not a completed empty collection. -/
theorem invalid_snapshot_not_failure (policy : Policy) (base : Nat) (value : Entry.Value)
    (caller : Frame) (results : List Result) :
    ¬RestoreRowsRel (SnapshotServices.appendModel Unit Nat) () (base,[]) policy caller
      [.expression .active [value,.grounded (.int 0)]] [] results := by
  intro restored
  cases restored with
  | cons loaded _ _ | rejected loaded _ _ =>
      obtain ⟨index,_payload,read⟩ := loaded
      simp at read

/-- A model producer changes one counter exactly once and supplies only its
primitive outcome. It has no caller stack or recursive evaluator input. -/
def nativeServices (outcome : GroundedResult Entry.Value) : WorldServices Unit Nat where
  contextPayload _ := .int 0
  nativeCall := fun _ _ _ _ _ _ _ _ => False
  groundedCall _ before call produced after :=
    call = .expression .active [.symbol "host"] ∧ produced = outcome ∧ after = before + 1

def nativeDispatch (outcome : GroundedResult Entry.Value) (provenance : NativeValueProvenance) : GroundedDispatch where
  executable operator := operator = .symbol "host"
  outcome operator arguments result :=
    operator = .symbol "host" ∧ arguments = [] ∧ result = outcome.map Entry.Value.erase
  valueProvenance := fun _ _ => provenance

def nativeEnvironment (outcome : GroundedResult Entry.Value) (provenance : NativeValueProvenance) :
    WorldEnvironment Unit Nat :=
  ⟨fun _ _ => Space.empty,nativeServices outcome,nativeDispatch outcome provenance,rawLookup,.historical⟩

def nativeCallValue : Entry.Value := .expression .active [.symbol "host"]
def nativeFunctionBody : Entry.Value := .expression .active [.symbol "return",.symbol "Kept"]
def nativeFunctionValue : Entry.Value := .expression .active [.symbol "function",nativeFunctionBody]

theorem native_producer_erasure {outcome provenance before call produced after}
    (executed : (nativeServices outcome).groundedCall () before call produced after) :
    (nativeDispatch outcome provenance).outcome (.symbol "host") [] (produced.map Entry.Value.erase) ∧
      after = before + 1 := by
  obtain ⟨_call,rfl,reached⟩ := executed
  exact ⟨⟨rfl,rfl,rfl⟩,reached⟩

theorem native_rows_single (policy : Policy) (outcome : GroundedResult Entry.Value)
    (provenance : NativeValueProvenance) (value : Entry.Value) :
    NativeRowsRel policy (nativeDispatch outcome provenance) (.symbol "host") [] Frame.empty
      [(value,Bindings.empty)] [(value,Frame.empty)] :=
  .cons (Frame.NativeRenewRel.empty policy Frame.empty) .nil

private theorem native_function_pending (policy : Policy) : FunctionPending policy nativeFunctionValue := by
  refine ⟨?_,Or.inr rfl⟩
  refine ⟨nativeFunctionBody.erase,?_⟩
  simp [nativeFunctionValue,Entry.Value.erase]

theorem native_function_minimal (policy : Policy) (outcome : GroundedResult Entry.Value)
    (provenance : NativeValueProvenance) (world : Nat) (live : List Atom) (scope : List String) (caller : Option Atom) :
    Stateful.MinimalRel (nativeEnvironment outcome provenance) () world live scope caller nativeFunctionValue Frame.empty
      [(.symbol "Kept",Frame.empty)] world (policy := policy) := by
  refine .function (world1 := world) (raw := [(nativeFunctionBody,Frame.empty)]) rfl ?_ ?_
  · refine .run (world1 := world) (raw := [(nativeFunctionBody,Frame.empty)])
      (.data (by simp [nativeFunctionBody,Entry.Value.erase,Minimal.embeddedInstruction])) ?_
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    simpa only [Frame.read_empty] using
      (Stateful.BoundaryRel.bodyTerminal (value := nativeFunctionBody) (frame := Frame.empty) (policy := policy)
        (by simp [nativeFunctionBody,Entry.Value.erase,Minimal.embeddedInstruction]))
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .functionReturn

theorem native_completed_raw_source (policy : Policy) (value : Entry.Value) (world : Nat) :
    Stateful.InvocationRel (nativeEnvironment (.ok [(value,Bindings.empty)]) .completed) () world [] [] none
      nativeCallValue Frame.empty [(value,Frame.empty)] (world + 1) (policy := policy) := by
  refine .groundedResume (operator := .symbol "host") (arguments := [])
    (outcome := .ok [(value,Bindings.empty)]) (rows := [(value,Frame.empty)]) (world1 := world + 1)
    ?_ rfl ⟨rfl,rfl,rfl⟩ (.success (native_rows_single policy _ _ value)) ?_
  · simp [nativeCallValue,Entry.Value.erase]
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .nativeCompletedRaw

theorem native_completed_full_source (policy : Policy) (value : Entry.Value) (world : Nat) :
    Stateful.CallRel (nativeEnvironment (.ok [(value,Bindings.empty)]) .completed) () world [] []
      nativeCallValue Atom.atomType Frame.empty [(value,Frame.empty)] (world + 1) (policy := policy) := by
  refine .groundedResume (operator := .symbol "host") (arguments := [])
    (outcome := .ok [(value,Bindings.empty)]) (rows := [(value,Frame.empty)]) (world1 := world + 1)
    ?_ rfl ?_ ⟨rfl,rfl,rfl⟩ (.success (native_rows_single policy _ _ value)) ?_
  · simp [nativeCallValue,Entry.Value.erase]
  · simp [nativeCallValue,Entry.Value.erase,IsErrorRel]
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .nativeCompletedReturn (.keep (Or.inr (Or.inr (Or.inl rfl))))

theorem native_emitted_raw_source (policy : Policy) (world : Nat) :
    Stateful.InvocationRel (nativeEnvironment (.ok [(nativeFunctionValue,Bindings.empty)]) .emitted) () world [] [] none
      nativeCallValue Frame.empty [(.symbol "Kept",Frame.empty)] (world + 1) (policy := policy) := by
  refine .groundedResume (operator := .symbol "host") (arguments := [])
    (outcome := .ok [(nativeFunctionValue,Bindings.empty)]) (rows := [(nativeFunctionValue,Frame.empty)])
    (world1 := world + 1) ?_ rfl ⟨rfl,rfl,rfl⟩ (.success (native_rows_single policy _ _ _)) ?_
  · simp [nativeCallValue,Entry.Value.erase]
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .nativeEmittedRaw (.producerFunction (native_function_pending policy) (native_function_minimal policy _ _ _ _ _ _))

theorem native_emitted_full_source (policy : Policy) (world : Nat) :
    Stateful.CallRel (nativeEnvironment (.ok [(nativeFunctionValue,Bindings.empty)]) .emitted) () world [] []
      nativeCallValue Atom.atomType Frame.empty [(.symbol "Kept",Frame.empty)] (world + 1) (policy := policy) := by
  refine .groundedResume (operator := .symbol "host") (arguments := [])
    (outcome := .ok [(nativeFunctionValue,Bindings.empty)]) (rows := [(nativeFunctionValue,Frame.empty)])
    (world1 := world + 1) ?_ rfl ?_ ⟨rfl,rfl,rfl⟩ (.success (native_rows_single policy _ _ _)) ?_
  · simp [nativeCallValue,Entry.Value.erase]
  · simp [nativeCallValue,Entry.Value.erase,IsErrorRel]
  · apply Stateful.BoundaryBatchRel.single_iff.mpr
    refine .nativeEmittedReturn
      (.producerFunction (native_function_pending policy) (native_function_minimal policy _ _ _ _ _ _)) ?_
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    refine .returned (.evaluate (by simp [Entry.Value.erase,Atom.notReducible])
      (by simp [Entry.Value.erase,IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) ?_)
    have entered : Entry.Rel policy.reentry
        (Frame.empty.read policy (Entry.Value.symbol "Kept")).status
        (Frame.empty.read policy (Entry.Value.symbol "Kept")).erase Atom.atomType .deliver := by
      simpa only [Frame.read_empty,Entry.Value.status,Entry.Value.erase] using
        (Entry.Rel.pass (atom := Atom.symbol "Kept") (expected := Atom.atomType)
          (policy := policy.reentry) (status := Entry.Status.active)
          (by simp [IsEmptyOrErrorRel,IsErrorRel,Atom.empty]) (MetaTypeRel.symbol "Kept") (Or.inl rfl))
    simpa only [Frame.read_empty] using
      (Stateful.AtomRel.delivered (value := Entry.Value.symbol "Kept")
        (expected := Atom.atomType) (frame := Frame.empty) (policy := policy) entered)

theorem native_provenance_separates : nativeFunctionValue.erase ≠ Atom.symbol "Kept" := by
  simp [nativeFunctionValue,Entry.Value.erase]

theorem native_duplicate_rows (policy : Policy) (value : Entry.Value) :
    NativeRowsRel policy (nativeDispatch (.ok [(value,Bindings.empty)]) .completed) (.symbol "host") [] Frame.empty
      [(value,Bindings.empty),(value,Bindings.empty)] [(value,Frame.empty),(value,Frame.empty)] :=
  .cons (Frame.NativeRenewRel.empty policy Frame.empty)
    (.cons (Frame.NativeRenewRel.empty policy Frame.empty) .nil)

theorem native_duplicate_cannot_drop (policy : Policy) (value : Entry.Value) :
    ¬NativeRowsRel policy (nativeDispatch (.ok [(value,Bindings.empty)]) .completed) (.symbol "host") [] Frame.empty
      [(value,Bindings.empty),(value,Bindings.empty)] [(value,Frame.empty)] := by
  intro source
  have length := source.length_eq_of_compatible (by
    intro row member
    have empty : row.2 = Bindings.empty := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> rfl
    rw [empty]
    exact ⟨Bindings.empty,BindingSourceAgreement.refl _,Frame.empty.certified.satisfiable⟩)
  simp only [List.length_cons,List.length_nil] at length
  cases length

def nativeIdentityCall (value : Entry.Value) : Entry.Value :=
  .expression .active [.symbol "identity-host",value]

def nativeIdentityProducer (call : Entry.Value) (outcome : GroundedResult Entry.Value) : Prop :=
  ∃ readiness value, call = .expression readiness [.symbol "identity-host",value] ∧
    outcome = .ok [(value,Bindings.empty)]

theorem native_identity_exact (value : Entry.Value) (outcome : GroundedResult Entry.Value) :
    nativeIdentityProducer (nativeIdentityCall value) outcome ↔ outcome = .ok [(value,Bindings.empty)] := by
  simp [nativeIdentityProducer,nativeIdentityCall]

/-- A bare-call relation cannot describe exact identity production for two
occurrences with equal syntax and different readiness. Extra metadata may
be represented in any way, but it cannot be absent from the logical input. -/
theorem native_identity_needs_annotations :
    ¬∃ reduce : Atom → GroundedResult Entry.Value → Prop,
      ∀ call outcome, reduce call.erase outcome ↔ nativeIdentityProducer call outcome := by
  rintro ⟨reduce,exactness⟩
  let active : Entry.Value := .expression .active [.symbol "f"]
  let held : Entry.Value := .expression .held [.symbol "f"]
  have heldReply : reduce (nativeIdentityCall held).erase (.ok [(held,Bindings.empty)]) :=
    (exactness _ _).mpr ((native_identity_exact held _).mpr rfl)
  have same : (nativeIdentityCall held).erase = (nativeIdentityCall active).erase := by
    simp [nativeIdentityCall,held,active,Entry.Value.erase]
  rw [same] at heldReply
  have impossible := (native_identity_exact active _).mp ((exactness _ _).mp heldReply)
  simp [held,active] at impossible

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed.Controls

/-! ## Simultaneous renaming for contextual values, certified frames, and completed premises -/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation Spec.Bindings.ScopeObservation

@[simp] theorem isErrorAtom_renameTypeVars (p : Equiv.Perm String) (atom : Atom) :
    isErrorAtom (renameTypeVars p atom) = isErrorAtom atom := by
  cases atom with
  | symbol | var | grounded => simp [isErrorAtom]
  | expression atoms =>
      rcases atoms with _ | ⟨head, tail⟩
      · simp [isErrorAtom]
      · cases head with
        | symbol name =>
            by_cases isErr : name = "Error" <;> simp [isErrorAtom, isErr]
        | var | grounded | expression => simp [isErrorAtom]

@[simp] theorem renameTypeVars_id_simp (atom : Atom) :
    renameTypeVars id atom = atom := by
  induction atom using Atom.rec
      (motive_2 := fun atoms => atoms.map (renameTypeVars id) = atoms) with
  | symbol | var | grounded => simp [renameTypeVars]
  | expression atoms ih => simp [renameTypeVars, ih]
  | nil => rfl
  | cons _ _ first rest => exact congrArg₂ List.cons first rest

@[simp] theorem renameTypeVars_id_fun :
    renameTypeVars id = id := by
  funext atom
  exact renameTypeVars_id_simp atom

@[simp] theorem renameBindings_perm_inverse_reverse (p : Equiv.Perm String) (bindings : Bindings) :
    renameBindings p (renameBindings p.symm bindings) = bindings :=
  renameBindings_perm_inverse p.symm bindings

@[simp] theorem isEmptyAtom_renameTypeVars (p : Equiv.Perm String) (atom : Atom) :
    isEmptyAtom (renameTypeVars p atom) = isEmptyAtom atom := by
  cases atom <;> simp [isEmptyAtom, Atom.empty]

@[simp] theorem isEmptyOrError_renameTypeVars (p : Equiv.Perm String) (atom : Atom) :
    isEmptyOrError (renameTypeVars p atom) = isEmptyOrError atom := by
  simp [isEmptyOrError]

theorem Rel.rename (p : Equiv.Perm String) {policy : ReentryPolicy} {status : Status}
    {atom expected : Atom} {action : Action}
    (entered : Rel policy status atom expected action) :
    Rel policy status (renameTypeVars p atom) (renameTypeVars p expected) action := by
  cases entered with
  | stopped stopped =>
      exact .stopped ((Renaming.stopped_iff p _).mpr stopped)
  | @pass atom expected metaType clean typed raw =>
      refine .pass ((not_congr (Renaming.stopped_iff p _)).mpr clean)
        (Renaming.metaType p typed) ((Renaming.pass_type p expected metaType).mpr raw)
  | @held atoms expected clean raw reused heldStatus =>
      have exprFixed : renameTypeVars p Atom.expressionType = Atom.expressionType :=
        Renaming.metaType_fixed (.expression atoms) p
      have noPass : ¬(renameTypeVars p expected = Atom.atomType ∨
          renameTypeVars p expected = Atom.expressionType ∨
          Atom.expressionType = Atom.variableType) := by
        have EquivPass := Renaming.pass_type p expected Atom.expressionType
        rw [exprFixed] at EquivPass
        exact (not_congr EquivPass).mpr raw
      simpa only [renameTypeVars] using Rel.held
        (by simpa only [renameTypeVars] using (not_congr (Renaming.stopped_iff p (.expression atoms))).mpr clean)
        noPass reused heldStatus
  | @cast atom expected metaType clean typed raw scalar unitActive =>
      refine .cast ((not_congr (Renaming.stopped_iff p _)).mpr clean)
        (Renaming.metaType p typed)
        ((not_congr (Renaming.pass_type p expected metaType)).mpr raw)
        (Renaming.cast_shape p scalar) ?_
      intro isUnit
      apply unitActive
      apply renameTypeVars_perm_injective p
      simpa [Atom.unit] using isUnit
  | @expression head tail expected clean raw active =>
      have exprFixed : renameTypeVars p Atom.expressionType = Atom.expressionType :=
        Renaming.metaType_fixed (.expression (head :: tail)) p
      have noPass : ¬(renameTypeVars p expected = Atom.atomType ∨
          renameTypeVars p expected = Atom.expressionType ∨
          Atom.expressionType = Atom.variableType) := by
        have EquivPass := Renaming.pass_type p expected Atom.expressionType
        rw [exprFixed] at EquivPass
        exact (not_congr EquivPass).mpr raw
      simpa only [renameTypeVars, List.map_cons] using Rel.expression
        (by simpa only [renameTypeVars, List.map_cons] using
          (not_congr (Renaming.stopped_iff p (.expression (head :: tail)))).mpr clean)
        noPass active

theorem Rel.rename_iff (p : Equiv.Perm String) {policy : ReentryPolicy} {status : Status}
    {atom expected : Atom} {action : Action} :
    Rel policy status (renameTypeVars p atom) (renameTypeVars p expected) action ↔
      Rel policy status atom expected action := by
  constructor
  · intro entered
    simpa only [renameTypeVars_perm_inverse] using entered.rename p.symm
  · exact Rel.rename p

@[simp] theorem publish_status_rename (p : Equiv.Perm String) (policy : MarkPolicy)
    (original : Atom) (result : FrameResult) (inherited : Status := .active) :
    (publish policy (renameTypeVars p original) (Renaming.frameResult p result) inherited).status =
      (publish policy original result inherited).status := by
  rcases result with ⟨atom, frame⟩
  cases atom with
  | symbol | var | grounded =>
      simp [publish, Renaming.frameResult]
  | expression atoms =>
      have errEq := isErrorAtom_renameTypeVars p (.expression atoms)
      have eqIff : (Atom.expression (atoms.map (renameTypeVars p)) = renameTypeVars p original) ↔
          (Atom.expression atoms = original) := by
        simpa only [renameTypeVars] using
          (renameTypeVars_perm_injective p).eq_iff (a := .expression atoms) (b := original)
      simp only [publish, Renaming.frameResult, renameTypeVars] at errEq ⊢
      simp [errEq, eqIff]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry.Value

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type.RuntimeRefinement Spec.Type.Presentation
open Spec.Type.Presentation.ScopeObservation Spec.Bindings.ScopeObservation

@[simp] theorem rename_symbol (names : String → String) (name : String) :
    rename names (.symbol name) = .symbol name := by
  simp [rename, substitute]

@[simp] theorem rename_var (names : String → String) (name : String) :
    rename names (.var name) = .var (names name) := by
  simp [rename, substitute]

@[simp] theorem rename_grounded (names : String → String) (value : GroundedValue) :
    rename names (.grounded value) = .grounded value := by
  simp [rename, substitute]

@[simp] theorem rename_expression (names : String → String) (previous : Status) (children : List Value) :
    rename names (.expression previous children) =
      .expression previous (children.map (rename names)) := by
  simp [rename, substitute, rebuildStatus]

@[simp] theorem rename_cancel_simp (names : Equiv.Perm String) (value : Value) :
    rename names.symm (rename names value) = value :=
  rename_cancel names value

@[simp] theorem rename_cancel_reverse (names : Equiv.Perm String) (value : Value) :
    rename names (rename names.symm value) = value :=
  rename_cancel names.symm value

def renameEnvironment (names : String → String) (environment : Environment) : Environment :=
  environment.map fun row => (names row.1, rename names row.2)

@[simp] theorem renameEnvironment_nil (names : String → String) :
    renameEnvironment names [] = [] := rfl

@[simp] theorem renameEnvironment_cons (names : String → String)
    (row : String × Value) (rest : Environment) :
    renameEnvironment names (row :: rest) =
      (names row.1, rename names row.2) :: renameEnvironment names rest := rfl

@[simp] theorem renameEnvironment_id (environment : Environment) :
    renameEnvironment id environment = environment := by
  simp [renameEnvironment]

theorem renameEnvironment_comp (outer inner : String → String) (environment : Environment) :
    renameEnvironment outer (renameEnvironment inner environment) =
      renameEnvironment (outer ∘ inner) environment := by
  simp [renameEnvironment, rename_comp, Function.comp_def]

@[simp] theorem renameEnvironment_cancel (p : Equiv.Perm String) (environment : Environment) :
    renameEnvironment p.symm (renameEnvironment p environment) = environment := by
  rw [renameEnvironment_comp]
  have idComp : ((p.symm : String → String) ∘ p) = id := by
    funext name
    exact p.symm_apply_apply name
  rw [idComp, renameEnvironment_id]

@[simp] theorem renameEnvironment_cancel_reverse (p : Equiv.Perm String) (environment : Environment) :
    renameEnvironment p (renameEnvironment p.symm environment) = environment :=
  renameEnvironment_cancel p.symm environment

@[simp] theorem eraseEnvironment_renameEnvironment (names : String → String) (environment : Environment) :
    eraseEnvironment (renameEnvironment names environment) =
      (eraseEnvironment environment).renameVars names := by
  induction environment with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨name, value⟩
      simpa only [renameEnvironment, eraseEnvironment, TypeSubst.renameVars,
        List.map_cons, rename_erase] using congrArg (List.cons _) ih

theorem lookup_renameEnvironment (p : Equiv.Perm String) (environment : Environment) (name : String) :
    (renameEnvironment p environment).lookup (p name) =
      (environment.lookup name).map (rename p) := by
  induction environment with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      by_cases same : name = key
      · subst key
        simp [renameEnvironment, List.lookup]
      · have mapped : (p name == p key) = false := by
          simp [p.injective.eq_iff, same]
        have raw : (name == key) = false := by simp [same]
        simpa [renameEnvironment, List.lookup, mapped, raw] using ih

theorem resolve_renameEnvironment (p : Equiv.Perm String) (environment : Environment) (name : String) :
    resolve (renameEnvironment p environment) (p name) =
      rename p (resolve environment name) := by
  unfold resolve
  rw [lookup_renameEnvironment]
  cases environment.lookup name with
  | none => simp
  | some value => rfl

theorem resolve_renameEnvironment_symm (p : Equiv.Perm String) (environment : Environment) (name : String) :
    resolve (renameEnvironment p environment) name =
      rename p (resolve environment (p.symm name)) := by
  simpa using resolve_renameEnvironment p environment (p.symm name)

@[simp] theorem rename_withStatus (names : String → String) (value : Value) (readiness : Status) :
    rename names (value.withStatus readiness) = (rename names value).withStatus readiness := by
  cases value <;> simp [withStatus]

@[simp] theorem rebuildStatus_renameTypeVars (p : Equiv.Perm String) (policy : RebuildPolicy)
    (previous : Status) (before after : Atom) :
    rebuildStatus policy previous (renameTypeVars p before) (renameTypeVars p after) =
      rebuildStatus policy previous before after := by
  cases policy <;> simp [rebuildStatus, (renameTypeVars_perm_injective p).eq_iff]

theorem substitute_rename (p : Equiv.Perm String) (policy : RebuildPolicy)
    (environment : String → Value) (value : Value) :
    substitute policy (fun name => rename p (environment (p.symm name))) (rename p value) =
      rename p (substitute policy environment value) := by
  induction value using Value.rec
      (motive_2 := fun values =>
        (values.map (rename p)).map (substitute policy (fun name => rename p (environment (p.symm name)))) =
          (values.map (substitute policy environment)).map (rename p)) with
  | symbol => simp [substitute]
  | var name => simp [substitute]
  | grounded => simp [substitute]
  | expression previous children ih =>
      simp only [rename_expression, substitute]
      rw [ih]
      have beforeErase : (children.map (rename p)).map erase =
          (children.map erase).map (renameTypeVars p) := by
        simp [List.map_map, Function.comp_def, rename_erase]
      have afterErase : ((children.map (substitute policy environment)).map (rename p)).map erase =
          ((children.map (substitute policy environment)).map erase).map (renameTypeVars p) := by
        simp [List.map_map, Function.comp_def, rename_erase]
      rw [beforeErase, afterErase]
      simpa only [renameTypeVars] using congrArg
        (fun readiness => Value.expression readiness ((children.map (substitute policy environment)).map (rename p)))
        (rebuildStatus_renameTypeVars p policy previous
          (.expression (children.map erase))
          (.expression ((children.map (substitute policy environment)).map erase)))
  | nil => rfl
  | cons head tail first rest => simpa only [List.map_cons] using congrArg₂ List.cons first rest

theorem substitute_resolve_renameEnvironment (p : Equiv.Perm String) (policy : RebuildPolicy)
    (environment : Environment) (value : Value) :
    substitute policy (resolve (renameEnvironment p environment)) (rename p value) =
      rename p (substitute policy (resolve environment) value) := by
  have envEq : resolve (renameEnvironment p environment) =
      fun name => rename p (resolve environment (p.symm name)) := by
    funext name
    exact resolve_renameEnvironment_symm p environment name
  rw [envEq]
  exact substitute_rename p policy (resolve environment) value

theorem bind_renameEnvironment (p : Equiv.Perm String) (policy : RebuildPolicy)
    (environment : Environment) (name : String) (value : Value) :
    bind policy (renameEnvironment p environment) (p name) (rename p value) =
      renameEnvironment p (bind policy environment name value) := by
  unfold bind
  rw [substitute_resolve_renameEnvironment]
  let resolved := substitute policy (resolve environment) value
  have filterEq : (renameEnvironment p environment).filter (fun row => row.1 != p name) =
      renameEnvironment p (environment.filter (fun row => row.1 != name)) := by
    induction environment with
    | nil => rfl
    | cons row rest ih =>
        rcases row with ⟨key, val⟩
        by_cases same : key = name
        · subst key
          simpa [renameEnvironment_cons, List.filter_cons] using ih
        · have mapped : (p key != p name) = true := by
            simp [p.injective.eq_iff, same]
          have raw : (key != name) = true := by simp [same]
          simpa [renameEnvironment_cons, List.filter_cons, mapped, raw] using
            congrArg (List.cons (p key, rename p val)) ih
  rw [filterEq]
  simp only [renameEnvironment, List.map_cons, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro row _
  rcases row with ⟨key, val⟩
  congr 1
  simpa only [renameEnvironment, List.map_cons, List.map_nil] using
    substitute_resolve_renameEnvironment p policy [(name, resolved)] val

private theorem unification_rename (p : Equiv.Perm String) (policy : RebuildPolicy) :
    (∀ {environment output left right}, AppliedUnifyRel policy environment left right output →
      AppliedUnifyRel policy (renameEnvironment p environment) (rename p left) (rename p right)
        (renameEnvironment p output)) ∧
    (∀ {environment output left right}, UnifyRel policy environment left right output →
      UnifyRel policy (renameEnvironment p environment) (rename p left) (rename p right)
        (renameEnvironment p output)) ∧
    (∀ {environment output left right}, UnifyListRel policy environment left right output →
      UnifyListRel policy (renameEnvironment p environment) (left.map (rename p)) (right.map (rename p))
        (renameEnvironment p output)) := by
  let applied := fun environment left right output (_ : AppliedUnifyRel policy environment left right output) =>
    AppliedUnifyRel policy (renameEnvironment p environment) (rename p left) (rename p right)
      (renameEnvironment p output)
  let ordinary := fun environment left right output (_ : UnifyRel policy environment left right output) =>
    UnifyRel policy (renameEnvironment p environment) (rename p left) (rename p right)
      (renameEnvironment p output)
  let many := fun environment left right output (_ : UnifyListRel policy environment left right output) =>
    UnifyListRel policy (renameEnvironment p environment) (left.map (rename p)) (right.map (rename p))
      (renameEnvironment p output)
  have identical {environment left right} (same : left.erase = right.erase) :
      applied environment left right environment (.identical same) := by
    dsimp [applied]
    apply AppliedUnifyRel.identical
    rw [rename_erase, rename_erase, same]
  have bindLeft {environment name right} (absent : name ∉ TypeSubst.typeVars right.erase) :
      applied environment (.var name) right (bind policy environment name right) (.bindLeft absent) := by
    dsimp [applied]
    rw [← bind_renameEnvironment, rename_var]
    apply AppliedUnifyRel.bindLeft
    rw [rename_erase, typeVars_renameTypeVars]
    intro present
    obtain ⟨original, member, equal⟩ := List.mem_map.mp present
    obtain rfl := p.injective equal
    exact absent member
  have bindRight {environment left name} (nonvar : ∀ other, left.erase ≠ .var other)
      (absent : name ∉ TypeSubst.typeVars left.erase) :
      applied environment left (.var name) (bind policy environment name left) (.bindRight nonvar absent) := by
    dsimp [applied]
    rw [← bind_renameEnvironment, rename_var]
    apply AppliedUnifyRel.bindRight
    · intro other same
      rw [rename_erase] at same
      apply nonvar (p.symm other)
      simpa using congrArg (renameTypeVars p.symm) same
    · rw [rename_erase, typeVars_renameTypeVars]
      intro present
      obtain ⟨original, member, equal⟩ := List.mem_map.mp present
      obtain rfl := p.injective equal
      exact absent member
  have expression {environment output left right earlier later}
      (children : UnifyListRel policy environment left right output)
      (ih : many environment left right output children) :
      applied environment (.expression earlier left) (.expression later right) output
        (.expression children) := by
    dsimp [applied]
    rw [rename_expression, rename_expression]
    exact AppliedUnifyRel.expression ih
  have materialized {environment output left right}
      (derived : AppliedUnifyRel policy environment
        (substitute policy (resolve environment) left)
        (substitute policy (resolve environment) right) output)
      (ih : applied environment _ _ output derived) :
      ordinary environment left right output (.ordinary derived) := by
    dsimp [ordinary]
    apply UnifyRel.ordinary
    rw [substitute_resolve_renameEnvironment, substitute_resolve_renameEnvironment]
    exact ih
  have nil (environment) : many environment [] [] environment (.nil environment) := .nil _
  have cons {environment next output left right lefts rights}
      (head : UnifyRel policy environment left right next)
      (tail : UnifyListRel policy next lefts rights output)
      (ih : ordinary environment left right next head)
      (it : many next lefts rights output tail) :
      many environment (left :: lefts) (right :: rights) output (.cons head tail) :=
    .cons ih it
  exact ⟨fun derived => AppliedUnifyRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => UnifyRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived,
    fun derived => UnifyListRel.rec
      (motive_1 := applied) (motive_2 := ordinary) (motive_3 := many)
      identical bindLeft bindRight expression materialized nil cons derived⟩

theorem AppliedUnifyRel.rename (p : Equiv.Perm String) {policy environment output left right}
    (derived : AppliedUnifyRel policy environment left right output) :
    AppliedUnifyRel policy (renameEnvironment p environment) (rename p left) (rename p right)
      (renameEnvironment p output) :=
  (unification_rename p policy).1 derived

theorem UnifyRel.rename (p : Equiv.Perm String) {policy environment output left right}
    (derived : UnifyRel policy environment left right output) :
    UnifyRel policy (renameEnvironment p environment) (rename p left) (rename p right)
      (renameEnvironment p output) :=
  (unification_rename p policy).2.1 derived

theorem UnifyListRel.rename (p : Equiv.Perm String) {policy environment output left right}
    (derived : UnifyListRel policy environment left right output) :
    UnifyListRel policy (renameEnvironment p environment) (left.map (rename p)) (right.map (rename p))
      (renameEnvironment p output) :=
  (unification_rename p policy).2.2 derived

@[simp] theorem rename_publish (p : Equiv.Perm String) (policy : MarkPolicy)
    (original : Atom) (frame : BindingFrame) (value : Value) :
    rename p (publish policy original frame value) =
      publish policy (renameTypeVars p original) (frame.rename p) (rename p value) := by
  unfold publish
  rw [rename_withStatus]
  have sameStatus := Entry.publish_status_rename p policy original (value.erase, frame) value.status
  simpa only [Renaming.frameResult, rename_erase, rename_status] using
    congrArg (withStatus (rename p value)) sameStatus.symm

@[simp] theorem rename_argumentPacket (names : String → String) (values : List Value) :
    rename names (argumentPacket values) = argumentPacket (values.map (rename names)) := by
  simp [argumentPacket]

@[simp] theorem unpackArguments_rename (names : String → String) (value : Value) :
    unpackArguments (rename names value) =
      (unpackArguments value).map (List.map (rename names)) := by
  cases value with
  | symbol | var | grounded => simp [unpackArguments]
  | expression readiness children =>
      rcases children with _ | ⟨head, tail⟩
      · simp [unpackArguments]
      rcases tail with _ | ⟨payload, tail⟩
      · simp [unpackArguments]
      rcases tail with _ | ⟨extra, rest⟩
      · cases head <;> cases payload <;> simp [unpackArguments]
      · simp [unpackArguments]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry.Value

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation Spec.Bindings.ScopeObservation
open Spec.Eval.Renaming

def EquationWork.rename (p : Equiv.Perm String) (work : EquationWork) : EquationWork where
  position := work.position
  left := renameTypeVars p work.left
  right := renameTypeVars p work.right
  pattern := renameTypeVars p work.pattern
  body := renameTypeVars p work.body
  bindings := renameBindings p work.bindings

@[simp] theorem EquationWork.rename_id (work : EquationWork) :
    work.rename (Equiv.refl String) = work := by
  cases work
  simp [EquationWork.rename, show (Equiv.refl String : String → String) = id from rfl]

theorem EquationWork.rename_comp (p q : Equiv.Perm String) (work : EquationWork) :
    (work.rename p).rename q = work.rename (q * p) := by
  cases work
  simp [EquationWork.rename, renameTypeVars_comp, renameBindings_comp,
    Function.comp_def, Equiv.Perm.coe_mul]

@[simp] theorem EquationWork.rename_cancel (p : Equiv.Perm String) (work : EquationWork) :
    (work.rename p).rename p.symm = work := by
  cases work
  simp [EquationWork.rename]

@[simp] theorem EquationWork.rename_cancel_reverse (p : Equiv.Perm String) (work : EquationWork) :
    (work.rename p.symm).rename p = work :=
  EquationWork.rename_cancel p.symm work

theorem EquationRowResultsRel.rename (p : Equiv.Perm String)
    {live : List Atom} {query row : Atom} {incoming : Bindings} {position : Nat}
    {results : List EquationWork}
    (derived : EquationRowResultsRel live query incoming position row results) :
    EquationRowResultsRel (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p incoming) position (renameTypeVars p row)
      (results.map (EquationWork.rename p)) := by
  cases derived with
  | irrelevant row notEquation =>
      apply EquationRowResultsRel.irrelevant
      intro left right same
      apply notEquation (renameTypeVars p.symm left) (renameTypeVars p.symm right)
      simpa using congrArg (renameTypeVars p.symm) same
  | miss left right pattern body alpha absent =>
      simpa only [renameTypeVars, List.map_cons, List.map_nil] using
        EquationRowResultsRel.miss position (renameTypeVars p left) (renameTypeVars p right)
          (renameTypeVars p pattern) (renameTypeVars p body) (alpha_variant p alpha)
          (by
            intro otherPattern otherBody otherAlpha matched output viable
            exact absent (renameTypeVars p.symm otherPattern) (renameTypeVars p.symm otherBody)
              (by
                simpa only [atoms_inverse, renameTypeVars_perm_inverse, renameBindings_perm_inverse] using
                  alpha_variant p.symm otherAlpha)
              (renameBindings p.symm matched) (renameBindings p.symm output)
              ⟨by
                simpa only [renameTypeVars_perm_inverse] using match_rename p.symm viable.1,
               by
                simpa only [renameBindings_perm_inverse] using viable.2.rename p.symm⟩)
  | hit left right pattern body matched output alpha matching merged =>
      simpa only [renameTypeVars, List.map_cons, List.map_nil, EquationWork.rename] using
        EquationRowResultsRel.hit position (renameTypeVars p left) (renameTypeVars p right)
          (renameTypeVars p pattern) (renameTypeVars p body)
          (renameBindings p matched) (renameBindings p output)
          (alpha_variant p alpha) (match_rename p matching) (merged.rename p)

theorem EquationFrontierRel.rename (p : Equiv.Perm String)
    {context : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {results : List EquationWork}
    (derived : EquationFrontierRel context live query incoming results) :
    EquationFrontierRel (space p context) (live.map (renameTypeVars p)) (renameTypeVars p query)
      (renameBindings p incoming) (results.map (EquationWork.rename p)) := by
  cases derived with
  | @completed blocks covered =>
      have zipMap : ∀ (atoms : List Atom) (start : Nat),
          (atoms.map (renameTypeVars p)).zipIdx start =
            (atoms.zipIdx start).map (fun row => (renameTypeVars p row.1, row.2)) := by
        intro atoms
        induction atoms with
        | nil => intro _; rfl
        | cons head tail ih =>
            intro start
            simpa only [List.map_cons, List.zipIdx_cons] using congrArg (List.cons _) (ih (start + 1))
      have blocksRenamed :
          List.Forall₂ (fun row block =>
            EquationRowResultsRel (live.map (renameTypeVars p)) (renameTypeVars p query)
              (renameBindings p incoming) row.2 row.1 block)
            ((space p context).atoms.zipIdx)
            (blocks.map (List.map (EquationWork.rename p))) := by
        change List.Forall₂ _ ((context.atoms.map (renameTypeVars p)).zipIdx 0) _
        rw [zipMap]
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact covered.imp (fun _ _ rowDerived => rowDerived.rename p)
      have flattenMap : ∀ (items : List (List EquationWork)),
          (items.map (List.map (EquationWork.rename p))).flatten =
            items.flatten.map (EquationWork.rename p) := by
        intro items
        induction items with
        | nil => rfl
        | cons first rest ih =>
            simp only [List.map_cons, List.flatten_cons, List.map_append, ih]
      rw [← flattenMap]
      exact .completed blocksRenamed

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Eval.Steps Spec.Eval.Renaming
open Mettapedia.Machines.OrderedProtocol.Completion

theorem TypeMatchingPolicy.Rel.rename (p : Equiv.Perm String)
    {policy : TypeMatchingPolicy} {expected actual : Atom} {before after : Bindings}
    (matched : policy.Rel expected actual before after) :
    policy.Rel (renameTypeVars p expected) (renameTypeVars p actual)
      (renameBindings p before) (renameBindings p after) := by
  cases policy with
  | raw => exact TypeMatchRel.rename p matched
  | finite => exact ⟨TypeMatchRel.rename p matched.1, type_model p matched.2⟩

theorem TypeMatchingPolicy.Rel.rename_iff (p : Equiv.Perm String)
    {policy : TypeMatchingPolicy} {expected actual : Atom} {before after : Bindings} :
    policy.Rel (renameTypeVars p expected) (renameTypeVars p actual)
      (renameBindings p before) (renameBindings p after) ↔
      policy.Rel expected actual before after := by
  constructor
  · intro matched
    simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using matched.rename p.symm
  · exact TypeMatchingPolicy.Rel.rename p

def renameTypeLookup (p : Equiv.Perm String) (lookup : TypeLookupRel) : TypeLookupRel :=
  fun bindings subject expected types =>
    lookup (renameBindings p.symm bindings) (renameTypeVars p.symm subject)
      (renameTypeVars p.symm expected) (types.map (renameTypeVars p.symm))

def renameCastLookup (p : Equiv.Perm String) (lookup : CastLookup) : CastLookup :=
  fun scope context => renameTypeLookup p (lookup (scope.map p.symm) (space p.symm context))

@[simp] theorem renameTypeLookup_id (lookup : TypeLookupRel) :
    renameTypeLookup (Equiv.refl String) lookup = lookup := by
  funext bindings subject expected types
  simp [renameTypeLookup, show (Equiv.refl String : String → String) = id from rfl]

theorem renameTypeLookup_comp (p q : Equiv.Perm String) (lookup : TypeLookupRel) :
    renameTypeLookup q (renameTypeLookup p lookup) = renameTypeLookup (q * p) lookup := by
  funext bindings subject expected types
  have symmMul : ((q * p).symm : String → String) = fun x => p.symm (q.symm x) := rfl
  simp [renameTypeLookup, renameBindings_comp, renameTypeVars_comp,
    List.map_map, Function.comp_def, symmMul]

@[simp] theorem renameTypeLookup_cancel (p : Equiv.Perm String) (lookup : TypeLookupRel) :
    renameTypeLookup p.symm (renameTypeLookup p lookup) = lookup := by
  funext bindings subject expected types
  simp [renameTypeLookup, List.map_map, Function.comp_def]

@[simp] theorem renameTypeLookup_cancel_reverse (p : Equiv.Perm String) (lookup : TypeLookupRel) :
    renameTypeLookup p (renameTypeLookup p.symm lookup) = lookup :=
  renameTypeLookup_cancel p.symm lookup

@[simp] theorem renameTypeLookup_apply (p : Equiv.Perm String) (lookup : TypeLookupRel)
    (bindings : Bindings) (subject expected : Atom) (types : List Atom) :
    renameTypeLookup p lookup (renameBindings p bindings) (renameTypeVars p subject)
      (renameTypeVars p expected) (types.map (renameTypeVars p)) ↔
      lookup bindings subject expected types := by
  simp [renameTypeLookup, List.map_map, Function.comp_def]

@[simp] theorem renameCastLookup_id (lookup : CastLookup) :
    renameCastLookup (Equiv.refl String) lookup = lookup := by
  funext scope context
  cases context
  simp [renameCastLookup, space, show (Equiv.refl String : String → String) = id from rfl]

theorem renameCastLookup_comp (p q : Equiv.Perm String) (lookup : CastLookup) :
    renameCastLookup q (renameCastLookup p lookup) = renameCastLookup (q * p) lookup := by
  funext scope context
  have symmMul : ((q * p).symm : String → String) = fun x => p.symm (q.symm x) := rfl
  simp [renameCastLookup, renameTypeLookup_comp, space, List.map_map,
    Function.comp_def, renameTypeVars_comp, symmMul]

@[simp] theorem renameCastLookup_cancel (p : Equiv.Perm String) (lookup : CastLookup) :
    renameCastLookup p.symm (renameCastLookup p lookup) = lookup := by
  funext scope context
  simp [renameCastLookup, List.map_map, Function.comp_def]

@[simp] theorem renameCastLookup_cancel_reverse (p : Equiv.Perm String) (lookup : CastLookup) :
    renameCastLookup p (renameCastLookup p.symm lookup) = lookup :=
  renameCastLookup_cancel p.symm lookup

@[simp] theorem renameCastLookup_apply (p : Equiv.Perm String) (lookup : CastLookup)
    (scope : List String) (context : Space) :
    renameCastLookup p lookup (scope.map p) (space p context) =
      renameTypeLookup p (lookup scope context) := by
  simp [renameCastLookup, List.map_map, Function.comp_def]

@[simp] theorem renameCastLookup_rawLookup (p : Equiv.Perm String) :
    renameCastLookup p rawLookup = rawLookup := by
  funext scope context bindings subject expected types
  exact propext (StorageTypesRel.rename_iff p.symm context subject types)

@[simp] theorem renameCastLookup_scopedLookup (p : Equiv.Perm String) :
    renameCastLookup p scopedLookup = scopedLookup := by
  funext scope context bindings subject expected types
  apply propext
  unfold renameCastLookup renameTypeLookup scopedLookup scopedTypeLookup
  constructor
  · rintro ⟨raw, inferred, variants⟩
    refine ⟨raw.map (renameTypeVars p), ?_, ?_⟩
    · simpa only [space_inverse_reverse, renameTypeVars_perm_inverse_reverse] using
        inferred.rename p
    · have transported := argument_variants p variants
      rw [← invocation_scope p] at transported
      simpa [List.map_map, Function.comp_def] using transported
  · rintro ⟨raw, inferred, variants⟩
    refine ⟨raw.map (renameTypeVars p.symm), inferred.rename p.symm, ?_⟩
    have transported := argument_variants p.symm variants
    rw [← invocation_scope p.symm] at transported
    simpa only [List.map_nil] using transported

theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeCastBatchRel.rename (p : Equiv.Perm String)
    {context : Space} {atom expected : Atom} {bindings : Bindings} {raw : ResultSet}
    {lookup : TypeLookupRel} {policy : TypeMatchingPolicy}
    (batch : TypeCastBatchRel context atom expected bindings raw
      (lookup := lookup) (matching := policy.Rel)) :
    TypeCastBatchRel (space p context) (renameTypeVars p atom) (renameTypeVars p expected)
      (renameBindings p bindings) (results p raw)
      (lookup := renameTypeLookup p lookup) (matching := policy.Rel) := by
  cases batch with
  | @success _ _ types earlier later actual output queried selected rejected matched =>
      simpa only [results, List.map_cons, List.map_nil, result] using
        TypeCastBatchRel.success
          (lookup := renameTypeLookup p lookup) (matching := policy.Rel)
          (types := types.map (renameTypeVars p))
          (earlierTypes := earlier.map (renameTypeVars p))
          (laterTypes := later.map (renameTypeVars p))
          (actualType := renameTypeVars p actual)
          (output := renameBindings p output)
          ((renameTypeLookup_apply p lookup bindings atom expected types).mpr queried)
          (by simpa only [List.map_append, List.map_cons] using congrArg (List.map (renameTypeVars p)) selected)
          (by
            intro prior member candidate accepted
            obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
            apply rejected original present (renameBindings p.symm candidate)
            simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using
              accepted.rename p.symm)
          (matched.rename p)
  | @failure _ _ types queried rejected =>
      have mapped : results p (types.map fun actualType => (mkError atom (.badType expected actualType), bindings)) =
          (types.map (renameTypeVars p)).map fun actualType =>
            (mkError (renameTypeVars p atom) (.badType (renameTypeVars p expected) actualType),
              renameBindings p bindings) := by
        simp [results, result, List.map_map, Function.comp_def, renamed_badType]
      rw [mapped]
      exact TypeCastBatchRel.failure
        ((renameTypeLookup_apply p lookup bindings atom expected types).mpr queried)
        (by
          intro candidateType member candidate accepted
          obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
          apply rejected original present (renameBindings p.symm candidate)
          simpa only [renameTypeVars_perm_inverse, renameBindings_perm_inverse] using
            accepted.rename p.symm)

namespace Frame

def rename (p : Equiv.Perm String) (frame : Frame) : Frame where
  bindings := renameBindings p frame.bindings
  environment := Entry.Value.renameEnvironment p frame.environment
  certified := by
    rw [Entry.Value.eraseEnvironment_renameEnvironment]
    exact frame.certified.rename p

@[simp] theorem rename_bindings (p : Equiv.Perm String) (frame : Frame) :
    (frame.rename p).bindings = renameBindings p frame.bindings := rfl

@[simp] theorem rename_environment (p : Equiv.Perm String) (frame : Frame) :
    (frame.rename p).environment = Entry.Value.renameEnvironment p frame.environment := rfl

@[simp] theorem rename_id (frame : Frame) : frame.rename (Equiv.refl String) = frame := by
  rcases frame with ⟨bindings, environment, certified⟩
  simp [rename]

@[simp] theorem rename_id_fun : rename (Equiv.refl String) = id := by
  funext frame
  exact rename_id frame

theorem rename_comp (p q : Equiv.Perm String) (frame : Frame) :
    (frame.rename p).rename q = frame.rename (q * p) := by
  rcases frame with ⟨bindings, environment, certified⟩
  simp [rename, renameBindings_comp, Entry.Value.renameEnvironment_comp, Equiv.Perm.coe_mul]

@[simp] theorem rename_cancel (p : Equiv.Perm String) (frame : Frame) :
    (frame.rename p).rename p.symm = frame := by
  rcases frame with ⟨bindings, environment, certified⟩
  simp [rename]

@[simp] theorem rename_cancel_reverse (p : Equiv.Perm String) (frame : Frame) :
    (frame.rename p.symm).rename p = frame :=
  rename_cancel p.symm frame

@[simp] theorem source_rename (p : Equiv.Perm String) (frame : Frame) :
    (frame.rename p).source = frame.source.rename p := by
  rcases frame with ⟨bindings, environment, certified⟩
  exact BindingFrame.selected_congr rfl
    (Entry.Value.eraseEnvironment_renameEnvironment p environment)

@[simp] theorem read_rename (p : Equiv.Perm String) (policy : Policy)
    (frame : Frame) (value : Entry.Value) :
    (frame.rename p).read policy (Entry.Value.rename p value) =
      Entry.Value.rename p (frame.read policy value) :=
  Entry.Value.substitute_resolve_renameEnvironment p policy.rebuilding frame.environment value

@[simp] theorem argumentDemand_rename (p : Equiv.Perm String) (policy : Policy) (frame : Frame) (formal : Atom) :
    (frame.rename p).argumentDemand policy (renameTypeVars p formal) = renameTypeVars p (frame.argumentDemand policy formal) := by
  cases mode : policy.operandDemand with
  | raw => rw [argumentDemand_raw policy (frame.rename p) _ mode, argumentDemand_raw policy frame formal mode]
  | retained =>
      rw [argumentDemand_retained policy (frame.rename p) _ mode, argumentDemand_retained policy frame formal mode,
        ← Entry.Value.rename_ofAtom, read_rename, Entry.Value.rename_erase]

@[simp] theorem empty_rename (p : Equiv.Perm String) :
    empty.rename p = empty := by
  simp [empty, rename, renameBindings, Bindings.empty, Entry.Value.renameEnvironment]

theorem CastRenewRel.rename (p : Equiv.Perm String)
    {policy : Policy} {lookup : TypeLookupRel} {original expected : Atom}
    {before after : Frame}
    (renewed : CastRenewRel policy lookup original expected before after) :
    CastRenewRel policy (renameTypeLookup p lookup)
      (renameTypeVars p original) (renameTypeVars p expected)
      (before.rename p) (after.rename p) := by
  cases renewed with
  | same => exact .same _
  | matched queried selected rejected matched unified =>
      rename_i types earlier later actual
      refine .matched
        (types := types.map (renameTypeVars p))
        (earlier := earlier.map (renameTypeVars p))
        (later := later.map (renameTypeVars p))
        (actual := renameTypeVars p actual)
        ((renameTypeLookup_apply p lookup before.bindings original expected types).mpr queried)
        (by simpa only [List.map_append, List.map_cons] using congrArg (List.map (renameTypeVars p)) selected)
        (by
          intro prior member candidate accepted
          obtain ⟨rawPrior, present, rfl⟩ := List.mem_map.mp member
          apply rejected rawPrior present (renameBindings p.symm candidate)
          simpa only [rename_bindings, renameTypeVars_perm_inverse, renameBindings_perm_inverse] using
            accepted.rename p.symm)
        (matched.rename p)
        (by
          rw [← Entry.Value.rename_ofAtom, ← Entry.Value.rename_ofAtom]
          exact Entry.Value.UnifyRel.rename p unified)

theorem TypeRenewRel.rename (p : Equiv.Perm String)
    {policy : Policy} {expected actual : Atom} {before after : Frame}
    (renewed : TypeRenewRel policy expected actual before after) :
    TypeRenewRel policy (renameTypeVars p expected) (renameTypeVars p actual)
      (before.rename p) (after.rename p) := by
  cases renewed with
  | unchanged matched => exact .unchanged (matched.rename p)
  | unified matched unified =>
      exact .unified (matched.rename p)
        (by
          rw [← Entry.Value.rename_ofAtom, ← Entry.Value.rename_ofAtom]
          exact Entry.Value.UnifyRel.rename p unified)

end Frame

def Result.rename (p : Equiv.Perm String) (result : Result) : Result :=
  (Entry.Value.rename p result.1, result.2.rename p)

@[simp] theorem Result.rename_fst (p : Equiv.Perm String) (result : Result) :
    (Result.rename p result).1 = Entry.Value.rename p result.1 := rfl

@[simp] theorem Result.rename_snd (p : Equiv.Perm String) (result : Result) :
    (Result.rename p result).2 = result.2.rename p := rfl

@[simp] theorem Result.rename_id (result : Result) :
    Result.rename (Equiv.refl String) result = result := by
  rcases result with ⟨value, frame⟩
  simp [Result.rename, show (Equiv.refl String : String → String) = id from rfl]

theorem Result.rename_comp (p q : Equiv.Perm String) (result : Result) :
    Result.rename q (Result.rename p result) = Result.rename (q * p) result := by
  rcases result with ⟨value, frame⟩
  simp [Result.rename, Entry.Value.rename_comp, Frame.rename_comp, Equiv.Perm.coe_mul]

@[simp] theorem Result.rename_cancel (p : Equiv.Perm String) (result : Result) :
    Result.rename p.symm (Result.rename p result) = result := by
  rcases result with ⟨value, frame⟩
  simp [Result.rename]

@[simp] theorem Result.rename_cancel_reverse (p : Equiv.Perm String) (result : Result) :
    Result.rename p (Result.rename p.symm result) = result :=
  Result.rename_cancel p.symm result

@[simp] theorem rawResult_rename (p : Equiv.Perm String) (item : Result) :
    rawResult (Result.rename p item) = Renaming.result p (rawResult item) := by
  rcases item with ⟨value, frame⟩
  simp [rawResult, Result.rename, Renaming.result, Entry.Value.rename_erase]

@[simp] theorem sourceResult_rename (p : Equiv.Perm String) (item : Result) :
    sourceResult (Result.rename p item) = Renaming.frameResult p (sourceResult item) := by
  rcases item with ⟨value, frame⟩
  simp [sourceResult, Result.rename, Renaming.frameResult, Entry.Value.rename_erase]

@[simp] theorem readResult_rename (p : Equiv.Perm String) (policy : Policy) (item : Result) :
    readResult policy (Result.rename p item) = Result.rename p (readResult policy item) := by
  rcases item with ⟨value, frame⟩
  simp [readResult, Result.rename]

@[simp] theorem publishResult_rename (p : Equiv.Perm String) (policy : Policy)
    (original : Atom) (item : Result) :
    publishResult policy (renameTypeVars p original) (Result.rename p item) =
      Result.rename p (publishResult policy original item) := by
  rcases item with ⟨value, frame⟩
  simp [publishResult, Result.rename]

theorem CastResultRel.rename (p : Equiv.Perm String)
    {policy : Policy} {lookup : TypeLookupRel} {before : Frame}
    {original : Entry.Value} {expected : Atom} {raw : ResultPair} {item : Result}
    (related : CastResultRel policy lookup before original expected raw item) :
    CastResultRel policy (renameTypeLookup p lookup) (before.rename p)
      (Entry.Value.rename p original) (renameTypeVars p expected)
      (Renaming.result p raw) (Result.rename p item) := by
  rcases related with ⟨readout, renewed, payload⟩
  refine ⟨by rw [rawResult_rename, readout], ?_, ?_⟩
  · rw [Result.rename_snd, Entry.Value.rename_erase]
    exact renewed.rename p
  · have condEq : ((Renaming.result p raw).1 == (Entry.Value.rename p original).erase) =
        (raw.1 == original.erase) := by
      simp [Renaming.result, Entry.Value.rename_erase, (renameTypeVars_perm_injective p).eq_iff]
    rw [Result.rename_fst, condEq, payload]
    split <;> simp [Renaming.result, Entry.Value.rename_ofAtom]

def renameTypeCheck (p : Equiv.Perm String) : Sum Atom Frame → Sum Atom Frame
  | .inl actual => .inl (renameTypeVars p actual)
  | .inr frame => .inr (frame.rename p)

theorem TypeCheckRel.rename (p : Equiv.Perm String)
    {policy : Policy} {expected : Atom} {before : Frame}
    {actual : Atom} {check : Sum Atom Frame}
    (checked : TypeCheckRel policy expected before actual check) :
    TypeCheckRel policy (renameTypeVars p expected) (before.rename p)
      (renameTypeVars p actual) (renameTypeCheck p check) := by
  cases checked with
  | accepted renewed => exact .accepted (renewed.rename p)
  | rejected absent =>
      apply TypeCheckRel.rejected
      intro output matched
      apply absent (renameBindings p.symm output)
      simpa only [Frame.rename_bindings, renameTypeVars_perm_inverse,
        renameBindings_perm_inverse] using matched.rename p.symm

@[simp] theorem checkedFrames_rename (p : Equiv.Perm String) (checks : List (Sum Atom Frame)) :
    checkedFrames (checks.map (renameTypeCheck p)) =
      (checkedFrames checks).map (Frame.rename p) := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      cases check with
      | inl actual => exact ih
      | inr frame => exact congrArg (List.cons (frame.rename p)) ih

@[simp] theorem checkedFailures_rename (p : Equiv.Perm String) (checks : List (Sum Atom Frame)) :
    checkedFailures (checks.map (renameTypeCheck p)) =
      (checkedFailures checks).map (renameTypeVars p) := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      cases check with
      | inl actual => exact congrArg (List.cons (renameTypeVars p actual)) ih
      | inr frame => exact ih

theorem ArgumentChecksRel.rename (p : Equiv.Perm String)
    {context : Space} {lookup : TypeLookupRel} {policy : Policy}
    {expression argument expected : Atom} {position : Nat}
    {frames outputs : List Frame} {errors : List Atom}
    (checked : ArgumentChecksRel context lookup policy expression argument expected
      position frames outputs errors) :
    ArgumentChecksRel (space p context) (renameTypeLookup p lookup) policy
      (renameTypeVars p expression) (renameTypeVars p argument) (renameTypeVars p expected)
      position (frames.map (Frame.rename p)) (outputs.map (Frame.rename p))
      (errors.map (renameTypeVars p)) := by
  induction checked with
  | nil => exact .nil
  | @cons before rest actuals checks outputs errors queried paired _ ih =>
      have checksRenamed :
          List.Forall₂ (TypeCheckRel policy (renameTypeVars p expected) (before.rename p))
            (actuals.map (renameTypeVars p)) (checks.map (renameTypeCheck p)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact paired.imp (fun _ _ item => item.rename p)
      have mappedErrors :
          (checkedFailures (checks.map (renameTypeCheck p))).map
              (fun actual => mkError (renameTypeVars p expression)
                (.badArgType position (renameTypeVars p expected) actual)) ++
            errors.map (renameTypeVars p) =
          ((checkedFailures checks).map
              (fun actual => mkError expression (.badArgType position expected actual)) ++
            errors).map (renameTypeVars p) := by
        simp [checkedFailures_rename, List.map_append, List.map_map,
          Function.comp_def, renamed_badArgType]
      have mappedFrames :
          checkedFrames (checks.map (renameTypeCheck p)) ++ outputs.map (Frame.rename p) =
            (checkedFrames checks ++ outputs).map (Frame.rename p) := by
        simp [checkedFrames_rename, List.map_append]
      rw [← mappedFrames, ← mappedErrors]
      exact .cons
        ((renameTypeLookup_apply p lookup before.bindings argument expected actuals).mpr queried)
        checksRenamed ih

theorem ApplicabilityArgumentsRel.rename (p : Equiv.Perm String)
    {context : Space} {lookup : TypeLookupRel} {policy : Policy}
    {expression : Atom} {position : Nat} {arguments expecteds : List Atom}
    {before after : List Frame} {errors : List Atom}
    (checked : ApplicabilityArgumentsRel context lookup policy expression position
      arguments expecteds before after errors) :
    ApplicabilityArgumentsRel (space p context) (renameTypeLookup p lookup) policy
      (renameTypeVars p expression) position
      (arguments.map (renameTypeVars p)) (expecteds.map (renameTypeVars p))
      (before.map (Frame.rename p)) (after.map (Frame.rename p))
      (errors.map (renameTypeVars p)) := by
  induction checked with
  | nil => exact .nil
  | cons head _ ih =>
      simpa only [List.map_cons, List.map_append] using ApplicabilityArgumentsRel.cons (head.rename p) ih

theorem ApplicationChecksRel.rename (p : Equiv.Perm String)
    {context : Space} {lookup : TypeLookupRel} {policy : Policy}
    {expression expected : Atom} {selected : SelectedTypePolicy}
    {before : Frame} {frames : List Frame} {errors : List Atom}
    (checked : ApplicationChecksRel context lookup policy expression expected selected
      before frames errors) :
    ApplicationChecksRel (space p context) (renameTypeLookup p lookup) policy
      (renameTypeVars p expression) (renameTypeVars p expected)
      (Renaming.policy p selected) (before.rename p)
      (frames.map (Frame.rename p)) (errors.map (renameTypeVars p)) := by
  cases checked with
  | @wrongArity operator arguments shaped arity =>
      simpa only [List.map_nil, List.map_cons, renamed_wrongArity] using
        ApplicationChecksRel.wrongArity
          (operator := renameTypeVars p operator)
          (arguments := arguments.map (renameTypeVars p))
          (by simpa only [renameTypeVars, List.map_cons] using congrArg (renameTypeVars p) shaped)
          (by simpa only [Renaming.policy, List.length_map] using arity)
  | @checked operator arguments afterArguments errors returnChecks shaped argsChecked returnsChecked =>
      have returnsRenamed :
          List.Forall₂
            (fun frame check => TypeCheckRel policy (renameTypeVars p expected)
              frame (Renaming.policy p selected).returnType check)
            (afterArguments.map (Frame.rename p))
            (returnChecks.map (renameTypeCheck p)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact returnsChecked.imp (fun _ _ item => item.rename p)
      have mappedErrors :
          errors.map (renameTypeVars p) ++
            (checkedFailures (returnChecks.map (renameTypeCheck p))).map
              (fun actual => mkError (renameTypeVars p expression)
                (.badType (renameTypeVars p expected) actual)) =
          (errors ++ (checkedFailures returnChecks).map
              (fun actual => mkError expression (.badType expected actual))).map
            (renameTypeVars p) := by
        simp [checkedFailures_rename, List.map_append, List.map_map,
          Function.comp_def, renamed_badType]
      rw [← checkedFrames_rename, ← mappedErrors]
      exact .checked
        (by simpa only [renameTypeVars, List.map_cons] using congrArg (renameTypeVars p) shaped)
        (by simpa only [Renaming.policy, List.map_cons, List.map_nil] using argsChecked.rename p)
        returnsRenamed

def InvocationSelection.rename (p : Equiv.Perm String) :
    InvocationSelection → InvocationSelection
  | .selected signature frames =>
      .selected (Renaming.policy p signature) (frames.map (Frame.rename p))
  | .exhausted errors tupleEligible =>
      .exhausted (errors.map (renameTypeVars p)) tupleEligible

@[simp] theorem InvocationSelection.rename_id (outcome : InvocationSelection) :
    outcome.rename (Equiv.refl String) = outcome := by
  cases outcome with
  | selected signature frames =>
      cases signature
      simp [InvocationSelection.rename, Renaming.policy,
        show (Equiv.refl String : String → String) = id from rfl]
  | exhausted errors tupleEligible =>
      simp [InvocationSelection.rename,
        show (Equiv.refl String : String → String) = id from rfl]

theorem InvocationSelection.rename_comp (p q : Equiv.Perm String) (outcome : InvocationSelection) :
    (outcome.rename p).rename q = outcome.rename (q * p) := by
  cases outcome with
  | selected signature frames =>
      cases signature
      simp [InvocationSelection.rename, Renaming.policy, Frame.rename_comp,
        renameTypeVars_comp, List.map_map, Function.comp_def, Equiv.Perm.coe_mul]
  | exhausted errors tupleEligible =>
      simp [InvocationSelection.rename, renameTypeVars_comp,
        List.map_map, Function.comp_def, Equiv.Perm.coe_mul]

@[simp] theorem InvocationSelection.rename_cancel (p : Equiv.Perm String) (outcome : InvocationSelection) :
    (outcome.rename p).rename p.symm = outcome := by
  cases outcome with
  | selected signature frames =>
      simp [InvocationSelection.rename, List.map_map, Function.comp_def]
  | exhausted errors tupleEligible =>
      simp [InvocationSelection.rename, List.map_map, Function.comp_def]

@[simp] theorem InvocationSelection.rename_cancel_reverse (p : Equiv.Perm String) (outcome : InvocationSelection) :
    (outcome.rename p.symm).rename p = outcome :=
  InvocationSelection.rename_cancel p.symm outcome

theorem InvocationScanRel.rename (p : Equiv.Perm String)
    {context : Space} {lookup : TypeLookupRel} {policy : Policy}
    {expression expected : Atom} {before : Frame}
    {candidates : List Atom} {outcome : InvocationSelection}
    (scanned : InvocationScanRel context lookup policy expression expected before candidates outcome) :
    InvocationScanRel (space p context) (renameTypeLookup p lookup) policy
      (renameTypeVars p expression) (renameTypeVars p expected) (before.rename p)
      (candidates.map (renameTypeVars p)) (outcome.rename p) := by
  induction scanned with
  | nil => exact .nil
  | @nonFunction candidate candidates outcome notArrow _ ih =>
      have notArrowRenamed :
          ¬∃ domains returned, FunctionTypeRel (renameTypeVars p candidate) domains returned := by
        rintro ⟨domains, returned, arrow⟩
        apply notArrow
        refine ⟨domains.map (renameTypeVars p.symm), renameTypeVars p.symm returned, ?_⟩
        simpa only [renameTypeVars_perm_inverse] using
          (functionType_iff p.symm _ _ _).mpr arrow
      cases outcome <;>
        simpa [InvocationSelection.rename] using InvocationScanRel.nonFunction notArrowRenamed ih
  | @selected signature candidates frames errors checked nonempty =>
      simpa only [List.map_cons, InvocationSelection.rename, Renaming.policy] using
        InvocationScanRel.selected (checked.rename p)
          (fun empty => nonempty (List.map_eq_nil_iff.mp empty))
  | @rejected signature candidates errors outcome checked _ ih =>
      have checkedEmpty :
          ApplicationChecksRel (space p context) (renameTypeLookup p lookup) policy
            (renameTypeVars p expression) (renameTypeVars p expected)
            (Renaming.policy p signature) (before.rename p) [] (errors.map (renameTypeVars p)) := by
        simpa only [List.map_nil] using checked.rename p
      cases outcome <;>
        simpa [InvocationSelection.rename, List.map_append, Renaming.policy] using
          InvocationScanRel.rejected checkedEmpty ih

theorem InvocationSelectionRel.rename (p : Equiv.Perm String)
    {context : Space} {lookup : CastLookup} {policy : Policy}
    {live : List Atom} {scope : List String} {expression operator expected : Atom}
    {before : Frame} {outcome : InvocationSelection}
    (selected : InvocationSelectionRel context lookup policy live scope
      expression operator expected before outcome) :
    InvocationSelectionRel (space p context) (renameCastLookup p lookup) policy
      (live.map (renameTypeVars p)) (scope.map p)
      (renameTypeVars p expression) (renameTypeVars p operator) (renameTypeVars p expected)
      (before.rename p) (outcome.rename p) := by
  obtain ⟨candidates, queried, scanned⟩ := selected
  refine ⟨candidates.map (renameTypeVars p), ?_, ?_⟩
  · simpa only [Frame.rename_bindings, invocation_scope, renameCastLookup_apply,
      Atom.undefinedType, atom_symbol] using
      (renameTypeLookup_apply p
        (lookup (invocationTypeScope scope live expression expected before.bindings) context)
        before.bindings operator Atom.undefinedType candidates).mpr queried
  · simpa only [Frame.rename_bindings, invocation_scope, renameCastLookup_apply] using
      scanned.rename p

theorem NativeCompletedReturnRel.rename (p : Equiv.Perm String)
    {context : Space} {lookup : TypeLookupRel} {policy : Policy}
    {value : Entry.Value} {expected : Atom} {frame : Frame} {results : List Result}
    (returned : NativeCompletedReturnRel context lookup policy value expected frame results) :
    NativeCompletedReturnRel (space p context) (renameTypeLookup p lookup) policy
      (Entry.Value.rename p value) (renameTypeVars p expected) (frame.rename p)
      (results.map (Result.rename p)) := by
  cases returned with
  | keep kept =>
      simpa only [List.map_cons, List.map_nil, Result.rename] using
        NativeCompletedReturnRel.keep
          (by simpa only [Entry.Value.rename_erase, completed_keep] using kept)
  | @cast raw results notKeep batch paired =>
      have batchRenamed :
          TypeCastBatchRel (space p context) (Entry.Value.rename p value).erase
            (renameTypeVars p expected) (frame.rename p).bindings
            (Renaming.results p raw)
            (lookup := renameTypeLookup p lookup) (matching := policy.matching.Rel) := by
        simpa only [Entry.Value.rename_erase, Frame.rename_bindings] using batch.rename p
      have pairedRenamed :
          List.Forall₂
            (CastResultRel policy (renameTypeLookup p lookup) (frame.rename p)
               (Entry.Value.rename p value) (renameTypeVars p expected))
            (Renaming.results p raw) (results.map (Result.rename p)) := by
        change List.Forall₂ _ (raw.map (Renaming.result p)) (results.map (Result.rename p))
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact paired.imp (fun _ _ item => item.rename p)
      exact .cast
        (by simpa only [Entry.Value.rename_erase, completed_keep] using notKeep)
        batchRenamed pairedRenamed

def ArgumentRequest.rename (p : Equiv.Perm String) (request : ArgumentRequest) : ArgumentRequest :=
  (Entry.Value.rename p request.1, renameTypeVars p request.2)

@[simp] theorem ArgumentRequest.rename_fst (p : Equiv.Perm String) (request : ArgumentRequest) :
    (ArgumentRequest.rename p request).1 = Entry.Value.rename p request.1 := rfl

@[simp] theorem ArgumentRequest.rename_snd (p : Equiv.Perm String) (request : ArgumentRequest) :
    (ArgumentRequest.rename p request).2 = renameTypeVars p request.2 := rfl

@[simp] theorem ArgumentRequest.rename_id (request : ArgumentRequest) :
    ArgumentRequest.rename (Equiv.refl String) request = request := by
  rcases request with ⟨value, expected⟩
  simp [ArgumentRequest.rename, show (Equiv.refl String : String → String) = id from rfl]

theorem ArgumentRequest.rename_comp (p q : Equiv.Perm String) (request : ArgumentRequest) :
    ArgumentRequest.rename q (ArgumentRequest.rename p request) =
      ArgumentRequest.rename (q * p) request := by
  rcases request with ⟨value, expected⟩
  simp [ArgumentRequest.rename, Entry.Value.rename_comp, renameTypeVars_comp,
    Function.comp_def, Equiv.Perm.coe_mul]

@[simp] theorem ArgumentRequest.rename_cancel (p : Equiv.Perm String) (request : ArgumentRequest) :
    ArgumentRequest.rename p.symm (ArgumentRequest.rename p request) = request := by
  rcases request with ⟨value, expected⟩
  simp [ArgumentRequest.rename]

@[simp] theorem ArgumentRequest.rename_cancel_reverse (p : Equiv.Perm String) (request : ArgumentRequest) :
    ArgumentRequest.rename p (ArgumentRequest.rename p.symm request) = request :=
  ArgumentRequest.rename_cancel p.symm request

@[simp] theorem argumentScope_rename (p : Equiv.Perm String) (requests : List ArgumentRequest) :
    argumentScope (requests.map (ArgumentRequest.rename p)) =
      (argumentScope requests).map (renameTypeVars p) := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
      rcases request with ⟨value, expected⟩
      change (Entry.Value.rename p value).erase :: renameTypeVars p expected ::
          argumentScope (rest.map (ArgumentRequest.rename p)) =
        renameTypeVars p value.erase :: renameTypeVars p expected ::
          (argumentScope rest).map (renameTypeVars p)
      rw [Entry.Value.rename_erase, ih]

@[simp] theorem ArgumentStopped.rename_iff (p : Equiv.Perm String)
    (original : Entry.Value) (item : Result) :
    ArgumentStopped (Entry.Value.rename p original) (Result.rename p item) ↔
      ArgumentStopped original item := by
  rcases item with ⟨value, frame⟩
  simp [ArgumentStopped, Result.rename, Entry.Value.rename_erase,
    (renameTypeVars_perm_injective p).eq_iff]

@[simp] theorem argumentPrepend_rename (p : Equiv.Perm String)
    (head : Entry.Value) (item : Result) :
    argumentPrepend (Entry.Value.rename p head) (Result.rename p item) =
      Result.rename p (argumentPrepend head item) := by
  rcases item with ⟨value, frame⟩
  unfold argumentPrepend
  simp only [Result.rename_fst, Result.rename_snd, Entry.Value.unpackArguments_rename]
  cases value.unpackArguments <;> simp [Result.rename]

@[simp] theorem functionAssemble_rename (p : Equiv.Perm String)
    (head : Entry.Value) (item : Result) :
    functionAssemble (Entry.Value.rename p head) (Result.rename p item) =
      Result.rename p (functionAssemble head item) := by
  rcases item with ⟨value, frame⟩
  unfold functionAssemble
  simp only [Result.rename_fst, Result.rename_snd, Entry.Value.unpackArguments_rename]
  cases value.unpackArguments <;> simp [Result.rename]

@[simp] theorem invocationReturnType_rename (p : Equiv.Perm String) (signature : SelectedTypePolicy) :
    invocationReturnType (Renaming.policy p signature) =
      renameTypeVars p (invocationReturnType signature) := by
  by_cases isExpression : signature.returnType = .symbol "Expression" <;>
    simp [invocationReturnType, Renaming.policy, Atom.expressionType, Atom.undefinedType, isExpression]

@[simp] theorem diagnosticResults_rename (p : Equiv.Perm String)
    (errors : List Atom) (frame : Frame) :
    diagnosticResults (errors.map (renameTypeVars p)) (frame.rename p) =
      (diagnosticResults errors frame).map (Result.rename p) := by
  simp [diagnosticResults, List.map_map, Function.comp_def, Result.rename, Entry.Value.rename_ofAtom]

@[simp] theorem tupleSingleton_rename (p : Equiv.Perm String) (item : Result) :
    tupleSingleton (Result.rename p item) = Result.rename p (tupleSingleton item) := by
  rcases item with ⟨value, frame⟩
  unfold tupleSingleton
  simp only [Result.rename_fst, Result.rename_snd, Entry.Value.rename_erase,
    Entry.isEmptyOrError_renameTypeVars]
  split <;> simp [Result.rename]

@[simp] theorem tuplePrepend_rename (p : Equiv.Perm String) (head : Entry.Value) (item : Result) :
    tuplePrepend (Entry.Value.rename p head) (Result.rename p item) =
      Result.rename p (tuplePrepend head item) := by
  rcases item with ⟨value, frame⟩
  unfold tuplePrepend
  simp only [Result.rename_fst, Result.rename_snd, Entry.Value.rename_erase,
    Entry.isEmptyOrError_renameTypeVars]
  split
  · rfl
  · cases value <;> simp [Result.rename]

@[simp] theorem FunctionPending.rename_iff (p : Equiv.Perm String)
    (policy : Policy) (value : Entry.Value) :
    FunctionPending policy (Entry.Value.rename p value) ↔ FunctionPending policy value := by
  simp [FunctionPending, Entry.Value.rename_erase, Entry.Value.rename_status]

@[simp] theorem substituteBinder_rename (p : Equiv.Perm String) (policy : Policy)
    (name : String) (value template : Entry.Value) :
    substituteBinder policy (p name) (Entry.Value.rename p value) (Entry.Value.rename p template) =
      Entry.Value.rename p (substituteBinder policy name value template) := by
  unfold substituteBinder
  have envEq : (fun key => if key = p name then Entry.Value.rename p value else .var key) =
      fun key => Entry.Value.rename p (if p.symm key = name then value else .var (p.symm key)) := by
    funext key
    by_cases same : p.symm key = name
    · have mapped : key = p name := by rw [← same, p.apply_symm_apply]
      simp [mapped]
    · have mapped : key ≠ p name := fun eq => same (by rw [eq, p.symm_apply_apply])
      simp [same, mapped]
  rw [envEq]
  exact Entry.Value.substitute_rename p policy.rebuilding
    (fun key => if key = name then value else .var key) template

def Boundary.rename (p : Equiv.Perm String) : Boundary → Boundary
  | .chain name template => .chain (p name) (Entry.Value.rename p template)
  | .body => .body
  | .functionDone => .functionDone
  | .producer => .producer
  | .returned original expected =>
      .returned (Entry.Value.rename p original) (renameTypeVars p expected)
  | .native original expected provenance =>
      .native (Entry.Value.rename p original) (expected.map (renameTypeVars p)) provenance

@[simp] theorem Boundary.rename_id (boundary : Boundary) :
    boundary.rename (Equiv.refl String) = boundary := by
  cases boundary <;>
    simp [Boundary.rename, show (Equiv.refl String : String → String) = id from rfl]

theorem Boundary.rename_comp (p q : Equiv.Perm String) (boundary : Boundary) :
    (boundary.rename p).rename q = boundary.rename (q * p) := by
  cases boundary <;>
    simp [Boundary.rename, Entry.Value.rename_comp, renameTypeVars_comp,
      Option.map_map, Function.comp_def, Equiv.Perm.coe_mul]

@[simp] theorem Boundary.rename_cancel (p : Equiv.Perm String) (boundary : Boundary) :
    (boundary.rename p).rename p.symm = boundary := by
  cases boundary <;>
    simp [Boundary.rename, Option.map_map, Function.comp_def]

@[simp] theorem Boundary.rename_cancel_reverse (p : Equiv.Perm String) (boundary : Boundary) :
    (boundary.rename p.symm).rename p = boundary :=
  Boundary.rename_cancel p.symm boundary

theorem SuccessPriorityRel.rename_results (p : Equiv.Perm String)
    {raw selected : List Result}
    (priority : SuccessPriorityRel (fun item : Result => isErrorAtom item.1.erase) raw selected) :
    SuccessPriorityRel (fun item : Result => isErrorAtom item.1.erase)
      (raw.map (Result.rename p)) (selected.map (Result.rename p)) :=
  priority.map (Result.rename p) (fun item => by
    simp [Result.rename, Entry.Value.rename_erase, Entry.isErrorAtom_renameTypeVars])

@[simp] theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Eval.Entry.Value.rename_id_fun :
    Entry.Value.rename id = id := by
  funext value
  exact Entry.Value.rename_id value

@[simp] theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.EquationWork.rename_id_fun :
    EquationWork.rename (Equiv.refl String) = id := by
  funext work
  exact EquationWork.rename_id work

@[simp] theorem Result.rename_id_fun :
    Result.rename (Equiv.refl String) = id := by
  funext result
  exact Result.rename_id result

@[simp] theorem ArgumentRequest.rename_id_fun :
    ArgumentRequest.rename (Equiv.refl String) = id := by
  funext request
  exact ArgumentRequest.rename_id request

@[simp] theorem Boundary.rename_id_fun :
    Boundary.rename (Equiv.refl String) = id := by
  funext boundary
  exact Boundary.rename_id boundary

@[simp] theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming.policy_id
    (signature : SelectedTypePolicy) :
    Renaming.policy (Equiv.refl String) signature = signature := by
  cases signature
  simp [Renaming.policy, show (Equiv.refl String : String → String) = id from rfl]

@[simp] theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming.policy_comp
    (p q : Equiv.Perm String) (signature : SelectedTypePolicy) :
    Renaming.policy q (Renaming.policy p signature) = Renaming.policy (q * p) signature := by
  cases signature
  simp [Renaming.policy, renameTypeVars_comp, List.map_map, Function.comp_def, Equiv.Perm.coe_mul]

@[simp] theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming.space_id
    (context : Space) :
    Renaming.space (Equiv.refl String) context = context := by
  cases context
  simp [Renaming.space, show (Equiv.refl String : String → String) = id from rfl]

@[simp] theorem _root_.Mettapedia.Languages.MeTTa.HE.Spec.Eval.Renaming.space_comp
    (p q : Equiv.Perm String) (context : Space) :
    Renaming.space q (Renaming.space p context) = Renaming.space (q * p) context := by
  cases context
  simp [Renaming.space, renameTypeVars_comp, List.map_map, Function.comp_def, Equiv.Perm.coe_mul]

end Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
