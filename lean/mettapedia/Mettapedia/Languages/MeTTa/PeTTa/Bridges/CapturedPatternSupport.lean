import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedOnceSource
import Mettapedia.Logic.LP.UnificationReadSupport

/-! A closed principal reading does not remove captured names from the retained
frame. Only the raw query-pattern position is replaced in these support laws;
they do not authorize substitution into evaluated source bodies. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPatternSupport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open LiteralQuerySource (Request)
open ClosedOnceQueryFrame (Frame)

theorem mem_expression_names (items : List Atom) (name : String) :
    name ∈ (encode (.expression items)).freeVars ↔ ∃ item ∈ items, name ∈ (encode item).freeVars := by
  rw [encode, Mettapedia.Logic.LP.Term.mem_freeVars_app (σ := signature)]
  constructor
  · rintro ⟨index, member⟩
    exact ⟨items[index], List.getElem_mem index.isLt, member⟩
  · rintro ⟨item, member, occurs⟩
    obtain ⟨index, same⟩ := List.mem_iff_get.mp member
    refine ⟨index, ?_⟩
    change name ∈ (encode (items.get index)).freeVars
    rw [same]
    exact occurs

theorem literal_names_empty (atom : Atom) (literal : SpaceSemantics.Literal atom) :
    (encode atom).freeVars = ∅ := by
  induction literal with
  | symbol => simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  | grounded => simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  | expression items _ _ ih =>
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro name occurs
      obtain ⟨item, member, used⟩ := (mem_expression_names items name).mp occurs
      rw [ih item member] at used
      exact Finset.notMem_empty name used

theorem source_names_bound (bindings : Equations) (principal : Environment) (patternCode : Atom) (request : Request)
    (resolved : resolve bindings = some principal) (reading : read principal patternCode = request.pattern) :
    (encode patternCode).freeVars ⊆ Mettapedia.Logic.LP.eqVars (equations bindings) := by
  have relevant := Mettapedia.Logic.LP.unifyTotal_relevantIdempotent (equations bindings) principal resolved
  apply relevant.ground_source_freeVars_subset
  have encoded := congrArg encode reading
  simp only [EagerDFS.Destination.read, encode_decode] at encoded
  rw [encoded, literal_names_empty request.pattern request.literal]

theorem equation_names_in_control (control : Control) :
    Mettapedia.Logic.LP.eqVars (equations control.bindings) ⊆ control.support := by
  intro name occurs
  obtain ⟨pair, member, used⟩ := (Mettapedia.Logic.LP.mem_eqVars (equations := equations control.bindings)).mp occurs
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact ClosedOnceQueryFrame.binding_names_in_support control original present (Finset.mem_union.mpr used)

theorem source_names_retained (control : Control) (principal : Environment) (patternCode : Atom) (request : Request)
    (resolved : resolve control.bindings = some principal) (reading : read principal patternCode = request.pattern) :
    (encode patternCode).freeVars ⊆ control.support :=
  (source_names_bound control.bindings principal patternCode request resolved reading).trans (equation_names_in_control control)

theorem query_names (request : Request) (patternCode : Atom) :
    (encode (CapturedOnceSource.query request patternCode)).freeVars = (encode patternCode).freeVars := by
  ext name
  rw [CapturedOnceSource.query, mem_expression_names]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [LiteralQuerySource.handle_freeVars, request.scalar.freeVars]
  simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem once_names (request : Request) (patternCode : Atom) :
    (encode (CapturedOnceSource.source request patternCode)).freeVars = (encode patternCode).freeVars := by
  ext name
  rw [CapturedOnceSource.source, mem_expression_names]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  rw [query_names]
  simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem evaluate_support (control : Control) (expression destination : Atom) :
    ({control with goals := .evaluate expression destination :: control.goals} : Control).support =
      control.support ∪ (encode expression).freeVars ∪ (encode destination).freeVars := by
  ext name
  simp only [Control.support, Finset.mem_union]
  rw [ClosedOnceQueryFrame.fold_support_iff, ClosedOnceQueryFrame.fold_support_iff]
  simp only [Goal.atoms, List.flatMap_cons, List.mem_cons, List.mem_append,
    Finset.notMem_empty, false_or]
  simp only [or_and_right, exists_or, exists_eq_left]
  simp only [List.not_mem_nil, false_and, exists_false, or_false]
  ac_nf

/-- The complete retained binding frame already covers every variable of the
captured query. Literalizing its raw pattern cannot shrink the source support. -/
theorem initial_support (frame : Frame) (request : Request) (patternCode : Atom)
    (principal : Environment) (resolved : resolve frame.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    (CapturedOnceSource.initial frame request patternCode).support =
      (CapturedOnceSource.initial frame request request.pattern).support := by
  let base : Control := {
    bindings := frame.bindings, goals := [], destination := .var frame.output,
    reserved := frame.reserved, cutBoundary := frame.boundary}
  have bounded : (encode patternCode).freeVars ⊆ base.support :=
    source_names_retained base principal patternCode request resolved reading
  have literal := literal_names_empty request.pattern request.literal
  change ({base with goals := .evaluate (CapturedOnceSource.source request patternCode) (.var frame.output) :: base.goals} : Control).support =
    ({base with goals := .evaluate (CapturedOnceSource.source request request.pattern) (.var frame.output) :: base.goals} : Control).support
  rw [evaluate_support, evaluate_support, once_names, once_names, literal,
    Finset.union_eq_left.mpr bounded, Finset.union_empty]

theorem initial_freshName (frame : Frame) (request : Request) (patternCode : Atom)
    (principal : Environment) (resolved : resolve frame.bindings = some principal)
    (reading : read principal patternCode = request.pattern) (index : Nat) :
    freshName (CapturedOnceSource.initial frame request patternCode) index =
      freshName (CapturedOnceSource.initial frame request request.pattern) index := by
  simp only [freshName, initial_support frame request patternCode principal resolved reading]

theorem calling_support (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat)
    (principal : Environment) (resolved : resolve frame.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    (CapturedOnceSource.calling frame request patternCode kept).support =
      (CapturedOnceSource.calling frame request request.pattern kept).support := by
  let base : Control := {
    bindings := frame.bindings, goals := [.commit, .restoreCommit frame.boundary],
    destination := .var frame.output, reserved := frame.reserved, cutBoundary := kept}
  have bounded : (encode patternCode).freeVars ⊆ base.support :=
    source_names_retained base principal patternCode request resolved reading
  have literal := literal_names_empty request.pattern request.literal
  change ({base with goals := .evaluate (CapturedOnceSource.query request patternCode) (.var frame.output) :: base.goals} : Control).support =
    ({base with goals := .evaluate (CapturedOnceSource.query request request.pattern) (.var frame.output) :: base.goals} : Control).support
  rw [evaluate_support, evaluate_support, query_names, query_names, literal,
    Finset.union_eq_left.mpr bounded, Finset.union_empty]

theorem location_eq_literal (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat)
    (principal : Environment) (resolved : resolve frame.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    CapturedOnceSource.location frame request patternCode kept = ClosedOnceQueryFrame.location frame request kept := by
  change freshName (CapturedOnceSource.calling frame request patternCode kept) 0 =
    freshName (CapturedOnceSource.calling frame request request.pattern kept) 0
  simp only [freshName, calling_support frame request patternCode kept principal resolved reading]

/-- Raw and literal once executions meet before collection copying: their
answer packets include exactly the same prepared equations and origin path. -/
theorem answer_eq_literal (frame : Frame) (request : Request) (patternCode : Atom) (kept : Nat) (origins : List Nat)
    (principal : Environment) (resolved : resolve frame.bindings = some principal)
    (reading : read principal patternCode = request.pattern) :
    CapturedOnceSource.answer frame request patternCode kept origins =
      ClosedOnceQueryFrame.answer frame request kept origins := by
  simp only [CapturedOnceSource.answer, CapturedOnceSource.acceptedBindings, CapturedOnceSource.ready,
    ClosedOnceQueryFrame.answer, ClosedOnceQueryFrame.acceptedBindings, ClosedOnceQueryFrame.ready,
    location_eq_literal frame request patternCode kept principal resolved reading]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPatternSupport
