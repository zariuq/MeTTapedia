import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec

/-!
# Scoped query answers through a read-only transform effect

Preparation retains each occurrence and its own computed source substitution.
The independent PeTTa queryBodies function specifies the resulting evaluation
requests. An admitted read-only effect preserves the store; it does not erase
those requests or turn their templates into data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaQueryInterpretation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open PeTTa.Unifying (unify rename Control queryBodies)
open PeTTaStoreSelection (atomFrames)

variable {O : Type} (label : O → Atom)

def scan (bindings : Subst) (pattern : Atom) : Nat → List O → Option (List (O × Subst))
  | _, [] => some []
  | use, occurrence :: rest => do
      let later ← scan bindings pattern (use + 1) rest
      match unify bindings pattern (rename use (label occurrence)) with
      | .ok bound => some ((occurrence, bound) :: later)
      | .clash => some later
      | .exhausted => none

def continuations (body : Atom) (packets : List (O × Subst)) : List Control :=
  packets.map fun row => .evaluate row.2 body

/-- Whole source computation, including exhaustion, equals the independently
prepared occurrence packets followed by continuation construction. -/
theorem scan_source (bindings : Subst) (pattern body : Atom) (use : Nat) (rows : List O) :
    queryBodies bindings pattern body use (rows.map label) =
      (scan label bindings pattern use rows).map (continuations body) := by
  induction rows generalizing use with
  | nil => rfl
  | cons occurrence rest ih =>
      simp only [List.map_cons, queryBodies, scan, ih]
      cases later : scan label bindings pattern (use + 1) rest with
      | none => simp
      | some packets =>
          cases matched : unify bindings pattern (rename use (label occurrence)) <;>
            simp [continuations]

theorem scanned_occurrences_sublist (bindings : Subst) (pattern : Atom) (use : Nat)
    (rows : List O) (packets : List (O × Subst))
    (prepared : scan label bindings pattern use rows = some packets) :
    (packets.map Prod.fst).Sublist rows := by
  induction rows generalizing use packets with
  | nil =>
      simp only [scan, Option.some.injEq] at prepared
      subst packets
      exact .slnil
  | cons occurrence rest ih =>
      cases later : scan label bindings pattern (use + 1) rest with
      | none => simp [scan, later] at prepared
      | some remaining =>
          have inherited := ih _ _ later
          cases matched : unify bindings pattern (rename use (label occurrence)) with
          | ok bound =>
              simp [scan, later, matched] at prepared
              subst packets
              exact inherited.cons_cons _
          | clash =>
              simp [scan, later, matched] at prepared
              subst packets
              exact inherited.cons _
          | exhausted => simp [scan, later, matched] at prepared

def request (packets : List (O × Subst)) : OrderedStore.Publication Atom O :=
  ⟨⟨[], packets.map Prod.fst, []⟩, []⟩

variable [DecidableEq O]

theorem prepared_admitted (bindings : Subst) (pattern : Atom) (use : Nat)
    (rows : List O) (packets : List (O × Subst))
    (prepared : scan label bindings pattern use rows = some packets) (unique : rows.Nodup)
    (knowledge : EquationStore Atom) (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, rows)) (request packets) := by
  refine ⟨⟨unique, List.nodup_nil, List.nodup_nil⟩, ?_, consistent⟩
  refine ⟨by simp [request, OrderedStore.Publication.commit, Selection.commit], ?_,
    by simp [request, OrderedStore.Publication.commit, Selection.commit],
    by simp [request, OrderedStore.Publication.commit, Selection.commit], ?_⟩
  · intro occurrence member
    exact List.mem_toFinset.mpr ((scanned_occurrences_sublist label bindings pattern use rows packets prepared).subset
      (List.mem_toFinset.mp member))
  · intro query member
    simp [request, OrderedStore.Publication.commit] at member

theorem read_preserves_store (knowledge : EquationStore Atom) (rows : List O)
    (packets : List (O × Subst))
    (admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, rows))
      (request packets)) :
    (OrderedStore.step atomFrames PUnit.unit label).result (request packets) admitted = (knowledge, rows) := by
  apply Prod.ext
  · exact OrderedStore.result_knowledge atomFrames PUnit.unit label admitted
  · rw [OrderedStore.result_rows]
    exact OrderedStore.reads_only _ _

/-- Preservation and reflection include the actual branch-local evaluation
requests and the target's unchanged world, not just its answer count. -/
theorem query_iff_target (bindings : Subst) (pattern body : Atom) (use : Nat)
    (rows : List O) (unique : rows.Nodup) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) (tasks : List Control) :
    queryBodies bindings pattern body use (rows.map label) = some tasks ↔
      ∃ packets, scan label bindings pattern use rows = some packets ∧
        continuations body packets = tasks ∧
        ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
            (s := (knowledge, rows)) (request packets),
          (OrderedStore.step atomFrames PUnit.unit label).result (request packets) admitted = (knowledge, rows) := by
  rw [scan_source]
  constructor
  · intro source
    obtain ⟨packets, prepared, same⟩ := Option.map_eq_some_iff.mp source
    have admitted := prepared_admitted label bindings pattern use rows packets prepared unique knowledge consistent
    exact ⟨packets, prepared, same, admitted, read_preserves_store label knowledge rows packets admitted⟩
  · rintro ⟨packets, prepared, same, _, _⟩
    simp [prepared, same]

omit [DecidableEq O] in
/-- The resulting requests enter the actual source continuation, retaining
all caller frames and advancing the source's renaming-use counter. -/
theorem source_query_transition (registry : PeTTa.SpaceSemantics.Program)
    (source : PeTTa.Unifying.Configuration) (answer : PeTTa.Unifying.Answer)
    (pattern body : Atom) (rest : List PeTTa.Unifying.Frame) (rows : List O)
    (packets : List (O × Subst))
    (control : source.control = .returned [answer])
    (frames : source.frames = .query pattern body :: rest)
    (opened : (PeTTa.Effects.readHandle answer.value >>= source.state.read) = some (rows.map label))
    (prepared : scan label answer.bindings pattern source.uses rows = some packets) :
    PeTTa.Unifying.Transition registry source
      { source with
        control := .sequence (continuations body packets) []
        frames := rest
        uses := source.uses + rows.length } := by
  apply PeTTa.Unifying.Transition.query_return control frames
  simp [PeTTa.Unifying.queries, opened, scan_source, prepared]

/-- This joins the read effect to the real evaluator continuation. The
unchanged target store does not suppress body evaluation requests. -/
theorem query_effect_and_continuation (registry : PeTTa.SpaceSemantics.Program)
    (source : PeTTa.Unifying.Configuration) (answer : PeTTa.Unifying.Answer)
    (pattern body : Atom) (rest : List PeTTa.Unifying.Frame) (rows : List O)
    (packets : List (O × Subst))
    (control : source.control = .returned [answer])
    (frames : source.frames = .query pattern body :: rest)
    (opened : (PeTTa.Effects.readHandle answer.value >>= source.state.read) = some (rows.map label))
    (prepared : scan label answer.bindings pattern source.uses rows = some packets)
    (unique : rows.Nodup) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
        (s := (knowledge, rows)) (request packets),
      (OrderedStore.step atomFrames PUnit.unit label).result (request packets) admitted = (knowledge, rows) ∧
      PeTTa.Unifying.Transition registry source
        { source with
          control := .sequence (continuations body packets) []
          frames := rest
          uses := source.uses + rows.length } := by
  have admitted := prepared_admitted label answer.bindings pattern source.uses rows packets
    prepared unique knowledge consistent
  exact ⟨admitted, read_preserves_store label knowledge rows packets admitted,
    source_query_transition label registry source answer pattern body rest rows packets control frames opened prepared⟩

omit [DecidableEq O] in
theorem exhaustion_is_not_empty (bindings : Subst) (pattern body : Atom) (use : Nat)
    (rows : List O) (exhausted : scan label bindings pattern use rows = none) :
    queryBodies bindings pattern body use (rows.map label) = none ∧
      queryBodies bindings pattern body use (rows.map label) ≠ some [] := by
  rw [scan_source, exhausted]
  simp

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaQueryInterpretation
