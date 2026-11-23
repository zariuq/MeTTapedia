import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution

/-!
# Membership in ordered reflective sink batches

For a fixed atom, a staged sink retains its current membership, sets it, or
clears it. Authored order composes these updates. Head and tail use the
selected extrema of the actual staged support.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def reflectiveSinkMembership (rows : List Subst) (candidate : Atom) (sink : Sink) :
    Option Bool :=
  let staged := rows.foldl (stageReflectiveSupportSink sink) []
  match sink with
  | .add _ => if candidate ∈ staged then some true else none
  | .remove _ => if candidate ∈ staged then some false else none
  | .head count _ => if candidate ∈ compactExtrema true count staged then some true else none
  | .tail count _ => if candidate ∈ compactExtrema false count staged then some true else none

def reflectiveBatchMembership (rows : List Subst) (candidate : Atom) :
    List Sink → Option Bool
  | [] => none
  | sink :: rest => (reflectiveBatchMembership rows candidate rest).orElse
      (fun _ => reflectiveSinkMembership rows candidate sink)

theorem decide_mem_reflective_finalize (rows : List Subst) (candidate : Atom)
    (sink : Sink) (space : Space) :
    decide (candidate ∈ reflectiveSupportSinkProvider.finalize sink
        (reflectiveSupportSinkProvider.stageAll sink rows) space) =
      (reflectiveSinkMembership rows candidate sink).getD (decide (candidate ∈ space)) := by
  cases sink <;>
    simp only [reflectiveSinkMembership, reflectiveSupportSinkProvider,
      BatchSinkProvider.stageAll, finalizeSupportSink, Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset] <;>
    split <;> simp_all

theorem decide_mem_reflective_run (rows : List Subst) (candidate : Atom)
    (sinks : List Sink) (space : Space) :
    decide (candidate ∈ reflectiveSupportSinkProvider.run rows space sinks) =
      (reflectiveBatchMembership rows candidate sinks).getD (decide (candidate ∈ space)) := by
  induction sinks generalizing space with
  | nil => rfl
  | cons sink rest induction =>
      rw [BatchSinkProvider.run_cons, induction, decide_mem_reflective_finalize]
      cases later : reflectiveBatchMembership rows candidate rest <;>
        simp only [reflectiveBatchMembership, later, Option.orElse, Option.getD]

theorem reflectiveBatchMembership_append
    (rows : List Subst) (candidate : Atom) (first last : List Sink) :
    reflectiveBatchMembership rows candidate (first ++ last) =
      (reflectiveBatchMembership rows candidate last).orElse
        (fun _ => reflectiveBatchMembership rows candidate first) := by
  induction first with
  | nil =>
      cases later : reflectiveBatchMembership rows candidate last <;>
        simp only [List.nil_append, reflectiveBatchMembership, later, Option.orElse]
  | cons sink rest induction =>
      cases later : reflectiveBatchMembership rows candidate last <;>
        simp only [List.cons_append, reflectiveBatchMembership, induction, later, Option.orElse]

private theorem reflectiveSinkMembership_ne_false_of_not_remove
    (rows : List Subst) (candidate : Atom) (sink : Sink) (guard : (!sink.isRemove) = true) :
    reflectiveSinkMembership rows candidate sink ≠ some false := by
  cases sink <;> simp_all [reflectiveSinkMembership, Sink.isRemove]

private theorem reflectiveBatchMembership_ne_false_of_no_removes
    (rows : List Subst) (candidate : Atom) (sinks : List Sink)
    (guard : sinks.all (fun sink => !sink.isRemove) = true) :
    reflectiveBatchMembership rows candidate sinks ≠ some false := by
  induction sinks with
  | nil => simp [reflectiveBatchMembership]
  | cons sink rest induction =>
      simp only [List.all_cons, Bool.and_eq_true] at guard
      cases later : reflectiveBatchMembership rows candidate rest with
      | none =>
          simpa only [reflectiveBatchMembership, later, Option.orElse] using
            reflectiveSinkMembership_ne_false_of_not_remove rows candidate sink guard.1
      | some outcome =>
          simpa only [reflectiveBatchMembership, later, Option.orElse] using induction guard.2

private theorem reflectiveSinkMembership_add_of_row
    {rows : List Subst} {candidate template : Atom} {row : Subst}
    (matched : row ∈ rows)
    (instantiated : instantiateTemplateAtom? row template = some candidate) :
    reflectiveSinkMembership rows candidate (.add template) = some true := by
  have staged : candidate ∈ (rows.foldl (stageReflectiveSupportSink (.add template)) []) :=
    (mem_foldl_stageReflectiveSupportSink_iff _ _ _ _).mpr
      (Or.inr ⟨row, matched, instantiated⟩)
  simp only [reflectiveSinkMembership, staged, if_pos]

/-- A matched add contributes its atom at its authored position. A suffix
without remove sinks preserves that contribution. -/
theorem reflectiveBatchMembership_add_at
    {rows : List Subst} {candidate template : Atom} {row : Subst}
    (sinks : List Sink) (index : Nat)
    (selected : sinks[index]? = some (.add template))
    (suffix : (sinks.drop (index + 1)).all (fun sink => !sink.isRemove) = true)
    (matched : row ∈ rows)
    (instantiated : instantiateTemplateAtom? row template = some candidate) :
    reflectiveBatchMembership rows candidate sinks = some true := by
  induction sinks generalizing index with
  | nil => simp at selected
  | cons sink rest induction =>
      cases index with
      | zero =>
          have same : sink = .add template := Option.some.inj selected
          subst sink
          have after := reflectiveBatchMembership_ne_false_of_no_removes rows candidate rest suffix
          cases later : reflectiveBatchMembership rows candidate rest with
          | none =>
              simp only [reflectiveBatchMembership, later, Option.orElse]
              exact reflectiveSinkMembership_add_of_row matched instantiated
          | some outcome =>
              cases outcome
              · exact (after later).elim
              · simp only [reflectiveBatchMembership, later, Option.orElse]
      | succ index =>
          have later := induction index selected suffix
          simp only [reflectiveBatchMembership, later, Option.orElse]

theorem mem_fireReflectiveSourceExecFact_of_add_at
    (space : Space) (directive : SourceExecFact) (index : Nat)
    {row : Subst} {candidate template : Atom}
    (selected : directive.rule.tmpl.sinks[index]? = some (.add template))
    (suffix : (directive.rule.tmpl.sinks.drop (index + 1)).all
      (fun sink => !sink.isRemove) = true)
    (matched : row ∈ (matchInputSpec [] (readCopyAtom space directive.atom)
      directive.rule.input).map Prod.fst)
    (instantiated : instantiateTemplateAtom? row template = some candidate) :
    candidate ∈ fireReflectiveSourceExecFact space directive := by
  have member := decide_mem_reflective_run
    ((matchInputSpec [] (readCopyAtom space directive.atom)
      directive.rule.input).map Prod.fst)
    candidate directive.rule.tmpl.sinks (consumeAtom space directive.atom)
  rw [reflectiveBatchMembership_add_at _ _ selected suffix matched instantiated] at member
  exact of_decide_eq_true member

section Controls

private def token : Atom := .symbol "receipt"

example : reflectiveBatchMembership [[]] token [.remove token, .add token] = some true :=
  by decide +kernel

example : reflectiveBatchMembership [[]] token [.add token, .remove token] = some false :=
  by decide +kernel

example : reflectiveBatchMembership [[]] token [.add (.var "missing")] = none :=
  by decide +kernel

example : reflectiveBatchMembership [[]] token [.head 0 token] = none :=
  by decide +kernel

end Controls

end Mettapedia.Languages.ProcessCalculi.MORK
