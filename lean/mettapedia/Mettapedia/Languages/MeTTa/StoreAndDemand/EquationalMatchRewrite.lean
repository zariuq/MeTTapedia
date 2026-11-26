import Mettapedia.GSLT.Equations.OccurrenceChoices
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.QuantifiedPremise

/-! # Per-occurrence replacement in a scoped Transform step

A modulo matcher can return several bindings for one entry occurrence.
This adapter takes the finite fibre of admissible, literal replacement
blocks at the entry cut. A per-occurrence choice supplies an exact
quantified take premise, so the existing Transform step provides the
publication. If all output blocks agree at the selected observation,
every exact group agrees at that observation, independently of which
match witnesses were found.

These theorems do not turn an incomplete search or a refused template
into an empty fibre. The finite answers are assumed complete for the
chosen match/instantiation relation; that is the producer's obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.StoreAndDemand.EquationalMatchRewrite

open Mettapedia.GSLT.Equations.OccurrenceChoices
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax (State Program Firing)
open RuleSyntax.OneFrame (Terms frames ext)
open RuleSyntax.QuantifiedPremise (Entry Group Mode ScopedRelation scopedStep scopedStep_admits_iff)

universe u v w

variable {O : Type u} {T : Type v} {S : Type w}

/-- Materialize chosen entries in the given order. The admission theorem
requires a well-aligned plan, so the zip cannot hide a missing choice. -/
def entries (label : O → T) (order : List O) (plan : List (Option (List T))) :
    List (Entry O T) :=
  (order.zip plan).filterMap fun (o, result) => result.map fun out => ⟨o, label o, out⟩

private theorem entries_spec (label : O → T) (answers : O → T → List (List T))
    {order : List O} {plan : List (Option (List T))}
    (completeChoice : List.Forall₂ (fun o p => Permitted (answers o (label o)) p) order plan) :
    ((entries label order plan).map Entry.occurrence).Sublist order ∧
      (∀ e ∈ entries label order plan,
        label e.occurrence = e.input ∧ e.outputs ∈ answers e.occurrence e.input) ∧
      (∀ o ∈ order, (∃ out, out ∈ answers o (label o)) →
        o ∈ (entries label order plan).map Entry.occurrence) := by
  induction completeChoice with
  | nil => simp [entries]
  | @cons o result order plan permitted _ ih =>
    obtain ⟨ordered, sound, covered⟩ := ih
    cases result with
    | none =>
      have miss : answers o (label o) = [] := permitted
      have omitHead : entries label (o :: order) (none :: plan) = entries label order plan := rfl
      rw [omitHead]
      refine ⟨ordered.cons o, sound, ?_⟩
      intro i here existsOut
      rcases List.mem_cons.mp here with rfl | later
      · rcases existsOut with ⟨out, mem⟩
        simp [miss] at mem
      · exact covered i later existsOut
    | some out =>
      have head : entries label (o :: order) (some out :: plan) =
          ⟨o, label o, out⟩ :: entries label order plan := rfl
      rw [head]
      refine ⟨ordered.cons_cons o, ?_, ?_⟩
      · intro e member
        rcases List.mem_cons.mp member with rfl | latter
        · exact ⟨rfl, permitted⟩
        · exact sound e latter
      · intro i here existsOut
        rcases List.mem_cons.mp here with rfl | later
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (covered i later existsOut)

theorem entries_length (label : O → T) {order : List O} {plan : List (Option (List T))}
    (aligned : order.length = plan.length) :
    (entries label order plan).length = (plan.filterMap id).length := by
  induction order generalizing plan with
  | nil =>
    have empty : plan = [] := List.length_eq_zero_iff.mp aligned.symm
    simp [empty, entries]
  | cons o rest ih =>
    cases plan with
    | nil => simp at aligned
    | cons p later =>
      have lengths : rest.length = later.length := Nat.succ_inj.mp aligned
      cases p with
      | none => exact ih lengths
      | some v =>
        change (entries label rest later).length + 1 = (later.filterMap id).length + 1
        rw [ih lengths]

theorem rewrite_count (label : O → T) (answers : O → T → List (List T))
    {order : List O} {plan : List (Option (List T))}
    (valid : List.Forall₂ (fun o p => Permitted (answers o (label o)) p) order plan) :
    (entries label order plan).length =
      (order.filter fun o => !(answers o (label o)).isEmpty).length :=
  (entries_length label valid.length_eq).trans (selected_count _ valid)

section Transform

variable [DecidableEq O]

theorem captured_exact (s : State (Terms T) O) (answers : O → T → List (List T))
    (order : List O) (distinct : order.Nodup) (covered : order.toFinset = s.present)
    {plan : List (Option (List T))}
    (valid : List.Forall₂ (fun o p => Permitted (answers o (s.label o)) p) order plan)
    (made : List O) :
    (⟨entries s.label order plan, made⟩ : Group O T).Exact s (fun o row out => out ∈ answers o row) := by
  obtain ⟨inOrder, sound, complete⟩ := entries_spec s.label answers valid
  refine ⟨inOrder.nodup distinct, ?_, ?_⟩
  · intro e member
    exact ⟨covered ▸ List.mem_toFinset.mpr (inOrder.subset (List.mem_map_of_mem member)), sound e member⟩
  · intro o member someAnswer
    exact complete o (List.mem_toFinset.mp (covered.symm ▸ member)) someAnswer

/-- The admission is the established scoped Transform step. Each
admissible choice of one block per occurrence gives that step, not a
separate engine. A base firing and its fresh, compatible allocation are
still required. The captured relation here does not depend on the
private model used to open the base firing. -/
theorem captured_admits (A : SubstitutionAction T S) {P : Program (Terms T)}
    {s : State (Terms T) O} (answers : O → T → List (List T))
    (order : List O) (distinct : order.Nodup) (covered : order.toFinset = s.present)
    {plan : List (Option (List T))}
    (valid : List.Forall₂ (fun o p => Permitted (answers o (s.label o)) p) order plan)
    (base : Firing O (ext A) P s.frame) (baseAdmits : base.Admits (frames A) s)
    (made : List O)
    (ground : (⟨entries s.label order plan, made⟩ : Group O T).Ground A)
    (fits : (⟨entries s.label order plan, made⟩ : Group O T).Fits .take s base.selection) :
    (scopedStep A P .take (fun _ _ _ o row out => out ∈ answers o row)).Admits
      ((⟨entries s.label order plan, made⟩ : Group O T).elaborate A .take base) :=
  (scopedStep_admits_iff ..).mpr ⟨base, _, rfl, ground, baseAdmits, fits,
    fun _ _ => captured_exact s answers order distinct covered valid made⟩

theorem prepared_exact [DecidableEq T] (s : State (Terms T) O)
    (answers : O → T → List (List T)) (order : List O)
    (distinct : order.Nodup) (covered : order.toFinset = s.present)
    {plan : List (Option (List T))}
    (preparation : prepare (fun o => answers o (s.label o)) order = some plan) (made : List O) :
    (⟨entries s.label order plan, made⟩ : Group O T).Exact s (fun o row out => out ∈ answers o row) :=
  captured_exact s answers order distinct covered
    (List.Forall₂.imp (fun _ _ => exact_permitted) ((prepare_iff ..).mp preparation)) made

omit [DecidableEq O] in
/-- Revalidating a *chosen* exact group after an equation edit is weaker
than reusing a deterministic consensus result. The chosen outputs must
remain admissible, and there must be no newly eligible occurrence. Other
replacement choices for an already included occurrence may change. This
fixes the raw world; changes to row identities or labels are separate. -/
theorem refresh_group_iff (s : State (Terms T) O)
    (before after : O → T → List T → Prop) (group : Group O T)
    (original : group.Exact s before) :
    group.Exact s after ↔
      (∀ e ∈ group.entries, after e.occurrence e.input e.outputs) ∧
      ∀ o ∈ s.present, (∃ out, after o (s.label o) out) → ∃ out, before o (s.label o) out := by
  constructor
  · intro complete
    refine ⟨fun e mem => (complete.sound e mem).2.2, ?_⟩
    intro o present found
    obtain ⟨e, mem, rfl⟩ := List.mem_map.mp (complete.complete o present found)
    obtain ⟨_, raw, admits⟩ := original.sound e mem
    exact ⟨e.outputs, by rwa [raw]⟩
  · rintro ⟨kept, noNew⟩
    refine ⟨original.distinct, ?_, fun o present h => original.complete o present (noNew o present h)⟩
    intro e mem
    exact ⟨(original.sound e mem).1, (original.sound e mem).2.1, kept e mem⟩

omit [DecidableEq O] in
/-- When every fibre is single-valued at the declared observation, two
exact groups agree as a bag of (occurrence, output observation) pairs.
They may allocate different fresh names. For an ordered observer, both
groups must additionally be traversed in the same entry order. -/
theorem exact_groups_observed_perm {V : Type*} (s : State (Terms T) O)
    (accepts : O → T → List T → Prop) (observe : O → List T → V)
    (single : ∀ o ∈ s.present, ∀ x y, accepts o (s.label o) x → accepts o (s.label o) y →
      observe o x = observe o y)
    {first second : Group O T} (left : first.Exact s accepts) (right : second.Exact s accepts) :
    (first.entries.map (fun e => (e.occurrence, observe e.occurrence e.outputs))).Perm
      (second.entries.map (fun e => (e.occurrence, observe e.occurrence e.outputs))) := by
  let readEntry := fun e : Entry O T => (e.occurrence, observe e.occurrence e.outputs)
  have distinct (g : Group O T) (e : g.Exact s accepts) : (g.entries.map readEntry).Nodup :=
    List.Nodup.of_map Prod.fst (by simpa only [List.map_map, readEntry, Function.comp_def] using e.distinct)
  have includes (a b : Group O T) (ea : a.Exact s accepts) (eb : b.Exact s accepts) :
      a.entries.map readEntry ⊆ b.entries.map readEntry := by
    intro result member
    obtain ⟨e, here, rfl⟩ := List.mem_map.mp member
    obtain ⟨there, labelHere, matchHere⟩ := ea.sound e here
    have leftMatch : accepts e.occurrence (s.label e.occurrence) e.outputs := by
      rwa [labelHere]
    obtain ⟨other, their, same⟩ :=
      List.mem_map.mp (eb.complete e.occurrence there ⟨e.outputs, leftMatch⟩)
    obtain ⟨_, labelThere, matchThere⟩ := eb.sound other their
    have rightMatch : accepts e.occurrence (s.label e.occurrence) other.outputs := by
      rw [← same, labelThere]
      exact matchThere
    refine List.mem_map.mpr ⟨other, their, ?_⟩
    exact Prod.ext same (by
      simpa only [readEntry, same] using (single _ there _ _ leftMatch rightMatch).symm)
  exact (List.perm_ext_iff_of_nodup (distinct _ left) (distinct _ right)).mpr
    (fun _ => ⟨fun h => includes _ _ left right h, fun h => includes _ _ right left h⟩)

end Transform

end Mettapedia.Languages.MeTTa.StoreAndDemand.EquationalMatchRewrite
