import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEventsOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsAbsence

/-!
# Controls for the events of the unfolding

* **Restored absence, two configurations** (`restored_absence_two_configurations`): the runs
  `reader, maker, taker` and `maker, taker, reader` fire one set of firings, and their
  configurations differ. The reader's event differs too: in the first it has no cause, in the
  second the maker and the taker are its causes. In the order (`reader_prefix_of_one_trace`), the
  reader alone is an initial part of the first configuration and not of the second, so its
  history is a prefix of one trace only.
* **Competing takes conflict** (`competing_takes_conflict`): two firings take one occurrence;
  each alone is a configuration, and no configuration contains both.
* **Read before take is asymmetric** (`read_before_take_asymmetric`): a reader and a taker of one
  occurrence run in one order only, both together form a configuration, and the taker has two
  events: with the reader as its cause, and alone without one.
* **A jointly inconsistent triple** (`inconsistent_triple_no_configuration`): three tells are
  pairwise configurations, and no configuration contains all three.
* **Guards fall outside the fragment** (`guard_or_causality`): an equation guard admitted after
  either of two tells. Two runs of one trace have different tells before the guarded firing, so
  its causes are disjunctive and no cause set is a property of the trace.
* **Positive control** (`round_one_configuration`): the two orders of a round have one
  configuration and one set of events.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents.Controls

open AnnotatedRuns
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRunUnfolding (Flow ReadBeforeTake)

/-- A path of the causal order starts at a member. -/
theorem TransGen.source_mem {T S O : Type*} {X : Config T S O} {a b : Firing T S O}
    (path : Relation.TransGen (Edge X) a b) : a ∈ X.firings := by
  induction path with
  | single edge => exact edge.1
  | tail _ _ ih => exact ih

/-- A firing with no edge into it has no causes. -/
theorem not_mem_causes_of_no_edge {T S O : Type*} {X : Config T S O} {a f : Firing T S O}
    (noEdge : ∀ g, ¬ Edge X g f) : a ∉ causes X f := by
  intro path
  change Relation.TransGen (Edge X) a f at path
  cases path with
  | single edge => exact noEdge a edge
  | tail _ edge => exact noEdge _ edge

/-! ## Restored absence: one set of firings, two configurations -/

namespace RestoredAbsence

open AnnotatedRuns.AbsenceControls (reader maker taker empty noPersistent query_first_runs
  query_last_runs)

local notation "label" => AnnotatedRuns.AbsenceControls.label

theorem reader_static : reader.Static :=
  ⟨rfl, by
    intro query member σ τ
    obtain rfl := List.mem_singleton.mp member
    rfl⟩

theorem maker_static : maker.Static := ⟨rfl, by simp [Firing.StaticQueries, maker]⟩

theorem taker_static : taker.Static := ⟨rfl, by simp [Firing.StaticQueries, taker]⟩

theorem reader_ne_maker : reader ≠ maker := fun same => by
  have made := congrArg (fun f : AnnotatedRuns.Controls.Run => f.selection.made) same
  simp [reader, maker] at made

theorem reader_ne_taker : reader ≠ taker := fun same => by
  have made := congrArg (fun f : AnnotatedRuns.Controls.Run => f.selection.made) same
  simp [reader, taker] at made

theorem maker_ne_taker : maker ≠ taker := fun same => by
  have made := congrArg (fun f : AnnotatedRuns.Controls.Run => f.selection.made) same
  simp [maker, taker] at made

/-- The three firings make `60`, `61` and `62`. -/
theorem made_cases (f : AnnotatedRuns.Controls.Run) (member : f ∈ [reader, maker, taker]) :
    (f = reader ∧ f.selection.made = [60]) ∨ (f = maker ∧ f.selection.made = [61]) ∨
      (f = taker ∧ f.selection.made = [62]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem fragment_of_perm (w : List AnnotatedRuns.Controls.Run) (perm : w.Perm [reader, maker, taker]) :
    Fragment empty w := by
  refine Fragment.perm ⟨?_, ?_, ?_, ?_⟩ perm.symm
  · intro f member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact reader_static
    · exact maker_static
    · exact taker_static
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨reader_ne_maker, reader_ne_taker⟩, maker_ne_taker, not_false, List.nodup_nil⟩
  · intro f _ o _ present
    simp [empty] at present
  · intro f hf g hg ne o inF inG
    rcases made_cases f hf with ⟨rfl, mf⟩ | ⟨rfl, mf⟩ | ⟨rfl, mf⟩ <;>
    rcases made_cases g hg with ⟨rfl, mg⟩ | ⟨rfl, mg⟩ | ⟨rfl, mg⟩ <;>
    first
      | exact ne rfl
      | (rw [mf] at inF; rw [mg] at inG; simp at inF inG; omega)

theorem fragment_first : Fragment empty [reader, maker, taker] :=
  fragment_of_perm _ (List.Perm.refl _)

theorem fragment_last : Fragment empty [maker, taker, reader] :=
  fragment_of_perm _ (List.perm_append_comm (l₁ := [maker, taker]) (l₂ := [reader]))

theorem maker_inhibits_reader : Inhibits label maker reader :=
  ⟨Subst.id signature, PredicateQueryAdmission.Query.fixed noPersistent, List.mem_singleton_self _, 61,
    Or.inr (List.mem_singleton_self _), rfl⟩

theorem taker_inhibits_reader : Inhibits label taker reader :=
  ⟨Subst.id signature, PredicateQueryAdmission.Query.fixed noPersistent, List.mem_singleton_self _, 61,
    Or.inl (List.mem_singleton_self _), rfl⟩

/-- No edge enters the reader when it comes first. -/
theorem no_edge_into_reader_first (g : AnnotatedRuns.Controls.Run) :
    ¬ Edge (configOf label [reader, maker, taker]) g reader := by
  rintro ⟨_, _, ⟨o, _, used⟩ | ⟨o, _, taken⟩ | before⟩
  · rcases used with taken | read
    · simp [reader] at taken
    · simp [reader] at read
  · simp [reader] at taken
  · exact not_precedes_head fragment_first.nodup before.1

/-- **Restored absence: one set of firings, two configurations, two events of the reader.** -/
theorem restored_absence_two_configurations :
    IsConfiguration A label empty (configOf label [reader, maker, taker]) ∧
      IsConfiguration A label empty (configOf label [maker, taker, reader]) ∧
      (configOf label [reader, maker, taker]).firings = (configOf label [maker, taker, reader]).firings ∧
      configOf label [reader, maker, taker] ≠ configOf label [maker, taker, reader] ∧
      maker ∉ causes (configOf label [reader, maker, taker]) reader ∧
      maker ∈ causes (configOf label [maker, taker, reader]) reader ∧
      taker ∈ causes (configOf label [maker, taker, reader]) reader ∧
      ¬ RoundEquiv A label empty [reader, maker, taker] [maker, taker, reader] := by
  refine ⟨configOf_isConfiguration A label query_first_runs fragment_first,
    configOf_isConfiguration A label query_last_runs fragment_last, ?_, ?_,
    not_mem_causes_of_no_edge no_edge_into_reader_first, ?_, ?_, ?_⟩
  · ext f
    rw [mem_configOf_firings, mem_configOf_firings]
    exact (List.perm_append_comm (l₁ := [reader]) (l₂ := [maker, taker])).mem_iff
  · intro same
    have orders := congrFun (congrFun (congrArg Config.before same) reader) maker
    rw [configOf_before, configOf_before] at orders
    have first : beforeOf label [reader, maker, taker] reader maker :=
      ⟨precedes_cons.mpr (Or.inl ⟨rfl, List.mem_cons_self⟩), Or.inr maker_inhibits_reader⟩
    rw [orders] at first
    exact precedes_asymm fragment_last.nodup
      (precedes_cons.mpr (Or.inl ⟨rfl, by simp⟩)) first.1
  · exact Relation.TransGen.single ⟨by simp [mem_configOf_firings], by simp [mem_configOf_firings],
      Or.inr (Or.inr ⟨precedes_cons.mpr (Or.inl ⟨rfl, by simp⟩), Or.inl maker_inhibits_reader⟩)⟩
  · exact Relation.TransGen.single ⟨by simp [mem_configOf_firings], by simp [mem_configOf_firings],
      Or.inr (Or.inr ⟨precedes_cons.mpr (Or.inr (precedes_cons.mpr (Or.inl ⟨rfl, by simp⟩))),
        Or.inl taker_inhibits_reader⟩)⟩
  · intro equivalent
    exact AnnotatedRuns.AbsenceControls.restored_absence_two_traces.2.2.2.2.1 equivalent

theorem reader_alone_runs : Executable A label empty [reader] :=
  ⟨AnnotatedRuns.AbsenceControls.reader_valid_empty,
    AnnotatedRuns.AbsenceControls.reader_valid_empty.firing.consistent⟩

theorem fragment_reader : Fragment empty [reader] :=
  ⟨by simpa using reader_static, List.nodup_singleton _, by intro f _ o _ present; simp [empty] at present,
    by intro g hg h hh ne; simp only [List.mem_singleton] at hg hh; exact absurd (hg.trans hh.symm) ne⟩

/-- **Restored absence, in the order.** The history of the reader alone is an initial part of the
first configuration and not of the second, although the second fires the same reader: there the
reader has causes. So the reader-first history is a prefix of one trace and not of the other. -/
theorem reader_prefix_of_one_trace :
    Extends (configOf label [reader]) (configOf label [reader, maker, taker]) ∧
      ¬ Extends (configOf label [reader]) (configOf label [maker, taker, reader]) ∧
      (∃ v, Executable A label empty ([reader] ++ v) ∧ Fragment empty ([reader] ++ v) ∧
        RoundEquiv A label empty ([reader] ++ v) [reader, maker, taker]) ∧
      ¬ ∃ v, Executable A label empty ([reader] ++ v) ∧ Fragment empty ([reader] ++ v) ∧
        RoundEquiv A label empty ([reader] ++ v) [maker, taker, reader] := by
  have first : Extends (configOf label [reader]) (configOf label [reader, maker, taker]) :=
    prefix_extends A label (u := [reader]) (v := [maker, taker]) query_first_runs fragment_first
  have second : ¬ Extends (configOf label [reader]) (configOf label [maker, taker, reader]) := by
    intro initial
    have edge : Edge (configOf label [maker, taker, reader]) maker reader :=
      ⟨by simp [mem_configOf_firings], by simp [mem_configOf_firings],
        Or.inr (Or.inr ⟨precedes_cons.mpr (Or.inl ⟨rfl, by simp⟩), Or.inl maker_inhibits_reader⟩)⟩
    have makerIn := initial.down reader (mem_configOf_firings.mpr (List.mem_singleton_self _)) maker
      edge
    rw [mem_configOf_firings, List.mem_singleton] at makerIn
    exact reader_ne_maker makerIn.symm
  refine ⟨first, second,
    (prefix_iff_extends A label reader_alone_runs fragment_reader query_first_runs fragment_first).mpr
      first, fun prefix_ => second ?_⟩
  exact (prefix_iff_extends A label reader_alone_runs fragment_reader query_last_runs
    fragment_last).mp prefix_

end RestoredAbsence

/-! ## Competing takes of one occurrence conflict -/

namespace Conflict

open AnnotatedRuns.Controls (label Run zeros taker start taker_valid)

/-- A second taker of occurrence `0`, making `4`. -/
def rival : Run :=
  ⟨⟨[ConstraintMultisetRewriting.Controls.f (.const 0)], [], [], [], [.const 2]⟩, [],
    ⟨[0], [], [4]⟩⟩

theorem rival_valid : rival.Valid A label start := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [rival]⟩,
    by simp [rival]⟩
  intro equation member
  have same : equation = (ConstraintMultisetRewriting.Controls.f (.const 0), label 0) := by
    simpa [Selection.problem, Selection.equations, start, rival] using member
  subst same
  rfl

theorem taker_ne_rival : taker ≠ rival := fun same => by
  have made := congrArg (fun f : Run => f.selection.made) same
  simp [taker, rival] at made

theorem single_fragment (f : Run) (static : f.Static) (fresh : ∀ o ∈ f.selection.made, o ∉ start.present) :
    Fragment start [f] :=
  ⟨by simpa using static, List.nodup_singleton f, by simpa using fresh,
    by intro g hg h hh ne; simp only [List.mem_singleton] at hg hh; exact absurd (hg.trans hh.symm) ne⟩

/-- **Competing takes conflict.** Each taker alone is a configuration; no configuration contains
both. -/
theorem competing_takes_conflict :
    TakeConflict taker rival ∧
      IsConfiguration A label start (configOf label [taker]) ∧
      IsConfiguration A label start (configOf label [rival]) ∧
      ∀ X : Config _ _ _, taker ∈ X.firings → rival ∈ X.firings → ¬ IsConfiguration A label start X := by
  refine ⟨⟨0, List.mem_singleton_self _, List.mem_singleton_self _⟩,
    configOf_isConfiguration A label ⟨taker_valid, taker_valid.firing.consistent⟩
      (single_fragment taker ⟨rfl, by simp [Firing.StaticQueries, taker]⟩ (by decide)),
    configOf_isConfiguration A label ⟨rival_valid, rival_valid.firing.consistent⟩
      (single_fragment rival ⟨rfl, by simp [Firing.StaticQueries, rival]⟩ (by decide)), ?_⟩
  intro X hTaker hRival config
  exact config.takes taker hTaker rival hRival taker_ne_rival 0 (List.mem_singleton_self _)
    (List.mem_singleton_self _)

end Conflict

/-! ## Read before take is asymmetric -/

namespace Asymmetry

open AnnotatedRuns.Controls (label Run zeros reader start)

/-- Takes `1 : X` with the pattern `Z`, and makes nothing. -/
def takesOne : Run := ⟨⟨[.var 2], [], [], [], []⟩, [], ⟨[1], [], []⟩⟩

theorem takesOne_valid_at_start : takesOne.Valid A label start := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [takesOne]⟩,
    by simp [takesOne]⟩
  intro equation member
  have same : equation = (.var 2, label 1) := by
    simpa [Selection.problem, Selection.equations, start, takesOne] using member
  subst same
  rfl

theorem takesOne_valid_after_reader : takesOne.Valid A label (reader.result label start) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨zeros, ?_⟩, by simp [takesOne]⟩,
    by simp [takesOne]⟩
  intro equation member
  have cases : equation = (.var 1, label 1) ∨ equation = (.var 2, label 1) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, start, reader,
      takesOne] using member
  rcases cases with rfl | rfl <;> rfl

theorem reader_then_takesOne : Executable A label start [reader, takesOne] :=
  ⟨RoundControls.reader_valid_at_start, takesOne_valid_after_reader,
    takesOne_valid_after_reader.firing.consistent⟩

theorem reader_not_after_takesOne : ¬ reader.Valid A label (takesOne.result label start) := by
  intro valid
  have present := read_present A label valid (o := 1) (by simp [reader])
  revert present
  decide

theorem reader_ne_takesOne : reader ≠ takesOne := fun same => by
  have taken := congrArg (fun f : Run => f.selection.taken) same
  simp [reader, takesOne] at taken

theorem fragment_pair : Fragment start [reader, takesOne] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨rfl, by simp [Firing.StaticQueries, reader]⟩
    · exact ⟨rfl, by simp [Firing.StaticQueries, takesOne]⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨reader_ne_takesOne, not_false, List.nodup_nil⟩
  · intro f member o made
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [reader, List.mem_singleton] at made
      subst made
      decide
    · simp [takesOne] at made
  · intro f hf g hg ne o inF inG
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf hg
    rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
    · exact ne rfl
    · simp [takesOne] at inG
    · simp [takesOne] at inF
    · exact ne rfl

theorem fragment_takesOne : Fragment start [takesOne] :=
  ⟨by simpa using (⟨rfl, by simp [Firing.StaticQueries, takesOne]⟩ : takesOne.Static),
    List.nodup_singleton _, by simp [takesOne],
    by intro g hg h hh ne; simp only [List.mem_singleton] at hg hh; exact absurd (hg.trans hh.symm) ne⟩

/-- **Read before take is asymmetric.** The reader and the taker of occurrence `1` run in one
order only; together they are a configuration in which the reader is a cause of the take, and the
take alone is a configuration in which it has no cause. -/
theorem read_before_take_asymmetric :
    ReadBeforeTake reader takesOne ∧ ¬ ReadBeforeTake takesOne reader ∧
      Executable A label start [reader, takesOne] ∧ ¬ Executable A label start [takesOne, reader] ∧
      IsConfiguration A label start (configOf label [reader, takesOne]) ∧
      IsConfiguration A label start (configOf label [takesOne]) ∧
      reader ∈ causes (configOf label [reader, takesOne]) takesOne ∧
      reader ∉ causes (configOf label [takesOne]) takesOne := by
  refine ⟨⟨1, by simp [reader], by simp [takesOne]⟩, ?_, reader_then_takesOne,
    fun run => reader_not_after_takesOne run.2.1,
    configOf_isConfiguration A label reader_then_takesOne fragment_pair,
    configOf_isConfiguration A label ⟨takesOne_valid_at_start, takesOne_valid_at_start.firing.consistent⟩
      fragment_takesOne, ?_, ?_⟩
  · rintro ⟨o, read, _⟩
    simp [takesOne] at read
  · exact Relation.TransGen.single ⟨by simp [mem_configOf_firings], by simp [mem_configOf_firings],
      Or.inr (Or.inl ⟨1, by simp [reader], by simp [takesOne]⟩)⟩
  · intro path
    have member := TransGen.source_mem path
    rw [mem_configOf_firings, List.mem_singleton] at member
    exact reader_ne_takesOne member

end Asymmetry

/-! ## A jointly inconsistent triple is never one configuration -/

namespace Joint

open AnnotatedRuns.Controls (label Run)
open AnnotatedRuns.RoundControls (tellSame tellOne tellTwo empty tells_jointly_inconsistent)

theorem tell_static (f : Run) (checks : f.rule.checks = []) (queries : f.queries = []) : f.Static :=
  ⟨checks, by intro query member; rw [queries] at member; cases member⟩

theorem pair_fragment (a b : Run) (sa : a.Static) (sb : b.Static) (ne : a ≠ b)
    (ma : a.selection.made = []) (mb : b.selection.made = []) : Fragment empty [a, b] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact sa
    · exact sb
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false]
    exact ⟨ne, not_false, List.nodup_nil⟩
  · intro f _ o _ present
    simp [empty] at present
  · intro f hf g _ _ o inF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · rw [ma] at inF
      cases inF
    · rw [mb] at inF
      cases inF

theorem same_ne_one : tellSame ≠ tellOne := fun same => by
  have tells := congrArg (fun f : Run => f.rule.tell) same
  simp [tellSame, tellOne] at tells

theorem same_ne_two : tellSame ≠ tellTwo := fun same => by
  have tells := congrArg (fun f : Run => f.rule.tell) same
  simp [tellSame, tellTwo] at tells

theorem one_ne_two : tellOne ≠ tellTwo := fun same => by
  have tells := congrArg (fun f : Run => f.rule.tell) same
  simp [tellOne, tellTwo] at tells

theorem same_then_one : Executable A label empty [tellSame, tellOne] := by
  have solved : ∀ e ∈ (tellOne.result label (tellSame.result label empty)).equations,
      A.Solves (fun _ => .const 1) e := by
    intro e member
    simp only [Firing.result, Selection.result, Selection.problem, Selection.equations, empty,
      tellSame, tellOne, List.zipWith_nil_left, List.nil_append, List.append_nil, List.mem_append,
      List.mem_singleton] at member
    rcases member with rfl | rfl <;> rfl
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨fun _ => .const 1, ?_⟩, by simp [tellSame]⟩,
    by simp [tellSame]⟩,
    ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨fun _ => .const 1, solved⟩, by simp [tellOne]⟩,
      by simp [tellOne]⟩, ⟨fun _ => .const 1, solved⟩⟩
  intro e member
  exact solved e (by
    simp only [Firing.result, Selection.result, Selection.problem, Selection.equations, empty,
      tellSame, tellOne, List.zipWith_nil_left, List.nil_append, List.append_nil, List.mem_append,
      List.mem_singleton] at member ⊢
    exact Or.inl member)

theorem same_then_two : Executable A label empty [tellSame, tellTwo] := by
  have solved : ∀ e ∈ (tellTwo.result label (tellSame.result label empty)).equations,
      A.Solves (fun _ => .const 2) e := by
    intro e member
    simp only [Firing.result, Selection.result, Selection.problem, Selection.equations, empty,
      tellSame, tellTwo, List.zipWith_nil_left, List.nil_append, List.append_nil, List.mem_append,
      List.mem_singleton] at member
    rcases member with rfl | rfl <;> rfl
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨fun _ => .const 2, ?_⟩, by simp [tellSame]⟩,
    by simp [tellSame]⟩,
    ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨fun _ => .const 2, solved⟩, by simp [tellTwo]⟩,
      by simp [tellTwo]⟩, ⟨fun _ => .const 2, solved⟩⟩
  intro e member
  exact solved e (by
    simp only [Firing.result, Selection.result, Selection.problem, Selection.equations, empty,
      tellSame, tellTwo, List.zipWith_nil_left, List.nil_append, List.append_nil, List.mem_append,
      List.mem_singleton] at member ⊢
    exact Or.inl member)

/-- `X = 1` and `Y = 2`. -/
def split : Subst signature := fun n => if n = 0 then .const 1 else .const 2

theorem one_then_two : Executable A label empty [tellOne, tellTwo] := by
  have solved : ∀ e ∈ (tellTwo.result label (tellOne.result label empty)).equations,
      A.Solves split e := by
    intro e member
    simp only [Firing.result, Selection.result, Selection.problem, Selection.equations, empty,
      tellOne, tellTwo, List.zipWith_nil_left, List.nil_append, List.append_nil, List.mem_append,
      List.mem_singleton] at member
    rcases member with rfl | rfl <;> rfl
  refine ⟨⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨split, ?_⟩, by simp [tellOne]⟩,
    by simp [tellOne]⟩,
    ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨split, solved⟩, by simp [tellTwo]⟩,
      by simp [tellTwo]⟩, ⟨split, solved⟩⟩
  intro e member
  exact solved e (by
    simp only [Firing.result, Selection.result, Selection.problem, Selection.equations, empty,
      tellOne, tellTwo, List.zipWith_nil_left, List.nil_append, List.append_nil, List.mem_append,
      List.mem_singleton] at member ⊢
    exact Or.inl member)

/-- **Every pair of the three tells is a configuration; no configuration holds all three.** -/
theorem inconsistent_triple_no_configuration :
    IsConfiguration A label empty (configOf label [tellSame, tellOne]) ∧
      IsConfiguration A label empty (configOf label [tellSame, tellTwo]) ∧
      IsConfiguration A label empty (configOf label [tellOne, tellTwo]) ∧
      ∀ X : Config _ _ _, tellSame ∈ X.firings → tellOne ∈ X.firings → tellTwo ∈ X.firings →
        ¬ IsConfiguration A label empty X := by
  have sSame := tell_static tellSame rfl rfl
  have sOne := tell_static tellOne rfl rfl
  have sTwo := tell_static tellTwo rfl rfl
  refine ⟨configOf_isConfiguration A label same_then_one
      (pair_fragment _ _ sSame sOne same_ne_one rfl rfl),
    configOf_isConfiguration A label same_then_two (pair_fragment _ _ sSame sTwo same_ne_two rfl rfl),
    configOf_isConfiguration A label one_then_two (pair_fragment _ _ sOne sTwo one_ne_two rfl rfl), ?_⟩
  intro X hSame hOne hTwo config
  obtain ⟨σ, base, all⟩ := config.joint
  refine tells_jointly_inconsistent ⟨σ, ?_⟩
  rw [jointProblem, A.models_append]
  refine ⟨base, fun e member => ?_⟩
  obtain ⟨f, inList, inAdded⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inList
  rcases inList with rfl | rfl | rfl
  · exact all _ hSame e inAdded
  · exact all _ hOne e inAdded
  · exact all _ hTwo e inAdded

end Joint

/-! ## Guards fall outside the fragment: or-causality -/

namespace Guards

open AnnotatedRuns.Controls (label Run teller asker empty ones teller_valid asker_valid_after
  asker_refused_first)

/-- Tells `1 = X`: the same equation as the teller, written the other way round. -/
def mirror : Run := ⟨⟨[], [], [(.const 1, .var 0)], [], []⟩, [], ⟨[], [], []⟩⟩

theorem mirror_valid : mirror.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, by simp [mirror]⟩,
    by simp [mirror]⟩
  intro equation member
  have same : equation = (.const 1, .var 0) := by
    simpa [Selection.problem, Selection.equations, empty, mirror] using member
  subst same
  rfl

theorem mirror_valid_after_teller : mirror.Valid A label (teller.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, by simp [mirror]⟩,
    by simp [mirror]⟩
  intro equation member
  have cases : equation = (.var 0, .const 1) ∨ equation = (.const 1, .var 0) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, teller,
      mirror] using member
  rcases cases with rfl | rfl <;> rfl

theorem teller_valid_after_mirror : teller.Valid A label (mirror.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, by simp [teller]⟩,
    by simp [teller]⟩
  intro equation member
  have cases : equation = (.const 1, .var 0) ∨ equation = (.var 0, .const 1) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, teller,
      mirror] using member
  rcases cases with rfl | rfl <;> rfl

theorem asker_valid_after_mirror : asker.Valid A label (mirror.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, ?_⟩, by simp [asker]⟩
  · intro equation member
    have same : equation = (.const 1, .var 0) := by
      simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, mirror,
        asker] using member
    subst same
    rfl
  · intro check member σ solved
    have only : check = .equal (.var 0) (.const 1) := by simpa [asker] using member
    subst only
    have told := solved (.const 1, .var 0) (by
      simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, mirror,
        asker])
    exact A.equivalence.symm told

theorem independent_footprints (f g : Run) (fEmpty : f.selection = ⟨[], [], []⟩)
    (gEmpty : g.selection = ⟨[], [], []⟩) :
    MeTTaCalculus.OccurrenceCommits.Independent label (f.selection.commit (T := Term signature))
      (g.selection.commit (T := Term signature)) := by
  rw [fEmpty, gEmpty]
  unfold MeTTaCalculus.OccurrenceCommits.Independent MeTTaCalculus.OccurrenceCommits.Clash
    MeTTaCalculus.OccurrenceCommits.Spoils MeTTaCalculus.OccurrenceCommits.WritesInto
  decide

theorem tells_round : Round A label empty [teller, mirror] := by
  refine ⟨?_, ⟨ones, ?_⟩, List.pairwise_pair.mpr ⟨independent_footprints _ _ rfl rfl, by simp [teller],
    by simp [mirror], by simp [teller], by simp [mirror]⟩⟩
  · intro f member
    rcases List.mem_pair.mp member with rfl | rfl
    · exact teller_valid
    · exact mirror_valid
  · intro equation member
    have cases : equation = (.var 0, .const 1) ∨ equation = (.const 1, .var 0) := by
      simpa [jointProblem, Firing.added, GuardFreeProcessOrders.added, Selection.equations, empty,
        teller, mirror] using member
    rcases cases with rfl | rfl <;> rfl

theorem asker_mirror_round : Round A label (teller.result label empty) [asker, mirror] := by
  refine ⟨?_, ⟨ones, ?_⟩, List.pairwise_pair.mpr ⟨independent_footprints _ _ rfl rfl, ?_,
    by simp [mirror], by simp [asker], by simp [mirror]⟩⟩
  · intro f member
    rcases List.mem_pair.mp member with rfl | rfl
    · exact asker_valid_after
    · exact mirror_valid_after_teller
  · intro equation member
    have cases : equation = (.var 0, .const 1) ∨ equation = (.const 1, .var 0) := by
      simpa [jointProblem, Firing.added, GuardFreeProcessOrders.added, Selection.equations,
        Selection.result, Selection.problem, Firing.result, empty, teller, mirror, asker] using member
    rcases cases with rfl | rfl <;> rfl
  · intro check member
    have only : check = .equal (.var 0) (.const 1) := by simpa [asker] using member
    subst only
    trivial

theorem asker_teller_round : Round A label (mirror.result label empty) [asker, teller] := by
  refine ⟨?_, ⟨ones, ?_⟩, List.pairwise_pair.mpr ⟨independent_footprints _ _ rfl rfl, ?_,
    by simp [teller], by simp [asker], by simp [teller]⟩⟩
  · intro f member
    rcases List.mem_pair.mp member with rfl | rfl
    · exact asker_valid_after_mirror
    · exact teller_valid_after_mirror
  · intro equation member
    have cases : equation = (.const 1, .var 0) ∨ equation = (.var 0, .const 1) := by
      simpa [jointProblem, Firing.added, GuardFreeProcessOrders.added, Selection.equations,
        Selection.result, Selection.problem, Firing.result, empty, teller, mirror, asker] using member
    rcases cases with rfl | rfl <;> rfl
  · intro check member
    have only : check = .equal (.var 0) (.const 1) := by simpa [asker] using member
    subst only
    trivial

theorem distinct : [teller, asker, mirror].Nodup := by
  have ta : teller ≠ asker := fun same => by
    have tells := congrArg (fun f : Run => f.rule.tell) same
    simp [teller, asker] at tells
  have tm : teller ≠ mirror := fun same => by
    have tells := congrArg (fun f : Run => f.rule.tell) same
    simp [teller, mirror] at tells
  have am : asker ≠ mirror := fun same => by
    have tells := congrArg (fun f : Run => f.rule.tell) same
    simp [asker, mirror] at tells
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨⟨ta, tm⟩, am, not_false, List.nodup_nil⟩

/-- **Guards fall outside the fragment: or-causality.** The asker is refused at the start and
admitted after either tell. The runs `teller, asker, mirror` and `mirror, asker, teller` are one
contextual trace, yet the tell before the asker is `teller` in one and `mirror` in the other: no
set of causes of the guarded firing is a property of its trace. -/
theorem guard_or_causality :
    ¬ asker.Valid A label empty ∧
      RoundEquiv A label empty [teller, asker, mirror] [mirror, asker, teller] ∧
      Precedes [teller, asker, mirror] teller asker ∧ ¬ Precedes [teller, asker, mirror] mirror asker ∧
      Precedes [mirror, asker, teller] mirror asker ∧ ¬ Precedes [mirror, asker, teller] teller asker := by
  have first : RoundEquiv A label empty [teller, asker, mirror] [teller, mirror, asker] :=
    .rel _ _ (RoundSwap.swap [teller] [] asker mirror asker_mirror_round)
  have middle : RoundEquiv A label empty [teller, mirror, asker] [mirror, teller, asker] :=
    .rel _ _ (RoundSwap.swap [] [asker] teller mirror tells_round)
  have last : RoundEquiv A label empty [mirror, teller, asker] [mirror, asker, teller] :=
    .rel _ _ (RoundSwap.swap [mirror] [] teller asker
      (asker_teller_round.perm A label (List.Perm.swap teller asker [])))
  have perm : [teller, asker, mirror].Perm [mirror, asker, teller] := by
    have step₁ : [teller, asker, mirror].Perm [teller, mirror, asker] :=
      List.Perm.cons _ (List.Perm.swap mirror asker [])
    have step₂ : [teller, mirror, asker].Perm [mirror, teller, asker] := List.Perm.swap mirror teller _
    have step₃ : [mirror, teller, asker].Perm [mirror, asker, teller] :=
      List.Perm.cons _ (List.Perm.swap asker teller [])
    exact step₁.trans (step₂.trans step₃)
  refine ⟨asker_refused_first, .trans _ _ _ first (.trans _ _ _ middle last),
    precedes_cons.mpr (Or.inl ⟨rfl, List.mem_cons_self⟩), ?_,
    precedes_cons.mpr (Or.inl ⟨rfl, List.mem_cons_self⟩), ?_⟩
  · exact precedes_asymm distinct
      (precedes_cons.mpr (Or.inr (precedes_cons.mpr (Or.inl ⟨rfl, List.mem_singleton_self _⟩))))
  · exact precedes_asymm (perm.nodup_iff.mp distinct)
      (precedes_cons.mpr (Or.inr (precedes_cons.mpr (Or.inl ⟨rfl, List.mem_singleton_self _⟩))))

end Guards

/-! ## Positive control: the orders of a round have one configuration -/

namespace Round

open AnnotatedRuns.Controls (label Run taker reader start taker_then_reader)

theorem static_pair : ∀ f ∈ [reader, taker], f.Static := by
  intro f member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨rfl, by simp [Firing.StaticQueries, reader]⟩
  · exact ⟨rfl, by simp [Firing.StaticQueries, AnnotatedRuns.Controls.taker]⟩

/-- **Positive control.** The two orders of the round of the taker and the reader have one
configuration and one set of events. -/
theorem round_one_configuration :
    configOf label [reader, taker] = configOf label [taker, reader] ∧
      events (configOf label [reader, taker]) = events (configOf label [taker, reader]) := by
  have same := configOf_eq_of_roundEquiv A label RoundControls.round_one_trace static_pair
  exact ⟨same, by rw [same]⟩

end Round

#print axioms TransGen.source_mem
#print axioms not_mem_causes_of_no_edge
#print axioms RestoredAbsence.restored_absence_two_configurations
#print axioms RestoredAbsence.reader_prefix_of_one_trace
#print axioms Conflict.competing_takes_conflict
#print axioms Asymmetry.read_before_take_asymmetric
#print axioms Joint.inconsistent_triple_no_configuration
#print axioms Guards.guard_or_causality
#print axioms Round.round_one_configuration

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunEvents.Controls
