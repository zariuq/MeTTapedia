import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPaths

/-!
# Predicate queries make traces finer than bags: restored absence

Without guards and predicate queries, the firings of a run determine its trace
(`AnnotatedRuns.same_firings_traceEquiv`): runs of the same firings, with fresh and distinct
footprints, are one trace. With a predicate query this fails even for the coarsest trace
equivalence of the run category, the contextual one.

## The control

A predicate query observes that no persistent atom is present and makes an output; a second
firing makes a persistent atom; a third takes it and makes another output. From the empty
configuration both orders `reader, maker, taker` and `maker, taker, reader` run, they have the
same firings, and they reach the same configuration (`restored_absence_two_traces`). They are
nevertheless two contextual traces, hence two static traces and two arrows of the contextual
trace category with one source and one target (`restored_absence_two_arrows`). The maker
falsifies the observed absence and the taker restores it: the query cannot move past the maker,
though the maker and the taker together leave its space as it was. This carries
`OccurrenceCommits.Controls.restored_absence_two_traces` from ground commits to the candidate
step.

## Why: no round among the three

No two of the three firings form a round at any configuration (`no_round_maker_reader`,
`no_round_reader_taker`, `no_round_maker_taker`). Where no pair of a run's firings ever forms a
round, round equivalence on the reorderings of the run is equality (`RoundEquiv.eq_of_no_round`),
the word-level form of `EventConcurrency.TraceEq.eq_of_no_tile`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open Mettapedia.GSLT.Causality.EventConcurrency (Trace)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Invariants

variable (A : SubstitutionAction T S) (label : O → T)

/-- **A word function kept by every round swap among the reorderings of `w₀` is kept by round
equivalence there.** -/
theorem RoundEquiv.invariant_on {X : Type*} (F : List (Firing T S O) → X)
    {C : Configuration T O} {w₀ : List (Firing T S O)}
    (respects : ∀ (u v : List (Firing T S O)) (f g : Firing T S O),
      Round A label (follow label C u) [f, g] → (u ++ f :: g :: v).Perm w₀ →
        F (u ++ f :: g :: v) = F (u ++ g :: f :: v))
    {w w' : List (Firing T S O)} (equivalent : RoundEquiv A label C w w') :
    w.Perm w₀ → F w = F w' := by
  induction equivalent with
  | rel _ _ swapped =>
      cases swapped with
      | swap u v f g isRound => exact respects u v f g isRound
  | refl => exact fun _ => rfl
  | symm _ _ first ih =>
      intro perm
      exact (ih ((RoundEquiv.perm A label first).trans perm)).symm
  | trans _ _ _ first _ ih₁ ih₂ =>
      intro perm
      exact (ih₁ perm).trans (ih₂ ((RoundEquiv.perm A label first).symm.trans perm))

/-- **Where no two firings form a round, round equivalence is equality.** If no pair of firings
of `w₀` forms a round at any configuration unless the two are equal, round equivalence on the
reorderings of `w₀` is equality. -/
theorem RoundEquiv.eq_of_no_round {C : Configuration T O} {w₀ : List (Firing T S O)}
    (noRound : ∀ f ∈ w₀, ∀ g ∈ w₀, ∀ D : Configuration T O, Round A label D [f, g] → f = g)
    {w w' : List (Firing T S O)} (equivalent : RoundEquiv A label C w w') (perm : w.Perm w₀) :
    w = w' := by
  refine RoundEquiv.invariant_on A label id ?_ equivalent perm
  intro u v f g isRound reordered
  have inF : f ∈ w₀ := reordered.subset (List.mem_append_right u List.mem_cons_self)
  have inG : g ∈ w₀ :=
    reordered.subset (List.mem_append_right u (List.mem_cons_of_mem f List.mem_cons_self))
  obtain rfl := noRound f inF g inG _ isRound
  rfl

end Invariants

/-! ## Restored absence -/

namespace AbsenceControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (Run persistent)
open MeTTaCalculus.OccurrenceCommits (regionOf mem_regionOf made_subset_fire)

/-- Occurrence `61` is persistent; every other occurrence is an output. -/
def label : Nat → Term signature
  | 61 => .const 9
  | _ => .const 2

/-- No persistent atom is present. -/
def noPersistent : MeTTaCalculus.OccurrenceCommits.PredicateQuery Nat (Term signature) :=
  ⟨persistent, ∅⟩

/-- Observes that no persistent atom is present, and makes the output `60`. -/
def reader : Run :=
  ⟨⟨[], [], [], [], [.const 2]⟩, [PredicateQueryAdmission.Query.fixed noPersistent], ⟨[], [], [60]⟩⟩

/-- Makes the persistent atom `61`. -/
def maker : Run := ⟨⟨[], [], [], [], [.const 9]⟩, [], ⟨[], [], [61]⟩⟩

/-- Takes the persistent atom `61`, and makes the output `62`. -/
def taker : Run := ⟨⟨[.const 9], [], [], [], [.const 2]⟩, [], ⟨[61], [], [62]⟩⟩

def empty : Configuration (Term signature) Nat := ⟨[], ∅⟩

/-! ### No two of the three form a round -/

/-- The query cannot follow the maker: the maker writes into its space. -/
theorem no_round_maker_reader (D : Configuration (Term signature) Nat) :
    ¬ Round A label D [maker, reader] := by
  intro isRound
  have after : reader.Valid A label (maker.result label D) :=
    ((isRound.cons A label).2).valid reader List.mem_cons_self
  obtain ⟨σ, solved⟩ := after.firing.consistent
  have holds : regionOf label (maker.result label D).present persistent = ∅ :=
    after.observations _ List.mem_cons_self σ solved
  have made : 61 ∈ (maker.result label D).present :=
    made_subset_fire (by simp [Selection.commit, maker])
  have seen : 61 ∈ regionOf label (maker.result label D).present persistent :=
    mem_regionOf.mpr ⟨made, rfl⟩
  rw [holds] at seen
  exact Finset.notMem_empty _ seen

/-- The query and the taker never share a configuration: one needs `61` absent, the other
present. -/
theorem no_round_reader_taker (D : Configuration (Term signature) Nat) :
    ¬ Round A label D [reader, taker] := by
  intro isRound
  have readerValid := isRound.valid reader List.mem_cons_self
  have takerValid := isRound.valid taker (List.mem_cons_of_mem _ List.mem_cons_self)
  have present : 61 ∈ D.present :=
    takerValid.firing.occurrences.taken_subset (by simp [Selection.commit, taker])
  obtain ⟨σ, solved⟩ := readerValid.firing.consistent
  have holds : regionOf label D.present persistent = ∅ :=
    readerValid.observations _ List.mem_cons_self σ solved
  have seen : 61 ∈ regionOf label D.present persistent := mem_regionOf.mpr ⟨present, rfl⟩
  rw [holds] at seen
  exact Finset.notMem_empty _ seen

/-- The maker and the taker never share a configuration: one needs `61` fresh, the other
present. -/
theorem no_round_maker_taker (D : Configuration (Term signature) Nat) :
    ¬ Round A label D [maker, taker] := by
  intro isRound
  have makerValid := isRound.valid maker List.mem_cons_self
  have takerValid := isRound.valid taker (List.mem_cons_of_mem _ List.mem_cons_self)
  have present : 61 ∈ D.present :=
    takerValid.firing.occurrences.taken_subset (by simp [Selection.commit, taker])
  exact Finset.disjoint_left.mp makerValid.firing.occurrences.fresh
    (by simp [Selection.commit, maker]) present

/-- **No round among the three, unless a firing is paired with itself.** -/
theorem no_round (f : Run) (inF : f ∈ [reader, maker, taker]) (g : Run)
    (inG : g ∈ [reader, maker, taker]) (D : Configuration (Term signature) Nat)
    (isRound : Round A label D [f, g]) : f = g := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inF inG
  rcases inF with rfl | rfl | rfl <;> rcases inG with rfl | rfl | rfl
  · rfl
  · exact (no_round_maker_reader D (isRound.perm A label (List.Perm.swap _ _ []))).elim
  · exact (no_round_reader_taker D isRound).elim
  · exact (no_round_maker_reader D isRound).elim
  · rfl
  · exact (no_round_maker_taker D isRound).elim
  · exact (no_round_reader_taker D (isRound.perm A label (List.Perm.swap _ _ []))).elim
  · exact (no_round_maker_taker D (isRound.perm A label (List.Perm.swap _ _ []))).elim
  · rfl

/-! ### Both orders run, to one configuration -/

theorem reader_valid_empty : reader.Valid A label empty := by
  refine (PredicateQueryAdmission.valid_fixed_iff A label reader.rule [noPersistent] empty
    reader.selection).mpr ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, empty, reader]⟩,
      by simp [reader]⟩, ?_⟩
  intro query member
  obtain rfl := List.mem_singleton.mp member
  decide

theorem taker_problem_solved (σ : Subst signature) (D : Configuration (Term signature) Nat)
    (base : A.Models σ D.equations) :
    A.Models σ (taker.selection.problem label taker.rule D) := by
  intro equation member
  simp only [Selection.problem, Selection.equations, taker, List.zipWith_cons_cons,
    List.zipWith_nil_left, List.append_nil, List.mem_append, List.mem_singleton] at member
  rcases member with inBase | rfl
  · exact base equation inBase
  · rfl

/-- The query first: absence, then the maker, then the taker. -/
theorem query_first_runs : Executable A label empty [reader, maker, taker] := by
  refine ⟨reader_valid_empty, ?_, ?_, ?_⟩
  · refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨Subst.id signature, by
        simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
          reader, maker]⟩, by simp [maker]⟩, by simp [maker]⟩
  · refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨Subst.id signature, taker_problem_solved _ _ (by
        simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
          reader, maker])⟩, by simp [taker]⟩, by simp [taker]⟩
  · exact ⟨Subst.id signature, taker_problem_solved _ _ (by
      simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
        reader, maker])⟩

/-- The query last: the maker falsifies the absence and the taker restores it. -/
theorem query_last_runs : Executable A label empty [maker, taker, reader] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, empty, maker]⟩,
      by simp [maker]⟩, by simp [maker]⟩
  · refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
      ⟨Subst.id signature, taker_problem_solved _ _ (by
        simp [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
          maker])⟩, by simp [taker]⟩, by simp [taker]⟩
  · refine (PredicateQueryAdmission.valid_fixed_iff A label reader.rule [noPersistent] _
      reader.selection).mpr ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
        ⟨Subst.id signature, by
          intro equation member
          simp only [Selection.problem, Selection.equations, Selection.result, Firing.result,
            empty, maker, taker, reader, List.zipWith_cons_cons, List.zipWith_nil_left,
            List.append_nil, List.nil_append, List.mem_singleton] at member
          subst member
          rfl⟩,
        by simp [reader]⟩, ?_⟩
    intro query member
    obtain rfl := List.mem_singleton.mp member
    decide
  · exact ⟨Subst.id signature, by
      intro equation member
      simp only [Selection.problem, Selection.equations, Selection.result, Firing.result, empty,
        maker, taker, reader, List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil,
        List.nil_append, List.mem_singleton] at member
      subst member
      rfl⟩

theorem same_end :
    SameUpTo A (follow label empty [reader, maker, taker]) (follow label empty [maker, taker, reader]) :=
  ⟨fun _ => Iff.rfl, by decide⟩

theorem same_firings : [reader, maker, taker].Perm [maker, taker, reader] :=
  List.perm_append_comm (l₁ := [reader]) (l₂ := [maker, taker])

/-- **Negative control: restored absence, two traces.** Both orders run from the empty
configuration, they have the same firings and reach the same configuration, and they are not
round equivalent, hence not statically trace equivalent either. -/
theorem restored_absence_two_traces :
    Executable A label empty [reader, maker, taker] ∧
      Executable A label empty [maker, taker, reader] ∧
      [reader, maker, taker].Perm [maker, taker, reader] ∧
      SameUpTo A (follow label empty [reader, maker, taker])
        (follow label empty [maker, taker, reader]) ∧
      ¬ RoundEquiv A label empty [reader, maker, taker] [maker, taker, reader] ∧
      ¬ Mettapedia.GSLT.Distinction.CausalGluing.TraceEquiv (StaticIndependent label)
        [reader, maker, taker] [maker, taker, reader] := by
  have different : ¬ RoundEquiv A label empty [reader, maker, taker] [maker, taker, reader] := by
    intro equivalent
    have same := RoundEquiv.eq_of_no_round A label no_round equivalent (List.Perm.refl _)
    have heads := congrArg (fun w : List Run => w.map fun f => f.selection.made) same
    revert heads
    decide
  exact ⟨query_first_runs, query_last_runs, same_firings, same_end, different,
    fun static => different (traceEquiv_roundEquiv A label static empty query_first_runs)⟩

/-- **Two arrows of the contextual trace category with one source, one target and one bag of
firings.** -/
theorem restored_absence_two_arrows :
    ∃ p q : OccurrencePath (presentation A label) (classOf A label empty)
      (classOf A label (follow label empty [reader, maker, taker])),
      (OccurrencePath.siteBag p = OccurrencePath.siteBag q) ∧
        Trace.mk (T := (concurrency A label).tiles) p ≠ Trace.mk q := by
  obtain ⟨p, pSites⟩ := exists_path A label empty _ query_first_runs _ rfl
  obtain ⟨q, qSites⟩ := exists_path A label empty _ query_last_runs _
    (Quotient.sound (sameUpTo_symm A same_end))
  refine ⟨p, q, ?_, fun same => ?_⟩
  · unfold OccurrencePath.siteBag
    exact (congrArg (fun l : List Run => (l : Multiset Run)) pSites).trans
      ((Multiset.coe_eq_coe.mpr same_firings).trans
        (congrArg (fun l : List Run => (l : Multiset Run)) qSites.symm))
  · have equivalent := (trace_eq_iff_roundEquiv A label p q).mp same
    have first := cast (congrArg (fun l : List Run => RoundEquiv A label empty l
      (OccurrencePath.sites q)) pSites) equivalent
    exact restored_absence_two_traces.2.2.2.2.1
      (cast (congrArg (RoundEquiv A label empty [reader, maker, taker]) qSites) first)

end AbsenceControls

#print axioms RoundEquiv.invariant_on
#print axioms RoundEquiv.eq_of_no_round
#print axioms AbsenceControls.no_round_maker_reader
#print axioms AbsenceControls.no_round_reader_taker
#print axioms AbsenceControls.no_round_maker_taker
#print axioms AbsenceControls.no_round
#print axioms AbsenceControls.query_first_runs
#print axioms AbsenceControls.query_last_runs
#print axioms AbsenceControls.restored_absence_two_traces
#print axioms AbsenceControls.restored_absence_two_arrows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
