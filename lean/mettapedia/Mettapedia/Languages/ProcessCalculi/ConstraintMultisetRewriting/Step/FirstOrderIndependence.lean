import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsRounds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence

/-!
# Transport and independence in the one-frame instance

The first-order step (`AnnotatedRuns.firstOrder`) has one frame, so its isomorphisms of states are
configurations with the same solutions and the same occurrences, and its firings move and have
residuals as themselves (`firstOrderTransport`).

* **Diamonds close** whenever both orders are admitted (`firstOrder_closes`), so semantic
  independence is the four admissions (`firstOrder_independent_iff`).
* **It coincides with the static independence where that applies.** For firings without guards
  whose query regions do not depend on the solution, once one order runs, semantic independence
  is exactly `StaticIndependent` (`firstOrder_independent_iff_static`).
* **Footprints disjoint at every solution give independence** (`round_independent`): a round of two,
  whose members ignore each other's writes at every solution of the pair's cut, is independent.
* **Solution-indexed footprints** (`TransportControls.overlap_at_one_solution_only`): a writer and
  a query whose region depends on the solution are disjoint at one solution and overlap at
  another. Uniform reasoning refuses the pair (not `Compatible`, not statically independent), and
  the pair is indeed dependent; the footprint at the disjoint solution alone would accept it.
* **The first-order fibre decides independence** (`valid_iff_tests`, `decidableIndependent`): for
  static firings, admission is the shapes, the occurrences, one consistency test and one evaluation
  per query; with decidable equality of terms and decidable consistency (first-order unification)
  independence is decided.
* **Site accounts** are properties of the one-frame traces in every commutative monoid
  (`firstOrder_account_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport)
open MeTTaCalculus.OccurrenceCommits (Commit TraceIndependent regionOf fire)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section OneFrameTransport

variable (A : SubstitutionAction T S) (label : O → T)

/-- Configurations with the same solutions and occurrences are isomorphic states of the interface,
over the identity of the one frame. -/
def sameStateIso {C D : Configuration T O} (same : SameUpTo A C D) :
    (firstOrder A label).StateIso C D where
  frame := Frames.Iso.refl PUnit.unit
  knowledge := Frames.Equivalent.trans (Frames.Iso.equivalent_refl _) (fun _ σ => same.1 σ)
  rename := Equiv.refl O
  present := by
    simp only [Equiv.refl_toEmbedding, Finset.map_refl]
    exact same.2

/-- **Transport in the one-frame instance.** -/
def firstOrderTransport : Transport (firstOrder A label).toStep where
  Iso C D := PLift (SameUpTo A C D)
  toStateIso i := sameStateIso A label i.down
  refl C := ⟨SameUpTo.refl A C⟩
  symm i := ⟨sameUpTo_symm A i.down⟩
  trans i j := ⟨SameUpTo.trans A i.down j.down⟩
  Alike f f' := f = f'
  alike_equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  selection_alike same := congrArg _ same
  admits_alike same := same ▸ Iff.rfl
  result_alike {C} {f} _ same _ _ := by
    subst same
    exact ⟨SameUpTo.refl A _⟩
  move _ f := f
  move_alike _ _ _ same := same
  move_refl _ := rfl
  move_trans _ _ _ := rfl
  move_symm _ _ := rfl
  selection_move _ f := (Interface.renameSelection_refl f.selection).symm
  admits_move i _ := (Firing.valid_congr A label i.down).symm
  result_move i f _ := ⟨f.result_congr A label i.down⟩
  residual _ _ f := f
  selection_residual _ _ _ := rfl
  move_residual _ _ _ _ := rfl

/-- **Diamonds close in the one-frame instance** whenever both orders are admitted. -/
theorem firstOrder_closes : (firstOrderTransport A label).Closes := by
  intro C f g first second _ _
  refine ⟨⟨fun σ => ?_, ?_⟩⟩
  · show A.Models σ (g.result label (f.result label C)).equations ↔
      A.Models σ (f.result label (g.result label C)).equations
    rw [Firing.result_equations', Firing.result_equations', Firing.result_equations',
      Firing.result_equations']
    simp only [SubstitutionAction.models_append]
    constructor
    · rintro ⟨⟨base, fAdded⟩, gAdded⟩
      exact ⟨⟨base, gAdded⟩, fAdded⟩
    · rintro ⟨⟨base, gAdded⟩, fAdded⟩
      exact ⟨⟨base, fAdded⟩, gAdded⟩
  · show MeTTaCalculus.OccurrenceCommits.fireList C.present
        [f.selection.commit (T := T), g.selection.commit (T := T)] =
      MeTTaCalculus.OccurrenceCommits.fireList C.present
        [g.selection.commit (T := T), f.selection.commit (T := T)]
    refine MeTTaCalculus.OccurrenceCommits.fireList_perm ?_ (List.Perm.swap _ _ [])
    intro c member
    rcases List.mem_pair.mp member with rfl | rfl
    · exact ⟨first.firing.occurrences.taken_subset, first.firing.occurrences.fresh⟩
    · exact ⟨second.firing.occurrences.taken_subset, second.firing.occurrences.fresh⟩

/-- **Independence in the one-frame instance is the four admissions.** -/
theorem firstOrder_independent_iff {C : Configuration T O} {f g : Firing T S O} :
    (firstOrderTransport A label).Independent C f g ↔
      f.Valid A label C ∧ g.Valid A label C ∧ g.Valid A label (f.result label C) ∧
        f.Valid A label (g.result label C) := by
  rw [Transport.independent_iff_admits (firstOrder_closes A label)]
  constructor
  · rintro ⟨first, second, afterFirst, afterSecond⟩
    exact ⟨first, second, afterFirst, afterSecond⟩
  · rintro ⟨first, second, afterFirst, afterSecond⟩
    exact ⟨first, second, afterFirst, afterSecond⟩

/-- Both orders admitted, for firings with solution-independent query regions, give footprints that
are trace independent at every solution. -/
theorem independent_of_both_orders {C : Configuration T O} {f g : Firing T S O}
    (fStatic : f.StaticQueries) (gStatic : g.StaticQueries)
    (fValid : f.Valid A label C) (gValid : g.Valid A label C)
    (gAfter : g.Valid A label (f.result label C)) (fAfter : f.Valid A label (g.result label C)) :
    Independent label f g := by
  have fEnabled := fValid.firing.occurrences
  have gEnabled := gValid.firing.occurrences
  have gFire := (MeTTaCalculus.OccurrenceCommits.enabled_fire_iff gEnabled fEnabled).mp
    gAfter.firing.occurrences
  have fFire := (MeTTaCalculus.OccurrenceCommits.enabled_fire_iff fEnabled gEnabled).mp
    fAfter.firing.occurrences
  intro σ
  refine ⟨⟨fFire.1, ?_, ?_⟩, ?_, ?_⟩
  · rintro (kept | ⟨read, readMember, o, written, inRegion⟩)
    · exact gFire.2 (Or.inl kept)
    · obtain ⟨query, member, rfl⟩ := List.mem_map.mp readMember
      obtain ⟨τ, solved⟩ := gAfter.firing.consistent
      refine census_refused_after_writer A label gValid fEnabled member solved
        (o := o) ?_ ?_ gAfter
      · simpa [Firing.footprintAt, PredicateQueryAdmission.commit, Selection.commit] using written
      · rw [gStatic query member τ σ]
        exact inRegion
  · rintro (kept | ⟨read, readMember, o, written, inRegion⟩)
    · exact fFire.2 (Or.inl kept)
    · obtain ⟨query, member, rfl⟩ := List.mem_map.mp readMember
      obtain ⟨τ, solved⟩ := fAfter.firing.consistent
      refine census_refused_after_writer A label fValid gEnabled member solved
        (o := o) ?_ ?_ fAfter
      · simpa [Firing.footprintAt, PredicateQueryAdmission.commit, Selection.commit] using written
      · rw [fStatic query member τ σ]
        exact inRegion
  · exact fEnabled.fresh.mono_right (Finset.union_subset gEnabled.taken_subset gEnabled.kept_subset)
  · exact gEnabled.fresh.mono_right (Finset.union_subset fEnabled.taken_subset fEnabled.kept_subset)

/-- **Semantic independence coincides with the static independence where that applies**: for
firings without guards whose query regions do not depend on the solution, once one order runs. -/
theorem firstOrder_independent_iff_static {C : Configuration T O} {f g : Firing T S O}
    (fStatic : f.Static) (gStatic : g.Static) (fValid : f.Valid A label C)
    (gAfter : g.Valid A label (f.result label C)) :
    (firstOrderTransport A label).Independent C f g ↔ StaticIndependent label f g := by
  constructor
  · intro independent
    obtain ⟨-, gValid, -, fAfter⟩ := (firstOrder_independent_iff A label).mp independent
    exact ⟨fStatic, gStatic,
      independent_of_both_orders A label fStatic.queries gStatic.queries fValid gValid gAfter fAfter⟩
  · intro independent
    obtain ⟨gValid, fAfter, -⟩ := swap_valid A label independent fValid gAfter
    exact (firstOrder_independent_iff A label).mpr ⟨fValid, gValid, gAfter, fAfter⟩

/-- **Footprints disjoint at every solution give independence**: a round of two is an independent
pair. Its members' guards ignore each other's writes, and each writes nothing into the other's
query regions, at every solution of the pair's cut. -/
theorem round_independent {C : Configuration T O} {f g : Firing T S O}
    (isRound : Round A label C [f, g]) : (firstOrderTransport A label).Independent C f g := by
  have forward := Round.executable A label isRound
  have backward := Round.executable A label (isRound.perm A label (List.Perm.swap g f []))
  exact (firstOrder_independent_iff A label).mpr ⟨forward.1, backward.1, forward.2.1, backward.2.1⟩

/-- **Site accounts of one-frame traces**, in every commutative monoid. -/
theorem firstOrder_account_eq {M : Type*} [CommMonoid M] (grade : Firing T S O → M)
    {C : Configuration T O} {r r' : (firstOrder A label).Run C}
    (equivalent : (firstOrderTransport A label).TraceEquiv C r r') :
    r.account (fun _ f => grade f) = r'.account (fun _ f => grade f) :=
  Transport.TraceEquiv.account_eq_comm _ (fun _ _ => rfl) (fun same => congrArg _ same)
    (fun _ _ _ => rfl) equivalent

/-! ## Deciding independence in the static first-order fibre -/

/-- **Admission of a static firing is a finite test**: its shapes, its occurrences, one consistency
test, and one evaluation of each query, at any solution. -/
theorem valid_iff_tests {f : Firing T S O} {C : Configuration T O} (static : f.Static) (σ₀ : S) :
    f.Valid A label C ↔
      (f.selection.taken.Nodup ∧ f.selection.made.Nodup ∧
        f.rule.take.length = f.selection.taken.length ∧ f.rule.read.length = f.selection.read.length ∧
        f.selection.made.map label = f.rule.produce ∧
        MeTTaCalculus.OccurrenceCommits.Enabled label C.present (f.selection.commit (T := T)) ∧
        A.Consistent (f.selection.problem label f.rule C)) ∧
      ∀ query ∈ f.queries, (query.atSolution σ₀).Holds label C.present := by
  have region : ∀ query ∈ f.queries, ∀ σ : S, query.atSolution σ = query.atSolution σ₀ := by
    intro query member σ
    simp only [PredicateQueryAdmission.Query.atSolution, static.queries query member σ σ₀]
  constructor
  · intro valid
    refine ⟨⟨valid.firing.take_distinct, valid.firing.output_distinct, valid.firing.take_length,
      valid.firing.read_length, valid.firing.outputs, valid.firing.occurrences,
      valid.firing.consistent⟩, fun query member => ?_⟩
    obtain ⟨τ, solved⟩ := valid.firing.consistent
    rw [← region query member τ]
    exact valid.observations query member τ solved
  · rintro ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences, consistent⟩,
      queries⟩
    refine ⟨⟨takeDistinct, outputDistinct, takeLength, readLength, outputs, occurrences, consistent,
      ?_⟩, ?_⟩
    · intro check member
      rw [static.checks] at member
      cases member
    · intro query member σ _
      show (query.atSolution σ).Holds label C.present
      rw [region query member σ]
      exact queries query member

/-- **The first-order fibre decides admission of static firings**, with decidable equality of terms
and decidable consistency (first-order unification). -/
def decidableValid [DecidableEq T] [∀ store : EquationStore T, Decidable (A.Consistent store)]
    {f : Firing T S O} (static : f.Static) (σ₀ : S) (C : Configuration T O) :
    Decidable (f.Valid A label C) :=
  decidable_of_iff _ (valid_iff_tests A label static σ₀).symm

/-- **The first-order fibre decides independence of static firings.** -/
def decidableIndependent [DecidableEq T] [∀ store : EquationStore T, Decidable (A.Consistent store)]
    {f g : Firing T S O} (fStatic : f.Static) (gStatic : g.Static) (σ₀ : S) (C : Configuration T O) :
    Decidable ((firstOrderTransport A label).Independent C f g) :=
  letI := decidableValid A label fStatic σ₀ C
  letI := decidableValid A label gStatic σ₀ C
  letI := decidableValid A label gStatic σ₀ (f.result label C)
  letI := decidableValid A label fStatic σ₀ (g.result label C)
  decidable_of_iff _ (firstOrder_independent_iff A label).symm

end OneFrameTransport

/-! ## Solution-indexed footprints: controls -/

namespace TransportControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)

/-- Firings of the controls. -/
abbrev Control := Firing (Term signature) (Subst signature) Nat

/-- Occurrence `5` is labelled `1`, occurrence `6` is labelled `0`. -/
def label : Nat → Term signature
  | 5 => .const 1
  | _ => .const 0

def isOne : Term signature → Bool
  | .const name => name == 1
  | _ => false

/-- A query whose region depends on the solution: the labels `1`, when the solution sets `X` to
`1`; nothing otherwise. Its census is empty. -/
def watched : PredicateQueryAdmission.Query (Term signature) (Subst signature) Nat :=
  ⟨fun σ t => isOne (Subst.applyTerm σ (.var 0)) && isOne t, ∅⟩

/-- Queries the watched region and writes nothing. -/
def watcher : Control := ⟨⟨[], [], [], [], []⟩, [watched], ⟨[], [], []⟩⟩

/-- Makes occurrence `5`, labelled `1`. -/
def writer : Control := ⟨⟨[], [], [], [], [.const 1]⟩, [], ⟨[], [], [5]⟩⟩

/-- Makes occurrence `6`, labelled `0`: outside the watched region at every solution. -/
def outsider : Control := ⟨⟨[], [], [], [], [.const 0]⟩, [], ⟨[], [], [6]⟩⟩

def start : Configuration (Term signature) Nat := ⟨[], ∅⟩

/-- `X` is `1`. -/
def one : Subst signature := Subst.single 0 (.const 1)

/-- `X` is `2`. -/
def two : Subst signature := Subst.single 0 (.const 2)

theorem watcher_valid : watcher.Valid A label start := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, start, watcher]⟩,
    by simp [watcher]⟩, ?_⟩
  intro query member σ _
  obtain rfl := List.mem_singleton.mp member
  simp [MeTTaCalculus.OccurrenceCommits.PredicateQuery.Holds, regionOf, start, watched,
    PredicateQueryAdmission.Query.atSolution]

theorem writer_valid : writer.Valid A label start := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, start, writer]⟩,
    by simp [writer]⟩, by simp [writer]⟩

/-- After the writer, the watcher is refused: at the solution `X = 1` its region holds the new
occurrence. -/
theorem watcher_refused_after_writer : ¬ watcher.Valid A label (writer.result label start) := by
  intro valid
  have holds := valid.observations _ (List.mem_singleton_self _) one (by
    simp [Selection.problem, Selection.equations, Selection.result, Firing.result, start,
      watcher, writer])
  revert holds
  decide

/-- **A pair whose footprints are disjoint at one solution and overlap at another.** At `X = 2`
the writer writes outside the watched region; at `X = 1` it writes into it. Uniform reasoning
refuses the pair: it is not a compatible pair of a round, and its footprints are not trace
independent at every solution. The pair is indeed dependent. Reasoning from the footprint at
`X = 2` alone would accept it, so authority over a query region has to be indexed by solutions. -/
theorem overlap_at_one_solution_only :
    TraceIndependent label (writer.footprintAt two) (watcher.footprintAt two) ∧
      ¬ TraceIndependent label (writer.footprintAt one) (watcher.footprintAt one) ∧
      ¬ Independent label writer watcher ∧ ¬ Compatible A label start writer watcher ∧
      ¬ (firstOrderTransport A label).Independent start writer watcher ∧
      ¬ watcher.StaticQueries := by
  have atTwo : TraceIndependent label (writer.footprintAt two) (watcher.footprintAt two) := by
    unfold TraceIndependent MeTTaCalculus.OccurrenceCommits.Independent
      MeTTaCalculus.OccurrenceCommits.Clash MeTTaCalculus.OccurrenceCommits.Spoils
      MeTTaCalculus.OccurrenceCommits.WritesInto MeTTaCalculus.OccurrenceCommits.Commit.uses
    simp only [Firing.footprintAt_taken, Firing.footprintAt_kept, Firing.footprintAt_made,
      Firing.footprintAt_queries, watcher, writer, List.map_cons, List.map_nil]
    decide
  have atOne : ¬ TraceIndependent label (writer.footprintAt one) (watcher.footprintAt one) := by
    unfold TraceIndependent MeTTaCalculus.OccurrenceCommits.Independent
      MeTTaCalculus.OccurrenceCommits.Clash MeTTaCalculus.OccurrenceCommits.Spoils
      MeTTaCalculus.OccurrenceCommits.WritesInto MeTTaCalculus.OccurrenceCommits.Commit.uses
    simp only [Firing.footprintAt_taken, Firing.footprintAt_kept, Firing.footprintAt_made,
      Firing.footprintAt_queries, watcher, writer, List.map_cons, List.map_nil]
    decide
  refine ⟨atTwo, atOne, fun independent => atOne (independent one), fun compatible => ?_,
    fun independent => watcher_refused_after_writer
      ((firstOrder_independent_iff A label).mp independent).2.2.1, fun static => ?_⟩
  · have ignored := compatible.2.2.2.2 watched (List.mem_singleton_self _) one (by
      simp [pairCut, Firing.added, GuardFreeProcessOrders.added, Selection.equations, start, watcher, writer]) 5
      (by simp [writer])
    revert ignored
    decide
  · have same := congrFun (static watched (List.mem_singleton_self _) one two) (.const 1)
    revert same
    decide

/-- **Positive control: disjoint at every solution.** The outsider writes outside the watched
region at every solution, so the pair forms a round and is independent. -/
theorem outsider_watcher_independent :
    (firstOrderTransport A label).Independent start outsider watcher := by
  apply round_independent
  refine ⟨?_, ⟨Subst.id signature, ?_⟩, List.pairwise_pair.mpr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x member
    rcases List.mem_pair.mp member with rfl | rfl
    · exact ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
        ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, start, outsider]⟩,
        by simp [outsider]⟩, by simp [outsider]⟩
    · exact watcher_valid
  · simp [jointProblem, Firing.added, GuardFreeProcessOrders.added, Selection.equations, start, watcher, outsider]
  · unfold MeTTaCalculus.OccurrenceCommits.Independent MeTTaCalculus.OccurrenceCommits.Clash
      MeTTaCalculus.OccurrenceCommits.Spoils MeTTaCalculus.OccurrenceCommits.WritesInto
    simp only [Selection.commit, watcher, outsider]
    decide
  · intro check member
    simp [outsider] at member
  · intro check member
    simp [watcher] at member
  · intro query member
    simp [outsider] at member
  · intro query member σ _ o written
    obtain rfl := List.mem_singleton.mp member
    have only : o = 6 := by simpa [outsider] using written
    subst only
    show (isOne (Subst.applyTerm σ (.var 0)) && isOne (.const 0)) = false
    simp [isOne]

end TransportControls

#print axioms firstOrder_closes
#print axioms firstOrder_independent_iff
#print axioms independent_of_both_orders
#print axioms firstOrder_independent_iff_static
#print axioms round_independent
#print axioms firstOrder_account_eq
#print axioms valid_iff_tests
#print axioms TransportControls.overlap_at_one_solution_only
#print axioms TransportControls.outsider_watcher_independent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
