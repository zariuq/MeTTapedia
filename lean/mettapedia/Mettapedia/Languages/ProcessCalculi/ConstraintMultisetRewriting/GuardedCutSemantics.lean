import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SharedReadProcessLayouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutOrders

/-!
# Original all-future guards at independently computed finite cuts

The cut world is before the current event's consumption and production.
The ask problem includes its port equations and tells. Prefix equations are
compared by their models, without letting a later tell discharge an earlier ask.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardedCutSemantics

open LinearConnectionLayout ConditionalComposite GuardFreeProcessOrders

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {n : Nat}

noncomputable def selected (events : Fin n → Event T O) (cut : Finset (Fin n)) : List (Event T O) :=
  cut.toList.map events

noncomputable def cutWorld (before : Configuration T O) (events : Fin n → Event T O)
    (cut : Finset (Fin n)) : Finset O :=
  LinearConnectionLayout.residual before.present (selected events cut)

noncomputable def cutStore (before : Configuration T O) (label : O → T)
    (events : Fin n → Event T O) (cut : Finset (Fin n)) : EquationStore T :=
  before.equations ++ (selected events cut).flatMap fun event => addedEquations label event.1 event.2

def Asks (A : SubstitutionAction T S) (label : O → T) (before : Configuration T O)
    (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n)) : Prop :=
  ∀ current check, check ∈ (events current).1.checks →
    A.Entails (cutStore before label events (cuts current) ++
      addedEquations label (events current).1 (events current).2)
      (fun σ => check.Holds A σ label (cutWorld before events (cuts current)))

theorem mem_cutWorld (before : Configuration T O) (events : Fin n → Event T O)
    (cut : Finset (Fin n)) (occurrence : O) :
    occurrence ∈ cutWorld before events cut ↔
      (occurrence ∈ before.present ∨ ∃ current ∈ cut, occurrence ∈ (events current).2.made) ∧
        ¬ ∃ current ∈ cut, occurrence ∈ (events current).2.taken := by
  simp [cutWorld, LinearConnectionLayout.residual, made, taken, selected, List.mem_flatMap]

omit [DecidableEq O] in
theorem models_cutStore (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) (cut : Finset (Fin n)) :
    A.Models assignment (cutStore before label events cut) ↔
      A.Models assignment before.equations ∧
        ∀ current ∈ cut, A.Models assignment (addedEquations label (events current).1 (events current).2) := by
  rw [cutStore, A.models_append]
  apply and_congr_right
  intro _
  constructor
  · intro solved current member equation inEquations
    apply solved equation
    exact List.mem_flatMap.mpr ⟨events current,
      List.mem_map.mpr ⟨current, by simpa using member, rfl⟩, inEquations⟩
  · intro solved equation member
    obtain ⟨event, selectedMember, inEquations⟩ := List.mem_flatMap.mp member
    obtain ⟨current, inCut, rfl⟩ := List.mem_map.mp selectedMember
    exact solved current (by simpa using inCut) equation inEquations

theorem prefix_same_cut (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) (earlier : List (Fin n))
    (cut : Finset (Fin n)) (distinct : earlier.Nodup) (same : earlier.toFinset = cut)
    (layout : SharedReadProcessLayouts.Layout A assignment label before (earlier.map events)) :
    SameUpTo A (ConditionalSchedule.follow label before (earlier.map events))
      ⟨cutStore before label events cut, cutWorld before events cut⟩ := by
  have perm : earlier.Perm cut.toList := by
    apply (List.perm_ext_iff_of_nodup distinct cut.nodup_toList).mpr
    intro current
    simp only [Finset.mem_toList, ← same, List.mem_toFinset]
  refine ⟨?_, ?_⟩
  · intro σ
    rw [models_follow_iff, models_cutStore]
    apply and_congr_right
    intro _
    constructor
    · intro solved current member
      exact solved (events current) (List.mem_map.mpr ⟨current, by simpa [← same] using member, rfl⟩)
    · intro solved event member
      obtain ⟨current, indexMember, rfl⟩ := List.mem_map.mp member
      exact solved current (by simpa only [← same, List.mem_toFinset] using indexMember)
  · exact layout.final_rows.trans (UnorderedOccurrenceConnections.residual_eq_of_perm
      before.present (perm.map events))

theorem executable_of_prefix_valid (A : SubstitutionAction T S) (label : O → T)
    (events : Fin n → Event T O) :
    ∀ (order : List (Fin n)) (before : Configuration T O),
      (∀ earlier current later, order = earlier ++ current :: later →
        (events current).2.Valid A label (events current).1
          (ConditionalSchedule.follow label before (earlier.map events))) →
      A.Consistent (ConditionalSchedule.follow label before (order.map events)).equations →
      ConditionalSchedule.Executable A label before (order.map events)
  | [], _before, _valid, consistent => consistent
  | current :: rest, before, valid, consistent => by
    refine ⟨valid [] current rest rfl, executable_of_prefix_valid A label events rest
      ((events current).2.result label (events current).1 before) ?_ consistent⟩
    intro earlier selected later decomposition
    exact valid (current :: earlier) selected later (by simp [decomposition])

theorem executes_of_asks (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    (order : List (Fin n)) (distinct : order.Nodup)
    (layout : SharedReadProcessLayouts.Layout A assignment label before (order.map events))
    (realizes : GuardCutOrders.RealizesCuts events cuts order) (asks : Asks A label before events cuts) :
    ConditionalSchedule.Executable A label before (order.map events) := by
  apply executable_of_prefix_valid A label events order before
  · intro earlier current later decomposition
    have rawSplit : order.map events = earlier.map events ++ events current :: later.map events := by
      simp [decomposition]
    have resourceLayout : SharedReadProcessLayouts.Layout A assignment label
        (ConditionalSchedule.follow label before (earlier.map events)) (events current :: later.map events) :=
      SharedReadProcessLayouts.Layout.drop_prefix (earlier.map events) (events current :: later.map events)
        before (rawSplit ▸ layout)
    have shape := resourceLayout.shapes _ List.mem_cons_self
    refine ⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2.1, shape.2.2.2.2,
      resourceLayout.head_occurrences, ⟨assignment, resourceLayout.head_consistent⟩, ?_⟩
    intro check member σ solved
    have guarded : (events current).1.checks ≠ [] := by intro empty; simp [empty] at member
    have prefixLayout := SharedReadProcessLayouts.Layout.initial_segment (rawSplit ▸ layout)
    have prefixDistinct : earlier.Nodup := (List.nodup_append.mp (decomposition ▸ distinct)).1
    have sameCut := prefix_same_cut A assignment label before events earlier (cuts current)
      prefixDistinct (realizes earlier current later decomposition guarded) prefixLayout
    have sameProblem := equivalent_append A sameCut.1
      (addedEquations label (events current).1 (events current).2)
    rw [ConditionalComposite.problem_eq] at solved
    have holds := asks current check member σ ((sameProblem σ).mp solved)
    have worldEq : (ConditionalSchedule.follow label before (earlier.map events)).present =
        cutWorld before events (cuts current) := sameCut.2
    rw [worldEq]
    exact holds
  · exact ⟨assignment, layout.final_model⟩

theorem asks_of_executes (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    (order : List (Fin n)) (distinct : order.Nodup) (covers : ∀ current, current ∈ order)
    (layout : SharedReadProcessLayouts.Layout A assignment label before (order.map events))
    (realizes : GuardCutOrders.RealizesCuts events cuts order)
    (executes : ConditionalSchedule.Executable A label before (order.map events)) :
    Asks A label before events cuts := by
  intro current check member σ solved
  obtain ⟨earlier, later, decomposition⟩ := List.mem_iff_append.mp (covers current)
  have rawSplit : order.map events = earlier.map events ++ events current :: later.map events := by
    simp [decomposition]
  have valid := valid_after_earlier A label (earlier.map events) (events current) (later.map events)
    before (rawSplit ▸ executes)
  have guarded : (events current).1.checks ≠ [] := by intro empty; simp [empty] at member
  have prefixLayout := SharedReadProcessLayouts.Layout.initial_segment (rawSplit ▸ layout)
  have prefixDistinct : earlier.Nodup := (List.nodup_append.mp (decomposition ▸ distinct)).1
  have sameCut := prefix_same_cut A assignment label before events earlier (cuts current)
    prefixDistinct (realizes earlier current later decomposition guarded) prefixLayout
  have sameProblem := equivalent_append A sameCut.1
    (addedEquations label (events current).1 (events current).2)
  have originalSolved : A.Models σ ((events current).2.problem label (events current).1
      (ConditionalSchedule.follow label before (earlier.map events))) := by
    rw [ConditionalComposite.problem_eq]
    exact (sameProblem σ).mpr solved
  have holds := valid.checks check member σ originalSolved
  have worldEq : (ConditionalSchedule.follow label before (earlier.map events)).present =
      cutWorld before events (cuts current) := sameCut.2
  rw [worldEq] at holds
  exact holds

theorem executes_iff_asks (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (before : Configuration T O) (events : Fin n → Event T O) (cuts : Fin n → Finset (Fin n))
    (order : List (Fin n)) (distinct : order.Nodup) (covers : ∀ current, current ∈ order)
    (layout : SharedReadProcessLayouts.Layout A assignment label before (order.map events))
    (realizes : GuardCutOrders.RealizesCuts events cuts order) :
    ConditionalSchedule.Executable A label before (order.map events) ↔ Asks A label before events cuts :=
  ⟨asks_of_executes A assignment label before events cuts order distinct covers layout realizes,
    executes_of_asks A assignment label before events cuts order distinct layout realizes⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardedCutSemantics
