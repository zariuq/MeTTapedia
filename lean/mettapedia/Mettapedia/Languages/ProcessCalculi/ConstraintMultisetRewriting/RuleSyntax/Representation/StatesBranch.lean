import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive

/-!
# Infinitely many successor states, finitely many successor bags

`Representation.results_finite` counts the bags that the results of admitted firings read as, and finds
finitely many for a finite range-restricted positive program. The step itself is a relation on states
(`Machines.stepSystem`), and a state carries the identities of its rows. A firing that makes a row may give it
any identity that is not present, so:

* `withMade_admits`: a firing with its made identities replaced by other fresh distinct identities is
  admitted exactly as before, over every frame action;
* `successors_infinite`: when identities are infinitely many, a state at which some admitted firing makes a
  row has infinitely many successor states, for every program; they differ in the identity of the made row;
* `start_successors_infinite`: the start state of every pending evaluation of the nineteen-rule program
  has infinitely many successor states, though they all read as one row (`PartialRecursive.deterministic`).

So the step of a finite range-restricted positive program branches finitely only up to identities: at a state
that reads as a bag, finitely many successor bags (`results_finite`); and wherever an admitted firing makes a
row, infinitely many successor states.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.StatesBranch

open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)

universe uO uT uH uE uOcc

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Interface.Frames Tm Hom) {O : Type uOcc} [DecidableEq O] {E : Extensions.{uO, uH, uE} Hom}
  {P : Program Tm}

/-- The same firing with another list of made identities. -/
def withMade {a : Obj} (f : Firing O E P a) (made : List O) : Firing O E P a :=
  { f with selection := { f.selection with made := made } }

/-- **Replacing the made identities by other fresh distinct ones keeps admission.** -/
theorem withMade_admits {s : State Tm O} (f : Firing O E P s.frame) (admitted : (step X O E P).Admits f)
    (made : List O) (nodup : made.Nodup) (length : made.length = f.selection.made.length)
    (fresh : ∀ o ∈ made, o ∉ s.present) : (step X O E P).Admits (withMade f made) := by
  obtain ⟨isFresh, ⟨takenNodup, -, takeLength, readLength, produceLength, collectLength⟩, enabled, solvable,
    checks, collect⟩ := (admits_iff f).mp admitted
  refine (admits_iff (withMade f made)).mpr ⟨isFresh, ⟨takenNodup, nodup, takeLength, readLength,
    produceLength.trans length.symm, collectLength⟩, ⟨enabled.taken_subset, enabled.kept_subset, enabled.apart,
    ?_, enabled.queries_hold⟩, solvable, checks, collect⟩
  exact Finset.disjoint_left.mpr fun o (inside : o ∈ made.toFinset) present =>
    fresh o (List.mem_toFinset.mp inside) present

/-- The present identities after the firing with other made identities. -/
theorem withMade_present {s : State Tm O} (f : Firing O E P s.frame) (made : List O) (o : O) :
    o ∈ ((withMade f made).result X s).present ↔ (o ∈ s.present ∧ o ∉ f.selection.taken) ∨ o ∈ made := by
  show o ∈ fire s.present ((withMade f made).selection.commit (T := Unit)) ↔ _
  rw [mem_fire]
  simp [withMade, Selection.commit]

/-- **Infinitely many successor states**: when identities are infinitely many, a state at which some admitted
firing makes a row has infinitely many successors. They differ in the identity of the made row. -/
theorem successors_infinite [Infinite O] {s : State Tm O} (f : Firing O E P s.frame)
    (admitted : (step X O E P).Admits f) (makes : f.selection.made ≠ []) :
    {t | Succ (step X O E P).toStep s t}.Infinite := by
  obtain ⟨m, rest, isMade⟩ := List.exists_cons_of_ne_nil makes
  obtain ⟨-, ⟨-, madeNodup, -, -, -, -⟩, enabled, -⟩ := (admits_iff f).mp admitted
  rw [isMade] at madeNodup
  have restNodup : rest.Nodup := (List.nodup_cons.mp madeNodup).2
  have restFresh : ∀ o ∈ rest, o ∉ s.present := fun o inside present =>
    Finset.disjoint_left.mp enabled.fresh
      (show o ∈ f.selection.made.toFinset by rw [isMade]; exact List.mem_toFinset.mpr (List.mem_cons_of_mem _ inside))
      present
  let used : Finset O := s.present ∪ rest.toFinset
  let outside : Set O := {o | o ∉ used}
  have outsideInfinite : outside.Infinite := (Set.toFinite (used : Set O)).infinite_compl
  let F : O → State Tm O := fun o => (withMade f (o :: rest)).result X s
  refine Set.infinite_of_injOn_mapsTo (f := F) ?_ ?_ outsideInfinite
  · intro o (inO : o ∉ used) o' (inO' : o' ∉ used) same
    have here : o ∈ (F o).present := (withMade_present X f (o :: rest) o).mpr (Or.inr List.mem_cons_self)
    rw [same] at here
    rcases (withMade_present X f (o' :: rest) o).mp here with ⟨present, -⟩ | inMade
    · exact absurd (Finset.mem_union_left _ present) inO
    · rcases List.mem_cons.mp inMade with isO' | inRest
      · exact isO'
      · exact absurd (Finset.mem_union_right _ (List.mem_toFinset.mpr inRest)) inO
  · intro o (inO : o ∉ used)
    have oNotPresent : o ∉ s.present := fun present => inO (Finset.mem_union_left _ present)
    have oNotRest : o ∉ rest := fun inside => inO (Finset.mem_union_right _ (List.mem_toFinset.mpr inside))
    have admitted' := withMade_admits X f admitted (o :: rest) (List.nodup_cons.mpr ⟨oNotRest, restNodup⟩)
      (by rw [isMade]; rfl)
      (fun o' inside => (List.mem_cons.mp inside).elim (fun same => same ▸ oNotPresent) (restFresh o'))
    exact ⟨withMade f (o :: rest), admitted', rfl⟩

end General

/-! ## The nineteen-rule program -/

section Partrec

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.PartialRecursive
open Presentation.Schematic
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec

/-- **The start state of every pending evaluation has infinitely many successor states** under the step of the
nineteen-rule program. Each of them reads as the one row of the reduct (`PartialRecursive.deterministic`). -/
theorem start_successors_infinite (c : Code) (v : List ℕ) :
    {t | Succ (schematicStep ℕ program).toStep (start c v) t}.Infinite := by
  have reduces : Reduces (Point.normal c .halt v).pattern (afterNormal c .halt v).pattern :=
    (reduces_iff_successor (.normal c .halt v) _).mpr ⟨afterNormal c .halt v, rfl, rfl⟩
  obtain ⟨g, admitted, -, -, -⟩ := firing_of_reduction (rowState_reads (eNormal c .halt v)) reduces
  have makesOne : g.selection.made.length = 1 := by
    obtain ⟨-, ⟨-, -, -, -, produceLength, -⟩, -⟩ := (admits_iff g).mp admitted
    obtain ⟨n, -, isRule⟩ := List.mem_map.mp g.member
    rw [← produceLength, ← isRule]
    rfl
  exact successors_infinite X g admitted (List.ne_nil_of_length_pos (by omega))

end Partrec

#print axioms withMade_admits
#print axioms successors_infinite
#print axioms start_successors_infinite

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.StatesBranch
