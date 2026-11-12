import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.HeatingBisimulation

/-!
# Firings over ground terms, for the fragments' theorems and controls

The first-order step over ground terms with generative names and codes (`IssuingControls.base`):
equal means identical, and the identity is the only solution. This module collects what the
fragments use there.

* `ground_valid`: build an admitted selection from its parts (through `IssuingControls.admits_of`).
* `GroundStep R`: the step restricted to a rule set `R`; `facts`: the labels present, as a set.
* `groundStep_knowledge`: every firing leaves knowledge whose equations have identical sides, so
  knowledge never blocks a later firing.
* `exists_fresh`, `fresh_outputs`: a store always has fresh identities for any labels.
* `taken_nil_present`: a firing that takes nothing keeps every occurrence.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.GroundFirings

open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open NamesOnTheStep NamesOnTheStep.IssuingControls
open HeatingBisimulation (RuleSet)

/-- **An admitted ground selection, from its parts.** -/
theorem ground_valid {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (takenDistinct : sel.taken.Nodup) (madeDistinct : sel.made.Nodup)
    (takes : r.take = sel.taken.map Prod.fst) (reads : r.read = sel.read.map Prod.fst)
    (outputs : sel.made.map Prod.fst = r.produce)
    (enabled : Enabled Prod.fst C.present (sel.commit (T := Expr)))
    (knowledge : ∀ e ∈ C.equations, e.1 = e.2) (noTells : r.tell = [])
    (checks : ∀ c ∈ r.checks, c.Holds ground () Prod.fst C.present) :
    sel.Valid ground Prod.fst r C :=
  (PredicateQueryAdmission.valid_empty_iff ground Prod.fst r C sel).mp
    (admits_of (D := fun _ _ _ _ => True) (σ := (C, ∅)) (fresh := []) takenDistinct madeDistinct
      takes reads outputs enabled knowledge noTells checks trivial).1

/-- **The step restricted to a rule set**, over ground terms. -/
def GroundStep (R : RuleSet Expr) (C C' : Conf) : Prop :=
  ∃ rule, R rule ∧ ConstraintMultisetRewriting.Step ground Prod.fst rule C C'

/-- The labels present, as a set. -/
def facts (C : Conf) : Set Expr := {p | ∃ o ∈ C.present, o.1 = p}

/-- An admitted ground selection solves its whole problem at the one solution. -/
theorem solved_of_valid {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) : ground.Models () (sel.problem Prod.fst r C) := by
  obtain ⟨u, solved⟩ := valid.consistent
  cases u
  exact solved

/-- **Ground knowledge stays trivial**: every equation after a firing has identical sides. -/
theorem result_knowledge {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) :
    ∀ e ∈ (sel.result Prod.fst r C).equations, e.1 = e.2 :=
  fun e member => solved_of_valid valid e member

theorem groundStep_knowledge {R : RuleSet Expr} {C C' : Conf} (step : GroundStep R C C') :
    ∀ e ∈ C'.equations, e.1 = e.2 := by
  obtain ⟨_, _, sel, valid, rfl⟩ := step
  exact result_knowledge valid

/-- The tells of an admitted ground rule have identical sides. -/
theorem tells_trivial {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (valid : sel.Valid ground Prod.fst r C) : ∀ e ∈ r.tell, e.1 = e.2 :=
  fun e member => (Selection.models_problem ground valid (solved_of_valid valid)).2.2.2 e member

/-- **A firing that takes nothing keeps every occurrence.** -/
theorem taken_nil_present {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    (noTakes : r.take = []) (valid : sel.Valid ground Prod.fst r C) :
    C.present ⊆ (sel.result Prod.fst r C).present := by
  have lengths := valid.take_length
  rw [noTakes] at lengths
  have taken : sel.taken = [] := List.length_eq_zero_iff.mp lengths.symm
  intro o member
  change o ∈ fire C.present (sel.commit (T := Expr))
  rw [mem_fire]
  left
  exact ⟨member, by simp [Selection.commit, taken]⟩

/-- Made occurrences are present after the firing. -/
theorem made_present {C : Conf} {r : RuleInstance Expr} {sel : Selection Occ}
    {o : Occ} (member : o ∈ sel.made) : o ∈ (sel.result Prod.fst r C).present := by
  change o ∈ fire C.present (sel.commit (T := Expr))
  rw [mem_fire]
  right
  simpa [Selection.commit] using member

/-- **Fresh identities exist** for every label beside every store. -/
theorem exists_fresh (used : Finset Occ) (value : Expr) : ∃ o : Occ, o ∉ used ∧ o.1 = value := by
  obtain ⟨n, unused⟩ := Infinite.exists_notMem_finset (used.image Prod.snd)
  exact ⟨(value, n), fun member => unused (Finset.mem_image.mpr ⟨_, member, rfl⟩), rfl⟩

/-- **Fresh outputs**: distinct new identities carrying any list of labels. -/
theorem fresh_outputs : ∀ (values : List Expr) (world : Finset Occ), ∃ made : List Occ,
    made.Nodup ∧ Disjoint made.toFinset world ∧ made.map Prod.fst = values
  | [], _ => ⟨[], by simp, by simp, rfl⟩
  | value :: values, world => by
      obtain ⟨o, fresh, atValue⟩ := exists_fresh world value
      obtain ⟨made, distinct, away, outputs⟩ := fresh_outputs values (insert o world)
      have absent : o ∉ made := fun member =>
        Finset.disjoint_left.mp away (by simpa using member) (by simp)
      refine ⟨o :: made, List.nodup_cons.mpr ⟨absent, distinct⟩, ?_, ?_⟩
      · apply Finset.disjoint_left.mpr
        intro item inMade inWorld
        rcases List.mem_cons.mp (by simpa using inMade) with rfl | member
        · exact fresh inWorld
        · exact Finset.disjoint_left.mp away (by simpa using member) (by simp [inWorld])
      · simp [outputs, atValue]

#print axioms ground_valid
#print axioms groundStep_knowledge
#print axioms tells_trivial
#print axioms taken_nil_present
#print axioms fresh_outputs

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.GroundFirings
