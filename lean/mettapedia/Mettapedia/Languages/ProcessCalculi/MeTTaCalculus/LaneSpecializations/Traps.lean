import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations.BagInstances

/-!
# Traps on the way from a lane's operation to its transform

Each trap is a place where an instance looks right and is not, or where a lane's behaviour is
not the instance it appears to be.

* **The vacuous-`every` lint** (`vacuousEveryLint`) flags a take in the kernel followed by an
  `every` suffix: when the suffix has no row, the commit consumes the kernel's occurrence and
  produces nothing (`linted_vacuous_consumes`). None of the lane instances is flagged
  (`instances_not_flagged`): `match` and remove-all have empty kernels, removal by one has no
  `every`. Remove-all with nothing to remove fires an empty commit (`removeAll_vacuous`), which is
  the PeTTa lane answering `true` when nothing was removed; the lint rightly leaves it alone.
* **`unique` is not the standard library's `unique`** (`Controls.unique_vs_dedup`): the library
  function removes duplicate answers, the source asks for exactly one occurrence. With two equal
  atoms in the region, the deduplicated answers are one value while the source has no row.
* **Instantiation that evaluates bound values is another term layer**
  (`Controls.evaluating_instantiation`): a `case` whose pattern contains a variable bound to
  `(- 3 1)` matches `(from 2)` when the binding is evaluated and `(from (- 3 1))` when it is
  data. The evaluating reading answers what the data layer's steps do not
  (`Controls.evaluating_unsound_for_data`), so a lane that evaluates there does not run the `let`
  source over its own term layer.

The alpha-ambiguity of removal (two alpha-equal copies, nothing removed) is
`BagInstances.Controls.two_alpha_copies`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Lanes

universe uO uV uT uP

variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP}

/-! ## The vacuous-`every` lint -/

/-- Whether a source takes what it picks. -/
def sourceTakes : Source V T P → Bool
  | .take _ => true
  | .unique .take _ => true
  | .all .take _ _ _ => true
  | _ => false

/-- Whether an `every` suffix follows. -/
def hasEvery : SourceList V T P → Bool
  | .done => false
  | .every _ => true
  | .cons _ rest => hasEvery rest
  | .absent _ rest => hasEvery rest

/-- **The vacuous-`every` lint**: some kernel source takes, and an `every` suffix follows it. -/
def vacuousEveryLint : SourceList V T P → Bool
  | .done => false
  | .every _ => false
  | .cons s rest => (sourceTakes s && hasEvery rest) || vacuousEveryLint rest
  | .absent _ rest => vacuousEveryLint rest

/-- The lint flags a take before an `every`. -/
theorem lint_flags_kernel_take (a p : P) :
    vacuousEveryLint (.cons (.take a) (.every (.cons (.read p) .done)) : SourceList V T P) = true :=
  rfl

/-- **None of the lane instances is flagged.** -/
theorem instances_not_flagged (p a xs : P) (t : T) (fold : Multiset T → T) :
    vacuousEveryLint (matchEvery p [] : Transform V T P).sources = false ∧
      vacuousEveryLint (matchEach p [] : Transform V T P).sources = false ∧
      vacuousEveryLint (.every (.cons (.take p) .done) : SourceList V T P) = false ∧
      vacuousEveryLint (.cons (.all .take p xs fold) .done : SourceList V T P) = false ∧
      vacuousEveryLint (addT a : Transform V T P).sources = false ∧
      vacuousEveryLint (takeIdentical t : Transform V T T).sources = false ∧
      vacuousEveryLint (takeUnique t : Transform V T T).sources = false ∧
      vacuousEveryLint (unifyT a t [] : Transform V T P).sources = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section Vacuous

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}

/-- **What the lint guards against**: a row of a take followed by an `every` whose suffix has no
row takes the kernel's occurrence and makes nothing. -/
theorem linted_vacuous_consumes {p : P} {rest : SourceList V T P} {template : List P}
    {σ : Subst V T} {x : Subst V T × List (Pick O T)}
    (member : x ∈ rows L m label S template (.cons (.take p) (.every rest)) σ)
    (empty : ∀ τ, rows L m label S template rest τ = 0) :
    ∃ o ∈ S, (footprintOf x.2).takes = {o} ∧ (footprintOf x.2).makes = 0 := by
  obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
  obtain ⟨o, inS, τ, -, rfl⟩ := mem_stepRows_take.mp inStep
  rw [rows_every, Multiset.mem_singleton] at inRest
  subst inRest
  obtain ⟨takes, -, makes⟩ := everyFootprint_vacuous (label := label) (S := S) (empty τ)
  refine ⟨o, inS, ?_, ?_⟩
  · simp [footprintOf_cons, takes]
  · simp [footprintOf_cons, makes]

/-- **Remove-all with nothing to remove fires an empty commit**: the `every` row of a take over an
empty region takes nothing and makes nothing, for a unitary matcher. -/
theorem removeAll_vacuous (unitary : Matcher.Unitary m) {p : P} {σ : Subst V T}
    (empty : regionOf label S (Matcher.region m σ p) = ∅) :
    (everyFootprint L m label S [] (.cons (.take p) .done) σ).takes = 0 ∧
      (everyFootprint L m label S [] (.cons (.take p) .done) σ).makes = 0 := by
  refine ⟨by rw [everyTake_takes_eq_region unitary, empty]; rfl, ?_⟩
  unfold everyFootprint
  simp only [Footprint.makes_add, Footprint.makes_sum, complQueries, add_zero, Multiset.map_map]
  refine Multiset.sum_eq_zero fun x member => ?_
  obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨z, inStep, w, inRest, rfl⟩ := mem_rows_cons.mp (Multiset.mem_of_mem_filter inFilter)
  obtain ⟨o, -, τ, -, rfl⟩ := mem_stepRows_take.mp inStep
  rw [rows_done] at inRest
  simp only [instTemplate, List.mapM_nil, Option.pure_def, Multiset.mem_singleton] at inRest
  subst inRest
  simp [footprintOf_cons]

end Vacuous

/-! ## Controls -/

namespace Controls

/-- **The source `unique` is not the library's `unique`.** Two occurrences of one atom `a`: the
library's deduplication leaves one answer; the source has no row, because the region holds two
occurrences. -/
theorem unique_vs_dedup :
    ((labels (fun _ : ℕ => (0 : ℕ)) ({0, 1} : Finset ℕ)).dedup = {0}) ∧
      ¬ HasRow (constLayer (V := ℕ) (· = ·) ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩)
        (constMatcher (· = ·)) (fun _ : ℕ => (0 : ℕ)) {0, 1} (takeUnique 0) := by
  refine ⟨by decide, fun has => ?_⟩
  have := (hasRow_takeUnique_iff (V := ℕ) (E := (· = ·)) (label := fun _ : ℕ => (0 : ℕ))
    (S := ({0, 1} : Finset ℕ)) (a := 0)
    (equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩)).mp has
  revert this
  decide

/-- **With one occurrence the two agree**: one answer, one row. -/
theorem unique_one :
    ((labels (fun _ : ℕ => (0 : ℕ)) ({0} : Finset ℕ)).dedup = {0}) ∧
      HasRow (constLayer (V := ℕ) (· = ·) ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩)
        (constMatcher (· = ·)) (fun _ : ℕ => (0 : ℕ)) {0} (takeUnique 0) := by
  refine ⟨by decide, ?_⟩
  exact (hasRow_takeUnique_iff (V := ℕ) (E := (· = ·)) (label := fun _ : ℕ => (0 : ℕ))
    (S := ({0} : Finset ℕ)) (a := 0)
    (equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩)).mpr (by decide)

/-- Values of the `case` example: `2`, `(- 3 1)`, and `(from v)`. -/
inductive CVal where
  | two
  | minus31
  | from_ (v : CVal)
  deriving DecidableEq, Repr

/-- Patterns: `(from $w)`, or a literal. -/
inductive CPat where
  | fromVar
  | lit (v : CVal)
  deriving DecidableEq, Repr

/-- Evaluation of the arithmetic value. -/
def CVal.eval : CVal → CVal
  | .minus31 => .two
  | v => v

/-- **The data layer**: a bound value is substituted as it is. -/
def dataLayer : TermLayer ℕ CVal CPat where
  E := (· = ·)
  equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  vars := fun
    | .fromVar => {0}
    | .lit _ => ∅
  inst := fun σ p => match p with
    | .fromVar => (σ 0).map CVal.from_
    | .lit v => some v
  inst_bound := by intro σ p; cases p <;> simp
  inst_local := by
    intro σ τ p same
    cases p with
    | fromVar => simp [same 0 (by simp)]
    | lit v => rfl
  inst_congr := by
    intro σ τ p same
    cases p with
    | fromVar =>
        have := same 0 (by simp)
        change Option.Rel (· = ·) ((σ 0).map CVal.from_) ((τ 0).map CVal.from_)
        generalize σ 0 = a at this ⊢
        generalize τ 0 = b at this ⊢
        cases this with
        | none => exact Option.Rel.none
        | some h => subst h; exact Option.Rel.some rfl
    | lit v => exact Option.Rel.some rfl

/-- **The evaluating layer**: a bound value is evaluated before it is substituted. -/
def evalLayer : TermLayer ℕ CVal CPat where
  E := (· = ·)
  equivalence := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩
  vars := dataLayer.vars
  inst := fun σ p => dataLayer.inst (fun k => (σ k).map CVal.eval) p
  inst_bound := by intro σ p; cases p <;> simp [dataLayer]
  inst_local := by
    intro σ τ p same
    cases p with
    | fromVar => simp [dataLayer, same 0 (by simp [dataLayer])]
    | lit v => rfl
  inst_congr := by
    intro σ τ p same
    cases p with
    | fromVar =>
        have := same 0 (by simp [dataLayer])
        change Option.Rel (· = ·) (((σ 0).map CVal.eval).map CVal.from_)
          (((τ 0).map CVal.eval).map CVal.from_)
        generalize σ 0 = a at this ⊢
        generalize τ 0 = b at this ⊢
        cases this with
        | none => exact Option.Rel.none
        | some h => subst h; exact Option.Rel.some rfl
    | lit v => exact Option.Rel.some rfl

/-- `$w` bound to `(- 3 1)`. -/
def boundMinus : Subst ℕ CVal := fun k => if k = 0 then some .minus31 else none

/-- **The two readings of `(case v (((from $w) …) …))` with `$w = (- 3 1)`**: the evaluating layer
matches `(from 2)` and not `(from (- 3 1))`; the data layer the other way round. These are the
answers of the opt PeTTa lane and of SWI-PeTTa on the same program. -/
theorem evaluating_instantiation :
    evalLayer.Solves boundMinus .fromVar (.from_ .two) ∧
      ¬ evalLayer.Solves boundMinus .fromVar (.from_ .minus31) ∧
      ¬ dataLayer.Solves boundMinus .fromVar (.from_ .two) ∧
      dataLayer.Solves boundMinus .fromVar (.from_ .minus31) := by
  refine ⟨⟨_, rfl, rfl⟩, ?_, ?_, ⟨_, rfl, rfl⟩⟩ <;>
  · rintro ⟨u, inst, same⟩
    simp [evalLayer, dataLayer, boundMinus, CVal.eval] at inst
    subst inst
    cases same

/-- **The evaluating answer is not a step of the data layer**: a lane that evaluates bound values
in a `case` pattern answers, at `(from 2)`, what no step of its own data layer gives. -/
theorem evaluating_unsound_for_data :
    evalLayer.Step boundMinus .fromVar (.from_ .two) boundMinus ∧
      ¬ dataLayer.Step boundMinus .fromVar (.from_ .two) boundMinus :=
  ⟨⟨Extends.refl _, fun _ _ => rfl, evaluating_instantiation.1⟩,
    fun step => evaluating_instantiation.2.2.1 step.solves⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.LaneSpecializations
