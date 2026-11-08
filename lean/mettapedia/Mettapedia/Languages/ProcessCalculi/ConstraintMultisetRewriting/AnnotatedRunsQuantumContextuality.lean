import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantum

/-!
# When classical grades suffice: global sections, and a family that has none

## Classical grades are global sections

A measurement scenario has global assignments `G`, contexts, and a restriction of each global
assignment to the outcomes it gives in a context. An empirical model is a table of outcome
weights in every context.

* A **global section** (Abramsky and Brandenburger, "The sheaf-theoretic structure of non-locality
  and contextuality", New J. Phys. 13 (2011) 113036) is a distribution on global assignments whose
  marginal in each context is that context's table.
* A **classical-grade model over runs** has finitely many runs with probability grades. Each run
  records an outcome for every measurement, and each table aggregates the grades of the runs over
  their recorded outcomes.
* **The two are the same** (`classicalModel_iff_globalSection`): pushing the grades forward along
  the records gives a global section, and a global section is a model whose runs are the global
  assignments.

## Mermin's family has no global section; two unrecorded histories reproduce it

* Three parties measure `X` or `Y` in the contexts `XXX`, `XYY`, `YXY` and `YYX`. Mermin's table
  is uniform over the outcomes whose product is `+1` in `XXX` and `-1` in the others.
* **No global assignment is consistent with it** (`exists_forbidden`): the four parities multiply
  to `-1`, while each outcome of a global assignment appears in two contexts. So there is no global
  section (`mermin_no_global_section`) and no classical-grade model (`mermin_no_classical_model`).
* **The amplitude model**: two histories, `|000⟩` and `|111⟩`, reach every outcome. The first has
  amplitude `1`; the second has the product of `⟨o|1⟩` over the parties, which is `±1` for `X` and
  `∓ i` for `Y`. Added coherently, allowed outcomes have Born weight `4` and forbidden ones `0`
  (`ghzWeight_eq`), and normalized in each context this is Mermin's table
  (`ghz_reproduces_mermin`).

## Records destroy the contextuality; phase carries it

* **Recorded histories read classically**: added incoherently, every outcome has weight `2`
  (`recordedWeight_eq`), the table is uniform (`recorded_table`), and it has a global section
  (`recorded_has_global_section`).
* **A probability forgets phase** (`phase_blind_twin`): replacing the `Y` factors by real signs keeps
  every history's Born weight, and changes a coherent weight from `0` to `4`.
-/

set_option autoImplicit false

open scoped QuadraticAlgebra

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace AmplitudeRuns

namespace Contextuality

open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born born_formula)

/-! ## Global sections and classical-grade models -/

section Scenario

variable {G Ctx L : Type} [Fintype G] [DecidableEq L]

/-- **The marginal of a distribution on global assignments** in a context. -/
def marginal (restrict : Ctx → G → L) (d : G → ℚ) (c : Ctx) (ℓ : L) : ℚ :=
  ∑ g ∈ Finset.univ.filter (fun g => restrict c g = ℓ), d g

/-- **A global section** of an empirical model: a distribution on global assignments whose
marginal in every context is that context's table. -/
def GlobalSection (restrict : Ctx → G → L) (table : Ctx → L → ℚ) : Prop :=
  ∃ d : G → ℚ, (∀ g, 0 ≤ d g) ∧ ∑ g, d g = 1 ∧ ∀ c ℓ, marginal restrict d c ℓ = table c ℓ

/-- **A classical-grade model over runs**: finitely many runs with probability grades, each
recording an outcome for every measurement, whose tables aggregate the grades of the runs over
their recorded outcomes. -/
def ClassicalModel (restrict : Ctx → G → L) (table : Ctx → L → ℚ) : Prop :=
  ∃ (R : Type) (_ : Fintype R) (grade : R → ℚ) (record : R → G), (∀ r, 0 ≤ grade r) ∧
    ∑ r, grade r = 1 ∧
    ∀ c ℓ, ∑ r ∈ Finset.univ.filter (fun r => restrict c (record r) = ℓ), grade r = table c ℓ

/-- **Classical grades over runs are global sections.** -/
theorem classicalModel_iff_globalSection [DecidableEq G] (restrict : Ctx → G → L)
    (table : Ctx → L → ℚ) : ClassicalModel restrict table ↔ GlobalSection restrict table := by
  constructor
  · rintro ⟨R, _, grade, record, nonneg, total, tables⟩
    refine ⟨fun g => ∑ r ∈ Finset.univ.filter (fun r => record r = g), grade r,
      fun g => Finset.sum_nonneg fun r _ => nonneg r, ?_, fun c ℓ => ?_⟩
    · rw [← total]
      exact Finset.sum_fiberwise_of_maps_to (fun r _ => Finset.mem_univ (record r)) grade
    · rw [← tables c ℓ]
      unfold marginal
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ.filter fun r => restrict c (record r) = ℓ)
        (t := Finset.univ.filter fun g => restrict c g = ℓ) (g := record) ?_ grade]
      · refine Finset.sum_congr rfl fun g member => ?_
        rw [Finset.filter_filter]
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro same
          refine ⟨?_, same⟩
          rw [same]
          exact (Finset.mem_filter.mp member).2
        · exact fun both => both.2
      · intro r member
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member ⊢
        exact member
  · rintro ⟨d, nonneg, total, marginals⟩
    exact ⟨G, inferInstance, d, id, nonneg, total, fun c ℓ => marginals c ℓ⟩

end Scenario

/-! ## Mermin's family -/

/-- Mermin's four contexts. -/
inductive Context where
  | xxx
  | xyy
  | yxy
  | yyx
deriving DecidableEq

/-- A global assignment: each party's outcomes for the settings `X` and `Y`; `true` is `-1`. -/
abbrev Hidden := (Bool × Bool) × (Bool × Bool) × (Bool × Bool)

/-- The outcomes of the three parties in one context; `true` is `-1`. -/
abbrev Outcome := Bool × Bool × Bool

/-- The settings of a context, `false` for `X` and `true` for `Y`. -/
def settings : Context → Bool × Bool × Bool
  | .xxx => (false, false, false)
  | .xyy => (false, true, true)
  | .yxy => (true, false, true)
  | .yyx => (true, true, false)

/-- A party's outcome for a setting. -/
def pick (pair : Bool × Bool) (setting : Bool) : Bool := if setting then pair.2 else pair.1

/-- **The outcomes a global assignment gives in a context.** -/
def merminRestrict (c : Context) (g : Hidden) : Outcome :=
  (pick g.1 (settings c).1, pick g.2.1 (settings c).2.1, pick g.2.2 (settings c).2.2)

/-- The parity a context requires of the product of its outcomes: `+1` for `XXX`, `-1` for the
others. -/
def requiredParity : Context → Bool
  | .xxx => false
  | _ => true

/-- The outcomes a context allows. -/
def allowed (c : Context) (o : Outcome) : Bool := (o.1 ^^ o.2.1 ^^ o.2.2) == requiredParity c

/-- **Mermin's table**: uniform over the allowed outcomes of each context. -/
def mermin (c : Context) (o : Outcome) : ℚ := if allowed c o then 1 / 4 else 0

/-- Whether a global assignment is consistent with all four contexts. -/
def consistentWith (g : Hidden) : Bool :=
  allowed .xxx (merminRestrict .xxx g) && allowed .xyy (merminRestrict .xyy g) &&
    allowed .yxy (merminRestrict .yxy g) && allowed .yyx (merminRestrict .yyx g)

/-- **No global assignment is consistent with Mermin's parities.** -/
theorem mermin_parity (g : Hidden) : consistentWith g = false := by
  rcases g with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩, ⟨x₃, y₃⟩⟩
  cases x₁ <;> cases y₁ <;> cases x₂ <;> cases y₂ <;> cases x₃ <;> cases y₃ <;> rfl

/-- **Strong contextuality**: every global assignment gives a forbidden outcome in some context. -/
theorem exists_forbidden (g : Hidden) : ∃ c, allowed c (merminRestrict c g) = false := by
  have parity := mermin_parity g
  unfold consistentWith at parity
  cases h₀ : allowed .xxx (merminRestrict .xxx g)
  · exact ⟨.xxx, h₀⟩
  cases h₁ : allowed .xyy (merminRestrict .xyy g)
  · exact ⟨.xyy, h₁⟩
  cases h₂ : allowed .yxy (merminRestrict .yxy g)
  · exact ⟨.yxy, h₂⟩
  cases h₃ : allowed .yyx (merminRestrict .yyx g)
  · exact ⟨.yyx, h₃⟩
  rw [h₀, h₁, h₂, h₃] at parity
  exact absurd parity (by decide)

/-- **Mermin's family has no global section.** -/
theorem mermin_no_global_section : ¬ GlobalSection merminRestrict mermin := by
  rintro ⟨d, nonneg, total, marginals⟩
  have zero : ∀ g, d g = 0 := by
    intro g
    obtain ⟨c, forbidden⟩ := exists_forbidden g
    have bound : d g ≤ marginal merminRestrict d c (merminRestrict c g) :=
      Finset.single_le_sum (fun g' _ => nonneg g')
        (Finset.mem_filter.mpr ⟨Finset.mem_univ g, rfl⟩)
    rw [marginals, mermin, forbidden] at bound
    exact le_antisymm (by simpa using bound) (nonneg g)
  rw [Finset.sum_eq_zero fun g _ => zero g] at total
  exact zero_ne_one total

/-- **Mermin's family has no classical-grade model over runs.** -/
theorem mermin_no_classical_model : ¬ ClassicalModel merminRestrict mermin := fun model =>
  mermin_no_global_section ((classicalModel_iff_globalSection merminRestrict mermin).mp model)

/-! ## Two unrecorded histories reproduce it -/

/-- **The second history's amplitude for one party**, `⟨o|1⟩` in the measured basis: the outcomes
of `X` are `|0⟩ ± |1⟩`, giving `±1`, and those of `Y` are `|0⟩ ± i|1⟩`, giving `∓ i`. The first
history, `|000⟩`, gives every outcome the amplitude `1`. -/
def factor : Bool → Bool → Amplitude
  | false, false => 1
  | false, true => -1
  | true, false => -unitI
  | true, true => unitI

/-- **The amplitude of the second history, `|111⟩`, for an outcome**: the product of the parties'
factors. -/
def secondHistory (c : Context) (o : Outcome) : Amplitude :=
  factor (settings c).1 o.1 * factor (settings c).2.1 o.2.1 * factor (settings c).2.2 o.2.2

/-- **The two histories that reach an outcome**: `|000⟩` with amplitude `1`, and `|111⟩`. -/
def histories (c : Context) (o : Outcome) : Multiset Amplitude := {1, secondHistory c o}

/-- **The Born weight of an outcome**: its two histories added coherently. -/
def ghzWeight (c : Context) (o : Outcome) : ℚ := born (coherent (histories c o))

/-- **The weight with the histories recorded**: their Born weights added. -/
def recordedWeight (c : Context) (o : Outcome) : ℚ := incoherent (histories c o)

theorem ghzWeight_two_paths (c : Context) (o : Outcome) :
    ghzWeight c o = born (1 + secondHistory c o) := by
  unfold ghzWeight histories
  rw [coherent_pair]

theorem recordedWeight_two_paths (c : Context) (o : Outcome) :
    recordedWeight c o = born 1 + born (secondHistory c o) := by
  unfold recordedWeight histories
  rw [incoherent_pair]

/-- Every factor has Born weight `1`. -/
theorem born_factor (setting outcome : Bool) : born (factor setting outcome) = 1 := by
  cases setting <;> cases outcome <;> simp [factor, born_neg, born_unitI]

/-- **Each history alone has Born weight `1`**: the Born weight is multiplicative. -/
theorem born_secondHistory (c : Context) (o : Outcome) : born (secondHistory c o) = 1 := by
  simp only [secondHistory, map_mul, born_factor, mul_one]

/-- **Allowed outcomes have Born weight `4`, forbidden ones `0`.** -/
theorem ghzWeight_eq (c : Context) (o : Outcome) :
    ghzWeight c o = if allowed c o then 4 else 0 := by
  rw [ghzWeight_two_paths]
  rcases o with ⟨o₁, o₂, o₃⟩
  cases c <;> cases o₁ <;> cases o₂ <;> cases o₃ <;>
    norm_num [secondHistory, factor, settings, allowed, requiredParity, born_formula, unitI]

/-- The total Born weight of a context is `16`. -/
theorem ghz_total (c : Context) : ∑ o : Outcome, ghzWeight c o = 16 := by
  simp only [ghzWeight_eq, Fintype.sum_prod_type, Fintype.sum_bool]
  cases c <;> norm_num [allowed, requiredParity]

/-- **The two-history amplitude model reproduces Mermin's family.** -/
theorem ghz_reproduces_mermin (c : Context) (o : Outcome) :
    ghzWeight c o / ∑ o' : Outcome, ghzWeight c o' = mermin c o := by
  rw [ghz_total, ghzWeight_eq]
  unfold mermin
  by_cases allowedHere : allowed c o = true
  · rw [if_pos allowedHere, if_pos allowedHere]
    norm_num
  · rw [if_neg allowedHere, if_neg allowedHere]
    norm_num

/-! ## Records destroy the contextuality -/

/-- **Recorded, every outcome has the incoherent weight `2`.** -/
theorem recordedWeight_eq (c : Context) (o : Outcome) : recordedWeight c o = 2 := by
  rw [recordedWeight_two_paths, born_one, born_secondHistory]
  norm_num

/-- The uniform table: every outcome of a context has weight `1/8`. -/
def uniform (_ : Context) (_ : Outcome) : ℚ := 1 / 8

/-- **Recorded, the table is uniform.** -/
theorem recorded_table (c : Context) (o : Outcome) :
    recordedWeight c o / ∑ o' : Outcome, recordedWeight c o' = uniform c o := by
  simp only [recordedWeight_eq, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_bool, uniform]
  norm_num

/-- Every outcome of a context comes from eight global assignments. -/
theorem fiber_card (c : Context) (o : Outcome) :
    (Finset.univ.filter fun g : Hidden => merminRestrict c g = o).card = 8 := by
  rcases o with ⟨o₁, o₂, o₃⟩
  cases c <;> cases o₁ <;> cases o₂ <;> cases o₃ <;> decide

/-- **With the histories recorded, Mermin's contexts have a global section**: the uniform
distribution on the sixty-four global assignments. -/
theorem recorded_has_global_section : GlobalSection merminRestrict uniform := by
  refine ⟨fun _ => 1 / 64, fun _ => by norm_num, ?_, fun c o => ?_⟩
  · show ∑ _g : Hidden, (1 / 64 : ℚ) = 1
    rw [Finset.sum_const, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
    norm_num
  · unfold marginal uniform
    show ∑ _g ∈ Finset.univ.filter (fun g : Hidden => merminRestrict c g = o), (1 / 64 : ℚ) =
      1 / 8
    rw [Finset.sum_const, fiber_card, nsmul_eq_mul]
    norm_num

/-- **With the histories recorded there is a classical-grade model over runs.** -/
theorem recorded_classical_model : ClassicalModel merminRestrict uniform :=
  (classicalModel_iff_globalSection merminRestrict uniform).mpr recorded_has_global_section

/-- **Records destroy contextuality.** The same two histories, read coherently, reproduce
Mermin's family, which has no global section; read with the histories recorded, they give the
uniform table, which has one. -/
theorem records_destroy_contextuality :
    (∀ c o, ghzWeight c o / ∑ o' : Outcome, ghzWeight c o' = mermin c o) ∧
      ¬ GlobalSection merminRestrict mermin ∧
      (∀ c o, recordedWeight c o / ∑ o' : Outcome, recordedWeight c o' = uniform c o) ∧
      GlobalSection merminRestrict uniform :=
  ⟨ghz_reproduces_mermin, mermin_no_global_section, recorded_table, recorded_has_global_section⟩

/-! ## A probability forgets phase -/

/-- The phase-blind twin of a factor: the `Y` factors replaced by the real signs of the same Born
weight. -/
def blindFactor (_ : Bool) (outcome : Bool) : Amplitude := if outcome then -1 else 1

/-- The second history of the phase-blind twin. -/
def blindSecond (c : Context) (o : Outcome) : Amplitude :=
  blindFactor (settings c).1 o.1 * blindFactor (settings c).2.1 o.2.1 *
    blindFactor (settings c).2.2 o.2.2

/-- The histories of the phase-blind twin. -/
def blindHistories (c : Context) (o : Outcome) : Multiset Amplitude := {1, blindSecond c o}

theorem born_blindFactor (setting outcome : Bool) : born (blindFactor setting outcome) = 1 := by
  cases outcome <;> simp [blindFactor, born_neg]

theorem born_blindSecond (c : Context) (o : Outcome) : born (blindSecond c o) = 1 := by
  simp only [blindSecond, map_mul, born_blindFactor, mul_one]

/-- **A phase-blind readout does not preserve interference.** Every history of the model and of
its phase-blind twin has Born weight `1`, so their histories have the same Born weights in every
context and outcome; in the context `XYY` with every outcome `+1`, their coherent weights are `0`
and `4`. -/
theorem phase_blind_twin :
    (∀ c o, (histories c o).map born = (blindHistories c o).map born) ∧
      ghzWeight .xyy (false, false, false) = 0 ∧
      born (coherent (blindHistories .xyy (false, false, false))) = 4 := by
  refine ⟨fun c o => ?_, ?_, ?_⟩
  · simp only [histories, blindHistories, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, born_secondHistory, born_blindSecond]
  · rw [ghzWeight_eq]
    simp [allowed, requiredParity]
  · rw [blindHistories, coherent_pair]
    norm_num [blindSecond, blindFactor, settings, born_formula]

end Contextuality

end AmplitudeRuns

open AmplitudeRuns.Contextuality

#print axioms classicalModel_iff_globalSection
#print axioms mermin_parity
#print axioms exists_forbidden
#print axioms mermin_no_global_section
#print axioms mermin_no_classical_model
#print axioms ghzWeight_two_paths
#print axioms recordedWeight_two_paths
#print axioms born_factor
#print axioms born_secondHistory
#print axioms ghzWeight_eq
#print axioms ghz_total
#print axioms ghz_reproduces_mermin
#print axioms recordedWeight_eq
#print axioms recorded_table
#print axioms fiber_card
#print axioms recorded_has_global_section
#print axioms recorded_classical_model
#print axioms records_destroy_contextuality
#print axioms born_blindSecond
#print axioms phase_blind_twin

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
