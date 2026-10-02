import Mettapedia.Logic.TheoryModel.Forgetting
import Mettapedia.Cybernetics.DistinctionCalculus.Ledger

/-!
# Hosting up to ε

Faithful hosting (`HostsFaithfully`) is exact: a universe of structures
validates no sentence beyond the consequences of the theory. This module grades
it. A finitely supported weighting `ν` of sentences, positive on its support,
measures how far two structures are apart by the `ν`-mass of the tested
sentences on which they disagree (`WithinTest`); this is a pseudometric on
structures, and for a probability weighting and decidable satisfaction it is a
metric tolerance of the distinction calculus whose zero kernel is the
indistinguishability `indistinguishable Sat ν.support` of the observer–language
connection (`testTolerance_indistinguishable_iff`).

* **ε-hosting.** `U` ε-hosts `T` when every model of `T` has a model of `T` in
  `U` within `ε` (`EpsHosts`). It is monotone in the universe and in `ε`, and
  errors add along chains of universes (`EpsHostsFrom.trans`).
* **Leak bound.** A sentence leaks when `U` validates it and `T` does not
  entail it. For every model `m` of `T`, the tested sentences that leak and
  that `m` refutes have `ν`-mass at most `ε` (`leak_mass_le`); in particular a
  single leaked tested sentence refuted by a model forces `ε ≥ ν(φ)`.
* **ε = 0.** Zero hosting is exactly the existence of twins agreeing on the
  tested sentences (`zeroHosts_iff_twins`), and it makes the universe faithful
  on the tested sentences (`entails_of_zeroHosts`); with full support it is
  faithful hosting (`hostsFaithfully_of_zeroHosts`). The twin criterion
  `hostsFaithfully_of_twins` factors through it (`zeroHosts_of_twins`).

The controls module shows that faithful hosting does not imply zero hosting,
that zero hosting on some sentences leaves leaks elsewhere, and grades the
collapsing comorphism and the identity-proof ladder.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel

open Set

universe uStr uSent

/-! ## Weightings of sentences -/

/-- A finitely supported weighting of sentences, positive on its support. -/
structure SentenceWeighting (Sent : Type uSent) where
  support : Finset Sent
  weight : Sent → ℚ
  weight_pos : ∀ φ ∈ support, 0 < weight φ

namespace SentenceWeighting

variable {Sent : Type uSent} (ν : SentenceWeighting Sent)

/-- The mass of a finite set of sentences. -/
def mass (D : Finset Sent) : ℚ :=
  ∑ φ ∈ D, ν.weight φ

theorem mass_nonneg {D : Finset Sent} (inside : D ⊆ ν.support) : 0 ≤ ν.mass D :=
  Finset.sum_nonneg fun φ member => (ν.weight_pos φ (inside member)).le

theorem mass_mono {D D' : Finset Sent} (inside : D' ⊆ ν.support) (included : D ⊆ D') :
    ν.mass D ≤ ν.mass D' :=
  Finset.sum_le_sum_of_subset_of_nonneg included fun φ member _ =>
    (ν.weight_pos φ (inside member)).le

theorem mass_union_le [DecidableEq Sent] {D D' : Finset Sent} (inside : D ⊆ ν.support) :
    ν.mass (D ∪ D') ≤ ν.mass D + ν.mass D' := by
  unfold mass
  rw [← Finset.sum_union_inter]
  have : 0 ≤ ∑ φ ∈ D ∩ D', ν.weight φ :=
    Finset.sum_nonneg fun φ member => (ν.weight_pos φ (inside (Finset.mem_inter.mp member).1)).le
  linarith

/-- A set of zero mass inside the support is empty. -/
theorem eq_empty_of_mass_nonpos {D : Finset Sent} (inside : D ⊆ ν.support)
    (zero : ν.mass D ≤ 0) : D = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro φ member
  have single : ν.weight φ ≤ ν.mass D :=
    Finset.single_le_sum (f := ν.weight) (fun ψ member' => (ν.weight_pos ψ (inside member')).le)
      member
  linarith [ν.weight_pos φ (inside member)]

theorem weight_le_mass {D : Finset Sent} (inside : D ⊆ ν.support) {φ : Sent} (member : φ ∈ D) :
    ν.weight φ ≤ ν.mass D :=
  Finset.single_le_sum (f := ν.weight) (fun ψ member' => (ν.weight_pos ψ (inside member')).le)
    member

end SentenceWeighting

/-! ## The testing pseudometric -/

section Testing

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)
  (ν : SentenceWeighting Sent)

/-- `m` and `m'` agree on the tested sentences outside a set of `ν`-mass at
most `ε`. -/
def WithinTest (m m' : Str) (ε : ℚ) : Prop :=
  ∃ D ⊆ ν.support, (∀ φ ∈ ν.support, φ ∉ D → (Sat m φ ↔ Sat m' φ)) ∧ ν.mass D ≤ ε

variable {Sat ν}

theorem withinTest_refl (m : Str) : WithinTest Sat ν m m 0 :=
  ⟨∅, Finset.empty_subset _, fun _ _ _ => Iff.rfl, by simp [SentenceWeighting.mass]⟩

theorem WithinTest.symm {m m' : Str} {ε : ℚ} (within : WithinTest Sat ν m m' ε) :
    WithinTest Sat ν m' m ε := by
  obtain ⟨D, inside, agree, small⟩ := within
  exact ⟨D, inside, fun φ member outside => (agree φ member outside).symm, small⟩

/-- **Triangle law**: tested disagreements add. -/
theorem WithinTest.trans [DecidableEq Sent] {m m' m'' : Str} {ε δ : ℚ}
    (first : WithinTest Sat ν m m' ε)
    (second : WithinTest Sat ν m' m'' δ) : WithinTest Sat ν m m'' (ε + δ) := by
  obtain ⟨D, inside, agree, small⟩ := first
  obtain ⟨D', inside', agree', small'⟩ := second
  refine ⟨D ∪ D', Finset.union_subset inside inside', fun φ member outside => ?_,
    (ν.mass_union_le inside).trans (add_le_add small small')⟩
  rw [Finset.mem_union, not_or] at outside
  exact (agree φ member outside.1).trans (agree' φ member outside.2)

theorem WithinTest.mono {m m' : Str} {ε δ : ℚ} (within : WithinTest Sat ν m m' ε) (le : ε ≤ δ) :
    WithinTest Sat ν m m' δ := by
  obtain ⟨D, inside, agree, small⟩ := within
  exact ⟨D, inside, agree, small.trans le⟩

/-- Zero tested distance is agreement on every tested sentence. -/
theorem withinTest_zero_iff {m m' : Str} :
    WithinTest Sat ν m m' 0 ↔ ∀ φ ∈ ν.support, (Sat m φ ↔ Sat m' φ) := by
  constructor
  · rintro ⟨D, inside, agree, small⟩ φ member
    have empty := ν.eq_empty_of_mass_nonpos inside small
    exact agree φ member (by rw [empty]; exact Finset.notMem_empty φ)
  · intro agree
    exact ⟨∅, Finset.empty_subset _, fun φ member _ => agree φ member,
      by simp [SentenceWeighting.mass]⟩

/-- Zero tested distance is W3's indistinguishability by the tested sentences. -/
theorem withinTest_zero_iff_indistinguishable {m m' : Str} :
    WithinTest Sat ν m m' 0 ↔ indistinguishable Sat (↑ν.support : Set Sent) m m' :=
  withinTest_zero_iff.trans
    ⟨fun agree _ member => agree _ member, fun agree _ member => agree member⟩

/-! ### The decidable readout -/

variable [DecidableEq Sent] [∀ m φ, Decidable (Sat m φ)]

variable (Sat ν) in
/-- The `ν`-mass of the tested sentences on which `m` and `m'` disagree. -/
def testDistance (m m' : Str) : ℚ :=
  ν.mass (ν.support.filter fun φ => ¬ (Sat m φ ↔ Sat m' φ))

theorem withinTest_iff_testDistance_le {m m' : Str} {ε : ℚ} :
    WithinTest Sat ν m m' ε ↔ testDistance Sat ν m m' ≤ ε := by
  constructor
  · rintro ⟨D, inside, agree, small⟩
    refine le_trans (ν.mass_mono inside ?_) small
    intro φ member
    rw [Finset.mem_filter] at member
    by_contra outside
    exact member.2 (agree φ member.1 outside)
  · intro small
    refine ⟨_, Finset.filter_subset _ _, fun φ member outside => ?_, small⟩
    rw [Finset.mem_filter, not_and, Decidable.not_not] at outside
    exact outside member

omit [DecidableEq Sent] in
theorem testDistance_nonneg (m m' : Str) : 0 ≤ testDistance Sat ν m m' :=
  ν.mass_nonneg (Finset.filter_subset _ _)

theorem testDistance_self (m : Str) : testDistance Sat ν m m = 0 :=
  le_antisymm (withinTest_iff_testDistance_le.mp (withinTest_refl m)) (testDistance_nonneg m m)

omit [DecidableEq Sent] in
theorem testDistance_symm (m m' : Str) : testDistance Sat ν m m' = testDistance Sat ν m' m := by
  unfold testDistance
  congr 1
  ext φ
  simp only [Finset.mem_filter]
  exact and_congr Iff.rfl (not_congr ⟨Iff.symm, Iff.symm⟩)

theorem testDistance_triangle (m m' m'' : Str) :
    testDistance Sat ν m m'' ≤ testDistance Sat ν m m' + testDistance Sat ν m' m'' :=
  withinTest_iff_testDistance_le.mp
    ((withinTest_iff_testDistance_le.mpr le_rfl).trans (withinTest_iff_testDistance_le.mpr le_rfl))

variable (Sat) in
/-- For a probability weighting (total tested mass at most one), the testing
pseudometric is a metric tolerance of the distinction calculus. -/
def testTolerance (total : ν.mass ν.support ≤ 1) :
    Mettapedia.Cybernetics.DistinctionCalculus.Tolerance Str where
  similarity m m' := 1 - testDistance Sat ν m m'
  nonnegative m m' := sub_nonneg.mpr
    ((ν.mass_mono (Finset.Subset.refl _) (Finset.filter_subset _ _)).trans total)
  bounded m m' := by linarith [testDistance_nonneg (Sat := Sat) (ν := ν) m m']
  reflexive m := by rw [testDistance_self, sub_zero]
  symmetric m m' := by rw [testDistance_symm]

theorem testTolerance_distance (total : ν.mass ν.support ≤ 1) (m m' : Str) :
    (testTolerance Sat total).distance m m' = testDistance Sat ν m m' := by
  simp [Mettapedia.Cybernetics.DistinctionCalculus.Tolerance.distance, testTolerance]

theorem testTolerance_metric (total : ν.mass ν.support ≤ 1) :
    (testTolerance Sat total).Metric := by
  intro m m' m''
  rw [testTolerance_distance, testTolerance_distance, testTolerance_distance]
  exact testDistance_triangle m m' m''

/-- **The zero kernel of the testing tolerance is W3's indistinguishability by
the tested sentences**: the graded observer refines the upper adjoint of the
observer–language connection. -/
theorem testTolerance_indistinguishable_iff (total : ν.mass ν.support ≤ 1) {m m' : Str} :
    (testTolerance Sat total).Indistinguishable m m' ↔
      indistinguishable Sat (↑ν.support : Set Sent) m m' := by
  unfold Mettapedia.Cybernetics.DistinctionCalculus.Tolerance.Indistinguishable
  rw [testTolerance_distance, ← withinTest_zero_iff_indistinguishable]
  constructor
  · intro zero
    exact withinTest_iff_testDistance_le.mpr zero.le
  · intro within
    exact le_antisymm (withinTest_iff_testDistance_le.mp within) (testDistance_nonneg m m')

end Testing

/-! ## ε-hosting -/

section Hosting

variable {Str : Type uStr} {Sent : Type uSent} (Sat : Str → Sent → Prop)
  (ν : SentenceWeighting Sent)

/-- Every model of `T` in `V` has a model of `T` in `U` within `ε`. -/
def EpsHostsFrom (V U : Set Str) (T : Set Sent) (ε : ℚ) : Prop :=
  ∀ ⦃m⦄, m ∈ modelsIn Sat V T → ∃ m' ∈ modelsIn Sat U T, WithinTest Sat ν m m' ε

/-- **`U` hosts `T` up to `ε`**: every model of `T` has a model of `T` in `U`
within `ε`. -/
def EpsHosts (U : Set Str) (T : Set Sent) (ε : ℚ) : Prop :=
  EpsHostsFrom Sat ν univ U T ε

variable {Sat ν}

theorem epsHosts_iff {U : Set Str} {T : Set Sent} {ε : ℚ} :
    EpsHosts Sat ν U T ε ↔
      ∀ ⦃m⦄, m ∈ models Sat T → ∃ m' ∈ modelsIn Sat U T, WithinTest Sat ν m m' ε :=
  ⟨fun hosts m model => hosts ⟨mem_univ m, model⟩, fun hosts _ member => hosts member.2⟩

/-- **A larger universe hosts at least as well.** -/
theorem EpsHostsFrom.mono_universe {V U U' : Set Str} {T : Set Sent} {ε : ℚ}
    (hosts : EpsHostsFrom Sat ν V U T ε) (included : U ⊆ U') : EpsHostsFrom Sat ν V U' T ε :=
  fun _ member => let ⟨m', hosted, within⟩ := hosts member
    ⟨m', modelsIn_mono included T hosted, within⟩

theorem EpsHosts.mono_universe {U U' : Set Str} {T : Set Sent} {ε : ℚ}
    (hosts : EpsHosts Sat ν U T ε) (included : U ⊆ U') : EpsHosts Sat ν U' T ε :=
  EpsHostsFrom.mono_universe hosts included

theorem EpsHostsFrom.mono_eps {V U : Set Str} {T : Set Sent} {ε δ : ℚ}
    (hosts : EpsHostsFrom Sat ν V U T ε) (le : ε ≤ δ) : EpsHostsFrom Sat ν V U T δ :=
  fun _ member =>
    let ⟨m', hosted, within⟩ := hosts member
    ⟨m', hosted, within.mono le⟩

/-- **Hosting errors add along chains of universes.** -/
theorem EpsHostsFrom.trans [DecidableEq Sent] {V U W : Set Str} {T : Set Sent} {ε δ : ℚ}
    (first : EpsHostsFrom Sat ν V U T ε) (second : EpsHostsFrom Sat ν U W T δ) :
    EpsHostsFrom Sat ν V W T (ε + δ) := by
  intro m member
  obtain ⟨m', hosted, within⟩ := first member
  obtain ⟨m'', hosted', within'⟩ := second hosted
  exact ⟨m'', hosted', within.trans within'⟩

/-! ### The leak bound -/

/-- **Per-model leak bound.** For every model `m` of `T`, the tested sentences
that `U` validates and `m` refutes have `ν`-mass at most `ε`. Each of them is
a leak: `U` validates it, and `T` does not entail it since `m` refutes it. -/
theorem leak_mass_le [DecidableEq Sent] {U : Set Str} {T : Set Sent} {ε : ℚ}
    (hosts : EpsHosts Sat ν U T ε)
    {m : Str} (model : m ∈ models Sat T) {L : Finset Sent}
    (leaked : ∀ φ ∈ L, φ ∈ ν.support ∧ φ ∈ consequencesIn Sat U T ∧ ¬ Sat m φ) :
    ν.mass L ≤ ε := by
  obtain ⟨m', hosted, D, inside, agree, small⟩ := (epsHosts_iff.mp hosts) model
  refine le_trans (ν.mass_mono inside fun φ member => ?_) small
  obtain ⟨tested, validated, refuted⟩ := leaked φ member
  by_contra outside
  exact refuted ((agree φ tested outside).mpr (validated hosted))

/-- Each leaked tested sentence refuted by some model forces `ε ≥ ν(φ)`. -/
theorem weight_le_of_leak [DecidableEq Sent] {U : Set Str} {T : Set Sent} {ε : ℚ}
    (hosts : EpsHosts Sat ν U T ε)
    {φ : Sent} (tested : φ ∈ ν.support) (validated : φ ∈ consequencesIn Sat U T) {m : Str}
    (model : m ∈ models Sat T) (refuted : ¬ Sat m φ) : ν.weight φ ≤ ε := by
  have := leak_mass_le hosts model (L := {φ}) fun ψ member => by
    rw [Finset.mem_singleton] at member
    subst member
    exact ⟨tested, validated, refuted⟩
  simpa [SentenceWeighting.mass] using this

/-- A leaked tested sentence refuted by a model is an unentailed consequence of
the universe. -/
theorem not_entails_of_refuted {T : Set Sent} {φ : Sent} {m : Str} (model : m ∈ models Sat T)
    (refuted : ¬ Sat m φ) : ¬ Entails Sat T φ :=
  fun entailed => refuted (entailed model)

/-! ### Zero hosting -/

/-- **Zero hosting is the existence of twins on the tested sentences.** -/
theorem zeroHosts_iff_twins {U : Set Str} {T : Set Sent} :
    EpsHosts Sat ν U T 0 ↔
      ∀ ⦃m⦄, m ∈ models Sat T → ∃ m' ∈ modelsIn Sat U T, ∀ φ ∈ ν.support, (Sat m φ ↔ Sat m' φ) := by
  rw [epsHosts_iff]
  constructor
  · intro hosts m model
    obtain ⟨m', hosted, within⟩ := hosts model
    exact ⟨m', hosted, withinTest_zero_iff.mp within⟩
  · intro twins m model
    obtain ⟨m', hosted, agree⟩ := twins model
    exact ⟨m', hosted, withinTest_zero_iff.mpr agree⟩

/-- **Zero hosting is faithful on the tested sentences**: every tested sentence
the universe validates is entailed. -/
theorem entails_of_zeroHosts {U : Set Str} {T : Set Sent} (hosts : EpsHosts Sat ν U T 0)
    {φ : Sent} (tested : φ ∈ ν.support) (validated : φ ∈ consequencesIn Sat U T) :
    Entails Sat T φ := by
  intro m model
  obtain ⟨m', hosted, agree⟩ := zeroHosts_iff_twins.mp hosts model
  exact (agree φ tested).mpr (validated hosted)

/-- **With full support, zero hosting is faithful hosting.** -/
theorem hostsFaithfully_of_zeroHosts {U : Set Str} {T : Set Sent}
    (full : ∀ φ, φ ∈ ν.support) (hosts : EpsHosts Sat ν U T 0) : HostsFaithfully Sat U T :=
  hostsFaithfully_iff_subset.mpr fun φ validated => entails_of_zeroHosts hosts (full φ) validated

/-- **Twins give zero hosting for every weighting and every theory.** -/
theorem zeroHosts_of_twins {U : Set Str} (twin : ∀ m, ∃ m' ∈ U, ∀ φ, Sat m' φ ↔ Sat m φ)
    (T : Set Sent) : EpsHosts Sat ν U T 0 := by
  rw [zeroHosts_iff_twins]
  intro m model
  obtain ⟨m', hosted, equivalent⟩ := twin m
  exact ⟨m', ⟨hosted, fun ψ member => (equivalent ψ).mpr (model member)⟩,
    fun φ _ => (equivalent φ).symm⟩

/-- The twin criterion of faithful hosting, recovered through zero hosting for a
finite language. -/
theorem hostsFaithfully_of_twins_via_zeroHosts [Fintype Sent] {U : Set Str}
    (twin : ∀ m, ∃ m' ∈ U, ∀ φ, Sat m' φ ↔ Sat m φ) (T : Set Sent) : HostsFaithfully Sat U T :=
  hostsFaithfully_of_zeroHosts (ν := ⟨Finset.univ, fun _ => 1, fun _ _ => zero_lt_one⟩)
    (fun φ => Finset.mem_univ φ) (zeroHosts_of_twins twin T)

end Hosting

end Mettapedia.Logic.TheoryModel
