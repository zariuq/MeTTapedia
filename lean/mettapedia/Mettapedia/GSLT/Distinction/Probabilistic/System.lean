import Mettapedia.GSLT.Causality.WeightedObservers
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Probabilistic GSLTs, their support erasure, and Larsen–Skou bisimulation

A **probabilistic system** over a GSLT (`ProbabilisticSystem`) gives each
labelled step a finite sub-distribution over successor terms
(`SubDistribution`): finitely many draws with nonnegative weights of total at
most one, the defect being the probability that the step is refused.  The
weights are read modulo the equations: equated sources give every
equation-closed set of successors the same mass (`kernel_resp`), so the mass of
each equation class is well defined.

**Support erasure** (`support`).  Forgetting the weights leaves the
possibilistic system whose steps are the positively weighted successors, up to
the equations: a `HennessyMilner.System`.
* The diamond of the erasure holds exactly when the step gives its body
  positive probability (`support_sat_dia_iff`).  For an enabled step the
  normalised draws are a `WeightedObservers.Weighting` of the erased step
  (`toWeighting`), whose weighted observer is the mass divided by the total
  (`chance_toWeighting`), so `WeightedObservers.Weighting.erasure` is the same
  statement (`support_sat_dia_iff_of_enabled`).
* Every Hennessy–Milner formula of the erasure is a Larsen–Skou formula with
  threshold `0` (`support_sat_iff`).

**Larsen–Skou bisimulation** (`IsLSBisimulation`): an equivalence relation
containing the equations, preserving the atoms, under which related terms
give every closed set of successors the same mass under every label
(K. G. Larsen and A. Skou, *Bisimulation through probabilistic testing*,
Inf. Comput. 94, 1991).
* **The logical characterisation** (`lsBisimilar_iff_logicallyEquivalent`):
  bisimilarity is agreement on every formula of the logic with truth, atoms,
  negation, conjunction and the modality `⟨a⟩_{>q} φ` ("an `a`-step reaches `φ`
  with probability more than `q`", `q` rational).  Each step has finite
  support, so the systems are finitely branching and no further hypothesis is
  needed.
* **Erasure of bisimulations** (`IsLSBisimulation.isBisimulation_support`): a
  Larsen–Skou bisimulation is a bisimulation of the support.  The converse
  fails (`Controls`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Causality.WeightedObservers
open Mettapedia.InformationTheory

universe uS uAtom uLabel uα

/-! ## Finite sub-distributions -/

/-- **A finite sub-distribution**: finitely supported nonnegative weights of
total at most one. -/
structure SubDistribution (α : Type uα) where
  /-- The weights. -/
  weight : α →₀ ℝ
  nonneg : ∀ x, 0 ≤ weight x
  /-- The total weight is at most one; the defect is refusal. -/
  total_le_one : ∑ x ∈ weight.support, weight x ≤ 1

namespace SubDistribution

variable {α : Type uα} (μ : SubDistribution α)

open Classical in
/-- The mass of a predicate. -/
noncomputable def mass (C : α → Prop) : ℝ :=
  ∑ x ∈ μ.weight.support, if C x then μ.weight x else 0

/-- The total mass. -/
noncomputable def total : ℝ := ∑ x ∈ μ.weight.support, μ.weight x

theorem weight_pos {x : α} (member : x ∈ μ.weight.support) : 0 < μ.weight x :=
  lt_of_le_of_ne (μ.nonneg x) (Finsupp.mem_support_iff.mp member).symm

theorem mass_nonneg (C : α → Prop) : 0 ≤ μ.mass C := by
  classical
  unfold mass
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> first | exact μ.nonneg x | exact le_rfl

/-- **The mass depends only on the predicate on the support.** -/
theorem mass_congr {C D : α → Prop} (same : ∀ x ∈ μ.weight.support, C x ↔ D x) :
    μ.mass C = μ.mass D := by
  classical
  unfold mass
  refine Finset.sum_congr rfl fun x member => ?_
  by_cases holds : C x
  · rw [if_pos holds, if_pos ((same x member).mp holds)]
  · rw [if_neg holds, if_neg fun other => holds ((same x member).mpr other)]

/-- **Positive mass is a supported witness.** -/
theorem mass_pos_iff (C : α → Prop) : 0 < μ.mass C ↔ ∃ x ∈ μ.weight.support, C x := by
  classical
  unfold mass
  constructor
  · intro positive
    obtain ⟨x, member, nonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero positive.ne'
    by_cases holds : C x
    · exact ⟨x, member, holds⟩
    · rw [if_neg holds] at nonzero
      exact absurd rfl nonzero
  · rintro ⟨x, member, holds⟩
    refine Finset.sum_pos' (fun y _ => by
      split_ifs <;> first | exact μ.nonneg y | exact le_rfl) ⟨x, member, ?_⟩
    rw [if_pos holds]
    exact μ.weight_pos member

theorem mass_le_total (C : α → Prop) : μ.mass C ≤ μ.total := by
  classical
  unfold mass total
  exact Finset.sum_le_sum fun x _ => by
    split_ifs
    · exact le_rfl
    · exact μ.nonneg x

theorem mass_true : μ.mass (fun _ => True) = μ.total := by
  classical
  simp [mass, total]

theorem total_nonneg : 0 ≤ μ.total :=
  Finset.sum_nonneg fun x _ => μ.nonneg x

theorem total_le_one' : μ.total ≤ 1 :=
  μ.total_le_one

open Classical in
/-- On a finite type the mass is a sum over every point. -/
theorem mass_eq_sum [Fintype α] (C : α → Prop) :
    μ.mass C = ∑ x, if C x then μ.weight x else 0 := by
  unfold mass
  refine Finset.sum_subset (Finset.subset_univ _) fun x _ outside => ?_
  rw [Finsupp.notMem_support_iff.mp outside]
  simp

/-- On a finite type the total is a sum over every point. -/
theorem total_eq_sum [Fintype α] : μ.total = ∑ x, μ.weight x := by
  unfold total
  exact Finset.sum_subset (Finset.subset_univ _) fun x _ outside =>
    Finsupp.notMem_support_iff.mp outside

/-- A finitely supported family of nonnegative weights on a finite type with
total at most one. -/
noncomputable def ofFunction [Fintype α] (w : α → ℝ) (nonneg : ∀ x, 0 ≤ w x)
    (total : ∑ x, w x ≤ 1) : SubDistribution α where
  weight := Finsupp.equivFunOnFinite.symm w
  nonneg x := by simpa using nonneg x
  total_le_one := by
    have := Finset.sum_subset (Finset.subset_univ (Finsupp.equivFunOnFinite.symm w).support)
      fun x _ outside => Finsupp.notMem_support_iff.mp outside
    rw [this]
    simpa using total

@[simp] theorem ofFunction_weight [Fintype α] (w : α → ℝ) (nonneg : ∀ x, 0 ≤ w x)
    (total : ∑ x, w x ≤ 1) (x : α) : (ofFunction w nonneg total).weight x = w x := by
  simp [ofFunction]

end SubDistribution

/-! ## Probabilistic systems over a GSLT -/

set_option linter.checkUnivs false in
/-- **A probabilistic system over a GSLT**: atomic observations and labelled
steps, each a finite sub-distribution over successor terms, read modulo the
equations. -/
structure ProbabilisticSystem (S : GSLT.{uS}) where
  /-- The observation set. -/
  Atom : Type uAtom
  /-- Atomic observations. -/
  observes : Atom → S.Term → Prop
  /-- Observations cannot separate equated terms. -/
  observes_resp : ∀ (atom : Atom) {left right : S.Term},
    S.Equiv left right → (observes atom left ↔ observes atom right)
  /-- The labels. -/
  Label : Type uLabel
  /-- The labelled steps: a sub-distribution over successor terms. -/
  kernel : Label → S.Term → SubDistribution S.Term
  /-- **The weights are read modulo the equations**: equated sources give
  every equation-closed set of successors the same mass. -/
  kernel_resp : ∀ (label : Label) {left right : S.Term}, S.Equiv left right →
    ∀ C : S.Term → Prop, (∀ x y, S.Equiv x y → (C x ↔ C y)) →
      (kernel label left).mass C = (kernel label right).mass C

namespace ProbabilisticSystem

variable {S : GSLT.{uS}} (M : ProbabilisticSystem.{uS, uAtom, uLabel} S)

/-- The probability that an `label`-step from `term` lands in `C`. -/
noncomputable def prob (label : M.Label) (term : S.Term) (C : S.Term → Prop) : ℝ :=
  (M.kernel label term).mass C

/-- The mass of the equation class of `target`. -/
noncomputable def classMass (label : M.Label) (term target : S.Term) : ℝ :=
  M.prob label term (S.Equiv · target)

theorem equiv_closed (target : S.Term) :
    ∀ x y, S.Equiv x y → (S.Equiv x target ↔ S.Equiv y target) := fun _ _ equivalent =>
  ⟨fun first => S.equations.iseqv.trans (S.equations.iseqv.symm equivalent) first,
    fun second => S.equations.iseqv.trans equivalent second⟩

/-- **Class masses are a property of classes.** -/
theorem classMass_resp (label : M.Label) {term term' : S.Term} (equivalent : S.Equiv term term')
    (target : S.Term) : M.classMass label term target = M.classMass label term' target :=
  M.kernel_resp label equivalent _ (equiv_closed target)

/-! ## Support erasure -/

/-- **The support erasure**: a step goes to every term equated to a positively
weighted draw. -/
def support : System.{uAtom, uLabel} S where
  Atom := M.Atom
  observes := M.observes
  observes_resp := M.observes_resp
  Label := M.Label
  act label source target := ∃ x ∈ (M.kernel label source).weight.support, S.Equiv x target
  act_resp_left := by
    intro label left right target equivalent ⟨x, member, close⟩
    have positive : 0 < M.classMass label left target :=
      ((M.kernel label left).mass_pos_iff _).mpr ⟨x, member, close⟩
    rw [M.classMass_resp label equivalent] at positive
    obtain ⟨x', member', close'⟩ := ((M.kernel label right).mass_pos_iff _).mp positive
    exact ⟨target, ⟨x', member', close'⟩, S.equations.iseqv.refl target⟩
  act_resp_right := by
    intro label source target target' ⟨x, member, close⟩ equivalent
    exact ⟨x, member, S.equations.iseqv.trans close equivalent⟩

/-- **Erasure.**  The diamond of the support erasure holds exactly when the
step gives its body positive probability. -/
theorem support_sat_dia_iff (label : M.Label) (formula : Formula M.Atom M.Label)
    (source : S.Term) :
    M.support.sat (.dia label formula) source ↔
      0 < M.prob label source (M.support.sat formula) := by
  unfold prob
  rw [SubDistribution.mass_pos_iff]
  constructor
  · rintro ⟨target, ⟨x, member, close⟩, holds⟩
    exact ⟨x, member, (M.support.sat_resp formula close).mpr holds⟩
  · rintro ⟨x, member, holds⟩
    exact ⟨x, ⟨x, member, S.equations.iseqv.refl x⟩, holds⟩

/-! ### The normalised draws are a `Weighting` of the erased step -/

section Weighting

variable (label : M.Label) (source : S.Term)

/-- The draws of an enabled step, normalised. -/
noncomputable def normalisedLaw (enabled : 0 < (M.kernel label source).total) :
    Prob (M.kernel label source).weight.support :=
  ⟨fun x => (M.kernel label source).weight x.1 / (M.kernel label source).total,
    fun x => div_nonneg ((M.kernel label source).nonneg x.1) enabled.le, by
      rw [Finset.sum_coe_sort (M.kernel label source).weight.support
        (fun x => (M.kernel label source).weight x / (M.kernel label source).total),
        ← Finset.sum_div]
      exact div_self enabled.ne'⟩

/-- **An enabled step, normalised, is a `Weighting` of its support erasure.** -/
noncomputable def toWeighting (enabled : 0 < (M.kernel label source).total) :
    Weighting M.support label source (M.kernel label source).weight.support where
  law := M.normalisedLaw label source enabled
  draw x := x.1
  sound x _ := ⟨x.1, x.2, S.equations.iseqv.refl _⟩
  complete target := by
    rintro ⟨x, member, close⟩
    exact ⟨⟨x, member⟩, div_pos ((M.kernel label source).weight_pos member) enabled, close⟩

/-- **The weighted observer of the normalised draws is the mass over the
total.** -/
theorem chance_toWeighting (enabled : 0 < (M.kernel label source).total)
    (formula : Formula M.Atom M.Label) :
    chance M.support (M.toWeighting label source enabled).law
        (M.toWeighting label source enabled).draw formula =
      M.prob label source (M.support.sat formula) / (M.kernel label source).total := by
  classical
  unfold chance
  rw [mass_eq_sum]
  unfold prob SubDistribution.mass
  rw [Finset.sum_div]
  rw [← Finset.sum_coe_sort (M.kernel label source).weight.support]
  refine Finset.sum_congr rfl fun x _ => ?_
  change (M.kernel label source).weight x.1 / (M.kernel label source).total *
      Set.indicator {ω | M.support.sat formula ω.1} 1 x = _
  by_cases holds : M.support.sat formula x.1
  · rw [Set.indicator_of_mem (show x ∈ {ω : (M.kernel label source).weight.support |
      M.support.sat formula ω.1} from holds), if_pos holds]
    simp
  · rw [Set.indicator_of_notMem (show x ∉ {ω : (M.kernel label source).weight.support |
      M.support.sat formula ω.1} from holds), if_neg holds]
    simp

/-- **Erasure through `Weighting.erasure`**: for an enabled step the support
diamond holds exactly when the normalised weighted observer is positive. -/
theorem support_sat_dia_iff_of_enabled (enabled : 0 < (M.kernel label source).total)
    (formula : Formula M.Atom M.Label) :
    M.support.sat (.dia label formula) source ↔
      0 < chance M.support (M.toWeighting label source enabled).law
        (M.toWeighting label source enabled).draw formula :=
  (M.toWeighting label source enabled).erasure formula

end Weighting

/-! ## The logic of Larsen and Skou -/

/-- **Larsen–Skou formulas**: truth, atoms, negation, conjunction, and
`more a q φ`, "an `a`-step reaches `φ` with probability more than `q`". -/
inductive LSFormula (Atom : Type uAtom) (Label : Type uLabel) : Type (max uAtom uLabel) where
  | top : LSFormula Atom Label
  | atom (atom : Atom) : LSFormula Atom Label
  | neg (inner : LSFormula Atom Label) : LSFormula Atom Label
  | conj (left right : LSFormula Atom Label) : LSFormula Atom Label
  | more (label : Label) (threshold : ℚ) (inner : LSFormula Atom Label) : LSFormula Atom Label

instance {Atom : Type uAtom} {Label : Type uLabel} : Inhabited (LSFormula Atom Label) :=
  ⟨.top⟩

/-- Finite conjunction. -/
def LSFormula.conjList {Atom : Type uAtom} {Label : Type uLabel} :
    List (LSFormula Atom Label) → LSFormula Atom Label
  | [] => .top
  | formula :: formulas => .conj formula (LSFormula.conjList formulas)

/-- Finite disjunction. -/
def LSFormula.disjList {Atom : Type uAtom} {Label : Type uLabel}
    (formulas : List (LSFormula Atom Label)) : LSFormula Atom Label :=
  .neg (LSFormula.conjList (formulas.map .neg))

/-- Satisfaction. -/
def sat : LSFormula M.Atom M.Label → S.Term → Prop
  | .top, _ => True
  | .atom atom, term => M.observes atom term
  | .neg inner, term => ¬ sat inner term
  | .conj left right, term => sat left term ∧ sat right term
  | .more label threshold inner, term => (threshold : ℝ) < M.prob label term (sat inner)

theorem sat_conjList (formulas : List (LSFormula M.Atom M.Label)) (term : S.Term) :
    M.sat (LSFormula.conjList formulas) term ↔ ∀ formula ∈ formulas, M.sat formula term := by
  induction formulas with
  | nil => simp [LSFormula.conjList, sat]
  | cons formula formulas inductionHypothesis =>
      simp [LSFormula.conjList, sat, inductionHypothesis]

theorem sat_disjList (formulas : List (LSFormula M.Atom M.Label)) (term : S.Term) :
    M.sat (LSFormula.disjList formulas) term ↔ ∃ formula ∈ formulas, M.sat formula term := by
  simp [LSFormula.disjList, sat, sat_conjList]

/-- **Satisfaction respects the equations.** -/
theorem sat_resp : ∀ (formula : LSFormula M.Atom M.Label) {left right : S.Term},
    S.Equiv left right → (M.sat formula left ↔ M.sat formula right)
  | .top, _, _, _ => Iff.rfl
  | .atom atom, _, _, equivalent => M.observes_resp atom equivalent
  | .neg inner, _, _, equivalent => not_congr (sat_resp inner equivalent)
  | .conj first second, _, _, equivalent =>
      and_congr (sat_resp first equivalent) (sat_resp second equivalent)
  | .more label threshold inner, _, _, equivalent => by
      simp only [sat, prob]
      rw [M.kernel_resp label equivalent _ fun x y close => sat_resp inner close]

/-- Two terms satisfy the same Larsen–Skou formulas. -/
def LogicallyEquivalent (left right : S.Term) : Prop :=
  ∀ formula : LSFormula M.Atom M.Label, M.sat formula left ↔ M.sat formula right

/-- Hennessy–Milner formulas of the erasure, read as Larsen–Skou formulas: the
diamond is the modality with threshold `0`. -/
def ofHM : Formula M.Atom M.Label → LSFormula M.Atom M.Label
  | .top => .top
  | .atom atom => .atom atom
  | .conj left right => .conj (ofHM left) (ofHM right)
  | .neg inner => .neg (ofHM inner)
  | .dia label inner => .more label 0 (ofHM inner)

/-- **The support erasure is the threshold-`0` fragment.** -/
theorem support_sat_iff : ∀ (formula : Formula M.Atom M.Label) (term : S.Term),
    M.support.sat formula term ↔ M.sat (M.ofHM formula) term
  | .top, _ => Iff.rfl
  | .atom _, _ => Iff.rfl
  | .conj left right, term => and_congr (support_sat_iff left term) (support_sat_iff right term)
  | .neg inner, term => not_congr (support_sat_iff inner term)
  | .dia label inner, term => by
      refine (M.support_sat_dia_iff label inner term).trans ?_
      simp only [ofHM, sat, Rat.cast_zero, prob]
      rw [(M.kernel label term).mass_congr fun x _ => support_sat_iff inner x]

/-! ## Larsen–Skou bisimulation -/

/-- A predicate closed under a relation. -/
def ClosedUnder (relation : S.Term → S.Term → Prop) (C : S.Term → Prop) : Prop :=
  ∀ x y, relation x y → (C x ↔ C y)

/-- **A Larsen–Skou bisimulation**: an equivalence containing the equations,
preserving atoms, under which related terms give every closed set the same
mass under every label. -/
structure IsLSBisimulation (relation : S.Term → S.Term → Prop) : Prop where
  equivalence : Equivalence relation
  equations : ∀ {left right}, S.Equiv left right → relation left right
  observes : ∀ {left right}, relation left right → ∀ atom,
    (M.observes atom left ↔ M.observes atom right)
  masses : ∀ {left right}, relation left right → ∀ (label : M.Label) (C : S.Term → Prop),
    ClosedUnder relation C → M.prob label left C = M.prob label right C

/-- **Larsen–Skou bisimilarity.** -/
def LSBisimilar (left right : S.Term) : Prop :=
  ∃ relation, M.IsLSBisimulation relation ∧ relation left right

variable {M} in
/-- **Soundness**: related terms satisfy the same formulas. -/
theorem IsLSBisimulation.sat_iff {relation : S.Term → S.Term → Prop}
    (bisimulation : M.IsLSBisimulation relation) :
    ∀ (formula : LSFormula M.Atom M.Label) {left right : S.Term},
      relation left right → (M.sat formula left ↔ M.sat formula right)
  | .top, _, _, _ => Iff.rfl
  | .atom atom, _, _, related => bisimulation.observes related atom
  | .neg inner, _, _, related => not_congr (IsLSBisimulation.sat_iff bisimulation inner related)
  | .conj first second, _, _, related =>
      and_congr (IsLSBisimulation.sat_iff bisimulation first related)
        (IsLSBisimulation.sat_iff bisimulation second related)
  | .more label threshold inner, _, _, related => by
      simp only [sat]
      rw [bisimulation.masses related label _ fun x y close =>
        IsLSBisimulation.sat_iff bisimulation inner close]

variable {M} in
theorem LSBisimilar.logicallyEquivalent {left right : S.Term}
    (bisimilar : M.LSBisimilar left right) : M.LogicallyEquivalent left right := by
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  exact fun formula => bisimulation.sat_iff formula related

open Classical in
/-- The masses of a closed set agree when a formula picks out the set on the
supports. -/
theorem prob_eq_of_separating {label : M.Label} {left right : S.Term} {C : S.Term → Prop}
    (formula : LSFormula M.Atom M.Label)
    (picks : ∀ x, x ∈ (M.kernel label left).weight.support ∪ (M.kernel label right).weight.support →
      (M.sat formula x ↔ C x))
    (equivalent : M.LogicallyEquivalent left right) :
    M.prob label left C = M.prob label right C := by
  have leftMass : M.prob label left C = M.prob label left (M.sat formula) :=
    (M.kernel label left).mass_congr fun x member =>
      (picks x (Finset.mem_union_left _ member)).symm
  have rightMass : M.prob label right C = M.prob label right (M.sat formula) :=
    (M.kernel label right).mass_congr fun x member =>
      (picks x (Finset.mem_union_right _ member)).symm
  rw [leftMass, rightMass]
  by_contra different
  rcases lt_or_gt_of_ne different with less | greater
  · obtain ⟨threshold, above, below⟩ := exists_rat_btwn less
    have holds : M.sat (.more label threshold formula) right := below
    exact absurd ((equivalent _).mpr holds) (not_lt.mpr above.le)
  · obtain ⟨threshold, above, below⟩ := exists_rat_btwn greater
    have holds : M.sat (.more label threshold formula) left := below
    exact absurd ((equivalent _).mp holds) (not_lt.mpr above.le)

/-- **Logical equivalence is a Larsen–Skou bisimulation.**  The supports are
finite, so a finite Boolean combination of separating formulas picks out any
closed set on them. -/
theorem isLSBisimulation_logicallyEquivalent : M.IsLSBisimulation M.LogicallyEquivalent where
  equivalence := ⟨fun _ _ => Iff.rfl, fun same formula => (same formula).symm,
    fun first second formula => (first formula).trans (second formula)⟩
  equations equivalent formula := M.sat_resp formula equivalent
  observes related atom := related (.atom atom)
  masses := by
    classical
    intro left right equivalent label C closed
    set support := (M.kernel label left).weight.support ∪ (M.kernel label right).weight.support
    have separate : ∀ x y, C x → ¬ C y →
        ∃ formula, M.sat formula x ∧ ¬ M.sat formula y := by
      intro x y inside outside
      have different : ¬ M.LogicallyEquivalent x y := fun same =>
        outside ((closed x y same).mp inside)
      obtain ⟨formula, differs⟩ := not_forall.mp different
      by_cases holds : M.sat formula x
      · exact ⟨formula, holds, fun other => differs (iff_of_true holds other)⟩
      · exact ⟨.neg formula, holds, fun other => differs (iff_of_false holds other)⟩
    choose! separator separator_spec using separate
    let inside := support.filter C
    let outside := support.filter fun y => ¬ C y
    let picker : LSFormula M.Atom M.Label := LSFormula.disjList
      (inside.toList.map fun x => LSFormula.conjList (outside.toList.map (separator x)))
    refine M.prob_eq_of_separating picker (fun z member => ?_) equivalent
    rw [sat_disjList]
    constructor
    · rintro ⟨formula, chosen, holds⟩
      obtain ⟨x, xInside, rfl⟩ := List.mem_map.mp chosen
      rw [Finset.mem_toList, Finset.mem_filter] at xInside
      by_contra outsideZ
      rw [sat_conjList] at holds
      have zOutside : z ∈ outside.toList := by
        rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨member, outsideZ⟩
      exact (separator_spec x z xInside.2 outsideZ).2
        (holds _ (List.mem_map.mpr ⟨z, zOutside, rfl⟩))
    · intro insideZ
      refine ⟨_, List.mem_map.mpr ⟨z, ?_, rfl⟩, ?_⟩
      · rw [Finset.mem_toList, Finset.mem_filter]
        exact ⟨member, insideZ⟩
      · rw [sat_conjList]
        intro formula chosen
        obtain ⟨y, yOutside, rfl⟩ := List.mem_map.mp chosen
        rw [Finset.mem_toList, Finset.mem_filter] at yOutside
        exact (separator_spec z y insideZ yOutside.2).1

/-- **The logical characterisation of Larsen–Skou bisimilarity.** -/
theorem lsBisimilar_iff_logicallyEquivalent {left right : S.Term} :
    M.LSBisimilar left right ↔ M.LogicallyEquivalent left right :=
  ⟨fun bisimilar => bisimilar.logicallyEquivalent,
    fun equivalent => ⟨_, M.isLSBisimulation_logicallyEquivalent, equivalent⟩⟩

variable {M} in
/-- Logical equivalence is the largest Larsen–Skou bisimulation. -/
theorem IsLSBisimulation.le_logicallyEquivalent {relation : S.Term → S.Term → Prop}
    (bisimulation : M.IsLSBisimulation relation) {left right : S.Term}
    (related : relation left right) : M.LogicallyEquivalent left right :=
  fun formula => bisimulation.sat_iff formula related

/-! ## Erasure of bisimulations -/

variable {M} in
/-- **A Larsen–Skou bisimulation is a bisimulation of the support erasure.** -/
theorem IsLSBisimulation.isBisimulation_support {relation : S.Term → S.Term → Prop}
    (bisimulation : M.IsLSBisimulation relation) : M.support.IsBisimulation relation := by
  have transfer : ∀ {left right}, relation left right → ∀ (label : M.Label) {left'},
      M.support.act label left left' → ∃ right', M.support.act label right right' ∧
        relation left' right' := by
    intro left right related label left' ⟨x, member, close⟩
    have closedSet : ClosedUnder relation (relation left') := fun y z yz =>
      ⟨fun first => bisimulation.equivalence.trans first yz,
        fun second => bisimulation.equivalence.trans second (bisimulation.equivalence.symm yz)⟩
    have positive : 0 < M.prob label left (relation left') :=
      ((M.kernel label left).mass_pos_iff _).mpr ⟨x, member,
        bisimulation.equivalence.symm (bisimulation.equations close)⟩
    rw [bisimulation.masses related label _ closedSet] at positive
    obtain ⟨y, member', related'⟩ := ((M.kernel label right).mass_pos_iff _).mp positive
    exact ⟨y, ⟨y, member', S.equations.iseqv.refl y⟩, related'⟩
  refine ⟨?_, ?_, ?_⟩
  · intro left right related label left' step
    exact transfer related label step
  · intro left right related label right' step
    obtain ⟨left', step', related'⟩ :=
      transfer (bisimulation.equivalence.symm related) label step
    exact ⟨left', step', bisimulation.equivalence.symm related'⟩
  · intro left right related atom
    exact bisimulation.observes related atom

variable {M} in
/-- **Larsen–Skou bisimilar terms are bisimilar in the support erasure.** -/
theorem LSBisimilar.support_bisimilar {left right : S.Term} (bisimilar : M.LSBisimilar left right) :
    M.support.Bisimilar left right := by
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  exact ⟨relation, bisimulation.isBisimulation_support, related⟩

end ProbabilisticSystem

end Mettapedia.GSLT.Distinction.Probabilistic
