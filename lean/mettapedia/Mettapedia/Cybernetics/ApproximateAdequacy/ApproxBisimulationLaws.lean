import Mettapedia.Cybernetics.MindWorldApproximation

/-!
# Laws of approximate bisimulation

The `ε`-approximate simulations and bisimulations of A. Girard and G. J. Pappas
(*Approximation metrics for discrete and continuous systems*, IEEE Trans.
Automatic Control 52(5), 2007) are defined in
`Mettapedia.Cybernetics.MindWorldApproximation`: related states have
observations within `ε`, and transitions are matched exactly.  This module
proves the laws that say what such a relation certifies and how certificates
compose.  The distance is any function into an ordered additive monoid; no
result here uses a property of the real numbers.

**What it certifies.**
* *Observations along every run, uniformly in time.*  Every run of the first
  system from a related state is matched, for every horizon, by a run of the
  second system whose observations stay within `ε` at every step
  (`IsApproxSimulation.exists_run`, `IsApproxSimulation.run_close`).  The
  bound does not grow with the horizon: the relation is invariant, not
  accumulated.
* *Positive modal formulas up to inflation.*  For formulas built from
  predicates on observations with conjunction, disjunction, `◇` and `□`, a
  formula true at a state holds at every `ε`-approximately bisimilar state
  once each atomic predicate is inflated by `ε`
  (`PositiveFormula.sat_inflate`).  Inflations compose along the triangle
  inequality (`PositiveFormula.sat_inflate_inflate`).  Negation is excluded:
  a crisp threshold can flip under any positive error (see
  `Mettapedia.Cybernetics.ApproximateAdequacy.Hosting`).

**How certificates compose.**
* The equality relation is a `0`-approximate bisimulation whenever the
  distance vanishes on the diagonal (`isApproxBisimulation_eq`).
* Reversing a certificate needs no symmetry of the distance, because the
  definition already measures the reverse direction from the second system
  (`IsApproxBisimulation.symm`).
* **Sequential composition adds errors** (`IsApproxSimulation.comp`,
  `IsApproxBisimulation.comp`): approximate bisimilarity satisfies the
  triangle inequality (`ApproxBisimilar.trans`).
* Approximate bisimilarity is itself the largest approximate bisimulation at
  its precision (`approxBisimilar_isApproxBisimulation`), and is monotone in
  the precision (`ApproxBisimilar.mono`).
* **Parallel composition adds errors** for the sum of the component
  distances, both for the synchronous product
  (`IsApproxBisimulation.sync`) and for interleaving
  (`IsApproxBisimulation.interleave`).

The laws about the predicates of `MindWorldApproximation` are declared in its
namespace, so that dot notation reaches them; the new definitions live in
`Mettapedia.Cybernetics.ApproximateAdequacy`.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

/-! ## Products of transition systems -/

section Products

variable {X₁ X₂ Y₁ Y₂ O₁ O₂ D : Type*}

/-- The synchronous product: both components move. -/
def syncStep (step₁ : X₁ → X₁ → Prop) (step₂ : X₂ → X₂ → Prop) : X₁ × X₂ → X₁ × X₂ → Prop :=
  fun p q => step₁ p.1 q.1 ∧ step₂ p.2 q.2

/-- Interleaving: exactly one component moves. -/
def interleaveStep (step₁ : X₁ → X₁ → Prop) (step₂ : X₂ → X₂ → Prop) :
    X₁ × X₂ → X₁ × X₂ → Prop :=
  fun p q => (step₁ p.1 q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ step₂ p.2 q.2)

/-- The sum of the component distances on paired observations. -/
def sumDistance [Add D] (distance₁ : O₁ → O₁ → D) (distance₂ : O₂ → O₂ → D) :
    O₁ × O₂ → O₁ × O₂ → D :=
  fun a b => distance₁ a.1 b.1 + distance₂ a.2 b.2

/-- The product of two relations. -/
def prodRel (R₁ : X₁ → Y₁ → Prop) (R₂ : X₂ → Y₂ → Prop) : X₁ × X₂ → Y₁ × Y₂ → Prop :=
  fun p q => R₁ p.1 q.1 ∧ R₂ p.2 q.2

/-- The converse of a product relation is the product of the converses. -/
theorem flip_prodRel (R₁ : X₁ → Y₁ → Prop) (R₂ : X₂ → Y₂ → Prop) :
    flip (prodRel R₁ R₂) = prodRel (flip R₁) (flip R₂) :=
  rfl

end Products

/-! ## Positive modal formulas over observations -/

/-- Modal formulas over predicates on observations, without negation. -/
inductive PositiveFormula (O : Type*) : Type _
  | atom (predicate : O → Prop)
  | and (first second : PositiveFormula O)
  | or (first second : PositiveFormula O)
  | dia (body : PositiveFormula O)
  | box (body : PositiveFormula O)

namespace PositiveFormula

variable {X O D : Type*}

/-- Satisfaction at a state of a transition system with observations. -/
def Sat (step : X → X → Prop) (obs : X → O) : PositiveFormula O → X → Prop
  | atom predicate, x => predicate (obs x)
  | and first second, x => first.Sat step obs x ∧ second.Sat step obs x
  | or first second, x => first.Sat step obs x ∨ second.Sat step obs x
  | dia body, x => ∃ x', step x x' ∧ body.Sat step obs x'
  | box body, x => ∀ x', step x x' → body.Sat step obs x'

/-- Inflate every atomic predicate by `ε`: an observation satisfies the
inflation when it is within `ε` of one satisfying the predicate. -/
def inflate [LE D] (distance : O → O → D) (ε : D) : PositiveFormula O → PositiveFormula O
  | atom predicate => atom fun o => ∃ o', predicate o' ∧ distance o' o ≤ ε
  | and first second => and (first.inflate distance ε) (second.inflate distance ε)
  | or first second => or (first.inflate distance ε) (second.inflate distance ε)
  | dia body => dia (body.inflate distance ε)
  | box body => box (body.inflate distance ε)

end PositiveFormula

end Mettapedia.Cybernetics.ApproximateAdequacy

namespace Mettapedia.Cybernetics.MindWorldApproximation

open Mettapedia.Cybernetics.ApproximateAdequacy

variable {X Y Z O D : Type*}

/-! ## Identity, monotonicity, reversal -/

section Basic

variable [Preorder D] {distance : O → O → D} {step : X → X → Prop} {step' : Y → Y → Prop}
  {obs : X → O} {obs' : Y → O} {ε δ : D} {R : X → Y → Prop}

/-- **The equality relation is an approximate bisimulation** at every precision
that bounds the distance of an observation to itself. -/
theorem isApproxBisimulation_eq (self : ∀ o, distance o o ≤ ε) :
    IsApproxBisimulation distance step step obs obs ε Eq :=
  ⟨⟨fun x _ same => same ▸ self (obs x), fun _ _ same x' moved => ⟨x', same ▸ moved, rfl⟩⟩,
    ⟨fun _ x same => by
        change x = _ at same
        exact same ▸ self (obs x),
      fun _ x same x' moved => by
        change x = _ at same
        exact ⟨x', same ▸ moved, rfl⟩⟩⟩

theorem IsApproxSimulation.mono (simulation : IsApproxSimulation distance step step' obs obs' ε R)
    (le : ε ≤ δ) : IsApproxSimulation distance step step' obs obs' δ R :=
  ⟨fun _ _ related => (simulation.close related).trans le, simulation.forth⟩

theorem IsApproxBisimulation.mono
    (bisimulation : IsApproxBisimulation distance step step' obs obs' ε R) (le : ε ≤ δ) :
    IsApproxBisimulation distance step step' obs obs' δ R :=
  ⟨bisimulation.1.mono le, bisimulation.2.mono le⟩

/-- **Reversal**: the converse of an approximate bisimulation is one. -/
theorem IsApproxBisimulation.symm
    (bisimulation : IsApproxBisimulation distance step step' obs obs' ε R) :
    IsApproxBisimulation distance step' step obs' obs ε (flip R) :=
  ⟨bisimulation.2, bisimulation.1⟩

theorem ApproxBisimilar.mono {x : X} {y : Y}
    (bisimilar : ApproxBisimilar distance step step' obs obs' ε x y) (le : ε ≤ δ) :
    ApproxBisimilar distance step step' obs obs' δ x y :=
  let ⟨R, bisimulation, related⟩ := bisimilar
  ⟨R, bisimulation.mono le, related⟩

theorem ApproxBisimilar.symm {x : X} {y : Y}
    (bisimilar : ApproxBisimilar distance step step' obs obs' ε x y) :
    ApproxBisimilar distance step' step obs' obs ε y x :=
  let ⟨R, bisimulation, related⟩ := bisimilar
  ⟨flip R, bisimulation.symm, related⟩

/-- **Approximate bisimilarity is the largest approximate bisimulation** at its
precision. -/
theorem approxBisimilar_isApproxBisimulation :
    IsApproxBisimulation distance step step' obs obs' ε
      (ApproxBisimilar distance step step' obs obs' ε) := by
  refine ⟨⟨fun _ _ ⟨_, bisimulation, related⟩ => bisimulation.1.close related,
    fun _ _ ⟨R, bisimulation, related⟩ x' moved => ?_⟩,
    ⟨fun _ _ ⟨_, bisimulation, related⟩ => bisimulation.2.close related,
      fun _ _ ⟨R, bisimulation, related⟩ y' moved => ?_⟩⟩
  · obtain ⟨y', moved', related'⟩ := bisimulation.1.forth related x' moved
    exact ⟨y', moved', R, bisimulation, related'⟩
  · obtain ⟨x', moved', related'⟩ := bisimulation.2.forth related y' moved
    exact ⟨x', moved', R, bisimulation, related'⟩

end Basic

/-! ## Sequential composition -/

section Composition

variable [AddCommMonoid D] [PartialOrder D] [IsOrderedAddMonoid D] {distance : O → O → D}
  {step : X → X → Prop} {step' : Y → Y → Prop} {step'' : Z → Z → Prop}
  {obs : X → O} {obs' : Y → O} {obs'' : Z → O} {ε δ : D}
  {R : X → Y → Prop} {S : Y → Z → Prop}

/-- **Approximate simulations compose, adding their errors.** -/
theorem IsApproxSimulation.comp (triangle : ∀ a b c, distance a c ≤ distance a b + distance b c)
    (first : IsApproxSimulation distance step step' obs obs' ε R)
    (second : IsApproxSimulation distance step' step'' obs' obs'' δ S) :
    IsApproxSimulation distance step step'' obs obs'' (ε + δ) (Relation.Comp R S) where
  close := fun _ _ ⟨_, related, related'⟩ =>
    (triangle _ _ _).trans (add_le_add (first.close related) (second.close related'))
  forth := fun _ _ ⟨_, related, related'⟩ x' moved => by
    obtain ⟨y', moved', relatedY⟩ := first.forth related x' moved
    obtain ⟨z', moved'', relatedZ⟩ := second.forth related' y' moved'
    exact ⟨z', moved'', y', relatedY, relatedZ⟩

/-- **Approximate bisimulations compose, adding their errors.** -/
theorem IsApproxBisimulation.comp (triangle : ∀ a b c, distance a c ≤ distance a b + distance b c)
    (first : IsApproxBisimulation distance step step' obs obs' ε R)
    (second : IsApproxBisimulation distance step' step'' obs' obs'' δ S) :
    IsApproxBisimulation distance step step'' obs obs'' (ε + δ) (Relation.Comp R S) := by
  refine ⟨first.1.comp triangle second.1, ?_⟩
  have reverse := second.2.comp triangle first.2
  rw [add_comm] at reverse
  refine ⟨fun _ _ ⟨y, related, related'⟩ => reverse.close ⟨y, related', related⟩,
    fun _ _ ⟨y, related, related'⟩ z' moved => ?_⟩
  obtain ⟨x', moved', y', relatedZ, relatedX⟩ := reverse.forth ⟨y, related', related⟩ z' moved
  exact ⟨x', moved', y', relatedX, relatedZ⟩

/-- **The triangle inequality for approximate bisimilarity.** -/
theorem ApproxBisimilar.trans (triangle : ∀ a b c, distance a c ≤ distance a b + distance b c)
    {x : X} {y : Y} {z : Z} (first : ApproxBisimilar distance step step' obs obs' ε x y)
    (second : ApproxBisimilar distance step' step'' obs' obs'' δ y z) :
    ApproxBisimilar distance step step'' obs obs'' (ε + δ) x z :=
  let ⟨_, bisimulation, related⟩ := first
  let ⟨_, bisimulation', related'⟩ := second
  ⟨_, bisimulation.comp triangle bisimulation', _, related, related'⟩

end Composition

/-! ## Parallel composition -/

section Parallel

variable {X₁ X₂ Y₁ Y₂ O₁ O₂ : Type*} [AddCommMonoid D] [PartialOrder D] [IsOrderedAddMonoid D]
  {distance₁ : O₁ → O₁ → D} {distance₂ : O₂ → O₂ → D}
  {step₁ : X₁ → X₁ → Prop} {step₂ : X₂ → X₂ → Prop}
  {step₁' : Y₁ → Y₁ → Prop} {step₂' : Y₂ → Y₂ → Prop}
  {obs₁ : X₁ → O₁} {obs₂ : X₂ → O₂} {obs₁' : Y₁ → O₁} {obs₂' : Y₂ → O₂}
  {ε₁ ε₂ : D} {R₁ : X₁ → Y₁ → Prop} {R₂ : X₂ → Y₂ → Prop}

theorem IsApproxSimulation.sync
    (first : IsApproxSimulation distance₁ step₁ step₁' obs₁ obs₁' ε₁ R₁)
    (second : IsApproxSimulation distance₂ step₂ step₂' obs₂ obs₂' ε₂ R₂) :
    IsApproxSimulation (sumDistance distance₁ distance₂) (syncStep step₁ step₂)
      (syncStep step₁' step₂') (Prod.map obs₁ obs₂) (Prod.map obs₁' obs₂') (ε₁ + ε₂)
      (prodRel R₁ R₂) where
  close := fun _ _ related => add_le_add (first.close related.1) (second.close related.2)
  forth := fun _ _ related x' moved => by
    obtain ⟨y₁, moved₁, related₁⟩ := first.forth related.1 x'.1 moved.1
    obtain ⟨y₂, moved₂, related₂⟩ := second.forth related.2 x'.2 moved.2
    exact ⟨(y₁, y₂), ⟨moved₁, moved₂⟩, related₁, related₂⟩

theorem IsApproxSimulation.interleave
    (first : IsApproxSimulation distance₁ step₁ step₁' obs₁ obs₁' ε₁ R₁)
    (second : IsApproxSimulation distance₂ step₂ step₂' obs₂ obs₂' ε₂ R₂) :
    IsApproxSimulation (sumDistance distance₁ distance₂) (interleaveStep step₁ step₂)
      (interleaveStep step₁' step₂') (Prod.map obs₁ obs₂) (Prod.map obs₁' obs₂') (ε₁ + ε₂)
      (prodRel R₁ R₂) where
  close := fun _ _ related => add_le_add (first.close related.1) (second.close related.2)
  forth := fun _ q related x' moved => by
    rcases moved with ⟨moved₁, same₂⟩ | ⟨same₁, moved₂⟩
    · obtain ⟨y₁, moved₁', related₁⟩ := first.forth related.1 x'.1 moved₁
      exact ⟨(y₁, q.2), Or.inl ⟨moved₁', rfl⟩, related₁, same₂ ▸ related.2⟩
    · obtain ⟨y₂, moved₂', related₂⟩ := second.forth related.2 x'.2 moved₂
      exact ⟨(q.1, y₂), Or.inr ⟨rfl, moved₂'⟩, same₁ ▸ related.1, related₂⟩

/-- **Parallel composition, synchronous: errors add.** -/
theorem IsApproxBisimulation.sync
    (first : IsApproxBisimulation distance₁ step₁ step₁' obs₁ obs₁' ε₁ R₁)
    (second : IsApproxBisimulation distance₂ step₂ step₂' obs₂ obs₂' ε₂ R₂) :
    IsApproxBisimulation (sumDistance distance₁ distance₂) (syncStep step₁ step₂)
      (syncStep step₁' step₂') (Prod.map obs₁ obs₂) (Prod.map obs₁' obs₂') (ε₁ + ε₂)
      (prodRel R₁ R₂) :=
  ⟨first.1.sync second.1, first.2.sync second.2⟩

/-- **Parallel composition, interleaving: errors add.** -/
theorem IsApproxBisimulation.interleave
    (first : IsApproxBisimulation distance₁ step₁ step₁' obs₁ obs₁' ε₁ R₁)
    (second : IsApproxBisimulation distance₂ step₂ step₂' obs₂ obs₂' ε₂ R₂) :
    IsApproxBisimulation (sumDistance distance₁ distance₂) (interleaveStep step₁ step₂)
      (interleaveStep step₁' step₂') (Prod.map obs₁ obs₂) (Prod.map obs₁' obs₂') (ε₁ + ε₂)
      (prodRel R₁ R₂) :=
  ⟨first.1.interleave second.1, first.2.interleave second.2⟩

end Parallel

/-! ## What a certificate certifies: runs -/

section Runs

variable [LE D] {distance : O → O → D} {step : X → X → Prop} {step' : Y → Y → Prop}
  {obs : X → O} {obs' : Y → O} {ε : D} {R : X → Y → Prop}

/-- **Every run is matched, for every horizon.**  A run of length `n` of the
first system from a related state is matched by a run of the second system
that stays related at every step. -/
theorem IsApproxSimulation.exists_run
    (simulation : IsApproxSimulation distance step step' obs obs' ε R)
    (run : ℕ → X) {y : Y} (related : R (run 0) y) :
    ∀ n : ℕ, (∀ i < n, step (run i) (run (i + 1))) →
      ∃ run' : ℕ → Y, run' 0 = y ∧ (∀ i < n, step' (run' i) (run' (i + 1))) ∧
        ∀ i ≤ n, R (run i) (run' i)
  | 0, _ => ⟨fun _ => y, rfl, fun _ bound => absurd bound (Nat.not_lt_zero _),
      fun _ bound => (Nat.le_zero.mp bound) ▸ related⟩
  | n + 1, moves => by
    obtain ⟨run', start, moves', relatedAlong⟩ :=
      simulation.exists_run run related n fun i bound => moves i (Nat.lt_succ_of_lt bound)
    obtain ⟨y', moved, related'⟩ :=
      simulation.forth (relatedAlong n le_rfl) (run (n + 1)) (moves n (Nat.lt_succ_self n))
    refine ⟨fun i => if i ≤ n then run' i else y', ?_, fun i bound => ?_, fun i bound => ?_⟩
    · change (if 0 ≤ n then run' 0 else y') = y
      rw [if_pos (Nat.zero_le n)]
      exact start
    · change step' (if i ≤ n then run' i else y') (if i + 1 ≤ n then run' (i + 1) else y')
      by_cases last : i = n
      · subst last
        rw [if_pos le_rfl, if_neg (Nat.not_succ_le_self i)]
        exact moved
      · have inside : i + 1 ≤ n := by omega
        rw [if_pos (Nat.le_of_succ_le inside), if_pos inside]
        exact moves' i inside
    · change R (run i) (if i ≤ n then run' i else y')
      by_cases last : i = n + 1
      · subst last
        rw [if_neg (Nat.not_succ_le_self n)]
        exact related'
      · have inside : i ≤ n := by omega
        rw [if_pos inside]
        exact relatedAlong i inside

/-- **Observations along every run stay within `ε`, uniformly in the
horizon.** -/
theorem IsApproxSimulation.run_close
    (simulation : IsApproxSimulation distance step step' obs obs' ε R)
    (run : ℕ → X) {y : Y} (related : R (run 0) y) (n : ℕ)
    (moves : ∀ i < n, step (run i) (run (i + 1))) :
    ∃ run' : ℕ → Y, run' 0 = y ∧ (∀ i < n, step' (run' i) (run' (i + 1))) ∧
      ∀ i ≤ n, distance (obs (run i)) (obs' (run' i)) ≤ ε := by
  obtain ⟨run', start, moves', relatedAlong⟩ := simulation.exists_run run related n moves
  exact ⟨run', start, moves', fun i bound => simulation.close (relatedAlong i bound)⟩

end Runs

end Mettapedia.Cybernetics.MindWorldApproximation

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Mettapedia.Cybernetics.MindWorldApproximation

namespace PositiveFormula

variable {X Y O D : Type*}

/-! ## What a certificate certifies: positive formulas up to inflation -/

section Transfer

variable [LE D] {distance : O → O → D} {step : X → X → Prop} {step' : Y → Y → Prop}
  {obs : X → O} {obs' : Y → O} {ε : D} {R : X → Y → Prop}

/-- **Positive formulas transfer along an approximate bisimulation, up to
inflation of their atoms.** -/
theorem sat_inflate (bisimulation : IsApproxBisimulation distance step step' obs obs' ε R) :
    ∀ (φ : PositiveFormula O) {x : X} {y : Y}, R x y → φ.Sat step obs x →
      (φ.inflate distance ε).Sat step' obs' y
  | atom _, _, _, related, holds => ⟨_, holds, bisimulation.1.close related⟩
  | and first second, _, _, related, holds =>
      ⟨sat_inflate bisimulation first related holds.1,
        sat_inflate bisimulation second related holds.2⟩
  | or first second, _, _, related, holds =>
      holds.elim (fun left => Or.inl (sat_inflate bisimulation first related left))
        fun right => Or.inr (sat_inflate bisimulation second related right)
  | dia body, _, _, related, ⟨x', moved, holds⟩ => by
      obtain ⟨y', moved', related'⟩ := bisimulation.1.forth related x' moved
      exact ⟨y', moved', sat_inflate bisimulation body related' holds⟩
  | box body, _, _, related, holds => fun y' moved => by
      obtain ⟨x', moved', related'⟩ := bisimulation.2.forth related y' moved
      exact sat_inflate bisimulation body related' (holds x' moved')

end Transfer

/-- **Inflations compose along the triangle inequality.** -/
theorem sat_inflate_inflate [AddCommMonoid D] [PartialOrder D] [IsOrderedAddMonoid D]
    {distance : O → O → D} (triangle : ∀ a b c, distance a c ≤ distance a b + distance b c)
    {ε δ : D} {step : X → X → Prop} {obs : X → O} :
    ∀ (φ : PositiveFormula O) {x : X},
      ((φ.inflate distance ε).inflate distance δ).Sat step obs x →
        (φ.inflate distance (ε + δ)).Sat step obs x
  | atom _, _, ⟨_, ⟨o', holds, close⟩, close'⟩ =>
      ⟨o', holds, (triangle _ _ _).trans (add_le_add close close')⟩
  | and first second, _, holds =>
      ⟨sat_inflate_inflate triangle first holds.1, sat_inflate_inflate triangle second holds.2⟩
  | or first second, _, holds =>
      holds.elim (fun left => Or.inl (sat_inflate_inflate triangle first left))
        fun right => Or.inr (sat_inflate_inflate triangle second right)
  | dia body, _, ⟨x', moved, holds⟩ => ⟨x', moved, sat_inflate_inflate triangle body holds⟩
  | box body, _, holds => fun x' moved => sat_inflate_inflate triangle body (holds x' moved)

end PositiveFormula

end Mettapedia.Cybernetics.ApproximateAdequacy
