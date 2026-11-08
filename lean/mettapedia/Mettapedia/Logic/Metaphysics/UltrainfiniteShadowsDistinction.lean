import Mathlib.SetTheory.Cardinal.Finite
import Mettapedia.Cybernetics.DistinctionCalculus.Basic
import Mettapedia.Logic.StoneGunkDuality
import Mettapedia.Logic.Metaphysics.UltrainfiniteShadowsCantor

/-!
# Observers of the distinction calculus see finite shadows

A `Tolerance` of the distinction calculus is an observer: `Indistinguishable` is zero distance and
`Apart` is a witnessed distinction. Under the metric law zero distance is an equivalence, and the
observer's quotient is `Quotient (a.zeroSetoid metric)`.

* **Open classes never single out a point**, on any carrier without isolated points
  (`exists_ne_indistinguishable_of_isOpen`): Cantor space (`cantor_not_isOpen_singleton`), or the
  Stone space of a gunky algebra (`stoneSpace_not_isOpen_singleton`). On a gunky carrier finitely many
  distinctions never single out a point (`gunky_exists_ne_of_finite_distinctions`).
* **Finite resolution on Cantor space.** An observer that draws no distinction below depth `n`
  (`ResolvesWithin a n`) has infinite classes (`ResolvesWithin.infinite_class`) and, if metric, a
  finite quotient with at most `2 ^ n` classes (`ResolvesWithin.finite_quotient`). For a metric
  observer, finite resolution is exactly openness of its classes
  (`exists_resolvesWithin_iff_isOpen_classes`; compactness gives the uniform depth).
* **Separating a point needs distinctions at every depth**
  (`exists_apart_of_class_eq_singleton`, `not_resolvesWithin_of_class_eq_singleton`).

Controls: the depth observer `Tolerance.ofReport (depth n)` resolves within `n`, with at most
`2 ^ n` classes; the identity observer separates every point and resolves within no depth; the
observer "is it `f`?" has two classes, and its class `{f}` is a singleton that is not open
(`pointObserver_class_eq`), so finitely many classes alone do not prevent singletons.

The quotient needs the metric law: without it `Indistinguishable` need not be transitive, and the
statements about classes that hold for every tolerance are `ResolvesWithin.infinite_class` and
`exists_ne_indistinguishable_of_isOpen`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Set Function Mettapedia.Cybernetics.DistinctionCalculus Mettapedia.Foundations.Gunk

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## Open classes on a carrier without isolated points -/

/-- **An observer class that is open is never a single point**, on any space without isolated
points. -/
theorem exists_ne_indistinguishable_of_isOpen {X : Type*} [TopologicalSpace X]
    (noIsolated : ∀ x : X, ¬ IsOpen ({x} : Set X)) (a : Tolerance X R) {x : X}
    (hx : IsOpen {y | a.Indistinguishable x y}) : ∃ y ≠ x, a.Indistinguishable x y := by
  by_contra h
  apply noIsolated x
  have hcl : {y | a.Indistinguishable x y} = {x} := by
    ext y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · by_contra hne
      exact h ⟨y, hne, hy⟩
    · rw [Set.mem_singleton_iff.1 hy]
      exact a.distance_self x
  rw [← hcl]
  exact hx

/-- A report that is continuous into a discrete space gives an observer with open classes. -/
theorem isOpen_indistinguishable_ofReport {X W : Type*} [TopologicalSpace X] [TopologicalSpace W]
    [DiscreteTopology W] [DecidableEq W] {report : X → W} (h : Continuous report) (x : X) :
    IsOpen {y | (Tolerance.ofReport report R).Indistinguishable x y} := by
  have hcl : {y | (Tolerance.ofReport report R).Indistinguishable x y} = report ⁻¹' {report x} :=
    Set.ext fun y => (Tolerance.ofReport_indistinguishable (R := R) report x y).trans eq_comm
  rw [hcl]
  exact (isOpen_discrete _).preimage h

/-- The Stone space of a gunky algebra has no isolated point. -/
theorem stoneSpace_not_isOpen_singleton {B : Type*} [BooleanAlgebra B] (hg : IsGunky B)
    (p : StoneSpace B) : ¬ IsOpen ({p} : Set (StoneSpace B)) := by
  have hperf := isGunky_iff_perfect_stoneSpace.1 hg
  rw [perfectSpace_iff_forall_not_isolated] at hperf
  intro hopen
  exact (hperf p).ne' ((isOpen_singleton_iff_punctured_nhds p).1 hopen)

/-- **On a gunky carrier, finitely many distinctions never single out a point**: for finitely many
elements of a gunky algebra, every point of its Stone space shares its answers with another
point. -/
theorem gunky_exists_ne_of_finite_distinctions {B : Type*} [BooleanAlgebra B] (hg : IsGunky B)
    (S : Finset B) (p : StoneSpace B) :
    ∃ q ≠ p, ∀ a ∈ S, (q ∈ (stoneRepr B a : Set (StoneSpace B)) ↔
      p ∈ (stoneRepr B a : Set (StoneSpace B))) := by
  classical
  obtain ⟨q, hqp, hq⟩ := exists_ne_of_finite_distinctions (stoneSpace_not_isOpen_singleton hg)
    (S.image fun a => (stoneRepr B a : Set (StoneSpace B))) (fun C hC => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hC
      exact (stoneRepr B a).isClopen) p
  exact ⟨q, hqp, fun a ha => hq _ (Finset.mem_image_of_mem _ ha)⟩

/-- On a gunky carrier, an observer reporting continuously into a discrete space never singles
out a point. -/
theorem gunky_exists_ne_ofReport {B : Type*} [BooleanAlgebra B] (hg : IsGunky B) {W : Type*}
    [TopologicalSpace W] [DiscreteTopology W] [DecidableEq W] {report : StoneSpace B → W}
    (h : Continuous report) (p : StoneSpace B) :
    ∃ q ≠ p, (Tolerance.ofReport report R).Indistinguishable p q :=
  exists_ne_indistinguishable_of_isOpen (stoneSpace_not_isOpen_singleton hg) _
    (isOpen_indistinguishable_ofReport h p)

/-! ## Finite resolution on Cantor space -/

/-- An observer on Cantor space **resolves within depth `n`** when it draws no distinction between
points with the same depth-`n` shadow. -/
def ResolvesWithin (a : Tolerance (ℕ → Bool) R) (n : ℕ) : Prop :=
  ∀ f g, depth n f = depth n g → a.Indistinguishable f g

/-- An observer of depth-`n` patterns, read through the depth-`n` shadow, resolves within `n`. -/
theorem resolvesWithin_pullback {n : ℕ} (b : Tolerance (Fin n → Bool) R) :
    ResolvesWithin (b.pullback (depth n)) n := by
  intro f g h
  show (b.pullback (depth n)).distance f g = 0
  rw [Tolerance.distance_pullback, h]
  exact b.distance_self _

/-- **Each class of a finite-resolution observer is infinite.** -/
theorem ResolvesWithin.infinite_class {a : Tolerance (ℕ → Bool) R} {n : ℕ}
    (h : ResolvesWithin a n) (f : ℕ → Bool) : {g | a.Indistinguishable f g}.Infinite :=
  (depth_fibre_infinite (depth n f)).mono fun g (hg : depth n g = depth n f) => h f g hg.symm

theorem ResolvesWithin.exists_ne {a : Tolerance (ℕ → Bool) R} {n : ℕ}
    (h : ResolvesWithin a n) (f : ℕ → Bool) : ∃ g ≠ f, a.Indistinguishable f g := by
  obtain ⟨g, hgf, hg⟩ := exists_ne_depth_eq f n
  exact ⟨g, hgf, h f g hg.symm⟩

/-- **A metric observer of finite resolution has a finite quotient**, with at most `2 ^ n`
classes. -/
theorem ResolvesWithin.finite_quotient {a : Tolerance (ℕ → Bool) R} (metric : a.Metric) {n : ℕ}
    (h : ResolvesWithin a n) :
    Finite (Quotient (a.zeroSetoid metric)) ∧
      Nat.card (Quotient (a.zeroSetoid metric)) ≤ 2 ^ n := by
  have hs : Surjective fun p : Fin n → Bool =>
      Quotient.mk (a.zeroSetoid metric) (splice p fun _ => false) := by
    intro q
    obtain ⟨f, rfl⟩ := Quotient.exists_rep q
    exact ⟨depth n f, Quotient.sound (h _ _ (depth_splice _ _))⟩
  refine ⟨Finite.of_surjective _ hs, (Nat.card_le_card_of_surjective _ hs).trans ?_⟩
  simp [Nat.card_eq_fintype_card]

/-- **For a metric observer on Cantor space, finite resolution is exactly openness of its
classes.** The uniform depth comes from compactness. -/
theorem exists_resolvesWithin_iff_isOpen_classes {a : Tolerance (ℕ → Bool) R}
    (metric : a.Metric) :
    (∃ n, ResolvesWithin a n) ↔ ∀ f, IsOpen {g | a.Indistinguishable f g} := by
  refine ⟨fun ⟨n, hn⟩ f => isOpen_iff_forall_mem_open.2 fun g hg =>
    ⟨depth n ⁻¹' {depth n g}, fun k (hk : depth n k = depth n g) => ?_,
      (isOpen_discrete _).preimage (continuous_depth n),
      Set.mem_preimage.2 (Set.mem_singleton _)⟩,
    fun ho => exists_depth_of_isOpen_classes (a.zeroSetoid metric) ho⟩
  exact (a.zeroSetoid metric).iseqv.trans hg (hn g k hk.symm)

/-- **Separating a point needs distinctions at every depth.** If an observer's class of `f` is
`{f}`, then at every depth some point with the same shadow as `f` is apart from it. -/
theorem exists_apart_of_class_eq_singleton {a : Tolerance (ℕ → Bool) R} {f : ℕ → Bool}
    (hf : ∀ g, a.Indistinguishable f g → g = f) (n : ℕ) :
    ∃ g, depth n g = depth n f ∧ a.Apart f g := by
  obtain ⟨g, hgf, hg⟩ := exists_ne_depth_eq f n
  refine ⟨g, hg, ?_⟩
  by_contra hna
  exact hgf (hf g ((a.not_apart_iff_indistinguishable f g).1 hna))

theorem not_resolvesWithin_of_class_eq_singleton {a : Tolerance (ℕ → Bool) R} {f : ℕ → Bool}
    (hf : ∀ g, a.Indistinguishable f g → g = f) (n : ℕ) : ¬ ResolvesWithin a n := fun h =>
  let ⟨_, hgf, hg⟩ := h.exists_ne f
  hgf (hf _ hg)

/-! ## Controls -/

/-- **Positive control.** The depth observer resolves within `n`, is metric, and has at most
`2 ^ n` classes, each infinite. -/
theorem depthObserver_control (n : ℕ) :
    ResolvesWithin (Tolerance.ofReport (depth n) R) n ∧
      Nat.card (Quotient ((Tolerance.ofReport (depth n) R).zeroSetoid
        (Tolerance.ofReport_metric _))) ≤ 2 ^ n ∧
      ∀ f, {g | (Tolerance.ofReport (depth n) R).Indistinguishable f g}.Infinite := by
  have hres : ResolvesWithin (Tolerance.ofReport (depth n) R) n := fun f g h =>
    (Tolerance.ofReport_indistinguishable (R := R) (depth n) f g).2 h
  exact ⟨hres, (hres.finite_quotient _).2, hres.infinite_class⟩

open Classical in
/-- **Negative control.** The identity observer separates every point, so it resolves within no
depth. -/
theorem identityObserver_not_resolvesWithin (n : ℕ) :
    ¬ ResolvesWithin (Tolerance.ofReport (id : (ℕ → Bool) → (ℕ → Bool)) R) n :=
  not_resolvesWithin_of_class_eq_singleton (f := fun _ => false) (fun g hg =>
    ((Tolerance.ofReport_indistinguishable (R := R) id _ g).1 hg).symm) n

open Classical in
/-- **Negative control.** The observer "is it `f`?" has two classes, and its class of `f` is the
singleton `{f}`, which is not open: finitely many classes alone do not prevent singletons. -/
theorem pointObserver_class_eq (f : ℕ → Bool) :
    {g | (Tolerance.ofReport (fun g : ℕ → Bool => decide (g = f)) R).Indistinguishable f g} = {f} ∧
      ¬ IsOpen {g | (Tolerance.ofReport (fun g : ℕ → Bool => decide (g = f)) R).Indistinguishable
        f g} := by
  have hcl : {g | (Tolerance.ofReport (fun g : ℕ → Bool => decide (g = f)) R).Indistinguishable
      f g} = {f} := by
    ext g
    rw [Set.mem_ofPred_eq, Tolerance.ofReport_indistinguishable, Set.mem_singleton_iff]
    by_cases hg : g = f <;> simp [hg]
  refine ⟨hcl, ?_⟩
  rw [hcl]
  exact cantor_not_isOpen_singleton f

end Mettapedia.Logic.Metaphysics.Ultrainfinite
