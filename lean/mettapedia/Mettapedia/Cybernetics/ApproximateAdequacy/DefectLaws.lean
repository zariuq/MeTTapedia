import Mettapedia.Cybernetics.MindWorldApproximation
import Mettapedia.Cybernetics.ApproximateAdequacy.Weighting
import Mettapedia.Cybernetics.ApproximateAdequacy.ApproxBisimulationLaws

/-!
# Laws of correspondence defects

A path correspondence (`MindWorldApproximateFunctor.PathCorrespondence`) maps
world paths to mind paths; its identity and composition defects measure how
far it is from a functor, in a geometry on the mind's arrows.

**What a defect certifies.**  A composition defect at most `δ` for the pair
`(P, Q)` says that the mind's arrow for the composite world path is within
`δ` of the composite of the mind's arrows for the parts: a model of a whole
process may be replaced by the composite of models of its parts.  Along a
chain of paths the replacement errors add, weighted by how much
post-composition in the mind expands distances
(`PathCorrespondence.dist_map_comp_comp_le`).  The defect compares mind arrows
with mind arrows; it never compares a mind state with a world state.

**How defects compose.**
* **Parallel composition adds defects** (`PathCorrespondence.compositionDefect_prod`,
  `PathCorrespondence.identityDefect_prod`), in the sum geometry on pairs.
* **Composite correspondences multiply and add**
  (`PathCorrespondence.compositionDefect_comp_le`,
  `PathCorrespondence.identityDefect_comp_le`, `BoundedPathCorrespondence.comp`): if `G` is
  `L`-Lipschitz on the arrows `F` produces, the composite's defect is at most
  `G`'s defect at the images plus `L` times `F`'s defect.  This is the law of
  approximate squares (`Mettapedia.GSLT.Scope.ApproxSquare.comp`).
* **Maximal and averaged defects.**  A bound on every sampled pair
  (`DefectBoundedOn`) implies the same bound on every weighted average
  (`DefectBoundedOn.averageDefect_le`); an averaged defect implies only a tail
  bound (`averageDefect_tail_le`) and no uniform bound
  (`exists_small_expectation_large_error`).
* **Averages compose only along the push-forward weighting**
  (`averageDefect_comp_le`): the composite's average is bounded by `G`'s
  average over the images of `F`'s sampled pairs, with today's weights, not
  under a weighting chosen for `G`.

**Independence from observation drift.**  Lane A's `Collapse` has zero defect
and unbounded drift.  Its `Fold` model tracks the doubling dynamics exactly,
at approximate-bisimulation precision `0` (`Fold.approxBisimilar_double`),
yet has composition defect `1` (`Fold.compositionDefect_eq`): the defect sees
an inconsistency among the mind's own process arrows that the step dynamics
never exercises.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.TypedValueGeometry.ValueGeometry

variable {V₁ V₂ : Type*}

/-- **The sum geometry** on pairs. -/
def sum (first : ValueGeometry V₁) (second : ValueGeometry V₂) : ValueGeometry (V₁ × V₂) where
  distance a b := first.distance a.1 b.1 + second.distance a.2 b.2
  nonnegative a b := add_nonneg (first.nonnegative _ _) (second.nonnegative _ _)
  self a := by rw [first.self, second.self, add_zero]
  triangle a b c := by
    have := first.triangle a.1 b.1 c.1
    have := second.triangle a.2 b.2 c.2
    linarith

end Mettapedia.GSLT.Dynamics.TypedValueGeometry.ValueGeometry

namespace Mettapedia.Cybernetics.MindWorldApproximateFunctor

open CategoryTheory
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

variable {World : Type*} [Category World] {Mind : Type*} [Category Mind]
  {Mind' : Type*} [Category Mind']

namespace PathCorrespondence

/-- **The composite of two path correspondences**, measured in the second
correspondence's geometry. -/
def comp (F : PathCorrespondence World Mind) (G : PathCorrespondence Mind Mind') :
    PathCorrespondence World Mind' where
  obj x := G.obj (F.obj x)
  map p := G.map (F.map p)
  geometry s t := G.geometry (F.obj s) (F.obj t)

/-- `G` is `L`-Lipschitz on the arrows `F` produces, from `F`'s geometry to
`G`'s. -/
def LipschitzOnImage (F : PathCorrespondence World Mind) (G : PathCorrespondence Mind Mind')
    (L : ℝ) : Prop :=
  ∀ (s t : World) (f g : F.obj s ⟶ F.obj t),
    (G.geometry (F.obj s) (F.obj t)).distance (G.map f) (G.map g) ≤
      L * (F.geometry s t).distance f g

variable {F : PathCorrespondence World Mind} {G : PathCorrespondence Mind Mind'} {L : ℝ}

/-- **The composition defect of a composite correspondence.** -/
theorem compositionDefect_comp_le (lipschitz : LipschitzOnImage F G L) {first middle last : World}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    (F.comp G).compositionDefect earlier later ≤
      G.compositionDefect (F.map earlier) (F.map later) +
        L * F.compositionDefect earlier later := by
  change (G.geometry (F.obj first) (F.obj last)).distance (G.map (F.map (earlier ≫ later)))
      (G.map (F.map earlier) ≫ G.map (F.map later)) ≤
    (G.geometry (F.obj first) (F.obj last)).distance (G.map (F.map earlier ≫ F.map later))
      (G.map (F.map earlier) ≫ G.map (F.map later)) +
      L * (F.geometry first last).distance (F.map (earlier ≫ later)) (F.map earlier ≫ F.map later)
  calc _ ≤ (G.geometry (F.obj first) (F.obj last)).distance (G.map (F.map (earlier ≫ later)))
          (G.map (F.map earlier ≫ F.map later)) +
        (G.geometry (F.obj first) (F.obj last)).distance (G.map (F.map earlier ≫ F.map later))
          (G.map (F.map earlier) ≫ G.map (F.map later)) :=
        (G.geometry _ _).triangle _ _ _
    _ ≤ L * (F.geometry first last).distance (F.map (earlier ≫ later))
          (F.map earlier ≫ F.map later) +
        (G.geometry (F.obj first) (F.obj last)).distance (G.map (F.map earlier ≫ F.map later))
          (G.map (F.map earlier) ≫ G.map (F.map later)) :=
        add_le_add (lipschitz first last _ _) le_rfl
    _ = _ := add_comm _ _

/-- **The identity defect of a composite correspondence.** -/
theorem identityDefect_comp_le (lipschitz : LipschitzOnImage F G L) (x : World) :
    (F.comp G).identityDefect x ≤ G.identityDefect (F.obj x) + L * F.identityDefect x := by
  change (G.geometry (F.obj x) (F.obj x)).distance (G.map (F.map (𝟙 x))) (𝟙 (G.obj (F.obj x))) ≤
    (G.geometry (F.obj x) (F.obj x)).distance (G.map (𝟙 (F.obj x))) (𝟙 (G.obj (F.obj x))) +
      L * (F.geometry x x).distance (F.map (𝟙 x)) (𝟙 (F.obj x))
  calc _ ≤ (G.geometry (F.obj x) (F.obj x)).distance (G.map (F.map (𝟙 x))) (G.map (𝟙 (F.obj x))) +
        (G.geometry (F.obj x) (F.obj x)).distance (G.map (𝟙 (F.obj x))) (𝟙 (G.obj (F.obj x))) :=
        (G.geometry _ _).triangle _ _ _
    _ ≤ L * (F.geometry x x).distance (F.map (𝟙 x)) (𝟙 (F.obj x)) +
        (G.geometry (F.obj x) (F.obj x)).distance (G.map (𝟙 (F.obj x))) (𝟙 (G.obj (F.obj x))) :=
        add_le_add (lipschitz x x _ _) le_rfl
    _ = _ := add_comm _ _

/-- **What a defect certifies along a chain**: composing the mind's arrows for
three paths predicts its arrow for the whole chain within the two defects,
when post-composition with the image of the last path is `L`-Lipschitz. -/
theorem dist_map_comp_comp_le (F : PathCorrespondence World Mind) {a b c d : World}
    (p : a ⟶ b) (q : b ⟶ c) (r : c ⟶ d) {L : ℝ}
    (lipschitz : ∀ f g : F.obj a ⟶ F.obj c,
      (F.geometry a d).distance (f ≫ F.map r) (g ≫ F.map r) ≤ L * (F.geometry a c).distance f g) :
    (F.geometry a d).distance (F.map (p ≫ q ≫ r)) (F.map p ≫ F.map q ≫ F.map r) ≤
      F.compositionDefect (p ≫ q) r + L * F.compositionDefect p q := by
  rw [← Category.assoc p q r, ← Category.assoc (F.map p) (F.map q) (F.map r)]
  exact ((F.geometry a d).triangle _ ((F.map (p ≫ q)) ≫ F.map r) _).trans
    (add_le_add le_rfl (lipschitz _ _))

/-! ### Parallel composition -/

section Parallel

variable {World₁ World₂ Mind₁ Mind₂ : Type*} [Category World₁] [Category World₂] [Category Mind₁]
  [Category Mind₂]

/-- **The product of two path correspondences**, measured in the sum
geometry. -/
def prod (F : PathCorrespondence World₁ Mind₁) (G : PathCorrespondence World₂ Mind₂) :
    PathCorrespondence (World₁ × World₂) (Mind₁ × Mind₂) where
  obj x := (F.obj x.1, G.obj x.2)
  map p := (F.map p.1, G.map p.2)
  geometry s t := (F.geometry s.1 t.1).sum (G.geometry s.2 t.2)

/-- **Parallel composition adds composition defects.** -/
theorem compositionDefect_prod (F : PathCorrespondence World₁ Mind₁)
    (G : PathCorrespondence World₂ Mind₂) {first middle last : World₁ × World₂}
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    (F.prod G).compositionDefect earlier later =
      F.compositionDefect earlier.1 later.1 + G.compositionDefect earlier.2 later.2 :=
  rfl

/-- **Parallel composition adds identity defects.** -/
theorem identityDefect_prod (F : PathCorrespondence World₁ Mind₁)
    (G : PathCorrespondence World₂ Mind₂) (x : World₁ × World₂) :
    (F.prod G).identityDefect x = F.identityDefect x.1 + G.identityDefect x.2 :=
  rfl

end Parallel

end PathCorrespondence

namespace BoundedPathCorrespondence

/-- **Bounded correspondences compose, multiplying and adding their
budgets.** -/
noncomputable def comp (F : BoundedPathCorrespondence World Mind)
    (G : BoundedPathCorrespondence Mind Mind') {L : ℝ} (L_nonneg : 0 ≤ L)
    (lipschitz : F.toPathCorrespondence.LipschitzOnImage G.toPathCorrespondence L) :
    BoundedPathCorrespondence World Mind' where
  toPathCorrespondence := F.toPathCorrespondence.comp G.toPathCorrespondence
  identityBudget x := G.identityBudget (F.obj x) + L * F.identityBudget x
  compositionBudget p q := G.compositionBudget (F.map p) (F.map q) + L * F.compositionBudget p q
  identityBudget_nonnegative x :=
    add_nonneg (G.identityBudget_nonnegative _)
      (mul_nonneg L_nonneg (F.identityBudget_nonnegative x))
  compositionBudget_nonnegative p q :=
    add_nonneg (G.compositionBudget_nonnegative _ _)
      (mul_nonneg L_nonneg (F.compositionBudget_nonnegative p q))
  identity_bounded x :=
    (PathCorrespondence.identityDefect_comp_le lipschitz x).trans
      (add_le_add (G.identity_bounded _)
        (mul_le_mul_of_nonneg_left (F.identity_bounded x) L_nonneg))
  composition_bounded p q :=
    (PathCorrespondence.compositionDefect_comp_le lipschitz p q).trans
      (add_le_add (G.composition_bounded _ _)
        (mul_le_mul_of_nonneg_left (F.composition_bounded p q) L_nonneg))

end BoundedPathCorrespondence

end Mettapedia.Cybernetics.MindWorldApproximateFunctor

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open CategoryTheory
open Mettapedia.Cybernetics.MindWorldApproximateFunctor
open Mettapedia.Cybernetics.MindWorldApproximation

variable {World : Type*} [Category World] {Mind : Type*} [Category Mind]
  {Mind' : Type*} [Category Mind'] {ι : Type*}

/-! ## Maximal and averaged defects -/

/-- The image of a composable pair under a correspondence. -/
def ComposablePair.map (F : PathCorrespondence World Mind) (pair : ComposablePair World) :
    ComposablePair Mind :=
  ⟨F.obj pair.first, F.obj pair.middle, F.obj pair.last, F.map pair.earlier, F.map pair.later⟩

/-- The composition defect at a composable pair. -/
noncomputable def pairDefect (F : PathCorrespondence World Mind) (pair : ComposablePair World) :
    ℝ :=
  F.compositionDefect pair.earlier pair.later

/-- **The averaged defect** of sampled pairs under a weighting (the goal-weighted
average of the mind–world correspondence principle, normalised). -/
noncomputable def averageDefect (F : PathCorrespondence World Mind) (w : FiniteWeighting ℝ ι)
    (pairs : ι → ComposablePair World) : ℝ :=
  w.expectation fun i => pairDefect F (pairs i)

/-- **The maximal defect bound** on a finite sample. -/
def DefectBoundedOn (F : PathCorrespondence World Mind) (pairs : ι → ComposablePair World)
    (sample : Finset ι) (δ : ℝ) : Prop :=
  ∀ i ∈ sample, pairDefect F (pairs i) ≤ δ

/-- A maximal bound on the support implies the averaged bound. -/
theorem DefectBoundedOn.averageDefect_le {F : PathCorrespondence World Mind}
    {w : FiniteWeighting ℝ ι} {pairs : ι → ComposablePair World} {δ : ℝ}
    (bounded : DefectBoundedOn F pairs w.support δ) : averageDefect F w pairs ≤ δ :=
  FiniteWeighting.expectation_le_of_le bounded

/-- **An averaged defect gives only a tail bound**: the weight of the sampled
pairs with defect at least `t` is at most the average over `t`. -/
theorem averageDefect_tail_le (F : PathCorrespondence World Mind) (w : FiniteWeighting ℝ ι)
    (pairs : ι → ComposablePair World) {t : ℝ} (t_pos : 0 < t) :
    w.tailMass (fun i => pairDefect F (pairs i)) t ≤ averageDefect F w pairs / t :=
  FiniteWeighting.tailMass_le_div
    (fun _ _ => PathCorrespondence.compositionDefect_nonnegative F _ _)
    t_pos

/-- **An exact correspondence has averaged defect `0` under every weighting.** -/
theorem averageDefect_eq_zero_of_exact {F : PathCorrespondence World Mind} (exact : F.Exact)
    (w : FiniteWeighting ℝ ι) (pairs : ι → ComposablePair World) : averageDefect F w pairs = 0 :=
  Finset.sum_eq_zero fun i _ => by
    change w.weight i * F.compositionDefect (pairs i).earlier (pairs i).later = 0
    rw [F.compositionDefect_eq_zero_of_exact exact, mul_zero]

/-- **Averages compose along the push-forward weighting.** -/
theorem averageDefect_comp_le {F : PathCorrespondence World Mind}
    {G : PathCorrespondence Mind Mind'}
    {L : ℝ} (lipschitz : F.LipschitzOnImage G L) (w : FiniteWeighting ℝ ι)
    (pairs : ι → ComposablePair World) :
    averageDefect (F.comp G) w pairs ≤
      averageDefect G w (fun i => ComposablePair.map F (pairs i)) +
        L * averageDefect F w pairs := by
  unfold averageDefect FiniteWeighting.expectation
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i member => ?_
  have pointwise := PathCorrespondence.compositionDefect_comp_le lipschitz (pairs i).earlier
    (pairs i).later
  calc w.weight i * pairDefect (F.comp G) (pairs i)
      ≤ w.weight i * (pairDefect G (ComposablePair.map F (pairs i)) + L * pairDefect F (pairs i)) :=
        mul_le_mul_of_nonneg_left pointwise (w.nonneg i member)
    _ = _ := by ring

/-! ## Separation from drift: `Fold` -/

namespace Fold

open Mettapedia.Cybernetics.MindWorldApproximation.Fold

/-- The model of doubling is doubling. -/
theorem model_two : model 2 = fun y => (2 : ℕ) • y := by
  funext y
  simp [model]

/-- **The doubling dynamics is tracked exactly**: every state is approximately
bisimilar to itself at precision `0`, the world stepping by doubling and the
mind by its model of doubling. -/
theorem approxBisimilar_double (x : ℝ) :
    ApproxBisimilar dist (fun a b => (2 : ℕ) • a = b) (fun a b => model 2 a = b) id id 0 x x := by
  rw [model_two]
  exact ⟨Eq, isApproxBisimulation_eq fun o => (dist_self o).le, rfl⟩

/-- **Drift `0`, defect `1`.** -/
theorem drift_zero_defect_one :
    (∀ x : ℝ, ApproxBisimilar dist (fun a b => (2 : ℕ) • a = b) (fun a b => model 2 a = b) id id 0
      x x) ∧
      correspondence.toPathCorrespondence.compositionDefect double double = 1 :=
  ⟨approxBisimilar_double, compositionDefect_eq⟩

end Fold

end Mettapedia.Cybernetics.ApproximateAdequacy
