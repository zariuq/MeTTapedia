import Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric

/-!
# Lumpings: a chain and its quotient are at distance zero

A map `view : S → C` of the states of a chain `P` onto the states of a chain `Q` is a **lumping**
(`IsLumping`) when, for every action and state `s`, the mass that the successor distribution of `s`
puts on each fibre of `view` is the mass of the successor distribution of `view s` in `Q` at that
class, and every observation of `s` is the observation of `view s`. This is the row compatibility of
strong lumpability (J. G. Kemeny and J. L. Snell), with the coarse chain supplied rather than built
from representatives, so no representative and no surjectivity is needed.

**The law.** Coupling bounds are the morphisms of a category whose objects are chains: they compose by
gluing (`CouplingBound.comp`). A lumping is a morphism of cost zero on its graph, so any coupling bound
of the quotient is a coupling bound of the chain, read through the map:

* `graphCoupling`: the successor distribution of `s` and the quotient's distribution at `view s` are
  coupled by sending each successor to its class; the coupling lives on the graph of `view`.
* `couplingBound_pullback`: a coupling bound of `Q` against any chain `R` gives one of `P` against
  `R`, by gluing the graph coupling in front of each coupling of `Q`; no discount restriction
  (`0 ≤ c`).
* `couplingBound_lift`: a coupling bound `m` of `Q` with itself gives the coupling bound
  `(s, t) ↦ m (view s) (view t)` of `P` with itself (pull back on both sides).
* `isProbabilisticBisimulation_graph`: the graph of a lumping is a probabilistic bisimulation between
  the two chains.
* `bisimulationMetric_lump`: **the metric is invariant under lumping**: at every discount
  `0 < c ≤ 1`, the distance of `s` and `t` in `P` is the distance of `view s` and `view t` in `Q`
  (from the tree's zero-distance theorem, triangle inequality and symmetry).

So a certificate of the quotient certifies the chain; its size and its check depend on the number of
classes, and the lumping itself is checked by sums of masses, without any product.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

open Mettapedia.Cybernetics.ApproximateAdequacy

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {A Atom S C T : Type*} [Fintype S] [Fintype C] [Fintype T] [DecidableEq C]

/-! ## Fibres and lumpings -/

/-- **The mass a weighting puts on the fibre of a class.** -/
def fibreMass (view : S → C) (μ : S → 𝕜) (k : C) : 𝕜 :=
  ∑ x ∈ Finset.univ.filter (fun x => view x = k), μ x

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype C] in
theorem fibreMass_eq_sum_ite (view : S → C) (μ : S → 𝕜) (k : C) :
    fibreMass view μ k = ∑ x, if view x = k then μ x else 0 :=
  Finset.sum_filter _ _

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype C] in
/-- **A point mass puts its mass on the fibre of its class.** -/
theorem fibreMass_dirac [DecidableEq S] (view : S → C) (x₀ : S) (k : C) :
    fibreMass view (dirac (𝕜 := 𝕜) x₀) k = if view x₀ = k then 1 else 0 := by
  rw [fibreMass_eq_sum_ite]
  simp only [dirac]
  rw [Finset.sum_eq_single x₀ (fun x _ other => by simp [other]) (fun missing =>
    absurd (Finset.mem_univ x₀) missing)]
  simp

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype C] in
/-- **Fibre masses are linear.** -/
theorem fibreMass_add (view : S → C) (μ ν : S → 𝕜) (k : C) :
    fibreMass view (fun x => μ x + ν x) k = fibreMass view μ k + fibreMass view ν k :=
  Finset.sum_add_distrib

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Fintype C] in
theorem fibreMass_mul_left (view : S → C) (q : 𝕜) (μ : S → 𝕜) (k : C) :
    fibreMass view (fun x => q * μ x) k = q * fibreMass view μ k :=
  (Finset.mul_sum _ _ _).symm

/-- **A lumping** of `P` onto `Q` along `view`: the successor distribution of every state puts on each
fibre the mass of the quotient's distribution at its class, and every observation of a state is that
of its class. -/
structure IsLumping (P : LabelledMarkovChain 𝕜 A Atom S) (Q : LabelledMarkovChain 𝕜 A Atom C)
    (view : S → C) : Prop where
  trans_eq : ∀ a s k, fibreMass view (P.trans a s) k = Q.trans a (view s) k
  observe_eq : ∀ i s, P.observe i s = Q.observe i (view s)

/-! ## The graph coupling -/

/-- **The graph coupling**: a weighting coupled with its fibre masses by sending each point to its
class. -/
def graphCoupling (view : S → C) {μ : S → 𝕜} {ν : C → 𝕜} (nonneg : ∀ x, 0 ≤ μ x)
    (fibres : ∀ k, fibreMass view μ k = ν k) : Coupling μ ν where
  weight x k := if view x = k then μ x else 0
  nonneg x k := by
    split_ifs
    · exact nonneg x
    · exact le_rfl
  sum_right x := by simp
  sum_left k := by rw [← fibres k, fibreMass_eq_sum_ite]

omit [IsStrictOrderedRing 𝕜] in
/-- **The graph coupling costs nothing** for a cost that vanishes on the graph. -/
theorem cost_graphCoupling (view : S → C) {μ : S → 𝕜} {ν : C → 𝕜} (nonneg : ∀ x, 0 ≤ μ x)
    (fibres : ∀ k, fibreMass view μ k = ν k) (M : 𝕜) :
    (graphCoupling view nonneg fibres).cost (fun x k => if view x = k then 0 else M) = 0 := by
  unfold Coupling.cost
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun k _ => ?_
  change (if view x = k then μ x else 0) * (if view x = k then 0 else M) = 0
  split_ifs <;> simp

/-! ## Coupling bounds pull back along a lumping -/

section Pullback

variable {P : LabelledMarkovChain 𝕜 A Atom S} {Q : LabelledMarkovChain 𝕜 A Atom C}
  {R : LabelledMarkovChain 𝕜 A Atom T} {view : S → C} {c : 𝕜}

/-- **Pullback**: a coupling bound of the quotient against any chain `R` is, read through the
lumping, a coupling bound of the chain against `R`, at every discount `0 ≤ c`. The coupling at
`(s, r)` is the graph coupling of `s` glued in front of the quotient's coupling at `(view s, r)`. -/
theorem couplingBound_pullback (lump : IsLumping P Q view) {m : C → T → 𝕜}
    (bound : CouplingBound Q R c m) (c_nonneg : 0 ≤ c) :
    CouplingBound P R c fun s r => m (view s) r where
  nonneg s r := bound.nonneg (view s) r
  observe_le i s r := by
    rw [lump.observe_eq i s]
    exact bound.observe_le i (view s) r
  step_le a s r := by
    obtain ⟨ω, le⟩ := bound.step_le a (view s) r
    let γ := graphCoupling view (P.isDistribution a s).nonneg (lump.trans_eq a s)
    have entry_le : ∀ k r', m k r' ≤ ∑ k', ∑ r'', m k' r'' := fun k r' =>
      (Finset.single_le_sum (fun r'' _ => bound.nonneg k r'') (Finset.mem_univ r')).trans
        (Finset.single_le_sum (f := fun k' => ∑ r'', m k' r'')
          (fun k' _ => Finset.sum_nonneg fun r'' _ => bound.nonneg k' r'') (Finset.mem_univ k))
    have triangle : ∀ x k r', m (view x) r' ≤
        (if view x = k then 0 else ∑ k', ∑ r'', m k' r'') + m k r' := by
      intro x k r'
      split_ifs with same
      · rw [same, zero_add]
      · linarith [entry_le (view x) r', bound.nonneg k r']
    have glued := γ.cost_glue_le ω triangle
    rw [cost_graphCoupling, zero_add] at glued
    exact ⟨γ.glue ω, (mul_le_mul_of_nonneg_left glued c_nonneg).trans le⟩

/-- **Lift**: a coupling bound `m` of the quotient with itself gives the coupling bound
`(s, t) ↦ m (view s) (view t)` of the chain with itself, at every discount `0 ≤ c`. -/
theorem couplingBound_lift (lump : IsLumping P Q view) {m : C → C → 𝕜}
    (bound : CouplingBound Q Q c m) (c_nonneg : 0 ≤ c) :
    CouplingBound P P c fun s t => m (view s) (view t) :=
  (couplingBound_pullback lump (couplingBound_pullback lump bound c_nonneg).swap c_nonneg).swap

omit [IsStrictOrderedRing 𝕜] in
/-- **The graph of a lumping is a probabilistic bisimulation** between the chain and its quotient. -/
theorem isProbabilisticBisimulation_graph (lump : IsLumping P Q view) :
    IsProbabilisticBisimulation P Q fun s k => view s = k := by
  intro s k related
  subst related
  refine ⟨fun i => lump.observe_eq i s, fun a =>
    ⟨graphCoupling view (P.isDistribution a s).nonneg (lump.trans_eq a s), fun x k positive => ?_⟩⟩
  by_contra other
  exact positive (if_neg other)

end Pullback

/-! ## The metric is invariant under lumping -/

section Invariance

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℝ A Atom S}
  {Q : LabelledMarkovChain ℝ A Atom C} {view : S → C} {c : ℝ}

/-- **A state is at distance zero from its class**, at every discount `0 < c ≤ 1`. -/
theorem bisimulationMetric_view_eq_zero (lump : IsLumping P Q view) (c_pos : 0 < c) (c_le : c ≤ 1)
    (s : S) : bisimulationMetric P Q c s (view s) = 0 :=
  (bisimulationMetric_eq_zero_iff c_pos c_le).mpr ⟨_, isProbabilisticBisimulation_graph lump, rfl⟩

/-- **The metric is invariant under lumping**: at every discount `0 < c ≤ 1`, the distance of two
states is the distance of their classes in the quotient. -/
theorem bisimulationMetric_lump (lump : IsLumping P Q view) (c_pos : 0 < c) (c_le : c ≤ 1)
    (s t : S) : bisimulationMetric P P c s t = bisimulationMetric Q Q c (view s) (view t) := by
  have zero := bisimulationMetric_view_eq_zero lump c_pos c_le
  have zero' : ∀ x, bisimulationMetric Q P c (view x) x = 0 := fun x => by
    rw [bisimulationMetric_comm (P := P) (Q := Q) c_pos.le c_le x (view x)]
    exact zero x
  apply le_antisymm
  · calc bisimulationMetric P P c s t
        ≤ bisimulationMetric P Q c s (view s) + bisimulationMetric Q P c (view s) t :=
          bisimulationMetric_triangle (P := P) (Q := Q) P c_pos.le c_le s (view s) t
      _ ≤ bisimulationMetric P Q c s (view s) +
            (bisimulationMetric Q Q c (view s) (view t) + bisimulationMetric Q P c (view t) t) :=
          add_le_add le_rfl
            (bisimulationMetric_triangle (P := Q) (Q := Q) P c_pos.le c_le (view s) (view t) t)
      _ = bisimulationMetric Q Q c (view s) (view t) := by rw [zero, zero']; ring
  · calc bisimulationMetric Q Q c (view s) (view t)
        ≤ bisimulationMetric Q P c (view s) s + bisimulationMetric P Q c s (view t) :=
          bisimulationMetric_triangle (P := Q) (Q := P) Q c_pos.le c_le (view s) s (view t)
      _ ≤ bisimulationMetric Q P c (view s) s +
            (bisimulationMetric P P c s t + bisimulationMetric P Q c t (view t)) :=
          add_le_add le_rfl
            (bisimulationMetric_triangle (P := P) (Q := P) Q c_pos.le c_le s t (view t))
      _ = bisimulationMetric P P c s t := by rw [zero, zero']; ring

end Invariance

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
