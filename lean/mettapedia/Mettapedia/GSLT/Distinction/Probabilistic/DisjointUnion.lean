import Mettapedia.GSLT.Distinction.Probabilistic.LogicalDistance

/-!
# The bisimulation metric between two chains is a logical distance

`LogicalDistance` proves the theorem of Desharnais, Gupta, Jagadeesan and
Panangaden for the states of one finite chain.  Between two chains `P` and `Q`
over the same actions and observables, the same holds through their disjoint
union (`union`):

* the union reads each side as that side does: every functional expression
  takes at `inl s` its value in `P` at `s`, and at `inr t` its value in `Q` at
  `t` (`eval_union_inl`, `eval_union_inr`);
* a coupling of the union's steps from `inl s` and `inr t` lives on the pairs
  `(inl x, inr y)` and restricts to a coupling of the two chains' steps with
  the same cost (`restrictCoupling`, `cost_restrictCoupling`), so the union's
  distance between the two copies is a coupling bound for `P` and `Q`
  (`bisimulationMetric_le_union`);
* the union's distance is its logical distance, and soundness closes the
  circle.

**The two-chain theorem** (`bisimulationMetric_eq_iSup`): at a discount
`0 ≤ c ≤ 1`, `bisimulationMetric P Q c s t` is the largest difference
`|φ_P(s) − φ_Q(t)|` over all functional expressions `φ`, and it is the union's
distance between the two copies (`bisimulationMetric_eq_union`).  At a positive
discount two states of different chains are probabilistically bisimilar
exactly when every functional expression takes the same value at them
(`probabilisticallyBisimilar_iff_eval_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.Cybernetics.ApproximateAdequacy
open FunctionalExpression

variable {A Atom S T : Type*} [Fintype S] [Fintype T]

/-! ## The disjoint union of two chains -/

section Union

variable (P : LabelledMarkovChain ℝ A Atom S) (Q : LabelledMarkovChain ℝ A Atom T)

/-- The steps of the disjoint union: each side steps as it does, and never
crosses. -/
def unionTrans (a : A) : S ⊕ T → S ⊕ T → ℝ
  | .inl s, .inl x => P.trans a s x
  | .inl _, .inr _ => 0
  | .inr _, .inl _ => 0
  | .inr t, .inr y => Q.trans a t y

/-- The observables of the disjoint union. -/
def unionObserve (i : Atom) : S ⊕ T → ℝ
  | .inl s => P.observe i s
  | .inr t => Q.observe i t

/-- **The disjoint union of two chains.** -/
def union : LabelledMarkovChain ℝ A Atom (S ⊕ T) where
  trans := unionTrans P Q
  isDistribution a state := by
    rcases state with s | t
    · refine ⟨fun target => ?_, ?_⟩
      · rcases target with x | y
        · exact (P.isDistribution a s).nonneg x
        · exact le_rfl
      · rw [Fintype.sum_sum_type]
        simp only [unionTrans, Finset.sum_const_zero, add_zero]
        exact (P.isDistribution a s).sum_eq_one
    · refine ⟨fun target => ?_, ?_⟩
      · rcases target with x | y
        · exact le_rfl
        · exact (Q.isDistribution a t).nonneg y
      · rw [Fintype.sum_sum_type]
        simp only [unionTrans, Finset.sum_const_zero, zero_add]
        exact (Q.isDistribution a t).sum_eq_one
  observe := unionObserve P Q

variable {P Q}

@[simp] theorem union_trans_inl_inl (a : A) (s x : S) :
    (union P Q).trans a (.inl s) (.inl x) = P.trans a s x := rfl

@[simp] theorem union_trans_inl_inr (a : A) (s : S) (y : T) :
    (union P Q).trans a (.inl s) (.inr y) = 0 := rfl

@[simp] theorem union_trans_inr_inl (a : A) (t : T) (x : S) :
    (union P Q).trans a (.inr t) (.inl x) = 0 := rfl

@[simp] theorem union_trans_inr_inr (a : A) (t y : T) :
    (union P Q).trans a (.inr t) (.inr y) = Q.trans a t y := rfl

@[simp] theorem union_observe_inl (i : Atom) (s : S) :
    (union P Q).observe i (.inl s) = P.observe i s := rfl

@[simp] theorem union_observe_inr (i : Atom) (t : T) :
    (union P Q).observe i (.inr t) = Q.observe i t := rfl

/-- **The left copy reads as the first chain.** -/
theorem eval_union_inl (c : ℝ) :
    ∀ (φ : FunctionalExpression ℝ A Atom) (s : S), φ.eval (union P Q) c (.inl s) = φ.eval P c s
  | .one, _ => rfl
  | .observe _, _ => rfl
  | .oneMinus φ, s => by
      simp only [eval]
      rw [eval_union_inl c φ s]
  | .min φ ψ, s => by
      simp only [eval]
      rw [eval_union_inl c φ s, eval_union_inl c ψ s]
  | .max φ ψ, s => by
      simp only [eval]
      rw [eval_union_inl c φ s, eval_union_inl c ψ s]
  | .sub φ q, s => by
      simp only [eval]
      rw [eval_union_inl c φ s]
  | .next a φ, s => by
      simp only [eval, expect]
      rw [Fintype.sum_sum_type]
      simp only [union_trans_inl_inl, union_trans_inl_inr, zero_mul, Finset.sum_const_zero,
        add_zero, eval_union_inl c φ]

/-- **The right copy reads as the second chain.** -/
theorem eval_union_inr (c : ℝ) :
    ∀ (φ : FunctionalExpression ℝ A Atom) (t : T), φ.eval (union P Q) c (.inr t) = φ.eval Q c t
  | .one, _ => rfl
  | .observe _, _ => rfl
  | .oneMinus φ, t => by
      simp only [eval]
      rw [eval_union_inr c φ t]
  | .min φ ψ, t => by
      simp only [eval]
      rw [eval_union_inr c φ t, eval_union_inr c ψ t]
  | .max φ ψ, t => by
      simp only [eval]
      rw [eval_union_inr c φ t, eval_union_inr c ψ t]
  | .sub φ q, t => by
      simp only [eval]
      rw [eval_union_inr c φ t]
  | .next a φ, t => by
      simp only [eval, expect]
      rw [Fintype.sum_sum_type]
      simp only [union_trans_inr_inl, union_trans_inr_inr, zero_mul, Finset.sum_const_zero,
        zero_add, eval_union_inr c φ]

/-! ## Couplings across the two copies -/

variable {a : A} {s : S} {t : T}

theorem weight_inr_left (ω : Coupling ((union P Q).trans a (.inl s)) ((union P Q).trans a (.inr t)))
    (y : T) (w : S ⊕ T) : ω.weight (.inr y) w = 0 :=
  ω.weight_eq_zero_of_left (x := .inr y) rfl w

theorem weight_inl_right (ω : Coupling ((union P Q).trans a (.inl s)) ((union P Q).trans a (.inr t)))
    (z : S ⊕ T) (x : S) : ω.weight z (.inl x) = 0 :=
  ω.weight_eq_zero_of_right (y := .inl x) rfl z

/-- **A coupling of the union's steps from the two copies restricts to a
coupling of the two chains' steps.** -/
def restrictCoupling (ω : Coupling ((union P Q).trans a (.inl s)) ((union P Q).trans a (.inr t))) :
    Coupling (P.trans a s) (Q.trans a t) where
  weight x y := ω.weight (.inl x) (.inr y)
  nonneg x y := ω.nonneg _ _
  sum_right x := by
    have row := ω.sum_right (.inl x)
    rw [Fintype.sum_sum_type] at row
    simp only [weight_inl_right ω, Finset.sum_const_zero, zero_add, union_trans_inl_inl] at row
    exact row
  sum_left y := by
    have column := ω.sum_left (.inr y)
    rw [Fintype.sum_sum_type] at column
    simp only [weight_inr_left ω, Finset.sum_const_zero, add_zero, union_trans_inr_inr] at column
    exact column

/-- **The restriction has the same cost.** -/
theorem cost_restrictCoupling
    (ω : Coupling ((union P Q).trans a (.inl s)) ((union P Q).trans a (.inr t)))
    (D : S ⊕ T → S ⊕ T → ℝ) :
    (restrictCoupling ω).cost (fun x y => D (.inl x) (.inr y)) = ω.cost D := by
  unfold Coupling.cost
  rw [Fintype.sum_sum_type]
  simp only [weight_inr_left ω, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_sum_type]
  simp only [weight_inl_right ω, zero_mul, Finset.sum_const_zero, zero_add]
  rfl

end Union

/-! ## The two-chain theorem -/

section Theorem

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℝ A Atom S}
  {Q : LabelledMarkovChain ℝ A Atom T} {c : ℝ}

/-- **The union's distance between the two copies is a coupling bound for the
two chains.** -/
theorem couplingBound_union (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    CouplingBound P Q c fun s t => bisimulationMetric (union P Q) (union P Q) c (.inl s) (.inr t) where
  nonneg s t := bisimulationMetric_nonneg c_nonneg c_le _ _
  observe_le i s t :=
    (couplingBound_bisimulationMetric (P := union P Q) (Q := union P Q) c_nonneg c_le).observe_le
      i (.inl s) (.inr t)
  step_le a s t := by
    obtain ⟨ω, le⟩ := (couplingBound_bisimulationMetric (P := union P Q) (Q := union P Q) c_nonneg
      c_le).step_le a (.inl s) (.inr t)
    exact ⟨restrictCoupling ω, by rw [cost_restrictCoupling]; exact le⟩

theorem bisimulationMetric_le_union (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s : S) (t : T) :
    bisimulationMetric P Q c s t ≤
      bisimulationMetric (union P Q) (union P Q) c (.inl s) (.inr t) :=
  bisimulationMetric_le (couplingBound_union c_nonneg c_le) c_nonneg s t

theorem bddAbove_cross (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s : S) (t : T) :
    BddAbove (Set.range fun φ : FunctionalExpression ℝ A Atom => |φ.eval P c s - φ.eval Q c t|) :=
  ⟨bisimulationMetric P Q c s t, by
    rintro _ ⟨φ, rfl⟩
    exact abs_eval_sub_le_bisimulationMetric c_nonneg c_le φ s t⟩

/-- **The two-chain theorem of Desharnais, Gupta, Jagadeesan and Panangaden**:
the bisimulation metric between states of two chains is the largest difference
of a functional expression. -/
theorem bisimulationMetric_eq_iSup (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s : S) (t : T) :
    bisimulationMetric P Q c s t =
      ⨆ φ : FunctionalExpression ℝ A Atom, |φ.eval P c s - φ.eval Q c t| := by
  have : Nonempty (FunctionalExpression ℝ A Atom) := ⟨.one⟩
  refine le_antisymm ?_ (ciSup_le fun φ => abs_eval_sub_le_bisimulationMetric c_nonneg c_le φ s t)
  refine (bisimulationMetric_le_union c_nonneg c_le s t).trans ?_
  rw [bisimulationMetric_eq_logicalDistance c_nonneg c_le]
  have : Nonempty (Set.univ : Set (FunctionalExpression ℝ A Atom)) := ⟨⟨.one, Set.mem_univ _⟩⟩
  refine ciSup_le fun φ => ?_
  rw [eval_union_inl, eval_union_inr]
  exact le_ciSup (bddAbove_cross c_nonneg c_le s t) φ.1

/-- **The union's distance between the two copies is the distance between the
two chains.** -/
theorem bisimulationMetric_eq_union (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s : S) (t : T) :
    bisimulationMetric P Q c s t =
      bisimulationMetric (union P Q) (union P Q) c (.inl s) (.inr t) := by
  refine le_antisymm (bisimulationMetric_le_union c_nonneg c_le s t) ?_
  rw [bisimulationMetric_eq_iSup c_nonneg c_le s t,
    bisimulationMetric_eq_logicalDistance c_nonneg c_le]
  have : Nonempty (Set.univ : Set (FunctionalExpression ℝ A Atom)) := ⟨⟨.one, Set.mem_univ _⟩⟩
  refine ciSup_le fun φ => ?_
  rw [eval_union_inl, eval_union_inr]
  exact le_ciSup (bddAbove_cross c_nonneg c_le s t) φ.1

/-- **Logical characterisation between two chains**: at a positive discount,
states of two chains are probabilistically bisimilar exactly when every
functional expression takes the same value at them. -/
theorem probabilisticallyBisimilar_iff_eval_eq (c_pos : 0 < c) (c_le : c ≤ 1) {s : S} {t : T} :
    ProbabilisticallyBisimilar P Q s t ↔
      ∀ φ : FunctionalExpression ℝ A Atom, φ.eval P c s = φ.eval Q c t := by
  constructor
  · exact fun bisimilar φ => bisimilar.eval_eq c φ
  · intro same
    have : Nonempty (FunctionalExpression ℝ A Atom) := ⟨.one⟩
    refine (bisimulationMetric_eq_zero_iff c_pos c_le).mp ?_
    rw [bisimulationMetric_eq_iSup c_pos.le c_le]
    have zero : (fun φ : FunctionalExpression ℝ A Atom => |φ.eval P c s - φ.eval Q c t|) =
        fun _ => 0 := by
      funext φ
      rw [same φ, sub_self, abs_zero]
    rw [zero, ciSup_const]

end Theorem

end Mettapedia.GSLT.Distinction.Probabilistic
