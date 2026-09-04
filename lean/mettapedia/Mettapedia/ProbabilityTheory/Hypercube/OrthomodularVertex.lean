import Mettapedia.ProbabilityTheory.Hypercube.UnifiedTheory
import Mathlib.Data.Complex.Basic

/-!
# Inhabiting the quantum vertex: MO2, orthomodularity, and interference

The hypercube's quantum vertex (`DistributivityAxis.orthomodular`,
`ProbabilityVertex.quantum`) has until now been a label.  This module
inhabits it:

* `OrthomodularLattice` — the class Mathlib lacks: an ortholattice whose
  complement satisfies the orthomodular law `x ≤ y → y = x ⊔ (xᵒ ⊓ y)`.
  `ofBooleanAlgebra` shows every Boolean algebra qualifies — the classical
  vertex embeds, so the axis is genuinely a specialization edge.
* `MO2` — the minimal quantum logic: two incompatible binary questions
  (Foulis's firefly box with two windows; a qubit measured in two bases).
  Six elements; all laws by `decide`.  `MO2_orthomodular` inhabits the
  vertex; `MO2_not_distributive` is the strictness witness: the classical
  law genuinely fails.
* `bornMO2` — complex amplitudes `(ψ₁, ψ₂)` induce a valuation: the two
  blocks read out `‖ψᵢ‖²` and `‖ψ₁ ± ψ₂‖²/2` (computational and rotated
  basis).  `bornUncertainty` packages it as an `UncertaintyAlgebra MO2` —
  the vertex's first valuation, with normalization by the parallelogram law.
* **`interference`** — two states with identical block-`a` statistics and
  different block-`b` statistics: the phase carried by ℂ is real information
  that no per-block probability sees.

## Application to CeTTa Prime's V/value/choice channel

If Prime's V channel over choice branches carries ℂ (amplitudes) with
branch-aggregation `+` and readout `normSq` only at observation boundaries,
then: (1) each observer's compatible query set is a Boolean block; (2)
incompatible observers (different readout bases, different observation
scopes) paste into an orthomodular question lattice — this module's shape;
(3) `interference` is the design justification: a phase-carrying V supports
observables that no per-branch probability channel can express; (4) the
absence of a global valuation across blocks is the same no-global-view
discipline the anti-magic/ε-visibility results already impose — a
complete-bag observer of amplitudes would destroy exactly the information
that makes the ℂ carrier worth having.  Whether Prime ever selects this
vertex is a profile decision; the mathematics of the option is now real.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.Hypercube.OrthomodularVertex

open Mettapedia.ProbabilityTheory.Hypercube.UnifiedTheory

/-! ## The class Mathlib lacks -/

/-- An orthomodular lattice: bounded lattice with an order-reversing
involutive complement satisfying the orthomodular law. -/
class OrthomodularLattice (α : Type*) extends Lattice α, BoundedOrder α where
  oc : α → α
  oc_oc : ∀ x, oc (oc x) = x
  oc_antitone : ∀ x y, x ≤ y → oc y ≤ oc x
  inf_oc : ∀ x, x ⊓ oc x = ⊥
  sup_oc : ∀ x, x ⊔ oc x = ⊤
  orthomodular : ∀ x y, x ≤ y → y = x ⊔ (oc x ⊓ y)

/-- Every Boolean algebra is orthomodular: the classical vertex embeds. -/
@[reducible] def OrthomodularLattice.ofBooleanAlgebra (α : Type*) [BooleanAlgebra α] :
    OrthomodularLattice α where
  oc := compl
  oc_oc := compl_compl
  oc_antitone _ _ h := compl_le_compl h
  inf_oc _ := inf_compl_eq_bot
  sup_oc _ := sup_compl_eq_top
  orthomodular x y h := by
    rw [sup_inf_left, sup_compl_eq_top, top_inf_eq, sup_eq_right.mpr h]

/-! ## MO2: two incompatible binary questions -/

/-- The minimal quantum logic: `a/a'` one binary question, `b/b'` an
incompatible one.  Foulis's firefly box; a qubit with two bases. -/
inductive MO2 : Type where
  | bot | top | a | a' | b | b'
deriving DecidableEq, Repr, Fintype

namespace MO2

def leB : MO2 → MO2 → Bool
  | .bot, _ => true
  | _, .top => true
  | .a, .a => true
  | .a', .a' => true
  | .b, .b => true
  | .b', .b' => true
  | _, _ => false

instance : LE MO2 := ⟨fun x y => leB x y = true⟩

instance : DecidableRel ((· ≤ ·) : MO2 → MO2 → Prop) :=
  fun x y => inferInstanceAs (Decidable (leB x y = true))

instance : PartialOrder MO2 where
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide

def supM : MO2 → MO2 → MO2
  | .bot, y => y
  | x, .bot => x
  | .top, _ => .top
  | _, .top => .top
  | .a, .a => .a
  | .a', .a' => .a'
  | .b, .b => .b
  | .b', .b' => .b'
  | _, _ => .top

def infM : MO2 → MO2 → MO2
  | .top, y => y
  | x, .top => x
  | .bot, _ => .bot
  | _, .bot => .bot
  | .a, .a => .a
  | .a', .a' => .a'
  | .b, .b => .b
  | .b', .b' => .b'
  | _, _ => .bot

instance : Lattice MO2 where
  sup := supM
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf := infM
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : BoundedOrder MO2 where
  top := .top
  le_top := by decide
  bot := .bot
  bot_le := by decide

def ocM : MO2 → MO2
  | .bot => .top
  | .top => .bot
  | .a => .a'
  | .a' => .a
  | .b => .b'
  | .b' => .b

/-- **The quantum vertex is inhabited**: MO2 is an orthomodular lattice. -/
instance : OrthomodularLattice MO2 where
  oc := ocM
  oc_oc := by decide
  oc_antitone := by decide
  inf_oc := by decide
  sup_oc := by decide
  orthomodular := by decide

/-- **Strictness of the axis**: the distributive law genuinely fails —
`a ⊓ (b ⊔ b') = a` but `(a ⊓ b) ⊔ (a ⊓ b') = ⊥`. -/
theorem not_distributive :
    ¬ ∀ x y z : MO2, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  decide

end MO2

/-! ## The Born valuation from complex amplitudes -/

/-- A state `(ψ₁, ψ₂)` read in the computational basis on the `a` block and
in the rotated basis on the `b` block. -/
noncomputable def bornMO2 (ψ₁ ψ₂ : ℂ) : MO2 → ℝ
  | .bot => 0
  | .top => 1
  | .a => Complex.normSq ψ₁
  | .a' => Complex.normSq ψ₂
  | .b => Complex.normSq (ψ₁ + ψ₂) / 2
  | .b' => Complex.normSq (ψ₁ - ψ₂) / 2

theorem parallelogram (x y : ℂ) :
    Complex.normSq (x + y) + Complex.normSq (x - y) =
      2 * (Complex.normSq x + Complex.normSq y) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

theorem bornMO2_nonneg (ψ₁ ψ₂ : ℂ) : ∀ p, 0 ≤ bornMO2 ψ₁ ψ₂ p := by
  intro p
  cases p
  · exact le_refl 0
  · exact zero_le_one
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)
  · exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)

theorem bornMO2_le_one (ψ₁ ψ₂ : ℂ)
    (h : Complex.normSq ψ₁ + Complex.normSq ψ₂ = 1) :
    ∀ p, bornMO2 ψ₁ ψ₂ p ≤ 1 := by
  intro p
  cases p
  · simp [bornMO2]
  · simp [bornMO2]
  · simp only [bornMO2]
    linarith [Complex.normSq_nonneg ψ₂]
  · simp only [bornMO2]
    linarith [Complex.normSq_nonneg ψ₁]
  · simp only [bornMO2]
    linarith [parallelogram ψ₁ ψ₂, Complex.normSq_nonneg (ψ₁ - ψ₂)]
  · simp only [bornMO2]
    linarith [parallelogram ψ₁ ψ₂, Complex.normSq_nonneg (ψ₁ + ψ₂)]

/-- **The vertex's first valuation**: amplitudes induce an uncertainty
algebra on MO2 — block-wise Born probabilities, coherent, with no global
sample space behind them. -/
noncomputable def bornUncertainty (ψ₁ ψ₂ : ℂ)
    (h : Complex.normSq ψ₁ + Complex.normSq ψ₂ = 1) :
    UncertaintyAlgebra MO2 where
  lower := bornMO2 ψ₁ ψ₂
  upper := bornMO2 ψ₁ ψ₂
  lower_le_upper _ := le_refl _
  lower_mono := by
    intro p q hpq
    cases p <;> cases q <;>
      first
        | exact le_refl _
        | exact absurd hpq (by decide)
        | exact bornMO2_nonneg ψ₁ ψ₂ _
        | exact bornMO2_le_one ψ₁ ψ₂ h _
  lower_bot := rfl
  upper_top := rfl

/-! ## Interference: why a ℂ-valued V channel carries real information -/

theorem ψplus_normalized :
    Complex.normSq (Complex.ofReal (3/5)) +
      Complex.normSq (Complex.ofReal (4/5)) = 1 := by
  simp
  norm_num

theorem ψminus_normalized :
    Complex.normSq (Complex.ofReal (3/5)) +
      Complex.normSq (Complex.ofReal (-(4/5))) = 1 := by
  simp
  norm_num

/-- **Interference.**  Two states agree on every `a`-block probability and
differ on the `b` block: the relative phase is information no per-block
(per-branch) probability channel sees.  This is the formal justification for
a ℂ-valued V channel with readout only at observation boundaries. -/
theorem interference :
    bornMO2 (Complex.ofReal (3/5)) (Complex.ofReal (4/5)) .a =
      bornMO2 (Complex.ofReal (3/5)) (Complex.ofReal (-(4/5))) .a ∧
    bornMO2 (Complex.ofReal (3/5)) (Complex.ofReal (4/5)) .a' =
      bornMO2 (Complex.ofReal (3/5)) (Complex.ofReal (-(4/5))) .a' ∧
    bornMO2 (Complex.ofReal (3/5)) (Complex.ofReal (4/5)) .b ≠
      bornMO2 (Complex.ofReal (3/5)) (Complex.ofReal (-(4/5))) .b := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [bornMO2]
  · simp only [bornMO2, ← Complex.ofReal_add, Complex.normSq_ofReal]
    norm_num

#print axioms MO2.not_distributive
#print axioms interference
#print axioms parallelogram

end Mettapedia.ProbabilityTheory.Hypercube.OrthomodularVertex
