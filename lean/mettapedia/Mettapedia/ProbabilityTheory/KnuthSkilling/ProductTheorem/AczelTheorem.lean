import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.Basic

/-!
# Appendix B: Distributive Tensors Are Scaled Multiplication

This file is an **alternative** Appendix B route that avoids postulating a global Aczél-style
representation theorem for `⊗` on `(0,∞)`.

K&S phrase the key step as “apply Appendix A again” to the tensor operation `⊗`.
In Lean, our Appendix A representation theorem for `⊕` is packaged by
`AdditiveOrderIsoRep`, but it assumes a monoid identity that is the minimum element
(`ident_le`), which does not hold for operations on `(0,∞)` (identity `1` is not the infimum).

Instead of adding a separate global “Aczél theorem” axiom, we prove directly:

- From K&S Axiom 3 (distributivity over `+`), `x ↦ x ⊗ t` is additive on `(0,∞)`,
  hence linear: `x ⊗ t = x * k(t)` for a scalar `k(t) > 0`.
- From K&S Axiom 4 (associativity of `⊗`) and continuity/strict-monotonicity, the scalar
  `k` is forced to be a *global scale* times the identity: `k(t) = t / C`.
- Therefore `x ⊗ y = (x * y) / C`, i.e. `⊗` is multiplication up to a global constant.

This produces the paper’s direct product rule *without any unproven “specification” axioms*.

-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem

open Classical
open Set

open Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

/-! ## Distinguished element -/

/-- The distinguished element `1 : (0,∞)` (as a `PosReal`). -/
def onePos : PosReal := ⟨(1 : ℝ), by norm_num⟩

@[simp] theorem coe_onePos : ((onePos : PosReal) : ℝ) = 1 := rfl

/-! ## Regularity package for tensor on `PosReal` -/

/-- A **regularity hypothesis package** for a tensor-like operation `⊗` on positive reals.

This is *not* an additional axiom of the KS project: it is a convenient bundle of properties
used by this file’s direct argument.  When one already has an additive order-isomorphism
representation `Θ (x ⊗ y) = Θ x + Θ y`, these properties are derivable.
-/
structure TensorRegularity (tensor : PosReal → PosReal → PosReal) : Prop where
  /-- Associativity (K&S Axiom 4). -/
  assoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w)
  /-- Injectivity of the “right scaling factor” map `t ↦ 1 ⊗ t`. -/
  inj_kPos : Function.Injective (fun t : PosReal => tensor onePos t)

namespace TensorRegularity

variable {tensor : PosReal → PosReal → PosReal}

/-- If `⊗` is conjugate to addition by an order isomorphism, then it satisfies the regularity
package used in this file. -/
theorem of_additiveOrderIsoRep (hRep : AdditiveOrderIsoRep PosReal tensor) :
    TensorRegularity tensor := by
  refine ⟨?_, ?_⟩
  · intro u v w
    simpa using (AdditiveOrderIsoRep.op_assoc (α := PosReal) (op := tensor) hRep u v w)
  · -- Injectivity follows from strict monotonicity, which is automatic under representation.
    have hmono : StrictMono fun t : PosReal => tensor onePos t := by
      simpa using
        (AdditiveOrderIsoRep.strictMono_right (α := PosReal) (op := tensor) hRep onePos)
    exact hmono.injective

end TensorRegularity

namespace TensorDerivation

variable {tensor : PosReal → PosReal → PosReal}

/-- The “right scaling factor” induced by a tensor: `k(t) := 1 ⊗ t`. -/
def kPos (tensor : PosReal → PosReal → PosReal) (t : PosReal) : PosReal :=
  tensor onePos t

@[simp] theorem coe_kPos (tensor : PosReal → PosReal → PosReal) (t : PosReal) :
    ((kPos tensor t : PosReal) : ℝ) = ((tensor onePos t : PosReal) : ℝ) :=
  rfl

/-- From distributivity over `+`, the tensor is linear in the left argument:
`(x ⊗ t) = x * (1 ⊗ t)` (after coercion to `ℝ`). -/
theorem tensor_coe_eq_mul_kPos
    (hDistrib : DistributesOverAdd tensor) (t x : PosReal) :
    ((tensor x t : PosReal) : ℝ) = ((x : ℝ) * ((kPos tensor t : PosReal) : ℝ)) := by
  -- Extend `x ↦ x ⊗ t` to a total function on `ℝ`, but only use it on `(0,∞)`.
  let f : ℝ → ℝ := fun r => if hr : 0 < r then ((tensor ⟨r, hr⟩ t : PosReal) : ℝ) else 0

  have hadd : ∀ {u v : ℝ}, 0 < u → 0 < v → f (u + v) = f u + f v := by
    intro u v hu hv
    have huv : 0 < u + v := add_pos hu hv
    have hdis :
        tensor (addPos ⟨u, hu⟩ ⟨v, hv⟩) t = addPos (tensor ⟨u, hu⟩ t) (tensor ⟨v, hv⟩ t) :=
      hDistrib ⟨u, hu⟩ ⟨v, hv⟩ t
    have hdis' : ((tensor (addPos ⟨u, hu⟩ ⟨v, hv⟩) t : PosReal) : ℝ)
        = ((tensor ⟨u, hu⟩ t : PosReal) : ℝ) + ((tensor ⟨v, hv⟩ t : PosReal) : ℝ) := by
      simpa [coe_addPos] using congrArg (fun z : PosReal => (z : ℝ)) hdis
    -- Now unfold the `if`-definitions; `addPos` is definitional `(u+v)` on coercions.
    simpa [f, hu, hv, huv] using hdis'

  have hpos : ∀ {u : ℝ}, 0 < u → 0 < f u := by
    intro u hu
    -- `tensor ⟨u,hu⟩ t` is a positive real by construction.
    simp [f, hu]
    have hmem : ((tensor ⟨u, hu⟩ t : PosReal) : ℝ) ∈ PosReal := (tensor ⟨u, hu⟩ t).2
    change ((tensor ⟨u, hu⟩ t : PosReal) : ℝ) ∈ Ioi (0 : ℝ) at hmem
    exact (Set.mem_Ioi).1 hmem

  rcases AdditiveOnPos.exists_mul_const_of_add_of_pos f hadd (hpos := hpos) with ⟨c, hc, hc_spec⟩

  -- Identify the constant `c` as `f 1 = (1 ⊗ t)`.
  have h1 : f 1 = c := by
    have h := hc_spec (u := (1 : ℝ)) (by norm_num)
    simpa [one_mul] using h

  have hc_eq : c = ((kPos tensor t : PosReal) : ℝ) := by
    -- `f 1` unfolds to `((1 ⊗ t) : ℝ)`.
    have h' : f 1 = ((kPos tensor t : PosReal) : ℝ) := by
      simp [f, kPos, onePos, show (0 : ℝ) < 1 by norm_num]
    exact by simpa [h'] using h1.symm

  -- Apply `hc_spec` at `x` to get the desired linear form.
  have hx_pos : 0 < (x : ℝ) := by
    have hmem : (x : ℝ) ∈ PosReal := x.2
    change (x : ℝ) ∈ Ioi (0 : ℝ) at hmem
    exact (Set.mem_Ioi).1 hmem
  have hx : f (x : ℝ) = c * (x : ℝ) := hc_spec (u := (x : ℝ)) hx_pos
  have hx' : ((tensor x t : PosReal) : ℝ) = c * (x : ℝ) := by
    simpa [f, hx_pos] using hx
  -- Rewrite `c` as `(1 ⊗ t)` and commute multiplication.
  simpa [hc_eq, mul_comm, mul_left_comm, mul_assoc] using hx'

/-- Log of a positive product in `PosReal` is additive. -/
theorem log_mulPos (a b : PosReal) :
    Real.expOrderIso.symm (mulPos a b) = Real.expOrderIso.symm a + Real.expOrderIso.symm b := by
  -- Rewrite `expOrderIso.symm` as `Real.log` on positive inputs, then use `Real.log_mul`.
  have ha0 : (a : ℝ) ≠ 0 := ne_of_gt a.2
  have hb0 : (b : ℝ) ≠ 0 := ne_of_gt b.2
  have hlog_mul : Real.log ((mulPos a b : PosReal) : ℝ) = Real.log (a : ℝ) + Real.log (b : ℝ) := by
    simpa [mulPos] using (Real.log_mul ha0 hb0)
  -- Convert the logs back to `expOrderIso.symm`.
  have hlog_a : Real.log (a : ℝ) = Real.expOrderIso.symm a := by
    simpa using (Real.log_of_pos a.2)
  have hlog_b : Real.log (b : ℝ) = Real.expOrderIso.symm b := by
    simpa using (Real.log_of_pos b.2)
  have hlog_ab : Real.log ((mulPos a b : PosReal) : ℝ) = Real.expOrderIso.symm (mulPos a b) := by
    simpa [mulPos] using (Real.log_of_pos (mul_pos a.2 b.2))
  -- Assemble.
  have hlog_ab' : Real.expOrderIso.symm (mulPos a b) = Real.log ((mulPos a b : PosReal) : ℝ) := by
    simpa using hlog_ab.symm
  calc
    Real.expOrderIso.symm (mulPos a b)
        = Real.log ((mulPos a b : PosReal) : ℝ) := hlog_ab'
    _ = Real.log (a : ℝ) + Real.log (b : ℝ) := hlog_mul
    _ = Real.expOrderIso.symm a + Real.expOrderIso.symm b := by simp [hlog_a, hlog_b]

/-- `exp` regrades multiplication on `PosReal` into addition on `ℝ`. -/
theorem mulPos_expOrderIso (x y : ℝ) : mulPos (Real.expOrderIso x) (Real.expOrderIso y) = Real.expOrderIso (x + y) := by
  ext
  simp [mulPos, Real.exp_add]

/-- The key functional equation induced by associativity, in logarithmic coordinates. -/
theorem g_equation
    (hTensor : TensorRegularity tensor) (hDistrib : DistributesOverAdd tensor) :
    let g : ℝ → ℝ := fun x => Real.expOrderIso.symm (kPos tensor (Real.expOrderIso x))
    ∀ x y : ℝ, g (x + g y) = g x + g y := by
  intro g x y
  -- Notation: `X = exp x`, `Y = exp y`.
  let X : PosReal := Real.expOrderIso x
  let Y : PosReal := Real.expOrderIso y

  have hx : ((tensor X Y : PosReal) : ℝ) =
      ((X : ℝ) * ((kPos tensor Y : PosReal) : ℝ)) :=
    tensor_coe_eq_mul_kPos (tensor := tensor) hDistrib Y X

  -- Rewrite `kPos tensor Y` as `exp (g y)`.
  have h_kY : (kPos tensor Y : PosReal) = Real.expOrderIso (g y) := by
    -- `g y` is definitionally `log (kPos tensor (exp y))`, so exponentiating gives back `kPos tensor Y`.
    have : Real.expOrderIso (g y) = kPos tensor Y := by
      -- Avoid `simp` rewriting the goal to `True`; make the target match `apply_symm_apply`.
      dsimp [g]
      change Real.expOrderIso (Real.expOrderIso.symm (kPos tensor Y)) = kPos tensor Y
      exact Real.expOrderIso.apply_symm_apply (kPos tensor Y)
    exact this.symm

  have h_kY_coe : ((kPos tensor Y : PosReal) : ℝ) = Real.exp (g y) := by
    simp [h_kY]

  have h_tensorXY : tensor X Y = Real.expOrderIso (x + g y) := by
    ext
    -- Coerce everything to `ℝ` and use the previous computations.
    have hx' : ((tensor X Y : PosReal) : ℝ) = Real.exp x * Real.exp (g y) := by
      -- `X` coerces to `exp x`.
      calc
        ((tensor X Y : PosReal) : ℝ) = (X : ℝ) * ((kPos tensor Y : PosReal) : ℝ) := hx
        _ = Real.exp x * Real.exp (g y) := by
          -- Rewrite the two factors independently.
          -- (Use `rw` rather than `simp` to avoid rewriting `kPos` via `coe_kPos`.)
          rw [h_kY_coe]
          simp [X, Real.coe_expOrderIso_apply]
    simpa [Real.coe_expOrderIso_apply, Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using hx'

  -- Apply `kPos` to the associativity equation in this coordinate system.
  have hk_mul : kPos tensor (tensor X Y) = mulPos (kPos tensor X) (kPos tensor Y) := by
    -- `kPos(tensor X Y) = 1 ⊗ (X ⊗ Y) = (1 ⊗ X) ⊗ Y` by associativity.
    have h1 : kPos tensor (tensor X Y) = tensor (kPos tensor X) Y := by
      -- expand and rewrite with associativity
      simpa [kPos, onePos] using (hTensor.assoc onePos X Y).symm
    -- Use linearity in the left argument at `Y`.
    have hcoe : ((tensor (kPos tensor X) Y : PosReal) : ℝ)
        = ((kPos tensor X : PosReal) : ℝ) * ((kPos tensor Y : PosReal) : ℝ) := by
      simpa [kPos] using
        tensor_coe_eq_mul_kPos (tensor := tensor) hDistrib Y (kPos tensor X)
    -- Compare with `mulPos`.
    apply Subtype.ext
    simpa [h1, coe_mulPos] using hcoe

  -- Take `log` of both sides and simplify to the functional equation for `g`.
  calc
    g (x + g y)
        = Real.expOrderIso.symm (kPos tensor (Real.expOrderIso (x + g y))) := by
            rfl
    _ = Real.expOrderIso.symm (kPos tensor (tensor X Y)) := by
            simp [g, h_tensorXY, X, Y]
    _ = Real.expOrderIso.symm (mulPos (kPos tensor X) (kPos tensor Y)) := by
            simp [hk_mul]
    _ = Real.expOrderIso.symm (kPos tensor X) + Real.expOrderIso.symm (kPos tensor Y) := by
            simpa using log_mulPos (kPos tensor X) (kPos tensor Y)
    _ = g x + g y := by
            simp [g, X, Y]

/-- Solve `g(x+g(y)) = g(x) + g(y)` assuming only injectivity of `g`: `g(x) = x + c`. -/
theorem g_eq_add_const_of_injective
    (g : ℝ → ℝ)
    (hg : Function.Injective g)
    (hg_eq : ∀ x y : ℝ, g (x + g y) = g x + g y) :
    ∃ c : ℝ, ∀ x : ℝ, g x = x + c := by
  let c : ℝ := g 0
  refine ⟨c, ?_⟩
  intro y

  have hneg : ∀ y : ℝ, g (-g y) = c - g y := by
    intro y
    have h1 := hg_eq (-g y) y
    have : c = g (-g y) + g y := by
      simpa [c] using h1
    linarith

  have hc0 : g (-c) = 0 := by
    simpa [c] using hneg 0

  have hfix : g (-c + g y) = g y := by
    have h2 := hg_eq (-c) y
    simpa [hc0] using h2

  have : -c + g y = y := hg hfix
  linarith

/-- Main theorem: from tensor axioms and distributivity, `⊗` is multiplication up to a global scale. -/
theorem tensor_coe_eq_mul_div_const_of_tensorRegularity
    (hTensor : TensorRegularity tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C := by
  let g : ℝ → ℝ := fun x => Real.expOrderIso.symm (kPos tensor (Real.expOrderIso x))
  have hg_eq : ∀ x y : ℝ, g (x + g y) = g x + g y := by
    simpa [g] using (g_equation (tensor := tensor) hTensor hDistrib)

  have hg_inj : Function.Injective g := by
    intro x₁ x₂ hx
    have hx' : kPos tensor (Real.expOrderIso x₁) = kPos tensor (Real.expOrderIso x₂) :=
      Real.expOrderIso.symm.injective hx
    have hx'' : Real.expOrderIso x₁ = Real.expOrderIso x₂ :=
      hTensor.inj_kPos (by simpa [kPos] using hx')
    exact Real.expOrderIso.injective hx''

  rcases g_eq_add_const_of_injective g hg_inj hg_eq with ⟨c, hc⟩

  have hkPos_exp : ∀ x : ℝ,
      kPos tensor (Real.expOrderIso x) = mulPos (Real.expOrderIso x) (Real.expOrderIso c) := by
    intro x
    have hx : Real.expOrderIso.symm (kPos tensor (Real.expOrderIso x)) = x + c := by
      simpa [g] using hc x
    have hx' : kPos tensor (Real.expOrderIso x) = Real.expOrderIso (x + c) := by
      simpa using congrArg Real.expOrderIso hx
    calc
      kPos tensor (Real.expOrderIso x) = Real.expOrderIso (x + c) := hx'
      _ = mulPos (Real.expOrderIso x) (Real.expOrderIso c) := by
            simpa using (mulPos_expOrderIso x c).symm

  have hkPos : ∀ t : PosReal, kPos tensor t = mulPos t (Real.expOrderIso c) := by
    intro t
    simpa using (hkPos_exp (Real.expOrderIso.symm t))

  let C : ℝ := (1 : ℝ) / Real.exp c
  have hC : 0 < C := one_div_pos.mpr (Real.exp_pos c)
  refine ⟨C, hC, ?_⟩
  intro x y
  have hxy : ((tensor x y : PosReal) : ℝ) = (x : ℝ) * ((kPos tensor y : PosReal) : ℝ) :=
    tensor_coe_eq_mul_kPos (tensor := tensor) hDistrib y x
  have hkPos_y : ((kPos tensor y : PosReal) : ℝ) = (y : ℝ) * Real.exp c := by
    have hy := congrArg (fun z : PosReal => (z : ℝ)) (hkPos y)
    simpa [mulPos, Real.coe_expOrderIso_apply, mul_assoc, mul_left_comm, mul_comm] using hy
  calc
    ((tensor x y : PosReal) : ℝ)
        = (x : ℝ) * ((kPos tensor y : PosReal) : ℝ) := hxy
    _ = (x : ℝ) * ((y : ℝ) * Real.exp c) := by rw [hkPos_y]
    _ = ((x : ℝ) * (y : ℝ)) * Real.exp c := by simp [mul_assoc]
    _ = ((x : ℝ) * (y : ℝ)) / C := by
          -- `C = 1 / exp c`, so dividing by `C` is multiplying by `exp c`.
          simp [C, div_eq_mul_inv, mul_assoc]

end TensorDerivation

namespace TensorDerivation

variable {tensor : PosReal → PosReal → PosReal}

/-- Distributivity over `+` forces injectivity in the **left** argument:
for each fixed `t`, the map `x ↦ x ⊗ t` is injective on `(0,∞)`. -/
theorem inj_left_of_distrib
    (hDistrib : DistributesOverAdd tensor) (t : PosReal) :
    Function.Injective (fun x : PosReal => tensor x t) := by
  intro x₁ x₂ hx
  have hxcoe : ((tensor x₁ t : PosReal) : ℝ) = ((tensor x₂ t : PosReal) : ℝ) :=
    congrArg (fun z : PosReal => (z : ℝ)) hx
  have h₁ :
      ((tensor x₁ t : PosReal) : ℝ) = ((x₁ : ℝ) * ((kPos tensor t : PosReal) : ℝ)) :=
    tensor_coe_eq_mul_kPos (tensor := tensor) hDistrib t x₁
  have h₂ :
      ((tensor x₂ t : PosReal) : ℝ) = ((x₂ : ℝ) * ((kPos tensor t : PosReal) : ℝ)) :=
    tensor_coe_eq_mul_kPos (tensor := tensor) hDistrib t x₂
  have hk_ne : ((kPos tensor t : PosReal) : ℝ) ≠ 0 := ne_of_gt (kPos tensor t).2

  have : (x₁ : ℝ) = (x₂ : ℝ) := by
    apply mul_right_cancel₀ hk_ne
    calc
      (x₁ : ℝ) * ((kPos tensor t : PosReal) : ℝ)
          = ((tensor x₁ t : PosReal) : ℝ) := by simpa using h₁.symm
      _ = ((tensor x₂ t : PosReal) : ℝ) := hxcoe
      _ = (x₂ : ℝ) * ((kPos tensor t : PosReal) : ℝ) := by simpa using h₂

  exact Subtype.ext (by simpa using this)

end TensorDerivation

namespace TensorRegularity

variable {tensor : PosReal → PosReal → PosReal}

/-- If `⊗` is distributive over `+` (Axiom 3) and is symmetric with `1` in the sense that
`1 ⊗ t = t ⊗ 1`, then the map `t ↦ 1 ⊗ t` is injective.

This is the minimal “commutativity-style” hypothesis needed to eliminate an explicit
`inj_kPos` assumption in `TensorRegularity`. -/
theorem inj_kPos_of_distrib_of_comm_one
    (hDistrib : DistributesOverAdd tensor)
    (hCommOne : ∀ t : PosReal, tensor onePos t = tensor t onePos) :
    Function.Injective (fun t : PosReal => tensor onePos t) := by
  intro t₁ t₂ ht
  have ht' : tensor t₁ onePos = tensor t₂ onePos := by
    calc
      tensor t₁ onePos = tensor onePos t₁ := by simpa using (hCommOne t₁).symm
      _ = tensor onePos t₂ := ht
      _ = tensor t₂ onePos := by simpa using (hCommOne t₂)
  have hinj_left : Function.Injective (fun x : PosReal => tensor x onePos) :=
    TensorDerivation.inj_left_of_distrib (tensor := tensor) hDistrib onePos
  exact hinj_left ht'

/-- Full commutativity implies the weaker symmetry hypothesis used in
`inj_kPos_of_distrib_of_comm_one`. -/
theorem inj_kPos_of_distrib_of_comm
    (hDistrib : DistributesOverAdd tensor)
    (hComm : ∀ u v : PosReal, tensor u v = tensor v u) :
    Function.Injective (fun t : PosReal => tensor onePos t) :=
  inj_kPos_of_distrib_of_comm_one (tensor := tensor) hDistrib (fun t => hComm onePos t)

/-- Build `TensorRegularity` from associativity (Axiom 4), distributivity (Axiom 3),
and symmetry with `1` (a commutativity-style “independence” hypothesis). -/
theorem of_assoc_of_distrib_of_comm_one
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hCommOne : ∀ t : PosReal, tensor onePos t = tensor t onePos) :
    TensorRegularity tensor :=
  ⟨hAssoc, inj_kPos_of_distrib_of_comm_one (tensor := tensor) hDistrib hCommOne⟩

/-- Build `TensorRegularity` from associativity (Axiom 4), distributivity (Axiom 3),
and full commutativity (a common “independence” hypothesis). -/
theorem of_assoc_of_distrib_of_comm
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hComm : ∀ u v : PosReal, tensor u v = tensor v u) :
    TensorRegularity tensor :=
  of_assoc_of_distrib_of_comm_one (tensor := tensor) hAssoc hDistrib (fun t => hComm onePos t)

end TensorRegularity

/-- Re-export: from tensor regularity and distributivity, `⊗` is multiplication up to a global
scale constant. This is the Lean-friendly Appendix B route that avoids “Appendix A again”. -/
theorem tensor_coe_eq_mul_div_const_of_tensorRegularity
    {tensor : PosReal → PosReal → PosReal}
    (hTensor : TensorRegularity tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C := by
  exact
    TensorDerivation.tensor_coe_eq_mul_div_const_of_tensorRegularity
      (tensor := tensor) hTensor hDistrib

/-- Convenience: an additive order-isomorphism representation implies `TensorRegularity`. -/
theorem tensorRegularity_of_additiveOrderIsoRep
    {tensor : PosReal → PosReal → PosReal}
    (hRep : AdditiveOrderIsoRep PosReal tensor) :
    TensorRegularity tensor :=
  TensorRegularity.of_additiveOrderIsoRep (tensor := tensor) hRep

/-- If `⊗` satisfies Axioms 3–4 and is symmetric with `1`, then `⊗` is scaled multiplication. -/
theorem tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm_one
    {tensor : PosReal → PosReal → PosReal}
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hCommOne : ∀ t : PosReal, tensor onePos t = tensor t onePos) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C :=
  tensor_coe_eq_mul_div_const_of_tensorRegularity
    (tensor := tensor)
    (TensorRegularity.of_assoc_of_distrib_of_comm_one
      (tensor := tensor) hAssoc hDistrib hCommOne)
    hDistrib

/-- If `⊗` satisfies Axioms 3–4 and is commutative, then `⊗` is scaled multiplication. -/
theorem tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm
    {tensor : PosReal → PosReal → PosReal}
    (hAssoc : ∀ u v w : PosReal, tensor (tensor u v) w = tensor u (tensor v w))
    (hDistrib : DistributesOverAdd tensor)
    (hComm : ∀ u v : PosReal, tensor u v = tensor v u) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C :=
  tensor_coe_eq_mul_div_const_of_assoc_of_distrib_of_comm_one
    (tensor := tensor) hAssoc hDistrib (fun t => hComm onePos t)

/-- If `⊗` is already given with an additive order-isomorphism representation
`Θ(x ⊗ y) = Θ x + Θ y`, then it satisfies `TensorRegularity`, so the Lean-friendly Appendix B
route applies without adding any extra axioms. -/
theorem tensor_coe_eq_mul_div_const_of_additiveOrderIsoRep
    {tensor : PosReal → PosReal → PosReal}
    (hRep : AdditiveOrderIsoRep PosReal tensor)
    (hDistrib : DistributesOverAdd tensor) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : PosReal, ((tensor x y : PosReal) : ℝ) = ((x : ℝ) * (y : ℝ)) / C := by
  exact
    tensor_coe_eq_mul_div_const_of_tensorRegularity
      (tensor := tensor) (TensorRegularity.of_additiveOrderIsoRep (tensor := tensor) hRep) hDistrib

end Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem
