import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromGLVLocalDirectionality

/-!
# Routed CAROM: GLV saddle values and cyclic return exponents

Afraimovich, Rabinovich, and Varona, *Heteroclinic Contours in Neural
Ensembles and the Winnerless Competition Principle* (2003,
arXiv:nlin/0304016), study the normalized generalized Lotka--Volterra field

`a_i' = a_i * (1 - a_i - sum_{j != i} rho_ij * a_j)`.

At the single-species saddle `A_i`, the outgoing direction toward `A_(i+1)`
has rate `1 - rho_(i+1,i)` and the incoming stable direction has rate
`1 - rho_(i,i+1)`.  Equation (10) defines their magnitude ratio

`nu_i = (rho_(i,i+1) - 1) / (1 - rho_(i+1,i))`,

and Equation (11) uses the cyclic product of these saddle values.

This file connects that ratio to the already formalized GLV invasion rates,
proves its exact subcritical, critical, and dissipative boundaries, and
derives the product exponent by composing the source-shaped local power maps
in logarithmic coordinates.  A positive fixture shows that a cyclic return
can have product exponent greater than one even when one local passage has
exponent below one; a negative fixture shows that positive local exponents
alone do not imply a dissipative cycle.

The source's global attraction theorem also requires its existence,
leading-direction, and regularity hypotheses.  The results below formalize
the saddle-ratio and return-exponent layer; they do not infer a global
heteroclinic orbit or robustness under perturbation.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

namespace RoutedCarom

/-! ## Saddle values from GLV invasion rates -/

/-- Stable-rate magnitude divided by outgoing expansion rate, expressed in
the predation parameters of the generalized GLV field. -/
noncomputable def glvSaddleValue
    (death stablePredation expansionPredation : ℝ) : ℝ :=
  (stablePredation - death) / (death - expansionPredation)

/-- The saddle value is exactly the ratio of the incoming contraction
magnitude to the outgoing invasion rate.  The common reproduction/death
scale cancels. -/
theorem glvSaddleValue_eq_invasionRate_ratio
    {reproduction death stablePredation expansionPredation : ℝ}
    (hreproduction : 0 < reproduction) (hdeath : 0 < death) :
    glvSaddleValue death stablePredation expansionPredation =
      -glvInvasionRate reproduction death stablePredation /
        glvInvasionRate reproduction death expansionPredation := by
  rw [glvInvasionRate_eq_scale_mul_gap hdeath.ne',
    glvInvasionRate_eq_scale_mul_gap hdeath.ne']
  unfold glvSaddleValue
  have hscale : reproduction / death ≠ 0 :=
    div_ne_zero hreproduction.ne' hdeath.ne'
  field_simp
  ring

/-- The source's stable/unstable inequalities make every saddle value
positive. -/
theorem glvSaddleValue_pos
    {death stablePredation expansionPredation : ℝ}
    (hstable : death < stablePredation)
    (hexpansion : expansionPredation < death) :
    0 < glvSaddleValue death stablePredation expansionPredation := by
  exact div_pos (sub_pos.mpr hstable) (sub_pos.mpr hexpansion)

/-- A local passage is dissipative exactly when the two opposing predation
coefficients sum to more than twice the self-limitation rate. -/
theorem one_lt_glvSaddleValue_iff
    {death stablePredation expansionPredation : ℝ}
    (hexpansion : expansionPredation < death) :
    1 < glvSaddleValue death stablePredation expansionPredation ↔
      2 * death < stablePredation + expansionPredation := by
  unfold glvSaddleValue
  rw [one_lt_div (sub_pos.mpr hexpansion)]
  constructor <;> intro h <;> nlinarith

/-- The critical surface has saddle value exactly one. -/
theorem glvSaddleValue_eq_one_iff
    {death stablePredation expansionPredation : ℝ}
    (hexpansion : expansionPredation < death) :
    glvSaddleValue death stablePredation expansionPredation = 1 ↔
      stablePredation + expansionPredation = 2 * death := by
  unfold glvSaddleValue
  have hden : death - expansionPredation ≠ 0 :=
    (sub_pos.mpr hexpansion).ne'
  constructor
  · intro h
    apply (div_eq_one_iff_eq hden).mp at h
    nlinarith
  · intro h
    apply (div_eq_one_iff_eq hden).2
    nlinarith

/-- Below the critical surface the local saddle map expands transverse
distance. -/
theorem glvSaddleValue_lt_one_iff
    {death stablePredation expansionPredation : ℝ}
    (hexpansion : expansionPredation < death) :
    glvSaddleValue death stablePredation expansionPredation < 1 ↔
      stablePredation + expansionPredation < 2 * death := by
  unfold glvSaddleValue
  rw [div_lt_one (sub_pos.mpr hexpansion)]
  constructor <;> intro h <;> nlinarith

/-! ## Composition of local passage maps in logarithmic coordinates -/

/-- In log-distance coordinates, a local power map
`xi = c * eta ^ exponent` becomes an affine map. -/
structure LogPassage where
  exponent : ℝ
  bias : ℝ

namespace LogPassage

noncomputable def run (passage : LogPassage) (distance : ℝ) : ℝ :=
  passage.exponent * distance + passage.bias

def identity : LogPassage where
  exponent := 1
  bias := 0

@[simp] theorem identity_exponent : identity.exponent = 1 := rfl

/-- `compose later earlier` executes `earlier` first. -/
noncomputable def compose
    (later earlier : LogPassage) : LogPassage where
  exponent := later.exponent * earlier.exponent
  bias := later.exponent * earlier.bias + later.bias

@[simp] theorem run_identity (distance : ℝ) :
    identity.run distance = distance := by
  simp [run, identity]

theorem run_compose
    (later earlier : LogPassage) (distance : ℝ) :
    (compose later earlier).run distance =
      later.run (earlier.run distance) := by
  simp [run, compose]
  ring

/-- Sequential composition in list order. -/
noncomputable def chain : List LogPassage → LogPassage
  | [] => identity
  | first :: rest => compose (chain rest) first

theorem run_chain (passages : List LogPassage) (distance : ℝ) :
    (chain passages).run distance =
      passages.foldl (fun state passage => passage.run state) distance := by
  induction passages generalizing distance with
  | nil => simp [chain]
  | cons first rest ih =>
      simp [chain, run_compose, ih]

/-- The slope of one cyclic return in log distance is the product of the
local saddle values. -/
theorem chain_exponent (passages : List LogPassage) :
    (chain passages).exponent =
      (passages.map LogPassage.exponent).prod := by
  induction passages with
  | nil => rfl
  | cons first rest ih =>
      simp [chain, compose, ih, mul_comm]

noncomputable def zeroBias (exponent : ℝ) : LogPassage where
  exponent := exponent
  bias := 0

@[simp] theorem zeroBias_exponent (exponent : ℝ) :
    (zeroBias exponent).exponent = exponent := rfl

theorem chain_zeroBias_eq (exponents : List ℝ) :
    chain (exponents.map zeroBias) =
      zeroBias exponents.prod := by
  induction exponents with
  | nil => rfl
  | cons exponent rest ih =>
      simp [chain, compose, zeroBias, ih, mul_comm]

theorem chain_zeroBias_run
    (exponents : List ℝ) (distance : ℝ) :
    (chain (exponents.map zeroBias)).run distance =
      exponents.prod * distance := by
  rw [chain_zeroBias_eq]
  simp [run, zeroBias]

/-- If every nonempty local passage is dissipative, the cyclic return
exponent is greater than one.  The converse is deliberately not claimed. -/
theorem one_lt_chainExponent_of_each
    {exponents : List ℝ} (hnonempty : exponents ≠ [])
    (heach : ∀ exponent ∈ exponents, 1 < exponent) :
    1 < (chain (exponents.map zeroBias)).exponent := by
  have hprod : 1 < exponents.prod := by
    induction exponents with
    | nil => exact (hnonempty rfl).elim
    | cons head tail ih =>
        have hhead : 1 < head := heach head (by simp)
        by_cases htail : tail = []
        · subst tail
          simpa using hhead
        · have htailEach :
              ∀ exponent ∈ tail, 1 < exponent := by
            intro exponent hexponent
            exact heach exponent (by simp [hexponent])
          have htailProd : 1 < tail.prod := ih htail htailEach
          rw [List.prod_cons]
          have hpositive :
              0 < head * (tail.prod - 1) :=
            mul_pos (lt_trans zero_lt_one hhead)
              (sub_pos.mpr htailProd)
          nlinarith
  rw [chain_exponent]
  simpa [List.map_map, Function.comp_def, zeroBias] using hprod

end LogPassage

/-! ## Positive and negative boundaries -/

theorem dissipative_saddle :
    glvSaddleValue 1 2 (1 / 2) = 2 := by
  norm_num [glvSaddleValue]

theorem critical_saddle :
    glvSaddleValue 1 (3 / 2) (1 / 2) = 1 := by
  norm_num [glvSaddleValue]

theorem expansive_saddle :
    glvSaddleValue 1 (5 / 4) (1 / 2) = 1 / 2 := by
  norm_num [glvSaddleValue]

/-- A cyclic return can be dissipative even though one local passage is
expansive.  Thus Equation (11) is genuinely a product condition rather than
the conjunction of `nu_i > 1`. -/
theorem cyclic_product_can_dominate_one_local_expansion :
    let exponents : List ℝ := [2, 2, 1 / 2]
    1 < (LogPassage.chain
          (exponents.map LogPassage.zeroBias)).exponent ∧
      exponents.getLast! < 1 := by
  norm_num [LogPassage.chain, LogPassage.compose,
    LogPassage.zeroBias]

/-- Merely positive local saddle values do not imply a dissipative cyclic
return. -/
theorem positive_local_values_do_not_imply_product_gt_one :
    let exponents : List ℝ := [1 / 2, 1 / 2, 1 / 2]
    (∀ exponent ∈ exponents, 0 < exponent) ∧
      (LogPassage.chain
        (exponents.map LogPassage.zeroBias)).exponent < 1 := by
  norm_num [LogPassage.chain, LogPassage.compose,
    LogPassage.zeroBias]

#print axioms glvSaddleValue_eq_invasionRate_ratio
#print axioms one_lt_glvSaddleValue_iff
#print axioms glvSaddleValue_eq_one_iff
#print axioms LogPassage.run_chain
#print axioms LogPassage.chain_exponent
#print axioms LogPassage.one_lt_chainExponent_of_each
#print axioms cyclic_product_can_dominate_one_local_expansion
#print axioms positive_local_values_do_not_imply_product_gt_one

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
