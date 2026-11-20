import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Controls

/-!
# Certificates through a quotient with an error

An exact lumping is brittle: one perturbed copy breaks it (`perturbed_refused`). The law behind the
certificate on classes is more general: coupling bounds compose by gluing (`CouplingBound.comp`), so
a certificate of the chain can be factored through **any** chain `Q` by a coupling bound between the
chain and `Q`. A lumping is the case of error zero.

**The certificate** (`Abstraction`): a map `view` of the states onto the states of a chain `Q`, a
prefixpoint certificate of `Q`, an error `e s ≥ 0` for every state, and, for some actions and states,
a table meant to couple the state's successor distribution with `Q`'s distribution at its class.
The **cross kernel** (`crossKernel`) is `e s` at `(s, view s)` and one elsewhere.

**The checker** (`abstractionCheck`), in exact rationals: `c ≤ 1`; `0 ≤ e ≤ 1`; every observation
difference between a state and a class is at most the cross kernel; for every action and state, a
listed table must couple and cost at most `e s` after discount (`crossCovered`), and an omitted one is
filled in by the graph coupling when the fibre masses agree, its cost the expected error; and the
quotient's prefixpoint certificate.

**Soundness** (`abstractionCheck_sound`): acceptance implies, at every discount `0 ≤ c`,

  `metric(s, t) ≤ e s + D (view s) (view t) + e t`.

The proof: the cross kernel is a coupling bound of the chain against `Q` (pairs off the graph by the
independent coupling, which needs `c ≤ 1`), the quotient's certificate is one of `Q`, and the
composite through `Q` and back (the tree's `CouplingBound.comp`, `CouplingBound.swap`) is one of the
chain, bounded at `(s, t)` through `view s` and `view t` (`infConvolution_le`).

**Controls.** With zero errors and no listed table it is the certificate on classes
(`exact_case_accepted`). On the perturbed blow-up, with errors `27/319` and `60/319` at the two leaky
copies and one listed table, it is accepted (`perturbed_accepted`) and brackets the distance of the two
copies between `3/20` (a test) and `87/319` (`perturbed_bracket`). Its checker's whole work is at most a
quarter of the products and additions of every accepted prefixpoint certificate of the perturbed chain
(`perturbed_four_times_cheaper`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

open Mettapedia.Cybernetics.ApproximateAdequacy

variable {A Atom S C : Type*} [Fintype S] [Fintype C] [DecidableEq C]

/-! ## Tables between two state spaces -/

/-- **A table couples `μ` on `S` with `ν` on `C`.** -/
def IsCrossTable (μ : S → ℚ) (ν : C → ℚ) (ω : S → C → ℚ) : Prop :=
  (∀ x k, 0 ≤ ω x k) ∧ (∀ x, ∑ k, ω x k = μ x) ∧ ∀ k, ∑ x, ω x k = ν k

omit [DecidableEq C] in
instance (μ : S → ℚ) (ν : C → ℚ) (ω : S → C → ℚ) : Decidable (IsCrossTable μ ν ω) := by
  unfold IsCrossTable
  infer_instance

omit [DecidableEq C] in
/-- The coupling given by a table that couples. -/
def IsCrossTable.coupling {μ : S → ℚ} {ν : C → ℚ} {ω : S → C → ℚ} (table : IsCrossTable μ ν ω) :
    Coupling μ ν :=
  ⟨ω, table.1, table.2.1, table.2.2⟩

omit [DecidableEq C] in
/-- The expected value of `m` under a joint weighting. -/
def crossCost (ω m : S → C → ℚ) : ℚ :=
  ∑ x, ∑ k, ω x k * m x k

/-- **The cross kernel**: the error on the graph of the map, one elsewhere. -/
def crossKernel (view : S → C) (error : S → ℚ) (s : S) (k : C) : ℚ :=
  if view s = k then error s else 1

/-! ## The certificate and its checker -/

/-- **A certificate through a quotient with an error.** -/
structure Abstraction (A Atom S C : Type*) [Fintype C] where
  /-- The class of each state. -/
  view : S → C
  /-- The chain on the classes. -/
  quotient : LabelledMarkovChain ℚ A Atom C
  /-- The certificate of the chain on the classes. -/
  cert : Prefixpoint A C
  /-- The claimed distance of each state from its class. -/
  error : S → ℚ
  /-- The listed tables coupling a state's successors with its class's. -/
  cross : A → S → Option (S → C → ℚ)

/-- **One action at one state.** A listed table must couple the state's successor distribution with
the quotient's distribution at its class, with discounted cost under the cross kernel at most the
state's error; an omitted one is filled in by the graph coupling when the fibre masses agree, its
cost the expected error. -/
def crossCovered (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ) (abs : Abstraction A Atom S C) (a : A)
    (s : S) : Bool :=
  match abs.cross a s with
  | some ω =>
      decide (IsCrossTable (P.trans a s) (abs.quotient.trans a (abs.view s)) ω) &&
        decide (c * crossCost ω (crossKernel abs.view abs.error) ≤ abs.error s)
  | none =>
      decide (∀ k, fibreMass abs.view (P.trans a s) k = abs.quotient.trans a (abs.view s) k) &&
        decide (c * expect (P.trans a s) abs.error ≤ abs.error s)

/-- **The checker** of certificates through a quotient with an error. -/
def abstractionCheck [Fintype A] [Fintype Atom] (P : LabelledMarkovChain ℚ A Atom S) (c : ℚ)
    (abs : Abstraction A Atom S C) : Bool :=
  decide (c ≤ 1) && decide (∀ s, 0 ≤ abs.error s ∧ abs.error s ≤ 1) &&
    decide (∀ i s k, |P.observe i s - abs.quotient.observe i k| ≤ crossKernel abs.view abs.error s k) &&
    decide (∀ a s, crossCovered P c abs a s = true) && check abs.quotient c abs.cert

/-! ## Soundness -/

section Soundness

variable [Fintype A] [Fintype Atom] {P : LabelledMarkovChain ℚ A Atom S} {c : ℚ}
  {abs : Abstraction A Atom S C}

theorem abstractionCheck_iff :
    abstractionCheck P c abs = true ↔
      c ≤ 1 ∧ (∀ s, 0 ≤ abs.error s ∧ abs.error s ≤ 1) ∧
        (∀ i s k, |P.observe i s - abs.quotient.observe i k| ≤ crossKernel abs.view abs.error s k) ∧
        (∀ a s, crossCovered P c abs a s = true) ∧ check abs.quotient c abs.cert = true := by
  simp only [abstractionCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

omit [Fintype A] [Fintype Atom] in
/-- The graph coupling costs the expected error under the cross kernel. -/
theorem cost_graphCoupling_crossKernel (view : S → C) (error : S → ℚ) {μ : S → ℚ} {ν : C → ℚ}
    (nonneg : ∀ x, 0 ≤ μ x) (fibres : ∀ k, fibreMass view μ k = ν k) :
    (graphCoupling view nonneg fibres).cost (crossKernel view error) = expect μ error := by
  unfold Coupling.cost expect
  refine Finset.sum_congr rfl fun x _ => ?_
  change ∑ k, (if view x = k then μ x else 0) * crossKernel view error x k = μ x * error x
  have each : ∀ k, (if view x = k then μ x else 0) * crossKernel view error x k =
      if view x = k then μ x * error x else 0 := by
    intro k
    unfold crossKernel
    split_ifs <;> simp
  simp only [each, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **The cross kernel is a coupling bound of the chain against the quotient**, at every discount
`0 ≤ c`, when the checker accepts. -/
theorem abstractionCheck_couplingBound (accepted : abstractionCheck P c abs = true)
    (c_nonneg : 0 ≤ c) : CouplingBound P abs.quotient c (crossKernel abs.view abs.error) := by
  obtain ⟨c_le, errors, observed, covered, _⟩ := abstractionCheck_iff.mp accepted
  have kernel_le : ∀ s k, crossKernel abs.view abs.error s k ≤ 1 := by
    intro s k
    unfold crossKernel
    split_ifs
    · exact (errors s).2
    · exact le_rfl
  refine ⟨fun s k => ?_, observed, fun a s k => ?_⟩
  · unfold crossKernel
    split_ifs
    · exact (errors s).1
    · exact zero_le_one
  · by_cases on : abs.view s = k
    · subst on
      have here := covered a s
      have at_graph : crossKernel abs.view abs.error s (abs.view s) = abs.error s := if_pos rfl
      rw [at_graph]
      rcases hit : abs.cross a s with _ | ω
      · simp only [crossCovered, hit, Bool.and_eq_true, decide_eq_true_eq] at here
        refine ⟨graphCoupling abs.view (P.isDistribution a s).nonneg here.1, ?_⟩
        rw [cost_graphCoupling_crossKernel]
        exact here.2
      · simp only [crossCovered, hit, Bool.and_eq_true, decide_eq_true_eq] at here
        exact ⟨here.1.coupling, here.2⟩
    · refine ⟨Coupling.independent (P.isDistribution a s) (abs.quotient.isDistribution a k), ?_⟩
      have cost_le := (Coupling.independent (P.isDistribution a s)
        (abs.quotient.isDistribution a k)).cost_le_of_le (P.isDistribution a s) kernel_le
      have off : crossKernel abs.view abs.error s k = 1 := if_neg on
      rw [off]
      calc c * _ ≤ c * 1 := mul_le_mul_of_nonneg_left cost_le c_nonneg
        _ ≤ 1 := by linarith

/-- **Soundness**: acceptance implies that the distance of two states is at most the error of the
first, plus the quotient's kernel at their classes, plus the error of the second, at every discount
`0 ≤ c`. -/
theorem abstractionCheck_sound (accepted : abstractionCheck P c abs = true) (c_nonneg : 0 ≤ c)
    (s t : S) :
    bisimulationMetric (realChain P) (realChain P) (c : ℝ) s t ≤
      ((abs.error s + abs.cert.kernel (abs.view s) (abs.view t) + abs.error t : ℚ) : ℝ) := by
  have : Nonempty C := ⟨abs.view s⟩
  obtain ⟨_, errors, _, _, quotientAccepted⟩ := abstractionCheck_iff.mp accepted
  have cross := abstractionCheck_couplingBound accepted c_nonneg
  have quotient := coreCheck_couplingBound (check_iff.mp quotientAccepted).1 c_nonneg
  have composed := (cross.comp quotient c_nonneg).comp cross.swap c_nonneg
  refine (bisimulationMetric_le_real composed c_nonneg s t).trans (Rat.cast_le.mpr ?_)
  have first := infConvolution_le
    (infConvolution (crossKernel abs.view abs.error) (offDiagonal abs.cert.kernel))
    (fun k x => crossKernel abs.view abs.error x k) s (abs.view t) t
  have second := infConvolution_le (crossKernel abs.view abs.error) (offDiagonal abs.cert.kernel) s
    (abs.view s) (abs.view t)
  have diagonal := offDiagonal_le (coreCheck_iff.mp (check_iff.mp quotientAccepted).1).1
    (abs.view s) (abs.view t)
  have at_s : crossKernel abs.view abs.error s (abs.view s) = abs.error s := if_pos rfl
  have at_t : crossKernel abs.view abs.error t (abs.view t) = abs.error t := if_pos rfl
  simp only [at_t] at first
  rw [at_s] at second
  linarith

end Soundness

/-! ## Counted work -/

/-- `IsCrossTable μ ν ω` over `n` and `k` states, when it holds. -/
def crossTableWork (n k : ℕ) : Work := (0, 2 * (n * k), n * k + n + k, 0)

/-- `crossCost ω (crossKernel view error)`: one product and one test of the graph per entry. -/
def crossJointWork (n k : ℕ) : Work := (n * k, n * k + n, 0, n * k)

/-- The fibre masses of one state against its class's row: every class's fibre sum and equality. -/
def fibreWork (n k : ℕ) : Work := (0, n, k, n * k)

/-- `expect μ e` over `n` states. -/
def expectWork (n : ℕ) : Work := (n, n, 0, 0)

/-- **The work of one action at one state**, following `crossCovered`; the last comparison decides
nothing further, so the work does not depend on the discount. -/
def crossCoveredWork (P : LabelledMarkovChain ℚ A Atom S) (abs : Abstraction A Atom S C) (a : A)
    (s : S) : Work :=
  match abs.cross a s with
  | some ω =>
      if IsCrossTable (P.trans a s) (abs.quotient.trans a (abs.view s)) ω then
        crossTableWork (Fintype.card S) (Fintype.card C) +
          crossJointWork (Fintype.card S) (Fintype.card C) + stepWork
      else crossTableWork (Fintype.card S) (Fintype.card C)
  | none =>
      if ∀ k, fibreMass abs.view (P.trans a s) k = abs.quotient.trans a (abs.view s) k then
        fibreWork (Fintype.card S) (Fintype.card C) + expectWork (Fintype.card S) + stepWork
      else fibreWork (Fintype.card S) (Fintype.card C)

/-- **The work of the checker** `abstractionCheck`: the discount, the errors, every observation
difference against the cross kernel, every action at every state, and the quotient's certificate. -/
def abstractionWork [Fintype A] [Fintype Atom] [DecidableEq S] (P : LabelledMarkovChain ℚ A Atom S)
    (c : ℚ) (abs : Abstraction A Atom S C) : Work :=
  (0, 0, 1, 0) + (0, 0, 2 * Fintype.card S, 0) +
    (0, 2 * (Fintype.card Atom * (Fintype.card S * Fintype.card C)),
      2 * (Fintype.card Atom * (Fintype.card S * Fintype.card C)),
      Fintype.card Atom * (Fintype.card S * Fintype.card C)) +
    ∑ a, ∑ s, crossCoveredWork P abs a s + prefixpointWork abs.quotient c abs.cert

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact

/-! ## Controls -/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.AbstractionControls

open Mettapedia.Cybernetics.ApproximateAdequacy
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Family
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.Controls

/-- **The exact case**: zero errors and no listed table, on the blown-up chain. -/
def exactAbs : Abstraction Unit Unit (St 1) (Fin 4) := ⟨Prod.fst, leak, correct, fun _ => 0, fun _ _ => none⟩

theorem exact_case_accepted : abstractionCheck (blowup 1) discount exactAbs = true := by
  decide +kernel

/-- The errors on the perturbed chain: at the two leaky copies. -/
def perturbedError (s : St 1) : ℚ :=
  if s = (2, 0) then 27 / 319 else if s = (2, 1) then 60 / 319 else 0

/-- The table at the perturbed copy: its successor `(2, 0)` split between leaky and the sink, its
successor `(3, 1)` to the sink. -/
def perturbedTable (x : St 1) (k : Fin 4) : ℚ :=
  if x = (2, 0) ∧ k = 2 then 1 / 2
  else if x = (2, 0) ∧ k = 3 then 1 / 6
  else if x = (3, 1) ∧ k = 3 then 1 / 3
  else 0

/-- **The certificate of the perturbed chain** through the leak chain, with errors. -/
def perturbedAbs : Abstraction Unit Unit (St 1) (Fin 4) where
  view := Prod.fst
  quotient := leak
  cert := correct
  error := perturbedError
  cross _ s := if s = (2, 1) then some perturbedTable else none

theorem perturbed_accepted : abstractionCheck perturbed discount perturbedAbs = true := by
  decide +kernel

/-- **The two leaky copies of the perturbed chain are bracketed**: between `3/20` and `87/319`. -/
theorem perturbed_bracket :
    (3 / 20 : ℝ) ≤ bisimulationMetric (realChain perturbed) (realChain perturbed) (discount : ℝ)
        (2, 0) (2, 1) ∧
      bisimulationMetric (realChain perturbed) (realChain perturbed) (discount : ℝ) (2, 0) (2, 1) ≤
        87 / 319 := by
  refine ⟨perturbed_apart, ?_⟩
  have bound := abstractionCheck_sound perturbed_accepted discount_nonneg (2, 0) (2, 1)
  have value : perturbedAbs.error (2, 0) + perturbedAbs.cert.kernel (perturbedAbs.view (2, 0))
      (perturbedAbs.view (2, 1)) + perturbedAbs.error (2, 1) = 87 / 319 := by decide +kernel
  rw [value] at bound
  have cast : ((87 / 319 : ℚ) : ℝ) = 87 / 319 := by norm_num
  rw [cast] at bound
  exact bound

/-- **The work of the checker on the perturbed chain.** -/
theorem perturbed_work : abstractionWork perturbed discount perturbedAbs = (460, 584, 277, 303) := by
  decide +kernel

/-- **Four times cheaper on the perturbed chain**: all the work of the checker is at most a quarter of
the products and additions of every accepted prefixpoint certificate of the perturbed chain. -/
theorem perturbed_four_times_cheaper {cert : Prefixpoint Unit (St 1)}
    (accepted : check perturbed discount cert = true) :
    4 * (abstractionWork perturbed discount perturbedAbs).all ≤
      (prefixpointWork perturbed discount cert).1 + (prefixpointWork perturbed discount cert).2.1 := by
  obtain ⟨products, additions⟩ := prefixpointWork_lower accepted
  rw [card_St, Fintype.card_unit] at products additions
  rw [perturbed_work]
  simp only [Work.all]
  omega

/-- The kernel one off the diagonal, every pair filled in. -/
def trivialCert : Prefixpoint Unit (St 1) := ⟨fun s t => if s = t then 0 else 1, fun _ _ _ => none⟩

/-- **An accepted prefixpoint certificate of the perturbed chain exists.** -/
theorem trivialCert_accepted : check perturbed discount trivialCert = true := by decide +kernel

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.Certificates.Compact.AbstractionControls
