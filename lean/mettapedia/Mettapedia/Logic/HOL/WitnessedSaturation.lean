import Mettapedia.Logic.HOL.WitnessedExtension
import Mettapedia.Logic.HOL.Syntax.FreshConst
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Tauto

/-!
# Henkin saturation chain

Building on the single-step conservativity `consistent_addWitness`, this file
constructs, over the parameter-extended signature `WithParams Const`, a
**consistent theory that witnesses every existential** — the Henkin saturation.

Given a (param-free) consistent base theory `T₀` and an enumeration `enum` of all
one-variable bodies, we add at stage `n` the witness axiom `(∃x. enum n) →
(enum n)[c]`, where `c = param σ kₙ` is a parameter chosen *larger than every
parameter already used* (`kₙ = max (axiomBound …) (maxParam …)`).  Freshness is
therefore automatic, and `consistent_addWitness` keeps every finite stage
consistent.

This file (Piece 1) builds the chain, the per-stage consistency, and the bound
machinery.  The limit's consistency (finite character) and the existence property
are added on top.
-/

namespace Mettapedia.Logic.HOL

open Mettapedia.Logic.HOL.WithParams

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- An existential body to be witnessed: a type paired with a one-variable formula. -/
abbrev Body (Const : Ty Base → Type v) := (σ : Ty Base) × Formula (WithParams Const) [σ]

/-- A source of parameter indices for Henkin witnesses.  The lower-bound field is
what makes the existing `maxParam` freshness proof reusable; injectivity records
that the supply is a genuine reserve of distinct parameters for later
level-bounded canonical worlds. -/
structure WitnessSupply where
  index : Nat → Nat
  le_index : ∀ n : Nat, n ≤ index n
  injective : Function.Injective index

/-- The original Henkin construction uses the identity parameter supply. -/
def identityWitnessSupply : WitnessSupply where
  index := id
  le_index := by intro n; rfl
  injective := by intro m n h; exact h

/-- The level-`ℓ` reserve of parameters, encoded by the standard pairing
function.  Fixed levels give injective supplies, and `Nat.right_le_pair` keeps
the `maxParam` freshness proof available. -/
def levelWitnessSupply (ℓ : Nat) : WitnessSupply where
  index := fun k => Nat.pair ℓ k
  le_index := by
    intro k
    exact Nat.right_le_pair ℓ k
  injective := by
    intro k k' h
    exact (Nat.pair_eq_pair.mp h).2

/-- A stage-reserved subsupply inside one parameter layer.  Stage `s` of layer
`ℓ` uses parameters encoded as `(ℓ, (s, k))`, leaving stages `s+1, s+2, ...`
available while keeping the whole construction below outer layer `ℓ+1`. -/
def stageWitnessSupply (ℓ s : Nat) : WitnessSupply where
  index := fun k => Nat.pair ℓ (Nat.pair s k)
  le_index := by
    intro k
    exact le_trans (Nat.right_le_pair s k) (Nat.right_le_pair ℓ (Nat.pair s k))
  injective := by
    intro k k' h
    have hStage : Nat.pair s k = Nat.pair s k' := (Nat.pair_eq_pair.mp h).2
    exact (Nat.pair_eq_pair.mp hStage).2

/-- A strict upper bound on the parameter indices occurring in a finite list of
closed formulas. -/
def axiomBound : List (ClosedFormula (WithParams Const)) → Nat
  | [] => 0
  | ψ :: l => max (maxParam ψ) (axiomBound l)

theorem maxParam_le_axiomBound :
    ∀ {l : List (ClosedFormula (WithParams Const))} {ψ},
      ψ ∈ l → maxParam (Const := Const) ψ ≤ axiomBound l
  | [], _, h => by simp at h
  | a :: l, ψ, h => by
      simp only [axiomBound]
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (maxParam_le_axiomBound h') (le_max_right _ _)

/-- The witness index chosen at stage `n`: larger than every parameter already in
the accumulated axioms and in the body being witnessed. -/
def witnessIndex (chain : List (ClosedFormula (WithParams Const))) (b : Body Const) : Nat :=
  max (axiomBound chain) (maxParam b.2)

/-- The witness axioms accumulated through the first `n` stages of the chain,
using a specified parameter supply. -/
def witnessChainUsing (supply : WitnessSupply) (enum : Nat → Body Const) :
    Nat → List (ClosedFormula (WithParams Const))
  | 0 => []
  | n + 1 =>
      witnessAxiom
        (param (enum n).1 (supply.index
          (witnessIndex (witnessChainUsing supply enum n) (enum n))))
        (enum n).2
      :: witnessChainUsing supply enum n

/-- The original identity-supply witness chain. -/
def witnessChain (enum : Nat → Body Const) :
    Nat → List (ClosedFormula (WithParams Const)) :=
  witnessChainUsing identityWitnessSupply enum

/-- The theory at stage `n`: the base plus the stage-`n` supplied witness axioms. -/
def witnessTheoryUsing (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) : ClosedTheorySet (WithParams Const) :=
  T₀ ∪ {ψ | ψ ∈ witnessChainUsing supply enum n}

/-- The original identity-supply theory at stage `n`. -/
def witnessTheory (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) : ClosedTheorySet (WithParams Const) :=
  witnessTheoryUsing identityWitnessSupply T₀ enum n

/-- The supplied Henkin saturation: the base plus *all* supplied witness axioms. -/
def witnessLimitUsing (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) : ClosedTheorySet (WithParams Const) :=
  T₀ ∪ {ψ | ∃ n, ψ ∈ witnessChainUsing supply enum n}

/-- The original identity-supply Henkin saturation. -/
def witnessLimit (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) : ClosedTheorySet (WithParams Const) :=
  witnessLimitUsing identityWitnessSupply T₀ enum

theorem witnessTheoryUsing_zero (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const)) (enum : Nat → Body Const) :
    witnessTheoryUsing supply T₀ enum 0 = T₀ := by
  simp [witnessTheoryUsing, witnessChainUsing]

theorem witnessTheoryUsing_succ (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    witnessTheoryUsing supply T₀ enum (n + 1)
      = insert (witnessAxiom
          (param (enum n).1 (supply.index
            (witnessIndex (witnessChainUsing supply enum n) (enum n))))
          (enum n).2)
          (witnessTheoryUsing supply T₀ enum n) := by
  simp only [witnessTheoryUsing, witnessChainUsing]
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, Set.mem_insert_iff]
  tauto

theorem witnessTheory_zero (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) : witnessTheory T₀ enum 0 = T₀ := by
  exact witnessTheoryUsing_zero identityWitnessSupply T₀ enum

theorem witnessTheory_succ (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    witnessTheory T₀ enum (n + 1)
      = insert (witnessAxiom
          (param (enum n).1 (witnessIndex (witnessChain enum n) (enum n)))
          (enum n).2)
          (witnessTheory T₀ enum n) := by
  exact witnessTheoryUsing_succ identityWitnessSupply T₀ enum n

/-- **Per-stage consistency.**  Every finite stage of the saturation chain is
consistent, by induction using `consistent_addWitness` and the fresh-index choice. -/
theorem witnessTheoryUsing_consistent (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T₀)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ) :
    ∀ n, ClosedTheorySet.Consistent (Const := WithParams Const)
      (witnessTheoryUsing supply T₀ enum n) := by
  intro n
  induction n with
  | zero => rw [witnessTheoryUsing_zero]; exact hCons
  | succ n ih =>
      rw [witnessTheoryUsing_succ]
      refine consistent_addWitness
        (c := param (enum n).1 (supply.index
          (witnessIndex (witnessChainUsing supply enum n) (enum n))))
        ih ?_ ?_
      · intro ψ hψ
        simp only [witnessTheoryUsing, Set.mem_union, Set.mem_setOf_eq] at hψ
        rcases hψ with hψ0 | hψc
        · exact hT0 ψ hψ0 (enum n).1 _
        · exact noConstOccurrence_param_of_ge _ ψ
            (le_trans (maxParam_le_axiomBound hψc)
              (le_trans (le_max_left _ _) (supply.le_index _)))
      · exact noConstOccurrence_param_of_ge _ (enum n).2
          (le_trans (le_max_right _ _) (supply.le_index _))

theorem witnessTheory_consistent (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T₀)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ) :
    ∀ n, ClosedTheorySet.Consistent (Const := WithParams Const)
      (witnessTheory T₀ enum n) := by
  exact witnessTheoryUsing_consistent identityWitnessSupply T₀ enum hCons hT0

/-! ## Omission-preserving finite witness-instance chain -/

/-- The pair-saturation chain used for separating intuitionistic extensions.
At stage `n` it adds the fresh instance of `enum n` only if the corresponding
existential is already provable from the current raw theory. -/
noncomputable def witnessInstanceChainUsing
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) : Nat → List (ClosedFormula (WithParams Const))
  | 0 => []
  | n + 1 =>
      let chain := witnessInstanceChainUsing supply T₀ enum n
      let Tn : ClosedTheorySet (WithParams Const) := T₀ ∪ {ψ | ψ ∈ chain}
      let b := enum n
      let c : WithParams Const b.1 :=
        param b.1 (supply.index (witnessIndex chain b))
      let inst : ClosedFormula (WithParams Const) :=
        instantiate (Base := Base) (.const c) b.2
      by
        classical
        exact
          if ClosedTheorySet.Provable (Const := WithParams Const) Tn (.ex b.2) then
            inst :: chain
          else
            chain

/-- The raw theory at a finite stage of the omission-preserving instance chain. -/
noncomputable def witnessInstanceTheoryUsing
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    ClosedTheorySet (WithParams Const) :=
  T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n}

theorem witnessInstanceTheoryUsing_zero
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) :
    witnessInstanceTheoryUsing supply T₀ enum 0 = T₀ := by
  simp [witnessInstanceTheoryUsing, witnessInstanceChainUsing]

open scoped Classical in
theorem witnessInstanceTheoryUsing_succ
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    witnessInstanceTheoryUsing supply T₀ enum (n + 1) =
      if _ : ClosedTheorySet.Provable (Const := WithParams Const)
          (T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n}) (.ex (enum n).2) then
        insert
          (instantiate (Base := Base)
            (.const (param (enum n).1 (supply.index
              (witnessIndex (witnessInstanceChainUsing supply T₀ enum n) (enum n)))))
            (enum n).2)
          (T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n})
      else
        T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n} := by
  classical
  ext ψ
  by_cases hEx : ClosedTheorySet.Provable (Const := WithParams Const)
      (T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n}) (.ex (enum n).2)
  · simp [witnessInstanceTheoryUsing, witnessInstanceChainUsing, hEx,
      Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff]
    tauto
  · simp [witnessInstanceTheoryUsing, witnessInstanceChainUsing, hEx,
      Set.mem_union, Set.mem_setOf_eq]

/-- The stage-`n` instance witness is fresh for the current raw instance theory. -/
theorem witnessInstanceTheoryUsing_fresh_selected
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ) :
    ∀ n, ∀ ψ ∈ witnessInstanceTheoryUsing supply T₀ enum n,
      NoConstOccurrence
        (param (enum n).1 (supply.index
          (witnessIndex (witnessInstanceChainUsing supply T₀ enum n) (enum n)))) ψ := by
  intro n ψ hψ
  simp only [witnessInstanceTheoryUsing, Set.mem_union, Set.mem_setOf_eq] at hψ
  rcases hψ with hψ0 | hψc
  · exact hT0 ψ hψ0 (enum n).1 _
  · exact noConstOccurrence_param_of_ge _ ψ
      (le_trans (maxParam_le_axiomBound hψc)
        (le_trans (le_max_left _ _) (supply.le_index _)))

/-- The stage-`n` instance witness is fresh for the body being witnessed. -/
theorem witnessInstanceBody_fresh_selected
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    NoConstOccurrence
      (param (enum n).1 (supply.index
        (witnessIndex (witnessInstanceChainUsing supply T₀ enum n) (enum n))))
      (enum n).2 := by
  exact noConstOccurrence_param_of_ge _ (enum n).2
    (le_trans (le_max_right _ _) (supply.le_index _))

/-- Finite stages of the pair-saturation instance chain preserve omission of any
formula fresh for the witness supply. -/
theorem witnessInstanceTheoryUsing_omits
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T₀ θ)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ)
    (hθ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) θ) :
    ∀ n, ¬ ClosedTheorySet.Provable (Const := WithParams Const)
      (witnessInstanceTheoryUsing supply T₀ enum n) θ := by
  intro n
  induction n with
  | zero =>
      simpa [witnessInstanceTheoryUsing_zero] using hNot
  | succ n ih =>
      classical
      rw [witnessInstanceTheoryUsing_succ]
      by_cases hEx : ClosedTheorySet.Provable (Const := WithParams Const)
          (T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n}) (.ex (enum n).2)
      · simp [hEx]
        exact not_provable_insert_fresh_instance_of_ex_provable
          (Const := WithParams Const)
          (param (enum n).1 (supply.index
            (witnessIndex (witnessInstanceChainUsing supply T₀ enum n) (enum n))))
          ih
          (by simpa [witnessInstanceTheoryUsing] using hEx)
          (witnessInstanceTheoryUsing_fresh_selected
            (Base := Base) (Const := Const) supply T₀ enum hT0 n)
          (witnessInstanceBody_fresh_selected
            (Base := Base) (Const := Const) supply T₀ enum n)
          (hθ (enum n).1 _)
      · simp [hEx]
        exact ih

/-- The omission-preserving instance chain is monotone at each successor stage. -/
theorem witnessInstanceChainUsing_subset_succ
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    witnessInstanceChainUsing supply T₀ enum n ⊆
      witnessInstanceChainUsing supply T₀ enum (n + 1) := by
  intro ψ hψ
  classical
  simp only [witnessInstanceChainUsing]
  by_cases hEx : ClosedTheorySet.Provable (Const := WithParams Const)
      (T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n}) (.ex (enum n).2)
  · simp [hEx, hψ]
  · simp [hEx, hψ]

/-- Monotonicity of the finite omission-preserving instance chain. -/
theorem witnessInstanceChainUsing_mono
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) {m n : Nat} (h : m ≤ n) :
    witnessInstanceChainUsing supply T₀ enum m ⊆
      witnessInstanceChainUsing supply T₀ enum n := by
  induction n, h using Nat.le_induction with
  | base => exact List.Subset.refl _
  | succ n _ ih =>
      exact List.Subset.trans ih
        (witnessInstanceChainUsing_subset_succ supply T₀ enum n)

/-- Monotonicity of the raw finite instance theories. -/
theorem witnessInstanceTheoryUsing_mono
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) {m n : Nat} (h : m ≤ n) :
    witnessInstanceTheoryUsing supply T₀ enum m ⊆
      witnessInstanceTheoryUsing supply T₀ enum n := by
  intro ψ hψ
  simp only [witnessInstanceTheoryUsing, Set.mem_union, Set.mem_setOf_eq] at hψ ⊢
  rcases hψ with h0 | hc
  · exact Or.inl h0
  · exact Or.inr (witnessInstanceChainUsing_mono supply T₀ enum h hc)

/-- The limit of the omission-preserving instance chain. -/
noncomputable def witnessInstanceLimitUsing
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) : ClosedTheorySet (WithParams Const) :=
  T₀ ∪ {ψ | ∃ n, ψ ∈ witnessInstanceChainUsing supply T₀ enum n}

/-- The base theory is contained in the omission-preserving instance limit. -/
theorem subset_witnessInstanceLimitUsing
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) :
    ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T₀ →
      ψ ∈ witnessInstanceLimitUsing supply T₀ enum :=
  fun hψ => Set.mem_union_left _ hψ

/-- A finite set of formulas drawn from the instance limit already occurs at one
finite instance stage. -/
theorem exists_stage_instance_using
    (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const)) (enum : Nat → Body Const) :
    ∀ (Γ : List (ClosedFormula (WithParams Const))),
      (∀ ψ ∈ Γ, ψ ∈ witnessInstanceLimitUsing supply T₀ enum) →
      ∃ N, ∀ ψ ∈ Γ, ψ ∈ witnessInstanceTheoryUsing supply T₀ enum N
  | [], _ => ⟨0, by intro ψ hψ; cases hψ⟩
  | a :: Γ, hΓ => by
      obtain ⟨N, hN⟩ :=
        exists_stage_instance_using supply T₀ enum Γ
          (fun ψ hψ => hΓ ψ (List.mem_cons_of_mem _ hψ))
      have ha := hΓ a (List.mem_cons_self)
      simp only [witnessInstanceLimitUsing, Set.mem_union, Set.mem_setOf_eq] at ha
      rcases ha with ha0 | ⟨na, hna⟩
      · refine ⟨N, fun ψ hψ => ?_⟩
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact Set.mem_union_left _ ha0
        · exact hN ψ hψ'
      · refine ⟨max N na, fun ψ hψ => ?_⟩
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact Set.mem_union_right _
            (witnessInstanceChainUsing_mono supply T₀ enum (le_max_right N na) hna)
        · exact witnessInstanceTheoryUsing_mono supply T₀ enum
            (le_max_left N na) (hN ψ hψ')

/-- The omission-preserving instance limit still omits any formula fresh for the
witness supply that was not derivable from the base theory. -/
theorem witnessInstanceLimitUsing_omits
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T₀ θ)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ)
    (hθ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) θ) :
    ¬ ClosedTheorySet.Provable (Const := WithParams Const)
      (witnessInstanceLimitUsing supply T₀ enum) θ := by
  intro hProv
  rcases hProv with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ := exists_stage_instance_using supply T₀ enum Γ hΓ
  exact witnessInstanceTheoryUsing_omits supply T₀ enum hNot hT0 hθ N ⟨Γ, hN, d⟩

/-- Fairness condition for pair saturation: every existential body appears again
at or after any finite stage. -/
def BodyFairAfter (enum : Nat → Body Const) : Prop :=
  ∀ b : Body Const, ∀ N : Nat, ∃ n, N ≤ n ∧ enum n = b

/-- The fair omission-preserving instance limit has the existential witness
property. -/
theorem exists_witnessInstanceLimitUsing
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (hfair : BodyFairAfter (Const := Const) enum) :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      ClosedTheorySet.Provable (Const := WithParams Const)
        (witnessInstanceLimitUsing supply T₀ enum) (.ex φ) →
      ∃ t : ClosedTerm (WithParams Const) σ,
        instantiate (Base := Base) t φ ∈ witnessInstanceLimitUsing supply T₀ enum := by
  intro σ φ hEx
  rcases hEx with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ := exists_stage_instance_using supply T₀ enum Γ hΓ
  have hExStage : ClosedTheorySet.Provable (Const := WithParams Const)
      (witnessInstanceTheoryUsing supply T₀ enum N) (.ex φ) :=
    ⟨Γ, hN, d⟩
  obtain ⟨n, hNn, hn⟩ := hfair ⟨σ, φ⟩ N
  have hExAtN : ClosedTheorySet.Provable (Const := WithParams Const)
      (witnessInstanceTheoryUsing supply T₀ enum n) (.ex φ) :=
    ClosedTheorySet.provable_mono (Const := WithParams Const)
      (T := witnessInstanceTheoryUsing supply T₀ enum N)
      (U := witnessInstanceTheoryUsing supply T₀ enum n)
      (by intro ψ hψ; exact witnessInstanceTheoryUsing_mono supply T₀ enum hNn hψ)
      hExStage
  rcases hEnum : enum n with ⟨ρ, χ⟩
  have hEq : ρ = σ ∧ HEq χ φ := by
    simpa [hEnum, Sigma.ext_iff] using hn
  rcases hEq with ⟨hρ, hχ⟩
  subst hρ
  cases hχ
  let k := supply.index (witnessIndex (witnessInstanceChainUsing supply T₀ enum n) ⟨ρ, χ⟩)
  refine ⟨.const (param ρ k), ?_⟩
  refine Set.mem_union_right _ ?_
  refine ⟨n + 1, ?_⟩
  have hExRaw : ClosedTheorySet.Provable (Const := WithParams Const)
      (T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n}) (.ex χ) := by
    simpa [witnessInstanceTheoryUsing] using hExAtN
  have hExRawEnum : ClosedTheorySet.Provable (Const := WithParams Const)
      (T₀ ∪ {ψ | ψ ∈ witnessInstanceChainUsing supply T₀ enum n}) (.ex (enum n).2) := by
    rw [hEnum]
    exact hExRaw
  rw [witnessInstanceChainUsing]
  simp only [hExRawEnum, if_true, List.mem_cons]
  left
  rw [hEnum]

/-- Membership form of the fair instance-limit witness property. -/
theorem exists_witnessInstanceLimitUsing_of_mem
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (hfair : BodyFairAfter (Const := Const) enum) :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      (.ex φ : ClosedFormula (WithParams Const)) ∈
        witnessInstanceLimitUsing supply T₀ enum →
      ∃ t : ClosedTerm (WithParams Const) σ,
        instantiate (Base := Base) t φ ∈ witnessInstanceLimitUsing supply T₀ enum := by
  intro σ φ hEx
  exact exists_witnessInstanceLimitUsing supply T₀ enum hfair
    (ClosedTheorySet.provable_of_mem (Const := WithParams Const) hEx)

/-- Consistency is preserved by the fair instance limit whenever the base is
consistent and fresh for the witness supply. -/
theorem witnessInstanceLimitUsing_consistent
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T₀)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ) :
    ClosedTheorySet.Consistent (Const := WithParams Const)
      (witnessInstanceLimitUsing supply T₀ enum) := by
  exact witnessInstanceLimitUsing_omits supply T₀ enum hCons hT0
    (by intro σ k; exact NoConstOccurrence.bot)

namespace ClosedTheorySet

/-- The deductive closure of a closed theory set, represented as all formulas
provable from it. -/
def provableClosure (T : ClosedTheorySet Const) : ClosedTheorySet Const :=
  fun φ => Provable (Const := Const) T φ

/-- Every formula in a theory belongs to its deductive closure. -/
theorem subset_provableClosure (T : ClosedTheorySet Const) :
    ∀ {φ : ClosedFormula Const}, φ ∈ T → φ ∈ provableClosure (Const := Const) T := by
  intro φ hφ
  exact provable_of_mem (Const := Const) hφ

/-- A finite derivation whose hypotheses are each provable from `T` gives a
proof from `T`. -/
theorem provable_of_closedTheory_provable_hyps
    {T : ClosedTheorySet Const} :
    ∀ {Γ : ClosedTheory Const} {φ : ClosedFormula Const},
      (∀ ψ, ψ ∈ Γ → Provable (Const := Const) T ψ) →
      ClosedTheory.Provable (Const := Const) Γ φ →
      Provable (Const := Const) T φ
  | [], φ, _hΓ, d =>
      provable_of_closedTheory (Const := Const) (T := T)
        (hΔ := by intro ψ hψ; cases hψ) d
  | ψ :: Γ, φ, hΓ, d => by
      have hImpDer : ClosedTheory.Provable (Const := Const) Γ (.imp ψ φ) :=
        ExtDerivation.impI d
      have hImp : Provable (Const := Const) T (.imp ψ φ) :=
        provable_of_closedTheory_provable_hyps
          (T := T)
          (Γ := Γ)
          (φ := .imp ψ φ)
          (fun ξ hξ => hΓ ξ (List.mem_cons_of_mem _ hξ))
          hImpDer
      have hψ : Provable (Const := Const) T ψ :=
        hΓ ψ List.mem_cons_self
      exact provable_mp (Const := Const) hImp hψ

/-- Provability from the deductive closure is the same as provability from the
original theory. -/
theorem provable_of_provableClosure
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (h : Provable (Const := Const) (provableClosure (Const := Const) T) φ) :
    Provable (Const := Const) T φ := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact provable_of_closedTheory_provable_hyps
    (Const := Const) (T := T)
    (fun ψ hψ => hΓ ψ hψ) d

/-- The provability closure is deductively closed. -/
theorem provableClosure_deductivelyClosed (T : ClosedTheorySet Const) :
    DeductivelyClosed (Const := Const) (provableClosure (Const := Const) T) := by
  intro φ hφ
  exact provable_of_provableClosure (Const := Const) hφ

/-- Consistency transfers from a theory to its provability closure. -/
theorem provableClosure_consistent {T : ClosedTheorySet Const}
    (hCons : Consistent (Const := Const) T) :
    Consistent (Const := Const) (provableClosure (Const := Const) T) := by
  intro hbot
  exact hCons (provable_of_provableClosure (Const := Const) hbot)

/-- Omission of a formula by provability is exactly omission from the provability
closure. -/
theorem not_mem_provableClosure_of_not_provable
    {T : ClosedTheorySet Const} {θ : ClosedFormula Const}
    (hθ : ¬ Provable (Const := Const) T θ) :
    θ ∉ provableClosure (Const := Const) T := by
  exact hθ

end ClosedTheorySet

/-- The provability closure of a fair instance limit is witnessed. -/
theorem provableClosure_witnessInstanceLimitUsing_witnessed
    (supply : WitnessSupply) (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (hfair : BodyFairAfter (Const := Const) enum) :
    ∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
      (.ex φ : ClosedFormula (WithParams Const)) ∈
        ClosedTheorySet.provableClosure
          (Const := WithParams Const) (witnessInstanceLimitUsing supply T₀ enum) →
      ∃ t : ClosedTerm (WithParams Const) σ,
        instantiate (Base := Base) t φ ∈
          ClosedTheorySet.provableClosure
            (Const := WithParams Const) (witnessInstanceLimitUsing supply T₀ enum) := by
  intro σ φ hEx
  obtain ⟨t, ht⟩ :=
    exists_witnessInstanceLimitUsing supply T₀ enum hfair hEx
  exact ⟨t,
    ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const) (witnessInstanceLimitUsing supply T₀ enum) ht⟩

/-- The provability closure of the fair instance limit is a consistent,
deductively closed, witnessed extension that preserves the target omission. -/
theorem exists_closed_witnessed_instanceLimit_separating
    (supply : WitnessSupply) {T₀ : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const) (hfair : BodyFairAfter (Const := Const) enum)
    {θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T₀ θ)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ)
    (hθ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) θ) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T₀ → ψ ∈ U) ∧
      ClosedTheorySet.DeductivelyClosed (Const := WithParams Const) U ∧
      ClosedTheorySet.Consistent (Const := WithParams Const) U ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        (.ex φ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t φ ∈ U) ∧
      θ ∉ U := by
  let L := witnessInstanceLimitUsing supply T₀ enum
  let U : ClosedTheorySet (WithParams Const) :=
    ClosedTheorySet.provableClosure (Const := WithParams Const) L
  have hOmitL : ¬ ClosedTheorySet.Provable (Const := WithParams Const) L θ :=
    witnessInstanceLimitUsing_omits supply T₀ enum hNot hT0 hθ
  have hConsT0 : ClosedTheorySet.Consistent (Const := WithParams Const) T₀ := by
    intro hbot
    rcases hbot with ⟨Γ, hΓ, d⟩
    exact hNot ⟨Γ, hΓ, ExtDerivation.botE d⟩
  have hConsL : ClosedTheorySet.Consistent (Const := WithParams Const) L :=
    witnessInstanceLimitUsing_consistent supply T₀ enum hConsT0 hT0
  refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ
    exact ClosedTheorySet.subset_provableClosure
      (Const := WithParams Const) L
      (subset_witnessInstanceLimitUsing supply T₀ enum hψ)
  · exact ClosedTheorySet.provableClosure_deductivelyClosed
      (Const := WithParams Const) L
  · exact ClosedTheorySet.provableClosure_consistent
      (Const := WithParams Const) hConsL
  · intro σ φ hEx
    exact provableClosure_witnessInstanceLimitUsing_witnessed
      (Base := Base) (Const := Const) supply T₀ enum hfair hEx
  · exact ClosedTheorySet.not_mem_provableClosure_of_not_provable
      (Const := WithParams Const) hOmitL

/-- Freshness for a supplied reserve is preserved when inserting a formula that
is itself fresh for that reserve. -/
theorem fresh_for_supply_insert
    (supply : WitnessSupply) {T₀ : ClosedTheorySet (WithParams Const)}
    {δ : ClosedFormula (WithParams Const)}
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ)
    (hδ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) δ) :
    ∀ ψ ∈ insert δ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ := by
  intro ψ hψ σ k
  rcases Set.mem_insert_iff.mp hψ with rfl | hψT
  · exact hδ σ k
  · exact hT0 ψ hψT σ k

/-- Raw disjunction-branch choice over an arbitrary theory with a reserved
parameter supply.  This is the substrate for alternating prime/witness
constructions: closure is not taken here, so future-layer freshness can still be
tracked on the next raw stage. -/
theorem exists_raw_or_branch_supply_omitting
    (supply : WitnessSupply) {T₀ : ClosedTheorySet (WithParams Const)}
    {φ ψ θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T₀ θ)
    (hOr : ClosedTheorySet.Provable (Const := WithParams Const) T₀ (.or φ ψ))
    (hT0 : ∀ ξ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ)
    (hφ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) φ)
    (hψ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ) :
    ∃ δ : ClosedFormula (WithParams Const),
      (δ = φ ∨ δ = ψ) ∧
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) (insert δ T₀) θ ∧
      (∀ ξ ∈ insert δ T₀, ∀ (σ : Ty Base) (k : Nat),
        NoConstOccurrence (param σ (supply.index k)) ξ) := by
  have hBranch :=
    exists_or_branch_omitting (Const := WithParams Const)
      (T := T₀) (φ := φ) (ψ := ψ) (θ := θ) hNot hOr
  rcases hBranch with hLeft | hRight
  · exact ⟨φ, Or.inl rfl, hLeft,
      fresh_for_supply_insert
        (Base := Base) (Const := Const) supply hT0 hφ⟩
  · exact ⟨ψ, Or.inr rfl, hRight,
      fresh_for_supply_insert
        (Base := Base) (Const := Const) supply hT0 hψ⟩

/-- One disjunction-prime decision step compatible with fair witnessed
instance-saturation: if `T₀ ⊢ φ ∨ ψ` while still omitting `θ`, at least one
branch can be inserted and then closed/witnessed without deriving `θ`. -/
theorem exists_closed_witnessed_or_branch_instanceLimit_separating
    (supply : WitnessSupply) {T₀ : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const) (hfair : BodyFairAfter (Const := Const) enum)
    {φ ψ θ : ClosedFormula (WithParams Const)}
    (hNot : ¬ ClosedTheorySet.Provable (Const := WithParams Const) T₀ θ)
    (hOr : ClosedTheorySet.Provable (Const := WithParams Const) T₀ (.or φ ψ))
    (hT0 : ∀ ξ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ξ)
    (hφ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) φ)
    (hψ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ)
    (hθ : ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) θ) :
    (∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ξ : ClosedFormula (WithParams Const)}, ξ ∈ T₀ → ξ ∈ U) ∧
      φ ∈ U ∧
      ClosedTheorySet.DeductivelyClosed (Const := WithParams Const) U ∧
      ClosedTheorySet.Consistent (Const := WithParams Const) U ∧
      (∀ {σ : Ty Base} {χ : Formula (WithParams Const) [σ]},
        (.ex χ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t χ ∈ U) ∧
      θ ∉ U) ∨
    (∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ξ : ClosedFormula (WithParams Const)}, ξ ∈ T₀ → ξ ∈ U) ∧
      ψ ∈ U ∧
      ClosedTheorySet.DeductivelyClosed (Const := WithParams Const) U ∧
      ClosedTheorySet.Consistent (Const := WithParams Const) U ∧
      (∀ {σ : Ty Base} {χ : Formula (WithParams Const) [σ]},
        (.ex χ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t χ ∈ U) ∧
      θ ∉ U) := by
  classical
  have hBranch :=
    exists_or_branch_omitting (Const := WithParams Const)
      (T := T₀) (φ := φ) (ψ := ψ) (θ := θ) hNot hOr
  rcases hBranch with hφNot | hψNot
  · left
    obtain ⟨U, hExt, hClosed, hCons, hWit, hOmit⟩ :=
      exists_closed_witnessed_instanceLimit_separating
        (Base := Base) (Const := Const) supply
        (T₀ := insert φ T₀) enum hfair hφNot
        (fresh_for_supply_insert
          (Base := Base) (Const := Const) supply hT0 hφ)
        hθ
    refine ⟨U, ?_, ?_, hClosed, hCons, hWit, hOmit⟩
    · intro ξ hξ
      exact hExt (Set.mem_insert_of_mem φ hξ)
    · exact hExt (Set.mem_insert φ T₀)
  · right
    obtain ⟨U, hExt, hClosed, hCons, hWit, hOmit⟩ :=
      exists_closed_witnessed_instanceLimit_separating
        (Base := Base) (Const := Const) supply
        (T₀ := insert ψ T₀) enum hfair hψNot
        (fresh_for_supply_insert
          (Base := Base) (Const := Const) supply hT0 hψ)
        hθ
    refine ⟨U, ?_, ?_, hClosed, hCons, hWit, hOmit⟩
    · intro ξ hξ
      exact hExt (Set.mem_insert_of_mem ψ hξ)
    · exact hExt (Set.mem_insert ψ T₀)

/-! ## Monotonicity and the limit -/

theorem witnessChainUsing_subset_succ (supply : WitnessSupply)
    (enum : Nat → Body Const) (n : Nat) :
    witnessChainUsing supply enum n ⊆ witnessChainUsing supply enum (n + 1) := by
  intro x hx
  rw [witnessChainUsing]
  exact List.mem_cons_of_mem _ hx

theorem witnessChainUsing_mono (supply : WitnessSupply)
    (enum : Nat → Body Const) {m n : Nat} (h : m ≤ n) :
    witnessChainUsing supply enum m ⊆ witnessChainUsing supply enum n := by
  induction n, h using Nat.le_induction with
  | base => exact List.Subset.refl _
  | succ n hn ih => exact List.Subset.trans ih (witnessChainUsing_subset_succ supply enum n)

theorem witnessChain_subset_succ (enum : Nat → Body Const) (n : Nat) :
    witnessChain enum n ⊆ witnessChain enum (n + 1) := by
  exact witnessChainUsing_subset_succ identityWitnessSupply enum n

theorem witnessChain_mono (enum : Nat → Body Const) {m n : Nat} (h : m ≤ n) :
    witnessChain enum m ⊆ witnessChain enum n := by
  exact witnessChainUsing_mono identityWitnessSupply enum h

theorem witnessTheoryUsing_mono (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) {m n : Nat} (h : m ≤ n) :
    witnessTheoryUsing supply T₀ enum m ⊆ witnessTheoryUsing supply T₀ enum n := by
  intro ψ hψ
  simp only [witnessTheoryUsing, Set.mem_union, Set.mem_setOf_eq] at hψ ⊢
  rcases hψ with h0 | hc
  · exact Or.inl h0
  · exact Or.inr (witnessChainUsing_mono supply enum h hc)

theorem witnessTheory_mono (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) {m n : Nat} (h : m ≤ n) :
    witnessTheory T₀ enum m ⊆ witnessTheory T₀ enum n := by
  exact witnessTheoryUsing_mono identityWitnessSupply T₀ enum h

/-- **Finite character.**  Any finite set of formulas drawn from the saturation
limit already lives at a single finite stage. -/
theorem exists_stage_using (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const)) (enum : Nat → Body Const) :
    ∀ (Γ : List (ClosedFormula (WithParams Const))),
      (∀ ψ ∈ Γ, ψ ∈ witnessLimitUsing supply T₀ enum) →
      ∃ N, ∀ ψ ∈ Γ, ψ ∈ witnessTheoryUsing supply T₀ enum N
  | [], _ => ⟨0, by intro ψ hψ; cases hψ⟩
  | a :: Γ, hΓ => by
      obtain ⟨N, hN⟩ :=
        exists_stage_using supply T₀ enum Γ
          (fun ψ hψ => hΓ ψ (List.mem_cons_of_mem _ hψ))
      have ha := hΓ a (List.mem_cons_self)
      simp only [witnessLimitUsing, Set.mem_union, Set.mem_setOf_eq] at ha
      rcases ha with ha0 | ⟨na, hna⟩
      · refine ⟨N, fun ψ hψ => ?_⟩
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact Set.mem_union_left _ ha0
        · exact hN ψ hψ'
      · refine ⟨max N na, fun ψ hψ => ?_⟩
        rcases List.mem_cons.mp hψ with rfl | hψ'
        · exact Set.mem_union_right _
            (witnessChainUsing_mono supply enum (le_max_right N na) hna)
        · exact witnessTheoryUsing_mono supply T₀ enum (le_max_left N na) (hN ψ hψ')

theorem exists_stage (T₀ : ClosedTheorySet (WithParams Const)) (enum : Nat → Body Const) :
    ∀ (Γ : List (ClosedFormula (WithParams Const))),
      (∀ ψ ∈ Γ, ψ ∈ witnessLimit T₀ enum) →
      ∃ N, ∀ ψ ∈ Γ, ψ ∈ witnessTheory T₀ enum N :=
  exists_stage_using identityWitnessSupply T₀ enum

/-- **Consistency of the Henkin saturation.**  The full witnessed theory is
consistent: any refutation uses finitely many axioms, hence lives at a consistent
finite stage. -/
theorem witnessLimitUsing_consistent (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T₀)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat),
      NoConstOccurrence (param σ (supply.index k)) ψ) :
    ClosedTheorySet.Consistent (Const := WithParams Const)
      (witnessLimitUsing supply T₀ enum) := by
  intro hbot
  rcases hbot with ⟨Γ, hΓ, d⟩
  obtain ⟨N, hN⟩ := exists_stage_using supply T₀ enum Γ hΓ
  exact witnessTheoryUsing_consistent supply T₀ enum hCons hT0 N ⟨Γ, hN, d⟩

theorem witnessLimit_consistent (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T₀)
    (hT0 : ∀ ψ ∈ T₀, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ) :
    ClosedTheorySet.Consistent (Const := WithParams Const) (witnessLimit T₀ enum) := by
  exact witnessLimitUsing_consistent identityWitnessSupply T₀ enum hCons hT0

theorem subset_witnessLimitUsing (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) :
    ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T₀ →
      ψ ∈ witnessLimitUsing supply T₀ enum :=
  fun hψ => Set.mem_union_left _ hψ

theorem subset_witnessLimit (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) :
    ∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T₀ → ψ ∈ witnessLimit T₀ enum :=
  subset_witnessLimitUsing identityWitnessSupply T₀ enum

theorem witnessAxiom_mem_witnessLimitUsing (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    witnessAxiom (param (enum n).1 (supply.index
        (witnessIndex (witnessChainUsing supply enum n) (enum n))))
        (enum n).2 ∈ witnessLimitUsing supply T₀ enum := by
  refine Set.mem_union_right _ ?_
  refine ⟨n + 1, ?_⟩
  rw [witnessChainUsing]
  exact List.mem_cons_self

theorem witnessAxiom_mem_witnessLimit (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (n : Nat) :
    witnessAxiom (param (enum n).1 (witnessIndex (witnessChain enum n) (enum n)))
        (enum n).2 ∈ witnessLimit T₀ enum := by
  change witnessAxiom
      (param (enum n).1 (identityWitnessSupply.index
        (witnessIndex (witnessChainUsing identityWitnessSupply enum n) (enum n))))
      (enum n).2 ∈ witnessLimitUsing identityWitnessSupply T₀ enum
  refine Set.mem_union_right _ ?_
  refine ⟨n + 1, ?_⟩
  rw [witnessChainUsing]
  exact List.mem_cons_self

/-- **Existence property (axiom form).**  For every body in the range of the
enumeration, the saturation contains a witness axiom `(∃x. φ) → φ[c]` whose witness
`c` is a closed parameter constant. -/
theorem exists_witnessAxiomUsing (supply : WitnessSupply)
    (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (b : Body Const) (hb : ∃ n, enum n = b) :
    ∃ k : Nat, witnessAxiom (param b.1 k) b.2 ∈ witnessLimitUsing supply T₀ enum := by
  obtain ⟨n, hn⟩ := hb
  subst hn
  exact ⟨supply.index (witnessIndex (witnessChainUsing supply enum n) (enum n)),
    witnessAxiom_mem_witnessLimitUsing supply T₀ enum n⟩

theorem exists_witnessAxiom (T₀ : ClosedTheorySet (WithParams Const))
    (enum : Nat → Body Const) (b : Body Const) (hb : ∃ n, enum n = b) :
    ∃ k : Nat, witnessAxiom (param b.1 k) b.2 ∈ witnessLimit T₀ enum := by
  exact exists_witnessAxiomUsing identityWitnessSupply T₀ enum b hb

end Mettapedia.Logic.HOL
