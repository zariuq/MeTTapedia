import Mathlib.Computability.PartrecCode
import Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet.HutterEnumeration

/-!
# Levin/Hutter Enumeration Theorem (Lower-Semicomputable Semimeasures, Finite Alphabet)

This is the finite-alphabet analogue of:
* `Mettapedia/UniversalAI/UniversalPrediction/HutterEnumerationTheoremSemimeasure.lean`.

We implement a concrete, surjective enumeration of all Hutter-lower-semicomputable semimeasures
on `Word α := List α`, indexed by `Nat.Partrec.Code`.

Key idea (same as the binary development):
* A lower semicomputable semimeasure `ξ` comes with a computable, monotone dyadic approximation
  `a x n / 2^n → (ξ x).toReal`.
* Mathlib gives a universal partial recursive evaluator `Nat.Partrec.Code.eval`, so we can
  extract a code `c` for the dyadic witness `a`.
* We then define `evalLSC c` as “the unique semimeasure witnessed by `c`”, defaulting to `0`.

This is the “mixture-route” level needed for the Chapter‑3 dominance→regret theorems:
once the enumeration exists, the universal mixture `xi` is definable without any toy axioms.
-/

noncomputable section

namespace Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet

open scoped Classical BigOperators

open Mettapedia.Computability.Hutter
open FiniteAlphabet

namespace HutterEnumerationTheoremSemimeasure

variable {α : Type*} [Fintype α] [Primcodable α]

/-! ## A harmless default semimeasure -/

noncomputable def zeroSemimeasure : Semimeasure α :=
  { toFun := fun _ => 0
    superadditive' := by
      intro x
      simp
    root_le_one' := by
      simp }

/-! ## Extracting dyadic witnesses from `Nat.Partrec.Code` -/

/-- Interpret a `Nat.Partrec.Code` as a total `ℕ`-valued function on `(Word α × ℕ)` by
running the code on `encode (x,n)` and defaulting to `0` if it diverges. -/
noncomputable def approxOfCode (c : Nat.Partrec.Code) (x : Word α) (n : ℕ) : ℕ :=
  match (Nat.Partrec.Code.eval c (Encodable.encode (x, n))).toOption with
  | none => 0
  | some k => (Encodable.decode (α := ℕ) k).getD 0

/-- A code `c` witnesses a semimeasure `ξ` if `approxOfCode c` gives a monotone dyadic
approximation converging to `ξ(x)` for every prefix `x`. -/
def CodeWitness (c : Nat.Partrec.Code) (ξ : Semimeasure α) : Prop :=
  (∀ x : Word α, Monotone (fun n => dyadic (approxOfCode c x n) n)) ∧
    ∀ x : Word α,
      Filter.Tendsto (fun n => dyadic (approxOfCode c x n) n) Filter.atTop (nhds ((ξ x).toReal))

theorem codeWitness_unique (c : Nat.Partrec.Code) {ξ₁ ξ₂ : Semimeasure α}
    (h₁ : CodeWitness (α := α) c ξ₁) (h₂ : CodeWitness (α := α) c ξ₂) : ξ₁ = ξ₂ := by
  -- Two limits of the same sequence must agree pointwise.
  have hEq_toReal : ∀ x : Word α, (ξ₁ x).toReal = (ξ₂ x).toReal := by
    intro x
    exact tendsto_nhds_unique (h₁.2 x) (h₂.2 x)
  -- `ENNReal.toReal` is injective on semimeasure values (bounded by `1`).
  have hEq_val : ∀ x : Word α, ξ₁ x = ξ₂ x := by
    intro x
    have hTop₁ : ξ₁ x ≠ (⊤ : ENNReal) := Semimeasure.ne_top ξ₁ x
    have hTop₂ : ξ₂ x ≠ (⊤ : ENNReal) := Semimeasure.ne_top ξ₂ x
    exact (ENNReal.toReal_eq_toReal_iff' hTop₁ hTop₂).1 (hEq_toReal x)
  -- Conclude equality of structures by proof irrelevance on the Prop fields.
  cases ξ₁ with
  | mk f₁ s₁ r₁ =>
    cases ξ₂ with
    | mk f₂ s₂ r₂ =>
      have hf : f₁ = f₂ := funext hEq_val
      cases hf
      have hs : s₁ = s₂ := Subsingleton.elim _ _
      have hr : r₁ = r₂ := Subsingleton.elim _ _
      cases hs
      cases hr
      rfl

/-! ## From a dyadic witness to a code -/

omit [Fintype α] in
/-- If `a` is a total computable dyadic witness, then it has a `Nat.Partrec.Code`
which reproduces it on all inputs. -/
theorem exists_code_of_computable₂ (a : Word α → ℕ → ℕ) (ha : Computable₂ a) :
    ∃ c : Nat.Partrec.Code, ∀ x n, approxOfCode (α := α) c x n = a x n := by
  classical
  -- Let `f : Word α × ℕ → ℕ` be the uncurried version of `a`.
  let f : (Word α × ℕ) → ℕ := fun p => a p.1 p.2
  have hf : Computable f := ha
  have hf' : Partrec (f : (Word α × ℕ) →. ℕ) := hf
  have hfNat :
      Nat.Partrec
        (fun n : ℕ =>
          Part.bind (Encodable.decode (α := Word α × ℕ) n) fun p =>
            (f p : Part ℕ).map Encodable.encode) := by
    simpa [Partrec] using hf'
  rcases (Nat.Partrec.Code.exists_code).1 hfNat with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro x n
  unfold approxOfCode
  have hEval :
      Nat.Partrec.Code.eval c (Encodable.encode (x, n)) =
        Part.bind (Encodable.decode (α := Word α × ℕ) (Encodable.encode (x, n)))
          (fun p => (f p : Part ℕ).map Encodable.encode) := by
    simpa using congrArg (fun g => g (Encodable.encode (x, n))) hc
  have hdecode :
      Encodable.decode (α := Word α × ℕ) (Encodable.encode (x, n)) = some (x, n) :=
    Encodable.encodek (x, n)
  have hEval' :
      Nat.Partrec.Code.eval c (Encodable.encode (x, n)) = Part.some (Encodable.encode (a x n)) := by
    calc
      Nat.Partrec.Code.eval c (Encodable.encode (x, n))
          = Part.bind (Encodable.decode (α := Word α × ℕ) (Encodable.encode (x, n)))
              (fun p => (f p : Part ℕ).map Encodable.encode) := hEval
      _ = Part.bind (some (x, n)) (fun p => (f p : Part ℕ).map Encodable.encode) := by
            simp
      _ = (f (x, n) : Part ℕ).map Encodable.encode := by
            simp [Part.bind_some]
      _ = Part.some (Encodable.encode (f (x, n))) := by
            simp [Part.map_some]
      _ = Part.some (Encodable.encode (a x n)) := rfl
  rw [hEval']
  simp

/-! ## A concrete enumeration of LSC semimeasures -/

/-- Interpret a code as the (unique) semimeasure it lower-semicomputes, if any;
otherwise return a harmless default semimeasure. -/
noncomputable def evalLSC (c : Nat.Partrec.Code) : Semimeasure α :=
  if h : ∃ ξ : Semimeasure α, CodeWitness (α := α) c ξ then
    Classical.choose h
  else
    zeroSemimeasure (α := α)

theorem evalLSC_spec {c : Nat.Partrec.Code} (h : ∃ ξ : Semimeasure α, CodeWitness (α := α) c ξ) :
    CodeWitness (α := α) c (evalLSC (α := α) c) := by
  classical
  simp [evalLSC, h, Classical.choose_spec]

theorem surj_evalLSC :
    ∀ ξ : Semimeasure α, LowerSemicomputableSemimeasure (α := α) ξ → ∃ c : Nat.Partrec.Code, evalLSC (α := α) c = ξ := by
  intro ξ hξ
  rcases hξ with ⟨a, ha_comp, ha_mono, ha_tendsto⟩
  rcases exists_code_of_computable₂ (α := α) (a := a) ha_comp with ⟨c, hc⟩
  -- Show this code witnesses `ξ`.
  have hW : CodeWitness (α := α) c ξ := by
    refine ⟨?_, ?_⟩
    · intro x
      simpa [hc] using ha_mono x
    · intro x
      simpa [hc] using ha_tendsto x
  have hex : ∃ ξ' : Semimeasure α, CodeWitness (α := α) c ξ' := ⟨ξ, hW⟩
  refine ⟨c, ?_⟩
  -- `evalLSC c` chooses the unique semimeasure witnessed by `c`.
  have hChosen : CodeWitness (α := α) c (evalLSC (α := α) c) := evalLSC_spec (α := α) (c := c) hex
  exact codeWitness_unique (α := α) c hChosen hW

/-- The concrete `LSCSemimeasureEnumeration` (Levin/Hutter enumeration theorem, semimeasure form). -/
noncomputable def lscSemimeasureEnumeration : LSCSemimeasureEnumeration (α := α) :=
  { Code := Nat.Partrec.Code
    eval := evalLSC (α := α)
    surj_eval := surj_evalLSC (α := α) }

end HutterEnumerationTheoremSemimeasure

end Mettapedia.UniversalAI.UniversalPrediction.FiniteAlphabet
