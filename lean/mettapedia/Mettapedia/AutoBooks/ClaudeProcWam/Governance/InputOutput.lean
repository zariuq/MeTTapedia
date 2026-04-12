/-
# Input-Output Logic

Formalization of Input-Output (I/O) logic for deontic reasoning.

I/O logic represents norms as pairs (a, x) meaning:
"Given input a, the output x is obligatory/permitted."

## References

- Makinson & van der Torre (2000): Input-Output Logics
- Parent & van der Torre (2013): Handbook chapter
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Basic

namespace Mettapedia.AutoBooks.ClaudeProcWam.Governance

/-! ## Propositional Language -/

/-- Propositional variables -/
abbrev PropVar := String

/-- Propositional formulas -/
inductive PropFormula where
  | var : PropVar → PropFormula
  | tt : PropFormula
  | ff : PropFormula
  | neg : PropFormula → PropFormula
  | conj : PropFormula → PropFormula → PropFormula
  | disj : PropFormula → PropFormula → PropFormula
  | impl : PropFormula → PropFormula → PropFormula
  deriving DecidableEq, Repr, Inhabited

instance : ToString PropFormula where
  toString f := go f
where
  go : PropFormula → String
    | .var v => v
    | .tt => "⊤"
    | .ff => "⊥"
    | .neg p => s!"¬{go p}"
    | .conj p q => s!"({go p} ∧ {go q})"
    | .disj p q => s!"({go p} ∨ {go q})"
    | .impl p q => s!"({go p} → {go q})"

/-! ## Valuations and Satisfaction -/

/-- A valuation assigns truth values to variables -/
abbrev Valuation := PropVar → Bool

/-- Evaluate a formula under a valuation -/
def PropFormula.eval (v : Valuation) : PropFormula → Bool
  | .var p => v p
  | .tt => true
  | .ff => false
  | .neg φ => !φ.eval v
  | .conj φ ψ => φ.eval v && ψ.eval v
  | .disj φ ψ => φ.eval v || ψ.eval v
  | .impl φ ψ => !φ.eval v || ψ.eval v

/-- Satisfaction: v ⊨ φ -/
def PropFormula.satisfies (v : Valuation) (φ : PropFormula) : Prop :=
  φ.eval v = true

/-- Logical consequence: Γ ⊨ φ -/
def LogicalConsequence (Γ : Set PropFormula) (φ : PropFormula) : Prop :=
  ∀ v : Valuation, (∀ ψ ∈ Γ, PropFormula.satisfies v ψ) → PropFormula.satisfies v φ

/-! ## Norms -/

/-- A norm (conditional directive) -/
structure Norm where
  input : PropFormula
  output : PropFormula
  deriving DecidableEq, Repr

instance : ToString Norm where
  toString n := s!"({n.input}, {n.output})"

/-- A normative code is a set of norms -/
abbrev NormativeCode := Set Norm

/-! ## Derivability -/

/-- Classical consequence closure -/
def Cn (A : Set PropFormula) : Set PropFormula :=
  { φ | LogicalConsequence A φ }

/-! ## Input-Output Operations -/

/-- Helper: get outputs for triggered norms -/
def triggeredOutputs (G : NormativeCode) (derivable : Set PropFormula) : Set PropFormula :=
  { φ | ∃ n ∈ G, n.input ∈ derivable ∧ n.output = φ }

/-- out1: Simple-minded output (unconditional) -/
def out1 (G : NormativeCode) (A : Set PropFormula) : Set PropFormula :=
  Cn (triggeredOutputs G (Cn A))

/-- out2: Basic output (throughput - includes input in output)
    out₂(G, A) = Cn(G(Cn(A)) ∪ A)
    The input facts are available in the output -/
def out2 (G : NormativeCode) (A : Set PropFormula) : Set PropFormula :=
  Cn (triggeredOutputs G (Cn A) ∪ A)

/-- out3: Simple-minded reusable output (fixpoint iteration)
    The outputs can trigger further norms iteratively -/
def out3Aux (G : NormativeCode) (A : Set PropFormula) (fuel : Nat) : Set PropFormula :=
  match fuel with
  | 0 => Cn A
  | n + 1 =>
    let prev := out3Aux G A n
    Cn (triggeredOutputs G prev ∪ prev)

def out3 (G : NormativeCode) (A : Set PropFormula) : Set PropFormula :=
  -- In theory, this is a fixpoint; we approximate with finite iterations
  out3Aux G A 100

/-- out4: Basic reusable output (fixpoint with throughput)
    Combines throughput and iteration -/
def out4Aux (G : NormativeCode) (A : Set PropFormula) (fuel : Nat) : Set PropFormula :=
  match fuel with
  | 0 => Cn A
  | n + 1 =>
    let prev := out4Aux G A n
    Cn (triggeredOutputs G prev ∪ A ∪ prev)

def out4 (G : NormativeCode) (A : Set PropFormula) : Set PropFormula :=
  out4Aux G A 100

/-! ## Relationships Between Operations -/

/-- Cn is monotonic: if A ⊆ B then Cn A ⊆ Cn B -/
theorem Cn_mono (A B : Set PropFormula) (h : A ⊆ B) : Cn A ⊆ Cn B := by
  intro φ hφ
  unfold Cn at hφ ⊢
  simp only [Set.mem_setOf_eq] at hφ ⊢
  intro v hv
  apply hφ
  intro ψ hψ
  exact hv ψ (h hψ)

/-- A ⊆ Cn A: Assumptions are consequences of themselves -/
theorem sub_Cn (A : Set PropFormula) : A ⊆ Cn A := by
  intro φ hφ
  unfold Cn
  simp only [Set.mem_setOf_eq]
  intro v hv
  exact hv φ hφ

/-- out3Aux at step n is contained in step n+1 -/
theorem out3Aux_mono_step (G : NormativeCode) (A : Set PropFormula) (n : Nat) :
    out3Aux G A n ⊆ out3Aux G A (n + 1) := by
  induction n with
  | zero =>
    simp only [out3Aux]
    -- Need to show Cn A ⊆ Cn (triggeredOutputs G (Cn A) ∪ Cn A)
    -- A ⊆ Cn A, and Cn A ⊆ triggeredOutputs G (Cn A) ∪ Cn A
    calc Cn A ⊆ Cn (Cn A) := Cn_mono A (Cn A) (sub_Cn A)
         _ ⊆ Cn (triggeredOutputs G (Cn A) ∪ Cn A) :=
           Cn_mono (Cn A) _ Set.subset_union_right
  | succ m ih =>
    simp only [out3Aux]
    -- out3Aux G A (m + 1) ⊆ out3Aux G A (m + 2)
    -- prev = out3Aux G A m, prev' = out3Aux G A (m + 1)
    -- Show Cn (trig prev ∪ prev) ⊆ Cn (trig prev' ∪ prev')
    have h1 : triggeredOutputs G (out3Aux G A m) ⊆ triggeredOutputs G (out3Aux G A (m + 1)) := by
      intro ψ hψ
      unfold triggeredOutputs at hψ ⊢
      simp only [Set.mem_setOf_eq] at hψ ⊢
      obtain ⟨norm, hnorm, hin, hout⟩ := hψ
      exact ⟨norm, hnorm, ih hin, hout⟩
    have h2 : out3Aux G A m ⊆ out3Aux G A (m + 1) := ih
    have h3 : triggeredOutputs G (out3Aux G A m) ∪ out3Aux G A m ⊆
              triggeredOutputs G (out3Aux G A (m + 1)) ∪ out3Aux G A (m + 1) :=
      Set.union_subset_union h1 h2
    exact Cn_mono _ _ h3

/-- out3Aux is monotonic in fuel -/
theorem out3Aux_mono (G : NormativeCode) (A : Set PropFormula) (m n : Nat)
    (h : m ≤ n) : out3Aux G A m ⊆ out3Aux G A n := by
  induction n with
  | zero =>
    simp only [Nat.le_zero] at h
    rw [h]
  | succ k ih =>
    cases Nat.eq_or_lt_of_le h with
    | inl heq =>
      rw [heq]
    | inr hlt =>
      calc out3Aux G A m ⊆ out3Aux G A k := ih (Nat.lt_succ_iff.mp hlt)
           _ ⊆ out3Aux G A (k + 1) := out3Aux_mono_step G A k

/-- out1 ⊆ out3: Simple-minded is contained in reusable -/
theorem out1_sub_out3 (G : NormativeCode) (A : Set PropFormula) :
    out1 G A ⊆ out3 G A := by
  intro φ hφ
  unfold out3
  -- out1 G A = Cn (triggeredOutputs G (Cn A))
  -- out3Aux G A 1 = Cn (triggeredOutputs G (Cn A) ∪ Cn A)
  -- So out1 G A ⊆ out3Aux G A 1 ⊆ out3Aux G A 100
  apply out3Aux_mono G A 1 100 (by omega)
  simp only [out3Aux]
  unfold out1 at hφ
  apply Cn_mono
  · intro ψ hψ
    left
    exact hψ
  · exact hφ

/-- out4Aux at step n is contained in step n+1 -/
theorem out4Aux_mono_step (G : NormativeCode) (A : Set PropFormula) (n : Nat) :
    out4Aux G A n ⊆ out4Aux G A (n + 1) := by
  induction n with
  | zero =>
    simp only [out4Aux]
    -- Cn A ⊆ Cn (triggeredOutputs G (Cn A) ∪ A ∪ Cn A)
    -- = Cn ((trig ∪ A) ∪ Cn A) by associativity
    -- A ⊆ Cn A, and Cn A is on the right
    have h : A ⊆ triggeredOutputs G (Cn A) ∪ A ∪ Cn A := by
      intro x hx
      -- x ∈ (trig ∪ A) ∪ Cn A
      exact Or.inr (sub_Cn A hx)
    exact Cn_mono A _ h
  | succ m ih =>
    simp only [out4Aux]
    -- Show Cn (trig prev ∪ A ∪ prev) ⊆ Cn (trig prev' ∪ A ∪ prev')
    have h1 : triggeredOutputs G (out4Aux G A m) ⊆ triggeredOutputs G (out4Aux G A (m + 1)) := by
      intro ψ hψ
      unfold triggeredOutputs at hψ ⊢
      simp only [Set.mem_setOf_eq] at hψ ⊢
      obtain ⟨norm, hnorm, hin, hout⟩ := hψ
      exact ⟨norm, hnorm, ih hin, hout⟩
    have h2 : out4Aux G A m ⊆ out4Aux G A (m + 1) := ih
    have h3 : triggeredOutputs G (out4Aux G A m) ∪ A ∪ out4Aux G A m ⊆
              triggeredOutputs G (out4Aux G A (m + 1)) ∪ A ∪ out4Aux G A (m + 1) := by
      intro x hx
      -- hx : x ∈ (trig ∪ A) ∪ prev
      simp only [Set.mem_union] at hx ⊢
      rcases hx with (htrig | hA) | hprev
      · left; left; exact h1 htrig
      · left; right; exact hA
      · right; exact h2 hprev
    exact Cn_mono _ _ h3

/-- out4Aux is monotonic in fuel -/
theorem out4Aux_mono (G : NormativeCode) (A : Set PropFormula) (m n : Nat)
    (h : m ≤ n) : out4Aux G A m ⊆ out4Aux G A n := by
  induction n with
  | zero =>
    simp only [Nat.le_zero] at h
    rw [h]
  | succ k ih =>
    cases Nat.eq_or_lt_of_le h with
    | inl heq => rw [heq]
    | inr hlt =>
      calc out4Aux G A m ⊆ out4Aux G A k := ih (Nat.lt_succ_iff.mp hlt)
           _ ⊆ out4Aux G A (k + 1) := out4Aux_mono_step G A k

/-- out2 ⊆ out4: Basic is contained in basic reusable -/
theorem out2_sub_out4 (G : NormativeCode) (A : Set PropFormula) :
    out2 G A ⊆ out4 G A := by
  intro φ hφ
  unfold out4
  -- out2 G A = Cn (triggeredOutputs G (Cn A) ∪ A)
  -- out4Aux G A 1 = Cn (triggeredOutputs G (Cn A) ∪ A ∪ Cn A)
  -- = Cn ((trig ∪ A) ∪ Cn A)
  -- So out2 G A ⊆ out4Aux G A 1 ⊆ out4Aux G A 100
  apply out4Aux_mono G A 1 100 (by omega)
  simp only [out4Aux]
  unfold out2 at hφ
  -- Show Cn (trig ∪ A) ⊆ Cn ((trig ∪ A) ∪ Cn A)
  have h : triggeredOutputs G (Cn A) ∪ A ⊆ triggeredOutputs G (Cn A) ∪ A ∪ Cn A := by
    intro x hx
    simp only [Set.mem_union] at hx ⊢
    left
    exact hx
  exact Cn_mono _ _ h hφ

/-- out1 ⊆ out2: Adding input to output -/
theorem out1_sub_out2 (G : NormativeCode) (A : Set PropFormula) :
    out1 G A ⊆ out2 G A := by
  intro φ hφ
  unfold out1 at hφ
  unfold out2
  unfold Cn at hφ ⊢
  simp only [Set.mem_setOf_eq] at hφ ⊢
  intro v hv
  apply hφ
  intro ψ hψ
  apply hv
  left
  exact hψ

/-! ## Deontic Operators -/

/-- Obligation: given facts A and norms G, φ is obligatory -/
def Obligation (G : NormativeCode) (A : Set PropFormula) (φ : PropFormula) : Prop :=
  φ ∈ out1 G A

/-- Weak permission: φ is permitted if ¬φ is not obligatory -/
def WeakPermission (G : NormativeCode) (A : Set PropFormula) (φ : PropFormula) : Prop :=
  ¬ Obligation G A (.neg φ)

/-! ## Properties -/

/-- out1 is monotonic in the normative code -/
theorem out1_mono_code (G G' : NormativeCode) (A : Set PropFormula)
    (hGG' : G ⊆ G') : out1 G A ⊆ out1 G' A := by
  intro φ hφ
  unfold out1 at hφ ⊢
  unfold Cn at hφ ⊢
  unfold triggeredOutputs at hφ ⊢
  simp only [Set.mem_setOf_eq] at hφ ⊢
  intro v hv
  apply hφ
  intro ψ hψ
  simp only [Set.mem_setOf_eq] at hψ
  apply hv
  simp only [Set.mem_setOf_eq]
  obtain ⟨n, hn, hin, hout⟩ := hψ
  exact ⟨n, hGG' hn, hin, hout⟩

/-- out1 is monotonic in the input -/
theorem out1_mono_input (G : NormativeCode) (A A' : Set PropFormula)
    (hAA' : A ⊆ A') : out1 G A ⊆ out1 G A' := by
  intro φ hφ
  unfold out1 at hφ ⊢
  unfold Cn at hφ ⊢
  unfold triggeredOutputs at hφ ⊢
  simp only [Set.mem_setOf_eq] at hφ ⊢
  intro v hv
  apply hφ
  intro ψ hψ
  simp only [Set.mem_setOf_eq] at hψ
  obtain ⟨n, hn, hin, hout⟩ := hψ
  apply hv
  simp only [Set.mem_setOf_eq]
  refine ⟨n, hn, ?_, hout⟩
  -- Need to show n.input ∈ Cn A', i.e., LogicalConsequence A' n.input
  -- We have hin : n.input ∈ Cn A, i.e., LogicalConsequence A n.input
  show LogicalConsequence A' n.input
  intro v' hv'
  have hin' : LogicalConsequence A n.input := hin
  apply hin'
  intro ψ' hψ'
  apply hv'
  exact hAA' hψ'

/-! ## Examples -/

/-- Example norm: "If it rains, take an umbrella" -/
def exampleNorm1 : Norm := {
  input := .var "rain"
  output := .var "umbrella"
}

/-- Example norm: "If sunny, wear sunscreen" -/
def exampleNorm2 : Norm := {
  input := .var "sunny"
  output := .var "sunscreen"
}

/-- Example normative code -/
def exampleCode : NormativeCode := {exampleNorm1, exampleNorm2}

#check exampleCode

end Mettapedia.AutoBooks.ClaudeProcWam.Governance
