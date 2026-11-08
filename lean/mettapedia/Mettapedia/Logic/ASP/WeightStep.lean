import Mettapedia.Logic.ASP.WeightDefs
import Mettapedia.GSLT.Logic.PropositionalFormula

/-!
# Weight steps: clauses a weight definition implies

The C solver propagates a weight definition `W ↔ L ≤ {l₁ = w₁, …}` by sums, and explains each
consequence by a clause the definition implies: a **weight step** of its certificates. The step
gives a clause and a definition; the checker accepts it by arithmetic, without unit propagation.

The check (`weightCheck`, a transcription of `weight_step_ok` in `asp_cdnl_v1.c`), over native
literals and a numbering `idx` of the atoms, with `n` variables:

* the clause is scanned in order (`tautScan`): a literal past the `n` variables refuses it; a
  literal whose complement came before it accepts it, the clause holding always;
* otherwise the clause must hold the definition's atom `W`. Each literal of the definition whose
  variable occurs in the clause has the value the first literal over that variable denies
  (`falsifiedValue`): it is forced to contribute, or forced not to. Two literals of the definition
  over one atom each count, as in the sums the solver keeps.
  - With `W` positive in the clause, the falsifying assignments make `W` false, so the forced
    contributions must reach the bound: `L ≤ forcedIn`.
  - With `not W` in it, they make `W` true, so the total less the forced non-contributions must
    stay below the bound: `total - forcedOut < L`.

**Soundness** (`weightCheck_sound`): an accepted clause holds in every assignment of the variables
that satisfies the definition, `σ (idx W) ↔ L ≤ numWeight idx σ`. No property of the numbering is
needed: the check reads the definition's literals through `idx` as the assignment does.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Mettapedia.GSLT.Logic PropositionalFormula

universe u

variable {A : Type u}

/-- The variable of a native literal. -/
def litVar : Literal → ℕ
  | .pos n => n
  | .neg n => n

/-- The scan of a weight step's clause, in order: `some false` at the first literal past the `n`
variables, `some true` at the first literal whose complement came before it, else `none`. -/
def tautScan (n : ℕ) : List Literal → Clause → Option Bool
  | _, [] => none
  | seen, x :: rest =>
    if n ≤ litVar x then some false
    else if x.complement ∈ seen then some true
    else tautScan n (x :: seen) rest

/-- The value an assignment falsifying the clause gives the variable `v`, when the clause has a
literal over it: the first such literal is false, so `v` is true exactly when it is negative. -/
def falsifiedValue (clause : Clause) (v : ℕ) : Option Bool :=
  (clause.find? fun x => litVar x == v).map fun
    | .pos _ => false
    | .neg _ => true

section Check

variable (idx : A → ℕ)

/-- What a literal of a definition contributes for certain under the assignments falsifying the
clause: its weight when it is forced to contribute. -/
def forcedInTerm (clause : Clause) (t : WTerm A) : ℕ :=
  match falsifiedValue clause (idx t.lit.atom) with
  | some b => if b = t.lit.isPos then t.weight else 0
  | none => 0

/-- What a literal of a definition withholds for certain: its weight when it is forced not to
contribute. -/
def forcedOutTerm (clause : Clause) (t : WTerm A) : ℕ :=
  match falsifiedValue clause (idx t.lit.atom) with
  | some b => if b = t.lit.isPos then 0 else t.weight
  | none => 0

/-- The weight of the literals every assignment falsifying the clause makes true. -/
def forcedIn (clause : Clause) (ts : List (WTerm A)) : ℕ := (ts.map (forcedInTerm idx clause)).sum

/-- The weight of the literals every assignment falsifying the clause makes false. -/
def forcedOut (clause : Clause) (ts : List (WTerm A)) : ℕ := (ts.map (forcedOutTerm idx clause)).sum

/-- What a literal contributes under an assignment of the numbered variables. -/
def numValue (σ : ℕ → Bool) (t : WTerm A) : ℕ := if σ (idx t.lit.atom) = t.lit.isPos then t.weight else 0

/-- The weight of the true literals under an assignment of the numbered variables. -/
def numWeight (σ : ℕ → Bool) (ts : List (WTerm A)) : ℕ := (ts.map (numValue idx σ)).sum

/-- **The weight step check** (`weight_step_ok`): over `n` variables, the clause holds both a variable
and its negation, or it holds the definition's atom and the forced literals decide the definition
against every assignment falsifying it. -/
def weightCheck (n : ℕ) (d : WeightDef A) (clause : Clause) : Bool :=
  match tautScan n [] clause with
  | some b => b
  | none =>
    if Literal.pos (idx d.atom) ∈ clause then decide (d.bound ≤ forcedIn idx clause d.terms)
    else if Literal.neg (idx d.atom) ∈ clause then decide (d.total - forcedOut idx clause d.terms < d.bound)
    else false

end Check

/-! ## Soundness -/

theorem tautScan_true : ∀ {n : ℕ} {seen clause : List Literal}, tautScan n seen clause = some true →
    ∃ x ∈ clause, x.complement ∈ seen ∨ x.complement ∈ clause
  | _, _, [], h => by simp [tautScan] at h
  | n, seen, x :: rest, h => by
    simp only [tautScan] at h
    by_cases range : n ≤ litVar x
    · simp [range] at h
    by_cases comp : x.complement ∈ seen
    · exact ⟨x, List.mem_cons_self, .inl comp⟩
    rw [if_neg range, if_neg comp] at h
    obtain ⟨y, hy, hc⟩ := tautScan_true h
    refine ⟨y, List.mem_cons_of_mem _ hy, ?_⟩
    rcases hc with hc | hc
    · rcases List.mem_cons.mp hc with hc | hc
      · exact .inr (hc ▸ List.mem_cons_self)
      · exact .inl hc
    · exact .inr (List.mem_cons_of_mem _ hc)

theorem sat_complement (σ : ℕ → Bool) (x : Literal) : Literal.sat σ x.complement = !Literal.sat σ x := by
  cases x <;> simp [Literal.complement, Literal.sat]

/-- Under an assignment falsifying the clause, the value of a variable it mentions is the one
`falsifiedValue` reads off. -/
theorem falsifiedValue_eq {σ : ℕ → Bool} {clause : Clause} (falsified : ∀ x ∈ clause, Literal.sat σ x = false)
    {v : ℕ} {b : Bool} (h : falsifiedValue clause v = some b) : σ v = b := by
  unfold falsifiedValue at h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
  have mem := List.mem_of_find?_eq_some hx
  have same := List.find?_some hx
  simp only [beq_iff_eq] at same
  have := falsified x mem
  cases x with
  | pos m =>
    simp only [litVar] at same
    subst same
    simpa [Literal.sat] using this
  | neg m =>
    simp only [litVar] at same
    subst same
    simpa [Literal.sat] using this

section Sound

variable (idx : A → ℕ)

theorem forcedInTerm_le {σ : ℕ → Bool} {clause : Clause} (falsified : ∀ x ∈ clause, Literal.sat σ x = false)
    (t : WTerm A) : forcedInTerm idx clause t ≤ numValue idx σ t := by
  unfold forcedInTerm numValue
  cases hv : falsifiedValue clause (idx t.lit.atom) with
  | none => exact Nat.zero_le _
  | some b => simp only [falsifiedValue_eq falsified hv]; exact le_rfl

theorem numValue_add_forcedOutTerm {σ : ℕ → Bool} {clause : Clause}
    (falsified : ∀ x ∈ clause, Literal.sat σ x = false) (t : WTerm A) :
    numValue idx σ t + forcedOutTerm idx clause t ≤ t.weight := by
  unfold forcedOutTerm numValue
  cases hv : falsifiedValue clause (idx t.lit.atom) with
  | none => simp only; split_ifs <;> omega
  | some b =>
    simp only [falsifiedValue_eq falsified hv]
    split_ifs <;> omega

theorem forcedIn_le {σ : ℕ → Bool} {clause : Clause} (falsified : ∀ x ∈ clause, Literal.sat σ x = false)
    (ts : List (WTerm A)) : forcedIn idx clause ts ≤ numWeight idx σ ts := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih =>
    simp only [forcedIn, numWeight, List.map_cons, List.sum_cons] at ih ⊢
    exact Nat.add_le_add (forcedInTerm_le idx falsified t) ih

theorem numWeight_add_forcedOut {σ : ℕ → Bool} {clause : Clause}
    (falsified : ∀ x ∈ clause, Literal.sat σ x = false) (ts : List (WTerm A)) :
    numWeight idx σ ts + forcedOut idx clause ts ≤ (ts.map WTerm.weight).sum := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih =>
    simp only [forcedOut, numWeight, List.map_cons, List.sum_cons] at ih ⊢
    have := numValue_add_forcedOutTerm idx falsified t
    omega

/-- **A weight step is sound**: an accepted clause holds in every assignment of the numbered
variables that satisfies the definition. -/
theorem weightCheck_sound {n : ℕ} {d : WeightDef A} {clause : Clause} (accepted : weightCheck idx n d clause = true)
    (σ : ℕ → Bool) (satisfies : σ (idx d.atom) = true ↔ d.bound ≤ numWeight idx σ d.terms) :
    Clause.sat σ clause = true := by
  by_contra notSat
  have falsified : ∀ x ∈ clause, Literal.sat σ x = false := by
    intro x hx
    by_contra hsat
    exact notSat (List.any_eq_true.mpr ⟨x, hx, by simpa using hsat⟩)
  unfold weightCheck at accepted
  split at accepted
  · rename_i b hb
    subst accepted
    obtain ⟨x, hx, hc | hc⟩ := tautScan_true hb
    · cases hc
    · have h1 := falsified x hx
      have h2 := falsified _ hc
      rw [sat_complement, h1] at h2
      cases h2
  · split_ifs at accepted with hpos hneg
    · rw [decide_eq_true_eq] at accepted
      have hW : σ (idx d.atom) = false := by simpa [Literal.sat] using falsified _ hpos
      have := satisfies.mpr (accepted.trans (forcedIn_le idx falsified d.terms))
      rw [hW] at this
      cases this
    · rw [decide_eq_true_eq] at accepted
      have hW : σ (idx d.atom) = true := by simpa [Literal.sat] using falsified _ hneg
      have bound := satisfies.mp hW
      have total := numWeight_add_forcedOut idx falsified d.terms
      unfold WeightDef.total at accepted
      omega

end Sound

end Mettapedia.Logic.ASP
