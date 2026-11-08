import Mathlib.Data.List.Dedup
import Mathlib.Logic.Function.Basic

/-!
# A compact CNF: the constraint language of the Boolean kernel

The Boolean kernel shared by the SAT, answer set and counting disciplines works
on clauses, not on rules. This module fixes that representation, separate from
the answer set syntax: a literal is a variable of an arbitrary type `V` with the
truth value it asserts (`Literal`), a clause is a list of literals read as their
disjunction (`Clause`), and a formula is a list of clauses read as their
conjunction (`Formula`). Everything is first-order data: lists of pairs.

## Contents

* **Satisfaction.** A total assignment is a function `V → Bool`; literals,
  clauses and formulas evaluate to `Bool` (`Literal.eval`, `Clause.eval`,
  `Formula.eval`). Consequence (`Formula.Entails`) and unsatisfiability
  (`Formula.Unsat`) are the usual semantic notions. Evaluation depends only on
  the variables that occur (`Formula.eval_congr`).
* **Monotonicity of adding clauses.** The models of `F ++ G` are the models of
  `F` that satisfy `G` (`Formula.eval_append`); consequence and
  unsatisfiability survive added clauses (`Formula.Entails.append`,
  `Formula.Unsat.append`, `Formula.Unsat.of_subset`).
* **Unit propagation.** A partial assignment is a list of literals assigned
  true. A clause is unit when one literal is not falsified by the assignment,
  and conflicting when none is (`Clause.openLits`). One propagation pass over the
  clauses (`Formula.propagatePass`) and `n` passes (`Formula.unitPropagate`)
  are sound: every model of the formula that agrees with the initial assignment
  agrees with the propagated one (`Formula.unitPropagate_sound`), and a reported
  conflict means that no model agrees with the initial assignment
  (`Formula.unitPropagate_conflict`).
* **Renaming.** Variables can be renamed along any map (`Formula.rename`); a
  renamed formula is evaluated by composing the assignment
  (`Formula.eval_rename`), and along an injective map unsatisfiability is
  preserved and reflected (`Formula.unsat_rename_iff`). This is how a formula
  over solver variables becomes a formula over variable numbers.
* **Conditioning.** `Formula.condition x b` is `F[x := b]`: clauses satisfied by
  the assignment are dropped and the variable is removed from the others. It is
  evaluated by updating the assignment (`Formula.eval_condition`) and no longer
  mentions `x` (`Formula.varsIn_condition`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.CNF

universe u v

/-- A literal: a variable and the truth value it asserts. -/
structure Literal (V : Type u) where
  var : V
  sign : Bool
  deriving DecidableEq, Repr

/-- A clause: the disjunction of its literals. -/
abbrev Clause (V : Type u) := List (Literal V)

/-- A formula in conjunctive normal form: the conjunction of its clauses. -/
abbrev Formula (V : Type u) := List (Clause V)

variable {V : Type u} {W : Type v}

/-! ## Satisfaction -/

namespace Literal

/-- The complementary literal. -/
def neg (l : Literal V) : Literal V := ⟨l.var, !l.sign⟩

@[simp] theorem neg_neg (l : Literal V) : l.neg.neg = l := by
  simp [neg]

@[simp] theorem neg_var (l : Literal V) : l.neg.var = l.var := rfl

theorem neg_ne (l : Literal V) : l.neg ≠ l := by
  intro h
  have := congrArg Literal.sign h
  cases hs : l.sign <;> simp [neg, hs] at this

/-- The value of a literal under a total assignment. -/
def eval (σ : V → Bool) (l : Literal V) : Bool := σ l.var == l.sign

theorem eval_eq_true {σ : V → Bool} {l : Literal V} : l.eval σ = true ↔ σ l.var = l.sign := by
  simp [eval]

@[simp] theorem eval_neg (σ : V → Bool) (l : Literal V) : l.neg.eval σ = !l.eval σ := by
  unfold eval neg
  cases σ l.var <;> cases l.sign <;> rfl

/-- Rename the variable of a literal. -/
def rename (f : V → W) (l : Literal V) : Literal W := ⟨f l.var, l.sign⟩

@[simp] theorem eval_rename (f : V → W) (σ : W → Bool) (l : Literal V) :
    (l.rename f).eval σ = l.eval (σ ∘ f) := rfl

end Literal

namespace Clause

/-- The value of a clause: some literal is true. -/
def eval (σ : V → Bool) (c : Clause V) : Bool := c.any (Literal.eval σ)

theorem eval_eq_true {σ : V → Bool} {c : Clause V} : c.eval σ = true ↔ ∃ l ∈ c, l.eval σ = true := by
  simp [eval]

theorem eval_eq_false {σ : V → Bool} {c : Clause V} : c.eval σ = false ↔ ∀ l ∈ c, l.eval σ = false := by
  simp [eval]

@[simp] theorem eval_nil (σ : V → Bool) : Clause.eval σ ([] : Clause V) = false := rfl

/-- Rename the variables of a clause. -/
def rename (f : V → W) (c : Clause V) : Clause W := c.map (Literal.rename f)

@[simp] theorem eval_rename (f : V → W) (σ : W → Bool) (c : Clause V) :
    (c.rename f).eval σ = c.eval (σ ∘ f) := by
  simp [rename, eval, List.any_map, Function.comp_def]

theorem eval_congr {σ τ : V → Bool} {c : Clause V} (same : ∀ l ∈ c, σ l.var = τ l.var) :
    c.eval σ = c.eval τ := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval_eq_true, Literal.eval_eq_true]
  exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, by rw [← same l hl]; exact h⟩,
    fun ⟨l, hl, h⟩ => ⟨l, hl, by rw [same l hl]; exact h⟩⟩

end Clause

namespace Formula

/-- The value of a formula: every clause is true. -/
def eval (σ : V → Bool) (F : Formula V) : Bool := F.all (Clause.eval σ)

theorem eval_eq_true {σ : V → Bool} {F : Formula V} : F.eval σ = true ↔ ∀ c ∈ F, c.eval σ = true := by
  simp [eval]

@[simp] theorem eval_nil (σ : V → Bool) : Formula.eval σ ([] : Formula V) = true := rfl

@[simp] theorem eval_cons (σ : V → Bool) (c : Clause V) (F : Formula V) :
    Formula.eval σ (c :: F) = (c.eval σ && F.eval σ) := rfl

/-- **Adding clauses**: the models of `F ++ G` are the models of `F` that satisfy `G`. -/
@[simp] theorem eval_append (σ : V → Bool) (F G : Formula V) :
    Formula.eval σ (F ++ G) = (F.eval σ && G.eval σ) := by
  simp [eval, List.all_append]

/-- The variables of `F` lie in `S`. -/
def VarsIn (F : Formula V) (S : Set V) : Prop := ∀ c ∈ F, ∀ l ∈ c, l.var ∈ S

theorem eval_congr {σ τ : V → Bool} {F : Formula V} (same : ∀ c ∈ F, ∀ l ∈ c, σ l.var = τ l.var) :
    F.eval σ = F.eval τ := by
  apply Bool.eq_iff_iff.mpr
  simp only [eval_eq_true]
  exact ⟨fun h c hc => by rw [← Clause.eval_congr (same c hc)]; exact h c hc,
    fun h c hc => by rw [Clause.eval_congr (same c hc)]; exact h c hc⟩

/-- `F` entails the clause `c`: every model of `F` satisfies `c`. -/
def Entails (F : Formula V) (c : Clause V) : Prop := ∀ σ, F.eval σ = true → c.eval σ = true

/-- `F` has no model. -/
def Unsat (F : Formula V) : Prop := ∀ σ, F.eval σ = false

theorem unsat_iff_entails_nil (F : Formula V) : F.Unsat ↔ F.Entails [] := by
  constructor
  · intro h σ sat
    rw [h σ] at sat
    cases sat
  · intro h σ
    cases sat : F.eval σ with
    | false => rfl
    | true => exact absurd (h σ sat) (by simp)

theorem Entails.append {F : Formula V} {c : Clause V} (h : F.Entails c) (G : Formula V) :
    (F ++ G).Entails c := fun σ sat => h σ (by simp only [eval_append, Bool.and_eq_true] at sat; exact sat.1)

theorem Entails.append_left {G : Formula V} {c : Clause V} (h : G.Entails c) (F : Formula V) :
    (F ++ G).Entails c := fun σ sat => h σ (by simp only [eval_append, Bool.and_eq_true] at sat; exact sat.2)

theorem Unsat.append {F : Formula V} (h : F.Unsat) (G : Formula V) : (F ++ G).Unsat := fun σ => by
  simp [h σ]

theorem entails_of_mem {F : Formula V} {c : Clause V} (h : c ∈ F) : F.Entails c :=
  fun _ sat => eval_eq_true.mp sat c h

/-- A formula containing every clause of an unsatisfiable formula is unsatisfiable: a refutation
of some of the clauses refutes them all. -/
theorem Unsat.of_subset {G F : Formula V} (h : G.Unsat) (sub : ∀ c ∈ G, c ∈ F) : F.Unsat := by
  intro σ
  cases sat : F.eval σ with
  | false => rfl
  | true =>
    have := h σ
    rw [show G.eval σ = true from eval_eq_true.mpr fun c hc => eval_eq_true.mp sat c (sub c hc)] at this
    cases this

/-! ## Renaming -/

/-- Rename the variables of a formula. -/
def rename (f : V → W) (F : Formula V) : Formula W := F.map (Clause.rename f)

@[simp] theorem eval_rename (f : V → W) (σ : W → Bool) (F : Formula V) :
    (F.rename f).eval σ = F.eval (σ ∘ f) := by
  simp [rename, eval, List.all_map, Function.comp_def]

/-- Along an injective renaming, a formula is unsatisfiable exactly when its image is. -/
theorem unsat_rename_iff {f : V → W} (injective : Function.Injective f) (F : Formula V) :
    (F.rename f).Unsat ↔ F.Unsat := by
  constructor
  · intro h τ
    have := h (Function.extend f τ fun _ => false)
    rwa [eval_rename, show (Function.extend f τ fun _ => false) ∘ f = τ from
      funext fun x => injective.extend_apply τ _ x] at this
  · intro h σ
    rw [eval_rename]
    exact h _

end Formula

/-! ## Unit propagation -/

/-- A total assignment agrees with a partial one, given as the list of its true literals. -/
def Agrees (σ : V → Bool) (α : List (Literal V)) : Prop := ∀ l ∈ α, l.eval σ = true

section Propagation

variable [DecidableEq V]

namespace Clause

/-- The literals of `c` that the partial assignment `α` does not falsify. -/
def openLits (α : List (Literal V)) (c : Clause V) : Clause V := c.filter fun l => decide (l.neg ∉ α)

/-- A true clause has a true literal that the agreeing partial assignment does not falsify. -/
theorem exists_open {σ : V → Bool} {α : List (Literal V)} {c : Clause V} (agrees : Agrees σ α)
    (sat : c.eval σ = true) : ∃ l ∈ c.openLits α, l.eval σ = true := by
  obtain ⟨l, hl, true_l⟩ := eval_eq_true.mp sat
  refine ⟨l, List.mem_filter.mpr ⟨hl, ?_⟩, true_l⟩
  simp only [decide_eq_true_eq]
  intro falsified
  have := agrees _ falsified
  simp [true_l] at this

/-- **A conflicting clause** (no open literal) is false under every agreeing assignment. -/
theorem conflict_sound {σ : V → Bool} {α : List (Literal V)} {c : Clause V} (agrees : Agrees σ α)
    (conflict : c.openLits α = []) : c.eval σ = false := by
  cases sat : c.eval σ with
  | false => rfl
  | true =>
    obtain ⟨l, hl, _⟩ := exists_open agrees sat
    rw [conflict] at hl
    cases hl

/-- **A unit clause** forces its open literal under every agreeing model. -/
theorem unit_sound {σ : V → Bool} {α : List (Literal V)} {c : Clause V} {l : Literal V}
    (agrees : Agrees σ α) (unit : c.openLits α = [l]) (sat : c.eval σ = true) : l.eval σ = true := by
  obtain ⟨m, hm, true_m⟩ := exists_open agrees sat
  rw [unit, List.mem_singleton] at hm
  exact hm ▸ true_m

/-- Propagate one clause: `none` on a conflict, the unit literal added when it is unit. -/
def propagate (α : List (Literal V)) (c : Clause V) : Option (List (Literal V)) :=
  match c.openLits α with
  | [] => none
  | [l] => some (l :: α)
  | _ :: _ :: _ => some α

theorem propagate_sound {σ : V → Bool} {α β : List (Literal V)} {c : Clause V} (agrees : Agrees σ α)
    (sat : c.eval σ = true) (h : c.propagate α = some β) : Agrees σ β := by
  unfold propagate at h
  split at h
  · cases h
  · rename_i l unit
    cases h
    rintro m (_ | ⟨_, hm⟩)
    · exact unit_sound agrees unit sat
    · exact agrees m hm
  · cases h
    exact agrees

theorem propagate_conflict {σ : V → Bool} {α : List (Literal V)} {c : Clause V} (agrees : Agrees σ α)
    (sat : c.eval σ = true) : c.propagate α ≠ none := by
  unfold propagate
  split
  · rename_i conflict
    rw [conflict_sound agrees conflict] at sat
    cases sat
  · simp
  · simp

end Clause

namespace Formula

/-- One unit-propagation pass over the clauses, in order. -/
def propagatePass : Formula V → List (Literal V) → Option (List (Literal V))
  | [], α => some α
  | c :: F, α => (c.propagate α).bind (propagatePass F)

/-- `n` unit-propagation passes. -/
def unitPropagate (F : Formula V) : ℕ → List (Literal V) → Option (List (Literal V))
  | 0, α => some α
  | n + 1, α => (F.propagatePass α).bind (F.unitPropagate n)

theorem propagatePass_sound {σ : V → Bool} :
    ∀ (F : Formula V) {α β : List (Literal V)}, F.eval σ = true → Agrees σ α →
      F.propagatePass α = some β → Agrees σ β
  | [], _, _, _, agrees, h => by cases h; exact agrees
  | c :: F, α, β, sat, agrees, h => by
    simp only [eval_cons, Bool.and_eq_true] at sat
    simp only [propagatePass, Option.bind_eq_some_iff] at h
    obtain ⟨γ, hγ, rest⟩ := h
    exact propagatePass_sound F sat.2 (Clause.propagate_sound agrees sat.1 hγ) rest

theorem propagatePass_conflict {σ : V → Bool} :
    ∀ (F : Formula V) {α : List (Literal V)}, F.eval σ = true → Agrees σ α → F.propagatePass α ≠ none
  | [], _, _, _ => by simp [propagatePass]
  | c :: F, α, sat, agrees => by
    simp only [eval_cons, Bool.and_eq_true] at sat
    simp only [propagatePass]
    cases hc : c.propagate α with
    | none => exact absurd hc (Clause.propagate_conflict agrees sat.1)
    | some γ => exact propagatePass_conflict F sat.2 (Clause.propagate_sound agrees sat.1 hc)

/-- **Unit propagation is sound**: a model of `F` that agrees with the initial assignment agrees
with every propagated literal. -/
theorem unitPropagate_sound {σ : V → Bool} {F : Formula V} (sat : F.eval σ = true) :
    ∀ (n : ℕ) {α β : List (Literal V)}, Agrees σ α → F.unitPropagate n α = some β → Agrees σ β
  | 0, _, _, agrees, h => by cases h; exact agrees
  | n + 1, α, β, agrees, h => by
    simp only [unitPropagate, Option.bind_eq_some_iff] at h
    obtain ⟨γ, hγ, rest⟩ := h
    exact unitPropagate_sound sat n (propagatePass_sound F sat agrees hγ) rest

/-- **A propagation conflict refutes the assignment**: no model of `F` agrees with it. -/
theorem unitPropagate_conflict {F : Formula V} {n : ℕ} {α : List (Literal V)}
    (conflict : F.unitPropagate n α = none) (σ : V → Bool) (agrees : Agrees σ α) : F.eval σ = false := by
  cases sat : F.eval σ with
  | false => rfl
  | true =>
    exfalso
    induction n generalizing α with
    | zero => cases conflict
    | succ n ih =>
      simp only [unitPropagate] at conflict
      cases hp : F.propagatePass α with
      | none => exact propagatePass_conflict F sat agrees hp
      | some γ =>
        rw [hp, Option.bind_some] at conflict
        exact ih conflict (propagatePass_sound F sat agrees hp)

/-- A literal unit propagation derives from the empty assignment is entailed. -/
theorem entails_of_unitPropagate {F : Formula V} {n : ℕ} {β : List (Literal V)}
    (h : F.unitPropagate n [] = some β) {l : Literal V} (hl : l ∈ β) : F.Entails [l] := by
  intro σ sat
  have := unitPropagate_sound sat n (fun _ h => absurd h List.not_mem_nil) h l hl
  simp [Clause.eval, this]

/-- A propagation conflict from the empty assignment refutes `F`. -/
theorem unsat_of_unitPropagate {F : Formula V} {n : ℕ} (h : F.unitPropagate n [] = none) : F.Unsat :=
  fun σ => unitPropagate_conflict h σ fun _ h => absurd h List.not_mem_nil

end Formula

end Propagation

/-! ## Conditioning -/

section Conditioning

variable [DecidableEq V]

namespace Formula

/-- `F[x := b]`: drop the clauses the assignment satisfies, and remove `x` from the rest. -/
def condition (x : V) (b : Bool) (F : Formula V) : Formula V :=
  (F.filter fun c => decide (⟨x, b⟩ ∉ c)).map fun c => c.filter fun l => decide (l.var ≠ x)

theorem clause_eval_update (σ : V → Bool) (x : V) (b : Bool) (c : Clause V) :
    c.eval (Function.update σ x b) =
      (decide ((⟨x, b⟩ : Literal V) ∈ c) || Clause.eval σ (c.filter fun l => decide (l.var ≠ x))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Clause.eval_eq_true, Literal.eval_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.mem_filter]
  constructor
  · rintro ⟨⟨y, s⟩, hl, value⟩
    by_cases hy : y = x
    · subst hy
      simp only [Function.update_self] at value
      subst value
      exact Or.inl hl
    · exact Or.inr ⟨⟨y, s⟩, ⟨hl, hy⟩, by simpa [Function.update_of_ne hy] using value⟩
  · rintro (hl | ⟨l, ⟨hl, hx⟩, value⟩)
    · exact ⟨_, hl, by simp⟩
    · exact ⟨l, hl, by rw [Function.update_of_ne hx]; exact value⟩

theorem condition_cons (x : V) (b : Bool) (c : Clause V) (F : Formula V) :
    condition x b (c :: F) = if (⟨x, b⟩ : Literal V) ∈ c then condition x b F
      else (c.filter fun l => decide (l.var ≠ x)) :: condition x b F := by
  unfold condition
  by_cases hc : (⟨x, b⟩ : Literal V) ∈ c
  · rw [List.filter_cons_of_neg (by simpa using hc), if_pos hc]
  · rw [List.filter_cons_of_pos (by simpa using hc), if_neg hc, List.map_cons]

/-- **Conditioning is evaluation under the updated assignment.** -/
theorem eval_condition (σ : V → Bool) (x : V) (b : Bool) (F : Formula V) :
    (F.condition x b).eval σ = F.eval (Function.update σ x b) := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    rw [condition_cons, eval_cons, clause_eval_update]
    by_cases hc : (⟨x, b⟩ : Literal V) ∈ c
    · rw [if_pos hc, ih]
      simp [hc]
    · rw [if_neg hc, eval_cons, ih]
      simp [hc]

/-- `F[x := b]` no longer mentions `x`. -/
theorem varsIn_condition {F : Formula V} {S : Set V} (h : F.VarsIn S) (x : V) (b : Bool) :
    (F.condition x b).VarsIn (S \ {x}) := by
  intro c hc l hl
  simp only [condition, List.mem_map, List.mem_filter, decide_eq_true_eq] at hc
  obtain ⟨c', ⟨hc', _⟩, rfl⟩ := hc
  simp only [List.mem_filter, decide_eq_true_eq] at hl
  exact ⟨h c' hc' l hl.1, hl.2⟩

/-- Conditioning on a variable that does not occur changes no value. -/
theorem eval_condition_of_not_mem {F : Formula V} {S : Set V} (h : F.VarsIn S) {x : V} (hx : x ∉ S)
    (b : Bool) (σ : V → Bool) : (F.condition x b).eval σ = F.eval σ := by
  rw [eval_condition]
  refine eval_congr fun c hc l hl => ?_
  have : l.var ≠ x := fun same => hx (same ▸ h c hc l hl)
  simp [Function.update_of_ne this]

end Formula

end Conditioning

end Mettapedia.Logic.ASP.CNF
