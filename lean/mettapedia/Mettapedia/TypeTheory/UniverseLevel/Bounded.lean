import Mettapedia.TypeTheory.UniverseLevel.Algebra
import Mettapedia.TypeTheory.UniverseLevel.Notation

/-!
# Level comparisons under bounded variables

A level variable is either unbounded or ranges strictly below a closed level, its bound.
Two level expressions are compared at the valuations that respect the bounds. Over a level
order with predecessors this comparison is decided on canonical forms: the left constant
must fit under what the right side exposes at the least valuation, and each left atom
`x + k` must either meet an atom `x + l` with `k ≤ l` on the right, or have a bounded
variable all of whose values, raised by `k`, fit under what the right side exposes without
`x`. The last condition is one comparison: at a successor bound the largest value is the
predecessor of the bound, and at a limit bound the values raised by `k` are cofinal in the
bound. A refused comparison comes with a valuation that respects the bounds and reverses
it. Bounds must be positive: under a bound at the least level no valuation is valid, and
every comparison holds.

The supremum of an expression over the values of a variable below a positive closed bound
is again an expression: the instance at the predecessor of a successor bound, and at a
limit bound the instance at the least level joined with the bound when the variable occurs.
It is the least upper bound at every valuation of the other variables.

Positive examples: over the natural numbers, `x + 1 ≤ 3` holds for `x < 3`, and the
supremum of `x + 1` over `x < 3` is `3`; over the ordinal notations, `x + 1 ≤ ω` holds for
`x < ω`, and the supremum of `x + 1` over `x < ω` is `ω`. Negative examples: `x + 2 ≤ 3`
fails for `x < 3`, at the valuation `x = 2`; `ω + 1 ≤ ω` fails, so `ω` is not a value of a
variable below `ω`; under the bound `x < 0` the false comparison `1 ≤ 0` holds.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

open LevelOrder PredLevelOrder

variable {L : Type}

/-! ## Occurrence and instantiation of a variable -/

namespace LevelExpr

/-- Whether the variable `x` occurs in an expression. -/
def occurs (x : Nat) : LevelExpr L → Bool
  | .const _ => false
  | .param i => decide (i = x)
  | .succ e => occurs x e
  | .max e₁ e₂ => occurs x e₁ || occurs x e₂

/-- The substitution that replaces the variable `x` by an expression and keeps the others. -/
def instantiate (x : Nat) (a : LevelExpr L) : Nat → LevelExpr L :=
  fun i => if i = x then a else .param i

variable [LevelOrder L]

/-- Instantiating a variable by a closed level evaluates as updating the valuation. -/
theorem eval_subst_instantiate (ν : Nat → L) (x : Nat) (c : L) (e : LevelExpr L) :
    eval ν (e.subst (instantiate x (.const c))) = eval (Function.update ν x c) e := by
  rw [eval_subst]
  congr 1
  funext i
  by_cases h : i = x
  · subst h
    simp [instantiate, eval]
  · simp [instantiate, h, eval]

/-- The value of an expression does not depend on a variable that does not occur in it. -/
theorem eval_update_of_not_occurs {x : Nat} (ν : Nat → L) (a : L) :
    ∀ {e : LevelExpr L}, occurs x e = false → eval (Function.update ν x a) e = eval ν e
  | .const _, _ => rfl
  | .param i, h => by
    have hne : i ≠ x := by simpa [occurs] using h
    simp [eval, Function.update_of_ne hne]
  | .succ e, h => by
    simp only [eval]
    rw [eval_update_of_not_occurs ν a (e := e) h]
  | .max e₁ e₂, h => by
    have h' : occurs x e₁ = false ∧ occurs x e₂ = false := by simpa [occurs] using h
    simp only [eval]
    rw [eval_update_of_not_occurs ν a h'.1, eval_update_of_not_occurs ν a h'.2]

/-- An expression lies above the value of a variable that occurs in it. -/
theorem le_eval_of_occurs {x : Nat} (ν : Nat → L) :
    ∀ {e : LevelExpr L}, occurs x e = true → ν x ≤ eval ν e
  | .const _, h => by simp [occurs] at h
  | .param i, h => by
    have hix : i = x := by simpa [occurs] using h
    subst hix
    exact le_refl _
  | .succ e, h => le_trans (le_eval_of_occurs ν (e := e) h) (le_succ _)
  | .max e₁ e₂, h => by
    have h' : occurs x e₁ = true ∨ occurs x e₂ = true := by simpa [occurs] using h
    rcases h' with h₁ | h₂
    · exact le_trans (le_eval_of_occurs ν h₁) (le_max_left _ _)
    · exact le_trans (le_eval_of_occurs ν h₂) (le_max_right _ _)

/-- Below a limit, the value of an expression at a value of `x` either does not exceed its
value at the least level, or stays below the limit. -/
theorem eval_update_le_or_lt {x : Nat} (ν : Nat → L) {c a : L} (limit : IsLimit c)
    (ha : a < c) :
    ∀ e : LevelExpr L,
      eval (Function.update ν x a) e ≤ eval (Function.update ν x bot) e ∨
        eval (Function.update ν x a) e < c
  | .const _ => .inl (le_refl _)
  | .param i => by
    by_cases h : i = x
    · subst h
      exact .inr (by simpa [eval] using ha)
    · exact .inl (by simp [eval, Function.update_of_ne h])
  | .succ e => by
    rcases eval_update_le_or_lt ν limit ha e with h | h
    · exact .inl (succ_le_succ h)
    · exact .inr (limit.succ_lt h)
  | .max e₁ e₂ => by
    rcases eval_update_le_or_lt ν limit ha e₁ with h₁ | h₁
    · rcases eval_update_le_or_lt ν limit ha e₂ with h₂ | h₂
      · exact .inl (max_le_max h₁ h₂)
      · rcases le_total (eval (Function.update ν x a) e₁) (eval (Function.update ν x a) e₂)
          with h | h
        · exact .inr (by simp only [eval]; rw [max_eq_right h]; exact h₂)
        · exact .inl (by
            simp only [eval]
            rw [max_eq_left h]
            exact le_trans h₁ (le_max_left _ _))
    · rcases eval_update_le_or_lt ν limit ha e₂ with h₂ | h₂
      · rcases le_total (eval (Function.update ν x a) e₁) (eval (Function.update ν x a) e₂)
          with h | h
        · exact .inl (by
            simp only [eval]
            rw [max_eq_right h]
            exact le_trans h₂ (le_max_right _ _))
        · exact .inr (by simp only [eval]; rw [max_eq_left h]; exact h₁)
      · exact .inr (max_lt h₁ h₂)

end LevelExpr

/-! ## Canonical forms at a single-variable valuation -/

namespace LevelNF

/-- The offsets supremum is the least bound of the offsets. -/
theorem supOffsets_le_iff {ps : List (Nat × Nat)} {B : Nat} :
    supOffsets ps ≤ B ↔ ∀ x ∈ ps, x.2 ≤ B := by
  induction ps with
  | nil => exact ⟨fun _ _ hx => absurd hx List.not_mem_nil, fun _ => Nat.zero_le B⟩
  | cons b rest ih =>
    obtain ⟨j, l⟩ := b
    rw [supOffsets_cons]
    constructor
    · intro h x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact Nat.le_trans (Nat.le_max_right _ _) h
      · exact ih.mp (Nat.le_trans (Nat.le_max_left _ _) h) x hmem
    · intro h
      exact Nat.max_le.mpr ⟨ih.mpr fun x hx => h x (List.Mem.tail _ hx),
        h (j, l) (List.Mem.head rest)⟩

/-- A sublist of atoms has a smaller offsets supremum. -/
theorem supOffsets_filter_le (p : Nat × Nat → Bool) (ps : List (Nat × Nat)) :
    supOffsets (ps.filter p) ≤ supOffsets ps :=
  supOffsets_le_iff.mpr fun x hx =>
    supOffsets_le_iff.mp (Nat.le_refl _) x (List.mem_filter.mp hx).1

/-- A decidable property that fails to hold on a whole list fails at one of its members. -/
theorem exists_mem_not_of_not_forall {α : Type} {p : α → Prop} [DecidablePred p] :
    ∀ {l : List α}, (¬ ∀ x ∈ l, p x) → ∃ x ∈ l, ¬ p x
  | [], h => absurd (fun _ hx => absurd hx List.not_mem_nil) h
  | a :: rest, h =>
    if ha : p a then
      let ⟨x, hx, hpx⟩ := exists_mem_not_of_not_forall (l := rest) fun hr => h fun y hy => by
        rcases List.mem_cons.mp hy with rfl | hmem
        · exact ha
        · exact hr y hmem
      ⟨x, List.Mem.tail a hx, hpx⟩
    else ⟨a, List.Mem.head rest, ha⟩

variable [LevelOrder L]

/-- What a canonical form exposes without the variable `i`: its constant, and the finite
levels of the offsets of the other variables. It is the value of the form when `i` is
removed and the other variables are at the least level. -/
def floorWithout (nf : LevelNF L) (i : Nat) : L :=
  max nf.constPart (ofNat (supOffsets (nf.params.filter fun jk => decide (jk.1 ≠ i))))

/-- A canonical form lies above what it exposes without a variable, at every valuation. -/
theorem floorWithout_le_eval (ν : Nat → L) (nf : LevelNF L) (i : Nat) :
    floorWithout nf i ≤ eval ν nf := by
  obtain ⟨c, ps⟩ := nf
  refine max_le (const_le_eval ν c ps) ?_
  refine le_trans (ofNat_le_ofNat_iff.mpr (supOffsets_filter_le _ ps)) ?_
  rw [eval_constPart]
  exact le_trans (eval_ge_sup ν ps) (le_max_right _ _)

/-- What a canonical form exposes without a variable lies below what it exposes at the
least valuation. -/
theorem floorWithout_le (nf : LevelNF L) (i : Nat) :
    floorWithout nf i ≤ max nf.constPart (ofNat (supOffsets nf.params)) :=
  max_le_max (le_refl _) (ofNat_le_ofNat_iff.mpr (supOffsets_filter_le _ nf.params))

/-- At a valuation with one variable above the least level, a canonical form with sorted
atoms lies below what it exposes without the variable, joined with the variable's atom. -/
theorem eval_single_le {c : L} {ps : List (Nat × Nat)} (hs : Sorted ps) (i : Nat) (a : L) :
    eval (fun j => if j = i then a else bot) ⟨c, ps⟩ ≤
      max (floorWithout ⟨c, ps⟩ i)
        (match lookupParam ps i with
          | some l => addNat a l
          | none => bot) := by
  refine eval_le_of_bounds _ ?_ c (le_trans (le_max_left _ _) (le_max_left _ _))
  intro x hx
  obtain ⟨j, l⟩ := x
  show addNat (if j = i then a else bot) l ≤ _
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, lookupParam_eq_some_of_mem hs hx]
    exact le_max_right _ _
  · rw [if_neg hji]
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ (le_max_right _ _)
    refine ofNat_le_ofNat_iff.mpr (supOffsets_ge_of_mem (j := j) ?_)
    exact List.mem_filter.mpr ⟨hx, by simpa using hji⟩

/-- **Separation at one variable.** If a left atom `(i, k)` meets no right atom of the same
variable with at least its offset, then every value `a` of `i` whose offset by `k` exceeds
what the right side exposes without `i` separates the two forms. -/
theorem single_separates {left right : LevelNF L} (hRight : WF right) {i k : Nat}
    (hLookup : lookupParam left.params i = some k) (hAtom : ¬ AtomLe right.params (i, k))
    {a : L} (ha : floorWithout right i < addNat a k) :
    eval (fun j => if j = i then a else bot) right <
      eval (fun j => if j = i then a else bot) left := by
  obtain ⟨c₁, p₁⟩ := left
  obtain ⟨c₂, p₂⟩ := right
  have hLeft : addNat a k ≤ eval (fun j => if j = i then a else bot) ⟨c₁, p₁⟩ := by
    have h := atom_le_eval (fun j => if j = i then a else bot) hLookup c₁
    rwa [if_pos rfl] at h
  refine lt_of_le_of_lt (eval_single_le hRight.1 i a) (lt_of_lt_of_le ?_ hLeft)
  refine max_lt ha ?_
  cases hR : lookupParam p₂ i with
  | none => exact lt_of_le_of_lt (bot_le _) ha
  | some l =>
    have hl : l < k := by
      unfold AtomLe at hAtom
      rw [show lookupParam (LevelNF.mk c₂ p₂).params (i, k).1 = some l from hR] at hAtom
      exact Nat.lt_of_not_ge hAtom
    exact addNat_lt_addNat_right a hl

end LevelNF

/-! ## Bounds of level variables -/

/-- Bounds of level variables: a variable is unbounded, or ranges strictly below a closed
level. -/
abbrev LevelBounds (L : Type) := Nat → Option L

namespace LevelBounds

section Order

variable [LevelOrder L]

/-- A valuation respects the bounds. -/
def Valid (Δ : LevelBounds L) (ν : Nat → L) : Prop :=
  ∀ (i : Nat) (c : L), Δ i = some c → ν i < c

/-- Every bound is positive. -/
def Positive (Δ : LevelBounds L) : Prop :=
  ∀ (i : Nat) (c : L), Δ i = some c → bot < c

/-- No variable is bounded. -/
def unbounded (L : Type) : LevelBounds L := fun _ => none

/-- Every valuation respects the absence of bounds. -/
theorem valid_unbounded (ν : Nat → L) : Valid (unbounded L) ν := fun _ _ h => nomatch h

/-- The absence of bounds is positive. -/
theorem positive_unbounded : Positive (unbounded L) := fun _ _ h => nomatch h

/-- Under positive bounds the least valuation is valid. -/
theorem Positive.valid_bot {Δ : LevelBounds L} (pos : Δ.Positive) : Δ.Valid fun _ => bot :=
  fun i c h => pos i c h

/-- Under positive bounds, a valuation that raises one variable to a value its bound allows
is valid. -/
theorem Positive.valid_single {Δ : LevelBounds L} (pos : Δ.Positive) {i : Nat} {a : L}
    (ha : ∀ c, Δ i = some c → a < c) : Δ.Valid fun j => if j = i then a else bot := by
  intro j c h
  show (if j = i then a else bot) < c
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    exact ha c h
  · rw [if_neg hji]
    exact pos j c h

/-- A valid valuation stays valid when one variable takes another value its bound allows. -/
theorem Valid.update {Δ : LevelBounds L} {ν : Nat → L} (valid : Δ.Valid ν) {x : Nat} {a : L}
    (ha : ∀ c, Δ x = some c → a < c) : Δ.Valid (Function.update ν x a) := by
  intro j c h
  by_cases hjx : j = x
  · subst hjx
    rw [Function.update_self]
    exact ha c h
  · rw [Function.update_of_ne hjx]
    exact valid j c h

/-- The order of two level expressions under the bounds: at every valuation that respects
them. -/
def LeUnder (Δ : LevelBounds L) (e₁ e₂ : LevelExpr L) : Prop :=
  ∀ ν : Nat → L, Δ.Valid ν → LevelExpr.eval ν e₁ ≤ LevelExpr.eval ν e₂

/-- Equality of two level expressions under the bounds. -/
def EqUnder (Δ : LevelBounds L) (e₁ e₂ : LevelExpr L) : Prop :=
  ∀ ν : Nat → L, Δ.Valid ν → LevelExpr.eval ν e₁ = LevelExpr.eval ν e₂

/-- Equality under the bounds is order in both directions. -/
theorem eqUnder_iff {Δ : LevelBounds L} {e₁ e₂ : LevelExpr L} :
    EqUnder Δ e₁ e₂ ↔ LeUnder Δ e₁ e₂ ∧ LeUnder Δ e₂ e₁ :=
  ⟨fun h => ⟨fun ν valid => le_of_eq (h ν valid), fun ν valid => le_of_eq (h ν valid).symm⟩,
    fun h ν valid => le_antisymm (h.1 ν valid) (h.2 ν valid)⟩

theorem LeUnder.refl (Δ : LevelBounds L) (e : LevelExpr L) : LeUnder Δ e e :=
  fun _ _ => le_refl _

theorem LeUnder.trans {Δ : LevelBounds L} {e₁ e₂ e₃ : LevelExpr L} (h₁ : LeUnder Δ e₁ e₂)
    (h₂ : LeUnder Δ e₂ e₃) : LeUnder Δ e₁ e₃ :=
  fun ν valid => le_trans (h₁ ν valid) (h₂ ν valid)

/-- An order that holds at every valuation holds under every bounds. -/
theorem LeUnder.of_forall {e₁ e₂ : LevelExpr L}
    (h : ∀ ν : Nat → L, LevelExpr.eval ν e₁ ≤ LevelExpr.eval ν e₂) (Δ : LevelBounds L) :
    LeUnder Δ e₁ e₂ :=
  fun ν _ => h ν

/-- Without bounds, the order under the bounds is the order at every valuation. -/
theorem leUnder_unbounded_iff {e₁ e₂ : LevelExpr L} :
    LeUnder (unbounded L) e₁ e₂ ↔
      ∀ ν : Nat → L, LevelExpr.eval ν e₁ ≤ LevelExpr.eval ν e₂ :=
  ⟨fun h ν => h ν (valid_unbounded ν), fun h => LeUnder.of_forall h _⟩

/-- A bounded variable is an admissible argument at its own bound: its successor lies below
the bound. -/
theorem succ_le_of_lt_bound {Δ : LevelBounds L} {i : Nat} {c : L} (h : Δ i = some c) :
    LeUnder Δ (.succ (.param i)) (.const c) :=
  fun _ valid => succ_le_of_lt (valid i c h)

/-- A substitution is admissible from the bounds `Δ` to the bounds `Δ'` when it sends every
variable bounded in `Δ` to an expression that stays below that bound under `Δ'`. -/
def Admissible (Δ' Δ : LevelBounds L) (σ : Nat → LevelExpr L) : Prop :=
  ∀ (i : Nat) (c : L), Δ i = some c → LeUnder Δ' (.succ (σ i)) (.const c)

/-- An admissible substitution turns valid valuations into valid valuations. -/
theorem Admissible.valid {Δ' Δ : LevelBounds L} {σ : Nat → LevelExpr L}
    (admissible : Admissible Δ' Δ σ) {ν : Nat → L} (valid : Δ'.Valid ν) :
    Δ.Valid fun i => LevelExpr.eval ν (σ i) :=
  fun i c h => lt_of_succ_le (admissible i c h ν valid)

/-- The order under bounds is stable under admissible substitutions. -/
theorem leUnder_subst {Δ' Δ : LevelBounds L} {σ : Nat → LevelExpr L} {e₁ e₂ : LevelExpr L}
    (h : LeUnder Δ e₁ e₂) (admissible : Admissible Δ' Δ σ) :
    LeUnder Δ' (e₁.subst σ) (e₂.subst σ) := by
  intro ν valid
  rw [LevelExpr.eval_subst, LevelExpr.eval_subst]
  exact h _ (admissible.valid valid)

/-- Equality under bounds is stable under admissible substitutions. -/
theorem eqUnder_subst {Δ' Δ : LevelBounds L} {σ : Nat → LevelExpr L} {e₁ e₂ : LevelExpr L}
    (h : EqUnder Δ e₁ e₂) (admissible : Admissible Δ' Δ σ) :
    EqUnder Δ' (e₁.subst σ) (e₂.subst σ) := by
  intro ν valid
  rw [LevelExpr.eval_subst, LevelExpr.eval_subst]
  exact h _ (admissible.valid valid)

/-- Instantiating a bounded variable by an expression below its bound is admissible, when
the other variables keep their bounds. -/
theorem admissible_instantiate {Δ' Δ : LevelBounds L} {x : Nat} {a : LevelExpr L}
    (others : ∀ i, i ≠ x → ∀ c, Δ i = some c → Δ' i = some c)
    (below : ∀ c, Δ x = some c → LeUnder Δ' (.succ a) (.const c)) :
    Admissible Δ' Δ (LevelExpr.instantiate x a) := by
  intro i c h
  by_cases hix : i = x
  · subst hix
    simpa [LevelExpr.instantiate] using below c h
  · have h' := succ_le_of_lt_bound (others i hix c h)
    simpa [LevelExpr.instantiate, hix] using h'

end Order

/-! ## The comparison on canonical forms -/

section Decision

open LevelNF

variable [PredLevelOrder L]

/-- Every level below the bound `β`, raised by `k`, fits under `D`, as one comparison: at a
successor bound the largest level below it is its predecessor, and at any other bound the
bound itself must fit. -/
def BoundFits (β : L) (k : Nat) (D : L) : Prop :=
  match pred? β with
  | some γ => addNat γ k ≤ D
  | none => β ≤ D

instance instDecidableBoundFits (β : L) (k : Nat) (D : L) : Decidable (BoundFits β k D) := by
  unfold BoundFits
  cases pred? β <;> infer_instance

/-- If the bound fits, every level below it, raised by `k`, fits. -/
theorem BoundFits.le {β : L} {k : Nat} {D : L} (fits : BoundFits β k D) {a : L}
    (ha : a < β) : addNat a k ≤ D := by
  unfold BoundFits at fits
  cases hp : pred? β with
  | some γ =>
    rw [hp] at fits
    have hβ : β = succ γ := pred?_eq_some.mp hp
    exact le_trans (addNat_le_addNat_left (le_of_lt_succ (hβ ▸ ha)) k) fits
  | none =>
    rw [hp] at fits
    have limit : IsLimit β :=
      isLimit_of_pred?_eq_none (lt_of_le_of_lt (bot_le a) ha) hp
    exact le_trans (le_of_lt (limit.addNat_lt ha k)) fits

/-- If a positive bound does not fit, some level below it, raised by `k`, exceeds `D`. -/
theorem exists_lt_of_not_boundFits {β : L} {k : Nat} {D : L} (pos : bot < β)
    (h : ¬ BoundFits β k D) : ∃ a : L, a < β ∧ D < addNat a k := by
  unfold BoundFits at h
  cases hp : pred? β with
  | some γ =>
    rw [hp] at h
    exact ⟨γ, (pred?_eq_some.mp hp) ▸ lt_succ γ, lt_of_not_ge h⟩
  | none =>
    rw [hp] at h
    have limit : IsLimit β := isLimit_of_pred?_eq_none pos hp
    exact ⟨succ D, limit.succ_lt (lt_of_not_ge h),
      lt_of_lt_of_le (lt_succ D) (le_addNat _ k)⟩

/-- A positive bound fits exactly when every level below it, raised by `k`, fits. -/
theorem boundFits_iff {β : L} {k : Nat} {D : L} (pos : bot < β) :
    BoundFits β k D ↔ ∀ a : L, a < β → addNat a k ≤ D :=
  ⟨fun fits _ ha => fits.le ha, fun h => Decidable.byContradiction fun hNot =>
    let ⟨a, ha, hD⟩ := exists_lt_of_not_boundFits pos hNot
    not_lt_of_ge (h a ha) hD⟩

/-- A left atom fits under a right canonical form: the right side has the same variable
with at least the offset, or the variable is bounded and its bound fits under what the
right side exposes without the variable. -/
def AtomLeUnder (Δ : LevelBounds L) (right : LevelNF L) (ik : Nat × Nat) : Prop :=
  AtomLe right.params ik ∨
    match Δ ik.1 with
    | some β => BoundFits β ik.2 (floorWithout right ik.1)
    | none => False

instance instDecidableAtomLeUnder (Δ : LevelBounds L) (right : LevelNF L) (ik : Nat × Nat) :
    Decidable (AtomLeUnder Δ right ik) := by
  unfold AtomLeUnder
  cases Δ ik.1 <;> infer_instance

/-- The computable order criterion for canonical forms under bounds. -/
def CanonicalLeUnder (Δ : LevelBounds L) (left right : LevelNF L) : Prop :=
  left.constPart ≤ max right.constPart (ofNat (supOffsets right.params)) ∧
    ∀ ik ∈ left.params, AtomLeUnder Δ right ik

instance instDecidableCanonicalLeUnder (Δ : LevelBounds L) (left right : LevelNF L) :
    Decidable (CanonicalLeUnder Δ left right) := by
  unfold CanonicalLeUnder
  infer_instance

/-- The criterion without bounds implies the criterion under any bounds. -/
theorem CanonicalLeUnder.of_canonicalLe {left right : LevelNF L} (h : CanonicalLe left right)
    (Δ : LevelBounds L) : CanonicalLeUnder Δ left right :=
  ⟨h.1, fun ik hik => .inl (h.2 ik hik)⟩

/-- Without bounds, the criterion under bounds is the criterion at every valuation. -/
theorem canonicalLeUnder_unbounded_iff {left right : LevelNF L} :
    CanonicalLeUnder (unbounded L) left right ↔ CanonicalLe left right :=
  ⟨fun h => ⟨h.1, fun ik hik => (h.2 ik hik).elim id False.elim⟩,
    fun h => .of_canonicalLe h _⟩

/-- Soundness of the criterion under bounds. -/
theorem eval_le_of_canonicalLeUnder {Δ : LevelBounds L} {left right : LevelNF L}
    (h : CanonicalLeUnder Δ left right) {ν : Nat → L} (valid : Δ.Valid ν) :
    LevelNF.eval ν left ≤ LevelNF.eval ν right := by
  obtain ⟨c₁, p₁⟩ := left
  refine eval_le_of_bounds ν ?_ c₁ ?_
  · intro ik hMem
    obtain ⟨i, k⟩ := ik
    rcases h.2 (i, k) hMem with hAtom | hBound
    · unfold AtomLe at hAtom
      cases hLookup : lookupParam right.params i with
      | none =>
        rw [show lookupParam right.params (i, k).1 = none from hLookup] at hAtom
        exact False.elim hAtom
      | some l =>
        rw [show lookupParam right.params (i, k).1 = some l from hLookup] at hAtom
        obtain ⟨c₂, p₂⟩ := right
        exact le_trans (addNat_le_addNat_right (ν i) hAtom) (atom_le_eval ν hLookup c₂)
    · cases hΔ : Δ i with
      | none =>
        rw [show Δ (i, k).1 = none from hΔ] at hBound
        exact False.elim hBound
      | some β =>
        rw [show Δ (i, k).1 = some β from hΔ] at hBound
        exact le_trans (BoundFits.le hBound (valid i β hΔ)) (floorWithout_le_eval ν right i)
  · obtain ⟨c₂, p₂⟩ := right
    calc
      c₁ ≤ max c₂ (ofNat (supOffsets p₂)) := h.1
      _ = LevelNF.eval (fun _ => bot) ⟨c₂, p₂⟩ := (eval_zero c₂ p₂).symm
      _ ≤ LevelNF.eval ν ⟨c₂, p₂⟩ := eval_zero_le_eval ν c₂ p₂

/-- **Constructive separation under bounds.** If the criterion fails under positive bounds,
a valuation that respects the bounds makes the left form strictly larger than the right. -/
theorem exists_valid_separator_of_not_canonicalLeUnder {Δ : LevelBounds L}
    (pos : Δ.Positive) {left right : LevelNF L} (hLeft : WF left) (hRight : WF right)
    (hNot : ¬ CanonicalLeUnder Δ left right) :
    ∃ ν : Nat → L, Δ.Valid ν ∧ LevelNF.eval ν right < LevelNF.eval ν left := by
  by_cases hConst :
      left.constPart ≤ max right.constPart (ofNat (supOffsets right.params))
  · have hAtoms : ¬ ∀ ik ∈ left.params, AtomLeUnder Δ right ik := fun h => hNot ⟨hConst, h⟩
    obtain ⟨⟨i, k⟩, hMem, hBad⟩ := exists_mem_not_of_not_forall hAtoms
    have hLookup : lookupParam left.params i = some k :=
      lookupParam_eq_some_of_mem hLeft.1 hMem
    have hAtom : ¬ AtomLe right.params (i, k) := fun h => hBad (.inl h)
    cases hΔ : Δ i with
    | none =>
      -- an unbounded variable: any level above what the right side exposes separates
      refine ⟨_, pos.valid_single (i := i) (a := succ (floorWithout right i))
        (fun c hc => by rw [hΔ] at hc; exact nomatch hc), ?_⟩
      exact single_separates hRight hLookup hAtom
        (lt_of_lt_of_le (lt_succ _) (le_addNat _ k))
    | some β =>
      have hFits : ¬ BoundFits β k (floorWithout right i) := fun h =>
        hBad (.inr (by rw [show Δ (i, k).1 = some β from hΔ]; exact h))
      obtain ⟨a, ha, hD⟩ := exists_lt_of_not_boundFits (pos i β hΔ) hFits
      refine ⟨_, pos.valid_single (i := i) (a := a)
        (fun c hc => by rw [hΔ] at hc; exact (Option.some.inj hc) ▸ ha), ?_⟩
      exact single_separates hRight hLookup hAtom hD
  · refine ⟨fun _ => bot, pos.valid_bot, ?_⟩
    obtain ⟨c₁, p₁⟩ := left
    obtain ⟨c₂, p₂⟩ := right
    rw [eval_zero, eval_zero]
    exact lt_of_lt_of_le (lt_of_not_ge hConst) (le_max_left _ _)

/-- **Exact order theorem for canonical forms under positive bounds.** -/
theorem canonicalLeUnder_iff_eval_le {Δ : LevelBounds L} (pos : Δ.Positive)
    {left right : LevelNF L} (hLeft : WF left) (hRight : WF right) :
    CanonicalLeUnder Δ left right ↔
      ∀ ν : Nat → L, Δ.Valid ν → LevelNF.eval ν left ≤ LevelNF.eval ν right :=
  ⟨fun h _ valid => eval_le_of_canonicalLeUnder h valid, fun h =>
    Decidable.byContradiction fun hNot =>
      let ⟨ν, valid, hSep⟩ :=
        exists_valid_separator_of_not_canonicalLeUnder pos hLeft hRight hNot
      not_lt_of_ge (h ν valid) hSep⟩

/-- **The order decision theorem under bounds.** Under positive bounds, the order of two
level expressions is exactly the finite test on their canonical forms. -/
theorem leUnder_iff_canonical {Δ : LevelBounds L} (pos : Δ.Positive) (e₁ e₂ : LevelExpr L) :
    CanonicalLeUnder Δ (normalize e₁) (normalize e₂) ↔ LeUnder Δ e₁ e₂ := by
  rw [canonicalLeUnder_iff_eval_le pos (wf_normalize e₁) (wf_normalize e₂)]
  constructor
  · intro h ν valid
    have := h ν valid
    rwa [eval_normalize, eval_normalize] at this
  · intro h ν valid
    rw [eval_normalize, eval_normalize]
    exact h ν valid

/-- The test is sound under any bounds, positive or not. -/
theorem leUnder_of_canonical {Δ : LevelBounds L} {e₁ e₂ : LevelExpr L}
    (h : CanonicalLeUnder Δ (normalize e₁) (normalize e₂)) : LeUnder Δ e₁ e₂ := by
  intro ν valid
  have := eval_le_of_canonicalLeUnder h valid
  rwa [eval_normalize, eval_normalize] at this

/-- Under positive bounds, the order of level expressions is decidable. -/
def decideLeUnder {Δ : LevelBounds L} (pos : Δ.Positive) (e₁ e₂ : LevelExpr L) :
    Decidable (LeUnder Δ e₁ e₂) :=
  decidable_of_iff _ (leUnder_iff_canonical pos e₁ e₂)

/-- Under positive bounds, equality of level expressions is decidable: two order tests. -/
def decideEqUnder {Δ : LevelBounds L} (pos : Δ.Positive) (e₁ e₂ : LevelExpr L) :
    Decidable (EqUnder Δ e₁ e₂) :=
  have := decideLeUnder pos e₁ e₂
  have := decideLeUnder pos e₂ e₁
  decidable_of_iff _ eqUnder_iff.symm

/-- Refusing a comparison under positive bounds produces a valuation that respects the
bounds and reverses the alleged order. -/
theorem exists_separator_of_not_leUnder {Δ : LevelBounds L} (pos : Δ.Positive)
    {e₁ e₂ : LevelExpr L} (hNot : ¬ LeUnder Δ e₁ e₂) :
    ∃ ν : Nat → L, Δ.Valid ν ∧ LevelExpr.eval ν e₂ < LevelExpr.eval ν e₁ := by
  have hCanonical : ¬ CanonicalLeUnder Δ (normalize e₁) (normalize e₂) := fun h =>
    hNot ((leUnder_iff_canonical pos e₁ e₂).mp h)
  obtain ⟨ν, valid, hSep⟩ :=
    exists_valid_separator_of_not_canonicalLeUnder pos (wf_normalize e₁) (wf_normalize e₂)
      hCanonical
  refine ⟨ν, valid, ?_⟩
  rwa [eval_normalize, eval_normalize] at hSep

end Decision

end LevelBounds

/-! ## The supremum over a bounded variable -/

namespace LevelExpr

variable [PredLevelOrder L]

/-- The supremum of an expression over the values of the variable `x` below the closed
bound `c`: at a successor bound, the instance at its predecessor; otherwise the instance
at the least level, joined with the bound when the variable occurs. -/
def boundedSup (x : Nat) (c : L) (e : LevelExpr L) : LevelExpr L :=
  match pred? c with
  | some p => e.subst (instantiate x (.const p))
  | none =>
    if occurs x e then .max (e.subst (instantiate x (.const bot))) (.const c)
    else e.subst (instantiate x (.const bot))

/-- The supremum is an upper bound: it lies above the expression at every value of the
variable below the bound. -/
theorem boundedSup_upper {x : Nat} {c : L} (e : LevelExpr L) (ν : Nat → L) {a : L}
    (ha : a < c) : eval (Function.update ν x a) e ≤ eval ν (boundedSup x c e) := by
  unfold boundedSup
  cases hp : pred? c with
  | some p =>
    show _ ≤ eval ν (e.subst (instantiate x (.const p)))
    rw [eval_subst_instantiate]
    refine eval_mono (fun i => ?_) e
    by_cases hix : i = x
    · subst hix
      rw [Function.update_self, Function.update_self]
      exact le_of_lt_succ ((pred?_eq_some.mp hp) ▸ ha)
    · rw [Function.update_of_ne hix, Function.update_of_ne hix]
  | none =>
    have limit : IsLimit c := isLimit_of_pred?_eq_none (lt_of_le_of_lt (bot_le a) ha) hp
    show _ ≤ eval ν (if occurs x e then
      .max (e.subst (instantiate x (.const bot))) (.const c)
      else e.subst (instantiate x (.const bot)))
    cases ho : occurs x e with
    | true =>
      rw [if_pos rfl]
      show _ ≤ Max.max (eval ν (e.subst (instantiate x (.const bot)))) c
      rw [eval_subst_instantiate]
      rcases eval_update_le_or_lt ν limit ha e with h | h
      · exact le_trans h (le_max_left _ _)
      · exact le_trans (le_of_lt h) (le_max_right _ _)
    | false =>
      rw [if_neg (by simp)]
      rw [eval_subst_instantiate, eval_update_of_not_occurs ν a ho,
        eval_update_of_not_occurs ν bot ho]

/-- The supremum is the least upper bound, at every valuation of the other variables. -/
theorem boundedSup_least {x : Nat} {c : L} (pos : bot < c) (e : LevelExpr L) (ν : Nat → L)
    {B : L} (h : ∀ a : L, a < c → eval (Function.update ν x a) e ≤ B) :
    eval ν (boundedSup x c e) ≤ B := by
  unfold boundedSup
  cases hp : pred? c with
  | some p =>
    show eval ν (e.subst (instantiate x (.const p))) ≤ B
    rw [eval_subst_instantiate]
    exact h p ((pred?_eq_some.mp hp) ▸ lt_succ p)
  | none =>
    have limit : IsLimit c := isLimit_of_pred?_eq_none pos hp
    show eval ν (if occurs x e then
      .max (e.subst (instantiate x (.const bot))) (.const c)
      else e.subst (instantiate x (.const bot))) ≤ B
    cases ho : occurs x e with
    | true =>
      rw [if_pos rfl]
      show Max.max (eval ν (e.subst (instantiate x (.const bot)))) c ≤ B
      rw [eval_subst_instantiate]
      refine max_le (h bot pos) (le_of_not_gt fun hB => ?_)
      have hsucc : LevelOrder.succ B < c := limit.succ_lt hB
      have hle : LevelOrder.succ B ≤ eval (Function.update ν x (LevelOrder.succ B)) e := by
        have := le_eval_of_occurs (Function.update ν x (LevelOrder.succ B)) ho
        rwa [Function.update_self] at this
      exact not_lt_of_ge (le_trans hle (h (LevelOrder.succ B) hsucc)) (lt_succ B)
    | false =>
      rw [if_neg (by simp)]
      rw [eval_subst_instantiate]
      exact h bot pos

omit [PredLevelOrder L] in
/-- Updating a variable twice keeps the last value. -/
theorem update_update (ν : Nat → L) (x : Nat) (a b : L) :
    Function.update (Function.update ν x a) x b = Function.update ν x b := by
  funext i
  by_cases h : i = x
  · subst h
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne h, Function.update_of_ne h, Function.update_of_ne h]

/-- The variable no longer matters in the supremum. -/
theorem eval_boundedSup_update {x : Nat} {c : L} (pos : bot < c) (e : LevelExpr L)
    (ν : Nat → L) (a : L) :
    eval (Function.update ν x a) (boundedSup x c e) = eval ν (boundedSup x c e) := by
  apply le_antisymm
  · refine boundedSup_least pos e _ fun b hb => ?_
    rw [update_update]
    exact boundedSup_upper e ν hb
  · refine boundedSup_least pos e _ fun b hb => ?_
    have := boundedSup_upper e (Function.update ν x a) (x := x) hb
    rwa [update_update] at this

end LevelExpr

/-! ## The least level whose successor reaches a level

The instance of a level parameter is inferred as the least level that satisfies its
constraints. For a constraint `a ≤ l + 1` the least `l` is the predecessor of `a` when `a` is a
successor, and `a` itself at the least level and at limits. -/

namespace PredLevelOrder

open LevelOrder

variable [PredLevelOrder L]

/-- The least level whose successor reaches a level: the predecessor of a successor, and the
level itself at the least level and at limits. -/
def underSucc (a : L) : L := (pred? a).getD a

/-- At a successor it is the predecessor. -/
@[simp] theorem underSucc_succ (p : L) : underSucc (succ p) = p := by
  unfold underSucc
  rw [pred?_succ]
  rfl

/-- At a level that is not a successor it is the level. -/
theorem underSucc_of_pred?_eq_none {a : L} (h : pred? a = none) : underSucc a = a := by
  unfold underSucc
  rw [h]
  rfl

/-- **A level is below the successor of another exactly when the least level whose successor
reaches it is below that one.** -/
theorem le_succ_iff_underSucc_le {a l : L} : a ≤ succ l ↔ underSucc a ≤ l := by
  cases hp : pred? a with
  | some p =>
    have ha : a = succ p := pred?_eq_some.mp hp
    subst ha
    rw [underSucc_succ]
    exact succ_le_succ_iff
  | none =>
    rw [underSucc_of_pred?_eq_none hp]
    constructor
    · intro h
      exact le_of_lt_succ (lt_of_le_of_ne h fun same => pred?_eq_none.mp hp l same.symm)
    · exact fun h => le_trans h (le_succ l)

/-- Its successor reaches the level. -/
theorem le_succ_underSucc (a : L) : a ≤ succ (underSucc a) :=
  le_succ_iff_underSucc_le.mpr (le_refl _)

/-- **It is the least such level.** -/
theorem underSucc_le_of_le_succ {a l : L} (h : a ≤ succ l) : underSucc a ≤ l :=
  le_succ_iff_underSucc_le.mp h

end PredLevelOrder

/-! ## Examples over the natural numbers -/

section Examples

open LevelBounds LevelExpr

/-- The variable `0` ranges below `3`; the others are unbounded. -/
def belowThree : LevelBounds Nat := fun i => if i = 0 then some 3 else none

theorem belowThree_positive : belowThree.Positive := by
  intro i c h
  unfold belowThree at h
  split at h
  · cases h
    decide
  · exact nomatch h

/-- For `x < 3`, `x + 1 ≤ 3`: the test compares the predecessor `2`, raised by one. -/
example : LeUnder belowThree (.succ (.param 0)) (.const 3) :=
  leUnder_of_canonical (by decide)

/-- Without the bound the same comparison fails. -/
example : ¬ ∀ ν : Nat → Nat, eval ν (.succ (.param 0)) ≤ eval ν (.const 3 : LevelExpr Nat) := by
  decide

/-- For `x < 3`, `x + 2 ≤ 3` fails. -/
example : ¬ LeUnder belowThree (.succ (.succ (.param 0))) (.const 3) :=
  fun h => absurd ((leUnder_iff_canonical belowThree_positive _ _).mpr h) (by decide)

/-- The valuation `x = 2` respects the bound and reverses that comparison. -/
example : belowThree.Valid (fun _ => 2) ∧
    eval (fun _ => 2) (.const 3 : LevelExpr Nat) <
      eval (fun _ => 2) (.succ (.succ (.param 0))) := by
  refine ⟨fun i c h => ?_, by decide⟩
  unfold belowThree at h
  split at h
  · cases h
    exact (by decide : (2 : Nat) < 3)
  · exact nomatch h

/-- A bounded variable is absorbed by a constant above its bound: for `x < 3`,
`max 5 (x + 1)` and `5` are equal, although their canonical forms differ. -/
example : EqUnder belowThree (.max (.const 5) (.succ (.param 0))) (.const 5) :=
  eqUnder_iff.mpr ⟨leUnder_of_canonical (by decide), leUnder_of_canonical (by decide)⟩

/-- The supremum of `x + 1` over `x < 3` is the instance at `2`, which is `3`. -/
example : ∀ ν : Nat → Nat,
    eval ν (boundedSup 0 3 (.succ (.param 0))) = eval ν (.const 3 : LevelExpr Nat) := by
  decide

/-- Under a bound at the least level no valuation is valid, so a false comparison holds:
bounds must be positive. -/
theorem leUnder_of_bound_bot :
    LeUnder (fun _ => some (0 : Nat)) (.const 1) (.const 0 : LevelExpr Nat) :=
  fun _ valid => absurd (valid 0 0 rfl) (Nat.not_lt_zero _)

/-- The same comparison fails at every valuation. -/
example : ¬ ∀ ν : Nat → Nat, eval ν (.const 1) ≤ eval ν (.const 0 : LevelExpr Nat) := by
  decide

/-- The least level whose successor reaches `3` is `2`; at `0` it is `0`. -/
example : PredLevelOrder.underSucc (3 : Nat) = 2 ∧ PredLevelOrder.underSucc (0 : Nat) = 0 := by
  decide

/-- Negative: `1` is not enough for a successor to reach `3`. -/
example : ¬ (3 : Nat) ≤ LevelOrder.succ 1 := by decide

end Examples

/-! ## Examples over the ordinal notations below ε₀ -/

section TransfiniteExamples

open LevelBounds LevelExpr

/-- The variable `0` ranges below `ω`; the others are unbounded. -/
def belowOmega : LevelBounds Level := fun i => if i = 0 then some Level.omega else none

theorem belowOmega_positive : belowOmega.Positive := by
  intro i c h
  unfold belowOmega at h
  split at h
  · cases h
    exact Level.ofNat_lt_omega 0
  · exact nomatch h

/-- For `x < ω`, `x + 1 ≤ ω`: at a limit bound the test compares the bound itself. -/
example : LeUnder belowOmega (.succ (.param 0)) (.const Level.omega) :=
  leUnder_of_canonical (by decide)

/-- For `x < ω`, every finite offset of `x` stays below `ω`. -/
example : LeUnder belowOmega (.succ (.succ (.succ (.param 0)))) (.const Level.omega) :=
  leUnder_of_canonical (by decide)

/-- For `x < ω`, `x ≤ 7` fails: the values of `x` are cofinal in `ω`. -/
example : ¬ LeUnder belowOmega (.param 0) (.const (Level.ofNat 7)) :=
  fun h => absurd ((leUnder_iff_canonical belowOmega_positive _ _).mpr h) (by decide)

/-- `ω + 1 ≤ ω` fails: `ω` is not a value of a variable below `ω`. -/
example : ¬ ∀ ν : Nat → Level,
    eval ν (.succ (.const Level.omega)) ≤ eval ν (.const Level.omega : LevelExpr Level) := by
  decide

/-- `ω + 1 ≤ 7` fails: the level `ω` lies below no finite level. -/
example : ¬ ∀ ν : Nat → Level,
    eval ν (.succ (.const Level.omega)) ≤ eval ν (.const (Level.ofNat 7) : LevelExpr Level) := by
  decide

/-- Every finite level lies below `ω`. -/
example : ∀ ν : Nat → Level,
    eval ν (.succ (.const (Level.ofNat 1000))) ≤ eval ν (.const Level.omega : LevelExpr Level) := by
  decide

/-- An unbounded variable may take the value `ω`: `x + 1 ≤ ω` fails without the bound. -/
example : ¬ ∀ ν : Nat → Level,
    eval ν (.succ (.param 0)) ≤ eval ν (.const Level.omega : LevelExpr Level) := by
  decide

/-- The supremum of `x + 1` over `x < ω` is `ω`. -/
example : ∀ ν : Nat → Level,
    eval ν (boundedSup 0 Level.omega (.succ (.param 0))) =
      eval ν (.const Level.omega : LevelExpr Level) := by
  decide

/-- The supremum of `x + 1` over `x < ω + 1` is `ω + 1`. -/
example : ∀ ν : Nat → Level,
    eval ν (boundedSup 0 (Level.succ Level.omega) (.succ (.param 0))) =
      eval ν (.const (Level.succ Level.omega) : LevelExpr Level) := by
  decide

/-- The supremum keeps the other variables: over `x < ω`, the supremum of
`max (x + 1) (y + 2)` is `max ω (y + 2)`. -/
example : ∀ ν : Nat → Level,
    eval ν (boundedSup 0 Level.omega (.max (.succ (.param 0)) (.succ (.succ (.param 1))))) =
      eval ν (.max (.const Level.omega) (.succ (.succ (.param 1))) : LevelExpr Level) := by
  decide

/-- A variable that does not occur leaves the expression alone: the supremum of `7` over
`x < ω` is `7`, not `ω`. -/
example : ∀ ν : Nat → Level,
    eval ν (boundedSup 0 Level.omega (.const (Level.ofNat 7))) =
      eval ν (.const (Level.ofNat 7) : LevelExpr Level) := by
  decide

/-- The least level whose successor reaches `ω` is `ω`: no finite level is enough. At `ω + 1`
it is `ω`. -/
example : PredLevelOrder.underSucc Level.omega = Level.omega ∧
    PredLevelOrder.underSucc (LevelOrder.succ Level.omega) = Level.omega := by
  decide

/-- Negative: the successor of the finite level `7` does not reach `ω`. -/
example : ¬ Level.omega ≤ LevelOrder.succ (Level.ofNat 7) := by decide

end TransfiniteExamples

end Mettapedia.TypeTheory.UniverseLevel
