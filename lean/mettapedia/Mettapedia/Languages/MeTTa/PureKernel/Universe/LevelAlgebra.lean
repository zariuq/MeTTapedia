import Mathlib

/-!
# The trusted level algebra (universe lane, tier 2 of 2)

Levels are the one piece of the universe design that is independent of
the Russell/Tarski adjudication: whatever presentation is chosen,
universe formation needs a *decidable* level theory at the trust
boundary — kernel conversion of `(u n₁)` with `(u n₂)` must never
involve evaluation of arbitrary language data.  This module isolates
exactly that algebra and proves it decidable.

Design (the two-tier verdict already on record):

* **Tier 1 — `LevelData`**: ordinary homoiconic data; anything users
  construct, quote, transform.  Not trusted.  (Lives outside this
  module; any term data type can serve.)
* **Tier 2 — the admitted algebra** (this module): literals, level
  parameters, `succ`, and `max`, with valuation semantics, canonical
  normal forms, and *decidable* equality and order under **all**
  valuations.  `imax` is deliberately absent: it is the impredicative
  option, and whether Prime wants impredicativity is a separate
  adjudication, not a default.

The central artifacts are `decideLevelEq` and `decideLevelLe`: level
equality and order under all valuations are decided by computing and
finitely comparing canonical forms.  Canonical form uniqueness
(`LevelNF.unique_of_eval_eq`) and exact order
(`LevelNF.canonicalLe_iff_eval_le`) make the procedures *sound and
complete*, not heuristics.

The semantics mirrors the standard level theory (offsets over
parameters, absorption of dominated atoms); predicativity is the only
commitment, matching the sealed fragment's conservative stance.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe

/-! ## Level expressions (the data tier, well-formed core) -/

/-- Level expressions: the kernel's admitted level language.
`param i` is a level *variable* — needed for universe polymorphism
(schema-level rules quantify over levels); `const n` a literal. -/
inductive LevelExpr where
  | const : Nat → LevelExpr
  | param : Nat → LevelExpr
  | succ : LevelExpr → LevelExpr
  | max : LevelExpr → LevelExpr → LevelExpr
  deriving DecidableEq, Repr

/-- Valuation semantics: a level expression denotes a natural number
once its parameters are assigned. -/
def LevelExpr.eval (v : Nat → Nat) : LevelExpr → Nat
  | .const c => c
  | .param i => v i
  | .succ e => eval v e + 1
  | .max e₁ e₂ => Max.max (eval v e₁) (eval v e₂)

/-- Simultaneous substitution of level expressions for parameters. -/
def LevelExpr.subst (σ : Nat → LevelExpr) : LevelExpr → LevelExpr
  | .const c => .const c
  | .param i => σ i
  | .succ e => .succ (subst σ e)
  | .max e₁ e₂ => .max (subst σ e₁) (subst σ e₂)

/-- Substitution acts on semantics by composing the valuation with the
semantic interpretation of the substituted expressions. -/
@[simp] theorem LevelExpr.eval_subst (v : Nat → Nat)
    (σ : Nat → LevelExpr) (e : LevelExpr) :
    eval v (subst σ e) = eval (fun i => eval v (σ i)) e := by
  induction e with
  | const c => rfl
  | param i => rfl
  | succ e ih => simp only [subst, eval, ih]
  | max e₁ e₂ ih₁ ih₂ => simp only [subst, eval, ih₁, ih₂]

/-- Parameters form the identity substitution. -/
@[simp] theorem LevelExpr.subst_param (e : LevelExpr) :
    subst param e = e := by
  induction e with
  | const c => rfl
  | param i => rfl
  | succ e ih => simp only [subst, ih]
  | max e₁ e₂ ih₁ ih₂ => simp only [subst, ih₁, ih₂]

/-- Simultaneous substitutions compose by substituting into each image
of the first substitution. -/
theorem LevelExpr.subst_subst (τ σ : Nat → LevelExpr) (e : LevelExpr) :
    subst τ (subst σ e) = subst (fun i => subst τ (σ i)) e := by
  induction e with
  | const c => rfl
  | param i => rfl
  | succ e ih => simp only [subst, ih]
  | max e₁ e₂ ih₁ ih₂ => simp only [subst, ih₁, ih₂]

/-! ## Canonical normal forms

A level expression under all valuations is a `max` of (i) a constant
and (ii) finitely many parameter-plus-offset atoms.  Constants and
same-parameter atoms collapse by idempotence; a constant dominated by
some parameter offset is absorbed (it can never be the maximum under
any valuation). -/

/-- Canonical normal form: one constant and a sorted, key-distinct
list of `(parameter, offset)` atoms. -/
structure LevelNF where
  constPart : Nat
  /-- `(parameter, offset)` atoms, strictly sorted by parameter. -/
  params : List (Nat × Nat)
  deriving DecidableEq, Repr

namespace LevelNF

/-- Lookup of a parameter's offset in the atom list. -/
def lookupParam : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (j, k) :: rest, i => if i = j then some k else lookupParam rest i

/-- The atom list is strictly sorted by parameter key. -/
def Sorted (ps : List (Nat × Nat)) : Prop :=
  ps.Pairwise fun a b => a.1 < b.1

/-- Well-formedness: sorted keys, and the constant, if nonzero, is not
absorbed by any parameter offset (a constant `≤ k + v i` for every
valuation contributes nothing). -/
def WF (nf : LevelNF) : Prop :=
  Sorted nf.params ∧
  ∀ (i k : Nat), lookupParam nf.params i = some k →
    nf.constPart = 0 ∨ k < nf.constPart

/-- Semantics of a canonical form under a valuation. -/
def eval (v : Nat → Nat) (nf : LevelNF) : Nat :=
  nf.params.foldl (fun acc (ik : Nat × Nat) => max acc
    (ik.2 + v ik.1)) nf.constPart

/-- The folded supremum of the offsets. -/
def supOffsets (ps : List (Nat × Nat)) : Nat :=
  ps.foldl (fun acc (ik : Nat × Nat) => max acc ik.2) 0

@[simp] theorem eval_nil (v : Nat → Nat) (constPart : Nat) :
    eval v ⟨constPart, []⟩ = constPart := rfl

theorem sorted_tail {b : Nat × Nat} {rest : List (Nat × Nat)}
    (h : Sorted (b :: rest)) : Sorted rest :=
  (List.pairwise_cons.mp h).2

/-- Sortedness does not feel the offset component. -/
theorem Sorted.snd_irrelevant {a b : Nat × Nat} {rest : List (Nat × Nat)}
    (hf : a.1 = b.1) (hs : Sorted (a :: rest)) :
    Sorted (b :: rest) := by
  cases rest with
  | nil => exact List.pairwise_singleton _ _
  | cons d tail =>
      have hs' : List.Pairwise (fun x y => x.1 < y.1) (a :: d :: tail) := hs
      rw [List.pairwise_cons] at hs'
      obtain ⟨h1, h2⟩ := hs'
      show List.Pairwise (fun x y => x.1 < y.1) (b :: d :: tail)
      rw [List.pairwise_cons]
      exact And.intro (fun x hx => hf ▸ h1 x hx) h2

/-- Every key strictly above `i` means `i` is absent. -/
theorem lookupParam_none_of_forall_lt {ps : List (Nat × Nat)} {i : Nat}
    (h : ∀ b ∈ ps, i < b.1) : lookupParam ps i = none := by
  induction ps with
  | nil => rfl
  | cons b rest ih =>
      simp only [lookupParam]
      rw [if_neg (Nat.ne_of_lt (h b (by simp)))]
      exact ih (fun c hc => h c (by simp [hc]))

theorem lookupParam_none_of_sorted_head_lt {ps : List (Nat × Nat)}
    {b : Nat × Nat}
    (hs : Sorted (b :: ps)) {i : Nat} (hlt : i < b.1) :
    lookupParam (b :: ps) i = none := by
  apply lookupParam_none_of_forall_lt
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hmem
  · exact hlt
  · exact lt_trans hlt ((List.pairwise_cons.mp hs).1 _ hmem)

/-- Keys are unique in a sorted list. -/
theorem lookupParam_unique_of_sorted {ps : List (Nat × Nat)}
    (hSort : Sorted ps) {i k₁ k₂ : Nat}
    (h₁ : lookupParam ps i = some k₁)
    (h₂ : lookupParam ps i = some k₂) : k₁ = k₂ := by
  induction ps with
  | nil => simp [lookupParam] at h₁
  | cons b rest ih =>
      simp only [lookupParam] at h₁ h₂
      by_cases hEq : i = b.1
      · rw [if_pos hEq] at h₁ h₂
        simp at h₁ h₂
        omega
      · rw [if_neg hEq] at h₁ h₂
        exact ih (sorted_tail hSort) h₁ h₂

/-- A sorted fold of `max` against a fixed valuation absorbs an
addition to the accumulator. -/
theorem foldl_max_acc (v : Nat → Nat) (x : Nat) :
    ∀ (ps : List (Nat × Nat)) (c : Nat),
      ps.foldl (fun acc (ik : Nat × Nat) => max acc (ik.2 + v ik.1))
          (max c x) =
        max
          (ps.foldl (fun acc (ik : Nat × Nat) => max acc (ik.2 + v ik.1))
            c) x
  | [], _ => rfl
  | b :: rest, c => by
      simp only [List.foldl_cons]
      have hSwap : max (max c x) (b.2 + v b.1) =
          max (max c (b.2 + v b.1)) x := by
        rw [Nat.max_assoc, Nat.max_assoc,
          Nat.max_comm x (b.2 + v b.1)]
      rw [hSwap, foldl_max_acc v x rest (Nat.max c (b.2 + v b.1))]

/-- The offsets-fold version of accumulator absorption. -/
theorem foldl_snd_acc (x : Nat) :
    ∀ (ps : List (Nat × Nat)) (c : Nat),
      ps.foldl (fun acc (ik : Nat × Nat) => max acc ik.2)
          (max c x) =
        max
          (ps.foldl (fun acc (ik : Nat × Nat) => max acc ik.2) c) x
  | [], _ => rfl
  | b :: rest, c => by
      simp only [List.foldl_cons]
      have hSwap : max (max c x) b.2 =
          max (max c b.2) x := by
        rw [Nat.max_assoc, Nat.max_assoc, Nat.max_comm x b.2]
      rw [hSwap, foldl_snd_acc x rest (Nat.max c b.2)]

/-- Evaluating a canonical form whose head atom is `(j, k)` splits the
head out. -/
theorem eval_cons (v : Nat → Nat) (c j k : Nat) (ps : List (Nat × Nat)) :
    eval v ⟨c, (j, k) :: ps⟩ = max (eval v ⟨c, ps⟩) (k + v j) := by
  have hUnfold : eval v ⟨c, (j, k) :: ps⟩ =
      eval v ⟨Nat.max c (k + v j), ps⟩ := rfl
  rw [hUnfold]
  unfold eval
  rw [foldl_max_acc]

/-- The offsets supremum of a cons list. -/
theorem supOffsets_cons (j k : Nat) (ps : List (Nat × Nat)) :
    supOffsets ((j, k) :: ps) = max (supOffsets ps) k := by
  unfold supOffsets
  simp only [List.foldl_cons]
  rw [foldl_snd_acc]

/-- A found atom's offset never exceeds the supremum. -/
theorem supOffsets_ge_of_lookup {ps : List (Nat × Nat)} {i k : Nat}
    (h : lookupParam ps i = some k) : k ≤ supOffsets ps := by
  induction ps with
  | nil =>
      rw [lookupParam] at h
      exact absurd h.symm (Option.some_ne_none k)
  | cons b rest ih =>
      simp only [lookupParam] at h
      by_cases hEq : i = b.1
      · rw [if_pos hEq] at h
        rw [Option.some.injEq] at h
        rw [supOffsets_cons, h]
        exact Nat.le_max_right _ _
      · rw [if_neg hEq] at h
        rw [supOffsets_cons]
        exact Nat.le_trans (ih h) (Nat.le_max_left _ _)

/-- `max` distributes over addition on the right. -/
theorem max_add_right (a b c : Nat) :
    max a b + c = max (a + c) (b + c) := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h, Nat.max_eq_right (Nat.add_le_add_right h c)]
  · rw [Nat.max_eq_left h, Nat.max_eq_left (Nat.add_le_add_right h c)]

/-- A zero constant contributes nothing. -/
theorem eval_constPart (v : Nat → Nat) (c : Nat) (ps : List (Nat × Nat)) :
    eval v ⟨c, ps⟩ = max c (eval v ⟨0, ps⟩) := by
  show ps.foldl (fun acc (ik : Nat × Nat) => max acc (ik.2 + v ik.1))
      c =
    max c (ps.foldl (fun acc (ik : Nat × Nat) =>
      max acc (ik.2 + v ik.1)) 0)
  have hAcc := foldl_max_acc v c ps 0
  rw [Nat.max_eq_right (Nat.zero_le c)] at hAcc
  rw [hAcc]
  exact Nat.max_comm _ _

/-- The offsets-fold is pointwise below the evaluation fold. -/
theorem foldl_max_le_eval (v : Nat → Nat) :
    ∀ (ps : List (Nat × Nat)) (c₁ c₂ : Nat), c₁ ≤ c₂ →
      ps.foldl (fun acc (ik : Nat × Nat) => max acc ik.2) c₁ ≤
        ps.foldl (fun acc (ik : Nat × Nat) => max acc (ik.2 + v ik.1))
          c₂
  | [], _, _, h => h
  | b :: rest, c₁, c₂, h => by
      simp only [List.foldl_cons]
      exact foldl_max_le_eval v rest _ _
        (Nat.max_le.mpr ⟨Nat.le_trans h (Nat.le_max_left _ _),
          Nat.le_trans (Nat.le_add_right b.2 (v b.1))
            (Nat.le_max_right _ _)⟩)

/-- The folded supremum of the offsets never exceeds the evaluation. -/
theorem eval_ge_sup (v : Nat → Nat) (ps : List (Nat × Nat)) :
    supOffsets ps ≤ eval v ⟨0, ps⟩ :=
  foldl_max_le_eval v ps 0 0 (le_refl 0)

/-- Semantic correctness of absorption: keeping or dropping a dominated
constant changes nothing. -/
theorem eval_absorb (v : Nat → Nat) (c : Nat) (ps : List (Nat × Nat)) :
    eval v ⟨if c ≤ supOffsets ps then 0 else c, ps⟩ =
      Nat.max c (eval v ⟨0, ps⟩) := by
  by_cases hc : c ≤ supOffsets ps
  · rw [if_pos hc]
    exact (Nat.max_eq_right (Nat.le_trans hc (eval_ge_sup v ps))).symm
  · rw [if_neg hc, eval_constPart]

/-! ### Insertion -/

/-- Insert a `(parameter, offset)` atom into a sorted atom list,
combining same-parameter offsets by `max`. -/
def insertParam (i k : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(i, k)]
  | (j, l) :: rest =>
      if i = j then (i, max k l) :: rest
      else if i < j then (i, k) :: (j, l) :: rest
      else (j, l) :: insertParam i k rest

/-- Keys of an inserted list are the old keys plus possibly `i`. -/
theorem key_eq_of_mem_insertParam {i k : Nat} {ps : List (Nat × Nat)}
    {x : Nat × Nat} (hx : x ∈ insertParam i k ps) :
    x.1 = i ∨ ∃ y ∈ ps, x.1 = y.1 := by
  induction ps with
  | nil =>
      simp only [insertParam, List.mem_singleton] at hx
      rw [hx]
      exact .inl rfl
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      unfold insertParam at hx
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact .inl rfl
        · exact .inr ⟨x, List.Mem.tail _ hmem, rfl⟩
      · by_cases hl : i < j
        · rw [if_neg hij, if_pos hl] at hx
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact .inl rfl
          · exact .inr ⟨x, hmem, rfl⟩
        · rw [if_neg hij, if_neg hl] at hx
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact .inr ⟨(j, l), by simp, rfl⟩
          · rcases ih hmem with h | ⟨y, hy, hf⟩
            · exact .inl h
            · exact .inr ⟨y, List.Mem.tail _ hy, hf⟩

/-- Insertion preserves sortedness. -/
theorem sorted_insert {i k : Nat} {ps : List (Nat × Nat)}
    (hs : Sorted ps) : Sorted (insertParam i k ps) := by
  induction ps with
  | nil =>
      exact List.pairwise_singleton _ _
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      unfold insertParam
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        exact Sorted.snd_irrelevant (a := (i, l))
          (b := (i, max k l)) rfl hs
      · by_cases hl : i < j
        · rw [if_neg hij, if_pos hl]
          show List.Pairwise (fun x y => x.1 < y.1)
            ((i, k) :: (j, l) :: rest)
          rw [List.pairwise_cons]
          refine And.intro (fun x hx => ?_) hs
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact hl
          · exact lt_trans hl ((List.pairwise_cons.mp hs).1 _ hmem)
        · rw [if_neg hij, if_neg hl]
          show List.Pairwise (fun x y => x.1 < y.1)
            ((j, l) :: insertParam i k rest)
          rw [List.pairwise_cons]
          refine And.intro (fun x hx => ?_) (ih (sorted_tail hs))
          rcases key_eq_of_mem_insertParam hx with hkey | ⟨y, hy, hf⟩
          · omega
          · calc (j : Nat) < y.1 := (List.pairwise_cons.mp hs).1 _ hy
              _ = x.1 := hf.symm

/-- The offsets supremum sits strictly below a surviving constant. -/
theorem sup_lt_const_of_wf {c : Nat} {ps : List (Nat × Nat)}
    (hs : Sorted ps)
    (hwf : ∀ (i k : Nat), lookupParam ps i = some k → c = 0 ∨ k < c)
    (hc : c ≠ 0) : supOffsets ps < c := by
  induction ps with
  | nil => simp [supOffsets]; omega
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      rw [supOffsets_cons]
      have hl : l < c := by
        rcases hwf j l (by rw [lookupParam, if_pos rfl]) with h | h
        · exact absurd h hc
        · exact h
      have hrec : supOffsets rest < c := by
        apply ih (sorted_tail hs)
        intro i k hk
        by_cases hij : i = j
        · subst hij
          exfalso
          have hNone : lookupParam rest i = none :=
            lookupParam_none_of_forall_lt
              (fun x hx => (List.pairwise_cons.mp hs).1 x hx)
          rw [hNone] at hk
          simp at hk
        · apply hwf i k
          rw [lookupParam, if_neg hij]
          exact hk
      omega

/-- A `max` swizzle used by the evaluation of insertion. -/
theorem max_stutter (a b c : Nat) :
    max (max a b) c = max (max a c) b := by
  apply Nat.le_antisymm
  · exact Nat.max_le.mpr
      ⟨Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left a c) (Nat.le_max_left _ b),
          Nat.le_max_right (max a c) b⟩,
        Nat.le_trans (Nat.le_max_right a c) (Nat.le_max_left _ b)⟩
  · exact Nat.max_le.mpr
      ⟨Nat.max_le.mpr
        ⟨Nat.le_trans (Nat.le_max_left a b) (Nat.le_max_left _ c),
          Nat.le_max_right (max a b) c⟩,
        Nat.le_trans (Nat.le_max_right a b) (Nat.le_max_left _ c)⟩

/-- Semantic correctness of insertion. -/
theorem eval_insert (v : Nat → Nat) (c i k : Nat) (ps : List (Nat × Nat)) :
    eval v ⟨c, insertParam i k ps⟩ =
      max (eval v ⟨c, ps⟩) (k + v i) := by
  induction ps with
  | nil =>
      rw [show insertParam i k [] = [(i, k)] from rfl, eval_cons]
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      unfold insertParam
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, eval_cons, eval_cons, max_add_right,
          Nat.max_left_comm (eval v ⟨c, rest⟩) (k + v i) (l + v i),
          Nat.max_comm (k + v i)]
      · by_cases hl : i < j
        · rw [if_neg hij, if_pos hl, eval_cons, eval_cons]
        · rw [if_neg hij, if_neg hl, eval_cons, eval_cons, ih,
            max_stutter]

/-- Insertion keeps the offset of the same parameter, combined by
`max`. -/
theorem lookupParam_insert_self {i k : Nat} {ps : List (Nat × Nat)}
    (hs : Sorted ps) :
    lookupParam (insertParam i k ps) i =
      some (max k ((lookupParam ps i).getD 0)) := by
  induction ps with
  | nil => simp [insertParam, lookupParam]
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      unfold insertParam
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, lookupParam, if_pos rfl, lookupParam, if_pos rfl]
        rfl
      · by_cases hl : i < j
        · rw [if_neg hij, if_pos hl, lookupParam, if_pos rfl,
            lookupParam_none_of_sorted_head_lt hs hl, Option.getD_none]
          simp
        · rw [if_neg hij, if_neg hl, lookupParam, if_neg hij,
            ih (sorted_tail hs), lookupParam, if_neg hij]

/-- Insertion under a different parameter leaves the entry alone. -/
theorem lookupParam_insert_other {i j k : Nat} {ps : List (Nat × Nat)}
    (hs : Sorted ps) (hij : i ≠ j) :
    lookupParam (insertParam j k ps) i = lookupParam ps i := by
  induction ps with
  | nil => simp [insertParam, lookupParam, hij]
  | cons b rest ih =>
      obtain ⟨j', l⟩ := b
      unfold insertParam
      by_cases hjj : j = j'
      · subst hjj
        rw [if_pos rfl, lookupParam, lookupParam, if_neg hij, if_neg hij]
      · by_cases hl : j < j'
        · rw [if_neg hjj, if_pos hl, lookupParam, if_neg hij]
        · rw [if_neg hjj, if_neg hl]
          by_cases hij' : i = j'
          · subst hij'
            rw [lookupParam, if_pos rfl, lookupParam, if_pos rfl]
          · rw [lookupParam, if_neg hij', lookupParam, if_neg hij']
            exact ih (sorted_tail hs)

/-! ### Successor -/

/-- Successor of a canonical form: every part shifts up by one, and the
constant is re-absorbed (a level raised past an existing offset does
not survive as a constant). -/
def succNF (nf : LevelNF) : LevelNF :=
  let ps := nf.params.map fun (i, k) => (i, k + 1)
  let c := nf.constPart + 1
  ⟨if c ≤ supOffsets ps then 0 else c, ps⟩

/-- The successor unfolded at a concrete record. -/
theorem succNF_eq (c : Nat) (ps : List (Nat × Nat)) :
    succNF ⟨c, ps⟩ =
      ⟨if c + 1 ≤ supOffsets (ps.map fun (i, k) => (i, k + 1))
        then 0 else c + 1, ps.map fun (i, k) => (i, k + 1)⟩ :=
  rfl

/-- The `+ 1`-shifted maximum identity. -/
theorem succ_max_succ' (a b : Nat) :
    max (a + 1) (b + 1) = max a b + 1 := by
  have h := Nat.succ_max_succ a b
  simp only [Nat.succ_eq_add_one] at h
  exact h

/-- Semantics of the parameter map, with an arbitrary outer constant. -/
theorem eval_map_succ_const (v : Nat → Nat) :
    ∀ (c : Nat) (ps : List (Nat × Nat)),
      max (c + 1) (eval v ⟨0, ps.map fun (i, k) => (i, k + 1)⟩) =
        eval v ⟨c, ps⟩ + 1
  | c, [] => by
      show max (c + 1) (eval v ⟨0, []⟩) = eval v ⟨c, []⟩ + 1
      rw [eval_nil, Nat.max_eq_left (Nat.zero_le _), eval_nil]
  | c, b :: rest => by
      obtain ⟨j, l⟩ := b
      have hrec := eval_map_succ_const v c rest
      rw [List.map_cons, eval_cons (c := 0), ← Nat.max_assoc, hrec,
        show l + 1 + v j = (l + v j) + 1 from by omega,
        show eval v ⟨c, (j, l) :: rest⟩ =
          max (eval v ⟨c, rest⟩) (l + v j) from eval_cons v c j l rest,
        succ_max_succ']

/-- Semantic correctness of the successor. -/
theorem eval_succNF (v : Nat → Nat) (nf : LevelNF) :
    eval v (succNF nf) = eval v nf + 1 := by
  obtain ⟨c, ps⟩ := nf
  have hAbs := eval_absorb v (c + 1) (ps.map fun (i, k) => (i, k + 1))
  rw [succNF_eq, hAbs]
  exact eval_map_succ_const v c ps

/-- Keys are untouched by the successor shift. -/
theorem lookupParam_map_succ {ps : List (Nat × Nat)} {i k : Nat} :
    lookupParam (ps.map fun (j, l) => (j, l + 1)) i = some k ↔
      lookupParam ps i = some (k - 1) ∧ k ≠ 0 := by
  induction ps with
  | nil =>
      show lookupParam ([] : List (Nat × Nat)) i = some k ↔
        lookupParam [] i = some (k - 1) ∧ k ≠ 0
      constructor
      · intro h
        rw [lookupParam] at h
        exact absurd h.symm (Option.some_ne_none k)
      · intro h
        rw [lookupParam] at h
        exact absurd h.1.symm (Option.some_ne_none (k - 1))
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      rw [List.map_cons]
      simp only [lookupParam]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, if_pos rfl]
        constructor
        · intro h
          rw [Option.some.injEq] at h
          subst k
          rw [Option.some.injEq]
          exact ⟨Nat.add_sub_cancel_right l 1, by
            rw [← Nat.succ_eq_add_one]
            exact Nat.succ_ne_zero l⟩
        · intro h
          rw [Option.some.injEq]
          rw [Option.some.injEq] at h
          cases k with
          | zero => exact False.elim (h.2 rfl)
          | succ k =>
              simp only [Nat.add_sub_cancel_right] at h
              exact congrArg (· + 1) h.1
      · rw [if_neg hij, if_neg hij]
        exact ih

/-- `succNF` preserves well-formedness. -/
theorem wf_succNF {nf : LevelNF} (hwf : WF nf) : WF (succNF nf) := by
  obtain ⟨hsort, hdom⟩ := hwf
  obtain ⟨c, ps⟩ := nf
  show WF (succNF ⟨c, ps⟩)
  constructor
  · show Sorted ((⟨c, ps⟩ : LevelNF).succNF).params
    unfold succNF
    rw [Sorted, List.pairwise_map]
    exact hsort
  · intro i k hk
    show (⟨c, ps⟩ : LevelNF).succNF.constPart = 0 ∨
      k < (⟨c, ps⟩ : LevelNF).succNF.constPart
    have hk' : lookupParam ps i = some (k - 1) ∧ k ≠ 0 :=
      lookupParam_map_succ.mp hk
    obtain ⟨hSome, hNe⟩ := hk'
    by_cases hAbs : c + 1 ≤
        supOffsets (ps.map fun (i, k) => (i, k + 1))
    · left
      rw [succNF_eq, if_pos hAbs]
    · right
      have hSup : k ≤ supOffsets (ps.map fun (i, k) => (i, k + 1)) :=
        supOffsets_ge_of_lookup hk
      obtain h | h := hdom i (k - 1) hSome
      · have h0 : c = 0 := h
        exact absurd (by omega : c + 1 ≤
            supOffsets (ps.map fun (i, k) => (i, k + 1))) hAbs
      · have h' : k - 1 < c := h
        rw [succNF_eq, if_neg hAbs]
        simp only
        omega

/-! ### Merge and normalization -/

/-- Merge of two canonical forms: fold-insert the atoms, absorb the
constant if it is dominated by some surviving offset. -/
def mergeNF (nf₁ nf₂ : LevelNF) : LevelNF :=
  let params := nf₁.params.foldl
    (fun acc (ik : Nat × Nat) => insertParam ik.1 ik.2 acc) nf₂.params
  let c := Nat.max nf₁.constPart nf₂.constPart
  ⟨if c ≤ supOffsets params then 0 else c, params⟩

theorem eval_foldl_insert (v : Nat → Nat) (c : Nat) :
    ∀ (l₂ l₁ : List (Nat × Nat)),
      eval v ⟨c, l₁.foldl
          (fun acc (ik : Nat × Nat) => insertParam ik.1 ik.2 acc) l₂⟩ =
        max (eval v ⟨c, l₂⟩) (eval v ⟨0, l₁⟩)
  | l₂, [] => by
      rw [List.foldl_nil, eval_nil,
        Nat.max_eq_left (Nat.zero_le (eval v ⟨c, l₂⟩))]
  | l₂, b :: rest => by
      simp only [List.foldl_cons]
      rw [eval_foldl_insert v c (insertParam b.1 b.2 l₂) rest,
        eval_insert]
      have hb : eval v ⟨0, b :: rest⟩ =
          max (eval v ⟨0, rest⟩) (b.2 + v b.1) := eval_cons v 0 _ _ _
      rw [hb, Nat.max_assoc (eval v ⟨c, l₂⟩) (b.2 + v b.1)
        (eval v ⟨0, rest⟩), Nat.max_comm (b.2 + v b.1)
        (eval v ⟨0, rest⟩)]

/-- The four-fold `max` shuffle used at the end of the merge. -/
theorem max4_diag (a b c d : Nat) :
    max (max a b) (max c d) = max (max a d) (max b c) := by
  have le1 : a ≤ max (max a d) (max b c) :=
    Nat.le_trans (Nat.le_max_left a d) (Nat.le_max_left _ _)
  have le2 : b ≤ max (max a d) (max b c) :=
    Nat.le_trans (Nat.le_max_left b c) (Nat.le_max_right _ _)
  have le3 : c ≤ max (max a d) (max b c) :=
    Nat.le_trans (Nat.le_max_right b c) (Nat.le_max_right _ _)
  have le4 : d ≤ max (max a d) (max b c) :=
    Nat.le_trans (Nat.le_max_right a d) (Nat.le_max_left _ _)
  apply Nat.le_antisymm
  · exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨le1, le2⟩,
      Nat.max_le.mpr ⟨le3, le4⟩⟩
  · have ge1 : a ≤ max (max a b) (max c d) :=
      Nat.le_trans (Nat.le_max_left a b) (Nat.le_max_left _ _)
    have ge2 : b ≤ max (max a b) (max c d) :=
      Nat.le_trans (Nat.le_max_right a b) (Nat.le_max_left _ _)
    have ge3 : c ≤ max (max a b) (max c d) :=
      Nat.le_trans (Nat.le_max_left c d) (Nat.le_max_right _ _)
    have ge4 : d ≤ max (max a b) (max c d) :=
      Nat.le_trans (Nat.le_max_right c d) (Nat.le_max_right _ _)
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨ge1, ge4⟩,
      Nat.max_le.mpr ⟨ge2, ge3⟩⟩

/-- Semantic correctness of the merge. -/
theorem eval_mergeNF (v : Nat → Nat) (nf₁ nf₂ : LevelNF) :
    eval v (mergeNF nf₁ nf₂) =
      max (eval v nf₁) (eval v nf₂) := by
  obtain ⟨c₁, p₁⟩ := nf₁
  obtain ⟨c₂, p₂⟩ := nf₂
  show eval v (mergeNF ⟨c₁, p₁⟩ ⟨c₂, p₂⟩) = _
  unfold mergeNF
  rw [eval_absorb, eval_foldl_insert]
  rw [show eval v ⟨c₁, p₁⟩ = max c₁ (eval v ⟨0, p₁⟩) from
      eval_constPart v c₁ p₁,
    show eval v ⟨c₂, p₂⟩ = max c₂ (eval v ⟨0, p₂⟩) from
      eval_constPart v c₂ p₂]
  exact max4_diag c₁ c₂ (eval v ⟨0, p₂⟩) (eval v ⟨0, p₁⟩)

/-- The canonicalizer: every level expression has a normal form. -/
def normalize : LevelExpr → LevelNF
  | .const c => ⟨c, []⟩
  | .param i => ⟨0, [(i, 0)]⟩
  | .succ e => succNF (normalize e)
  | .max e₁ e₂ => mergeNF (normalize e₁) (normalize e₂)

/-- **Soundness of canonicalization**: normalization preserves the
denotation under every valuation. -/
theorem eval_normalize (v : Nat → Nat) (e : LevelExpr) :
    eval v (normalize e) = LevelExpr.eval v e := by
  induction e with
  | const c => rfl
  | param i =>
      show eval v ⟨(0 : Nat), [(i, 0)]⟩ = v i
      rw [eval_cons, eval_nil, Nat.zero_add (v i),
        Nat.max_eq_right (Nat.zero_le _)]
  | succ e ih =>
      rw [normalize, LevelExpr.eval, eval_succNF, ih]
  | max e₁ e₂ ih₁ ih₂ =>
      rw [normalize, LevelExpr.eval, eval_mergeNF, ih₁, ih₂]

/-! ### Well-formedness of normalization -/

/-- Merging preserves sortedness. -/
theorem sorted_foldl_insert {l₂ : List (Nat × Nat)}
    (hs : Sorted l₂) :
    ∀ l₁ : List (Nat × Nat),
      Sorted (l₁.foldl (fun acc (ik : Nat × Nat) =>
        insertParam ik.1 ik.2 acc) l₂)
  | [] => hs
  | _b :: rest => sorted_foldl_insert (sorted_insert hs) rest

/-- The merge unfolded at concrete records. -/
theorem mergeNF_eq (c₁ c₂ : Nat) (p₁ p₂ : List (Nat × Nat)) :
    mergeNF ⟨c₁, p₁⟩ ⟨c₂, p₂⟩ =
      ⟨if max c₁ c₂ ≤ supOffsets
          (p₁.foldl (fun acc (ik : Nat × Nat) =>
            insertParam ik.1 ik.2 acc) p₂)
        then 0 else max c₁ c₂,
        p₁.foldl (fun acc (ik : Nat × Nat) =>
          insertParam ik.1 ik.2 acc) p₂⟩ :=
  rfl

/-- Merging preserves well-formedness. -/
theorem wf_mergeNF {nf₁ nf₂ : LevelNF}
    (h₁ : WF nf₁) (h₂ : WF nf₂) : WF (mergeNF nf₁ nf₂) := by
  obtain ⟨c₁, p₁⟩ := nf₁
  obtain ⟨c₂, p₂⟩ := nf₂
  show WF (mergeNF ⟨c₁, p₁⟩ ⟨c₂, p₂⟩)
  rw [mergeNF_eq]
  refine ⟨sorted_foldl_insert h₂.1 p₁, ?_⟩
  intro i k hk
  by_cases hAbs : max c₁ c₂ ≤ supOffsets
      (p₁.foldl (fun acc (ik : Nat × Nat) =>
        insertParam ik.1 ik.2 acc) p₂)
  · rw [if_pos hAbs]
    exact .inl rfl
  · rw [if_neg hAbs]
    right
    show k < max c₁ c₂
    exact lt_of_le_of_lt (supOffsets_ge_of_lookup hk)
      (Nat.lt_of_not_le hAbs)

/-- Normalization lands in well-formed canonical forms. -/
theorem wf_normalize (e : LevelExpr) : WF (normalize e) := by
  induction e with
  | const c =>
      show WF ⟨c, []⟩
      refine ⟨(by exact List.Pairwise.nil), ?_⟩
      intro i k hk
      simp only [lookupParam] at hk
      exact absurd hk.symm (Option.some_ne_none k)
  | param i =>
      show WF ⟨0, [(i, 0)]⟩
      refine ⟨by exact List.pairwise_singleton _ _, ?_⟩
      intro j k hk
      exact .inl rfl
  | succ e ih => exact wf_succNF ih
  | max e₁ e₂ ih₁ ih₂ => exact wf_mergeNF ih₁ ih₂

/-! ### The gadget valuations and uniqueness -/

/-- An atom found in the list contributes at least its
offset-plus-valuation. -/
theorem atom_le_eval {ps : List (Nat × Nat)} {i k : Nat} (v : Nat → Nat)
    (h : lookupParam ps i = some k) :
    ∀ (c : Nat), k + v i ≤ eval v ⟨c, ps⟩ := by
  intro c
  induction ps generalizing c with
  | nil => simp [lookupParam] at h
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      simp only [lookupParam] at h
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl] at h
        simp at h
        rw [eval_cons, h]
        exact Nat.le_max_right _ _
      · rw [if_neg hij] at h
        rw [eval_cons]
        exact Nat.le_trans (ih h c) (Nat.le_max_left _ _)

/-- The constant of a canonical form underlies its evaluation. -/
theorem const_le_eval (v : Nat → Nat) :
    ∀ (c : Nat) (ps : List (Nat × Nat)), c ≤ eval v ⟨c, ps⟩
  | c, [] => Nat.le_refl c
  | c, b :: rest => by
      rw [eval_cons]
      exact Nat.le_trans (const_le_eval v c rest) (Nat.le_max_left _ _)

/-- If the constant and every atom's contribution fit under a bound,
the evaluation fits too. -/
theorem eval_le_of_bounds (v : Nat → Nat) {ps : List (Nat × Nat)}
    {B : Nat}
    (hb : ∀ x : Nat × Nat, x ∈ ps → x.2 + v x.1 ≤ B) :
    ∀ (c : Nat), c ≤ B → eval v ⟨c, ps⟩ ≤ B
  | c, hc => by
      induction ps generalizing c with
      | nil => simpa using hc
      | cons b rest ih =>
          obtain ⟨j, l⟩ := b
          rw [eval_cons]
          apply Nat.max_le.mpr
          exact ⟨ih (fun x hx => hb x (List.Mem.tail (j, l) hx)) c hc,
            hb (j, l) (List.Mem.head rest)⟩

/-- The zero valuation sees constants and offsets only. -/
theorem eval_zero : ∀ (c : Nat) (ps : List (Nat × Nat)),
    eval (fun _ => 0) ⟨c, ps⟩ = max c (supOffsets ps)
  | c, [] => by
      simp [supOffsets]
  | c, b :: rest => by
      obtain ⟨j, l⟩ := b
      rw [eval_cons, supOffsets_cons, eval_zero c rest,
        show l + (fun _ => 0) j = l from rfl, Nat.max_assoc]

/-- The single-parameter valuation over an absent parameter sees only
constants and offsets. -/
theorem eval_single_of_none {ps : List (Nat × Nat)} {i : Nat}
    (h : lookupParam ps i = none) :
    ∀ (c M : Nat),
      eval (fun j => if j = i then M else 0) ⟨c, ps⟩ =
        max c (supOffsets ps) := by
  intro c M
  induction ps generalizing c with
  | nil => simp [supOffsets]
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      simp only [lookupParam] at h
      have hij : i ≠ j := by
        intro heq
        rw [heq, if_pos rfl] at h
        simp at h
      have hrest : lookupParam rest i = none := by
        rw [if_neg hij] at h
        exact h
      rw [eval_cons,
        show (if j = i then M else 0) = (0 : Nat) from
          if_neg (Ne.symm hij),
        Nat.add_zero l, ih hrest,
        supOffsets_cons, Nat.max_assoc]

/-- Every member's offset lies under the supremum. -/
theorem supOffsets_ge_of_mem {ps : List (Nat × Nat)} {j l : Nat}
    (hx : (j, l) ∈ ps) : l ≤ supOffsets ps := by
  induction ps with
  | nil => exact absurd hx List.not_mem_nil
  | cons b rest ih =>
      obtain ⟨j', l'⟩ := b
      rw [supOffsets_cons]
      cases hx with
      | head => exact Nat.le_max_right _ _
      | tail _ hmem =>
          exact Nat.le_trans (ih hmem) (Nat.le_max_left _ _)

/-- In a sorted list, a member under the key of a lookup hits the same
offset. -/
theorem eq_of_mem_lookupParam_sorted {ps : List (Nat × Nat)} {i l : Nat}
    (hs : Sorted ps) (hx : (i, l) ∈ ps) {k : Nat}
    (h : lookupParam ps i = some k) : l = k := by
  induction ps with
  | nil => exact absurd hx List.not_mem_nil
  | cons b rest ih =>
      obtain ⟨j, l'⟩ := b
      cases hx with
      | head =>
          rw [lookupParam, if_pos rfl] at h
          exact Option.some.inj h
      | tail _ hmem =>
          have hNeq : i ≠ j := by
            have hlt := (List.pairwise_cons.mp hs).1 (i, l) hmem
            exact Nat.ne_of_gt hlt
          exact ih (sorted_tail hs) hmem
            (by rwa [lookupParam, if_neg hNeq] at h)

/-- The single-parameter valuation over a present parameter with a
large enough value sees exactly `offset + M`. -/
theorem eval_single_of_some {ps : List (Nat × Nat)} {i k : Nat}
    (hs : Sorted ps) (h : lookupParam ps i = some k) (M : Nat)
    (hM : supOffsets ps ≤ M) (c : Nat) :
    eval (fun j => if j = i then M else 0) ⟨c, ps⟩ = max c (k + M) := by
  apply Nat.le_antisymm
  · refine eval_le_of_bounds (fun j => if j = i then M else 0) ?_ c
      (Nat.le_max_left c (k + M))
    intro x hx
    obtain ⟨j, l⟩ := x
    show l + (if j = i then M else 0) ≤ max c (k + M)
    by_cases hij : j = i
    · subst hij
      have hlk : l = k := eq_of_mem_lookupParam_sorted hs hx h
      rw [hlk, if_pos rfl]
      exact Nat.le_max_right _ _
    · rw [if_neg hij, Nat.add_zero l]
      exact Nat.le_trans (Nat.le_trans (supOffsets_ge_of_mem hx) hM)
        (Nat.le_trans (by omega : M ≤ k + M) (Nat.le_max_right _ _))
  · have hAtom : k + M ≤
        eval (fun j => if j = i then M else 0) ⟨c, ps⟩ := by
      have h' := atom_le_eval (fun j => if j = i then M else 0) h c
      rwa [if_pos rfl] at h'
    exact Nat.max_le.mpr ⟨const_le_eval _ c ps, hAtom⟩

/-! ### Decidable semantic order

Semantic order is pointwise order under every valuation.  It is not
implemented by quantifying over valuations: canonical forms admit a
finite comparison.  Every atom on the left must occur on the right
with at least the same offset, while the left constant need only fit
under what the right side already exposes at the zero valuation.

The completeness proof below is constructive.  When the finite test
fails it returns one of the same gadget valuations used by the proof:
the zero valuation for a constant failure, or a sufficiently large
single-parameter valuation for an atom failure. -/

/-- A left atom is bounded by the right atom with the same parameter. -/
def AtomLe (right : List (Nat × Nat)) (ik : Nat × Nat) : Prop :=
  match lookupParam right ik.1 with
  | none => False
  | some rightOffset => ik.2 ≤ rightOffset

/-- Atom comparison is decidable by one lookup and one natural-number
comparison. -/
instance instDecidableAtomLe (right : List (Nat × Nat)) :
    DecidablePred (AtomLe right) := fun ik => by
  unfold AtomLe
  cases lookupParam right ik.1 <;> infer_instance

/-- Every atom in `left` is bounded by its same-parameter atom in
`right`.  The membership formulation keeps the test finite. -/
def ParamsLe (left right : List (Nat × Nat)) : Prop :=
  ∀ ik ∈ left, AtomLe right ik

/-- The computable order criterion for canonical level forms. -/
def CanonicalLe (left right : LevelNF) : Prop :=
  left.constPart ≤ max right.constPart (supOffsets right.params) ∧
    ParamsLe left.params right.params

/-- The canonical criterion is decidable by finite list traversal and
natural-number comparison. -/
instance instDecidableCanonicalLe (left right : LevelNF) :
    Decidable (CanonicalLe left right) := by
  unfold CanonicalLe ParamsLe
  infer_instance

/-- Membership in a sorted atom list determines a successful lookup. -/
theorem lookupParam_eq_some_of_mem {ps : List (Nat × Nat)} {i k : Nat}
    (hs : Sorted ps) (hx : (i, k) ∈ ps) :
    lookupParam ps i = some k := by
  induction ps with
  | nil => exact absurd hx List.not_mem_nil
  | cons b rest ih =>
      obtain ⟨j, l⟩ := b
      cases hx with
      | head => rw [lookupParam, if_pos rfl]
      | tail _ hmem =>
          have hij : i ≠ j := by
            have hlt := (List.pairwise_cons.mp hs).1 (i, k) hmem
            exact Nat.ne_of_gt hlt
          rw [lookupParam, if_neg hij]
          exact ih (sorted_tail hs) hmem

/-- Evaluation is monotone from the zero valuation to any valuation. -/
theorem eval_zero_le_eval (v : Nat → Nat) (c : Nat)
    (ps : List (Nat × Nat)) :
    eval (fun _ => 0) ⟨c, ps⟩ ≤ eval v ⟨c, ps⟩ := by
  rw [eval_zero, eval_constPart]
  exact max_le_max (Nat.le_refl c) (eval_ge_sup v ps)

/-- A finite parameter comparison failure has a concrete offending
atom in the left list. -/
theorem exists_mem_not_atomLe {left right : List (Nat × Nat)}
    (h : ¬ ParamsLe left right) :
    ∃ ik ∈ left, ¬ AtomLe right ik := by
  induction left with
  | nil =>
      exfalso
      apply h
      intro ik hik
      exact absurd hik List.not_mem_nil
  | cons a rest ih =>
      by_cases ha : AtomLe right a
      · have hrest : ¬ ParamsLe rest right := by
          intro hr
          apply h
          intro ik hik
          rcases List.mem_cons.mp hik with rfl | hmem
          · exact ha
          · exact hr ik hmem
        obtain ⟨ik, hik, hbad⟩ := ih hrest
        exact ⟨ik, List.Mem.tail a hik, hbad⟩
      · exact ⟨a, List.Mem.head rest, ha⟩

/-- **Constructive separation.** If the finite canonical comparison
fails, a concrete valuation makes the left evaluation strictly larger
than the right evaluation. -/
theorem exists_separating_valuation_of_not_canonicalLe
    {left right : LevelNF} (hLeft : WF left) (hRight : WF right)
    (hNot : ¬ CanonicalLe left right) :
    ∃ v, eval v right < eval v left := by
  obtain ⟨c₁, p₁⟩ := left
  obtain ⟨c₂, p₂⟩ := right
  by_cases hConst : c₁ ≤ max c₂ (supOffsets p₂)
  · have hParams : ¬ ParamsLe p₁ p₂ := by
      intro hp
      exact hNot ⟨hConst, hp⟩
    obtain ⟨⟨i, k₁⟩, hMem, hAtom⟩ :=
      exists_mem_not_atomLe hParams
    have hLookupLeft : lookupParam p₁ i = some k₁ :=
      lookupParam_eq_some_of_mem hLeft.1 hMem
    let M := supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1
    have hM₁ : supOffsets p₁ ≤ M := by
      dsimp [M]
      omega
    have hM₂ : supOffsets p₂ ≤ M := by
      dsimp [M]
      omega
    cases hLookupRight : lookupParam p₂ i with
    | none =>
        refine ⟨(fun j => if j = i then M else 0), ?_⟩
        rw [eval_single_of_none hLookupRight,
          eval_single_of_some hLeft.1 hLookupLeft M hM₁]
        have hRightBound : max c₂ (supOffsets p₂) ≤
            c₂ + supOffsets p₂ :=
          Nat.max_le.mpr
            ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
        have hLeftBound : M ≤ max c₁ (k₁ + M) :=
          Nat.le_trans (by omega : M ≤ k₁ + M)
            (Nat.le_max_right _ _)
        have hLarge : c₂ + supOffsets p₂ < M := by
          dsimp [M]
          omega
        omega
    | some k₂ =>
        have hOffset : k₂ < k₁ := by
          unfold AtomLe at hAtom
          rw [hLookupRight] at hAtom
          exact Nat.lt_of_not_ge hAtom
        refine ⟨(fun j => if j = i then M else 0), ?_⟩
        rw [eval_single_of_some hRight.1 hLookupRight M hM₂,
          eval_single_of_some hLeft.1 hLookupLeft M hM₁]
        have hc₂ : c₂ ≤ k₂ + M := by
          dsimp [M]
          omega
        rw [Nat.max_eq_right hc₂]
        have hLeftBound : k₁ + M ≤ max c₁ (k₁ + M) :=
          Nat.le_max_right _ _
        omega
  · refine ⟨(fun _ => 0), ?_⟩
    rw [eval_zero, eval_zero]
    have hc₁ : c₁ ≤ max c₁ (supOffsets p₁) := Nat.le_max_left _ _
    omega

/-- Soundness of the finite order criterion. -/
theorem eval_le_of_canonicalLe {left right : LevelNF}
    (h : CanonicalLe left right) (v : Nat → Nat) :
    eval v left ≤ eval v right := by
  obtain ⟨c₁, p₁⟩ := left
  obtain ⟨c₂, p₂⟩ := right
  refine eval_le_of_bounds v ?_ c₁ ?_
  · intro ik hMem
    obtain ⟨i, k₁⟩ := ik
    have hAtom := h.2 (i, k₁) hMem
    unfold AtomLe at hAtom
    cases hLookup : lookupParam p₂ i with
    | none =>
        rw [hLookup] at hAtom
        exact False.elim hAtom
    | some k₂ =>
        rw [hLookup] at hAtom
        exact Nat.le_trans (Nat.add_le_add_right hAtom (v i))
          (atom_le_eval v hLookup c₂)
  · calc
      c₁ ≤ max c₂ (supOffsets p₂) := h.1
      _ = eval (fun _ => 0) ⟨c₂, p₂⟩ := (eval_zero c₂ p₂).symm
      _ ≤ eval v ⟨c₂, p₂⟩ := eval_zero_le_eval v c₂ p₂

/-- Completeness of the finite order criterion. -/
theorem canonicalLe_of_eval_le {left right : LevelNF}
    (hLeft : WF left) (hRight : WF right)
    (hEv : ∀ v, eval v left ≤ eval v right) :
    CanonicalLe left right := by
  by_contra hNot
  obtain ⟨v, hSep⟩ :=
    exists_separating_valuation_of_not_canonicalLe hLeft hRight hNot
  exact (Nat.not_lt_of_ge (hEv v)) hSep

/-- **Exact order theorem for canonical forms.** -/
theorem canonicalLe_iff_eval_le {left right : LevelNF}
    (hLeft : WF left) (hRight : WF right) :
    CanonicalLe left right ↔ ∀ v, eval v left ≤ eval v right :=
  ⟨fun h v => eval_le_of_canonicalLe h v,
    canonicalLe_of_eval_le hLeft hRight⟩

/-- Sorted atom lists with the same lookup function are equal. -/
theorem params_eq_of_lookup_eq :
    ∀ {p₁ p₂ : List (Nat × Nat)}, Sorted p₁ → Sorted p₂ →
      (∀ i, lookupParam p₁ i = lookupParam p₂ i) → p₁ = p₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by
      have hb := h b.1
      rw [lookupParam] at hb
      rw [lookupParam, if_pos rfl] at hb
      exact absurd hb.symm (Option.some_ne_none b.2)
  | b :: _, [], _, _, h => by
      have hb := h b.1
      rw [lookupParam] at hb
      rw [lookupParam, if_pos rfl] at hb
      exact absurd hb (Option.some_ne_none b.2)
  | b₁ :: rest₁, b₂ :: rest₂, hs₁, hs₂, h => by
      obtain ⟨a₁, k₁⟩ := b₁
      obtain ⟨a₂, k₂⟩ := b₂
      have hb1 := h a₁
      simp only [lookupParam] at hb1
      by_cases hEq : a₁ = a₂
      · subst hEq
        rw [if_pos rfl] at hb1
        simp at hb1
        subst hb1
        exact congrArg ((a₁, k₁) :: ·)
          (params_eq_of_lookup_eq (sorted_tail hs₁) (sorted_tail hs₂)
            (fun i => by
              have hi := h i
              by_cases hiEq : i = a₁
              · subst hiEq
                rw [lookupParam_none_of_forall_lt (ps := rest₁)
                    (fun x hx => (List.pairwise_cons.mp hs₁).1 x hx),
                  lookupParam_none_of_forall_lt (ps := rest₂)
                    (fun x hx => (List.pairwise_cons.mp hs₂).1 x hx)]
              · simp only [lookupParam, if_neg hiEq] at hi
                exact hi))
      · rw [if_neg hEq] at hb1
        exfalso
        by_cases hlt : a₂ < a₁
        · have hNoneFull : lookupParam ((a₁, k₁) :: rest₁) a₂ =
              none :=
            lookupParam_none_of_sorted_head_lt hs₁ hlt
          have hb2 := h a₂
          rw [hNoneFull] at hb2
          simp [lookupParam] at hb2
        · have hNoneFull : lookupParam ((a₂, k₂) :: rest₂) a₁ =
              none :=
            lookupParam_none_of_sorted_head_lt hs₂ (by omega)
          rw [lookupParam, if_neg hEq] at hNoneFull
          rw [hNoneFull] at hb1
          simp at hb1

/-- **Completeness premise**: evaluations equal at the gadget
valuations force equal parameter offsets. -/
theorem lookupParam_eq_of_eval_eq {nf₁ nf₂ : LevelNF}
    (h₁ : WF nf₁) (h₂ : WF nf₂)
    (hEv : ∀ v, eval v nf₁ = eval v nf₂) (i : Nat) :
    lookupParam nf₁.params i = lookupParam nf₂.params i := by
  obtain ⟨c₁, p₁⟩ := nf₁
  obtain ⟨c₂, p₂⟩ := nf₂
  cases hL : lookupParam p₁ i with
  | none =>
      cases hR : lookupParam p₂ i with
      | none => rfl
      | some k₂ =>
          exfalso
          have hM : supOffsets p₂ ≤
              supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1 := by omega
          have hEvM := hEv (fun j => if j = i then
              supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1 else 0)
          rw [eval_single_of_none hL,
            eval_single_of_some h₂.1 hR _ hM] at hEvM
          have hLe : max c₁ (supOffsets p₁) ≤
              c₁ + supOffsets p₁ :=
            Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
          have hGe : k₂ +
              (supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1) ≤
              max c₂ (k₂ + (supOffsets p₁ + supOffsets p₂ + c₁ + c₂ +
                1)) := Nat.le_max_right _ _
          omega
  | some k₁ =>
      cases hR : lookupParam p₂ i with
      | none =>
          exfalso
          have hM : supOffsets p₁ ≤
              supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1 := by omega
          have hEvM := hEv (fun j => if j = i then
              supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1 else 0)
          rw [eval_single_of_some h₁.1 hL _ hM,
            eval_single_of_none hR] at hEvM
          have hLe : max c₂ (supOffsets p₂) ≤
              c₂ + supOffsets p₂ :=
            Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
          have hGe : k₁ +
              (supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1) ≤
              max c₁ (k₁ + (supOffsets p₁ + supOffsets p₂ + c₁ + c₂ +
                1)) := Nat.le_max_right _ _
          omega
      | some k₂ =>
          have hM₁ : supOffsets p₁ ≤
              supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1 := by omega
          have hM₂ : supOffsets p₂ ≤
              supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1 := by omega
          have hEvM := hEv (fun j => if j = i then
              supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1 else 0)
          rw [eval_single_of_some h₁.1 hL _ hM₁,
            eval_single_of_some h₂.1 hR _ hM₂,
            Nat.max_eq_right (by omega : c₁ ≤ k₁ +
              (supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1)),
            Nat.max_eq_right (by omega : c₂ ≤ k₂ +
              (supOffsets p₁ + supOffsets p₂ + c₁ + c₂ + 1))] at hEvM
          have hkk : k₁ = k₂ := by omega
          rw [hkk]

/-- **Canonical forms are unique.** Two well-formed canonical forms
that agree under every valuation are identical — this is what makes
`normalize`-comparison a *sound and complete* decision procedure for
level equality. -/
theorem unique_of_eval_eq {nf₁ nf₂ : LevelNF}
    (h₁ : WF nf₁) (h₂ : WF nf₂)
    (hEv : ∀ v, eval v nf₁ = eval v nf₂) : nf₁ = nf₂ := by
  have hParams : ∀ i, lookupParam nf₁.params i =
      lookupParam nf₂.params i :=
    fun i => lookupParam_eq_of_eval_eq h₁ h₂ hEv i
  obtain ⟨c₁, p₁⟩ := nf₁
  obtain ⟨c₂, p₂⟩ := nf₂
  have hPP : p₁ = p₂ :=
    params_eq_of_lookup_eq h₁.1 h₂.1 hParams
  subst hPP
  have hEv0 := hEv (fun _ => 0)
  rw [eval_zero, eval_zero] at hEv0
  have hCP : c₁ = c₂ := by
    by_cases hc₁ : c₁ = 0
    · subst hc₁
      by_cases hc₂ : c₂ = 0
      · subst hc₂
        rfl
      · exfalso
        have hlt : supOffsets p₁ < c₂ :=
          sup_lt_const_of_wf h₂.1 h₂.2 hc₂
        rw [Nat.max_eq_right (Nat.zero_le _),
          Nat.max_eq_left hlt.le] at hEv0
        omega
    · by_cases hc₂ : c₂ = 0
      · subst hc₂
        exfalso
        have hlt : supOffsets p₁ < c₁ :=
          sup_lt_const_of_wf h₁.1 h₁.2 ‹c₁ ≠ 0›
        rw [Nat.max_eq_left hlt.le,
          Nat.max_eq_right (Nat.zero_le _)] at hEv0
        omega
      · have hlt₁ : supOffsets p₁ < c₁ :=
          sup_lt_const_of_wf h₁.1 h₁.2 hc₁
        have hlt₂ : supOffsets p₁ < c₂ :=
          sup_lt_const_of_wf h₂.1 h₂.2 hc₂
        rw [Nat.max_eq_left hlt₁.le, Nat.max_eq_left hlt₂.le] at hEv0
        exact hEv0
  subst hCP
  rfl

/-! ### Decidability of the trust boundary -/

/-- Soundness, contrapositive form: equal normal forms evaluate
equally. -/
theorem eval_eq_of_normalize_eq {e₁ e₂ : LevelExpr}
    (h : normalize e₁ = normalize e₂) (v : Nat → Nat) :
    LevelExpr.eval v e₁ = LevelExpr.eval v e₂ := by
  rw [← eval_normalize v e₁, ← eval_normalize v e₂, h]

/-- **The decision theorem.**  Level equality under all valuations
is exactly equality of canonical forms — the canonicalizer is a
complete invariant. -/
theorem normalize_eq_iff (e₁ e₂ : LevelExpr) :
    normalize e₁ = normalize e₂ ↔
      ∀ v, LevelExpr.eval v e₁ = LevelExpr.eval v e₂ :=
  ⟨fun h v => eval_eq_of_normalize_eq h v, fun h =>
    unique_of_eval_eq (wf_normalize e₁) (wf_normalize e₂)
      (fun v => by rw [eval_normalize v e₁, eval_normalize v e₂, h])⟩

/-- **The trust boundary is decidable.**  Kernel conversion of
universe sorts never needs to evaluate language data: compare the
canonical forms. -/
instance decideLevelEq (e₁ e₂ : LevelExpr) :
    Decidable (∀ v, LevelExpr.eval v e₁ = LevelExpr.eval v e₂) :=
  decidable_of_iff _ (normalize_eq_iff e₁ e₂)

/-- **The order decision theorem.** Semantic order of level
expressions is exactly the finite order test on their normal forms. -/
theorem normalize_le_iff (e₁ e₂ : LevelExpr) :
    CanonicalLe (normalize e₁) (normalize e₂) ↔
      ∀ v, LevelExpr.eval v e₁ ≤ LevelExpr.eval v e₂ := by
  constructor
  · intro h v
    have hLe := eval_le_of_canonicalLe h v
    rwa [eval_normalize v e₁, eval_normalize v e₂] at hLe
  · intro h
    apply canonicalLe_of_eval_le (wf_normalize e₁) (wf_normalize e₂)
    intro v
    rw [eval_normalize v e₁, eval_normalize v e₂]
    exact h v

/-- Kernel cumulativity comparison is decidable without enumerating
valuations. -/
instance decideLevelLe (e₁ e₂ : LevelExpr) :
    Decidable (∀ v, LevelExpr.eval v e₁ ≤ LevelExpr.eval v e₂) :=
  decidable_of_iff _ (normalize_le_iff e₁ e₂)

/-- Refusing a semantic level comparison produces an explicit
valuation at which the alleged order is reversed. -/
theorem exists_level_separator_of_not_le {e₁ e₂ : LevelExpr}
    (hNot : ¬ ∀ v, LevelExpr.eval v e₁ ≤ LevelExpr.eval v e₂) :
    ∃ v, LevelExpr.eval v e₂ < LevelExpr.eval v e₁ := by
  have hCanonical : ¬ CanonicalLe (normalize e₁) (normalize e₂) := by
    intro h
    exact hNot ((normalize_le_iff e₁ e₂).mp h)
  obtain ⟨v, hSep⟩ :=
    exists_separating_valuation_of_not_canonicalLe
      (wf_normalize e₁) (wf_normalize e₂) hCanonical
  refine ⟨v, ?_⟩
  rwa [eval_normalize v e₂, eval_normalize v e₁] at hSep

/-- Semantic level order is stable under simultaneous substitution. -/
theorem level_le_subst {e₁ e₂ : LevelExpr}
    (h : ∀ v, LevelExpr.eval v e₁ ≤ LevelExpr.eval v e₂)
    (σ : Nat → LevelExpr) :
    ∀ v, LevelExpr.eval v (LevelExpr.subst σ e₁) ≤
      LevelExpr.eval v (LevelExpr.subst σ e₂) := by
  intro v
  rw [LevelExpr.eval_subst, LevelExpr.eval_subst]
  exact h (fun i => LevelExpr.eval v (σ i))

/-- Normal-form equality is a congruence for level substitution. -/
theorem normalize_subst_congr {e₁ e₂ : LevelExpr}
    (h : normalize e₁ = normalize e₂) (σ : Nat → LevelExpr) :
    normalize (LevelExpr.subst σ e₁) =
      normalize (LevelExpr.subst σ e₂) := by
  apply (normalize_eq_iff _ _).mpr
  intro v
  rw [LevelExpr.eval_subst, LevelExpr.eval_subst]
  exact eval_eq_of_normalize_eq h (fun i => LevelExpr.eval v (σ i))

/-- A worked positive example: `max (succ (param 0)) 2` and
`max 2 (succ (max 1 (param 0)))` denote the same level under every
valuation, and the kernel *computes* that answer. -/
example : ∀ v, LevelExpr.eval v
      (.max (.succ (.param 0)) (.const 2)) =
      LevelExpr.eval v
      (.max (.const 2) (.succ (.max (.const 1) (.param 0)))) := by
  decide

/-- A worked negative example: the two sides differ at the valuation
`0 ↦ 0` (`2 ≠ 3`), so equality is rightly refused. -/
example : (∀ v, LevelExpr.eval v
      (.max (.const 2) (.param 0)) =
      LevelExpr.eval v (.max (.const 3) (.param 0))) →
    False := by
  intro h
  have := h (fun _ => 0)
  simp [LevelExpr.eval] at this

/-- A positive cumulative example: each left contribution is bounded
by a right contribution with the same parameter. -/
example : ∀ v, LevelExpr.eval v
      (.max (.const 2) (.param 0)) ≤
      LevelExpr.eval v
      (.max (.const 3) (.succ (.param 0))) := by
  decide

/-- An offset failure is rejected by computation. -/
example : ¬ ∀ v, LevelExpr.eval v (.succ (.param 0)) ≤
    LevelExpr.eval v (.param 0) := by
  decide

/-- The zero valuation is a concrete separator for the preceding
offset failure. -/
example : LevelExpr.eval (fun _ => 0) (.param 0) <
    LevelExpr.eval (fun _ => 0) (.succ (.param 0)) := by
  decide

/-- A missing parameter is rejected; raising an unrelated parameter
cannot dominate it. -/
example : ¬ ∀ v, LevelExpr.eval v (.param 0) ≤
    LevelExpr.eval v (.param 1) := by
  decide

/-- A concrete separating valuation for the missing-parameter case. -/
example : LevelExpr.eval (fun i => if i = 0 then 1 else 0) (.param 1) <
    LevelExpr.eval (fun i => if i = 0 then 1 else 0) (.param 0) := by
  decide

end LevelNF

end Mettapedia.Languages.MeTTa.PureKernel.Universe
