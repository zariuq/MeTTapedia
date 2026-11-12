import Mettapedia.TypeTheory.KnowledgeUnderBinders

/-!
# Substitution at a frame with knowledge

A frame of the bubble calculus is a context together with a store of assumed equations.
`KnowledgeUnderBinders.TypedKnowing` types a term at such a frame, and under a binder the store
moves with the frame. This module proves that the judgment is carried by the maps of frames.

* **Weakening** (`typedKnowing_weaken`): a variable may be inserted anywhere in the context. The
  term, its type and the store are shifted past it.
* **Substitution** (`typedKnowing_subst`): a term typed at its own frame may be substituted for a
  variable. The context, the term, the type and the store are instantiated, and the result is
  typed at every frame that knows the instantiated store and what the substituted term needed.
* **A solution discharges the knowledge** (`typedKnowing_subst_solution`): when the instantiated
  equations are conversions of the bubble, the result is typed in the bubble, with no knowledge
  left.
* The substitution property of the global judgment (`hasType_subst`) is the case with no declared
  step and no knowledge.

An instantiation moves the knowledge; it does not rewrite the term. No transport term appears in
any of the statements.

The hypotheses are on the bubble's rules only: stability under substitution
(`BubbleConversion.SubstitutionStable`) and under shifting (`KnowledgeUnderBinders.ShiftStable`).

The first part is the algebra of shifting and substitution on the core that the statements need:
`shiftAt_shiftAt`, `substAt_shiftAt`, `substAt_substAt`, `shiftAt_substAt` and their iterated
forms.

## Controls

* `Controls.vec_converts_instantiated`, `Controls.vec_not_converted_by_stale_store`: a conversion
  at the frame that knows `n ≐ 0` is carried by `n := 1` to the frame that knows `1 ≐ 0`, and is
  not a conversion when the store is left as it was.
* `Controls.weakened_conversion`, `Controls.weakening_needs_shifted_store`: the same for the
  insertion of a variable.
* `Controls.constant_function_solved`: instantiating by the solution `n := 0` gives a typing of
  the global judgment.
* `Controls.non_solution_keeps_the_knowledge`: instantiating by `n := 1` gives a typing at the
  frame that knows `1 ≐ 0`, and that typing is not a typing of the global judgment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeSubstitution

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Shifting and substitution on variables -/

theorem shiftAt_bvar_lt {i k : Nat} (below : i < k) :
    shiftAt k (bvar i : Expr Base Const) = bvar i := by
  simp [shiftAt, below]

theorem shiftAt_bvar_ge {i k : Nat} (above : ¬ i < k) :
    shiftAt k (bvar i : Expr Base Const) = bvar (i + 1) := by
  simp [shiftAt, above]

theorem substAt_bvar_lt {i k : Nat} (s : Expr Base Const) (below : i < k) :
    substAt k s (bvar i) = bvar i := by
  simp [substAt, below]

theorem substAt_bvar_eq (k : Nat) (s : Expr Base Const) : substAt k s (bvar k) = shiftN k s := by
  simp [substAt]

theorem substAt_bvar_gt {i k : Nat} (s : Expr Base Const) (above : k < i) :
    substAt k s (bvar i) = bvar (i - 1) := by
  have notBelow : ¬ i < k := by omega
  have notEqual : ¬ i = k := by omega
  simp [substAt, notBelow, notEqual]

/-! ## The algebra of shifting and substitution -/

/-- Shifts commute: a shift at a lower cutoff moves a later shift one further out. -/
theorem shiftAt_shiftAt : ∀ (e : Expr Base Const) (c d : Nat), c ≤ d →
    shiftAt (d + 1) (shiftAt c e) = shiftAt c (shiftAt d e)
  | .bvar i, c, d, ordered => by
      by_cases belowC : i < c
      · rw [shiftAt_bvar_lt belowC, shiftAt_bvar_lt (by omega : i < d + 1),
          shiftAt_bvar_lt (by omega : i < d), shiftAt_bvar_lt belowC]
      · by_cases belowD : i < d
        · rw [shiftAt_bvar_ge belowC, shiftAt_bvar_lt (by omega : i + 1 < d + 1),
            shiftAt_bvar_lt belowD, shiftAt_bvar_ge belowC]
        · rw [shiftAt_bvar_ge belowC, shiftAt_bvar_ge (by omega : ¬ i + 1 < d + 1),
            shiftAt_bvar_ge belowD, shiftAt_bvar_ge (by omega : ¬ i + 1 < c)]
  | .univ, _, _, _ => rfl
  | .prop, _, _, _ => rfl
  | .base _, _, _, _ => rfl
  | .pi A B, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt A c d ordered, shiftAt_shiftAt B (c + 1) (d + 1) (by omega)]
  | .lam A b, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt A c d ordered, shiftAt_shiftAt b (c + 1) (d + 1) (by omega)]
  | .app f a, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt f c d ordered, shiftAt_shiftAt a c d ordered]
  | .const _ _, _, _, _ => rfl
  | .tyFam _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .and p q, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt p c d ordered, shiftAt_shiftAt q c d ordered]
  | .or p q, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt p c d ordered, shiftAt_shiftAt q c d ordered]
  | .imp p q, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt p c d ordered, shiftAt_shiftAt q c d ordered]
  | .not p, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt p c d ordered]
  | .eq a b, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt a c d ordered, shiftAt_shiftAt b c d ordered]
  | .all A b, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt A c d ordered, shiftAt_shiftAt b (c + 1) (d + 1) (by omega)]
  | .ex A b, c, d, ordered => by
      simp only [shiftAt]
      rw [shiftAt_shiftAt A c d ordered, shiftAt_shiftAt b (c + 1) (d + 1) (by omega)]

/-- Shifting an iterated shift below its height is one more iteration. -/
theorem shiftAt_shiftN (s : Expr Base Const) : ∀ (m c : Nat), c ≤ m →
    shiftAt c (shiftN m s) = shiftN (m + 1) s
  | 0, c, ordered => by
      obtain rfl : c = 0 := by omega
      rfl
  | m + 1, 0, _ => rfl
  | m + 1, c + 1, ordered => by
      show shiftAt (c + 1) (shiftAt 0 (shiftN m s)) = shiftAt 0 (shiftN (m + 1) s)
      rw [shiftAt_shiftAt (shiftN m s) 0 c (by omega), shiftAt_shiftN s m c (by omega)]

/-- A shift above `count` binders of a term shifted past them is the shifted shift. -/
theorem shiftAt_shiftN_above (t : Expr Base Const) (c : Nat) : ∀ count : Nat,
    shiftAt (c + count) (shiftN count t) = shiftN count (shiftAt c t)
  | 0 => rfl
  | count + 1 => by
      show shiftAt (c + count + 1) (shiftAt 0 (shiftN count t)) =
        shiftAt 0 (shiftN count (shiftAt c t))
      rw [shiftAt_shiftAt (shiftN count t) 0 (c + count) (by omega), shiftAt_shiftN_above t c count]

/-- Substitution passes a shift below it. -/
theorem substAt_shiftAt (s : Expr Base Const) : ∀ (t : Expr Base Const) (k c : Nat), c ≤ k →
    substAt (k + 1) s (shiftAt c t) = shiftAt c (substAt k s t)
  | .bvar i, k, c, ordered => by
      by_cases belowC : i < c
      · rw [shiftAt_bvar_lt belowC, substAt_bvar_lt s (by omega : i < k + 1),
          substAt_bvar_lt s (by omega : i < k), shiftAt_bvar_lt belowC]
      · rw [shiftAt_bvar_ge belowC]
        rcases Nat.lt_trichotomy i k with below | same | above
        · rw [substAt_bvar_lt s (by omega : i + 1 < k + 1), substAt_bvar_lt s below,
            shiftAt_bvar_ge belowC]
        · subst same
          rw [substAt_bvar_eq, substAt_bvar_eq, shiftAt_shiftN s i c ordered]
        · rw [substAt_bvar_gt s (by omega : k + 1 < i + 1), substAt_bvar_gt s above,
            shiftAt_bvar_ge (by omega : ¬ i - 1 < c)]
          exact congrArg bvar (by omega)
  | .univ, _, _, _ => rfl
  | .prop, _, _, _ => rfl
  | .base _, _, _, _ => rfl
  | .pi A B, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s A k c ordered, substAt_shiftAt s B (k + 1) (c + 1) (by omega)]
  | .lam A b, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s A k c ordered, substAt_shiftAt s b (k + 1) (c + 1) (by omega)]
  | .app f a, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s f k c ordered, substAt_shiftAt s a k c ordered]
  | .const _ _, _, _, _ => rfl
  | .tyFam _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .and p q, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s p k c ordered, substAt_shiftAt s q k c ordered]
  | .or p q, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s p k c ordered, substAt_shiftAt s q k c ordered]
  | .imp p q, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s p k c ordered, substAt_shiftAt s q k c ordered]
  | .not p, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s p k c ordered]
  | .eq a b, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s a k c ordered, substAt_shiftAt s b k c ordered]
  | .all A b, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s A k c ordered, substAt_shiftAt s b (k + 1) (c + 1) (by omega)]
  | .ex A b, k, c, ordered => by
      simp only [shiftAt, substAt]
      rw [substAt_shiftAt s A k c ordered, substAt_shiftAt s b (k + 1) (c + 1) (by omega)]

/-- Substitution under `depth` binders of a term shifted past them is the shifted substitution. -/
theorem substAt_shiftN (s t : Expr Base Const) (k : Nat) : ∀ depth : Nat,
    substAt (k + depth) s (shiftN depth t) = shiftN depth (substAt k s t)
  | 0 => rfl
  | depth + 1 => by
      show substAt (k + depth + 1) s (shiftAt 0 (shiftN depth t)) =
        shiftAt 0 (shiftN depth (substAt k s t))
      rw [substAt_shiftAt s (shiftN depth t) (k + depth) 0 (by omega), substAt_shiftN s t k depth]

/-- Substituting for a variable that a shift has just skipped gives the term back. -/
theorem substAt_shiftAt_cancel (s : Expr Base Const) : ∀ (e : Expr Base Const) (k : Nat),
    substAt k s (shiftAt k e) = e
  | .bvar i, k => by
      by_cases below : i < k
      · rw [shiftAt_bvar_lt below, substAt_bvar_lt s below]
      · rw [shiftAt_bvar_ge below, substAt_bvar_gt s (by omega : k < i + 1)]
        exact congrArg bvar (by omega)
  | .univ, _ => rfl
  | .prop, _ => rfl
  | .base _, _ => rfl
  | .pi A B, k => congrArg₂ Expr.pi (substAt_shiftAt_cancel s A k) (substAt_shiftAt_cancel s B (k + 1))
  | .lam A b, k => congrArg₂ Expr.lam (substAt_shiftAt_cancel s A k) (substAt_shiftAt_cancel s b (k + 1))
  | .app f a, k => congrArg₂ Expr.app (substAt_shiftAt_cancel s f k) (substAt_shiftAt_cancel s a k)
  | .const _ _, _ => rfl
  | .tyFam _, _ => rfl
  | .top, _ => rfl
  | .bot, _ => rfl
  | .and p q, k => congrArg₂ Expr.and (substAt_shiftAt_cancel s p k) (substAt_shiftAt_cancel s q k)
  | .or p q, k => congrArg₂ Expr.or (substAt_shiftAt_cancel s p k) (substAt_shiftAt_cancel s q k)
  | .imp p q, k => congrArg₂ Expr.imp (substAt_shiftAt_cancel s p k) (substAt_shiftAt_cancel s q k)
  | .not p, k => congrArg Expr.not (substAt_shiftAt_cancel s p k)
  | .eq a b, k => congrArg₂ Expr.eq (substAt_shiftAt_cancel s a k) (substAt_shiftAt_cancel s b k)
  | .all A b, k => congrArg₂ Expr.all (substAt_shiftAt_cancel s A k) (substAt_shiftAt_cancel s b (k + 1))
  | .ex A b, k => congrArg₂ Expr.ex (substAt_shiftAt_cancel s A k) (substAt_shiftAt_cancel s b (k + 1))

/-- Substituting below the height of an iterated shift removes one iteration. -/
theorem substAt_shiftN_cancel (s t : Expr Base Const) (k m : Nat) (ordered : k ≤ m) :
    substAt k s (shiftN (m + 1) t) = shiftN m t := by
  rw [← shiftAt_shiftN t m k ordered, substAt_shiftAt_cancel]

/-- Two substitutions commute, the outer one passing under the inner. -/
theorem substAt_substAt (s a : Expr Base Const) : ∀ (B : Expr Base Const) (k j : Nat),
    substAt (k + j) s (substAt j a B) = substAt j (substAt k s a) (substAt (k + j + 1) s B)
  | .bvar i, k, j => by
      rcases Nat.lt_trichotomy i j with below | same | above
      · rw [substAt_bvar_lt a below, substAt_bvar_lt s (by omega : i < k + j),
          substAt_bvar_lt s (by omega : i < k + j + 1), substAt_bvar_lt (substAt k s a) below]
      · subst same
        rw [substAt_bvar_eq, substAt_shiftN, substAt_bvar_lt s (by omega : i < k + i + 1),
          substAt_bvar_eq]
      · rw [substAt_bvar_gt a above]
        rcases Nat.lt_trichotomy i (k + j + 1) with inside | atSubstituted | beyond
        · rw [substAt_bvar_lt s (by omega : i - 1 < k + j), substAt_bvar_lt s inside,
            substAt_bvar_gt (substAt k s a) above]
        · subst atSubstituted
          rw [Nat.add_sub_cancel, substAt_bvar_eq, substAt_bvar_eq,
            substAt_shiftN_cancel (substAt k s a) s j (k + j) (by omega)]
        · rw [substAt_bvar_gt s (by omega : k + j < i - 1), substAt_bvar_gt s beyond,
            substAt_bvar_gt (substAt k s a) (by omega : j < i - 1)]
  | .univ, _, _ => rfl
  | .prop, _, _ => rfl
  | .base _, _, _ => rfl
  | .pi A B, k, j => congrArg₂ Expr.pi (substAt_substAt s a A k j) (substAt_substAt s a B k (j + 1))
  | .lam A b, k, j => congrArg₂ Expr.lam (substAt_substAt s a A k j) (substAt_substAt s a b k (j + 1))
  | .app f x, k, j => congrArg₂ Expr.app (substAt_substAt s a f k j) (substAt_substAt s a x k j)
  | .const _ _, _, _ => rfl
  | .tyFam _, _, _ => rfl
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .and p q, k, j => congrArg₂ Expr.and (substAt_substAt s a p k j) (substAt_substAt s a q k j)
  | .or p q, k, j => congrArg₂ Expr.or (substAt_substAt s a p k j) (substAt_substAt s a q k j)
  | .imp p q, k, j => congrArg₂ Expr.imp (substAt_substAt s a p k j) (substAt_substAt s a q k j)
  | .not p, k, j => congrArg Expr.not (substAt_substAt s a p k j)
  | .eq x y, k, j => congrArg₂ Expr.eq (substAt_substAt s a x k j) (substAt_substAt s a y k j)
  | .all A b, k, j => congrArg₂ Expr.all (substAt_substAt s a A k j) (substAt_substAt s a b k (j + 1))
  | .ex A b, k, j => congrArg₂ Expr.ex (substAt_substAt s a A k j) (substAt_substAt s a b k (j + 1))

/-- A shift passes a substitution below it. -/
theorem shiftAt_substAt (a : Expr Base Const) : ∀ (B : Expr Base Const) (c k : Nat),
    shiftAt (c + k) (substAt k a B) = substAt k (shiftAt c a) (shiftAt (c + k + 1) B)
  | .bvar i, c, k => by
      rcases Nat.lt_trichotomy i k with below | same | above
      · rw [substAt_bvar_lt a below, shiftAt_bvar_lt (by omega : i < c + k),
          shiftAt_bvar_lt (by omega : i < c + k + 1), substAt_bvar_lt (shiftAt c a) below]
      · subst same
        rw [substAt_bvar_eq, shiftAt_shiftN_above, shiftAt_bvar_lt (by omega : i < c + i + 1),
          substAt_bvar_eq]
      · rw [substAt_bvar_gt a above]
        by_cases inside : i < c + k + 1
        · rw [shiftAt_bvar_lt (by omega : i - 1 < c + k), shiftAt_bvar_lt inside,
            substAt_bvar_gt (shiftAt c a) above]
        · rw [shiftAt_bvar_ge (by omega : ¬ i - 1 < c + k), shiftAt_bvar_ge inside,
            substAt_bvar_gt (shiftAt c a) (by omega : k < i + 1)]
          exact congrArg bvar (by omega)
  | .univ, _, _ => rfl
  | .prop, _, _ => rfl
  | .base _, _, _ => rfl
  | .pi A B, c, k => congrArg₂ Expr.pi (shiftAt_substAt a A c k) (shiftAt_substAt a B c (k + 1))
  | .lam A b, c, k => congrArg₂ Expr.lam (shiftAt_substAt a A c k) (shiftAt_substAt a b c (k + 1))
  | .app f x, c, k => congrArg₂ Expr.app (shiftAt_substAt a f c k) (shiftAt_substAt a x c k)
  | .const _ _, _, _ => rfl
  | .tyFam _, _, _ => rfl
  | .top, _, _ => rfl
  | .bot, _, _ => rfl
  | .and p q, c, k => congrArg₂ Expr.and (shiftAt_substAt a p c k) (shiftAt_substAt a q c k)
  | .or p q, c, k => congrArg₂ Expr.or (shiftAt_substAt a p c k) (shiftAt_substAt a q c k)
  | .imp p q, c, k => congrArg₂ Expr.imp (shiftAt_substAt a p c k) (shiftAt_substAt a q c k)
  | .not p, c, k => congrArg Expr.not (shiftAt_substAt a p c k)
  | .eq x y, c, k => congrArg₂ Expr.eq (shiftAt_substAt a x c k) (shiftAt_substAt a y c k)
  | .all A b, c, k => congrArg₂ Expr.all (shiftAt_substAt a A c k) (shiftAt_substAt a b c (k + 1))
  | .ex A b, c, k => congrArg₂ Expr.ex (shiftAt_substAt a A c k) (shiftAt_substAt a b c (k + 1))

/-! ## The frame's knowledge moves with the maps of frames -/

/-- The frame's equations after a substitution for the variable at depth `k`. -/
def substStore (k : Nat) (s : Expr Base Const) (store : EquationStore (Expr Base Const)) :
    EquationStore (Expr Base Const) :=
  store.map fun e => (substAt k s e.1, substAt k s e.2)

/-- The frame's equations after the insertion of a variable at depth `cutoff`. -/
def shiftStoreAt (cutoff : Nat) (store : EquationStore (Expr Base Const)) :
    EquationStore (Expr Base Const) :=
  store.map fun e => (shiftAt cutoff e.1, shiftAt cutoff e.2)

/-- The frame's equations under `count` further variables. -/
def liftStore : Nat → EquationStore (Expr Base Const) → EquationStore (Expr Base Const)
  | 0, store => store
  | count + 1, store => shiftStore (liftStore count store)

theorem liftStore_nil :
    ∀ count : Nat, liftStore count ([] : EquationStore (Expr Base Const)) = []
  | 0 => rfl
  | count + 1 => by
      show shiftStore (liftStore count ([] : EquationStore (Expr Base Const))) = []
      rw [liftStore_nil count]
      rfl

theorem substStore_shiftStore (k : Nat) (s : Expr Base Const) :
    ∀ store : EquationStore (Expr Base Const),
      substStore (k + 1) s (shiftStore store) = shiftStore (substStore k s store)
  | [] => rfl
  | e :: store => by
      show (substAt (k + 1) s (shiftAt 0 e.1), substAt (k + 1) s (shiftAt 0 e.2)) ::
          substStore (k + 1) s (shiftStore store) =
        (shiftAt 0 (substAt k s e.1), shiftAt 0 (substAt k s e.2)) ::
          shiftStore (substStore k s store)
      rw [substAt_shiftAt s e.1 k 0 (Nat.zero_le _), substAt_shiftAt s e.2 k 0 (Nat.zero_le _),
        substStore_shiftStore k s store]

theorem shiftStoreAt_shiftStore (cutoff : Nat) :
    ∀ store : EquationStore (Expr Base Const),
      shiftStoreAt (cutoff + 1) (shiftStore store) = shiftStore (shiftStoreAt cutoff store)
  | [] => rfl
  | e :: store => by
      show (shiftAt (cutoff + 1) (shiftAt 0 e.1), shiftAt (cutoff + 1) (shiftAt 0 e.2)) ::
          shiftStoreAt (cutoff + 1) (shiftStore store) =
        (shiftAt 0 (shiftAt cutoff e.1), shiftAt 0 (shiftAt cutoff e.2)) ::
          shiftStore (shiftStoreAt cutoff store)
      rw [shiftAt_shiftAt e.1 0 cutoff (Nat.zero_le _), shiftAt_shiftAt e.2 0 cutoff (Nat.zero_le _),
        shiftStoreAt_shiftStore cutoff store]

theorem shiftStore_subset {small large : EquationStore (Expr Base Const)}
    (included : ∀ equation ∈ small, equation ∈ large) :
    ∀ equation ∈ shiftStore small, equation ∈ shiftStore large := by
  intro equation member
  obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨original, included original inStore, rfl⟩

theorem substStore_under {k : Nat} {s : Expr Base Const}
    {K K' : EquationStore (Expr Base Const)}
    (known : ∀ equation ∈ substStore k s K, equation ∈ K') :
    ∀ equation ∈ substStore (k + 1) s (shiftStore K), equation ∈ shiftStore K' := by
  rw [substStore_shiftStore]
  exact shiftStore_subset known

/-! ### Conversions at a frame -/

theorem assumedAt_mono {small large : EquationStore (Expr Base Const)}
    (included : ∀ equation ∈ small, equation ∈ large) {depth : Nat} {left right : Expr Base Const}
    (rule : assumedAt small depth left right) : assumedAt large depth left right := by
  obtain ⟨equation, member, atLeft, atRight⟩ := rule
  exact ⟨equation, included equation member, atLeft, atRight⟩

/-- More knowledge, more conversions. -/
theorem convertibleKnowing_mono {rules : Expr Base Const → Expr Base Const → Prop}
    {small large : EquationStore (Expr Base Const)}
    (included : ∀ equation ∈ small, equation ∈ large) {A B : Expr Base Const}
    (converted : ConvertibleKnowing rules small A B) : ConvertibleKnowing rules large A B := by
  induction converted with
  | rel _ _ step =>
      exact Relation.EqvGen.rel _ _
        (RewriteUnder.mono (fun _ _ _ rule => rule.imp id (assumedAt_mono included)) step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-- With no declared step, a conversion at a frame is a conversion by the frame's knowledge. -/
theorem convertibleUnder_of_none {store : EquationStore (Expr Base Const)} {A B : Expr Base Const}
    (converted : ConvertibleKnowing (fun _ _ => False) store A B) : ConvertibleUnder store A B := by
  induction converted with
  | rel _ _ step =>
      exact Relation.EqvGen.rel _ _
        (RewriteUnder.mono (fun _ _ _ rule => rule.elim False.elim id) step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

theorem assumedAt_subst (k : Nat) (s : Expr Base Const) {store : EquationStore (Expr Base Const)}
    {depth : Nat} {left right : Expr Base Const} (rule : assumedAt store depth left right) :
    assumedAt (substStore k s store) depth (substAt (k + depth) s left)
      (substAt (k + depth) s right) := by
  obtain ⟨equation, member, atLeft, atRight⟩ := rule
  exact ⟨(substAt k s equation.1, substAt k s equation.2),
    List.mem_map.mpr ⟨equation, member, rfl⟩, by rw [atLeft, substAt_shiftN],
    by rw [atRight, substAt_shiftN]⟩

theorem rewriteUnder_subst {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SubstitutionStable rules) (k : Nat) (s : Expr Base Const)
    {store : EquationStore (Expr Base Const)} {depth : Nat} {e e' : Expr Base Const}
    (step : RewriteUnder
      (fun depth left right => rules left right ∨ assumedAt store depth left right) depth e e') :
    RewriteUnder
      (fun depth left right =>
        rules left right ∨ assumedAt (substStore k s store) depth left right)
      depth (substAt (k + depth) s e) (substAt (k + depth) s e') := by
  induction step with
  | root rule =>
      rcases rule with direct | told
      · exact .root (Or.inl (stable _ _ direct _ s))
      · exact .root (Or.inr (assumedAt_subst k s told))
  | piDomain _ ih => exact .piDomain ih
  | piBody _ ih => exact .piBody ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih
  | impLeft _ ih => exact .impLeft ih
  | impRight _ ih => exact .impRight ih
  | notBody _ ih => exact .notBody ih
  | eqLeft _ ih => exact .eqLeft ih
  | eqRight _ ih => exact .eqRight ih
  | allDomain _ ih => exact .allDomain ih
  | allBody _ ih => exact .allBody ih
  | exDomain _ ih => exact .exDomain ih
  | exBody _ ih => exact .exBody ih

/-- **Asks move with an instantiation.** A conversion at a frame with knowledge is carried by a
substitution to a conversion at the instantiated frame, with the instantiated knowledge. -/
theorem convertibleKnowing_subst {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SubstitutionStable rules) (k : Nat) (s : Expr Base Const)
    {store : EquationStore (Expr Base Const)} {A B : Expr Base Const}
    (converted : ConvertibleKnowing rules store A B) :
    ConvertibleKnowing rules (substStore k s store) (substAt k s A) (substAt k s B) := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (rewriteUnder_subst stable k s step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

theorem assumedAt_shift (cutoff : Nat) {store : EquationStore (Expr Base Const)} {depth : Nat}
    {left right : Expr Base Const} (rule : assumedAt store depth left right) :
    assumedAt (shiftStoreAt cutoff store) depth (shiftAt (cutoff + depth) left)
      (shiftAt (cutoff + depth) right) := by
  obtain ⟨equation, member, atLeft, atRight⟩ := rule
  exact ⟨(shiftAt cutoff equation.1, shiftAt cutoff equation.2),
    List.mem_map.mpr ⟨equation, member, rfl⟩, by rw [atLeft, shiftAt_shiftN_above],
    by rw [atRight, shiftAt_shiftN_above]⟩

theorem rewriteUnder_shift {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) (cutoff : Nat) {store : EquationStore (Expr Base Const)}
    {depth : Nat} {e e' : Expr Base Const}
    (step : RewriteUnder
      (fun depth left right => rules left right ∨ assumedAt store depth left right) depth e e') :
    RewriteUnder
      (fun depth left right =>
        rules left right ∨ assumedAt (shiftStoreAt cutoff store) depth left right)
      depth (shiftAt (cutoff + depth) e) (shiftAt (cutoff + depth) e') := by
  induction step with
  | root rule =>
      rcases rule with direct | told
      · exact .root (Or.inl (stable _ _ direct _))
      · exact .root (Or.inr (assumedAt_shift cutoff told))
  | piDomain _ ih => exact .piDomain ih
  | piBody _ ih => exact .piBody ih
  | lamDomain _ ih => exact .lamDomain ih
  | lamBody _ ih => exact .lamBody ih
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih
  | andLeft _ ih => exact .andLeft ih
  | andRight _ ih => exact .andRight ih
  | orLeft _ ih => exact .orLeft ih
  | orRight _ ih => exact .orRight ih
  | impLeft _ ih => exact .impLeft ih
  | impRight _ ih => exact .impRight ih
  | notBody _ ih => exact .notBody ih
  | eqLeft _ ih => exact .eqLeft ih
  | eqRight _ ih => exact .eqRight ih
  | allDomain _ ih => exact .allDomain ih
  | allBody _ ih => exact .allBody ih
  | exDomain _ ih => exact .exDomain ih
  | exBody _ ih => exact .exBody ih

/-- **Asks move with the insertion of a variable.** -/
theorem convertibleKnowing_shift {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) (cutoff : Nat) {store : EquationStore (Expr Base Const)}
    {A B : Expr Base Const} (converted : ConvertibleKnowing rules store A B) :
    ConvertibleKnowing rules (shiftStoreAt cutoff store) (shiftAt cutoff A) (shiftAt cutoff B) := by
  induction converted with
  | rel _ _ step => exact Relation.EqvGen.rel _ _ (rewriteUnder_shift stable cutoff step)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ihFirst ihSecond => exact Relation.EqvGen.trans _ _ _ ihFirst ihSecond

/-! ## Typing at a frame with more knowledge -/

/-- **Typing only refines with knowledge**: what is typed at a frame is typed at every frame that
knows at least as much. -/
theorem typedKnowing_mono_store {rules : Expr Base Const → Expr Base Const → Prop}
    {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : TypedKnowing rules K Γ e A) :
    ∀ K' : EquationStore (Expr Base Const), (∀ equation ∈ K, equation ∈ K') →
      TypedKnowing rules K' Γ e A := by
  induction typed with
  | var lookup => exact fun _ _ => .var lookup
  | base b => exact fun _ _ => .base b
  | prop => exact fun _ _ => .prop
  | pi _ _ ihA ihB =>
      exact fun K' included => .pi (ihA K' included) (ihB _ (shiftStore_subset included))
  | lam _ _ ihA ihb =>
      exact fun K' included => .lam (ihA K' included) (ihb _ (shiftStore_subset included))
  | app _ _ ihf iha => exact fun K' included => .app (ihf K' included) (iha K' included)
  | const τ c => exact fun _ _ => .const τ c
  | tyFam b => exact fun _ _ => .tyFam b
  | top => exact fun _ _ => .top
  | bot => exact fun _ _ => .bot
  | and _ _ ihp ihq => exact fun K' included => .and (ihp K' included) (ihq K' included)
  | or _ _ ihp ihq => exact fun K' included => .or (ihp K' included) (ihq K' included)
  | imp _ _ ihp ihq => exact fun K' included => .imp (ihp K' included) (ihq K' included)
  | not _ ihp => exact fun K' included => .not (ihp K' included)
  | eq _ _ iha ihb => exact fun K' included => .eq (iha K' included) (ihb K' included)
  | all _ _ ihA ihb =>
      exact fun K' included => .all (ihA K' included) (ihb _ (shiftStore_subset included))
  | ex _ _ ihA ihb =>
      exact fun K' included => .ex (ihA K' included) (ihb _ (shiftStore_subset included))
  | move _ converted ih =>
      exact fun K' included => .move (ih K' included) (convertibleKnowing_mono included converted)

/-! ## Weakening -/

/-- A context prefix, shifted past one new variable inserted below it. -/
def shiftCtx : List (Expr Base Const) → List (Expr Base Const)
  | [] => []
  | A :: Δ => shiftAt Δ.length A :: shiftCtx Δ

/-- A context prefix, with a term substituted for the variable just below it. -/
def substCtx (s : Expr Base Const) : List (Expr Base Const) → List (Expr Base Const)
  | [] => []
  | A :: Δ => substAt Δ.length s A :: substCtx s Δ

theorem length_substCtx (s : Expr Base Const) :
    ∀ Δ : List (Expr Base Const), (substCtx s Δ).length = Δ.length
  | [] => rfl
  | _ :: Δ => congrArg Nat.succ (length_substCtx s Δ)

/-- Where a variable and its type go when one variable is inserted below a prefix. -/
theorem var_weaken_lookup (D : Expr Base Const) (Θ : List (Expr Base Const)) :
    ∀ (Δ : List (Expr Base Const)) (i : Nat) (T : Expr Base Const), (Δ ++ Θ)[i]? = some T →
      ∃ (j : Nat) (T' : Expr Base Const), (shiftCtx Δ ++ D :: Θ)[j]? = some T' ∧
        shiftAt Δ.length (bvar i : Expr Base Const) = bvar j ∧
        shiftAt Δ.length (shiftN (i + 1) T) = shiftN (j + 1) T'
  | [], i, T, lookup => ⟨i + 1, T, lookup, shiftAt_bvar_ge (Nat.not_lt_zero i), rfl⟩
  | A :: Δ, 0, T, lookup => by
      obtain rfl : A = T := Option.some.inj lookup
      refine ⟨0, shiftAt Δ.length A, rfl, shiftAt_bvar_lt (Nat.succ_pos _), ?_⟩
      show shiftAt (Δ.length + 1) (shiftAt 0 A) = shiftAt 0 (shiftAt Δ.length A)
      exact shiftAt_shiftAt A 0 Δ.length (Nat.zero_le _)
  | A :: Δ, i + 1, T, lookup => by
      obtain ⟨j, T', lookup', atTerm, atType⟩ := var_weaken_lookup D Θ Δ i T lookup
      refine ⟨j + 1, T', lookup', ?_, ?_⟩
      · show shiftAt (Δ.length + 1) (bvar (i + 1) : Expr Base Const) = bvar (j + 1)
        rw [← shiftAt_bvar_ge (Nat.not_lt_zero i), shiftAt_shiftAt (bvar i) 0 Δ.length (Nat.zero_le _),
          atTerm, shiftAt_bvar_ge (Nat.not_lt_zero j)]
      · show shiftAt (Δ.length + 1) (shiftAt 0 (shiftN (i + 1) T)) = shiftAt 0 (shiftN (j + 1) T')
        rw [shiftAt_shiftAt (shiftN (i + 1) T) 0 Δ.length (Nat.zero_le _), atType]

/-- **Weakening at a frame with knowledge**: a variable may be inserted anywhere in the context.
The term, its type and the store are shifted past it. -/
theorem typedKnowing_weaken {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) (D : Expr Base Const) {K : EquationStore (Expr Base Const)}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (typed : TypedKnowing rules K Γ e A) :
    ∀ (Δ Θ : List (Expr Base Const)), Γ = Δ ++ Θ →
      TypedKnowing rules (shiftStoreAt Δ.length K) (shiftCtx Δ ++ D :: Θ) (shiftAt Δ.length e)
        (shiftAt Δ.length A) := by
  induction typed with
  | @var K Γ i T lookup =>
      intro Δ Θ split
      subst split
      obtain ⟨j, T', lookup', atTerm, atType⟩ := var_weaken_lookup D Θ Δ i T lookup
      rw [atTerm, atType]
      exact .var lookup'
  | base b => exact fun _ _ _ => .base b
  | prop => exact fun _ _ _ => .prop
  | @pi K Γ A B _ _ ihA ihB =>
      intro Δ Θ split
      have body := ihB (A :: Δ) Θ (by rw [split]; rfl)
      rw [show (A :: Δ).length = Δ.length + 1 from rfl, shiftStoreAt_shiftStore] at body
      exact .pi (ihA Δ Θ split) body
  | @lam K Γ A b B _ _ ihA ihb =>
      intro Δ Θ split
      have body := ihb (A :: Δ) Θ (by rw [split]; rfl)
      rw [show (A :: Δ).length = Δ.length + 1 from rfl, shiftStoreAt_shiftStore] at body
      exact .lam (ihA Δ Θ split) body
  | @app K Γ f a A B _ _ ihf iha =>
      intro Δ Θ split
      have applied := TypedKnowing.app (ihf Δ Θ split) (iha Δ Θ split)
      have key : shiftAt Δ.length (substAt 0 a B) =
          substAt 0 (shiftAt Δ.length a) (shiftAt (Δ.length + 1) B) :=
        shiftAt_substAt a B Δ.length 0
      show TypedKnowing rules _ _ (shiftAt Δ.length (Expr.app f a))
        (shiftAt Δ.length (substAt 0 a B))
      rw [key]
      exact applied
  | const τ c =>
      intro Δ Θ _
      show TypedKnowing rules _ _ (Expr.const τ c) (shiftAt Δ.length (tyToExpr τ))
      rw [shiftAt_tyToExpr]
      exact .const τ c
  | tyFam b => exact fun _ _ _ => .tyFam b
  | top => exact fun _ _ _ => .top
  | bot => exact fun _ _ _ => .bot
  | and _ _ ihp ihq => exact fun Δ Θ split => .and (ihp Δ Θ split) (ihq Δ Θ split)
  | or _ _ ihp ihq => exact fun Δ Θ split => .or (ihp Δ Θ split) (ihq Δ Θ split)
  | imp _ _ ihp ihq => exact fun Δ Θ split => .imp (ihp Δ Θ split) (ihq Δ Θ split)
  | not _ ihp => exact fun Δ Θ split => .not (ihp Δ Θ split)
  | eq _ _ iha ihb => exact fun Δ Θ split => .eq (iha Δ Θ split) (ihb Δ Θ split)
  | @all K Γ A b _ _ ihA ihb =>
      intro Δ Θ split
      have body := ihb (A :: Δ) Θ (by rw [split]; rfl)
      rw [show (A :: Δ).length = Δ.length + 1 from rfl, shiftStoreAt_shiftStore] at body
      exact .all (ihA Δ Θ split) body
  | @ex K Γ A b _ _ ihA ihb =>
      intro Δ Θ split
      have body := ihb (A :: Δ) Θ (by rw [split]; rfl)
      rw [show (A :: Δ).length = Δ.length + 1 from rfl, shiftStoreAt_shiftStore] at body
      exact .ex (ihA Δ Θ split) body
  | move _ converted ih =>
      exact fun Δ Θ split =>
        .move (ih Δ Θ split) (convertibleKnowing_shift stable Δ.length converted)

/-- A typing at a frame, seen under a further prefix of variables: the term, its type and the
store are shifted past the prefix. -/
theorem typedKnowing_lift {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : ShiftStable rules) {K₀ : EquationStore (Expr Base Const)}
    {Θ : List (Expr Base Const)} {s C : Expr Base Const} (typedS : TypedKnowing rules K₀ Θ s C) :
    ∀ Δ : List (Expr Base Const),
      TypedKnowing rules (liftStore Δ.length K₀) (Δ ++ Θ) (shiftN Δ.length s) (shiftN Δ.length C)
  | [] => typedS
  | D :: Δ => typedKnowing_weaken stable D (typedKnowing_lift stable typedS Δ) [] (Δ ++ Θ) rfl

/-! ## Substitution -/

/-- Where a variable and its type go under a substitution: the substituted variable itself, or a
variable of the instantiated context. -/
theorem var_subst_lookup (s C : Expr Base Const) (Θ : List (Expr Base Const)) :
    ∀ (Δ : List (Expr Base Const)) (i : Nat) (T : Expr Base Const),
      (Δ ++ C :: Θ)[i]? = some T →
        (i = Δ.length ∧ T = C) ∨
          ∃ (j : Nat) (T' : Expr Base Const), (substCtx s Δ ++ Θ)[j]? = some T' ∧
            substAt Δ.length s (bvar i) = bvar j ∧
            substAt Δ.length s (shiftN (i + 1) T) = shiftN (j + 1) T'
  | [], 0, T, lookup => by
      obtain rfl : C = T := Option.some.inj lookup
      exact Or.inl ⟨rfl, rfl⟩
  | [], i + 1, T, lookup => by
      refine Or.inr ⟨i, T, lookup, ?_, ?_⟩
      · show substAt 0 s (bvar (i + 1)) = bvar i
        exact substAt_bvar_gt s (Nat.succ_pos i)
      · show substAt 0 s (shiftN (i + 1 + 1) T) = shiftN (i + 1) T
        exact substAt_shiftN_cancel s T 0 (i + 1) (Nat.zero_le _)
  | A :: Δ, 0, T, lookup => by
      obtain rfl : A = T := Option.some.inj lookup
      refine Or.inr ⟨0, substAt Δ.length s A, rfl, ?_, ?_⟩
      · show substAt (Δ.length + 1) s (bvar 0) = bvar 0
        exact substAt_bvar_lt s (Nat.succ_pos _)
      · show substAt (Δ.length + 1) s (shiftAt 0 A) = shiftAt 0 (substAt Δ.length s A)
        exact substAt_shiftAt s A Δ.length 0 (Nat.zero_le _)
  | A :: Δ, i + 1, T, lookup => by
      rcases var_subst_lookup s C Θ Δ i T lookup with
        ⟨atVariable, same⟩ | ⟨j, T', lookup', atTerm, atType⟩
      · exact Or.inl ⟨congrArg Nat.succ atVariable, same⟩
      · refine Or.inr ⟨j + 1, T', lookup', ?_, ?_⟩
        · show substAt (Δ.length + 1) s (bvar (i + 1)) = bvar (j + 1)
          rw [← shiftAt_bvar_ge (Nat.not_lt_zero i),
            substAt_shiftAt s (bvar i) Δ.length 0 (Nat.zero_le _), atTerm,
            shiftAt_bvar_ge (Nat.not_lt_zero j)]
        · show substAt (Δ.length + 1) s (shiftAt 0 (shiftN (i + 1) T)) =
            shiftAt 0 (shiftN (j + 1) T')
          rw [substAt_shiftAt s (shiftN (i + 1) T) Δ.length 0 (Nat.zero_le _), atType]

/-- **Substitution at a frame with knowledge.** A term typed at its own frame is substituted for
a variable of a larger frame. The context, the term and the type are instantiated, and so is the
store: the result is typed at every frame that knows the instantiated store and the knowledge the
substituted term was typed with. -/
theorem typedKnowing_subst {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    {K₀ : EquationStore (Expr Base Const)} {Θ : List (Expr Base Const)} {s C : Expr Base Const}
    (typedS : TypedKnowing rules K₀ Θ s C) {K : EquationStore (Expr Base Const)}
    {Γ : List (Expr Base Const)} {e A : Expr Base Const} (typed : TypedKnowing rules K Γ e A) :
    ∀ (Δ : List (Expr Base Const)) (K' : EquationStore (Expr Base Const)), Γ = Δ ++ C :: Θ →
      (∀ equation ∈ substStore Δ.length s K, equation ∈ K') →
      (∀ equation ∈ liftStore Δ.length K₀, equation ∈ K') →
        TypedKnowing rules K' (substCtx s Δ ++ Θ) (substAt Δ.length s e)
          (substAt Δ.length s A) := by
  induction typed with
  | @var K Γ i T lookup =>
      intro Δ K' split _ needed
      subst split
      rcases var_subst_lookup s C Θ Δ i T lookup with
        ⟨atVariable, same⟩ | ⟨j, T', lookup', atTerm, atType⟩
      · have lifted := typedKnowing_lift shiftStable typedS (substCtx s Δ)
        rw [length_substCtx] at lifted
        rw [atVariable, same, substAt_bvar_eq,
          substAt_shiftN_cancel s C Δ.length Δ.length (Nat.le_refl _)]
        exact typedKnowing_mono_store lifted K' needed
      · rw [atTerm, atType]
        exact .var lookup'
  | base b => exact fun _ _ _ _ _ => .base b
  | prop => exact fun _ _ _ _ _ => .prop
  | @pi K Γ A B _ _ ihA ihB =>
      intro Δ K' split known needed
      exact .pi (ihA Δ K' split known needed)
        (ihB (A :: Δ) (shiftStore K') (by rw [split]; rfl)
          (substStore_under (k := Δ.length) known) (shiftStore_subset needed))
  | @lam K Γ A b B _ _ ihA ihb =>
      intro Δ K' split known needed
      exact .lam (ihA Δ K' split known needed)
        (ihb (A :: Δ) (shiftStore K') (by rw [split]; rfl)
          (substStore_under (k := Δ.length) known) (shiftStore_subset needed))
  | @app K Γ f a A B _ _ ihf iha =>
      intro Δ K' split known needed
      have applied :=
        TypedKnowing.app (ihf Δ K' split known needed) (iha Δ K' split known needed)
      have key : substAt Δ.length s (substAt 0 a B) =
          substAt 0 (substAt Δ.length s a) (substAt (Δ.length + 1) s B) :=
        substAt_substAt s a B Δ.length 0
      show TypedKnowing rules _ _ (substAt Δ.length s (Expr.app f a))
        (substAt Δ.length s (substAt 0 a B))
      rw [key]
      exact applied
  | const τ c =>
      intro Δ K' _ _ _
      show TypedKnowing rules _ _ (Expr.const τ c) (substAt Δ.length s (tyToExpr τ))
      rw [substAt_tyToExpr]
      exact .const τ c
  | tyFam b => exact fun _ _ _ _ _ => .tyFam b
  | top => exact fun _ _ _ _ _ => .top
  | bot => exact fun _ _ _ _ _ => .bot
  | and _ _ ihp ihq =>
      exact fun Δ K' split known needed =>
        .and (ihp Δ K' split known needed) (ihq Δ K' split known needed)
  | or _ _ ihp ihq =>
      exact fun Δ K' split known needed =>
        .or (ihp Δ K' split known needed) (ihq Δ K' split known needed)
  | imp _ _ ihp ihq =>
      exact fun Δ K' split known needed =>
        .imp (ihp Δ K' split known needed) (ihq Δ K' split known needed)
  | not _ ihp => exact fun Δ K' split known needed => .not (ihp Δ K' split known needed)
  | eq _ _ iha ihb =>
      exact fun Δ K' split known needed =>
        .eq (iha Δ K' split known needed) (ihb Δ K' split known needed)
  | @all K Γ A b _ _ ihA ihb =>
      intro Δ K' split known needed
      exact .all (ihA Δ K' split known needed)
        (ihb (A :: Δ) (shiftStore K') (by rw [split]; rfl)
          (substStore_under (k := Δ.length) known) (shiftStore_subset needed))
  | @ex K Γ A b _ _ ihA ihb =>
      intro Δ K' split known needed
      exact .ex (ihA Δ K' split known needed)
        (ihb (A :: Δ) (shiftStore K') (by rw [split]; rfl)
          (substStore_under (k := Δ.length) known) (shiftStore_subset needed))
  | move _ converted ih =>
      exact fun Δ K' split known needed =>
        .move (ih Δ K' split known needed)
          (convertibleKnowing_mono known
            (convertibleKnowing_subst substStable Δ.length s converted))

/-- Substitution for the newest variable. The knowledge of the result is the instantiated store
together with what the substituted term was typed with. -/
theorem typedKnowing_subst_top {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    {K₀ K : EquationStore (Expr Base Const)} {Θ : List (Expr Base Const)}
    {s C e A : Expr Base Const} (typedS : TypedKnowing rules K₀ Θ s C)
    (typed : TypedKnowing rules K (C :: Θ) e A) :
    TypedKnowing rules (substStore 0 s K ++ K₀) Θ (substAt 0 s e) (substAt 0 s A) :=
  typedKnowing_subst substStable shiftStable typedS typed [] (substStore 0 s K ++ K₀) rfl
    (fun _ member => List.mem_append_left _ member)
    (fun _ member => List.mem_append_right _ member)

/-- **A solution discharges the frame's knowledge.** When the substituted term is typed in the
bubble and the instantiated equations are conversions of the bubble, the instance is typed in the
bubble, with no knowledge. -/
theorem typedKnowing_subst_solution {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    {Θ : List (Expr Base Const)} {s C : Expr Base Const}
    (typedS : BubbleTypingInside.HasTypeInside rules Θ s C)
    {K : EquationStore (Expr Base Const)} {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : TypedKnowing rules K Γ e A) (Δ : List (Expr Base Const)) (split : Γ = Δ ++ C :: Θ)
    (solves : ∀ equation ∈ K,
      Convertible rules (substAt Δ.length s equation.1) (substAt Δ.length s equation.2)) :
    BubbleTypingInside.HasTypeInside rules (substCtx s Δ ++ Θ) (substAt Δ.length s e)
      (substAt Δ.length s A) :=
  typedKnowing_discharge shiftStable
    (typedKnowing_subst substStable shiftStable (typedKnowing_of_inside typedS []) typed Δ
      (substStore Δ.length s K) split (fun _ member => member)
      (fun _ member => by
        rw [liftStore_nil] at member
        exact absurd member List.not_mem_nil))
    (by
      intro equation member
      obtain ⟨original, inStore, rfl⟩ := List.mem_map.mp member
      exact solves original inStore)

/-- With no declared step and no knowledge, typing at a frame is the global judgment. -/
theorem hasType_of_typedKnowing_none {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typed : TypedKnowing (fun _ _ => False) [] Γ e A) : HasType Γ e A :=
  BubbleTypingInside.hasTypeInside_none_iff.mp
    (typedKnowing_discharge (fun _ _ rule => rule.elim) typed
      (fun _ member => absurd member List.not_mem_nil))

/-- **Weakening of the global judgment**, the case with no declared step and no knowledge. -/
theorem hasType_weaken (D : Expr Base Const) {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typing : HasType Γ e A) (Δ Θ : List (Expr Base Const)) (split : Γ = Δ ++ Θ) :
    HasType (shiftCtx Δ ++ D :: Θ) (shiftAt Δ.length e) (shiftAt Δ.length A) :=
  hasType_of_typedKnowing_none
    (typedKnowing_weaken (rules := fun _ _ => False) (fun _ _ rule => rule.elim) D
      (TypedKnowing.of_hasType typing []) Δ Θ split)

/-- **The substitution property of the global judgment**, the case with no declared step and no
knowledge. -/
theorem hasType_subst {Θ : List (Expr Base Const)} {s C : Expr Base Const}
    (typedS : HasType Θ s C) {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (typing : HasType Γ e A) (Δ : List (Expr Base Const)) (split : Γ = Δ ++ C :: Θ) :
    HasType (substCtx s Δ ++ Θ) (substAt Δ.length s e) (substAt Δ.length s A) :=
  BubbleTypingInside.hasTypeInside_none_iff.mp
    (typedKnowing_subst_solution (rules := fun _ _ => False) (fun _ _ rule => rule.elim)
      (fun _ _ rule => rule.elim) (BubbleTypingInside.hasTypeInside_none_iff.mpr typedS)
      (TypedKnowing.of_hasType typing []) Δ split
      (fun _ member => absurd member List.not_mem_nil))

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.KnowledgeUnderBinders.Controls

/-- The numeral one. -/
def one : AExpr := succE zeroE

/-- At the frame that knows `n ≐ 0`, `Vec n` converts with `Vec 0`. -/
theorem vec_converts_at_frame :
    ConvertibleKnowing (fun _ _ => False) knowsZero (vec (bvar 0)) (vec zeroE) :=
  Relation.EqvGen.rel _ _
    (RewriteUnder.appArgument
      (RewriteUnder.root (Or.inr ⟨(bvar 0, zeroE), List.mem_singleton_self _, rfl, rfl⟩)))

/-- **The conversion moves with the instantiation**: `n := 1` carries it to the frame that knows
`1 ≐ 0`. -/
theorem vec_converts_instantiated :
    ConvertibleKnowing (fun _ _ => False) [(one, zeroE)] (vec one) (vec zeroE) :=
  convertibleKnowing_subst (fun _ _ rule => rule.elim) 0 one vec_converts_at_frame

/-- **The store has to be instantiated too**: with the knowledge left as `n ≐ 0`, nothing
converts `Vec 1` with `Vec 0`. -/
theorem vec_not_converted_by_stale_store :
    ¬ ConvertibleKnowing (fun _ _ => False) knowsZero (vec one) (vec zeroE) := by
  intro converted
  have same := collapseAt_conv (convertibleUnder_of_none converted)
  simp [collapseAt, vec, one, succE, zeroE] at same

/-- **The conversion moves with the insertion of a variable**: above a new variable the knowledge
is about index one. -/
theorem weakened_conversion :
    ConvertibleKnowing (fun _ _ => False) [(bvar 1, zeroE)] (vec (bvar 1)) (vec zeroE) :=
  convertibleKnowing_shift (fun _ _ rule => rule.elim) 0 vec_converts_at_frame

/-- **The store has to be shifted too**: with the knowledge left at index zero, nothing converts
`Vec n` with `Vec 0` once `n` has index one. -/
theorem weakening_needs_shifted_store :
    ¬ ConvertibleKnowing (fun _ _ => False) knowsZero (vec (bvar 1)) (vec zeroE) := by
  intro converted
  have same := collapseAt_conv (convertibleUnder_of_none converted)
  simp [collapseAt, vec, zeroE] at same

/-- **Instantiating by a solution.** In `n : nat, v : Vec n` with `n ≐ 0` known, the function
`λ (m : nat). v` is typed at `Π (m : nat). Vec 0` (`constant_function_at_zero`). With `n := 0` the
knowledge becomes `0 ≐ 0`, and the instance is typed by the global judgment. -/
theorem constant_function_solved :
    HasType [vec zeroE] (Expr.lam natType (bvar 1)) (Expr.pi natType (vec zeroE)) :=
  BubbleTypingInside.hasTypeInside_none_iff.mp
    (typedKnowing_subst_solution (rules := fun _ _ => False) (fun _ _ rule => rule.elim)
      (fun _ _ rule => rule.elim)
      (BubbleTypingInside.hasTypeInside_none_iff.mpr (HasType.const _ ArithConst.zero))
      constant_function_at_zero [vec (bvar 0)] rfl (by
        intro equation member
        obtain rfl := List.mem_singleton.mp member
        exact Relation.EqvGen.refl _))

/-- The numeral one is typed with no knowledge. -/
theorem one_typed : TypedKnowing (fun _ _ => False) ([] : EquationStore AExpr) [] one natType :=
  TypedKnowing.app (A := natType) (B := natType) (TypedKnowing.const _ ArithConst.succ)
    (TypedKnowing.const _ ArithConst.zero)

/-- **Instantiating by a term that is not a solution keeps the knowledge.** With `n := 1` the
instance is typed at the frame that knows `1 ≐ 0`, and it is not typed by the global judgment:
the substitution has carried the equation, it has not made it true. -/
theorem non_solution_keeps_the_knowledge :
    TypedKnowing (fun _ _ => False) [(one, zeroE)] [vec one]
        (Expr.lam natType (bvar 1)) (Expr.pi natType (vec zeroE)) ∧
      ¬ HasType [vec one] (Expr.lam natType (bvar 1)) (Expr.pi natType (vec zeroE)) := by
  refine ⟨?_, ?_⟩
  · exact typedKnowing_subst (fun _ _ rule => rule.elim) (fun _ _ rule => rule.elim) one_typed
      constant_function_at_zero [vec (bvar 0)] [(one, zeroE)] rfl (fun _ member => member)
      (fun _ member => absurd member List.not_mem_nil)
  · intro typed
    have typing :
        HasType [vec one] (Expr.lam natType (bvar 1)) (Expr.pi natType (vec one)) :=
      HasType.lam (HasType.base ()) (HasType.var (Γ := [natType, vec one]) (i := 1) rfl)
    have same := typing.unique typed
    simp [vec, one, succE, zeroE] at same

end Controls

/-! ## Axiom audit -/

#print axioms shiftAt_shiftAt
#print axioms substAt_shiftAt
#print axioms substAt_substAt
#print axioms shiftAt_substAt
#print axioms convertibleKnowing_subst
#print axioms convertibleKnowing_shift
#print axioms typedKnowing_mono_store
#print axioms typedKnowing_weaken
#print axioms typedKnowing_subst
#print axioms typedKnowing_subst_top
#print axioms typedKnowing_subst_solution
#print axioms hasType_weaken
#print axioms hasType_subst
#print axioms Controls.vec_converts_instantiated
#print axioms Controls.vec_not_converted_by_stale_store
#print axioms Controls.weakened_conversion
#print axioms Controls.weakening_needs_shifted_store
#print axioms Controls.constant_function_solved
#print axioms Controls.non_solution_keeps_the_knowledge

end Mettapedia.TypeTheory.KnowledgeSubstitution
