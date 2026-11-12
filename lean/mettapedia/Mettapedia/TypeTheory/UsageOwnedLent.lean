import Mettapedia.TypeTheory.BubbleTypingAdmission

/-!
# Owned and lent hypotheses on the comparison core: what a term uses, and what its type mentions

A term uses its variables; its type mentions variables. This module counts the first and proves
the laws that separate the two ways a hypothesis can be held.

* `owned i e` is the number of times the term `e` uses the variable `i`. The type annotation of
  an abstraction is not counted: a type lends its variables, it does not use them.
* `owned_substAt`: substitution multiplies. The instance of `e` at `x := s` uses a variable as
  often as `e` does, plus the uses of `x` in `e` times the uses in `s`.
* `beta_owned`: the contractum of a β redex uses a variable as often as the body does, plus the
  uses of the bound variable times the uses in the argument.
* `beta_owned_once`: when the bound variable is used exactly once (an owned hypothesis), the
  contractum uses every variable exactly as often as the redex.
* `beta_owned_lent`: when the argument uses nothing (it can be lent any number of times), the same
  holds whatever the number of uses of the bound variable.
* `TypingAdmission.beta_exact`: in an admitted bubble, a β step on an owned binder keeps the type
  and the uses together.

The count is on terms only. A usage-annotated typing judgment, with the modes of the calculus's
takes and reads on the hypotheses of a context, is not defined here.

## Controls

* `Controls.dependency_is_a_loan`: `v : Vec n` uses `v` once and `n` never, and its type mentions
  `n`.
* `Controls.annotation_is_lent`: a variable mentioned only in the annotation of an abstraction is
  not used.
* `Controls.read_twice_doubles`, `Controls.unread_discards`: a binder used twice doubles what its
  argument uses, and a binder not used discards it; in both cases the β step changes the uses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UsageOwnedLent

open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleBetaTyping
open Mettapedia.TypeTheory.BubbleTypingAdmission
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The number of times a term uses the variable `i`. The annotation of an abstraction is not
counted. -/
def owned : Nat → Expr Base Const → Nat
  | i, .bvar j => if j = i then 1 else 0
  | _, .univ => 0
  | _, .prop => 0
  | _, .base _ => 0
  | i, .pi A B => owned i A + owned (i + 1) B
  | i, .lam _ b => owned (i + 1) b
  | i, .app f a => owned i f + owned i a
  | _, .const _ _ => 0
  | _, .tyFam _ => 0
  | _, .top => 0
  | _, .bot => 0
  | i, .and p q => owned i p + owned i q
  | i, .or p q => owned i p + owned i q
  | i, .imp p q => owned i p + owned i q
  | i, .not p => owned i p
  | i, .eq a b => owned i a + owned i b
  | i, .all A b => owned i A + owned (i + 1) b
  | i, .ex A b => owned i A + owned (i + 1) b

/-! ## Uses under a shift -/

/-- Below the cutoff a shift changes no use. -/
theorem owned_shiftAt_lt : ∀ (e : Expr Base Const) (i c : Nat), i < c →
    owned i (shiftAt c e) = owned i e
  | .bvar j, i, c, below => by
      by_cases under : j < c
      · rw [shiftAt_bvar_lt under]
      · rw [shiftAt_bvar_ge under]
        simp only [owned]
        rw [if_neg (by omega), if_neg (by omega)]
  | .univ, _, _, _ => rfl
  | .prop, _, _, _ => rfl
  | .base _, _, _, _ => rfl
  | .pi A B, i, c, below => by
      show owned i (shiftAt c A) + owned (i + 1) (shiftAt (c + 1) B) = owned i A + owned (i + 1) B
      rw [owned_shiftAt_lt A i c below, owned_shiftAt_lt B (i + 1) (c + 1) (by omega)]
  | .lam _ b, i, c, below => by
      show owned (i + 1) (shiftAt (c + 1) b) = owned (i + 1) b
      rw [owned_shiftAt_lt b (i + 1) (c + 1) (by omega)]
  | .app f a, i, c, below => by
      show owned i (shiftAt c f) + owned i (shiftAt c a) = owned i f + owned i a
      rw [owned_shiftAt_lt f i c below, owned_shiftAt_lt a i c below]
  | .const _ _, _, _, _ => rfl
  | .tyFam _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .and p q, i, c, below => by
      show owned i (shiftAt c p) + owned i (shiftAt c q) = owned i p + owned i q
      rw [owned_shiftAt_lt p i c below, owned_shiftAt_lt q i c below]
  | .or p q, i, c, below => by
      show owned i (shiftAt c p) + owned i (shiftAt c q) = owned i p + owned i q
      rw [owned_shiftAt_lt p i c below, owned_shiftAt_lt q i c below]
  | .imp p q, i, c, below => by
      show owned i (shiftAt c p) + owned i (shiftAt c q) = owned i p + owned i q
      rw [owned_shiftAt_lt p i c below, owned_shiftAt_lt q i c below]
  | .not p, i, c, below => by
      show owned i (shiftAt c p) = owned i p
      rw [owned_shiftAt_lt p i c below]
  | .eq a b, i, c, below => by
      show owned i (shiftAt c a) + owned i (shiftAt c b) = owned i a + owned i b
      rw [owned_shiftAt_lt a i c below, owned_shiftAt_lt b i c below]
  | .all A b, i, c, below => by
      show owned i (shiftAt c A) + owned (i + 1) (shiftAt (c + 1) b) = owned i A + owned (i + 1) b
      rw [owned_shiftAt_lt A i c below, owned_shiftAt_lt b (i + 1) (c + 1) (by omega)]
  | .ex A b, i, c, below => by
      show owned i (shiftAt c A) + owned (i + 1) (shiftAt (c + 1) b) = owned i A + owned (i + 1) b
      rw [owned_shiftAt_lt A i c below, owned_shiftAt_lt b (i + 1) (c + 1) (by omega)]

/-- The variable a shift makes room for is not used. -/
theorem owned_shiftAt_eq : ∀ (e : Expr Base Const) (c : Nat), owned c (shiftAt c e) = 0
  | .bvar j, c => by
      by_cases under : j < c
      · rw [shiftAt_bvar_lt under]
        simp only [owned]
        rw [if_neg (by omega)]
      · rw [shiftAt_bvar_ge under]
        simp only [owned]
        rw [if_neg (by omega)]
  | .univ, _ => rfl
  | .prop, _ => rfl
  | .base _, _ => rfl
  | .pi A B, c => by
      show owned c (shiftAt c A) + owned (c + 1) (shiftAt (c + 1) B) = 0
      rw [owned_shiftAt_eq A c, owned_shiftAt_eq B (c + 1)]
  | .lam _ b, c => by
      show owned (c + 1) (shiftAt (c + 1) b) = 0
      rw [owned_shiftAt_eq b (c + 1)]
  | .app f a, c => by
      show owned c (shiftAt c f) + owned c (shiftAt c a) = 0
      rw [owned_shiftAt_eq f c, owned_shiftAt_eq a c]
  | .const _ _, _ => rfl
  | .tyFam _, _ => rfl
  | .top, _ => rfl
  | .bot, _ => rfl
  | .and p q, c => by
      show owned c (shiftAt c p) + owned c (shiftAt c q) = 0
      rw [owned_shiftAt_eq p c, owned_shiftAt_eq q c]
  | .or p q, c => by
      show owned c (shiftAt c p) + owned c (shiftAt c q) = 0
      rw [owned_shiftAt_eq p c, owned_shiftAt_eq q c]
  | .imp p q, c => by
      show owned c (shiftAt c p) + owned c (shiftAt c q) = 0
      rw [owned_shiftAt_eq p c, owned_shiftAt_eq q c]
  | .not p, c => by
      show owned c (shiftAt c p) = 0
      rw [owned_shiftAt_eq p c]
  | .eq a b, c => by
      show owned c (shiftAt c a) + owned c (shiftAt c b) = 0
      rw [owned_shiftAt_eq a c, owned_shiftAt_eq b c]
  | .all A b, c => by
      show owned c (shiftAt c A) + owned (c + 1) (shiftAt (c + 1) b) = 0
      rw [owned_shiftAt_eq A c, owned_shiftAt_eq b (c + 1)]
  | .ex A b, c => by
      show owned c (shiftAt c A) + owned (c + 1) (shiftAt (c + 1) b) = 0
      rw [owned_shiftAt_eq A c, owned_shiftAt_eq b (c + 1)]

/-- Above the cutoff a shift moves every use one variable up. -/
theorem owned_shiftAt_gt : ∀ (e : Expr Base Const) (i c : Nat), c ≤ i →
    owned (i + 1) (shiftAt c e) = owned i e
  | .bvar j, i, c, above => by
      by_cases under : j < c
      · rw [shiftAt_bvar_lt under]
        simp only [owned]
        rw [if_neg (by omega), if_neg (by omega)]
      · rw [shiftAt_bvar_ge under]
        simp only [owned]
        by_cases same : j = i
        · rw [if_pos (by omega), if_pos same]
        · rw [if_neg (by omega), if_neg same]
  | .univ, _, _, _ => rfl
  | .prop, _, _, _ => rfl
  | .base _, _, _, _ => rfl
  | .pi A B, i, c, above => by
      show owned (i + 1) (shiftAt c A) + owned (i + 1 + 1) (shiftAt (c + 1) B) =
        owned i A + owned (i + 1) B
      rw [owned_shiftAt_gt A i c above, owned_shiftAt_gt B (i + 1) (c + 1) (by omega)]
  | .lam _ b, i, c, above => by
      show owned (i + 1 + 1) (shiftAt (c + 1) b) = owned (i + 1) b
      rw [owned_shiftAt_gt b (i + 1) (c + 1) (by omega)]
  | .app f a, i, c, above => by
      show owned (i + 1) (shiftAt c f) + owned (i + 1) (shiftAt c a) = owned i f + owned i a
      rw [owned_shiftAt_gt f i c above, owned_shiftAt_gt a i c above]
  | .const _ _, _, _, _ => rfl
  | .tyFam _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .and p q, i, c, above => by
      show owned (i + 1) (shiftAt c p) + owned (i + 1) (shiftAt c q) = owned i p + owned i q
      rw [owned_shiftAt_gt p i c above, owned_shiftAt_gt q i c above]
  | .or p q, i, c, above => by
      show owned (i + 1) (shiftAt c p) + owned (i + 1) (shiftAt c q) = owned i p + owned i q
      rw [owned_shiftAt_gt p i c above, owned_shiftAt_gt q i c above]
  | .imp p q, i, c, above => by
      show owned (i + 1) (shiftAt c p) + owned (i + 1) (shiftAt c q) = owned i p + owned i q
      rw [owned_shiftAt_gt p i c above, owned_shiftAt_gt q i c above]
  | .not p, i, c, above => by
      show owned (i + 1) (shiftAt c p) = owned i p
      rw [owned_shiftAt_gt p i c above]
  | .eq a b, i, c, above => by
      show owned (i + 1) (shiftAt c a) + owned (i + 1) (shiftAt c b) = owned i a + owned i b
      rw [owned_shiftAt_gt a i c above, owned_shiftAt_gt b i c above]
  | .all A b, i, c, above => by
      show owned (i + 1) (shiftAt c A) + owned (i + 1 + 1) (shiftAt (c + 1) b) =
        owned i A + owned (i + 1) b
      rw [owned_shiftAt_gt A i c above, owned_shiftAt_gt b (i + 1) (c + 1) (by omega)]
  | .ex A b, i, c, above => by
      show owned (i + 1) (shiftAt c A) + owned (i + 1 + 1) (shiftAt (c + 1) b) =
        owned i A + owned (i + 1) b
      rw [owned_shiftAt_gt A i c above, owned_shiftAt_gt b (i + 1) (c + 1) (by omega)]

/-- A term shifted past `count` variables uses none of them. -/
theorem owned_shiftN_lt (s : Expr Base Const) : ∀ (count i : Nat), i < count →
    owned i (shiftN count s) = 0
  | 0, _, below => absurd below (Nat.not_lt_zero _)
  | count + 1, 0, _ => owned_shiftAt_eq (shiftN count s) 0
  | count + 1, i + 1, below => by
      show owned (i + 1) (shiftAt 0 (shiftN count s)) = 0
      rw [owned_shiftAt_gt (shiftN count s) i 0 (Nat.zero_le _),
        owned_shiftN_lt s count i (by omega)]

/-- A term shifted past `count` variables uses the others as before. -/
theorem owned_shiftN_add (s : Expr Base Const) (i : Nat) : ∀ count : Nat,
    owned (i + count) (shiftN count s) = owned i s
  | 0 => rfl
  | count + 1 => by
      show owned (i + count + 1) (shiftAt 0 (shiftN count s)) = owned i s
      rw [owned_shiftAt_gt (shiftN count s) (i + count) 0 (Nat.zero_le _),
        owned_shiftN_add s i count]

/-! ## Substitution multiplies -/

/-- Below the substituted variable an instantiation changes no use. -/
theorem owned_substAt_lt (s : Expr Base Const) : ∀ (e : Expr Base Const) (i k : Nat), i < k →
    owned i (substAt k s e) = owned i e
  | .bvar j, i, k, below => by
      rcases Nat.lt_trichotomy j k with under | same | above
      · rw [substAt_bvar_lt s under]
      · subst same
        rw [substAt_bvar_eq, owned_shiftN_lt s j i below]
        simp only [owned]
        rw [if_neg (by omega)]
      · rw [substAt_bvar_gt s above]
        simp only [owned]
        rw [if_neg (by omega), if_neg (by omega)]
  | .univ, _, _, _ => rfl
  | .prop, _, _, _ => rfl
  | .base _, _, _, _ => rfl
  | .pi A B, i, k, below => by
      show owned i (substAt k s A) + owned (i + 1) (substAt (k + 1) s B) =
        owned i A + owned (i + 1) B
      rw [owned_substAt_lt s A i k below, owned_substAt_lt s B (i + 1) (k + 1) (by omega)]
  | .lam _ b, i, k, below => by
      show owned (i + 1) (substAt (k + 1) s b) = owned (i + 1) b
      rw [owned_substAt_lt s b (i + 1) (k + 1) (by omega)]
  | .app f a, i, k, below => by
      show owned i (substAt k s f) + owned i (substAt k s a) = owned i f + owned i a
      rw [owned_substAt_lt s f i k below, owned_substAt_lt s a i k below]
  | .const _ _, _, _, _ => rfl
  | .tyFam _, _, _, _ => rfl
  | .top, _, _, _ => rfl
  | .bot, _, _, _ => rfl
  | .and p q, i, k, below => by
      show owned i (substAt k s p) + owned i (substAt k s q) = owned i p + owned i q
      rw [owned_substAt_lt s p i k below, owned_substAt_lt s q i k below]
  | .or p q, i, k, below => by
      show owned i (substAt k s p) + owned i (substAt k s q) = owned i p + owned i q
      rw [owned_substAt_lt s p i k below, owned_substAt_lt s q i k below]
  | .imp p q, i, k, below => by
      show owned i (substAt k s p) + owned i (substAt k s q) = owned i p + owned i q
      rw [owned_substAt_lt s p i k below, owned_substAt_lt s q i k below]
  | .not p, i, k, below => by
      show owned i (substAt k s p) = owned i p
      rw [owned_substAt_lt s p i k below]
  | .eq a b, i, k, below => by
      show owned i (substAt k s a) + owned i (substAt k s b) = owned i a + owned i b
      rw [owned_substAt_lt s a i k below, owned_substAt_lt s b i k below]
  | .all A b, i, k, below => by
      show owned i (substAt k s A) + owned (i + 1) (substAt (k + 1) s b) =
        owned i A + owned (i + 1) b
      rw [owned_substAt_lt s A i k below, owned_substAt_lt s b (i + 1) (k + 1) (by omega)]
  | .ex A b, i, k, below => by
      show owned i (substAt k s A) + owned (i + 1) (substAt (k + 1) s b) =
        owned i A + owned (i + 1) b
      rw [owned_substAt_lt s A i k below, owned_substAt_lt s b (i + 1) (k + 1) (by omega)]

/-- **Substitution multiplies.** At or above the substituted variable, the instance uses a
variable as often as the term used the next one, plus the uses of the substituted variable times
the uses in the substituted term. -/
theorem owned_substAt (s : Expr Base Const) : ∀ (e : Expr Base Const) (i k : Nat),
    owned (i + k) (substAt k s e) = owned (i + k + 1) e + owned k e * owned i s
  | .bvar j, i, k => by
      rcases Nat.lt_trichotomy j k with under | same | above
      · rw [substAt_bvar_lt s under]
        simp only [owned]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        simp
      · subst same
        rw [substAt_bvar_eq, owned_shiftN_add s i j]
        simp only [owned]
        rw [if_neg (by omega)]
        simp
      · rw [substAt_bvar_gt s above]
        simp only [owned]
        rw [if_neg (by omega : ¬ j = k)]
        by_cases next : j = i + k + 1
        · rw [if_pos (by omega), if_pos next]
          simp
        · rw [if_neg (by omega), if_neg next]
          simp
  | .univ, _, _ => by simp [owned, substAt]
  | .prop, _, _ => by simp [owned, substAt]
  | .base _, _, _ => by simp [owned, substAt]
  | .pi A B, i, k => by
      have atA := owned_substAt s A i k
      have atB : owned (i + k + 1) (substAt (k + 1) s B) =
          owned (i + k + 1 + 1) B + owned (k + 1) B * owned i s := owned_substAt s B i (k + 1)
      show owned (i + k) (substAt k s A) + owned (i + k + 1) (substAt (k + 1) s B) =
        owned (i + k + 1) A + owned (i + k + 1 + 1) B + (owned k A + owned (k + 1) B) * owned i s
      rw [atA, atB, Nat.add_mul]
      omega
  | .lam _ b, i, k => by
      have atB : owned (i + k + 1) (substAt (k + 1) s b) =
          owned (i + k + 1 + 1) b + owned (k + 1) b * owned i s := owned_substAt s b i (k + 1)
      exact atB
  | .app f a, i, k => by
      have atF := owned_substAt s f i k
      have atA := owned_substAt s a i k
      show owned (i + k) (substAt k s f) + owned (i + k) (substAt k s a) =
        owned (i + k + 1) f + owned (i + k + 1) a + (owned k f + owned k a) * owned i s
      rw [atF, atA, Nat.add_mul]
      omega
  | .const _ _, _, _ => by simp [owned, substAt]
  | .tyFam _, _, _ => by simp [owned, substAt]
  | .top, _, _ => by simp [owned, substAt]
  | .bot, _, _ => by simp [owned, substAt]
  | .and p q, i, k => by
      have atP := owned_substAt s p i k
      have atQ := owned_substAt s q i k
      show owned (i + k) (substAt k s p) + owned (i + k) (substAt k s q) =
        owned (i + k + 1) p + owned (i + k + 1) q + (owned k p + owned k q) * owned i s
      rw [atP, atQ, Nat.add_mul]
      omega
  | .or p q, i, k => by
      have atP := owned_substAt s p i k
      have atQ := owned_substAt s q i k
      show owned (i + k) (substAt k s p) + owned (i + k) (substAt k s q) =
        owned (i + k + 1) p + owned (i + k + 1) q + (owned k p + owned k q) * owned i s
      rw [atP, atQ, Nat.add_mul]
      omega
  | .imp p q, i, k => by
      have atP := owned_substAt s p i k
      have atQ := owned_substAt s q i k
      show owned (i + k) (substAt k s p) + owned (i + k) (substAt k s q) =
        owned (i + k + 1) p + owned (i + k + 1) q + (owned k p + owned k q) * owned i s
      rw [atP, atQ, Nat.add_mul]
      omega
  | .not p, i, k => owned_substAt s p i k
  | .eq a b, i, k => by
      have atA := owned_substAt s a i k
      have atB := owned_substAt s b i k
      show owned (i + k) (substAt k s a) + owned (i + k) (substAt k s b) =
        owned (i + k + 1) a + owned (i + k + 1) b + (owned k a + owned k b) * owned i s
      rw [atA, atB, Nat.add_mul]
      omega
  | .all A b, i, k => by
      have atA := owned_substAt s A i k
      have atB : owned (i + k + 1) (substAt (k + 1) s b) =
          owned (i + k + 1 + 1) b + owned (k + 1) b * owned i s := owned_substAt s b i (k + 1)
      show owned (i + k) (substAt k s A) + owned (i + k + 1) (substAt (k + 1) s b) =
        owned (i + k + 1) A + owned (i + k + 1 + 1) b + (owned k A + owned (k + 1) b) * owned i s
      rw [atA, atB, Nat.add_mul]
      omega
  | .ex A b, i, k => by
      have atA := owned_substAt s A i k
      have atB : owned (i + k + 1) (substAt (k + 1) s b) =
          owned (i + k + 1 + 1) b + owned (k + 1) b * owned i s := owned_substAt s b i (k + 1)
      show owned (i + k) (substAt k s A) + owned (i + k + 1) (substAt (k + 1) s b) =
        owned (i + k + 1) A + owned (i + k + 1 + 1) b + (owned k A + owned (k + 1) b) * owned i s
      rw [atA, atB, Nat.add_mul]
      omega

/-! ## The β step and the two ways to hold a hypothesis -/

/-- **The uses of a contractum.** -/
theorem beta_owned (a b : Expr Base Const) (i : Nat) :
    owned i (substAt 0 a b) = owned (i + 1) b + owned 0 b * owned i a :=
  owned_substAt a b i 0

/-- The uses of a redex: the uses of the body and of the argument. -/
theorem redex_owned (A a b : Expr Base Const) (i : Nat) :
    owned i (Expr.app (Expr.lam A b) a) = owned (i + 1) b + owned i a :=
  rfl

/-- **An owned hypothesis.** When the bound variable is used exactly once, the contractum uses
every variable exactly as often as the redex. -/
theorem beta_owned_once (A a : Expr Base Const) {b : Expr Base Const} (once : owned 0 b = 1)
    (i : Nat) : owned i (substAt 0 a b) = owned i (Expr.app (Expr.lam A b) a) := by
  rw [beta_owned, redex_owned, once, Nat.one_mul]

/-- **A lent hypothesis.** When the argument uses nothing, the contractum uses every variable
exactly as often as the redex, whatever the number of uses of the bound variable. -/
theorem beta_owned_lent (A b : Expr Base Const) {a : Expr Base Const}
    (nothing : ∀ i : Nat, owned i a = 0) (i : Nat) :
    owned i (substAt 0 a b) = owned i (Expr.app (Expr.lam A b) a) := by
  rw [beta_owned, redex_owned, nothing i, Nat.mul_zero]

/-- **A β step on an owned binder keeps the type and the uses together**, in an admitted
bubble. -/
theorem _root_.Mettapedia.TypeTheory.BubbleTypingAdmission.TypingAdmission.beta_exact
    {rules : Expr Base Const → Expr Base Const → Prop} (admitted : TypingAdmission rules)
    {Γ : List (Expr Base Const)} {A b a T : Expr Base Const}
    (typed : HasTypeInside rules Γ (Expr.app (Expr.lam A b) a) T) (once : owned 0 b = 1) :
    HasTypeInside rules Γ (substAt 0 a b) T ∧
      ∀ i : Nat, owned i (substAt 0 a b) = owned i (Expr.app (Expr.lam A b) a) :=
  ⟨admitted.beta typed, beta_owned_once A a once⟩

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- **Dependency is a loan**: in `n : nat, v : Vec n`, the term `v` is typed at `Vec n`, it uses
`v` once and `n` never, and its type mentions `n`. -/
theorem dependency_is_a_loan :
    HasType vecContext (bvar 0) (vec (bvar 1)) ∧ owned 0 (bvar 0 : AExpr) = 1 ∧
      owned 1 (bvar 0 : AExpr) = 0 ∧ owned 1 (vec (bvar 1)) = 1 :=
  ⟨HasType.var (Γ := vecContext) (i := 0) rfl, rfl, rfl, rfl⟩

/-- **An annotation is lent**: the abstraction `λ (w : Vec n). w` does not use `n`, which its
annotation mentions. -/
theorem annotation_is_lent : owned 0 (Expr.lam (vec (bvar 0)) (bvar 0) : AExpr) = 0 :=
  rfl

/-- The body `x ≐ x`, which uses its bound variable twice. -/
def readsTwice : AExpr := Expr.eq (bvar 0) (bvar 0)

/-- **A binder used twice doubles what its argument uses**: the redex `(λ x. x ≐ x) y` uses `y`
once and its contractum uses it twice. -/
theorem read_twice_doubles :
    owned 0 (Expr.app (Expr.lam natType readsTwice) (bvar 0)) = 1 ∧
      owned 0 (substAt 0 (bvar 0) readsTwice) = 2 :=
  ⟨rfl, rfl⟩

/-- **A binder not used discards what its argument uses**: the redex `(λ x. 0) y` uses `y` once
and its contractum does not use it. -/
theorem unread_discards :
    owned 0 (Expr.app (Expr.lam natType zeroE) (bvar 0)) = 1 ∧
      owned 0 (substAt 0 (bvar 0) zeroE) = 0 :=
  ⟨rfl, rfl⟩

/-- The identity uses its bound variable once, so its β step keeps the uses. -/
theorem identity_keeps_uses (a : AExpr) (i : Nat) :
    owned i (substAt 0 a (bvar 0)) = owned i (Expr.app (Expr.lam natType (bvar 0)) a) :=
  beta_owned_once natType a rfl i

end Controls

/-! ## Axiom audit -/

#print axioms owned_shiftAt_gt
#print axioms owned_substAt_lt
#print axioms owned_substAt
#print axioms beta_owned
#print axioms beta_owned_once
#print axioms beta_owned_lent
#print axioms Mettapedia.TypeTheory.BubbleTypingAdmission.TypingAdmission.beta_exact
#print axioms Controls.dependency_is_a_loan
#print axioms Controls.annotation_is_lent
#print axioms Controls.read_twice_doubles
#print axioms Controls.unread_discards
#print axioms Controls.identity_keeps_uses

end Mettapedia.TypeTheory.UsageOwnedLent
