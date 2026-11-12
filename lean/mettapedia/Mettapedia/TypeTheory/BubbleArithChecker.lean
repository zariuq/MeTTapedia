import Mettapedia.TypeTheory.BubbleTypingAdmission

/-!
# A checker for the arithmetic bubbles: typing with conversion everywhere, decided

`BubbleTypingAlgorithmic.Synth` says where a typing asks for a conversion. In a bubble whose
conversion is decided by normal forms, every ask can be answered by computing: the function type
is normalized and matched against a product, and two types are compared by their normal forms.
This module does it for the arithmetic bubbles and proves the result correct.

* `infer plus Γ e` computes the type of `e` in normal form, when `e` has one.
* `infer_sound`: the type returned is a type of the term in the bubble.
* `infer_complete`: every type of the term has the returned type as its normal form.
* `typed_iff_infer`, `typed_iff_check`: typing with the conversion rule at every node is decided
  by the checker. The term carries no annotation for any conversion.
* `sameExpr`, `eq_of_sameExpr`: equality of terms of the arithmetic signature, computed.

## Controls

* `Controls.application_checked`: with `f : Vec (n + 0) → nat` and `v : Vec n`, the checker types
  `f v` in the bubble of the recursion equations; the conversion of `Vec (n + 0)` with `Vec n` is
  found by normalization.
* `Controls.zeroAdd_refused`, `Controls.zeroAdd_checked_in_plus`: with `f : Vec (0 + n) → nat`
  the same application has no type in that bubble, and has one in the bubble that also declares
  the left unit. The choice of bubble is what decides.
* `Controls.zeroAdd_not_typable`: so that application is not typable there, with the conversion
  rule at every node.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.BubbleArithChecker

open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic.Controls
open Mettapedia.TypeTheory.BubbleSubjectReduction
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

/-! ## Equality of terms, computed -/

/-- A number for each constant. -/
def constCode : {τ : Ty Unit} → ArithConst τ → Nat
  | _, .zero => 0
  | _, .succ => 1
  | _, .add => 2

theorem const_eq_of_code {τ τ' : Ty Unit} (c : ArithConst τ) (c' : ArithConst τ')
    (same : constCode c = constCode c') : (Expr.const τ c : AExpr) = Expr.const τ' c' := by
  cases c <;> cases c' <;> first | rfl | exact absurd same (by decide)

/-- Equality of two terms, computed. -/
def sameExpr : AExpr → AExpr → Bool
  | .bvar i, .bvar j => i == j
  | .univ, .univ => true
  | .prop, .prop => true
  | .base _, .base _ => true
  | .pi A B, .pi A' B' => sameExpr A A' && sameExpr B B'
  | .lam A b, .lam A' b' => sameExpr A A' && sameExpr b b'
  | .app f a, .app f' a' => sameExpr f f' && sameExpr a a'
  | .const _ c, .const _ c' => constCode c == constCode c'
  | .tyFam _, .tyFam _ => true
  | .top, .top => true
  | .bot, .bot => true
  | .and p q, .and p' q' => sameExpr p p' && sameExpr q q'
  | .or p q, .or p' q' => sameExpr p p' && sameExpr q q'
  | .imp p q, .imp p' q' => sameExpr p p' && sameExpr q q'
  | .not p, .not p' => sameExpr p p'
  | .eq a b, .eq a' b' => sameExpr a a' && sameExpr b b'
  | .all A b, .all A' b' => sameExpr A A' && sameExpr b b'
  | .ex A b, .ex A' b' => sameExpr A A' && sameExpr b b'
  | _, _ => false

theorem sameExpr_refl : ∀ a : AExpr, sameExpr a a = true
  | .bvar i => by simp [sameExpr]
  | .univ => rfl
  | .prop => rfl
  | .base _ => rfl
  | .pi A B => by simp [sameExpr, sameExpr_refl A, sameExpr_refl B]
  | .lam A b => by simp [sameExpr, sameExpr_refl A, sameExpr_refl b]
  | .app f a => by simp [sameExpr, sameExpr_refl f, sameExpr_refl a]
  | .const _ _ => by simp [sameExpr]
  | .tyFam _ => rfl
  | .top => rfl
  | .bot => rfl
  | .and p q => by simp [sameExpr, sameExpr_refl p, sameExpr_refl q]
  | .or p q => by simp [sameExpr, sameExpr_refl p, sameExpr_refl q]
  | .imp p q => by simp [sameExpr, sameExpr_refl p, sameExpr_refl q]
  | .not p => by simp [sameExpr, sameExpr_refl p]
  | .eq a b => by simp [sameExpr, sameExpr_refl a, sameExpr_refl b]
  | .all A b => by simp [sameExpr, sameExpr_refl A, sameExpr_refl b]
  | .ex A b => by simp [sameExpr, sameExpr_refl A, sameExpr_refl b]

/-- **The computed equality is equality.** -/
theorem eq_of_sameExpr (a : AExpr) : ∀ b : AExpr, sameExpr a b = true → a = b := by
  induction a with
  | bvar i =>
      intro b h
      cases b <;> simp [sameExpr] at h
      rw [h]
  | univ => intro b h; cases b <;> first | rfl | simp [sameExpr] at h
  | prop => intro b h; cases b <;> first | rfl | simp [sameExpr] at h
  | base _ => intro b h; cases b <;> first | rfl | simp [sameExpr] at h
  | pi A B ihA ihB =>
      intro b h
      cases b <;> simp [sameExpr] at h
      rw [ihA _ h.1, ihB _ h.2]
  | lam A b ihA ihb =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [ihA _ h.1, ihb _ h.2]
  | app f a ihf iha =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [ihf _ h.1, iha _ h.2]
  | const τ c =>
      intro b h
      cases b <;> simp [sameExpr] at h
      exact const_eq_of_code _ _ h
  | tyFam _ => intro b h; cases b <;> first | rfl | simp [sameExpr] at h
  | top => intro b h; cases b <;> first | rfl | simp [sameExpr] at h
  | bot => intro b h; cases b <;> first | rfl | simp [sameExpr] at h
  | and p q ihp ihq =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [ihp _ h.1, ihq _ h.2]
  | or p q ihp ihq =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [ihp _ h.1, ihq _ h.2]
  | imp p q ihp ihq =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [ihp _ h.1, ihq _ h.2]
  | not p ihp =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [ihp _ h]
  | eq a b iha ihb =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [iha _ h.1, ihb _ h.2]
  | all A b ihA ihb =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [ihA _ h.1, ihb _ h.2]
  | ex A b ihA ihb =>
      intro c h
      cases c <;> simp [sameExpr] at h
      rw [ihA _ h.1, ihb _ h.2]

/-! ## The checker -/

/-- The type of a term in an arithmetic bubble, in normal form, when it has one. -/
def infer (plus : Bool) : List AExpr → AExpr → Option AExpr
  | Γ, .bvar i => (Γ[i]?).map fun A => Arith.norm plus (shiftN (i + 1) A)
  | _, .univ => none
  | _, .prop => some .univ
  | _, .base _ => some .univ
  | Γ, .pi A B =>
      match infer plus Γ A, infer plus (A :: Γ) B with
      | some .univ, some .univ => some .univ
      | _, _ => none
  | Γ, .lam A b =>
      match infer plus Γ A, infer plus (A :: Γ) b with
      | some .univ, some B => some (.pi (Arith.norm plus A) B)
      | _, _ => none
  | Γ, .app f a =>
      match infer plus Γ f, infer plus Γ a with
      | some (.pi A B), some A' =>
          if sameExpr A A' then some (Arith.norm plus (substAt 0 a B)) else none
      | _, _ => none
  | _, .const τ _ => some (Arith.norm plus (tyToExpr τ))
  | _, .tyFam b => some (.pi (.base b) .univ)
  | _, .top => some .prop
  | _, .bot => some .prop
  | Γ, .and p q =>
      match infer plus Γ p, infer plus Γ q with
      | some .prop, some .prop => some .prop
      | _, _ => none
  | Γ, .or p q =>
      match infer plus Γ p, infer plus Γ q with
      | some .prop, some .prop => some .prop
      | _, _ => none
  | Γ, .imp p q =>
      match infer plus Γ p, infer plus Γ q with
      | some .prop, some .prop => some .prop
      | _, _ => none
  | Γ, .not p =>
      match infer plus Γ p with
      | some .prop => some .prop
      | _ => none
  | Γ, .eq a b =>
      match infer plus Γ a, infer plus Γ b with
      | some A, some B => if sameExpr A B then some .prop else none
      | _, _ => none
  | Γ, .all A b =>
      match infer plus Γ A, infer plus (A :: Γ) b with
      | some .univ, some .prop => some .prop
      | _, _ => none
  | Γ, .ex A b =>
      match infer plus Γ A, infer plus (A :: Γ) b with
      | some .univ, some .prop => some .prop
      | _, _ => none

theorem lam_normDomain (plus : Bool) {Γ : List AExpr} {A b B : AExpr}
    (typedA : HasTypeInside (bubbleRules plus) Γ A Expr.univ)
    (typedB : HasTypeInside (bubbleRules plus) (A :: Γ) b B) :
    HasTypeInside (bubbleRules plus) Γ (Expr.lam A b) (Expr.pi (Arith.norm plus A) B) :=
  Typed.move (Typed.lam typedA typedB)
    (convertible_congr (fun z => Expr.pi z B) (fun _ _ step => .piDomain step)
      (norm_reachable plus A))

theorem app_normResult (plus : Bool) {Γ : List AExpr} {f a A B : AExpr}
    (typedF : HasTypeInside (bubbleRules plus) Γ f (Expr.pi A B))
    (typedA : HasTypeInside (bubbleRules plus) Γ a A) :
    HasTypeInside (bubbleRules plus) Γ (Expr.app f a) (Arith.norm plus (substAt 0 a B)) :=
  Typed.move (Typed.app typedF typedA) (norm_reachable plus _)

/-- **The checker is sound**: the type it returns is a type of the term in the bubble. -/
theorem infer_sound (plus : Bool) (e : AExpr) : ∀ (Γ : List AExpr) (T : AExpr),
    infer plus Γ e = some T → HasTypeInside (bubbleRules plus) Γ e T := by
  induction e with
  | bvar i =>
      intro Γ T h
      simp only [infer] at h
      cases lookup : Γ[i]? with
      | none => simp [lookup] at h
      | some A =>
          simp [lookup] at h
          rw [← h]
          exact Typed.move (Typed.var lookup) (norm_reachable plus _)
  | univ => intro Γ T h; simp [infer] at h
  | prop => intro Γ T h; simp only [infer] at h; cases h; exact Typed.prop
  | base b => intro Γ T h; simp only [infer] at h; cases h; exact Typed.base b
  | pi A B ihA ihB =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · cases h
        exact Typed.pi (ihA _ _ (by assumption)) (ihB _ _ (by assumption))
      · cases h
  | lam A b ihA ihb =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · cases h
        exact lam_normDomain plus (ihA _ _ (by assumption)) (ihb _ _ (by assumption))
      · cases h
  | app f a ihf iha =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · split at h
        · cases h
          have equal := eq_of_sameExpr _ _ (by assumption)
          subst equal
          exact app_normResult plus (ihf _ _ (by assumption)) (iha _ _ (by assumption))
        · cases h
      · cases h
  | const τ c =>
      intro Γ T h
      simp only [infer] at h
      cases h
      exact Typed.move (Typed.const τ c) (norm_reachable plus _)
  | tyFam b => intro Γ T h; simp only [infer] at h; cases h; exact Typed.tyFam b
  | top => intro Γ T h; simp only [infer] at h; cases h; exact Typed.top
  | bot => intro Γ T h; simp only [infer] at h; cases h; exact Typed.bot
  | and p q ihp ihq =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · cases h
        exact Typed.and (ihp _ _ (by assumption)) (ihq _ _ (by assumption))
      · cases h
  | or p q ihp ihq =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · cases h
        exact Typed.or (ihp _ _ (by assumption)) (ihq _ _ (by assumption))
      · cases h
  | imp p q ihp ihq =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · cases h
        exact Typed.imp (ihp _ _ (by assumption)) (ihq _ _ (by assumption))
      · cases h
  | not p ihp =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · cases h
        exact Typed.not (ihp _ _ (by assumption))
      · cases h
  | eq a b iha ihb =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · split at h
        · cases h
          have equal := eq_of_sameExpr _ _ (by assumption)
          subst equal
          exact Typed.eq (iha _ _ (by assumption)) (ihb _ _ (by assumption))
        · cases h
      · cases h
  | all A b ihA ihb =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · cases h
        exact Typed.all (ihA _ _ (by assumption)) (ihb _ _ (by assumption))
      · cases h
  | ex A b ihA ihb =>
      intro Γ T h
      simp only [infer] at h
      split at h
      · cases h
        exact Typed.ex (ihA _ _ (by assumption)) (ihb _ _ (by assumption))
      · cases h

/-- The checker finds the normal form of every syntax-directed type. -/
theorem infer_of_synth (plus : Bool) {Γ : List AExpr} {e A : AExpr}
    (synth : Synth (Convertible (bubbleRules plus)) Γ e A) :
    infer plus Γ e = some (Arith.norm plus A) := by
  induction synth with
  | var lookup => simp [infer, lookup]
  | base b => rfl
  | prop => rfl
  | @pi Γ A B S S' _ atA _ atB ihA ihB =>
      have domain : infer plus Γ A = some Expr.univ :=
        ihA.trans (congrArg some ((conv_iff_norm plus).mp atA))
      have codomain : infer plus (A :: Γ) B = some Expr.univ :=
        ihB.trans (congrArg some ((conv_iff_norm plus).mp atB))
      simp only [infer, domain, codomain, Arith.norm]
  | @lam Γ A b B S _ atA _ ihA ihb =>
      have domain : infer plus Γ A = some Expr.univ :=
        ihA.trans (congrArg some ((conv_iff_norm plus).mp atA))
      simp only [infer, domain, ihb, Arith.norm]
  | @app Γ f a F A A' B _ atF _ atA ihf iha =>
      have function : infer plus Γ f = some (Expr.pi (Arith.norm plus A) (Arith.norm plus B)) :=
        ihf.trans (congrArg some ((conv_iff_norm plus).mp atF))
      have argument : infer plus Γ a = some (Arith.norm plus A) :=
        iha.trans (congrArg some ((conv_iff_norm plus).mp atA))
      have result : Arith.norm plus (substAt 0 a (Arith.norm plus B)) =
          Arith.norm plus (substAt 0 a B) :=
        (conv_iff_norm plus).mp
          (convertible_substAt (bubbleRules_stable plus)
            (Relation.EqvGen.symm _ _ (norm_reachable plus B)) 0 a)
      simp only [infer, function, argument, sameExpr_refl, ↓reduceIte, result]
  | const τ c => rfl
  | tyFam b => rfl
  | top => rfl
  | bot => rfl
  | @and Γ p q P Q _ atP _ atQ ihp ihq =>
      have left : infer plus Γ p = some Expr.prop :=
        ihp.trans (congrArg some ((conv_iff_norm plus).mp atP))
      have right : infer plus Γ q = some Expr.prop :=
        ihq.trans (congrArg some ((conv_iff_norm plus).mp atQ))
      simp only [infer, left, right, Arith.norm]
  | @or Γ p q P Q _ atP _ atQ ihp ihq =>
      have left : infer plus Γ p = some Expr.prop :=
        ihp.trans (congrArg some ((conv_iff_norm plus).mp atP))
      have right : infer plus Γ q = some Expr.prop :=
        ihq.trans (congrArg some ((conv_iff_norm plus).mp atQ))
      simp only [infer, left, right, Arith.norm]
  | @imp Γ p q P Q _ atP _ atQ ihp ihq =>
      have left : infer plus Γ p = some Expr.prop :=
        ihp.trans (congrArg some ((conv_iff_norm plus).mp atP))
      have right : infer plus Γ q = some Expr.prop :=
        ihq.trans (congrArg some ((conv_iff_norm plus).mp atQ))
      simp only [infer, left, right, Arith.norm]
  | @not Γ p P _ atP ihp =>
      have inner : infer plus Γ p = some Expr.prop :=
        ihp.trans (congrArg some ((conv_iff_norm plus).mp atP))
      simp only [infer, inner, Arith.norm]
  | @eq Γ a b A B _ _ same iha ihb =>
      have right : infer plus Γ b = some (Arith.norm plus A) :=
        ihb.trans (congrArg some ((conv_iff_norm plus).mp same).symm)
      simp only [infer, iha, right, sameExpr_refl, ↓reduceIte, Arith.norm]
  | @all Γ A b S P _ atA _ atP ihA ihb =>
      have domain : infer plus Γ A = some Expr.univ :=
        ihA.trans (congrArg some ((conv_iff_norm plus).mp atA))
      have body : infer plus (A :: Γ) b = some Expr.prop :=
        ihb.trans (congrArg some ((conv_iff_norm plus).mp atP))
      simp only [infer, domain, body, Arith.norm]
  | @ex Γ A b S P _ atA _ atP ihA ihb =>
      have domain : infer plus Γ A = some Expr.univ :=
        ihA.trans (congrArg some ((conv_iff_norm plus).mp atA))
      have body : infer plus (A :: Γ) b = some Expr.prop :=
        ihb.trans (congrArg some ((conv_iff_norm plus).mp atP))
      simp only [infer, domain, body, Arith.norm]

/-- **The checker is complete**: it returns the normal form of every type of the term. -/
theorem infer_complete (plus : Bool) {Γ : List AExpr} {e T : AExpr}
    (typed : HasTypeInside (bubbleRules plus) Γ e T) :
    infer plus Γ e = some (Arith.norm plus T) := by
  obtain ⟨A, synth, moved⟩ := synth_of_typed (arith_coherent plus) typed
  rw [infer_of_synth plus synth, (conv_iff_norm plus).mp moved]

/-- **Typing in an arithmetic bubble is decided by the checker.** -/
theorem typed_iff_infer (plus : Bool) {Γ : List AExpr} {e T : AExpr} :
    HasTypeInside (bubbleRules plus) Γ e T ↔ infer plus Γ e = some (Arith.norm plus T) := by
  constructor
  · exact infer_complete plus
  · intro found
    exact Typed.move (infer_sound plus e Γ _ found)
      (Relation.EqvGen.symm _ _ (norm_reachable plus T))

/-- Having a type in an arithmetic bubble is decided by the checker. -/
theorem typable_iff (plus : Bool) {Γ : List AExpr} {e : AExpr} :
    (∃ T, HasTypeInside (bubbleRules plus) Γ e T) ↔ (infer plus Γ e).isSome = true := by
  constructor
  · rintro ⟨T, typed⟩
    simp [infer_complete plus typed]
  · intro found
    cases result : infer plus Γ e with
    | none => simp [result] at found
    | some T => exact ⟨T, infer_sound plus e Γ T result⟩

/-- Whether a term has a given type in an arithmetic bubble, computed. -/
def check (plus : Bool) (Γ : List AExpr) (e T : AExpr) : Bool :=
  match infer plus Γ e with
  | some found => sameExpr found (Arith.norm plus T)
  | none => false

/-- **The computed check is typing with the conversion rule at every node.** -/
theorem typed_iff_check (plus : Bool) {Γ : List AExpr} {e T : AExpr} :
    HasTypeInside (bubbleRules plus) Γ e T ↔ check plus Γ e T = true := by
  constructor
  · intro typed
    simp [check, infer_complete plus typed, sameExpr_refl]
  · intro checked
    cases found : infer plus Γ e with
    | none => simp [check, found] at checked
    | some T₀ =>
        have same : sameExpr T₀ (Arith.norm plus T) = true := by
          simpa [check, found] using checked
        exact (typed_iff_infer plus).mpr
          (found.trans (congrArg some (eq_of_sameExpr _ _ same)))

instance (plus : Bool) (Γ : List AExpr) (e T : AExpr) :
    Decidable (HasTypeInside (bubbleRules plus) Γ e T) :=
  decidable_of_iff _ (typed_iff_check plus).symm

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleTypingInside.Controls

/-- **The checker finds the conversion**: with `f : Vec (n + 0) → nat` and `v : Vec n`, the
application `f v` is typed at `nat` in the bubble of the recursion equations, by computation. -/
theorem application_checked :
    HasTypeInside (bubbleRules false) appContext (Expr.app (bvar 0) (bvar 1)) natType := by
  decide

/-- The context `n : nat, v : Vec n, f : Vec (0 + n) → nat`, newest first. -/
def zeroAddContext : List AExpr :=
  [Expr.pi (vec (addE zeroE (bvar 1))) natType, vec (bvar 0), natType]

/-- **The recursion equations do not convert `Vec (0 + n)` with `Vec n`**: the checker returns
no type for `f v`. -/
theorem zeroAdd_refused : infer false zeroAddContext (Expr.app (bvar 0) (bvar 1)) = none :=
  rfl

/-- **The bubble that also declares the left unit does**: there `f v` is typed at `nat`. -/
theorem zeroAdd_checked_in_plus :
    HasTypeInside (bubbleRules true) zeroAddContext (Expr.app (bvar 0) (bvar 1)) natType := by
  decide

/-- **So `f v` has no type in the bubble of the recursion equations**, with the conversion rule
at every node. -/
theorem zeroAdd_not_typable :
    ¬ ∃ T, HasTypeInside (bubbleRules false) zeroAddContext (Expr.app (bvar 0) (bvar 1)) T := by
  intro typable
  have found := (typable_iff false).mp typable
  rw [zeroAdd_refused] at found
  cases found

/-- A term that is not typed is refused: `0 0` has no type. -/
theorem zero_applied_refused :
    ¬ ∃ T, HasTypeInside (bubbleRules false) [] (Expr.app zeroE zeroE) T := by
  intro typable
  have found := (typable_iff false).mp typable
  cases found

end Controls

/-! ## Axiom audit -/

#print axioms eq_of_sameExpr
#print axioms infer_sound
#print axioms infer_of_synth
#print axioms infer_complete
#print axioms typed_iff_infer
#print axioms typable_iff
#print axioms typed_iff_check
#print axioms Controls.application_checked
#print axioms Controls.zeroAdd_refused
#print axioms Controls.zeroAdd_checked_in_plus
#print axioms Controls.zeroAdd_not_typable
#print axioms Controls.zero_applied_refused

end Mettapedia.TypeTheory.BubbleArithChecker
