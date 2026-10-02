import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Strong
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion.Confluence
import Mettapedia.Algorithms.WellFoundedServices.Capabilities

/-!
# The strong variant diverges at an abstract accessibility proof

In the strong variant the recursor unfolds definitionally at every
accessibility proof. Take a relation `R` with a reflexivity proof
`ρ : Π x. holds (R x x)`, a point `a` and an abstract proof
`q : holds (acc R a)`, and the step function `loop := λ x z. z x (ρ x)`, which
calls the recursion at its own argument. Then

`rec P R loop a q ⟶ loop a (λ y r. rec P R loop y (inv R a q y r))
  ⟶ (λ z. z a (ρ a)) (λ y r. …) ⟶ (λ y r. …) a (ρ a)
  ⟶ (λ r. rec P R loop a (inv R a q a r)) (ρ a) ⟶ rec P R loop a (inv R a q a (ρ a))`,

one unfolding and four β-steps back to the recursor at the same point, with the
accessibility proof replaced by its inversion (`loop_cycle`). The term is typed
in the strong variant of every accessibility package (`loop_typed`), and no
sequence of steps from it reaches a normal form (`loop_no_normal_form`): the
terms reachable from it are described by `Looping`, which is closed under every
step of the strong variant (`Looping.step_closed`) and each of whose terms has a
step (`Looping.has_step`).

**A budgeted checker.** A weak-head evaluator (`whStep`) contracts a β-redex or
pair projection at the head, else asks a root oracle, else steps inside the head
position. Run for a budget with `runFor` (`whCheck`), it is incomplete at every
budget on the loop in the strong variant, for every sound oracle that unfolds
the recursor (`loop_whCheck_incomplete`), while in the propositional variant,
where the recursor is inert, the same evaluator establishes the loop's
weak-head normal form at once (`loop_whCheck_established`). Running out of
budget is never a refutation (`runFor_ne_refuted`).

**The propositional variant decides the loop's conversion problem**, and
negatively: the unfolding's recursive call carries the inverted accessibility
proof, which reduces to a spine headed by `q` with four arguments, so the loop
is not convertible to its unfolding (`loop_inert_not_conv`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Normalization (DecoderStep)
open Presentation.ConstructorSystem (spineHead)
open Confluence (varHead spineHead_of_varHead)
open Mettapedia.Algorithms.WellFoundedServices (runFor runFor_ne_refuted)
open Mettapedia.TypeTheory.AuthorityTheory (Outcome)

variable {Head : Type}

namespace Signature

variable (S : Signature Head)

/-- A step of the strong variant. -/
abbrev StrongStep {n : Nat} (t u : Tm Head n) : Prop :=
  Step S.strongRules.headEq t u S.strongRules.computation

/-- The base's root steps start at spines headed by constants other than the
recursor. -/
def BaseSpines : Prop :=
  ∀ {n : Nat} {l r : Tm Head n}, S.base.computation.step l r →
    ∃ c k, c ≠ S.recursor ∧ spineHead l = some (c, k)

end Signature

/-! ## Root steps of the strong variant -/

namespace Signature

variable {S : Signature Head}

theorem holds_ne_recursor (L : S.Laws) : S.codes.holds ≠ S.recursor := by
  intro same
  have h := L.recursor_fresh.1
  rw [← same, Codes.codeType_holds _ L.universes.codes.holds_apart] at h
  cases h

/-- Every root step of the strong variant starts at a constant spine. -/
theorem strong_root_spine (hb : S.BaseSpines) {n : Nat} {l r : Tm Head n}
    (step : S.strongRules.computation.step l r) : ∃ c k, spineHead l = some (c, k) := by
  rcases step with (base | unfold) | decoder
  · obtain ⟨c, k, -, h⟩ := hb base
    exact ⟨c, k, h⟩
  · obtain ⟨P, R, F, a, q, rfl, -⟩ := S.unfoldComputation_step unfold
    exact ⟨_, _, rfl⟩
  · cases decoder <;> exact ⟨_, _, rfl⟩

/-- A root step of the strong variant at a spine headed by the recursor is the
unfolding of a full application. -/
theorem strong_root_rec (L : S.Laws) (hb : S.BaseSpines) {n : Nat} {l r : Tm Head n}
    (step : S.strongRules.computation.step l r) {k : Nat}
    (head : spineHead l = some (S.recursor, k)) :
    ∃ P R F a q, l = S.recSpine P R F a q ∧ r = S.unfolding P R F a q := by
  rcases step with (base | unfold) | decoder
  · obtain ⟨c, k', ne, h⟩ := hb base
    rw [head] at h
    cases h
    exact absurd rfl ne
  · exact S.unfoldComputation_step unfold
  · exfalso
    cases decoder <;>
    · simp only [spineHead, Option.map_some, Option.some.injEq, Prod.mk.injEq] at head
      exact holds_ne_recursor L head.1

/-- No root step at a spine headed by the recursor with other than five
arguments. -/
theorem no_strong_root_partial (L : S.Laws) (hb : S.BaseSpines) {n : Nat} {l r : Tm Head n}
    {k : Nat} (head : spineHead l = some (S.recursor, k)) (ne : k ≠ 5) :
    ¬ S.strongRules.computation.step l r := by
  intro step
  obtain ⟨P, R, F, a, q, rfl, -⟩ := strong_root_rec L hb step head
  simp only [recSpine, spineHead, Option.map_some, Option.some.injEq, Prod.mk.injEq] at head
  exact ne head.2.symm

theorem no_strong_root_of_none (hb : S.BaseSpines) {n : Nat} {l r : Tm Head n}
    (head : spineHead l = none) : ¬ S.strongRules.computation.step l r := by
  intro step
  obtain ⟨c, k, h⟩ := strong_root_spine hb step
  rw [head] at h
  cases h

/-- A step from a full application of the recursor is its unfolding or a step
of one argument. -/
theorem step_recSpine (L : S.Laws) (hb : S.BaseSpines) {n : Nat} {P R F x q u : Tm Head n}
    (step : S.StrongStep (S.recSpine P R F x q) u) :
    u = S.unfolding P R F x q ∨
    (∃ P', S.StrongStep P P' ∧ u = S.recSpine P' R F x q) ∨
    (∃ R', S.StrongStep R R' ∧ u = S.recSpine P R' F x q) ∨
    (∃ F', S.StrongStep F F' ∧ u = S.recSpine P R F' x q) ∨
    (∃ x', S.StrongStep x x' ∧ u = S.recSpine P R F x' q) ∨
    (∃ q', S.StrongStep q q' ∧ u = S.recSpine P R F x q') := by
  unfold Signature.StrongStep at step
  unfold Signature.recSpine at step ⊢
  cases step with
  | root rootStep =>
      obtain ⟨P', R', F', a', q', same, rfl⟩ := strong_root_rec L hb rootStep rfl
      simp only [recSpine, Tm.app.injEq] at same
      obtain ⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := same
      exact .inl rfl
  | congAppFun s4 =>
      cases s4 with
      | root rootStep => exact absurd rootStep (no_strong_root_partial L hb (k := 4) rfl (by decide))
      | congAppFun s3 =>
          cases s3 with
          | root rootStep =>
              exact absurd rootStep (no_strong_root_partial L hb (k := 3) rfl (by decide))
          | congAppFun s2 =>
              cases s2 with
              | root rootStep =>
                  exact absurd rootStep (no_strong_root_partial L hb (k := 2) rfl (by decide))
              | congAppFun s1 =>
                  cases s1 with
                  | root rootStep =>
                      exact absurd rootStep (no_strong_root_partial L hb (k := 1) rfl (by decide))
                  | congAppFun s0 =>
                      cases s0 with
                      | root rootStep =>
                          exact absurd rootStep (no_strong_root_partial L hb (k := 0) rfl (by decide))
                  | congAppArg sP => exact .inr (.inl ⟨_, sP, rfl⟩)
              | congAppArg sR => exact .inr (.inr (.inl ⟨_, sR, rfl⟩))
          | congAppArg sF => exact .inr (.inr (.inr (.inl ⟨_, sF, rfl⟩)))
      | congAppArg sx => exact .inr (.inr (.inr (.inr (.inl ⟨_, sx, rfl⟩))))
  | congAppArg sq => exact .inr (.inr (.inr (.inr (.inr ⟨_, sq, rfl⟩))))

end Signature

/-! ## The terms reachable from the loop -/

/-- A step function of the shape `λ x z. z x t`: it calls the recursion at its
own argument. -/
def LoopStep {n : Nat} (F : Tm Head n) : Prop :=
  ∃ t : Tm Head (n + 2), F = .lam (.lam (.app (.app (.var 0) (.var 1)) t))

theorem LoopStep.rename {n m : Nat} {F : Tm Head n} (hF : LoopStep F) (ρ : Ren n m) :
    LoopStep (rename ρ F) := by
  obtain ⟨t, rfl⟩ := hF
  exact ⟨Presentation.rename (liftRen (liftRen ρ)) t, rfl⟩

theorem LoopStep.subst {n m : Nat} {F : Tm Head n} (hF : LoopStep F) (σ : Sub Head n m) :
    LoopStep (subst σ F) := by
  obtain ⟨t, rfl⟩ := hF
  exact ⟨Presentation.subst (liftSub (liftSub σ)) t, rfl⟩

/-- The terms reachable from `rec P R F x q` with a looping step function: the
recursor, its unfolding, and the three terms between the unfolding and the
next recursive call; the recursive call, under its two binders, is again
reachable. -/
inductive Looping (S : Signature Head) : {n : Nat} → Tm Head n → Prop
  | start {n : Nat} (P R F x q : Tm Head n) : LoopStep F → Looping S (S.recSpine P R F x q)
  | unfolded {n : Nat} (F x : Tm Head n) (B : Tm Head (n + 2)) : LoopStep F → Looping S B →
      Looping S (.app (.app F x) (.lam (.lam B)))
  | halfway {n : Nat} (X t : Tm Head (n + 1)) (B : Tm Head (n + 2)) : Looping S B →
      Looping S (.app (.lam (.app (.app (.var 0) X) t)) (.lam (.lam B)))
  | calling {n : Nat} (x t : Tm Head n) (B : Tm Head (n + 2)) : Looping S B →
      Looping S (.app (.app (.lam (.lam B)) x) t)
  | called {n : Nat} (t : Tm Head n) (B : Tm Head (n + 1)) : Looping S B →
      Looping S (.app (.lam B) t)

namespace Looping

variable {S : Signature Head}

/-- Substitution keeps a term reachable. -/
theorem subst {n : Nat} {t : Tm Head n} (h : Looping S t) :
    ∀ {m : Nat} (σ : Sub Head n m), Looping S (Presentation.subst σ t) := by
  induction h with
  | start P R F x q hF =>
      intro m σ
      rw [Signature.subst_recSpine]
      exact .start _ _ _ _ _ (hF.subst σ)
  | unfolded F x B hF _ ih =>
      intro m σ
      exact .unfolded _ _ _ (hF.subst σ) (ih (liftSub (liftSub σ)))
  | halfway X t B _ ih =>
      intro m σ
      exact .halfway _ _ _ (ih (liftSub (liftSub σ)))
  | calling x t B _ ih =>
      intro m σ
      exact .calling _ _ _ (ih (liftSub (liftSub σ)))
  | called t B _ ih =>
      intro m σ
      exact .called _ _ (ih (liftSub σ))

end Looping

namespace Signature

variable {S : Signature Head}

/-- A looping step function steps only inside the argument of its body. -/
theorem LoopStep.step (hb : S.BaseSpines) {n : Nat} {F F' : Tm Head n}
    (hF : LoopStep F) (step : S.StrongStep F F') : LoopStep F' := by
  obtain ⟨t, rfl⟩ := hF
  unfold Signature.StrongStep at step
  cases step with
  | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
  | congLam s1 =>
      cases s1 with
      | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
      | congLam s2 =>
          cases s2 with
          | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
          | congAppFun s3 =>
              cases s3 with
              | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
              | congAppFun s4 =>
                  cases s4 with
                  | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
              | congAppArg s4 =>
                  cases s4 with
                  | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
          | congAppArg st => exact ⟨_, rfl⟩

/-- Steps under two abstractions are steps of the body. -/
theorem step_lam_lam (hb : S.BaseSpines) {n : Nat} {B : Tm Head (n + 2)} {u : Tm Head n}
    (step : S.StrongStep (.lam (.lam B)) u) :
    ∃ B', S.StrongStep B B' ∧ u = .lam (.lam B') := by
  unfold Signature.StrongStep at step ⊢
  cases step with
  | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
  | congLam s1 =>
      cases s1 with
      | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
      | congLam s2 => exact ⟨_, s2, rfl⟩

end Signature

namespace Looping

open Signature

variable {S : Signature Head}

/-- **Every step keeps a term reachable.** -/
theorem step_closed (L : S.Laws) (hb : S.BaseSpines) {n : Nat} {t : Tm Head n}
    (h : Looping S t) : ∀ {u : Tm Head n}, S.StrongStep t u → Looping S u := by
  induction h with
  | start P R F x q hF =>
      intro u step
      rcases step_recSpine L hb step with rfl | ⟨P', _, rfl⟩ | ⟨R', _, rfl⟩ | ⟨F', sF, rfl⟩ |
          ⟨x', _, rfl⟩ | ⟨q', _, rfl⟩
      · exact .unfolded _ _ _ hF (.start _ _ _ _ _ ((hF.rename wk).rename wk))
      · exact .start _ _ _ _ _ hF
      · exact .start _ _ _ _ _ hF
      · exact .start _ _ _ _ _ (LoopStep.step hb hF sF)
      · exact .start _ _ _ _ _ hF
      · exact .start _ _ _ _ _ hF
  | unfolded F x B hF hB ih =>
      intro u step
      obtain ⟨t, rfl⟩ := hF
      unfold Signature.StrongStep at step
      cases step with
      | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
      | congAppFun s =>
          cases s with
          | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
          | betaPi body a => exact .halfway _ _ _ hB
          | congAppFun sF => exact .unfolded _ _ _ (LoopStep.step hb ⟨t, rfl⟩ sF) hB
          | congAppArg _ => exact .unfolded _ _ _ ⟨t, rfl⟩ hB
      | congAppArg s =>
          obtain ⟨B', sB, rfl⟩ := step_lam_lam hb s
          exact .unfolded _ _ _ ⟨t, rfl⟩ (ih sB)
  | halfway X t B hB ih =>
      intro u step
      unfold Signature.StrongStep at step
      cases step with
      | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
      | betaPi body a => exact .calling _ _ _ hB
      | congAppFun s =>
          cases s with
          | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
          | congLam s1 =>
              cases s1 with
              | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
              | congAppFun s2 =>
                  cases s2 with
                  | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
                  | congAppFun s3 =>
                      cases s3 with
                      | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
                  | congAppArg _ => exact .halfway _ _ _ hB
              | congAppArg _ => exact .halfway _ _ _ hB
      | congAppArg s =>
          obtain ⟨B', sB, rfl⟩ := step_lam_lam hb s
          exact .halfway _ _ _ (ih sB)
  | calling x t B hB ih =>
      intro u step
      unfold Signature.StrongStep at step
      cases step with
      | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
      | congAppFun s =>
          cases s with
          | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
          | betaPi body a => exact .called _ _ (hB.subst _)
          | congAppFun s1 =>
              obtain ⟨B', sB, rfl⟩ := step_lam_lam hb s1
              exact .calling _ _ _ (ih sB)
          | congAppArg _ => exact .calling _ _ _ hB
      | congAppArg _ => exact .calling _ _ _ hB
  | called t B hB ih =>
      intro u step
      unfold Signature.StrongStep at step
      cases step with
      | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
      | betaPi body a => exact hB.subst _
      | congAppFun s =>
          cases s with
          | root rootStep => exact absurd rootStep (no_strong_root_of_none hb rfl)
          | congLam sB => exact .called _ _ (ih sB)
      | congAppArg _ => exact .called _ _ hB

/-- **Every reachable term has a step.** -/
theorem has_step {n : Nat} {t : Tm Head n} (h : Looping S t) : ∃ u, S.StrongStep t u := by
  cases h with
  | start P R F x q _ => exact ⟨_, .root (S.strongRules_step P R F x q)⟩
  | unfolded F x B hF _ =>
      obtain ⟨t, rfl⟩ := hF
      exact ⟨_, .congAppFun (.betaPi _ _)⟩
  | halfway X t B _ => exact ⟨_, .betaPi _ _⟩
  | calling x t B _ => exact ⟨_, .congAppFun (.betaPi _ _)⟩
  | called t B _ => exact ⟨_, .betaPi _ _⟩

end Looping

namespace Signature

variable {S : Signature Head}

/-- **No normal form**: every term reachable from `rec P R F x q` with a looping
step function has a further step of the strong variant. -/
theorem loop_no_normal_form (L : S.Laws) (hb : S.BaseSpines) {n : Nat} {P R F x q u : Tm Head n}
    (hF : LoopStep F) (steps : Relation.ReflTransGen S.StrongStep (S.recSpine P R F x q) u) :
    ∃ v, S.StrongStep u v := by
  have reachable : Looping S u := by
    induction steps with
    | refl => exact .start _ _ _ _ _ hF
    | tail _ step ih => exact ih.step_closed L hb step
  exact reachable.has_step

end Signature

/-! ## The loop, typed -/

namespace Signature

variable (S : Signature Head)

/-- `Π x. holds (R x x)`, over `P R`: reflexivity of the relation. -/
def reflType : Tm Head 2 :=
  .pi (liftClosed S.carrier) (S.codes.holdsOf (CodeNames.relOf (.var 1) (.var 0) (.var 0)))

/-- The loop's telescope: a motive `P`, a relation `R`, a reflexivity proof
`ρ`, a point `a` and an abstract accessibility proof `q : holds (acc R a)`. -/
def loopTelescope : Ctx Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil S.motiveType) (S.relType S.carrier)) S.reflType)
    (liftClosed S.carrier)) (S.codes.holdsOf (S.acc (.var 2) (.var 0)))

/-- The looping step `λ x z. z x (ρ x)`, over the telescope. -/
def loopStep : Tm Head 5 := .lam (.lam (.app (.app (.var 0) (.var 1)) (.app (.var 4) (.var 1))))

/-- The loop: `rec P R (λ x z. z x (ρ x)) a q`. -/
def loopTerm : Tm Head 5 := S.recSpine (.var 4) (.var 3) loopStep (.var 1) (.var 0)

/-- Where the loop returns after one unfolding and four β-steps:
`rec P R (λ x z. z x (ρ x)) a (inv R a q a (ρ a))`. -/
def loopReturn : Tm Head 5 :=
  S.recSpine (.var 4) (.var 3) loopStep (.var 1)
    (S.invSpine (.var 3) (.var 1) (.var 0) (.var 1) (.app (.var 2) (.var 1)))

theorem loopStep_loops : LoopStep (loopStep (Head := Head)) := ⟨_, rfl⟩

/-- The loop starts the reachable terms. -/
theorem loopTerm_looping : Looping S S.loopTerm := .start _ _ _ _ _ loopStep_loops

/-- **The cycle.** One unfolding and four β-steps return to the recursor at the
same point, with the accessibility proof replaced by its inversion. -/
theorem loop_cycle : ∃ t₁ t₂ t₃ t₄ : Tm Head 5,
    S.StrongStep S.loopTerm t₁ ∧ S.StrongStep t₁ t₂ ∧ S.StrongStep t₂ t₃ ∧
      S.StrongStep t₃ t₄ ∧ S.StrongStep t₄ S.loopReturn :=
  ⟨_, _, _, _, .root (S.strongRules_step _ _ _ _ _), .congAppFun (.betaPi _ _), .betaPi _ _,
    .congAppFun (.betaPi _ _), .betaPi _ _⟩

/-- The loop's return is again a full application of the recursor with the
looping step. -/
theorem loopReturn_looping : Looping S S.loopReturn := .start _ _ _ _ _ loopStep_loops

variable {S}

theorem loopTelescope_vars {B : Rules Head} :
    Typed (S.toCodeNames.rules B) S.loopTelescope (.var 4) S.motiveType ∧
    Typed (S.toCodeNames.rules B) S.loopTelescope (.var 3) (S.relType S.carrier) ∧
    Typed (S.toCodeNames.rules B) S.loopTelescope (.var 2)
      (.pi (liftClosed S.carrier) (S.codes.holdsOf (CodeNames.relOf (.var 4) (.var 0) (.var 0)))) ∧
    Typed (S.toCodeNames.rules B) S.loopTelescope (.var 1) (liftClosed S.carrier) ∧
    Typed (S.toCodeNames.rules B) S.loopTelescope (.var 0)
      (S.codes.holdsOf (S.acc (.var 3) (.var 1))) := by
  let Γ1 : Ctx Head 1 := .snoc .nil S.motiveType
  let Γ2 : Ctx Head 2 := .snoc Γ1 (S.relType S.carrier)
  let Γ3 : Ctx Head 3 := .snoc Γ2 S.reflType
  let Γ4 : Ctx Head 4 := .snoc Γ3 (liftClosed S.carrier)
  have hP1 : Typed (S.toCodeNames.rules B) Γ1 (.var 0) S.motiveType := by
    have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := .nil) (X := S.motiveType)
    simpa only [Signature.rename_motiveType] using h
  have hR2 : Typed (S.toCodeNames.rules B) Γ2 (.var 0) (S.relType S.carrier) := by
    have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := Γ1)
      (X := S.relType S.carrier)
    simpa only [CodeNames.rename_relType] using h
  have hρ3 := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := Γ2) (X := S.reflType)
  have ha4 := CodeNames.Laws.var_carrier (C := S.toCodeNames) (B := B) (A := S.carrier) (Γ := Γ3)
  have hq5 := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := Γ4)
    (X := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := (((hP1.weaken (extension := S.relType S.carrier)).weaken (extension := S.reflType)).weaken
      (extension := liftClosed S.carrier)).weaken (extension := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
    simp only [Signature.rename_motiveType, Presentation.rename, wk, Fin.reduceSucc,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h
    exact h
  · have h := ((hR2.weaken (extension := S.reflType)).weaken (extension := liftClosed S.carrier)).weaken
      (extension := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
    simp only [CodeNames.rename_relType, Presentation.rename, wk, Fin.reduceSucc,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h
    exact h
  · have h := (hρ3.weaken (extension := liftClosed S.carrier)).weaken
      (extension := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
    simp only [reflType, Presentation.rename, rename_liftClosed] at h
    exact h
  · have h := ha4.weaken (extension := S.codes.holdsOf (S.acc (.var 2) (.var 0)))
    simp only [rename_liftClosed, Presentation.rename, wk, Fin.reduceSucc] at h
    exact h
  · simp only [Presentation.rename, CodeNames.rename_acc] at hq5
    exact hq5

namespace Universes

variable {B : Rules Head} (U : S.Universes B)
include U

/-- **The looping step is a step function** for the motive and the relation of
the telescope. -/
theorem loopStep_typed :
    Typed (S.toCodeNames.rules B) S.loopTelescope loopStep (S.stepTypeOf (.var 4) (.var 3)) := by
  have LC := U.codes
  obtain ⟨hP, hR, hρ, -, -⟩ := loopTelescope_vars (S := S) (B := B)
  let A : Tm Head 6 := liftClosed S.carrier
  let Γx : Ctx Head 6 := .snoc S.loopTelescope (liftClosed S.carrier)
  -- the variables at depth six
  have hP6 : Typed (S.toCodeNames.rules B) Γx (.var 5) S.motiveType := by
    simpa only [Signature.rename_motiveType, Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using hP.weaken (extension := liftClosed S.carrier)
  have hR6 : Typed (S.toCodeNames.rules B) Γx (.var 4) (S.relType S.carrier) := by
    simpa only [CodeNames.rename_relType, Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using hR.weaken (extension := liftClosed S.carrier)
  have hx6 : Typed (S.toCodeNames.rules B) Γx (.var 0) (liftClosed S.carrier) :=
    CodeNames.Laws.var_carrier
  -- the type `Z` of the recursive call, at depth six
  let rel7 : Tm Head 7 := S.codes.holdsOf (CodeNames.relOf (.var 5) (.var 0) (.var 1))
  let Z : Tm Head 6 := .pi (liftClosed S.carrier) (.pi rel7 (.app (.var 7) (.var 1)))
  have hR7 : Typed (S.toCodeNames.rules B) (.snoc Γx (liftClosed S.carrier)) (.var 5)
      (S.relType S.carrier) := by
    simpa only [CodeNames.rename_relType, Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using hR6.weaken (extension := liftClosed S.carrier)
  have hy7 : Typed (S.toCodeNames.rules B) (.snoc Γx (liftClosed S.carrier)) (.var 0)
      (liftClosed S.carrier) := CodeNames.Laws.var_carrier
  have hx7 : Typed (S.toCodeNames.rules B) (.snoc Γx (liftClosed S.carrier)) (.var 1)
      (liftClosed S.carrier) := by
    simpa only [rename_liftClosed, Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using hx6.weaken (extension := liftClosed S.carrier)
  have hrel7 : Typed (S.toCodeNames.rules B) (.snoc Γx (liftClosed S.carrier)) rel7
      (.head S.codes.proofs) := LC.holdsOf_typed (CodeNames.Laws.relOf_typed hR7 hy7 hx7)
  have hP8 : Typed (S.toCodeNames.rules B) (.snoc (.snoc Γx (liftClosed S.carrier)) rel7) (.var 7)
      S.motiveType := by
    have h := (hP6.weaken (extension := liftClosed S.carrier)).weaken (extension := rel7)
    simpa only [Signature.rename_motiveType, Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using h
  have hy8 : Typed (S.toCodeNames.rules B) (.snoc (.snoc Γx (liftClosed S.carrier)) rel7) (.var 1)
      (liftClosed S.carrier) := by
    simpa only [rename_liftClosed, Presentation.rename, wk, Fin.reduceSucc, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using hy7.weaken (extension := rel7)
  have hZ : Typed (S.toCodeNames.rules B) Γx Z (.head S.motive) :=
    U.piMotive (U.toMotive LC.carrier_typed')
      (U.piMotive (U.toMotive hrel7) (Signature.motiveApp_typed hP8 hy8))
  -- the body `z x (ρ x)` at depth seven
  have hz7 : Typed (S.toCodeNames.rules B) (.snoc Γx Z) (.var 0)
      (.pi (liftClosed S.carrier) (.pi (S.codes.holdsOf (CodeNames.relOf (.var 6) (.var 0) (.var 2)))
        (.app (.var 8) (.var 1)))) := by
    have h := CodeNames.Laws.var_zero (C := S.toCodeNames) (B := B) (Γ := Γx) (X := Z)
    simp only [Z, rel7, Presentation.rename, rename_liftClosed] at h
    exact h
  have hx7' : Typed (S.toCodeNames.rules B) (.snoc Γx Z) (.var 1) (liftClosed S.carrier) := by
    have h := hx6.weaken (extension := Z)
    simp only [rename_liftClosed, Presentation.rename] at h
    exact h
  have hρ7 : Typed (S.toCodeNames.rules B) (.snoc Γx Z) (.var 4)
      (.pi (liftClosed S.carrier) (S.codes.holdsOf (CodeNames.relOf (.var 6) (.var 0) (.var 0)))) := by
    have h := (hρ.weaken (extension := liftClosed S.carrier)).weaken (extension := Z)
    simp only [Presentation.rename, rename_liftClosed] at h
    exact h
  have hzx : Typed (S.toCodeNames.rules B) (.snoc Γx Z) (.app (.var 0) (.var 1))
      (.pi (S.codes.holdsOf (CodeNames.relOf (.var 5) (.var 1) (.var 1))) (.app (.var 7) (.var 2))) := by
    have h := Derivable.appElim hz7 hx7'
    simp only [inst0, Presentation.subst] at h
    exact h
  have hρx : Typed (S.toCodeNames.rules B) (.snoc Γx Z) (.app (.var 4) (.var 1))
      (S.codes.holdsOf (CodeNames.relOf (.var 5) (.var 1) (.var 1))) := by
    have h := Derivable.appElim hρ7 hx7'
    simp only [inst0, Presentation.subst] at h
    exact h
  have body : Typed (S.toCodeNames.rules B) (.snoc Γx Z)
      (.app (.app (.var 0) (.var 1)) (.app (.var 4) (.var 1))) (.app (.var 6) (.var 1)) := by
    have h := Derivable.appElim hzx hρx
    simp only [inst0, Presentation.subst] at h
    exact h
  -- the two abstractions
  have hPx : Typed (S.toCodeNames.rules B) (.snoc Γx Z) (.app (.var 6) (.var 1)) (.head S.motive) := by
    have h := hP6.weaken (extension := Z)
    simp only [Signature.rename_motiveType, Presentation.rename] at h
    exact Signature.motiveApp_typed h hx7'
  have hInner : Typed (S.toCodeNames.rules B) Γx (.pi Z (.app (.var 6) (.var 1))) (.head S.motive) :=
    U.piMotive hZ hPx
  have hOuter : Typed (S.toCodeNames.rules B) S.loopTelescope
      (.pi (liftClosed S.carrier) (.pi Z (.app (.var 6) (.var 1)))) (.head S.motive) :=
    U.piMotive (U.toMotive LC.carrier_typed') hInner
  rw [Signature.stepTypeOf_eq]
  simp only [Presentation.rename]
  exact .lamIntro hOuter U.motive_universe (.lamIntro hInner U.motive_universe body)

end Universes

/-- **The loop is typed** in the strong variant, at `P a`. -/
theorem loop_typed (L : S.Laws) :
    Typed S.strongRules S.loopTelescope S.loopTerm (.app (.var 4) (.var 1)) := by
  have U : S.Universes S.accBase := L.universes.mono L.base_accBase
  obtain ⟨hP, hR, -, ha, hq⟩ := loopTelescope_vars (S := S) (B := S.accBase)
  exact S.derivable_rules_strong
    (U.rec_apply (Signature.rules_constantType_recursor L) hP hR U.loopStep_typed ha hq)

end Signature

/-! ## A budgeted weak-head checker -/

/-- A root oracle proposes root steps. -/
abbrev RootOracle (Head : Type) := ∀ {n : Nat}, Tm Head n → Option (Tm Head n)

/-- A β-redex at the head, else a root step, else a step inside the function. -/
def headApp (root? : RootOracle Head) {n : Nat} (f a : Tm Head n) (inner : Option (Tm Head n)) :
    Option (Tm Head n) :=
  match f with
  | .lam body => some (inst0 a body)
  | _ => (root? (.app f a)).orElse fun _ => inner.map fun f' => .app f' a

/-- A first projection of a pair, else a root step, else a step inside. -/
def headFst (root? : RootOracle Head) {n : Nat} (p : Tm Head n) (inner : Option (Tm Head n)) :
    Option (Tm Head n) :=
  match p with
  | .pair a _ => some a
  | _ => (root? (.fst p)).orElse fun _ => inner.map .fst

/-- A second projection of a pair, else a root step, else a step inside. -/
def headSnd (root? : RootOracle Head) {n : Nat} (p : Tm Head n) (inner : Option (Tm Head n)) :
    Option (Tm Head n) :=
  match p with
  | .pair _ b => some b
  | _ => (root? (.snd p)).orElse fun _ => inner.map .snd

/-- **One weak-head step**, or `none` at a weak-head normal form of the oracle. -/
def whStep (root? : RootOracle Head) : {n : Nat} → Tm Head n → Option (Tm Head n)
  | _, .app f a => headApp root? f a (whStep root? f)
  | _, .fst p => headFst root? p (whStep root? p)
  | _, .snd p => headSnd root? p (whStep root? p)
  | _, t => root? t

/-- The machine of the checker: a step, or the term reached. -/
def whMachine (root? : RootOracle Head) {n : Nat} (t : Tm Head n) : Tm Head n ⊕ Tm Head n :=
  match whStep root? t with
  | some u => .inl u
  | none => .inr t

/-- **The budgeted checker**: run the weak-head machine for at most `k` steps. It
establishes the term reached when it stops, and is incomplete, with the
current term as its receipt, when the budget runs out. -/
def whCheck (root? : RootOracle Head) (k : Nat) {n : Nat} (t : Tm Head n) :
    Outcome (Tm Head n) Empty Empty (Tm Head n) :=
  runFor (whMachine root?) k t

/-- An oracle is sound for a package when it proposes only root steps. -/
def RootOracle.Sound (root? : RootOracle Head) (R : Rules Head) : Prop :=
  ∀ {n : Nat} {t u : Tm Head n}, root? t = some u → R.computation.step t u

/-- **The weak-head step is a step** of the package, for a sound oracle. -/
theorem whStep_sound {root? : RootOracle Head} {R : Rules Head} (sound : root?.Sound R) :
    ∀ {n : Nat} {t u : Tm Head n}, whStep root? t = some u → Step R.headEq t u R.computation := by
  intro n t
  induction t with
  | app f a ihf _ =>
      intro u h
      simp only [whStep, headApp] at h
      split at h
      · cases h
        exact .betaPi _ _
      · cases hr : root? (.app f a) with
        | some u' =>
            rw [hr] at h
            cases h
            exact .root (sound hr)
        | none =>
            rw [hr] at h
            simp only [Option.orElse, Option.map_eq_some_iff] at h
            obtain ⟨f', hf', rfl⟩ := h
            exact .congAppFun (ihf hf')
  | fst p ih =>
      intro u h
      simp only [whStep, headFst] at h
      split at h
      · cases h
        exact .betaSigmaFst _ _
      · cases hr : root? (.fst p) with
        | some u' =>
            rw [hr] at h
            cases h
            exact .root (sound hr)
        | none =>
            rw [hr] at h
            simp only [Option.orElse, Option.map_eq_some_iff] at h
            obtain ⟨p', hp', rfl⟩ := h
            exact .congFst (ih hp')
  | snd p ih =>
      intro u h
      simp only [whStep, headSnd] at h
      split at h
      · cases h
        exact .betaSigmaSnd _ _
      · cases hr : root? (.snd p) with
        | some u' =>
            rw [hr] at h
            cases h
            exact .root (sound hr)
        | none =>
            rw [hr] at h
            simp only [Option.orElse, Option.map_eq_some_iff] at h
            obtain ⟨p', hp', rfl⟩ := h
            exact .congSnd (ih hp')
  | var => intro u h; exact .root (sound h)
  | const => intro u h; exact .root (sound h)
  | head => intro u h; exact .root (sound h)
  | pi => intro u h; exact .root (sound h)
  | sigma => intro u h; exact .root (sound h)
  | id => intro u h; exact .root (sound h)
  | lam => intro u h; exact .root (sound h)
  | pair => intro u h; exact .root (sound h)
  | refl => intro u h; exact .root (sound h)

namespace Signature

variable {S : Signature Head}

/-- The oracle unfolds the recursor at every full application. -/
def UnfoldsRecursor (S : Signature Head) (root? : RootOracle Head) : Prop :=
  ∀ {n : Nat} (P R F a q : Tm Head n), root? (S.recSpine P R F a q) = some (S.unfolding P R F a q)

theorem whStep_app_app {root? : RootOracle Head} {n : Nat} (f a b : Tm Head n) :
    whStep root? (.app (.app f a) b) =
      (root? (.app (.app f a) b)).orElse fun _ => (whStep root? (.app f a)).map fun g => .app g b :=
  rfl

/-- **The checker makes progress on every reachable term.** -/
theorem whStep_looping {root? : RootOracle Head} (fires : S.UnfoldsRecursor root?) {n : Nat}
    {t : Tm Head n} (h : Looping S t) : ∃ u, whStep root? t = some u := by
  cases h with
  | start P R F x q _ =>
      refine ⟨S.unfolding P R F x q, ?_⟩
      have hr : root? (S.recSpine P R F x q) = some (S.unfolding P R F x q) := fires P R F x q
      show whStep root? (S.recSpine P R F x q) = _
      rw [recSpine, whStep_app_app, ← recSpine, hr]
      rfl
  | unfolded F x B hF _ =>
      obtain ⟨t, rfl⟩ := hF
      rw [whStep_app_app]
      cases root? (.app (.app (.lam (.lam (.app (.app (.var 0) (.var 1)) t))) x) (.lam (.lam B))) with
      | some u => exact ⟨u, rfl⟩
      | none => exact ⟨_, rfl⟩
  | halfway X t B _ => exact ⟨_, rfl⟩
  | calling x t B _ =>
      rw [whStep_app_app]
      cases root? (.app (.app (.lam (.lam B)) x) t) with
      | some u => exact ⟨u, rfl⟩
      | none => exact ⟨_, rfl⟩
  | called t B _ => exact ⟨_, rfl⟩

/-- **The strong checker is incomplete at every budget** on every reachable term,
for every sound oracle of the strong variant that unfolds the recursor. -/
theorem whCheck_incomplete (L : S.Laws) (hb : S.BaseSpines) {root? : RootOracle Head}
    (sound : root?.Sound S.strongRules) (fires : S.UnfoldsRecursor root?) :
    ∀ (k : Nat) {n : Nat} {t : Tm Head n}, Looping S t → ∃ s, whCheck root? k t = .incomplete s := by
  intro k
  induction k with
  | zero => intro n t _; exact ⟨t, rfl⟩
  | succ k ih =>
      intro n t h
      obtain ⟨u, hu⟩ := whStep_looping fires h
      have next := h.step_closed L hb (whStep_sound sound hu)
      obtain ⟨s, hs⟩ := ih next
      refine ⟨s, ?_⟩
      simp only [whCheck, runFor, whMachine, hu]
      exact hs

/-- **The loop is incomplete at every budget** in the strong variant: the checker
never establishes a weak-head normal form, and never refutes. -/
theorem loop_whCheck_incomplete (L : S.Laws) (hb : S.BaseSpines) {root? : RootOracle Head}
    (sound : root?.Sound S.strongRules) (fires : S.UnfoldsRecursor root?) (k : Nat) :
    ∃ s, whCheck root? k S.loopTerm = .incomplete s :=
  whCheck_incomplete L hb sound fires k S.loopTerm_looping

theorem loop_whCheck_ne_established (L : S.Laws) (hb : S.BaseSpines) {root? : RootOracle Head}
    (sound : root?.Sound S.strongRules) (fires : S.UnfoldsRecursor root?) (k : Nat)
    (u : Tm Head 5) : whCheck root? k S.loopTerm ≠ .established u := by
  obtain ⟨s, hs⟩ := loop_whCheck_incomplete L hb sound fires k
  rw [hs]
  intro h
  cases h

/-! ### The same checker in the propositional variant -/

/-- No root step of the propositional variant starts at a spine headed by the
recursor. -/
theorem no_rules_root_rec (L : S.Laws) (hb : S.BaseSpines) {n : Nat} {l r : Tm Head n} {k : Nat}
    (head : spineHead l = some (S.recursor, k)) : ¬ S.rules.computation.step l r := by
  rintro (base | decoder)
  · obtain ⟨c, k', ne, h⟩ := hb base
    rw [head] at h
    cases h
    exact ne rfl
  · cases decoder <;>
    · simp only [spineHead, Option.map_some, Option.some.injEq, Prod.mk.injEq] at head
      exact holds_ne_recursor L head.1

/-- The weak-head step of a sound oracle of the propositional variant is stuck at
every spine headed by the recursor. -/
theorem whStep_rec_stuck (L : S.Laws) (hb : S.BaseSpines) {root? : RootOracle Head}
    (sound : root?.Sound S.rules) :
    ∀ {n : Nat} {t : Tm Head n} {k : Nat}, spineHead t = some (S.recursor, k) → whStep root? t = none := by
  intro n t
  induction t with
  | app f a ihf _ =>
      intro k head
      simp only [spineHead] at head
      cases hf : spineHead f with
      | none => rw [hf] at head; cases head
      | some found =>
          obtain ⟨c, k'⟩ := found
          rw [hf] at head
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at head
          obtain ⟨rfl, rfl⟩ := head
          have inner := ihf hf
          have notLam : ∀ body, f ≠ .lam body := by
            intro body same
            rw [same] at hf
            cases hf
          have noRoot : root? (.app f a) = none := by
            cases hr : root? (.app f a) with
            | none => rfl
            | some u =>
                exact absurd (sound hr) (no_rules_root_rec L hb (k := k' + 1)
                  (by simp only [spineHead, hf, Option.map_some]))
          simp only [whStep, headApp]
          rw [noRoot, inner]
          rfl
  | const c =>
      intro k head
      simp only [whStep]
      cases hr : root? (Tm.const c : Tm Head _) with
      | none => rfl
      | some u => exact absurd (sound hr) (no_rules_root_rec L hb head)
  | _ => intro k head; simp [spineHead] at head

/-- **In the propositional variant the same checker establishes the loop at
once**: the recursor is inert, so the loop is its own weak-head normal form. -/
theorem loop_whCheck_established (L : S.Laws) (hb : S.BaseSpines) {root? : RootOracle Head}
    (sound : root?.Sound S.rules) (k : Nat) :
    whCheck root? (k + 1) S.loopTerm = .established S.loopTerm := by
  have stuck := whStep_rec_stuck L hb sound (t := S.loopTerm) (k := 5) rfl
  simp only [whCheck, runFor, whMachine, stuck]

end Signature

/-! ## The loop in the propositional variant: decided, and not convertible

In the propositional variant the recursor is inert, and the loop's unfolding
reduces by four β-steps to the recursor at the same point with the proof
`inv R a q a (ρ a)` in place of `q`. That proof reduces to a spine headed by
`q` with four arguments, so it is not convertible to `q`, and the loop is not
convertible to its unfolding (`loop_inert_not_conv`): with the proof-taking
guard, the propositional route decides the loop's conversion problem
negatively. -/

open Presentation.ConstructorSystem (ConstructorPresentation)
open Presentation.ConversionCoherence (StepStar stepStar_implies_conv)

/-- The variable at the head of an application spine, with its number of
arguments. -/
def varSpine {n : Nat} : Tm Head n → Option (Fin n × Nat)
  | .var i => some (i, 0)
  | .app f _ => (varSpine f).map fun found => (found.1, found.2 + 1)
  | _ => none

theorem spineHead_of_varSpine {n : Nat} {t : Tm Head n} {p : Fin n × Nat}
    (h : varSpine t = some p) : spineHead t = none := by
  induction t with
  | var => rfl
  | app f a ihf =>
      simp only [varSpine] at h
      cases hf : varSpine f with
      | none => rw [hf] at h; cases h
      | some found => simp only [spineHead, ihf hf, Option.map_none]
  | _ => simp [varSpine] at h

/-- **One step keeps a variable-headed spine and its number of arguments.** -/
theorem step_varSpine {rules : Rules Head} (E : ConstructorPresentation rules) {n : Nat}
    {t u : Tm Head n} (step : Step rules.headEq t u rules.computation) :
    ∀ {p : Fin n × Nat}, varSpine t = some p → varSpine u = some p := by
  induction step with
  | root rootStep =>
      intro p h
      obtain ⟨name, -, shape⟩ := Confluence.root_defined E rootStep
      rw [spineHead_of_varSpine h] at shape
      cases shape
  | @congAppFun _ g g' a _ ih =>
      intro p h
      simp only [varSpine] at h ⊢
      cases hg : varSpine g with
      | none => rw [hg] at h; cases h
      | some found =>
          rw [hg] at h
          rw [ih hg]
          exact h
  | congAppArg _ _ =>
      intro p h
      exact h
  | _ => intro p h; simp [varSpine] at h

theorem stepStar_varSpine {rules : Rules Head} (E : ConstructorPresentation rules) {n : Nat}
    {t u : Tm Head n} (steps : StepStar rules t u) {p : Fin n × Nat} (h : varSpine t = some p) :
    varSpine u = some p := by
  induction steps with
  | refl => exact h
  | tail _ step ih => exact step_varSpine E step ih

/-- **Two variable-headed spines with different numbers of arguments are not
convertible.** -/
theorem not_conv_varSpine {rules : Rules Head} (E : ConstructorPresentation rules) {n : Nat}
    {t u : Tm Head n} {i j : Fin n} {k k' : Nat} (h₁ : varSpine t = some (i, k))
    (h₂ : varSpine u = some (j, k')) (ne : k ≠ k') : ¬ Conv rules.headEq t u rules.computation := by
  intro conversion
  obtain ⟨w, tw, uw⟩ := E.churchRosser conversion
  have e := stepStar_varSpine E tw h₁
  rw [stepStar_varSpine E uw h₂] at e
  cases e
  exact ne rfl

namespace Signature

variable {S : Signature Head}

/-- In the propositional variant, a step from a full application of the inert
recursor is a step of one argument. -/
theorem step_recSpine_inert (E : ConstructorPresentation S.rules)
    (hrec : ¬ E.system.defined S.recursor) {n : Nat} {P R F x q u : Tm Head n}
    (step : Step S.rules.headEq (S.recSpine P R F x q) u S.rules.computation) :
    ∃ P' R' F' x' q', u = S.recSpine P' R' F' x' q' ∧
      Relation.ReflGen (Step S.rules.headEq · · S.rules.computation) q q' := by
  have noRoot : ∀ {m : Nat} {l r : Tm Head m} {k : Nat},
      spineHead l = some (S.recursor, k) → ¬ S.rules.computation.step l r := by
    intro m l r k head rootStep
    obtain ⟨name, defined, shape⟩ := Confluence.root_defined E rootStep
    rw [head] at shape
    cases shape
    exact hrec defined
  unfold Signature.recSpine at step ⊢
  cases step with
  | root rootStep => exact absurd rootStep (noRoot (k := 5) rfl)
  | congAppFun s4 =>
      cases s4 with
      | root rootStep => exact absurd rootStep (noRoot (k := 4) rfl)
      | congAppFun s3 =>
          cases s3 with
          | root rootStep => exact absurd rootStep (noRoot (k := 3) rfl)
          | congAppFun s2 =>
              cases s2 with
              | root rootStep => exact absurd rootStep (noRoot (k := 2) rfl)
              | congAppFun s1 =>
                  cases s1 with
                  | root rootStep => exact absurd rootStep (noRoot (k := 1) rfl)
                  | congAppFun s0 =>
                      cases s0 with
                      | root rootStep => exact absurd rootStep (noRoot (k := 0) rfl)
                  | congAppArg _ => exact ⟨_, _, _, _, _, rfl, .refl⟩
              | congAppArg _ => exact ⟨_, _, _, _, _, rfl, .refl⟩
          | congAppArg _ => exact ⟨_, _, _, _, _, rfl, .refl⟩
      | congAppArg _ => exact ⟨_, _, _, _, _, rfl, .refl⟩
  | congAppArg sq => exact ⟨_, _, _, _, _, rfl, .single sq⟩

theorem stepStar_recSpine_inert (E : ConstructorPresentation S.rules)
    (hrec : ¬ E.system.defined S.recursor) {n : Nat} {P R F x q u : Tm Head n}
    (steps : StepStar S.rules (S.recSpine P R F x q) u) :
    ∃ P' R' F' x' q', u = S.recSpine P' R' F' x' q' ∧ StepStar S.rules q q' := by
  induction steps with
  | refl => exact ⟨_, _, _, _, _, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨P', R', F', x', q', rfl, qs⟩ := ih
      obtain ⟨P'', R'', F'', x'', q'', rfl, qstep⟩ := step_recSpine_inert E hrec step
      refine ⟨_, _, _, _, _, rfl, ?_⟩
      cases qstep with
      | refl => exact qs
      | single s => exact .tail qs s

/-- **Convertible applications of the inert recursor have convertible
accessibility proofs.** -/
theorem conv_recSpine_proof (E : ConstructorPresentation S.rules)
    (hrec : ¬ E.system.defined S.recursor) {n : Nat} {P R F x q P₂ R₂ F₂ x₂ q₂ : Tm Head n}
    (conversion : Conv S.rules.headEq (S.recSpine P R F x q) (S.recSpine P₂ R₂ F₂ x₂ q₂)
      S.rules.computation) :
    Conv S.rules.headEq q q₂ S.rules.computation := by
  obtain ⟨w, first, second⟩ := E.churchRosser conversion
  obtain ⟨_, _, _, _, q', rfl, qs⟩ := stepStar_recSpine_inert E hrec first
  obtain ⟨_, _, _, _, q'', same, qs₂⟩ := stepStar_recSpine_inert E hrec second
  simp only [recSpine, Tm.app.injEq] at same
  obtain ⟨-, rfl⟩ := same
  exact .trans _ _ _ (stepStar_implies_conv qs) (.symm _ _ (stepStar_implies_conv qs₂))

/-- The loop's unfolding reduces to its return in four β-steps. -/
theorem unfolding_to_loopReturn :
    StepStar S.rules (S.unfolding (.var 4) (.var 3) loopStep (.var 1) (.var 0)) S.loopReturn :=
  .tail (.tail (.tail (.tail .refl (.congAppFun (.betaPi _ _))) (.betaPi _ _))
    (.congAppFun (.betaPi _ _))) (.betaPi _ _)

/-- The inversion of the abstract proof reduces to a spine headed by the proof,
with four arguments. -/
theorem inv_whnf : ∃ V : Tm Head 5,
    StepStar S.rules (S.invSpine (.var 3) (.var 1) (.var 0) (.var 1) (.app (.var 2) (.var 1))) V ∧
      varSpine V = some (0, 4) :=
  ⟨_, .tail (.tail (.tail .refl (.congAppFun (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _))))))
      (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _))))) (.congAppFun (.congAppFun (.betaPi _ _))),
    rfl⟩

/-- **In the propositional variant the loop is not convertible to its
unfolding.** -/
theorem loop_inert_not_conv (E : ConstructorPresentation S.rules)
    (hrec : ¬ E.system.defined S.recursor) :
    ¬ Conv S.rules.headEq S.loopTerm (S.unfolding (.var 4) (.var 3) loopStep (.var 1) (.var 0))
      S.rules.computation := by
  intro conversion
  have toReturn := Relation.EqvGen.trans _ _ _ conversion (stepStar_implies_conv unfolding_to_loopReturn)
  have proofs := conv_recSpine_proof E hrec toReturn
  obtain ⟨V, toV, spine⟩ := inv_whnf (S := S)
  exact not_conv_varSpine E (t := (.var 0 : Tm Head 5)) (k := 0) (k' := 4) rfl spine (by decide)
    (.trans _ _ _ proofs (stepStar_implies_conv toV))

end Signature

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion
