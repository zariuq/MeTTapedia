import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCensusReadsEta

/-!
# Distinct skeletons at any type

R99's head clash reads two neutral spines with distinct skeletons only at a rigid base type
(`ContextualDependentConstantHeads.skeletons_not_equal` asks for `BaseType`). At a flexible base, a type that a solution
may instantiate with a Π or Σ type, `λ g x. g x ≐ λ g x. x` at `(A → A) → A → A` with `A` a metavariable, it does not
apply, and the η-long prepared family is stuck there (`ContextualDependentEtaDepth.Controls.flexibleStore`).

**Two neutral terms of distinct skeletons are never equal, at any type** (`skeletons_not_equal_any`): completeness of
the algorithmic equality gives a comparison of the two terms, R110's descent (`ContextualDependentSpineEta.descends`)
carries it, through η, to a comparison of the two terms as spines after an injective renaming, spines compared as
spines have equal skeletons (`spines_skeleton`), and an injective renaming reflects equal skeletons
(`skeleton_rename_reflect`).

`SkeletonClash` is the reading under the equation's abstractions, at any annotation; it is kept by substitutions that
fix the locals (`SkeletonClash.subst`) and never holds (`skeletonClash_not_equal`). Its decision `skeletonClashAt` is
sound and complete (`skeletonClashAt_sound`, `skeletonClashAt_complete`), and **the skeleton clash rule**
(`skeletonSearch`) refutes, with a certificate, every store with an equation of equal annotation codes whose sides
clash (`skeletonSearch_isSome`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstantHeads

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist

variable {Head : Type}

/-! ## Skeletons under renaming -/

/-- The skeleton of a renamed spine is defined when the spine's is. -/
theorem skeleton_rename_isSome {n m : Nat} (ρ : Ren n m) :
    ∀ {t : Tm Head n}, (skeleton t).isSome → (skeleton (Presentation.rename ρ t)).isSome
  | .var _, _ => rfl
  | .const _, _ => rfl
  | .app f _, found => by
      simp only [Presentation.rename, skeleton, Option.isSome_map] at found ⊢
      exact skeleton_rename_isSome ρ (t := f) found
  | .fst p, found => by
      simp only [Presentation.rename, skeleton, Option.isSome_map] at found ⊢
      exact skeleton_rename_isSome ρ (t := p) found
  | .snd p, found => by
      simp only [Presentation.rename, skeleton, Option.isSome_map] at found ⊢
      exact skeleton_rename_isSome ρ (t := p) found
  | .head _, found | .pi _ _, found | .sigma _ _, found | .id _ _ _, found | .lam _, found | .pair _ _, found
  | .refl _, found => by simp [skeleton] at found

/-- **An injective renaming reflects equal skeletons.** -/
theorem skeleton_rename_reflect {n m : Nat} {ρ : Ren n m} (injective : Function.Injective ρ) :
    ∀ {l r : Tm Head n}, (skeleton l).isSome →
      skeleton (Presentation.rename ρ l) = skeleton (Presentation.rename ρ r) → skeleton l = skeleton r
  | .var i, r, _, same => by
      cases r with
      | var j =>
          simp only [Presentation.rename, skeleton, Option.some.injEq, Prod.mk.injEq, SpineHead.local.injEq,
            and_true] at same ⊢
          rw [injective (Fin.ext same.symm)]
      | const _ => simp [Presentation.rename, skeleton] at same
      | app g _ =>
          simp only [Presentation.rename, skeleton] at same
          cases h : skeleton (Presentation.rename ρ g) <;> simp [h] at same
      | fst q =>
          simp only [Presentation.rename, skeleton] at same
          cases h : skeleton (Presentation.rename ρ q) <;> simp [h] at same
      | snd q =>
          simp only [Presentation.rename, skeleton] at same
          cases h : skeleton (Presentation.rename ρ q) <;> simp [h] at same
      | head _ | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | refl _ => simp [Presentation.rename, skeleton] at same
  | .const c, r, _, same => by
      cases r with
      | var j => simp [Presentation.rename, skeleton] at same
      | const _ =>
          simp only [Presentation.rename, skeleton] at same ⊢
          exact same
      | app g _ =>
          simp only [Presentation.rename, skeleton] at same
          cases h : skeleton (Presentation.rename ρ g) <;> simp [h] at same
      | fst q =>
          simp only [Presentation.rename, skeleton] at same
          cases h : skeleton (Presentation.rename ρ q) <;> simp [h] at same
      | snd q =>
          simp only [Presentation.rename, skeleton] at same
          cases h : skeleton (Presentation.rename ρ q) <;> simp [h] at same
      | head _ | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | refl _ => simp [Presentation.rename, skeleton] at same
  | .app f a, r, found, same => by
      have inner : (skeleton f).isSome := by simpa [skeleton] using found
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (skeleton_rename_isSome ρ inner)
      cases r with
      | app g b =>
          simp only [Presentation.rename, skeleton, hs] at same ⊢
          cases hg : skeleton (Presentation.rename ρ g) with
          | none => simp [hg] at same
          | some s' =>
              simp only [hg, Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and] at same
              have equal : skeleton (Presentation.rename ρ f) = skeleton (Presentation.rename ρ g) := by
                rw [hs, hg]
                exact congrArg some (Prod.ext same.1 same.2)
              rw [skeleton_rename_reflect injective inner equal]
      | var _ | const _ =>
          simp only [Presentation.rename, skeleton, hs] at same
          simp at same
      | fst q =>
          simp only [Presentation.rename, skeleton, hs] at same
          cases h : skeleton (Presentation.rename ρ q) <;> simp [h] at same
      | snd q =>
          simp only [Presentation.rename, skeleton, hs] at same
          cases h : skeleton (Presentation.rename ρ q) <;> simp [h] at same
      | head _ | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | refl _ =>
          simp only [Presentation.rename, skeleton, hs] at same
          simp at same
  | .fst p, r, found, same => by
      have inner : (skeleton p).isSome := by simpa [skeleton] using found
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (skeleton_rename_isSome ρ inner)
      cases r with
      | fst q =>
          simp only [Presentation.rename, skeleton, hs] at same ⊢
          cases hq : skeleton (Presentation.rename ρ q) with
          | none => simp [hq] at same
          | some s' =>
              simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and] at same
              have equal : skeleton (Presentation.rename ρ p) = skeleton (Presentation.rename ρ q) := by
                rw [hs, hq]
                exact congrArg some (Prod.ext same.1 same.2)
              rw [skeleton_rename_reflect injective inner equal]
      | var _ | const _ =>
          simp only [Presentation.rename, skeleton, hs] at same
          simp at same
      | app g _ =>
          simp only [Presentation.rename, skeleton, hs] at same
          cases h : skeleton (Presentation.rename ρ g) <;> simp [h] at same
      | snd q =>
          simp only [Presentation.rename, skeleton, hs] at same
          cases h : skeleton (Presentation.rename ρ q) <;> simp [h] at same
      | head _ | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | refl _ =>
          simp only [Presentation.rename, skeleton, hs] at same
          simp at same
  | .snd p, r, found, same => by
      have inner : (skeleton p).isSome := by simpa [skeleton] using found
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp (skeleton_rename_isSome ρ inner)
      cases r with
      | snd q =>
          simp only [Presentation.rename, skeleton, hs] at same ⊢
          cases hq : skeleton (Presentation.rename ρ q) with
          | none => simp [hq] at same
          | some s' =>
              simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and] at same
              have equal : skeleton (Presentation.rename ρ p) = skeleton (Presentation.rename ρ q) := by
                rw [hs, hq]
                exact congrArg some (Prod.ext same.1 same.2)
              rw [skeleton_rename_reflect injective inner equal]
      | var _ | const _ =>
          simp only [Presentation.rename, skeleton, hs] at same
          simp at same
      | app g _ =>
          simp only [Presentation.rename, skeleton, hs] at same
          cases h : skeleton (Presentation.rename ρ g) <;> simp [h] at same
      | fst q =>
          simp only [Presentation.rename, skeleton, hs] at same
          cases h : skeleton (Presentation.rename ρ q) <;> simp [h] at same
      | head _ | pi _ _ | sigma _ _ | id _ _ _ | lam _ | pair _ _ | refl _ =>
          simp only [Presentation.rename, skeleton, hs] at same
          simp at same
  | .head _, _, found, _ | .pi _ _, _, found, _ | .sigma _ _, _, found, _ | .id _ _ _, _, found, _
  | .lam _, _, found, _ | .pair _ _, _, found, _ | .refl _, _, found, _ => by simp [skeleton] at found

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

section Refutation

variable (complete : AlgorithmicComplete S.R S.roles)

include complete in
/-- **Two neutral terms of different skeletons are never equal, at any type**: an algorithmic comparison of neutral
terms descends, through η, to their comparison as spines after an injective renaming. -/
theorem skeletons_not_equal_any {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {l r C : Tm Head n}
    (leftNeutral : Neutral S.roles l) (rightNeutral : Neutral S.roles r) (found : (skeleton l).isSome)
    (differ : skeleton l ≠ skeleton r) : ¬ Equal S.R Γ l r C := by
  intro same
  obtain ⟨_, _, ρ, _, _, injective, _, spines⟩ :=
    ContextualDependentSpineEta.descends (complete formed same) formed leftNeutral rightNeutral
  exact differ (skeleton_rename_reflect injective found (spines_skeleton _ _ _ spines))

end Refutation

/-! ## Skeleton clashes at any base type -/

/-- **A skeleton clash under abstractions**: two neutral spines with heads fixed under the abstractions and distinct
skeletons, at any type, under the same abstractions on both sides. -/
inductive SkeletonClash : Nat → {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | base {depth n : Nat} {C l r : Tm Head n} {s s' : Skeleton} :
      fixedSkeleton depth l = some s → fixedSkeleton depth r = some s' → s ≠ s' → SkeletonClash depth C l r
  | bind {depth n : Nat} {D : Tm Head n} {T l r : Tm Head (n + 1)} :
      SkeletonClash (depth + 1) T l r → SkeletonClash depth (.pi D T) (.lam l) (.lam r)

/-- **The reading is kept by substitutions that fix the locals.** -/
theorem SkeletonClash.subst {depth n : Nat} {annotation left right : Tm Head n}
    (clash : SkeletonClash depth annotation left right) :
    ∀ {m : Nat} (σ : Sub Head n m), ContextualDependentSpinesMany.Fixes σ depth → depth ≤ m →
      SkeletonClash depth (Presentation.subst σ annotation) (Presentation.subst σ left)
        (Presentation.subst σ right) := by
  induction clash with
  | base kl kr differ =>
      intro m σ fixes bound
      exact .base (fixedSkeleton_subst fixes bound kl) (fixedSkeleton_subst fixes bound kr) differ
  | bind _ ih =>
      intro m σ fixes bound
      exact .bind (ih (liftSub σ) fixes.lift (by omega))

section NotEqual

variable (facts : FormFacts S.R S.roles) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts rigid complete in
/-- **A skeleton clash under abstractions never holds**, at any type. -/
theorem skeletonClash_not_equal {depth n : Nat} {annotation left right : Tm Head n}
    (clash : SkeletonClash depth annotation left right) :
    ∀ {Γ : Ctx Head n}, CtxFormed S.R Γ → TypedEquality.Typed S.R Γ left annotation →
      TypedEquality.Typed S.R Γ right annotation → ¬ Equal S.R Γ left right annotation := by
  induction clash with
  | base kl kr differ =>
      intro Γ formed _ _ same
      refine skeletons_not_equal_any complete formed (skeleton_neutral rigid (fixedSkeleton_skeleton kl))
        (skeleton_neutral rigid (fixedSkeleton_skeleton kr)) (by rw [fixedSkeleton_skeleton kl]; rfl) ?_ same
      rw [fixedSkeleton_skeleton kl, fixedSkeleton_skeleton kr]
      intro equal
      exact differ (Option.some.inj equal)
  | bind _ ih =>
      intro Γ formed tl tr same
      obtain ⟨⟨u, hu, tD⟩, _⟩ := IsType.pi_parts (Typed.isType tl formed)
      exact ih (formed.snoc ⟨u, hu, tD⟩) (Typed.lam_inv facts tl formed) (Typed.lam_inv facts tr formed)
        (ContextualDependentOccursFull.lam_equal_inv facts formed same)

end NotEqual

/-! ## The decision -/

/-- Distinct skeletons of two spines with heads fixed under `depth` abstractions. -/
def baseClash (depth : Nat) {n : Nat} (l r : Tm Head n) : Bool :=
  match fixedSkeleton depth l, fixedSkeleton depth r with
  | some s, some s' => decide (s ≠ s')
  | _, _ => false

/-- One binder of the decision: a Π annotation over two abstractions. -/
def lamStep {n : Nat} (A r : Tm Head n) (inner : Tm Head (n + 1) → Tm Head (n + 1) → Bool) : Bool :=
  match A, r with
  | .pi _ T, .lam r' => inner T r'
  | _, _ => false

/-- **The skeleton clash decision.** -/
def skeletonClashAt : Nat → {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Bool
  | depth, _, A, .lam l, r => lamStep A r fun T r' => skeletonClashAt (depth + 1) T l r'
  | depth, _, _, l, r => baseClash depth l r

theorem baseClash_sound {depth n : Nat} {l r : Tm Head n} (found : baseClash depth l r = true) :
    ∃ s s', fixedSkeleton depth l = some s ∧ fixedSkeleton depth r = some s' ∧ s ≠ s' := by
  unfold baseClash at found
  split at found
  · rename_i s s' kl kr
    exact ⟨s, s', kl, kr, of_decide_eq_true found⟩
  · cases found

theorem baseClash_complete {depth n : Nat} {l r : Tm Head n} {s s' : Skeleton} (kl : fixedSkeleton depth l = some s)
    (kr : fixedSkeleton depth r = some s') (differ : s ≠ s') : baseClash depth l r = true := by
  unfold baseClash
  rw [kl, kr]
  exact decide_eq_true differ

/-- **The decision is sound.** -/
theorem skeletonClashAt_sound : ∀ (depth : Nat) {n : Nat} (A l r : Tm Head n),
    skeletonClashAt depth A l r = true → SkeletonClash depth A l r
  | depth, _, A, .lam l, r, found => by
      change lamStep A r (fun T r' => skeletonClashAt (depth + 1) T l r') = true at found
      unfold lamStep at found
      split at found
      · exact .bind (skeletonClashAt_sound (depth + 1) _ l _ found)
      · cases found
  | depth, _, A, .var _, r, found | depth, _, A, .const _, r, found | depth, _, A, .head _, r, found
  | depth, _, A, .pi _ _, r, found | depth, _, A, .sigma _ _, r, found | depth, _, A, .id _ _ _, r, found
  | depth, _, A, .app _ _, r, found | depth, _, A, .pair _ _, r, found | depth, _, A, .fst _, r, found
  | depth, _, A, .snd _, r, found | depth, _, A, .refl _, r, found => by
      obtain ⟨s, s', kl, kr, differ⟩ := baseClash_sound found
      exact .base kl kr differ

/-- **The decision is complete.** -/
theorem skeletonClashAt_complete {depth n : Nat} {A l r : Tm Head n} (clash : SkeletonClash depth A l r) :
    skeletonClashAt depth A l r = true := by
  induction clash with
  | @base depth n C l r s s' kl kr differ =>
      have base := baseClash_complete kl kr differ
      cases l
      case lam body => simp [fixedSkeleton] at kl
      all_goals exact base
  | bind _ ih => exact ih

/-! ## The skeleton clash rule -/

section Rule

variable [DecidableEq Head]

/-- **A store equation whose sides have distinct skeletons under its abstractions**, at one annotation code. -/
structure SkeletonShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Prop where
  same : equation.2.1.code = equation.1.1.code
  clash : SkeletonClash 0 equation.1.1.code equation.1.2.code equation.2.2.code

/-- Read a skeleton clash from the codes; no budget. -/
def skeletonShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (PLift (SkeletonShape equation)) :=
  if same : equation.2.1.code = equation.1.1.code then
    if found : skeletonClashAt 0 equation.1.1.code equation.1.2.code equation.2.2.code = true then
      some ⟨⟨same, skeletonClashAt_sound _ _ _ _ found⟩⟩
    else none
  else none

theorem skeletonShape_some {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : SkeletonShape equation) :
    (skeletonShape equation).isSome := by
  unfold skeletonShape
  rw [dif_pos shape.same, dif_pos (skeletonClashAt_complete shape.clash)]
  rfl

variable (facts : FormFacts S.R S.roles) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] in
include facts rigid complete in
/-- **A skeleton clash has no solution at any later context.** -/
theorem SkeletonShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : SkeletonShape equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [ContextualDependentRigidFormers.solves_raw] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.same] at tRight
  exact skeletonClash_not_equal facts rigid complete
    (shape.clash.subst σ.substitution (fun _ _ _ small => absurd small (Nat.not_lt_zero _)) (Nat.zero_le _))
    Δ.formed tLeft tRight solved.2

/-- **The skeleton clash rule**: refute the store at the first equation whose sides have distinct skeletons. -/
def skeletonSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) →
    Option (PLift (¬ (frames S.levels).Solvable problem))
  | [] => none
  | equation :: rest =>
      match skeletonShape equation with
      | some shape => some ⟨fun ⟨_, σ, solved⟩ =>
          shape.down.refutes facts rigid complete σ (solved equation List.mem_cons_self)⟩
      | none => (skeletonSearch rest).map fun absent =>
          ⟨fun ⟨Δ, σ, solved⟩ => absent.down ⟨Δ, σ, fun other member => solved other (List.mem_cons_of_mem _ member)⟩⟩

/-- **The skeleton clash rule reads every equation with distinct skeletons.** -/
theorem skeletonSearch_isSome {Θ : Context S.R} :
    ∀ {problem : EquationStore (TotalTerm Θ)} {equation : Equation (TotalTerm Θ)}, equation ∈ problem →
      SkeletonShape equation → (skeletonSearch facts rigid complete problem).isSome
  | [], _, member, _ => absurd member List.not_mem_nil
  | first :: rest, equation, member, shape => by
      simp only [skeletonSearch]
      cases computed : skeletonShape first with
      | some found => rfl
      | none =>
          rcases List.mem_cons.mp member with rfl | later
          · have := skeletonShape_some shape
            rw [computed] at this
            cases this
          · simp only [Option.isSome_map]
            exact skeletonSearch_isSome later shape

end Rule

end ContextualDependentConstantHeads
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
