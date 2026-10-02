import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Divergence
import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Soundness

/-!
# Controls for definitional and propositional unfolding

**Positive control** (consistent context).  Over a predicate `Q`, a point `a`,
a step `s` and a relation `r`, with the hypotheses `accCode r a` and
`respCode r s`:

* the strong variant proves `Q (rec r s a) ⊢ Q (s a (λb. rec r s b))` by the
  conversion rule along a definitional unfolding (`positive_strong`);
* by reflection the carved variant proves the same judgment
  (`positive_carved`), and the recursor application equals its unfolding
  propositionally there (`positive_carved_equal`);
* the carved variant does not relate them definitionally
  (`positive_carved_not_conv`): definitional and propositional unfolding are
  separated;
* without the propositional unfolding rule, the carved variant does not
  prove the judgment (`positive_needs_witness`): the witness is used, not
  decorative;
* the hypotheses are satisfiable in the standard model, so the context is
  consistent (`positive_consistent`).

**The loop's hypotheses are unsatisfiable** (`loopHyps_unsatisfiable`): the
negative control of `Divergence` lives in a context that no standard
environment satisfies, as the divergence requires.

**Curry control.**  The same unfolding without its two premises proves
`falsum` in the empty context (`curry_unguarded`), while the guarded strong
variant does not (`strong_consistent`): the accessibility and respect
premises are what make definitional unfolding consistent.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.Logic
open Mettapedia.TypeTheory.Unfolding
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

variable {A P : Ty}

/-! ## Semantic values -/

/-- Every semantic type is inhabited. -/
def Val.default : (T : Ty) → Val T
  | .atom => True
  | .arr _ codomain => fun _ => Val.default codomain

/-- A proposition embedded as a constant predicate. -/
def Val.ofProp : (T : Ty) → Prop → Val T
  | .atom, p => p
  | .arr _ codomain, p => fun _ => Val.ofProp codomain p

theorem Val.ofProp_injective : ∀ (T : Ty) {p q : Prop}, Val.ofProp T p = Val.ofProp T q → p = q
  | .atom, _, _, same => same
  | .arr domain codomain, _, _, same =>
      Val.ofProp_injective codomain (congrFun same (Val.default domain))

/-- Every semantic type has two distinct values. -/
theorem Val.ofProp_true_ne_false (T : Ty) : Val.ofProp T True ≠ Val.ofProp T False := by
  intro same
  have truth := Val.ofProp_injective T same
  exact truth ▸ trivial

/-! ## The positive control -/

/-- The positive control's context: a predicate on results, a point, a step and
a relation. -/
abbrev positiveContext (A P : Ty) : List Ty := [.arr P prop, A, stepTy A P, relTy A]

/-- The predicate variable. -/
def positivePredicate : Tm A P (positiveContext A P) (.arr P prop) := .var .zero

/-- The point variable. -/
def positivePoint : Tm A P (positiveContext A P) A := .var (.succ .zero)

/-- The step variable. -/
def positiveStep : Tm A P (positiveContext A P) (stepTy A P) := .var (.succ (.succ .zero))

/-- The relation variable. -/
def positiveRelation : Tm A P (positiveContext A P) (relTy A) := .var (.succ (.succ (.succ .zero)))

/-- The recursor application of the positive control. -/
def positiveRec : Tm A P (positiveContext A P) P :=
  recTerm positiveRelation positiveStep positivePoint

/-- Its unfolding. -/
def positiveUnfold : Tm A P (positiveContext A P) P :=
  unfoldTerm positiveRelation positiveStep positivePoint

/-- The hypotheses: the predicate holds of the recursor application, the
point is accessible, and the step respects the relation. -/
def positiveHyps : List (Tm A P (positiveContext A P) prop) :=
  [.app positivePredicate positiveRec, accCode positiveRelation positivePoint,
    respCode positiveRelation positiveStep]

/-- The strong variant unfolds definitionally under these hypotheses. -/
theorem positive_strong_conv :
    Strong A P (.conv (positiveContext A P) positiveHyps P positiveRec positiveUnfold) :=
  derives₂ (Or.inr (UnfoldRule.unfold positiveRelation positiveStep positivePoint))
    (derives₀ (Or.inl (Or.inl (SharedRule.hyp (.tail _ mem₀)))))
    (derives₀ (Or.inl (Or.inl (SharedRule.hyp (.tail _ mem₁)))))

/-- **The strong variant proves the goal by the conversion rule.** -/
theorem positive_strong :
    Strong A P (.holds (positiveContext A P) positiveHyps (.app positivePredicate positiveUnfold)) := by
  refine derives₂ (Or.inl (Or.inl (SharedRule.convert (.app positivePredicate positiveRec)
    (.app positivePredicate positiveUnfold)))) (derives₀ (Or.inl (Or.inl (SharedRule.hyp mem₀)))) ?_
  exact derives₂ (Or.inl (Or.inr (ConvRule.app positivePredicate positivePredicate positiveRec
      positiveUnfold)))
    (derives₀ (Or.inl (Or.inr (ConvRule.beta positivePredicate positivePredicate (.refl _)))))
    positive_strong_conv

/-- **By reflection, the carved variant proves the same judgment.** -/
theorem positive_carved :
    Carved A P (.holds (positiveContext A P) positiveHyps (.app positivePredicate positiveUnfold)) :=
  strong_holds_iff.mp positive_strong

/-- The carved variant proves the unfolding equation propositionally. -/
theorem positive_carved_equal :
    Carved A P (.equal (positiveContext A P) positiveHyps P positiveRec positiveUnfold) :=
  conv_reflects_to_equal positive_strong_conv

/-- An environment for the positive context with the given values. -/
def positiveEnvironment (recursor : Val (recTy A P)) (predicate : Val (.arr P prop)) (point : Val A)
    (step : Val (stepTy A P)) (relation : Val (relTy A)) :
    Environment Prop (positiveContext A P ++ signature A P) :=
  Environment.extend predicate <| Environment.extend point <| Environment.extend step <|
    Environment.extend relation (sigEnvironmentAt recursor)

theorem positiveEnvironment_standard (recursor : Val (recTy A P)) (predicate : Val (.arr P prop))
    (point : Val A) (step : Val (stepTy A P)) (relation : Val (relTy A)) :
    Standard recursor (positiveEnvironment recursor predicate point step relation) :=
  fun _ => rfl

/-- **Definitional and propositional unfolding are separated**: the carved
variant does not identify the recursor application with its unfolding. -/
theorem positive_carved_not_conv :
    ¬ Carved A P (.conv (positiveContext A P) positiveHyps P positiveRec positiveUnfold) := by
  intro derivation
  have convertible := carved_conv_iff.mp derivation
  have same := BetaConv.denote convertible
    (positiveEnvironment (fun _ _ _ => Val.ofProp P True) (Val.default _) (Val.default A)
      (fun _ _ => Val.ofProp P False) (Val.default _))
  exact Val.ofProp_true_ne_false P same

/-- The carved rules without the propositional unfolding rule. -/
abbrev CarvedWithoutWitness (judgment : Judgment A P) : Prop :=
  Derives (RuleUnion (SharedRule false) ConvRule) judgment

/-- **The propositional witness is used**: without it, the carved variant does
not prove the positive control's goal. -/
theorem positive_needs_witness :
    ¬ CarvedWithoutWitness (A := A) (P := P)
      (.holds (positiveContext A P) positiveHyps (.app positivePredicate positiveUnfold)) := by
  intro derivation
  let recursor : Val (recTy A P) := fun _ _ _ => Val.ofProp P True
  let environment := positiveEnvironment recursor (fun value => value = Val.ofProp P True)
    (Val.default A) (fun _ _ => Val.ofProp P False) (fun _ _ => False)
  have standard : Standard recursor environment :=
    positiveEnvironment_standard recursor (fun value => value = Val.ofProp P True)
      (Val.default A) (fun _ _ => Val.ofProp P False) (fun _ _ => False)
  have holds : HypsHold environment positiveHyps := by
    intro hypothesis member
    rcases List.mem_cons.mp member with rfl | member
    · change Val.ofProp P True = Val.ofProp P True
      rfl
    rcases List.mem_cons.mp member with rfl | member
    · exact (denote_accCode standard _ _).mpr (Acc.intro _ fun _ below => False.elim below)
    rcases List.mem_cons.mp member with rfl | member
    · exact (denote_respCode standard _ _).mpr fun _ _ _ _ => rfl
    · exact nomatch member
  have goal := noWitness_sound recursor derivation environment standard holds
  change Val.ofProp P False = Val.ofProp P True at goal
  exact Val.ofProp_true_ne_false P goal.symm

/-- **The positive context is consistent**: the strong variant does not derive
`falsum` from its hypotheses. -/
theorem positive_consistent :
    ¬ Strong A P (.holds (positiveContext A P) positiveHyps falsum) := by
  let step : Val (stepTy A P) := fun _ _ => Val.default P
  let relation : Val (relTy A) := fun _ _ => False
  let environment := positiveEnvironment standardRecursor
    (fun value => value = standardRecursor relation step (Val.default A)) (Val.default A) step relation
  have standard : Standard standardRecursor environment :=
    positiveEnvironment_standard standardRecursor
      (fun value => value = standardRecursor relation step (Val.default A)) (Val.default A) step relation
  apply strong_not_derivable_of_countermodel environment standard
  · intro hypothesis member
    rcases List.mem_cons.mp member with rfl | member
    · change standardRecursor relation step (Val.default A) =
        standardRecursor relation step (Val.default A)
      rfl
    rcases List.mem_cons.mp member with rfl | member
    · exact (denote_accCode standard _ _).mpr (Acc.intro _ fun _ below => False.elim below)
    rcases List.mem_cons.mp member with rfl | member
    · exact (denote_respCode standard _ _).mpr fun _ _ _ _ => rfl
    · exact nomatch member
  · rw [denote_falsum standard]
    exact fun everything => everything False

/-! ## The loop's hypotheses are unsatisfiable -/

/-- **No standard environment satisfies the negative control's hypotheses**,
whatever the recursor means. -/
theorem loopHyps_unsatisfiable (recursor : Val (recTy A P))
    (environment : Environment Prop (loopContext A ++ signature A P))
    (standard : Standard recursor environment) : ¬ HypsHold environment loopHyps := by
  intro holds
  have accessible := (denote_accCode standard _ _).mp (holds _ mem₀)
  have respects := (denote_respCode standard _ _).mp (holds _ mem₁)
  set relation := (Term.var loopRelation : Tm A P (loopContext A) (relTy A)).denote environment
  have reflexive : ∀ x, relation x x := by
    intro x
    have same := respects x (fun _ => Val.ofProp P True) (fun y => Val.ofProp P (relation y x))
      fun y related => congrArg (Val.ofProp P) (propext ⟨fun _ => related, fun _ => trivial⟩)
    change Val.ofProp P True = Val.ofProp P (relation x x) at same
    exact (Val.ofProp_injective P same) ▸ trivial
  have irreflexive : ∀ x, Acc relation x → ¬ relation x x := by
    intro x accessibleAt
    induction accessibleAt with
    | intro x _ ih => exact fun loop => ih x loop loop
  exact irreflexive _ accessible (reflexive _)

/-! ## The Curry control -/

/-- The unfolding of the recursor with no premises. -/
inductive UnguardedRule : List (Judgment A P) → Judgment A P → Prop
  | unfold {Γ : List Ty} {hyps : List (Tm A P Γ prop)} (R : Tm A P Γ (relTy A))
      (F : Tm A P Γ (stepTy A P)) (point : Tm A P Γ A) :
      UnguardedRule [] (.conv Γ hyps P (recTerm R F point) (unfoldTerm R F point))

/-- The carved variant with the unguarded definitional unfolding. -/
abbrev Unguarded (A P : Ty) (judgment : Judgment A P) : Prop :=
  Derives (RuleUnion (unfoldingSplit A P).carved UnguardedRule) judgment

/-- `falsum` over proposition codes, in the data context `Γ`. -/
abbrev falsumAt (Γ : List Ty) : Tm prop prop Γ prop := falsum (A := prop) (P := prop) (Γ := Γ)

/-- Curry's step, over proposition codes: `λx z. z x → falsum`. -/
def curryStep : Tm prop prop [] (stepTy prop prop) :=
  .lam (.lam (imp (A := prop) (P := prop) (Γ := [.arr prop prop, prop])
    (.app (.var .zero) (.var (.succ .zero))) (falsumAt [.arr prop prop, prop])))

/-- Any relation will do; the unguarded unfolding ignores it. -/
def curryRelation : Tm prop prop [] (relTy prop) := .lam (.lam (falsumAt [prop, prop]))

/-- Curry's proposition: `c ≡ (c → falsum)` under unguarded unfolding. -/
def curryCode : Tm prop prop [] prop := recTerm curryRelation curryStep (falsumAt [])

/-- The continuation of the unfolding. -/
def curryContinuation : Tm prop prop [] (.arr prop prop) :=
  .lam (recTerm (A := prop) (P := prop) (Γ := [prop]) (wk curryRelation) (wk curryStep) (.var .zero))

/-- The body reached after the first beta step. -/
def curryHalf : Tm prop prop [.arr prop prop] prop :=
  imp (A := prop) (P := prop) (Γ := [.arr prop prop]) (.app (.var .zero) (wk (falsumAt [])))
    (falsumAt [.arr prop prop])

/-- The abstraction reached after the first beta step. -/
def curryHalfAbstraction : Tm prop prop [] (.arr (.arr prop prop) prop) := .lam curryHalf

theorem curry_unfold_betaConv :
    BetaConv (unfoldTerm curryRelation curryStep (falsumAt []))
      (imp (A := prop) (P := prop) (Γ := []) curryCode (falsumAt [])) := by
  have first : BetaStep (unfoldTerm curryRelation curryStep (falsumAt []))
      (.app curryHalfAbstraction curryContinuation) :=
    BetaStep.appLeft (BetaStep.beta
      (.lam (imp (A := prop) (P := prop) (Γ := [.arr prop prop, prop])
        (.app (.var .zero) (.var (.succ .zero))) (falsumAt [.arr prop prop, prop])))
      (falsumAt []))
  have second : BetaStep (Γ := [] ++ signature prop prop) (.app curryHalfAbstraction curryContinuation)
      (imp (A := prop) (P := prop) (Γ := []) (.app curryContinuation (falsumAt [])) (falsumAt [])) :=
    BetaStep.beta curryHalf curryContinuation
  have third : BetaStep (Γ := [] ++ signature prop prop)
      (imp (A := prop) (P := prop) (Γ := []) (.app curryContinuation (falsumAt [])) (falsumAt []))
      (imp (A := prop) (P := prop) (Γ := []) curryCode (falsumAt [])) :=
    BetaStep.appLeft (BetaStep.appRight (BetaStep.beta
      (recTerm (A := prop) (P := prop) (Γ := [prop]) (wk curryRelation) (wk curryStep) (.var .zero))
      (falsumAt [])))
  exact .trans _ _ _ (.rel _ _ first) (.trans _ _ _ (.rel _ _ second) (.rel _ _ third))

/-- Curry's code converts to its own refutation. -/
abbrev curryRefutation : Tm prop prop [] prop :=
  imp (A := prop) (P := prop) (Γ := []) curryCode (falsumAt [])

theorem curry_conv (hyps : List (Tm prop prop [] prop)) :
    Unguarded prop prop (.conv [] hyps prop curryCode curryRefutation) :=
  derives₂ (Or.inl (Or.inr (ConvRule.trans curryCode
      (unfoldTerm curryRelation curryStep (falsumAt [])) curryRefutation)))
    (derives₀ (Or.inr (UnguardedRule.unfold curryRelation curryStep (falsumAt []))))
    (derives₀ (Or.inl (Or.inr (ConvRule.beta _ _ curry_unfold_betaConv))))

/-- **Curry.**  Unguarded definitional unfolding proves `falsum` in the empty
context. -/
theorem curry_unguarded : Unguarded prop prop (.holds [] [] (falsumAt [])) := by
  have assumed : Unguarded prop prop (.holds [] [curryCode] curryCode) :=
    derives₀ (Or.inl (Or.inl (SharedRule.hyp mem₀)))
  have refuted : Unguarded prop prop (.holds [] [curryCode] curryRefutation) :=
    derives₂ (Or.inl (Or.inl (SharedRule.convert _ _))) assumed (curry_conv [curryCode])
  have absurdity : Unguarded prop prop (.holds [] [curryCode] (falsumAt [])) :=
    derives₂ (Or.inl (Or.inl (SharedRule.impElim _ _))) refuted assumed
  have negation : Unguarded prop prop (.holds [] [] curryRefutation) :=
    derives₁ (Or.inl (Or.inl (SharedRule.impIntro _ _))) absurdity
  have backwards : Unguarded prop prop (.conv [] [] prop curryRefutation curryCode) :=
    derives₁ (Or.inl (Or.inr (ConvRule.symm _ _))) (curry_conv [])
  have proof : Unguarded prop prop (.holds [] [] curryCode) :=
    derives₂ (Or.inl (Or.inl (SharedRule.convert _ _))) negation backwards
  exact derives₂ (Or.inl (Or.inl (SharedRule.impElim _ _))) negation proof

/-- The guard is what separates the two: the guarded strong variant is
consistent, the unguarded one is not. -/
theorem guard_is_essential :
    Unguarded prop prop (.holds [] [] (falsumAt [])) ∧
      ¬ Strong prop prop (.holds [] [] (falsumAt [])) :=
  ⟨curry_unguarded, strong_consistent⟩

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
