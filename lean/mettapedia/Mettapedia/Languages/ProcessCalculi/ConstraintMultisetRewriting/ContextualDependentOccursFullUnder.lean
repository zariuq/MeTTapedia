import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRankRound

/-!
# The occurs check under abstractions

A store equation of the dynamic pattern fragment is read under its leading abstractions:
`λ x̄. V ≐ λ x̄. T` at `Π x̄. U`. Two abstractions equal at a Π type have equal bodies under the domain
(`lam_equal_inv`), so the equation holds only if `V ≐ T` holds at `U` under the binders. When `U` is a
universe and `V` occurs properly in `T` along type-former positions, that is impossible by the full
occurs check (`prefixed_not_equal`), at every later context, since the reading is kept by substitution
(`Prefixed.subst`).

So `λ x. G x ≐ λ x. Π (G x) x` at `U0 → U0` is refused: its body would make `G x` contain itself.

The **ranked occurs round** runs this refutation on the prepared store first, then the ranked round.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentOccursFull

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentInPlace
open ContextualDependentRigidFormers ContextualDependentEtaLong ContextualDependentOccursCheck
open ContextualDependentRank ContextualDependentDecisiveFragment ContextualDependentConversionBudget
open ContextualDependentEtaExpansion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Abstractions equal at a Π type -/

/-- **Equal abstractions have equal bodies** under the domain. -/
theorem lam_equal_inv (facts : FormFacts S.R S.roles) {n : Nat} {Δ : Ctx Head n} (formed : CtxFormed S.R Δ)
    {A : Tm Head n} {B b b' : Tm Head (n + 1)} (equal : Equal S.R Δ (.lam b) (.lam b') (.pi A B)) :
    Equal S.R (.snoc Δ A) b b' B := by
  obtain ⟨tl, tr⟩ := Equal.typed equal formed
  obtain ⟨u, hu, tPi⟩ := Typed.isType tl formed
  have tb := Typed.lam_inv facts tl formed
  have tb' := Typed.lam_inv facts tr formed
  have compatible := CtxRen.snoc (CtxRen.wk Δ A) A
  have tPi' : Typed S.R (.snoc Δ A) (.pi (Presentation.rename wk A) (Presentation.rename (liftRen wk) B)) (.head u) :=
    Typed.weaken (extension := A) tPi
  have tv : Typed S.R (.snoc Δ A) (.var 0) (Presentation.rename wk A) := .var 0
  have β₁ := Derivable.betaPi tPi' hu (tb.rename compatible) tv
  have β₂ := Derivable.betaPi tPi' hu (tb'.rename compatible) tv
  have applied := Derivable.appCong (Equal.weaken (extension := A) equal) (.refl tv)
  have joined : Equal S.R (.snoc Δ A) (inst0 (.var 0) (Presentation.rename (liftRen wk) b))
      (inst0 (.var 0) (Presentation.rename (liftRen wk) b')) (inst0 (.var 0) (Presentation.rename (liftRen wk) B)) :=
    .trans (.symm β₁) (.trans applied β₂)
  rw [inst0_var_rename_liftRen_wk, inst0_var_rename_liftRen_wk, inst0_var_rename_liftRen_wk] at joined
  exact joined

/-! ## Proper occurrences under abstractions -/

/-- **`λ x̄. V ≐ λ x̄. T` at `Π x̄. U`**, with `U` a universe and `V` occurring properly in `T`: the
annotation, the left side and the right side. -/
inductive Prefixed (R : Rules Head) : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop
  | base {n : Nat} {u : Head} {V T : Tm Head n} : R.isUniverse u → Within true V T → Prefixed R (.head u) V T
  | bind {n : Nat} {A : Tm Head n} {B V T : Tm Head (n + 1)} :
      Prefixed R B V T → Prefixed R (.pi A B) (.lam V) (.lam T)

theorem Prefixed.subst {R : Rules Head} {n : Nat} {annotation left right : Tm Head n}
    (prefixed : Prefixed R annotation left right) :
    ∀ {m : Nat} (σ : Sub Head n m),
      Prefixed R (Presentation.subst σ annotation) (Presentation.subst σ left) (Presentation.subst σ right) := by
  induction prefixed with
  | base universal within => exact fun σ => .base universal (within.subst σ)
  | bind _ ih => exact fun σ => .bind (ih (liftSub σ))

section Refutation

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **The occurs check under abstractions**: such an equation never holds. -/
theorem prefixed_not_equal {n : Nat} {annotation left right : Tm Head n}
    (prefixed : Prefixed S.R annotation left right) :
    ∀ {Δ : Ctx Head n}, CtxFormed S.R Δ → Typed S.R Δ left annotation → Typed S.R Δ right annotation →
      ¬ Equal S.R Δ left right annotation := by
  induction prefixed with
  | base universal within =>
      intro Δ formed tLeft tRight same
      exact occurrence_not_typeEq facts roots heads algebra rigid complete formed within ⟨_, universal, tLeft⟩
        ⟨_, universal, tRight⟩ ⟨_, universal, same⟩
  | @bind n A B V T _ ih =>
      intro Δ formed tLeft tRight same
      obtain ⟨⟨u, hu, tA⟩, _⟩ := IsType.pi_parts (Typed.isType tLeft formed)
      exact ih (formed.snoc ⟨u, hu, tA⟩) (Typed.lam_inv facts tLeft formed) (Typed.lam_inv facts tRight formed)
        (lam_equal_inv facts formed same)

end Refutation

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]

/-- **The decision of a proper occurrence under abstractions**, by the codes. -/
def prefixedOccurs : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Bool
  | _, .head u, V, T => decide (S.R.isUniverse u) && occurs V T
  | _, .pi _ B, .lam V, .lam T => prefixedOccurs B V T
  | _, _, _, _ => false

theorem prefixedOccurs_sound : ∀ {n : Nat} (annotation left right : Tm Head n),
    prefixedOccurs (S := S) annotation left right = true → Prefixed S.R annotation left right
  | _, .head u, V, T, found => by
      simp only [prefixedOccurs, Bool.and_eq_true, decide_eq_true_eq] at found
      exact .base found.1 (occurs_sound V T found.2)
  | _, .pi _ B, .lam V, .lam T, found => .bind (prefixedOccurs_sound B V T found)
  | _, .var _, _, _, found | _, .const _, _, _, found | _, .sigma _ _, _, _, found
  | _, .id _ _ _, _, _, found | _, .lam _, _, _, found | _, .app _ _, _, _, found
  | _, .pair _ _, _, _, found | _, .fst _, _, _, found | _, .snd _, _, _, found
  | _, .refl _, _, _, found => by simp [prefixedOccurs] at found
  | _, .pi _ _, .var _, _, found | _, .pi _ _, .const _, _, found | _, .pi _ _, .head _, _, found
  | _, .pi _ _, .pi _ _, _, found | _, .pi _ _, .sigma _ _, _, found | _, .pi _ _, .id _ _ _, _, found
  | _, .pi _ _, .app _ _, _, found | _, .pi _ _, .pair _ _, _, found | _, .pi _ _, .fst _, _, found
  | _, .pi _ _, .snd _, _, found | _, .pi _ _, .refl _, _, found => by simp [prefixedOccurs] at found
  | _, .pi _ _, .lam _, .var _, found | _, .pi _ _, .lam _, .const _, found
  | _, .pi _ _, .lam _, .head _, found | _, .pi _ _, .lam _, .pi _ _, found
  | _, .pi _ _, .lam _, .sigma _ _, found | _, .pi _ _, .lam _, .id _ _ _, found
  | _, .pi _ _, .lam _, .app _ _, found | _, .pi _ _, .lam _, .pair _ _, found
  | _, .pi _ _, .lam _, .fst _, found | _, .pi _ _, .lam _, .snd _, found
  | _, .pi _ _, .lam _, .refl _, found => by simp [prefixedOccurs] at found

/-! ## The rule -/

/-- **A store equation read under its abstractions with a proper occurrence**, both sides at one
annotation code. -/
structure UnderShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Type where
  same : equation.2.1.code = equation.1.1.code
  prefixed : Prefixed S.R equation.1.1.code equation.1.2.code equation.2.2.code

/-- Read the shape from the codes; no budget. -/
def underShape {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Option (UnderShape equation) :=
  if same : equation.2.1.code = equation.1.1.code then
    if found : prefixedOccurs (S := S) equation.1.1.code equation.1.2.code equation.2.2.code = true then
      some ⟨same, prefixedOccurs_sound _ _ _ found⟩
    else none
  else none

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

omit [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] in
include facts roots heads algebra rigid complete in
/-- **Such an equation has no solution at any later context.** -/
theorem UnderShape.refutes {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (shape : UnderShape equation)
    {Δ : Context S.R} (σ : Δ ⟶ Θ) : ¬ (frames S.levels).Solves σ equation := by
  intro solved
  rw [solves_raw] at solved
  have tLeft := equation.1.2.typed.substitute σ.typed
  have tRight := equation.2.2.typed.substitute σ.typed
  rw [shape.same] at tRight
  exact prefixed_not_equal facts roots heads algebra rigid complete (shape.prefixed.subst _) Δ.formed tLeft tRight
    solved.2

/-- **The occurs rule under abstractions**: refute the store at the first such equation, read in either
orientation. -/
def underSearch {Θ : Context S.R} : (problem : EquationStore (TotalTerm Θ)) → Option (Found problem)
  | [] => none
  | equation :: rest =>
      match underShape equation with
      | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
          shape.refutes facts roots heads algebra rigid complete σ (solved equation List.mem_cons_self))
      | none =>
          match underShape (swap equation) with
          | some shape => some (.refuted fun ⟨_, σ, solved⟩ =>
              shape.refutes facts roots heads algebra rigid complete σ
                ((solves_swap σ equation).mpr (solved equation List.mem_cons_self)))
          | none => (underSearch rest).map (Found.keepLeft equation)

variable [DecidableRel S.R.headEq] [DecidableRel S.R.cumulative]
variable (declared : DeclaredTypesFormed S.R) (choices : ExecutableChecking.HeadChoices S.R)
  (reducer : ExecutableReduction.Reducer S.R) (root : ExecutableReduction.RootEvaluator S.R)
  (normalizes : ∀ {Θ : Context S.R} {type : TypeOver Θ} (term : Term Θ type),
    ∃ code : Tm Head Θ.arity, ContextualDependentNormalChecking.Normal (S := S) code ∧
      Equal S.R Θ.raw term.code code type.code)
  (certifyNormal : ∀ {n : Nat} (term : Tm Head n),
    Option (PLift (ContextualDependentNormalChecking.Normal (S := S) term)))
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

/-- The refutation of the occurs rule under abstractions on the prepared store, moved back to the store. -/
def underOf {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)} (prepared : Update S.levels problem) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  match underSearch facts roots heads algebra rigid complete prepared.remaining with
  | some (.refuted absent) => some ⟨fun solvable => absent (prepared.solvable_iff.mp solvable)⟩
  | _ => none

/-- The occurs rule under abstractions on the prepared store. -/
def underPrepared (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Option (PLift (¬ (frames S.levels).Solvable problem)) :=
  underOf facts roots heads algebra rigid complete
    (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem)

/-- **One ranked occurs round**: the occurs rule under abstractions on the prepared store, then the
ranked round. -/
def rankedOccursRound (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    Round S.levels (weightRank facts roots heads algebra rigid complete) problem :=
  match underPrepared facts roots heads algebra rigid complete root rootComplete fuel problem with
  | some absent => .refuted absent.down
  | none => rankedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
      certifyNormal headTypingUnique rootComplete fuel problem

/-- **The ranked occurs family**, at the weight rank. -/
noncomputable def rankedOccursFamily : ContextualDependentDecisiveDriver.Family S.levels where
  rank := weightRank facts roots heads algebra rigid complete
  round fuel := rankedOccursRound facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete fuel

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- **The ranked occurs round is eventually constant on every store.** -/
theorem rankedOccursRound_const {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    EventuallyConst fun fuel => rankedOccursRound facts roots heads algebra rigid complete declared choices reducer
      root normalizes certifyNormal headTypingUnique rootComplete fuel problem := by
  have refuting : EventuallyConst fun fuel =>
      (underPrepared facts roots heads algebra rigid complete root rootComplete fuel problem).isSome :=
    EventuallyConst.comp (fun prepared => (underOf facts roots heads algebra rigid complete prepared).isSome)
      (prepare_const root rootComplete facts roots heads problem)
  have ranked := rankedRound_const facts roots heads algebra rigid complete declared choices reducer root normalizes
    certifyNormal headTypingUnique rootComplete stable problem
  refine round_const_of_view ?_
  have shape : ∀ fuel, roundView (rankedOccursRound facts roots heads algebra rigid complete declared choices reducer
      root normalizes certifyNormal headTypingUnique rootComplete fuel problem) =
      (fun pair : Bool × Option (Option (Update S.levels problem)) => if pair.1 then some none else pair.2)
        ((underPrepared facts roots heads algebra rigid complete root rootComplete fuel problem).isSome,
          roundView (rankedRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete fuel problem)) := by
    intro fuel
    unfold rankedOccursRound
    split
    · rename_i absent computed
      simp only [computed, Option.isSome_some, if_true, roundView]
    · rename_i computed
      simp only [computed, Option.isSome_none, Bool.false_eq_true, if_false]
  exact EventuallyConst.of_eq shape (EventuallyConst.comp
    (fun pair : Bool × Option (Option (Update S.levels problem)) => if pair.1 then some none else pair.2)
    (EventuallyConst.pair refuting (EventuallyConst.comp roundView ranked)))

include stable in
/-- **The ranked occurs family settles** on every class of stores on which, at each nonempty store and
from some budget on, its round is not stuck and keeps every residual store in the class. -/
noncomputable def rankedOccursSettledOfConst (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop)
    (eventual : ∀ {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)}, holds problem → problem ≠ [] →
      ∃ bound, ∀ larger, bound ≤ larger →
        rankedOccursRound facts roots heads algebra rigid complete declared choices reducer root normalizes
            certifyNormal headTypingUnique rootComplete larger problem ≠ .stuck ∧
        ∀ {update : Update S.levels problem}
          {smaller : ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete update.remaining)
            (weightRank facts roots heads algebra rigid complete problem)},
          rankedOccursRound facts roots heads algebra rigid complete declared choices reducer root normalizes
              certifyNormal headTypingUnique rootComplete larger problem = .progress update smaller →
            holds update.remaining) :
    ContextualDependentDecisiveDriver.Settled
      (rankedOccursFamily facts roots heads algebra rigid complete declared choices reducer root normalizes
        certifyNormal headTypingUnique rootComplete) :=
  Settled.ofConst _ (fun problem => rankedOccursRound_const facts roots heads algebra rigid complete declared choices
    reducer root normalizes certifyNormal headTypingUnique rootComplete stable problem) holds eventual

end ContextualDependentOccursFull
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
