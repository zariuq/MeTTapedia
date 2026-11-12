import Mettapedia.TypeTheory.BubbleArithChecker

/-!
# A frame that knows a definition is the instantiated frame, for typing too

`KnowledgeSolvedForm.solved_conversion_iff` says that at a frame whose knowledge is one definition
`x ≐ u`, conversion is the conversion of the instances at `x := u`. This module proves the same for
typing, in both directions.

* `lift_of_instance`: a typing of the instance lifts to the frame. The proof is by recursion on
  the term: the syntax-directed judgment reads the typing of the instance, and at each ask the
  frame converts a type with its instance (`KnowledgeSolvedForm.converts_with_instance`).
* `typedKnowing_iff_instance`: a term is typed at `A` at the frame exactly when its instance is
  typed at the instance of `A` in the bubble.
* `definition_subject_reduction`: so a typed term keeps its type at the frame along any
  computation by rules that keep types.
* `Controls.arith_definition_iff_check`: and over the arithmetic bubbles typing at the frame of a
  definition is decided by the checker, run on the instance.

Whatever the bubble's typing has, the frame of a definition has: it is the instantiation, not
carried out.

## Controls

* `Controls.constant_function_checked_at_frame`: in `n : nat, v : Vec n` with `n ≐ 0` known, the
  function `λ (m : nat). v` is typed at `Π (m : nat). Vec 0`; the checker says so on the instance.
* `Controls.vec_one_refused_at_frame`: there `v` is not typed at `Vec 1`; the checker refuses the
  instance.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.KnowledgeDefinitionTransfer

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleTypingInside
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic
open Mettapedia.TypeTheory.BubbleSubjectReduction
open Mettapedia.TypeTheory.BubbleTypingAdmission
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.KnowledgeUnderBinders
open Mettapedia.TypeTheory.KnowledgeSubstitution
open Mettapedia.TypeTheory.KnowledgeSolvedForm
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The store of a frame that knows one definition: the variable `k` is `defined`. -/
abbrev defStore (k : Nat) (defined : Expr Base Const) : EquationStore (Expr Base Const) :=
  [(bvar k, shiftN (k + 1) defined)]

/-- Under a binder the definition is about the next variable. -/
theorem shiftStore_defStore (k : Nat) (defined : Expr Base Const) :
    shiftStore (defStore k defined) = defStore (k + 1) defined :=
  congrArg (fun x => [(x, shiftN (k + 1 + 1) defined)])
    (shiftAt_bvar_ge (Base := Base) (Const := Const) (Nat.not_lt_zero k))

/-- At the frame of a definition, a typing moves to every type whose instance converts with the
instance of its type. -/
theorem moveByInstance {rules : Expr Base Const → Expr Base Const → Prop}
    (shiftStable : ShiftStable rules) {k : Nat} {defined : Expr Base Const}
    {Γ : List (Expr Base Const)} {e E X : Expr Base Const}
    (typed : TypedKnowing rules (defStore k defined) Γ e E)
    (instances : Convertible rules (substAt k defined E) (substAt k defined X)) :
    TypedKnowing rules (defStore k defined) Γ e X :=
  .move typed
    (convertibleKnowing_of_instances shiftStable k defined (List.mem_singleton_self _) instances)

/-- **A typing of the instance lifts to the frame of the definition.** -/
theorem lift_of_instance {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    (coherent : Coherent (Convertible rules)) {Θ : List (Expr Base Const)}
    {defined C : Expr Base Const} (typedU : HasTypeInside rules Θ defined C) :
    ∀ (e : Expr Base Const) (Δ : List (Expr Base Const)) (T' : Expr Base Const),
      HasTypeInside rules (substCtx defined Δ ++ Θ) (substAt Δ.length defined e) T' →
        ∃ E, TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) e E ∧
          Convertible rules (substAt Δ.length defined E) T'
  | .bvar i, Δ, T', typed => by
      cases found : (Δ ++ C :: Θ)[i]? with
      | none =>
          exfalso
          have long : (Δ ++ C :: Θ).length ≤ i := List.getElem?_eq_none_iff.mp found
          have above : Δ.length < i := by
            simp at long
            omega
          have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) (bvar (i - 1)) T' := by
            have copy := typed
            rw [substAt_bvar_gt defined above] at copy
            exact copy
          obtain ⟨_, synth, _⟩ := synth_of_typed coherent typed'
          cases synth with
          | var lookup' =>
              have short : (substCtx defined Δ ++ Θ).length ≤ i - 1 := by
                simp [length_substCtx] at long ⊢
                omega
              rw [List.getElem?_eq_none_iff.mpr short] at lookup'
              cases lookup'
      | some T =>
          rcases var_subst_lookup defined C Θ Δ i T found with
            ⟨atVariable, same⟩ | ⟨j, T₀, lookup', atTerm, atType⟩
          · refine ⟨shiftN (i + 1) T, .var found, ?_⟩
            have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) (shiftN Δ.length defined)
                T' := by
              have copy := typed
              rw [atVariable, substAt_bvar_eq] at copy
              exact copy
            have lifted : HasTypeInside rules (substCtx defined Δ ++ Θ)
                (shiftN Δ.length defined) (shiftN Δ.length C) := by
              have raw :=
                typedKnowing_lift shiftStable (typedKnowing_of_inside typedU []) (substCtx defined Δ)
              rw [length_substCtx, liftStore_nil] at raw
              exact typedKnowing_discharge shiftStable raw
                (fun _ member => absurd member List.not_mem_nil)
            rw [atVariable, same, substAt_shiftN_cancel defined C Δ.length Δ.length (Nat.le_refl _)]
            exact typed_unique coherent lifted typed'
          · refine ⟨shiftN (i + 1) T, .var found, ?_⟩
            have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) (bvar j) T' := by
              rw [← atTerm]
              exact typed
            rw [atType]
            exact typed_unique coherent (Typed.var lookup') typed'
  | .univ, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) Expr.univ T' := typed
      obtain ⟨_, synth, _⟩ := synth_of_typed coherent typed'
      cases synth
  | .prop, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) Expr.prop T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth
      exact ⟨Expr.univ, .prop, moved⟩
  | .base b, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) (Expr.base b) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth
      exact ⟨Expr.univ, .base b, moved⟩
  | .pi A B, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.pi (substAt Δ.length defined A) (substAt (Δ.length + 1) defined B)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | pi synthA atA synthB atB =>
          obtain ⟨EA, frameA, convA⟩ :=
            lift_of_instance substStable shiftStable coherent typedU A Δ _ synthA.typed
          obtain ⟨EB, frameB, convB⟩ :=
            lift_of_instance substStable shiftStable coherent typedU B (A :: Δ) _ synthB.typed
          have domain : TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) A Expr.univ :=
            moveByInstance shiftStable frameA (Relation.EqvGen.trans _ _ _ convA atA)
          have body : TypedKnowing rules (shiftStore (defStore Δ.length defined))
              (A :: (Δ ++ C :: Θ)) B Expr.univ := by
            rw [shiftStore_defStore]
            exact moveByInstance shiftStable frameB (Relation.EqvGen.trans _ _ _ convB atB)
          exact ⟨Expr.univ, .pi domain body, moved⟩
  | .lam A b, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.lam (substAt Δ.length defined A) (substAt (Δ.length + 1) defined b)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | lam synthA atA synthb =>
          obtain ⟨EA, frameA, convA⟩ :=
            lift_of_instance substStable shiftStable coherent typedU A Δ _ synthA.typed
          obtain ⟨EB, frameB, convB⟩ :=
            lift_of_instance substStable shiftStable coherent typedU b (A :: Δ) _ synthb.typed
          have domain : TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) A Expr.univ :=
            moveByInstance shiftStable frameA (Relation.EqvGen.trans _ _ _ convA atA)
          have body : TypedKnowing rules (shiftStore (defStore Δ.length defined))
              (A :: (Δ ++ C :: Θ)) b EB := by
            rw [shiftStore_defStore]
            exact frameB
          refine ⟨Expr.pi A EB, .lam domain body, ?_⟩
          exact Relation.EqvGen.trans _ _ _ (convertible_piBody _ convB) moved
  | .app f a, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.app (substAt Δ.length defined f) (substAt Δ.length defined a)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | @app _ _ _ F A₁ A₂ B₁ synthf atF syntha atA =>
          obtain ⟨Ef, framef, convf⟩ :=
            lift_of_instance substStable shiftStable coherent typedU f Δ _ synthf.typed
          obtain ⟨Ea, framea, conva⟩ :=
            lift_of_instance substStable shiftStable coherent typedU a Δ _ syntha.typed
          have function : TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) f
              (Expr.pi (shiftAt Δ.length A₁) (shiftAt (Δ.length + 1) B₁)) := by
            refine moveByInstance shiftStable framef ?_
            show Convertible rules (substAt Δ.length defined Ef)
              (Expr.pi (substAt Δ.length defined (shiftAt Δ.length A₁))
                (substAt (Δ.length + 1) defined (shiftAt (Δ.length + 1) B₁)))
            rw [substAt_shiftAt_cancel, substAt_shiftAt_cancel]
            exact Relation.EqvGen.trans _ _ _ convf atF
          have argument : TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) a
              (shiftAt Δ.length A₁) := by
            refine moveByInstance shiftStable framea ?_
            rw [substAt_shiftAt_cancel]
            exact Relation.EqvGen.trans _ _ _ conva atA
          refine ⟨substAt 0 a (shiftAt (Δ.length + 1) B₁), .app function argument, ?_⟩
          have key : substAt Δ.length defined (substAt 0 a (shiftAt (Δ.length + 1) B₁)) =
              substAt 0 (substAt Δ.length defined a)
                (substAt (Δ.length + 1) defined (shiftAt (Δ.length + 1) B₁)) :=
            substAt_substAt defined a (shiftAt (Δ.length + 1) B₁) Δ.length 0
          rw [key, substAt_shiftAt_cancel]
          exact moved
  | .const τ c, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) (Expr.const τ c) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth
      refine ⟨tyToExpr τ, .const τ c, ?_⟩
      rw [substAt_tyToExpr]
      exact moved
  | .tyFam b, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) (Expr.tyFam b) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth
      exact ⟨Expr.pi (Expr.base b) Expr.univ, .tyFam b, moved⟩
  | .top, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) Expr.top T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth
      exact ⟨Expr.prop, .top, moved⟩
  | .bot, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ) Expr.bot T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth
      exact ⟨Expr.prop, .bot, moved⟩
  | .and p q, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.and (substAt Δ.length defined p) (substAt Δ.length defined q)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | and synthp atP synthq atQ =>
          obtain ⟨EP, framep, convp⟩ :=
            lift_of_instance substStable shiftStable coherent typedU p Δ _ synthp.typed
          obtain ⟨EQ, frameq, convq⟩ :=
            lift_of_instance substStable shiftStable coherent typedU q Δ _ synthq.typed
          exact ⟨Expr.prop,
            .and (moveByInstance shiftStable framep (Relation.EqvGen.trans _ _ _ convp atP))
              (moveByInstance shiftStable frameq (Relation.EqvGen.trans _ _ _ convq atQ)), moved⟩
  | .or p q, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.or (substAt Δ.length defined p) (substAt Δ.length defined q)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | or synthp atP synthq atQ =>
          obtain ⟨EP, framep, convp⟩ :=
            lift_of_instance substStable shiftStable coherent typedU p Δ _ synthp.typed
          obtain ⟨EQ, frameq, convq⟩ :=
            lift_of_instance substStable shiftStable coherent typedU q Δ _ synthq.typed
          exact ⟨Expr.prop,
            .or (moveByInstance shiftStable framep (Relation.EqvGen.trans _ _ _ convp atP))
              (moveByInstance shiftStable frameq (Relation.EqvGen.trans _ _ _ convq atQ)), moved⟩
  | .imp p q, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.imp (substAt Δ.length defined p) (substAt Δ.length defined q)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | imp synthp atP synthq atQ =>
          obtain ⟨EP, framep, convp⟩ :=
            lift_of_instance substStable shiftStable coherent typedU p Δ _ synthp.typed
          obtain ⟨EQ, frameq, convq⟩ :=
            lift_of_instance substStable shiftStable coherent typedU q Δ _ synthq.typed
          exact ⟨Expr.prop,
            .imp (moveByInstance shiftStable framep (Relation.EqvGen.trans _ _ _ convp atP))
              (moveByInstance shiftStable frameq (Relation.EqvGen.trans _ _ _ convq atQ)), moved⟩
  | .not p, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.not (substAt Δ.length defined p)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | not synthp atP =>
          obtain ⟨EP, framep, convp⟩ :=
            lift_of_instance substStable shiftStable coherent typedU p Δ _ synthp.typed
          exact ⟨Expr.prop,
            .not (moveByInstance shiftStable framep (Relation.EqvGen.trans _ _ _ convp atP)), moved⟩
  | .eq a b, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.eq (substAt Δ.length defined a) (substAt Δ.length defined b)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | eq syntha synthb same =>
          obtain ⟨Ea, framea, conva⟩ :=
            lift_of_instance substStable shiftStable coherent typedU a Δ _ syntha.typed
          obtain ⟨Eb, frameb, convb⟩ :=
            lift_of_instance substStable shiftStable coherent typedU b Δ _ synthb.typed
          have right : TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) b Ea :=
            moveByInstance shiftStable frameb
              (Relation.EqvGen.trans _ _ _ convb
                (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ same)
                  (Relation.EqvGen.symm _ _ conva)))
          exact ⟨Expr.prop, .eq framea right, moved⟩
  | .all A b, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.all (substAt Δ.length defined A) (substAt (Δ.length + 1) defined b)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | all synthA atA synthb atP =>
          obtain ⟨EA, frameA, convA⟩ :=
            lift_of_instance substStable shiftStable coherent typedU A Δ _ synthA.typed
          obtain ⟨EB, frameB, convB⟩ :=
            lift_of_instance substStable shiftStable coherent typedU b (A :: Δ) _ synthb.typed
          have domain : TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) A Expr.univ :=
            moveByInstance shiftStable frameA (Relation.EqvGen.trans _ _ _ convA atA)
          have body : TypedKnowing rules (shiftStore (defStore Δ.length defined))
              (A :: (Δ ++ C :: Θ)) b Expr.prop := by
            rw [shiftStore_defStore]
            exact moveByInstance shiftStable frameB (Relation.EqvGen.trans _ _ _ convB atP)
          exact ⟨Expr.prop, .all domain body, moved⟩
  | .ex A b, Δ, T', typed => by
      have typed' : HasTypeInside rules (substCtx defined Δ ++ Θ)
          (Expr.ex (substAt Δ.length defined A) (substAt (Δ.length + 1) defined b)) T' := typed
      obtain ⟨_, synth, moved⟩ := synth_of_typed coherent typed'
      cases synth with
      | ex synthA atA synthb atP =>
          obtain ⟨EA, frameA, convA⟩ :=
            lift_of_instance substStable shiftStable coherent typedU A Δ _ synthA.typed
          obtain ⟨EB, frameB, convB⟩ :=
            lift_of_instance substStable shiftStable coherent typedU b (A :: Δ) _ synthb.typed
          have domain : TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) A Expr.univ :=
            moveByInstance shiftStable frameA (Relation.EqvGen.trans _ _ _ convA atA)
          have body : TypedKnowing rules (shiftStore (defStore Δ.length defined))
              (A :: (Δ ++ C :: Θ)) b Expr.prop := by
            rw [shiftStore_defStore]
            exact moveByInstance shiftStable frameB (Relation.EqvGen.trans _ _ _ convB atP)
          exact ⟨Expr.prop, .ex domain body, moved⟩

/-- **Typing at the frame of a definition is typing of the instance.** -/
theorem typedKnowing_iff_instance {rules : Expr Base Const → Expr Base Const → Prop}
    (substStable : SubstitutionStable rules) (shiftStable : ShiftStable rules)
    (coherent : Coherent (Convertible rules)) {Θ : List (Expr Base Const)}
    {defined C : Expr Base Const} (typedU : HasTypeInside rules Θ defined C)
    (Δ : List (Expr Base Const)) {e A : Expr Base Const} :
    TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) e A ↔
      HasTypeInside rules (substCtx defined Δ ++ Θ) (substAt Δ.length defined e)
        (substAt Δ.length defined A) := by
  constructor
  · intro typed
    exact typedKnowing_subst_solution substStable shiftStable typedU typed Δ rfl
      (definition_solves Δ.length defined)
  · intro typed
    obtain ⟨E, frame, conv⟩ :=
      lift_of_instance substStable shiftStable coherent typedU e Δ _ typed
    exact moveByInstance shiftStable frame conv

/-- A computation by the rules is carried by an instantiation. -/
theorem reduces_substAt {rules : Expr Base Const → Expr Base Const → Prop}
    (stable : SubstitutionStable rules) {e e' : Expr Base Const}
    (reduced : Relation.ReflTransGen (Rewrite rules) e e') (k : Nat) (s : Expr Base Const) :
    Relation.ReflTransGen (Rewrite rules) (substAt k s e) (substAt k s e') := by
  induction reduced with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (rewrite_substAt stable step k s)

/-- **Subject reduction at the frame of a definition**: a term typed at the frame keeps its type
along any computation by rules that keep types. -/
theorem definition_subject_reduction {rules : Expr Base Const → Expr Base Const → Prop}
    (admitted : TypingAdmission rules) {Θ : List (Expr Base Const)}
    {defined C : Expr Base Const} (typedU : HasTypeInside rules Θ defined C)
    (Δ : List (Expr Base Const)) {e e' A : Expr Base Const}
    (typed : TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) e A)
    (reduced : Relation.ReflTransGen (Rewrite rules) e e') :
    TypedKnowing rules (defStore Δ.length defined) (Δ ++ C :: Θ) e' A :=
  (typedKnowing_iff_instance admitted.substStable admitted.shiftStable admitted.coherent typedU
    Δ).mpr
    (admitted.reduces
      ((typedKnowing_iff_instance admitted.substStable admitted.shiftStable admitted.coherent
        typedU Δ).mp typed)
      (reduces_substAt admitted.substStable reduced Δ.length defined))

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.TypeTheory.BubbleTypingAlgorithmic.Controls
open Mettapedia.TypeTheory.KnowledgeSolvedForm.Controls
open Mettapedia.TypeTheory.BubbleArithChecker

/-- **Over the arithmetic bubbles, typing at the frame of a definition is decided by the checker
on the instance.** -/
theorem arith_definition_iff_check (plus : Bool) {Θ : List AExpr} {defined C : AExpr}
    (typedU : HasTypeInside (bubbleRules plus) Θ defined C) (Δ : List AExpr) {e A : AExpr} :
    TypedKnowing (bubbleRules plus) (defStore Δ.length defined) (Δ ++ C :: Θ) e A ↔
      check plus (substCtx defined Δ ++ Θ) (substAt Δ.length defined e)
        (substAt Δ.length defined A) = true :=
  (typedKnowing_iff_instance (bubbleRules_stable plus) (bubbleRules_shiftStable plus)
    (arith_coherent plus) typedU Δ).trans (typed_iff_check plus)

/-- Zero is a number in the bubble of the recursion equations. -/
theorem zero_typed : HasTypeInside (bubbleRules false) [] zeroE natType :=
  Typed.const _ ArithConst.zero

/-- **The checker types at a frame.** In `n : nat, v : Vec n` with `n ≐ 0` known, the function
`λ (m : nat). v` is typed at `Π (m : nat). Vec 0`. -/
theorem constant_function_checked_at_frame :
    TypedKnowing (bubbleRules false) (defStore 1 zeroE) vecContext
      (Expr.lam natType (bvar 1)) (Expr.pi natType (vec zeroE)) :=
  (arith_definition_iff_check false zero_typed [vec (bvar 0)]).mpr (by decide)

/-- **The checker refuses at a frame.** There `v` is not typed at `Vec 1`, with the conversion
rule and the frame's knowledge available at every node. -/
theorem vec_one_refused_at_frame :
    ¬ TypedKnowing (bubbleRules false) (defStore 1 zeroE) vecContext (bvar 0)
      (vec (succE zeroE)) := by
  intro typed
  have checked := (arith_definition_iff_check false zero_typed [vec (bvar 0)]).mp typed
  exact absurd checked (by decide)

end Controls

/-! ## Axiom audit -/

#print axioms lift_of_instance
#print axioms typedKnowing_iff_instance
#print axioms definition_subject_reduction
#print axioms Controls.arith_definition_iff_check
#print axioms Controls.constant_function_checked_at_frame
#print axioms Controls.vec_one_refused_at_frame

end Mettapedia.TypeTheory.KnowledgeDefinitionTransfer
