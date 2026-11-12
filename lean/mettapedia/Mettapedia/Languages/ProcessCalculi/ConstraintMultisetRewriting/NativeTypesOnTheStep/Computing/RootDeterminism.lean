import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.DeclaredConfluence

/-!
# What root determinism gives, and the smallest declarations outside the definitional class

`RootDeterministic d` says that no term has two different declared reducts at its root. It is the
only check of `declare` that runs at declaration time.

**What it gives.** It is necessary for the class: every declaration whose package is a constructor
system is root-deterministic (`rootDeterministic_of_presentation`). On its own it makes the root
firing of one call deterministic, and nothing more.

**What it does not give.** Each of the following declarations over the vector package is
root-deterministic, and each fails one property of the definitional reading. Each is the smallest
witness of one cause.

* **Overlap below the root, so two answers.** `add 0 b ↦ b` with `add (add a b) c ↦ 0`: the term
  `add (add 0 1) 0` has the two normal reducts `0` and `add 1 0` (`nest_two_answers`), so the
  conversion is not Church–Rosser (`nest_not_churchRosser`).
* **Non-termination.** `lookup k v i ↦ succ (lookup k v i)` is a constructor system, hence
  Church–Rosser (`loop_churchRosser`), yet the ground call `lookup 1 [2] (fz 0)` reduces forever and
  has no normal form (`loop_no_answer`). Its knowledge solves `t ≐ succ t` for that call
  (`loop_solvable`), which the rigid package refutes by a clash (`rigid_loop_unsolvable`).
* **Ill-typed right side.** `add 0 b ↦ junk`, with `junk` undeclared, is root-deterministic, and its
  root step takes a typed call to an untyped term (`junk_not_preserving`). The typed equality never
  uses that step (it relates typed terms only), so the declared computation and the conversion
  disagree: the call converts to `junk` untyped and equals it at no type (`junk_disagreement`).
* **Partiality.** `add 0 b ↦ b` alone is a constructor system (`half_churchRosser`), terminating and
  root-deterministic, but the ground call `add 1 0` is stuck: a closed normal term of `nat` that is no
  numeral (`stuck_normal`, `stuck_not_numeral`). It is not convertible with `1`
  (`stuck_not_one`); completing the definition by its successor row makes it convertible
  (`completed_converts`). A refutation drawn from a partial definition does not survive the row
  that completes it.
* **Effects.** A call whose answer is read from the store answers `0` at one state and `1` at
  another. A root computation that agrees with both readings is not root-deterministic
  (`effect_not_rootDeterministic`) and identifies `0` and `1` in the typed equality
  (`effect_identifies`), which the rigid package refutes. One such computation exists
  (`readComputation`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.RootDeterminism

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (System LeftSide Pattern ConstructorPresentation mentionsConst)
open ProgrammingOnTheStep.VectorPackage
open ProgrammingOnTheStep.VectorPrograms (one oneVec one_typed oneVec_typed fzZero_typed
  lookupRow_typed natTerm)
open NativeTypesOnTheStep.VectorAppend (AddStep vrules)

/-! ## What root determinism gives -/

/-- **Root determinism is necessary for the class**: a declaration whose declared package is a
constructor system is root-deterministic. -/
theorem rootDeterministic_of_presentation {Head : Type} (R : Rules Head) (d : RootComputation Head)
    (equations : ConstructorPresentation (declare R d)) : RootDeterministic d :=
  fun _ _ _ step step' =>
    ConstructorSystem.root_deterministic equations (declare_step step) (declare_step step')

/-- Head equality of the vector package is symmetric. -/
theorem headEq_symm {h h' : Tower.Head} (same : rules.headEq h h') : rules.headEq h' h :=
  Interface.DependentFull.Controls.setting.levels.headEq_symm same

/-! ## Overlap below the root -/

section Nest

/-- `add 0 b ↦ b` and `add (add a b) c ↦ 0`. -/
inductive NestStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | zero {n : Nat} (b : Tower.Tm n) : NestStep (.app (.app (.const addN) (.const zeroN)) b) b
  | nest {n : Nat} (a b c : Tower.Tm n) :
      NestStep (.app (.app (.const addN) (.app (.app (.const addN) a) b)) c) (.const zeroN)

def nestComputation : RootComputation Tower.Head where
  step l r := NestStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .zero b => NestStep.zero (Presentation.rename ρ b)
      | .nest a b c =>
          NestStep.nest (Presentation.rename ρ a) (Presentation.rename ρ b) (Presentation.rename ρ c)
  substitute := by
    intro n m σ left right h
    exact match h with
      | .zero b => NestStep.zero (subst σ b)
      | .nest a b c => NestStep.nest (subst σ a) (subst σ b) (subst σ c)

abbrev nrules : Rules Tower.Head := declare rules nestComputation

/-- **The nested declaration is root-deterministic.** -/
theorem nest_rootDeterministic : RootDeterministic nestComputation := by
  intro n l r r' h h'
  cases h with
  | zero b => cases h' with
    | zero => rfl
  | nest a b c => cases h' with
    | nest => rfl

/-- `add (add 0 1) 0`. -/
def nestTerm : Tower.Tm 0 :=
  .app (.app (.const addN) (.app (.app (.const addN) (.const zeroN)) one)) (.const zeroN)

/-- `add 1 0`. -/
def sumTerm : Tower.Tm 0 := .app (.app (.const addN) one) (.const zeroN)

theorem nest_to_zero : StepCore nrules.computation nrules.headEq nestTerm (.const zeroN) :=
  .root (declare_step (NestStep.nest (.const zeroN) one (.const zeroN)))

theorem nest_to_sum : StepCore nrules.computation nrules.headEq nestTerm sumTerm :=
  .congAppFun (.congAppArg (.root (declare_step (NestStep.zero one))))

theorem zero_normal_nest : ConstructorSystem.Normal nrules (.const zeroN : Tower.Tm 0) := by
  intro t h
  cases h with
  | root h => rcases h with h | h <;> cases h

theorem sum_normal_nest : ConstructorSystem.Normal nrules sumTerm := by
  intro t h
  cases h with
  | root h => rcases h with h | h <;> cases h
  | congAppFun h =>
      cases h with
      | root h => rcases h with h | h <;> cases h
      | congAppFun h =>
          cases h with
          | root h => rcases h with h | h <;> cases h
      | congAppArg h =>
          cases h with
          | root h => rcases h with h | h <;> cases h
          | congAppFun h =>
              cases h with
              | root h => rcases h with h | h <;> cases h
          | congAppArg h =>
              cases h with
              | root h => rcases h with h | h <;> cases h
  | congAppArg h =>
      cases h with
      | root h => rcases h with h | h <;> cases h

/-- **Two answers**: `add (add 0 1) 0` reaches the two distinct normal forms `0` and `add 1 0`. -/
theorem nest_two_answers :
    StepStar nrules nestTerm (.const zeroN) ∧ ConstructorSystem.Normal nrules (.const zeroN : Tower.Tm 0) ∧
      StepStar nrules nestTerm sumTerm ∧ ConstructorSystem.Normal nrules sumTerm ∧
        (.const zeroN : Tower.Tm 0) ≠ sumTerm :=
  ⟨.single nest_to_zero, zero_normal_nest, .single nest_to_sum, sum_normal_nest, by decide⟩

/-- **Root determinism does not give confluence.** -/
theorem nest_not_churchRosser : ¬ ChurchRosser nrules := by
  intro church
  have conversion : Conv nrules.headEq (.const zeroN : Tower.Tm 0) sumTerm nrules.computation :=
    .trans _ _ _ (.symm _ _ (.rel _ _ nest_to_zero)) (.rel _ _ nest_to_sum)
  obtain ⟨common, left, right⟩ := church conversion
  have fromZero := ConstructorSystem.Normal.stepStar zero_normal_nest left
  have fromSum := ConstructorSystem.Normal.stepStar sum_normal_nest right
  exact absurd (fromZero.symm.trans fromSum) (by decide)

end Nest

/-! ## Non-termination -/

section Loop

/-- `lookup k v i ↦ succ (lookup k v i)`. -/
inductive LoopStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | unfold {n : Nat} (k v i : Tower.Tm n) :
      LoopStep (.app (.app (.app (.const lookupN) k) v) i)
        (.app (.const succN) (.app (.app (.app (.const lookupN) k) v) i))

def loopComputation : RootComputation Tower.Head where
  step l r := LoopStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .unfold k v i =>
          LoopStep.unfold (Presentation.rename ρ k) (Presentation.rename ρ v) (Presentation.rename ρ i)
  substitute := by
    intro n m σ left right h
    exact match h with
      | .unfold k v i => LoopStep.unfold (subst σ k) (subst σ v) (subst σ i)

abbrev lrules : Rules Tower.Head := declare rules loopComputation

abbrev llevels : LevelModel lrules Nat := declareLevels levels loopComputation

theorem loop_rootDeterministic : RootDeterministic loopComputation := by
  intro n l r r' h h'
  cases h with
  | unfold k v i => cases h' with
    | unfold => rfl

/-- The one equation of the loop, over three variables. -/
inductive LoopSchema : {arity : Nat} → Tower.Tm arity → Tower.Tm arity → Prop
  | unfold : LoopSchema (arity := 3) (.app (.app (.app (.const lookupN) (.var 2)) (.var 1)) (.var 0))
      (.app (.const succN) (.app (.app (.app (.const lookupN) (.var 2)) (.var 1)) (.var 0)))

def loopPresentation : SchemaPresentation lrules where
  schema := LoopSchema
  sound := by
    intro arity ambient left right rule substitution
    cases rule with
    | unfold => exact Or.inr (LoopStep.unfold (substitution 2) (substitution 1) (substitution 0))
  cover := by
    intro n source target step
    rcases step with impossible | step
    · exact impossible.elim
    · exact match step with
        | .unfold k v i => ⟨3, _, _, Fin.cases i (Fin.cases v (fun _ => k)), .unfold, rfl, rfl⟩

/-- **The loop is a constructor system**: one linear left side, covered right side. -/
def loopSystem : System Tower.Head where
  schema := LoopSchema
  defined name := name = lookupN
  arity _ := 3
  left := by
    intro m left right rule
    refine ⟨lookupN, rfl, by decide, ?_⟩
    cases rule with
    | unfold => exact .app (.app (.app (.const lookupN) (.var 2)) (.var 1)) (.var 0)
  linear := by
    intro arity left right rule
    cases rule with
    | unfold => unfold LeftLinear; decide
  covered := by
    intro m left right rule
    cases rule with
    | unfold => decide
  determined := by
    intro m m' n n' left right left' right' rule rule' instantiation instantiation' same develop
    cases rule with
    | unfold =>
        cases rule' with
        | unfold =>
            have same' : Tm.app (.app (.app (.const lookupN) (instantiation 2)) (instantiation 1))
                (instantiation 0) =
              Tm.app (.app (.app (.const lookupN) (instantiation' 2)) (instantiation' 1))
                (instantiation' 0) := same
            obtain ⟨function, third⟩ := Tm.app.inj same'
            obtain ⟨function', second⟩ := Tm.app.inj function
            obtain ⟨-, first⟩ := Tm.app.inj function'
            show Tm.app (.const succN) (.app (.app (.app (.const lookupN) (develop (instantiation 2)))
                (develop (instantiation 1))) (develop (instantiation 0))) =
              Tm.app (.const succN) (.app (.app (.app (.const lookupN) (develop (instantiation' 2)))
                (develop (instantiation' 1))) (develop (instantiation' 0)))
            rw [first, second, third]

def loopConstructors : ConstructorPresentation lrules where
  presentation := loopPresentation
  system := loopSystem
  same _ _ := Iff.rfl
  symmetric := ⟨fun _ _ same => headEq_symm same⟩

/-- **The loop is Church–Rosser.** -/
theorem loop_churchRosser : ChurchRosser lrules := loopConstructors.churchRosser

/-- Terms built from constants by application. -/
inductive Spine : {n : Nat} → Tower.Tm n → Prop
  | const {n : Nat} (name : DeclName) : Spine (.const name : Tower.Tm n)
  | app {n : Nat} {f a : Tower.Tm n} : Spine f → Spine a → Spine (.app f a)

/-- A step of the loop package inside a spine mentions `lookup`. -/
theorem spine_step_mentions {n : Nat} {t t' : Tower.Tm n}
    (step : StepCore lrules.computation lrules.headEq t t') (spine : Spine t) :
    mentionsConst lookupN t = true := by
  induction step with
  | root h =>
      rcases h with h | h
      · cases h
      · cases h
        simp [mentionsConst]
  | congAppFun _ ih =>
      cases spine with
      | app sf _ => simp [mentionsConst, ih sf]
  | congAppArg _ ih =>
      cases spine with
      | app _ sa => simp [mentionsConst, ih sa]
  | betaPi body a =>
      cases spine with
      | app sf _ => cases sf
  | _ => cases spine

/-- A spine without `lookup` is normal in the loop package. -/
theorem spine_normal {n : Nat} {t : Tower.Tm n} (spine : Spine t)
    (absent : mentionsConst lookupN t = false) : ConstructorSystem.Normal lrules t := by
  intro t' step
  have mentions := spine_step_mentions step spine
  rw [absent] at mentions
  cases mentions

theorem one_spine : Spine (one : Tower.Tm 0) := .app (.const _) (.const _)

theorem oneVec_spine : Spine (oneVec : Tower.Tm 0) :=
  .app (.app (.app (.const _) (.const _)) (.app (.const _) (.app (.const _) (.const _)))) (.const _)

theorem fz_spine : Spine (fzC zeroC : Tower.Tm 0) := .app (.const _) (.const _)

/-- The ground call `lookup 1 [2] (fz 0)`. -/
def loopCall : Tower.Tm 0 := .app (.app (.app (.const lookupN) one) oneVec) (fzC zeroC)

/-- `succ` applied `m` times. -/
def succPow (t : Tower.Tm 0) : Nat → Tower.Tm 0
  | 0 => t
  | m + 1 => .app (.const succN) (succPow t m)

/-- **The only step from `succ^m (lookup 1 [2] (fz 0))` unfolds the call once more.** -/
theorem loop_step_target (m : Nat) {t' : Tower.Tm 0}
    (step : StepCore lrules.computation lrules.headEq (succPow loopCall m) t') :
    t' = succPow loopCall (m + 1) := by
  induction m generalizing t' with
  | zero =>
      change StepCore lrules.computation lrules.headEq
        (.app (.app (.app (.const lookupN) one) oneVec) (fzC zeroC)) t' at step
      cases step with
      | root h =>
          rcases h with h | h
          · cases h
          · cases h
            rfl
      | congAppFun h =>
          cases h with
          | root h => rcases h with h | h <;> cases h
          | congAppFun h =>
              cases h with
              | root h => rcases h with h | h <;> cases h
              | congAppFun h =>
                  cases h with
                  | root h => rcases h with h | h <;> cases h
              | congAppArg h => exact (spine_normal one_spine (by decide) h).elim
          | congAppArg h => exact (spine_normal oneVec_spine (by decide) h).elim
      | congAppArg h => exact (spine_normal fz_spine (by decide) h).elim
  | succ m ih =>
      change StepCore lrules.computation lrules.headEq (.app (.const succN) (succPow loopCall m)) t'
        at step
      cases step with
      | root h => rcases h with h | h <;> cases h
      | congAppFun h =>
          cases h with
          | root h => rcases h with h | h <;> cases h
      | congAppArg h =>
          rw [ih h]
          rfl

/-- Every reduct of the call is `succ^m` of the call. -/
theorem loop_reducts {t : Tower.Tm 0} (steps : StepStar lrules loopCall t) :
    ∃ m, t = succPow loopCall m := by
  induction steps with
  | refl => exact ⟨0, rfl⟩
  | tail _ step ih =>
      obtain ⟨m, rfl⟩ := ih
      exact ⟨m + 1, loop_step_target m step⟩

/-- The call unfolds forever. -/
theorem loop_unfolds (m : Nat) :
    StepCore lrules.computation lrules.headEq (succPow loopCall m) (succPow loopCall (m + 1)) := by
  induction m with
  | zero => exact .root (declare_step (LoopStep.unfold one oneVec (fzC zeroC)))
  | succ m ih => exact .congAppArg ih

/-- **No answer**: the ground call reaches no normal form. Root determinism and Church–Rosser hold;
termination does not. -/
theorem loop_no_answer : ¬ ∃ v, StepStar lrules loopCall v ∧ ConstructorSystem.Normal lrules v := by
  rintro ⟨v, steps, normal⟩
  obtain ⟨m, rfl⟩ := loop_reducts steps
  exact normal (loop_unfolds m)

/-- `t ≐ succ t` for the call, in the rigid package. -/
def rigidLoopStore : EquationStore (TotalTerm (empty rules)) :=
  [(natTerm loopCall lookupRow_typed, natTerm (succC loopCall) (succ_typed lookupRow_typed))]

/-- **The rigid package refutes `t ≐ succ t`**: the two sides clash at their heads. -/
theorem rigid_loop_unsolvable : ¬ (frames levels).Solvable rigidLoopStore :=
  ContextualDependentRigid.not_solvable_of_storeClashes (S := setting) rigid facts complete
    (by decide)

/-- `nat` over a frame of the loop package. -/
def lnat (Γ : Context lrules) : TypeOver Γ :=
  ⟨natC, u0, .sort _, typed_declare loopComputation (nat_typed _)⟩

/-- `t ≐ succ t` for the call, in the loop package. -/
def loopStore : EquationStore (TotalTerm (empty lrules)) :=
  [(⟨lnat _, ⟨loopCall, typed_declare loopComputation lookupRow_typed⟩⟩,
    ⟨lnat _, ⟨succC loopCall, typed_declare loopComputation (succ_typed lookupRow_typed)⟩⟩)]

/-- **The loop package's knowledge solves `t ≐ succ t`**, by the identity. -/
theorem loop_solvable : (frames llevels).Solvable loopStore := by
  refine ⟨empty lrules, 𝟙 _, ?_⟩
  intro e member
  obtain rfl := List.mem_singleton.mp member
  show (frames llevels).E (TotalTerm.reindex _ (𝟙 _)) (TotalTerm.reindex _ (𝟙 _))
  rw [reindex_id, reindex_id]
  exact (equivalent_iff llevels _ _).mpr ⟨(lnat _).isType.refl,
    .root (declare_step (LoopStep.unfold one oneVec (fzC zeroC)))
      (typed_declare loopComputation lookupRow_typed)
      (typed_declare loopComputation (succ_typed lookupRow_typed))⟩

/-- **The separation**: refuted without the loop, solved with it. -/
theorem loop_separation :
    ¬ (frames levels).Solvable rigidLoopStore ∧ (frames llevels).Solvable loopStore :=
  ⟨rigid_loop_unsolvable, loop_solvable⟩

end Loop

/-! ## An ill-typed right side -/

section Junk

/-- A name that the vector package does not declare. -/
def junkN : DeclName := .mkSimple "junk"

/-- `add 0 b ↦ junk`. -/
inductive JunkStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | drop {n : Nat} (b : Tower.Tm n) :
      JunkStep (.app (.app (.const addN) (.const zeroN)) b) (.const junkN)

def junkComputation : RootComputation Tower.Head where
  step l r := JunkStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .drop b => JunkStep.drop (Presentation.rename ρ b)
  substitute := by
    intro n m σ left right h
    exact match h with
      | .drop b => JunkStep.drop (subst σ b)

abbrev jrules : Rules Tower.Head := declare rules junkComputation

theorem junk_rootDeterministic : RootDeterministic junkComputation := by
  intro n l r r' h h'
  cases h with
  | drop b => cases h' with
    | drop => rfl

/-- `junk` has no type. -/
theorem junk_untyped {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} :
    ¬ Typed jrules Γ (.const junkN) A := by
  intro typing
  obtain ⟨type, w, declared, _⟩ := Typed.generation typing
  have undeclared : jrules.constantType junkN = none := by decide
  cases undeclared.symm.trans declared

/-- **Root determinism does not give subject reduction.** -/
theorem junk_not_preserving : ¬ RootPreserving jrules := fun roots =>
  junk_untyped (roots .nil (declare_step (JunkStep.drop one))
    (typed_declare junkComputation (add_typed (zero_typed _) (one_typed _))))

/-- **Computation and conversion disagree**: the call `add 0 1` converts to `junk` untyped, and is
equal to it at no type, since the typed equality relates typed terms only. -/
theorem junk_disagreement :
    Conv jrules.headEq (addC zeroC one : Tower.Tm 0) (.const junkN) jrules.computation ∧
      ∀ A : Tower.Tm 0, ¬ Equal jrules .nil (addC zeroC one) (.const junkN) A := by
  refine ⟨.rel _ _ (.root (declare_step (JunkStep.drop one))), fun A equal => ?_⟩
  exact junk_untyped
    (Derivable.presupposed (declareLevels levels junkComputation) equal .nil).2.1

end Junk

/-! ## Partiality -/

section Partial

/-- Only `add 0 b ↦ b`: the successor row is missing. -/
inductive HalfStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | zero {n : Nat} (b : Tower.Tm n) : HalfStep (.app (.app (.const addN) (.const zeroN)) b) b

def halfComputation : RootComputation Tower.Head where
  step l r := HalfStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .zero b => HalfStep.zero (Presentation.rename ρ b)
  substitute := by
    intro n m σ left right h
    exact match h with
      | .zero b => HalfStep.zero (subst σ b)

abbrev prules : Rules Tower.Head := declare rules halfComputation

theorem half_rootDeterministic : RootDeterministic halfComputation := by
  intro n l r r' h h'
  cases h with
  | zero b => cases h' with
    | zero => rfl

/-- The one equation, over one variable. -/
inductive HalfSchema : {arity : Nat} → Tower.Tm arity → Tower.Tm arity → Prop
  | zero : HalfSchema (arity := 1) (.app (.app (.const addN) (.const zeroN)) (.var 0)) (.var 0)

def halfPresentation : SchemaPresentation prules where
  schema := HalfSchema
  sound := by
    intro arity ambient left right rule substitution
    cases rule with
    | zero => exact Or.inr (HalfStep.zero (substitution 0))
  cover := by
    intro n source target step
    rcases step with impossible | step
    · exact impossible.elim
    · exact match step with
        | .zero b => ⟨1, _, _, fun _ => b, .zero, rfl, rfl⟩

def halfSystem : System Tower.Head where
  schema := HalfSchema
  defined name := name = addN
  arity _ := 2
  left := by
    intro m left right rule
    refine ⟨addN, rfl, by decide, ?_⟩
    cases rule with
    | zero =>
        exact .app (.app (.const addN) (.const (show ¬ zeroN = addN by decide))) (.var 0)
  linear := by
    intro arity left right rule
    cases rule with
    | zero => unfold LeftLinear; decide
  covered := by
    intro m left right rule
    cases rule with
    | zero => decide
  determined := by
    intro m m' n n' left right left' right' rule rule' instantiation instantiation' same develop
    cases rule with
    | zero =>
        cases rule' with
        | zero =>
            have same' : Tm.app (.app (.const addN) (.const zeroN)) (instantiation 0) =
                Tm.app (.app (.const addN) (.const zeroN)) (instantiation' 0) := same
            obtain ⟨-, argument⟩ := Tm.app.inj same'
            show develop (instantiation 0) = develop (instantiation' 0)
            rw [argument]

def halfConstructors : ConstructorPresentation prules where
  presentation := halfPresentation
  system := halfSystem
  same _ _ := Iff.rfl
  symmetric := ⟨fun _ _ same => headEq_symm same⟩

/-- **The partial declaration is Church–Rosser.** -/
theorem half_churchRosser : ChurchRosser prules := halfConstructors.churchRosser

/-- The ground call `add 1 0`. -/
def stuckCall : Tower.Tm 0 := .app (.app (.const addN) one) (.const zeroN)

theorem stuck_typed : Typed prules .nil stuckCall natC :=
  typed_declare halfComputation (add_typed (one_typed _) (zero_typed _))

/-- **The ground call is stuck**: no step applies to `add 1 0`. -/
theorem stuck_normal : ConstructorSystem.Normal prules stuckCall := by
  intro t h
  cases h with
  | root h => rcases h with h | h <;> cases h
  | congAppFun h =>
      cases h with
      | root h => rcases h with h | h <;> cases h
      | congAppFun h =>
          cases h with
          | root h => rcases h with h | h <;> cases h
      | congAppArg h =>
          cases h with
          | root h => rcases h with h | h <;> cases h
          | congAppFun h =>
              cases h with
              | root h => rcases h with h | h <;> cases h
          | congAppArg h =>
              cases h with
              | root h => rcases h with h | h <;> cases h
  | congAppArg h =>
      cases h with
      | root h => rcases h with h | h <;> cases h

theorem one_normal_half : ConstructorSystem.Normal prules (one : Tower.Tm 0) := by
  intro t h
  cases h with
  | root h => rcases h with h | h <;> cases h
  | congAppFun h =>
      cases h with
      | root h => rcases h with h | h <;> cases h
  | congAppArg h =>
      cases h with
      | root h => rcases h with h | h <;> cases h

/-- The numerals `succ^k 0`. -/
inductive IsNumeral : Tower.Tm 0 → Prop
  | zero : IsNumeral (.const zeroN)
  | succ {t : Tower.Tm 0} : IsNumeral t → IsNumeral (.app (.const succN) t)

/-- **Canonicity fails**: the closed normal term `add 1 0` of `nat` is no numeral. -/
theorem stuck_not_numeral : ¬ IsNumeral stuckCall := by
  intro numeral
  cases numeral

/-- **The partial definition refutes `add 1 0 ≡ 1`.** -/
theorem stuck_not_one : ¬ Conv prules.headEq stuckCall one prules.computation := by
  intro conversion
  obtain ⟨common, left, right⟩ := half_churchRosser conversion
  have fromStuck := ConstructorSystem.Normal.stepStar stuck_normal left
  have fromOne := ConstructorSystem.Normal.stepStar one_normal_half right
  exact absurd (fromStuck.symm.trans fromOne) (by decide)

/-- **Completing the definition turns that refutation into an equation**: with the successor row,
`add 1 0 ⟶ succ (add 0 0) ⟶ 1`. -/
theorem completed_converts : Conv vrules.headEq stuckCall one vrules.computation :=
  .trans _ _ _ (.rel _ _ (.root (declare_step (AddStep.succ (.const zeroN) (.const zeroN)))))
    (.rel _ _ (.congAppArg (.root (declare_step (AddStep.zero (.const zeroN))))))

/-- Every step of the partial declaration is a step of the complete one. -/
theorem half_sub_complete {n : Nat} {l r : Tower.Tm n} (step : halfComputation.step l r) :
    VectorAppend.addComputation.step l r :=
  match step with
  | .zero b => AddStep.zero b

end Partial

/-! ## Effects -/

section Effects

/-- A call whose answer is read from the store: `lookup 1 [2] (fz 0)` stands for the call, `0` and `1`
for the values the store holds at two states. The union of the two readings. -/
inductive ReadStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | atZero {n : Nat} : ReadStep (n := n) (lookupC one oneVec (fzC zeroC)) (.const zeroN)
  | atOne {n : Nat} : ReadStep (n := n) (lookupC one oneVec (fzC zeroC)) one

/-- **A root computation that agrees with the store at both states exists.** -/
def readComputation : RootComputation Tower.Head where
  step l r := ReadStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .atZero => ReadStep.atZero
      | .atOne => ReadStep.atOne
  substitute := by
    intro n m σ left right h
    exact match h with
      | .atZero => ReadStep.atZero
      | .atOne => ReadStep.atOne

/-- **Effects are not root-deterministic**: every root computation that agrees with the store at
two states holding `0` and `1` gives the call two reducts. -/
theorem effect_not_rootDeterministic (d : RootComputation Tower.Head)
    (atZero : d.step (lookupC one oneVec (fzC zeroC) : Tower.Tm 0) (.const zeroN))
    (atOne : d.step (lookupC one oneVec (fzC zeroC) : Tower.Tm 0) one) : ¬ RootDeterministic d := by
  intro deterministic
  exact absurd (deterministic _ _ _ atZero atOne) (by decide)

/-- **... and identifies `0` and `1`** in the typed equality, which the rigid package refutes. -/
theorem effect_identifies (d : RootComputation Tower.Head)
    (atZero : d.step (lookupC one oneVec (fzC zeroC) : Tower.Tm 0) (.const zeroN))
    (atOne : d.step (lookupC one oneVec (fzC zeroC) : Tower.Tm 0) one) :
    Equal (declare rules d) .nil (.const zeroN) one natC ∧
      ¬ (frames levels).Solvable VectorAppend.rigidOneZero :=
  ⟨.trans (.symm (.root (declare_step atZero) (typed_declare d lookupRow_typed)
      (typed_declare d (zero_typed _))))
    (.root (declare_step atOne) (typed_declare d lookupRow_typed) (typed_declare d (one_typed _))),
    VectorAppend.rigid_one_zero_unsolvable⟩

/-- The union of the readings is such a computation. -/
theorem read_agrees :
    readComputation.step (lookupC one oneVec (fzC zeroC) : Tower.Tm 0) (.const zeroN) ∧
      readComputation.step (lookupC one oneVec (fzC zeroC) : Tower.Tm 0) one :=
  ⟨ReadStep.atZero, ReadStep.atOne⟩

end Effects

end NativeTypesOnTheStep.Computing.RootDeterminism

#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.rootDeterministic_of_presentation
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.nest_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.nest_two_answers
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.nest_not_churchRosser
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loop_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loopConstructors
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loop_churchRosser
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.spine_step_mentions
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loop_step_target
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loop_reducts
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loop_unfolds
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loop_no_answer
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.rigid_loop_unsolvable
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loop_solvable
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.loop_separation
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.junk_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.junk_untyped
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.junk_not_preserving
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.junk_disagreement
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.half_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.half_churchRosser
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.stuck_normal
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.stuck_not_numeral
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.stuck_not_one
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.completed_converts
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.half_sub_complete
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.effect_not_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.effect_identifies
#print axioms NativeTypesOnTheStep.Computing.RootDeterminism.read_agrees

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
