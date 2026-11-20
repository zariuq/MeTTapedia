import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Judgment
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.VectorAppend

/-!
# A typed program with real takes: append's empty clause, then the first element

One program, written once, over two packages of naturals and vectors: the rigid package, where no
constant computes, and the package where addition computes (`add zero b ↦ b`,
`add (succ a) b ↦ succ (add a b)`). The program has two rules over closed telescopes:

* **`appendNil`**, with unknowns `k : nat, ys : vec k`: it takes a call `append zero k nil ys`, of type
  `vec (add zero k)`, and makes the answer `ys`, of type `vec k`. The answer answers the take.
* **`firstOf`**, with unknowns `n : nat, x : nat, xs : vec n`: it takes a vector `cons n x xs`, of type
  `vec (succ n)`, and makes its first element `x : nat`, a new row of its own type.

**The run** (`run`): from the closed call `append 0 1 nil [2] : vec (add 0 1)`, `appendNil` fires along
its canonical opening (`firstFiring_admitted`) and makes the answer `ys`, whose type `vec k` mentions
the opened unknown `k`; `firstOf` then takes that row, matching `vec (succ n)` with `vec k` through the
knowledge (`secondFiring_admitted`), and makes `x`. At the closed solution of the final knowledge the
answer reads `2` (`answer_reads_two`). Both takes take rows whose types depend on terms. The run is a
run of the step of the program in every package of this kind, and through `dependent_eq` a run of the
dependent full step restricted to the program (`dependent_run`): a program with terms on which
`dependent_eq` has transitions.

**Typing decides by package.** With addition computing, `vec k` and `vec (add zero k)` are equal types,
so the program is well typed (`declared_wellTyped`), the run is typed (`declared_run_typed`), and the
answer of the first firing has the call's type at every solution of what the run learned
(`declared_answer_typed`, with `declared_answer_inherits`). In the rigid package the same rule is not
well typed (`rigid_appendNil_not_wellTyped`): at the closed instance the two types are `vec 1` and
`vec (add 0 1)`, which no conversion relates (`rigid_vec_not_typeEq`). The step still admits the firing
(`firstFiring_admitted` holds in every package), and its result is not well typed at the retyping
(`rigid_result_not_wellTyped`).

**The clause with its match told** (`toldNil`): with unknowns `m k : nat, xs : vec m, ys : vec k`, it
takes the general call `append m k xs ys : vec (add m k)`, tells `m ≐ zero`, and answers `ys : vec k`.
Its answer has the call's type only at the solutions of its tell, so here the judgment uses the rule's
own tells: well typed where addition computes (`declared_toldNil_wellTyped`, with the answer typed after
its firing on the call, `declared_told_answer_typed`), not in the rigid package
(`rigid_toldNil_not_wellTyped`). It fires on the call in every package (`toldFiring_admitted`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Programs

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface (Frames)
open Interface.DependentFull (Helpers)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open LogicOverTheStep.StepSpan (Succ)
open Dependent (Terms helperExtensions toState ofState dependentOn dependent_eq)
open ProgrammingOnTheStep.VectorPackage
open ProgrammingOnTheStep.VectorPrograms (one two oneVec one_typed two_typed oneVec_typed)

/-! ## Packages that extend the rigid typing -/

/-- **A package of naturals and vectors**: a signature whose typing contains the rigid package's,
with a universe model and the small universe. -/
structure Package where
  R : Rules Tower.Head
  levels : LevelModel R ℕ
  small : R.isUniverse u0
  lift : ∀ {n : ℕ} {Γ : Tower.Ctx n} {t A : Tower.Tm n}, Typed rules Γ t A → Typed R Γ t A

/-- **The rigid package**: no constant computes. -/
def rigid : Package := ⟨rules, levels, .sort _, id⟩

/-- **The package where addition computes.** -/
def declared : Package :=
  ⟨NativeTypesOnTheStep.VectorAppend.vrules, NativeTypesOnTheStep.VectorAppend.vlevels, .sort _,
    NativeTypesOnTheStep.VectorAppend.vtyped⟩

section Generic

variable (K : Package)

/-! ## Types and frames -/

/-- `nat`, over any frame. -/
def natType (Γ : Context K.R) : TypeOver Γ := ⟨natC, u0, K.small, K.lift (nat_typed _)⟩

/-- The frame `k : nat`. -/
abbrev ctxK : Context K.R := extend (empty K.R) (natType K _)

/-- `vec k`, over `k : nat`. -/
def vecK : TypeOver (ctxK K) :=
  ⟨vecC (.var 0), u0, K.small,
    K.lift (vec_typed (Derivable.var (R := rules) (Γ := (ctxK K).raw) 0))⟩

/-- The telescope `k : nat, ys : vec k`. -/
def nilTelescope : Helpers (empty K.R) := .cons (natType K _) (.cons (vecK K) (.nil _))

/-- Its frame. -/
abbrev ctxKY : Context K.R := extend (ctxK K) (vecK K)

/-- The frame `n : nat, x : nat`. -/
abbrev ctxNX : Context K.R := extend (ctxK K) (natType K _)

/-- `vec n`, over `n : nat, x : nat`. -/
def vecOfFirst : TypeOver (ctxNX K) :=
  ⟨vecC (.var 1), u0, K.small,
    K.lift (vec_typed (Derivable.var (R := rules) (Γ := (ctxNX K).raw) 1))⟩

/-- The telescope `n : nat, x : nat, xs : vec n`. -/
def consTelescope : Helpers (empty K.R) :=
  .cons (natType K _) (.cons (natType K _) (.cons (vecOfFirst K) (.nil _)))

/-- Its frame. -/
abbrev ctxNXXs : Context K.R := extend (ctxNX K) (vecOfFirst K)

/-! ## The two rules -/

theorem k_typed : Typed rules (ctxKY K).raw (.var 1) natC := Derivable.var (1 : Fin 2)

theorem ys_typed : Typed rules (ctxKY K).raw (.var 0) (vecC (.var 1)) := Derivable.var (0 : Fin 2)

theorem nilCall_typed :
    Typed rules (ctxKY K).raw (appendC zeroC (.var 1) nilC (.var 0)) (vecC (addC zeroC (.var 1))) := by
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (append_const_typed (ctxKY K).raw) (zero_typed (ctxKY K).raw)) (k_typed K))
    (nil_typed (ctxKY K).raw)) (ys_typed K)
  exact typed

/-- **The call pattern** `append zero k nil ys : vec (add zero k)`. -/
def nilCall : TotalTerm (ctxKY K) :=
  ⟨⟨vecC (addC zeroC (.var 1)), u0, K.small, K.lift (vec_typed (add_typed (zero_typed _) (k_typed K)))⟩,
    ⟨appendC zeroC (.var 1) nilC (.var 0), K.lift (nilCall_typed K)⟩⟩

/-- **The answer** `ys : vec k`. -/
def nilAnswer : TotalTerm (ctxKY K) :=
  ⟨⟨vecC (.var 1), u0, K.small, K.lift (vec_typed (k_typed K))⟩, ⟨.var 0, K.lift (ys_typed K)⟩⟩

/-- Take the call, make its answer. -/
def nilBody : RuleInstance (TotalTerm (ctxKY K)) := ⟨[nilCall K], [], [], [], [nilAnswer K]⟩

/-- **The clause `append zero k nil ys = ys`.** -/
def appendNil : Rule (Terms K.R) := telescopeRule (nilTelescope K) (nilBody K) []

theorem n_typed : Typed rules (ctxNXXs K).raw (.var 2) natC := Derivable.var (2 : Fin 3)

theorem x_typed : Typed rules (ctxNXXs K).raw (.var 1) natC := Derivable.var (1 : Fin 3)

theorem xs_typed : Typed rules (ctxNXXs K).raw (.var 0) (vecC (.var 2)) := Derivable.var (0 : Fin 3)

theorem consPattern_typed :
    Typed rules (ctxNXXs K).raw (consC (.var 2) (.var 1) (.var 0)) (vecC (succC (.var 2))) := by
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim
    (cons_const_typed (ctxNXXs K).raw) (n_typed K)) (x_typed K)) (xs_typed K)
  exact typed

/-- **The vector pattern** `cons n x xs : vec (succ n)`. -/
def consPattern : TotalTerm (ctxNXXs K) :=
  ⟨⟨vecC (succC (.var 2)), u0, K.small, K.lift (vec_typed (succ_typed (n_typed K)))⟩,
    ⟨consC (.var 2) (.var 1) (.var 0), K.lift (consPattern_typed K)⟩⟩

/-- **The first element** `x : nat`. -/
def firstElement : TotalTerm (ctxNXXs K) := ⟨natType K _, ⟨.var 1, K.lift (x_typed K)⟩⟩

/-- Take the vector, make its first element. -/
def consBody : RuleInstance (TotalTerm (ctxNXXs K)) := ⟨[consPattern K], [], [], [], [firstElement K]⟩

/-- **The rule `cons n x xs ↦ x`.** -/
def firstOf : Rule (Terms K.R) := telescopeRule (consTelescope K) (consBody K) []

/-- **The program.** -/
def program : Program (Terms K.R) := {appendNil K, firstOf K}

theorem appendNil_mem : appendNil K ∈ program K := Set.mem_insert _ _

theorem firstOf_mem : firstOf K ∈ program K := Set.mem_insert_of_mem _ (Set.mem_singleton _)

theorem appendNil_ne_firstOf : appendNil K ≠ firstOf K := by
  intro same
  have arities := congrArg (fun r : Rule (Terms K.R) => r.locals.arity) same
  have two : (appendNil K).locals.arity = 2 := rfl
  have three : (firstOf K).locals.arity = 3 := rfl
  omega

open Classical in
/-- **Its answers**: the made row of `appendNil` answers its take; `firstOf` makes a new row. -/
noncomputable def answers : Rule (Terms K.R) → List (Option ℕ) :=
  fun r => if r = appendNil K then [some 0] else []

theorem answers_appendNil : answers K (appendNil K) = [some 0] := by
  simp [answers]

theorem answers_firstOf : answers K (firstOf K) = [] := by
  simp [answers, (appendNil_ne_firstOf K).symm]

/-- A rule without answers is well typed. -/
theorem wellTypedRule_nil {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel K.R L)
    (r : Rule (Terms K.R)) : WellTypedRule levels r [] := by
  intro j i made call hj
  simp at hj

/-! ## The run -/

theorem call_typed :
    Typed rules Ctx.nil (appendC zeroC one nilC oneVec) (vecC (addC zeroC one)) := by
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (append_const_typed Ctx.nil) (zero_typed Ctx.nil)) (one_typed Ctx.nil)) (nil_typed Ctx.nil))
    (oneVec_typed Ctx.nil)
  exact typed

/-- **The closed call** `append 0 1 nil [2] : vec (add 0 1)`. -/
def callRow : TotalTerm (empty K.R) :=
  ⟨⟨vecC (addC zeroC one), u0, K.small, K.lift (vec_typed (add_typed (zero_typed _) (one_typed _)))⟩,
    ⟨appendC zeroC one nilC oneVec, K.lift call_typed⟩⟩

/-- One present row, the call, and no knowledge. -/
def start : State (Terms K.R) ℕ := ⟨empty K.R, [], {0}, fun _ => callRow K⟩

/-- **`appendNil` fires on the call**, opened along its canonical opening, making row `1`. -/
def firstFiring : Firing ℕ (helperExtensions (rules := K.R)) (program K) (start K).frame :=
  canonicalFiring (nilTelescope K) (nilBody K) [] (appendNil_mem K) (start K).frame ⟨[0], [], [1]⟩ []

/-- The closed solution `k ↦ 1, ys ↦ [2]`. -/
def firstSolution : empty K.R ⟶ (firstFiring K).ext.frame :=
  pair (pair (toEmpty (empty K.R)) ⟨one, K.lift (one_typed _)⟩) ⟨oneVec, K.lift (oneVec_typed _)⟩

theorem firstFiring_information :
    (firstFiring K).information (frames K.levels) (start K) =
      [((nilCall K).reindex (Helpers.lift (toEmpty (empty K.R)) (nilTelescope K)),
        (callRow K).reindex (firstFiring K).ext.weaken)] := rfl

theorem firstSolution_solves :
    (frames K.levels).Models (firstSolution K)
      ((firstFiring K).information (frames K.levels) (start K)) := by
  rw [firstFiring_information]
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact equivalent_of_eq K.levels (totalTerm_ext (TypeOver.ext rfl rfl) rfl)

/-- **The first firing is admitted**, in every package. -/
theorem firstFiring_admitted :
    (step (frames K.levels) ℕ helperExtensions (program K)).Admits (s := start K) (firstFiring K) := by
  refine (RuleSyntax.admits_iff _).mpr ⟨canonical_fresh K.levels _ _ _ _ _ _ _,
    ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨empty K.R, firstSolution K, firstSolution_solves K⟩,
    fun c member => absurd member List.not_mem_nil, fun q member => absurd member List.not_mem_nil⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [firstFiring, canonicalFiring, start, Selection.commit]

/-- The state after the first firing. -/
def firstResult : State (Terms K.R) ℕ := (firstFiring K).result (frames K.levels) (start K)

theorem firstResult_present : (firstResult K).present = {1} := by
  simp [firstResult, Firing.result, firstFiring, canonicalFiring, start, fire, Selection.commit]

theorem firstResult_label :
    (firstResult K).label 1 =
      (nilAnswer K).reindex (Helpers.lift (toEmpty (empty K.R)) (nilTelescope K)) := rfl

/-- **`firstOf` takes the answer**, opened along its canonical opening, making row `2`. -/
def secondFiring : Firing ℕ (helperExtensions (rules := K.R)) (program K) (firstResult K).frame :=
  canonicalFiring (consTelescope K) (consBody K) [] (firstOf_mem K) (firstResult K).frame
    ⟨[1], [], [2]⟩ []

/-- The closed solution `k ↦ 1, ys ↦ [2], n ↦ 0, x ↦ 2, xs ↦ nil`. -/
def secondSolution : empty K.R ⟶ (secondFiring K).ext.frame :=
  pair (pair (pair (firstSolution K) ⟨zeroC, K.lift (zero_typed _)⟩) ⟨two, K.lift (two_typed _)⟩)
    ⟨nilC, K.lift (nil_typed _)⟩

theorem secondFiring_information :
    (secondFiring K).information (frames K.levels) (firstResult K) =
      [(((nilCall K).reindex (Helpers.lift (toEmpty (empty K.R)) (nilTelescope K))).reindex
          (secondFiring K).ext.weaken,
        ((callRow K).reindex (firstFiring K).ext.weaken).reindex (secondFiring K).ext.weaken),
       ((consPattern K).reindex (Helpers.lift (toEmpty (firstResult K).frame) (consTelescope K)),
        ((firstResult K).label 1).reindex (secondFiring K).ext.weaken)] := rfl

theorem secondSolution_solves :
    (frames K.levels).Models (secondSolution K)
      ((secondFiring K).information (frames K.levels) (firstResult K)) := by
  rw [secondFiring_information]
  intro e member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact equivalent_of_eq K.levels (totalTerm_ext (TypeOver.ext rfl rfl) rfl)
  · exact equivalent_of_eq K.levels (totalTerm_ext (TypeOver.ext rfl rfl) rfl)

/-- **The second firing is admitted**, in every package. -/
theorem secondFiring_admitted :
    (step (frames K.levels) ℕ helperExtensions (program K)).Admits (s := firstResult K)
      (secondFiring K) := by
  refine (RuleSyntax.admits_iff _).mpr ⟨canonical_fresh K.levels _ _ _ _ _ _ _,
    ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨empty K.R, secondSolution K, secondSolution_solves K⟩,
    fun c member => absurd member List.not_mem_nil, fun q member => absurd member List.not_mem_nil⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [secondFiring, canonicalFiring, firstResult_present, Selection.commit]

/-- The state after the second firing. -/
def secondResult : State (Terms K.R) ℕ := (secondFiring K).result (frames K.levels) (firstResult K)

/-- **The run of length two**, through two takes and two makes. -/
theorem run :
    Relation.ReflTransGen (Succ (step (frames K.levels) ℕ helperExtensions (program K)).toStep)
      (start K) (secondResult K) :=
  .head ⟨firstFiring K, firstFiring_admitted K, rfl⟩
    (.head ⟨secondFiring K, secondFiring_admitted K, rfl⟩ .refl)

/-- **The answer**: the final knowledge is solved by the closed solution, and there the made row
reads `2`. -/
theorem answer_reads_two :
    (frames K.levels).Models (secondSolution K) (secondResult K).knowledge ∧
      subst (secondSolution K).substitution ((secondResult K).label 2).2.code = two :=
  ⟨secondSolution_solves K, rfl⟩

/-! ## The empty clause with its match told -/

/-- `vec k`, over `m : nat, k : nat, xs : vec m`. -/
def vecOfSecond : TypeOver (ctxNXXs K) :=
  ⟨vecC (.var 1), u0, K.small,
    K.lift (vec_typed (Derivable.var (R := rules) (Γ := (ctxNXXs K).raw) 1))⟩

/-- The telescope `m : nat, k : nat, xs : vec m, ys : vec k`. -/
def toldTelescope : Helpers (empty K.R) :=
  .cons (natType K _) (.cons (natType K _) (.cons (vecOfFirst K) (.cons (vecOfSecond K) (.nil _))))

/-- Its frame. -/
abbrev ctxMKXY : Context K.R := extend (ctxNXXs K) (vecOfSecond K)

theorem toldCall_typed :
    Typed rules (ctxMKXY K).raw (appendC (.var 3) (.var 2) (.var 1) (.var 0))
      (vecC (addC (.var 3) (.var 2))) := by
  have m : Typed rules (ctxMKXY K).raw (.var 3) natC := Derivable.var (3 : Fin 4)
  have k : Typed rules (ctxMKXY K).raw (.var 2) natC := Derivable.var (2 : Fin 4)
  have xs : Typed rules (ctxMKXY K).raw (.var 1) (vecC (.var 3)) := Derivable.var (1 : Fin 4)
  have ys : Typed rules (ctxMKXY K).raw (.var 0) (vecC (.var 2)) := Derivable.var (0 : Fin 4)
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (append_const_typed (ctxMKXY K).raw) m) k) xs) ys
  exact typed

/-- **The general call pattern** `append m k xs ys : vec (add m k)`. -/
def toldCall : TotalTerm (ctxMKXY K) :=
  ⟨⟨vecC (addC (.var 3) (.var 2)), u0, K.small,
      K.lift (vec_typed (add_typed (Derivable.var (3 : Fin 4)) (Derivable.var (2 : Fin 4))))⟩,
    ⟨appendC (.var 3) (.var 2) (.var 1) (.var 0), K.lift (toldCall_typed K)⟩⟩

/-- **What matching `nil` teaches, told**: `m ≐ zero`. -/
def toldMatch : Equation (TotalTerm (ctxMKXY K)) :=
  (⟨natType K _, ⟨.var 3, K.lift (Derivable.var (3 : Fin 4))⟩⟩,
    ⟨natType K _, ⟨zeroC, K.lift (zero_typed _)⟩⟩)

/-- **The answer** `ys : vec k`. -/
def toldAnswer : TotalTerm (ctxMKXY K) :=
  ⟨⟨vecC (.var 2), u0, K.small, K.lift (vec_typed (Derivable.var (2 : Fin 4)))⟩,
    ⟨.var 0, K.lift (Derivable.var (0 : Fin 4))⟩⟩

/-- Take the general call, tell `m ≐ zero`, make `ys`. -/
def toldBody : RuleInstance (TotalTerm (ctxMKXY K)) :=
  ⟨[toldCall K], [], [toldMatch K], [], [toldAnswer K]⟩

/-- **The clause `append m k xs ys = ys`, told `m ≐ zero`**: its answer has the call's type only at the
solutions of its tell. -/
def toldNil : Rule (Terms K.R) := telescopeRule (toldTelescope K) (toldBody K) []

def toldProgram : Program (Terms K.R) := {toldNil K}

/-- It fires on the closed call. -/
def toldFiring : Firing ℕ (helperExtensions (rules := K.R)) (toldProgram K) (start K).frame :=
  canonicalFiring (toldTelescope K) (toldBody K) [] (Set.mem_singleton _) (start K).frame
    ⟨[0], [], [1]⟩ []

/-- The closed solution `m ↦ 0, k ↦ 1, xs ↦ nil, ys ↦ [2]`. -/
def toldSolution : empty K.R ⟶ (toldFiring K).ext.frame :=
  pair (pair (pair (pair (toEmpty (empty K.R)) ⟨zeroC, K.lift (zero_typed _)⟩) ⟨one, K.lift (one_typed _)⟩)
    ⟨nilC, K.lift (nil_typed _)⟩) ⟨oneVec, K.lift (oneVec_typed _)⟩

theorem toldFiring_information :
    (toldFiring K).information (frames K.levels) (start K) =
      [((toldCall K).reindex (Helpers.lift (toEmpty (empty K.R)) (toldTelescope K)),
          (callRow K).reindex (toldFiring K).ext.weaken),
        ((toldMatch K).1.reindex (Helpers.lift (toEmpty (empty K.R)) (toldTelescope K)),
          (toldMatch K).2.reindex (Helpers.lift (toEmpty (empty K.R)) (toldTelescope K)))] := rfl

/-- **The told clause fires on the call**, in every package. -/
theorem toldFiring_admitted :
    (step (frames K.levels) ℕ helperExtensions (toldProgram K)).Admits (s := start K) (toldFiring K) := by
  refine (RuleSyntax.admits_iff _).mpr ⟨canonical_fresh K.levels _ _ _ _ _ _ _,
    ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨empty K.R, toldSolution K, ?_⟩, fun c member => absurd member List.not_mem_nil,
    fun q member => absurd member List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [toldFiring, canonicalFiring, start, Selection.commit]
  · rw [toldFiring_information]
    intro e member
    rcases List.mem_cons.mp member with rfl | rest
    · exact equivalent_of_eq K.levels (totalTerm_ext (TypeOver.ext rfl rfl) rfl)
    · obtain rfl := List.mem_singleton.mp rest
      exact equivalent_of_eq K.levels (totalTerm_ext (TypeOver.ext rfl rfl) rfl)

/-- **The same run on the dependent full step restricted to the program**, through `dependent_eq`:
a program with terms on which the restricted dependent full step has transitions. -/
theorem dependent_run :
    Relation.ReflTransGen (Succ (dependentOn K.levels (program K))) (ofState (start K))
      (ofState (secondResult K)) :=
  .head ((dependent_eq (ofState (start K)) (ofState (firstResult K))).mpr
      ⟨firstFiring K, firstFiring_admitted K, rfl⟩)
    (.head ((dependent_eq (ofState (firstResult K)) (ofState (secondResult K))).mpr
      ⟨secondFiring K, secondFiring_admitted K, rfl⟩) .refl)

end Generic

/-! ## With addition computing, the program is well typed -/

section Declared

open NativeTypesOnTheStep (declare_step)
open NativeTypesOnTheStep.VectorAppend (AddStep)

/-- `vec k` and `vec (add zero k)` are equal types once addition computes. -/
theorem declared_types_equal :
    TypeEq declared.R (ctxKY declared).raw (vecC (.var 1)) (vecC (addC zeroC (.var 1))) := by
  have k : Typed declared.R (ctxKY declared).raw (.var 1) natC := declared.lift (k_typed declared)
  have addZeroK : Typed declared.R (ctxKY declared).raw (addC zeroC (.var 1)) natC :=
    declared.lift (add_typed (zero_typed _) (k_typed declared))
  have vecConst : Typed declared.R (ctxKY declared).raw (.const vecN) (.pi natC U0) :=
    declared.lift (.const declared_vec vecTy_typed (.sort _))
  have computes : Equal declared.R (ctxKY declared).raw (addC zeroC (.var 1)) (.var 1) natC :=
    .root (declare_step (AddStep.zero _)) addZeroK k
  exact ⟨u0, .sort _, .appCong (.refl vecConst) (.symm computes)⟩

/-- **`appendNil` is well typed once addition computes.** -/
theorem declared_appendNil_wellTyped :
    WellTypedRule declared.levels (appendNil declared) [some 0] := by
  refine (wellTypedRule_iff_of_tell_nil declared.levels _ _ rfl).mpr ?_
  intro j i made call hj hm hc
  cases j with
  | succ j => simp at hj
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hm' : some (nilAnswer declared) = some made := hm
      have hc' : some (nilCall declared) = some call := hc
      obtain rfl := Option.some.inj hm'
      obtain rfl := Option.some.inj hc'
      exact declared_types_equal

/-- **The program is well typed once addition computes.** -/
theorem declared_wellTyped :
    WellTypedProgram declared.levels (program declared) (answers declared) := by
  intro r member
  rcases member with rfl | member
  · rw [answers_appendNil]
    exact declared_appendNil_wellTyped
  · rw [Set.mem_singleton_iff] at member
    subst member
    rw [answers_firstOf]
    exact wellTypedRule_nil declared declared.levels _

/-- **The run is typed**: from the call at its own type, every state of the run is well typed at the
typing carried along it. -/
theorem declared_run_typed :
    ∃ Δ : ℕ → TypeOver (secondResult declared).frame,
      TypedReach declared.levels (program declared) (answers declared) (start declared)
        (fun o => ((start declared).label o).1) (secondResult declared) Δ ∧
      WellTypedState declared.levels (secondResult declared) Δ :=
  reach_wellTyped declared.levels declared_wellTyped (wellTypedState_own declared.levels _)
    (run declared)

/-- **The same for the dependent full step restricted to the program**: its run from the call is typed,
through `dependent_eq`. -/
theorem declared_dependent_run_typed :
    ∃ Δ : ℕ → TypeOver (secondResult declared).frame,
      TypedReach declared.levels (program declared) (answers declared) (toState (ofState (start declared)))
        (fun o => ((start declared).label o).1) (toState (ofState (secondResult declared))) Δ ∧
      WellTypedState declared.levels (toState (ofState (secondResult declared))) Δ :=
  dependent_reach_wellTyped declared.levels declared_wellTyped (wellTypedState_own declared.levels _)
    (dependent_run declared)

/-- **The answer inherits the call's type**: after the first firing, the answer row expects
`vec (add 0 1)`, the call's type read at the extended frame. -/
theorem declared_answer_inherits :
    retype declared.levels (firstFiring declared) [some 0] (fun o => ((start declared).label o).1) 1 =
      (callRow declared).1.reindex (firstFiring declared).ext.weaken :=
  retype_answer declared.levels (firstFiring declared) [some 0] _ (j := 0) (o := 1) (oi := 0)
    (t := (nilAnswer declared).reindex (Helpers.lift (toEmpty (empty declared.R)) (nilTelescope declared)))
    (List.nodup_singleton 1) rfl rfl rfl

/-- **... and has it at every solution of what the firing learned**, though its own type is
`vec k`. -/
theorem declared_answer_typed :
    WellTypedState declared.levels (firstResult declared)
      (retype declared.levels (firstFiring declared) [some 0] (fun o => ((start declared).label o).1)) :=
  result_wellTyped declared.levels declared_appendNil_wellTyped (firstFiring_admitted declared)
    (wellTypedState_own declared.levels _)

/-- **The told clause is well typed once addition computes**: at every solution of its tell `m ≐ zero`,
`vec k` and `vec (add m k)` are equal types. Here the judgment uses the rule's tell, since `m` is an
unknown of the rule. -/
theorem declared_toldNil_wellTyped : WellTypedRule declared.levels (toldNil declared) [some 0] := by
  intro j i made call hj hm hc Θ σ solved
  cases j with
  | succ j => simp at hj
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hm' : some (toldAnswer declared) = some made := hm
      have hc' : some (toldCall declared) = some call := hc
      obtain rfl := Option.some.inj hm'
      obtain rfl := Option.some.inj hc'
      let τ : Θ ⟶ ctxMKXY declared := σ
      have mZero : Equal declared.R Θ.raw (τ.substitution 3) zeroC natC :=
        (solved _ (List.mem_singleton_self _)).2
      have kTyped : Typed declared.R Θ.raw (τ.substitution 2) natC := τ.typed 2
      have addConst : Typed declared.R Θ.raw (.const addN) (.pi natC (.pi natC natC)) :=
        declared.lift (.const declared_add addTy_typed (.sort _))
      have vecConst : Typed declared.R Θ.raw (.const vecN) (.pi natC U0) :=
        declared.lift (.const declared_vec vecTy_typed (.sort _))
      have addZeroK : Typed declared.R Θ.raw (addC zeroC (τ.substitution 2)) natC :=
        .appElim (.appElim addConst (declared.lift (zero_typed _))) kTyped
      have toZero : Equal declared.R Θ.raw (addC (τ.substitution 3) (τ.substitution 2))
          (addC zeroC (τ.substitution 2)) natC :=
        .appCong (.appCong (.refl addConst) mZero) (.refl kTyped)
      have computes : Equal declared.R Θ.raw (addC zeroC (τ.substitution 2)) (τ.substitution 2) natC :=
        .root (declare_step (AddStep.zero _)) addZeroK kTyped
      have result : TypeEq declared.R Θ.raw (vecC (τ.substitution 2))
          (vecC (addC (τ.substitution 3) (τ.substitution 2))) :=
        ⟨u0, .sort _, .symm (.appCong (.refl vecConst) (.trans toZero computes))⟩
      exact result

/-- **The told clause's answer has the call's type** at every solution of what its firing learned. -/
theorem declared_told_answer_typed :
    WellTypedState declared.levels ((toldFiring declared).result (frames declared.levels) (start declared))
      (retype declared.levels (toldFiring declared) [some 0] (fun o => ((start declared).label o).1)) :=
  result_wellTyped declared.levels declared_toldNil_wellTyped (toldFiring_admitted declared)
    (wellTypedState_own declared.levels _)

end Declared

/-! ## In the rigid package the same rule is not well typed -/

section Rigid

/-- **`vec 1` and `vec (add 0 1)` are different types in the rigid package**, at every frame. -/
theorem rigid_vec_not_typeEq {Θ : Context rules} :
    ¬ TypeEq rules Θ.raw (vecC one) (vecC (addC zeroC one)) := by
  intro types
  have lengths : Equal rules Θ.raw one (addC zeroC one) natC :=
    LogicOverTheStep.RigidReadback.vec_injective types
  apply ProgrammingOnTheStep.VectorPrograms.add_not_in_knowledge
  refine ⟨Θ, toEmpty Θ, fun e member => ?_⟩
  obtain rfl := List.mem_singleton.mp member
  exact ⟨⟨u0, .sort _, .refl (nat_typed _)⟩, .symm lengths⟩

/-- The closed instance `k ↦ 1, ys ↦ [2]` of `appendNil`'s unknowns. -/
def rigidInstance : empty rules ⟶ ctxKY rigid :=
  pair (pair (toEmpty (empty rules)) ⟨one, one_typed _⟩) ⟨oneVec, oneVec_typed _⟩

/-- **`appendNil` is not well typed in the rigid package**: at the closed instance its answer has
type `vec 1` and its call `vec (add 0 1)`. -/
theorem rigid_appendNil_not_wellTyped : ¬ WellTypedRule rigid.levels (appendNil rigid) [some 0] := by
  intro typed
  have atInstance := typed 0 0 (nilAnswer rigid) (nilCall rigid) rfl rfl rfl (empty rules)
    rigidInstance (Frames.models_nil _)
  exact rigid_vec_not_typeEq atInstance

/-- **Nor is the program.** -/
theorem rigid_not_wellTyped : ¬ WellTypedProgram rigid.levels (program rigid) (answers rigid) := by
  intro typed
  have atRule := typed _ (appendNil_mem rigid)
  rw [answers_appendNil] at atRule
  exact rigid_appendNil_not_wellTyped atRule

/-- **The step admits the firing anyway, and its result is not well typed at the retyping**: at the
closed solution of its knowledge the answer has type `vec 1` where the call's type `vec (add 0 1)` is
expected. -/
theorem rigid_result_not_wellTyped :
    (step (frames rigid.levels) ℕ helperExtensions (program rigid)).Admits (s := start rigid)
        (firstFiring rigid) ∧
      ¬ WellTypedState rigid.levels (firstResult rigid)
        (retype rigid.levels (firstFiring rigid) [some 0] (fun o => ((start rigid).label o).1)) := by
  refine ⟨firstFiring_admitted rigid, fun typed => ?_⟩
  have atSolution := typed 1 (by rw [firstResult_present]; exact Finset.mem_singleton_self 1)
    (empty rules) (firstSolution rigid) (firstSolution_solves rigid)
  exact rigid_vec_not_typeEq atSolution

/-- The closed instance `m ↦ 0, k ↦ 1, xs ↦ nil, ys ↦ [2]` of the told clause's unknowns, a solution
of its tell. -/
def toldInstance : empty rules ⟶ ctxMKXY rigid :=
  pair (pair (pair (pair (toEmpty (empty rules)) ⟨zeroC, zero_typed _⟩) ⟨one, one_typed _⟩)
    ⟨nilC, nil_typed _⟩) ⟨oneVec, oneVec_typed _⟩

/-- **Without computing addition, the tell does not save the told clause**: its tell holds at the
closed instance, where the answer has type `vec 1` and the call `vec (add 0 1)`. -/
theorem rigid_toldNil_not_wellTyped : ¬ WellTypedRule rigid.levels (toldNil rigid) [some 0] := by
  intro typed
  have tell : (frames rigid.levels).Models toldInstance (toldNil rigid).body.tell := by
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact equivalent_of_eq rigid.levels (totalTerm_ext (TypeOver.ext rfl rfl) rfl)
  exact rigid_vec_not_typeEq
    (typed 0 0 (toldAnswer rigid) (toldCall rigid) rfl rfl rfl (empty rules) toldInstance tell)

end Rigid

#print axioms firstFiring_admitted
#print axioms secondFiring_admitted
#print axioms run
#print axioms answer_reads_two
#print axioms dependent_run
#print axioms declared_types_equal
#print axioms declared_appendNil_wellTyped
#print axioms declared_wellTyped
#print axioms declared_run_typed
#print axioms declared_dependent_run_typed
#print axioms declared_answer_inherits
#print axioms declared_answer_typed
#print axioms rigid_vec_not_typeEq
#print axioms rigid_appendNil_not_wellTyped
#print axioms rigid_not_wellTyped
#print axioms rigid_result_not_wellTyped
#print axioms toldFiring_admitted
#print axioms declared_toldNil_wellTyped
#print axioms declared_told_answer_typed
#print axioms rigid_toldNil_not_wellTyped

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Programs
