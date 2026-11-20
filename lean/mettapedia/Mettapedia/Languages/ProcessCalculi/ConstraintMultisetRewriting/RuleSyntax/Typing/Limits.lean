import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing.Check
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Locality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions

/-!
# What the judgment decides, what typing of the knowledge would be, and what typing does not give

## Deciding the judgment

With an initial solution of the rule's own tells, the judgment is one type equality per answer at
that solution (`wellTypedRule_iff_of_initial`); with no tells it is type equality in the rule's frame
(`wellTypedRule_iff_of_tell_nil`). So the judgment reduces to two judgments of the type theory: type
equality, decided where its conversion is decided, and unification of the rule's own tells, which is
needed only when the rule tells something.

## The knowledge is not made of equations between terms of one type

A program whose rules tell nothing and check nothing, from a state with no knowledge, reaches knowledge
with an equation between terms of different types (`heterogeneous_take`): the take equation of `firstOf`
relates `cons n x xs : vec (succ n)` to the answer `ys : vec k`, and `vec (succ n)` and `vec k` are not
equal types in the frame, since at the instance `n ↦ 0, k ↦ 0` they are `vec 1` and `vec 0`. Matching
solves equations between types; the knowledge is an equation store of typed terms of possibly different
types, and needs no typing of its own.

## What typing does not give

* **Termination** (`spin_runs_forever`): a well-typed program, one rule that takes `0 : nat` and answers
  it by `0 : nat`, has an infinite run.
* **Uniqueness of answers** (`answers_not_unique`): two well-typed rules answer the same call
  `add 0 1 : nat` with `1` and with `0`; both firings are admitted, and no substitution equates the two
  answers.
* **The none query beside another program** (`none_not_compositional`): a well-typed rule takes `0 : nat`,
  asks for the none query of `1 : nat` and answers `2 : nat`, and its firing is admitted; beside another
  well-typed rule that takes `0 : nat` and answers `1 : nat`, the union is well typed
  (`WellTypedProgram.union`) with each made row designated as the answer to the taken row, a
  designation that rejects an ill-typed rule of this package (`Programs.rigid_appendNil_not_wellTyped`);
  but after the other rule fires the same firing is refused, because the made row lies inside the
  none region. Locality
  (`RuleSyntax.admits_of_outsideRegions`) says when such a change does not matter: when it lies outside
  the firing's regions. A row `add 0 1` added beside the guarded rule is outside its region, and the
  firing stays admitted by locality (`locality_outside`); a row `1` added in the same way is inside, and
  refuses it (`locality_inside`). Typing is a property of each rule, so it composes; admission with a
  none check reads the store, and locality is what makes it compose: it is kept when the other
  program's changes lie outside the firing's regions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface (Frames)
open Interface.DependentFull (Helpers)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open Dependent (Terms helperExtensions)

/-! ## Deciding the judgment -/

section Decision

variable {Head : Type} {rules : Rules Head} {L : Type} [UniverseLevel.LevelOrder L]

theorem typeEq_through (levels : LevelModel rules L) {Γ M Θ : Context rules} (θ : M ⟶ Γ)
    (g : Θ ⟶ M) (σ : Θ ⟶ Γ) {A C : TypeOver Γ}
    (atInitial : TypeEq rules M.raw (A.reindex θ).code (C.reindex θ).code)
    (left : TypeEq rules Θ.raw (A.reindex σ).code (A.reindex (g ≫ θ)).code)
    (right : TypeEq rules Θ.raw (C.reindex σ).code (C.reindex (g ≫ θ)).code) :
    TypeEq rules Θ.raw (A.reindex σ).code (C.reindex σ).code := by
  have moved := reindex_typeEquality atInitial g
  have along : TypeEq rules Θ.raw (A.reindex (g ≫ θ)).code (C.reindex (g ≫ θ)).code := by
    rw [TypeOver.reindex_comp, TypeOver.reindex_comp]
    exact moved
  exact (left.trans levels along).trans levels right.symm

/-- **With an initial solution of the rule's tells, the judgment is one type equality per answer
there.** -/
theorem wellTypedRule_iff_of_initial (levels : LevelModel rules L) {r : Rule (Terms rules)}
    {answers : List (Option ℕ)}
    {M : Context rules} {θ : M ⟶ r.locals}
    (initial : UnificationWithLevels.InitialSolution (frames levels) r.body.tell θ) :
    WellTypedRule levels r answers ↔
      ∀ (j i : ℕ) (made call : TotalTerm r.locals), answers[j]? = some (some i) →
        r.body.produce[j]? = some made → r.body.take[i]? = some call → HasType θ made call.1 := by
  constructor
  · intro typed j i made call hj hm hc
    exact typed j i made call hj hm hc M θ initial.solves
  · intro atInitial j i made call hj hm hc Θ σ solved
    obtain ⟨g, agree⟩ := initial.factor Θ σ solved
    exact typeEq_through levels θ g σ (atInitial j i made call hj hm hc) (agree made).1 (agree call).1

end Decision

/-! ## The knowledge is not made of equations between terms of one type -/

section Hypothesis

open Programs
open ProgrammingOnTheStep.VectorPackage (natC zeroC nilC vecC succC zero_typed nil_typed nat_typed u0
  setting facts complete)
open ProgrammingOnTheStep.VectorPrograms (one one_typed natTerm)

/-- **`1 ≐ 0` is refuted in the rigid package**, at every frame. -/
theorem rigid_one_ne_zero {Θ : Context rigid.R} : ¬ Equal rigid.R Θ.raw one zeroC natC := by
  intro equal
  have refuted : ¬ (frames rigid.levels).Solvable
      [(natTerm one (one_typed _), natTerm zeroC (zero_typed _))] :=
    ContextualDependentRigid.not_solvable_of_storeClashes (S := setting)
      ProgrammingOnTheStep.VectorPackage.rigid facts complete (by decide)
  apply refuted
  refine ⟨Θ, toEmpty Θ, fun e member => ?_⟩
  obtain rfl := List.mem_singleton.mp member
  exact ⟨⟨u0, .sort _, .refl (nat_typed _)⟩, equal⟩

/-- The closed instance `k ↦ 0, ys ↦ nil, n ↦ 0, x ↦ 0, xs ↦ nil` of the frame of the run's end. -/
def zeroInstance : empty rigid.R ⟶ (secondFiring rigid).ext.frame :=
  pair (pair (pair (pair (pair (toEmpty (empty rigid.R)) ⟨zeroC, zero_typed _⟩) ⟨nilC, nil_typed _⟩)
    ⟨zeroC, zero_typed _⟩) ⟨zeroC, zero_typed _⟩) ⟨nilC, nil_typed _⟩

/-- The take equation of the second firing: `cons n x xs ≐ ys`. -/
abbrev secondTake : Equation (TotalTerm (secondFiring rigid).ext.frame) :=
  ((consPattern rigid).reindex (Helpers.lift (toEmpty (firstResult rigid).frame) (consTelescope rigid)),
    ((firstResult rigid).label 1).reindex (secondFiring rigid).ext.weaken)

/-- **The rules tell nothing and check nothing**, so they satisfy every clause on tells and guards. -/
theorem program_tells_nothing :
    ∀ r ∈ program rigid, r.body.tell = [] ∧ r.body.checks = [] := by
  intro r member
  rcases member with rfl | member
  · exact ⟨rfl, rfl⟩
  · rw [Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩

/-- **A heterogeneous take equation in the reached knowledge**: from a state with no knowledge, the
program reaches knowledge with an equation whose two sides have types that are not equal in its frame. -/
theorem heterogeneous_take :
    Relation.ReflTransGen (Succ (step (frames rigid.levels) ℕ helperExtensions (program rigid)).toStep)
        (start rigid) (secondResult rigid) ∧
      secondTake ∈ (secondResult rigid).knowledge ∧
      ¬ TypeEq rigid.R (secondResult rigid).frame.raw secondTake.1.1.code secondTake.2.1.code := by
  refine ⟨run rigid, ?_, fun same => ?_⟩
  · show secondTake ∈ (secondFiring rigid).information (frames rigid.levels) (firstResult rigid)
    rw [secondFiring_information]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · have atZero : TypeEq rigid.R (empty rigid.R).raw (vecC one) (vecC zeroC) :=
      reindex_typeEquality same zeroInstance
    exact rigid_one_ne_zero (LogicOverTheStep.RigidReadback.vec_injective atZero)

end Hypothesis

/-! ## Rules without unknowns over the rigid package -/

section Ground

open Programs
open ProgrammingOnTheStep.VectorPackage (natC zeroC addC zero_typed add_typed nat_typed u0)
open ProgrammingOnTheStep.VectorPrograms (one two one_typed two_typed)

/-- A closed natural, as a row. -/
def natRow (code : Tower.Tm 0) (typed : Typed rigid.R Ctx.nil code natC) : TotalTerm (empty rigid.R) :=
  ⟨natType rigid _, ⟨code, typed⟩⟩

/-- `0`, `1`, `2` and the call `add 0 1`. -/
def zeroRow : TotalTerm (empty rigid.R) := natRow zeroC (zero_typed _)
def oneRow : TotalTerm (empty rigid.R) := natRow one (one_typed _)
def twoRow : TotalTerm (empty rigid.R) := natRow two (two_typed _)
def addRow : TotalTerm (empty rigid.R) := natRow (addC zeroC one) (add_typed (zero_typed _) (one_typed _))

/-- **A rule without unknowns**. -/
def groundRule (body : RuleInstance (TotalTerm (empty rigid.R))) : Rule (Terms rigid.R) :=
  telescopeRule (.nil _) body []

/-- Its canonical firing at a frame. -/
def groundFiring {P : Program (Terms rigid.R)} (body : RuleInstance (TotalTerm (empty rigid.R)))
    (member : groundRule body ∈ P) (Γ : Context rigid.R) (selection : Selection ℕ) :
    Firing ℕ (helperExtensions (rules := rigid.R)) P Γ :=
  canonicalFiring (.nil _) body [] member Γ selection []

/-- **An equation of naturals whose two sides have the same code is solved by every substitution.** -/
theorem solves_same_code {Γ Θ : Context rigid.R} (σ : Θ ⟶ Γ) (e : Equation (TotalTerm Γ))
    (code : Tower.Tm Γ.arity) (typed : Typed rigid.R Θ.raw (subst σ.substitution code) natC)
    (leftType : e.1.1.code = natC) (rightType : e.2.1.code = natC)
    (leftCode : e.1.2.code = code) (rightCode : e.2.2.code = code) :
    (frames rigid.levels).Solves σ e := by
  show TypeEq rigid.R Θ.raw (subst σ.substitution e.1.1.code) (subst σ.substitution e.2.1.code) ∧
    Equal rigid.R Θ.raw (subst σ.substitution e.1.2.code) (subst σ.substitution e.2.2.code)
      (subst σ.substitution e.1.1.code)
  rw [leftType, rightType, leftCode, rightCode]
  exact ⟨⟨u0, .sort _, .refl (nat_typed _)⟩, .refl typed⟩

/-- **A rule that answers a natural by a natural is well typed.** -/
theorem nat_answer_wellTyped (take made : TotalTerm (empty rigid.R))
    (checks : List (Check (TotalTerm (empty rigid.R)))) (takeType : take.1.code = natC)
    (madeType : made.1.code = natC) :
    WellTypedRule rigid.levels (groundRule ⟨[take], [], [], checks, [made]⟩) [some 0] := by
  refine (wellTypedRule_iff_of_tell_nil rigid.levels _ _ rfl).mpr ?_
  intro j i m c hj hm hc
  cases j with
  | succ j => simp at hj
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      have hm' : some made = some m := hm
      have hc' : some take = some c := hc
      obtain rfl := Option.some.inj hm'
      obtain rfl := Option.some.inj hc'
      rw [madeType, takeType]
      exact (TypeOver.isType (natType rigid (empty rigid.R))).refl

/-! ### Termination: a well-typed program that runs forever -/

/-- Take `0`, answer it by `0`. -/
def spinBody : RuleInstance (TotalTerm (empty rigid.R)) := ⟨[zeroRow], [], [], [], [zeroRow]⟩

def spin : Rule (Terms rigid.R) := groundRule spinBody

def spinProgram : Program (Terms rigid.R) := {spin}

/-- **The program is well typed**: its answer `0 : nat` has its call's type. -/
theorem spin_wellTyped : WellTypedProgram rigid.levels spinProgram (fun _ => [some 0]) := by
  intro r member
  have same : r = spin := member
  subst same
  exact nat_answer_wellTyped zeroRow zeroRow [] rfl rfl

/-- Equations of `0 : nat` with `0 : nat`. -/
def ZeroEquation {Γ : Context rigid.R} (e : Equation (TotalTerm Γ)) : Prop :=
  e.1.1.code = natC ∧ e.2.1.code = natC ∧ e.1.2.code = zeroC ∧ e.2.2.code = zeroC

/-- **The invariant of the spin run at step `n`**: the row `n` is present alone and is `0`, and the
knowledge equates `0` with `0`. -/
structure Spinning (s : State (Terms rigid.R) ℕ) (n : ℕ) : Prop where
  present : s.present = {n}
  labelType : (s.label n).1.code = natC
  labelCode : (s.label n).2.code = zeroC
  knowledge : ∀ e ∈ s.knowledge, ZeroEquation e

/-- The firing that takes row `n` and makes row `n + 1`. -/
def spinFiring (s : State (Terms rigid.R) ℕ) (n : ℕ) :
    Firing ℕ (helperExtensions (rules := rigid.R)) spinProgram s.frame :=
  groundFiring spinBody (Set.mem_singleton _) s.frame ⟨[n], [], [n + 1]⟩

theorem spin_information {s : State (Terms rigid.R) ℕ} {n : ℕ} (spinning : Spinning s n) :
    ∀ e ∈ (spinFiring s n).information (frames rigid.levels) s, ZeroEquation e := by
  intro e member
  simp only [Firing.information, List.mem_append] at member
  rcases member with ((old | take) | read) | tell
  · obtain ⟨e', inside, rfl⟩ := List.mem_map.mp old
    obtain ⟨a, b, c, d⟩ := spinning.knowledge e' inside
    refine ⟨?_, ?_, ?_, ?_⟩
    · show subst _ e'.1.1.code = natC
      rw [a]
      rfl
    · show subst _ e'.2.1.code = natC
      rw [b]
      rfl
    · show subst _ e'.1.2.code = zeroC
      rw [c]
      rfl
    · show subst _ e'.2.2.code = zeroC
      rw [d]
      rfl
  · have single : e = (zeroRow.reindex (toEmpty s.frame), (s.label n).reindex (𝟙 s.frame)) :=
      List.mem_singleton.mp take
    subst single
    refine ⟨rfl, ?_, rfl, ?_⟩
    · show subst _ (s.label n).1.code = natC
      rw [spinning.labelType]
      rfl
    · show subst _ (s.label n).2.code = zeroC
      rw [spinning.labelCode]
      rfl
  · exact absurd read List.not_mem_nil
  · exact absurd tell List.not_mem_nil

theorem spin_admitted {s : State (Terms rigid.R) ℕ} {n : ℕ} (spinning : Spinning s n) :
    (step (frames rigid.levels) ℕ helperExtensions spinProgram).Admits (s := s) (spinFiring s n) := by
  refine (RuleSyntax.admits_iff _).mpr ⟨canonical_fresh rigid.levels _ _ _ _ _ _ _,
    ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨s.frame, 𝟙 s.frame, fun e member => ?_⟩,
    fun c member => absurd member List.not_mem_nil, fun q member => absurd member List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [spinFiring, groundFiring, canonicalFiring, spinning.present, Selection.commit]
  · obtain ⟨a, b, c, d⟩ := spin_information spinning e member
    exact solves_same_code (𝟙 s.frame) e zeroC (zero_typed _) a b c d

theorem spin_result {s : State (Terms rigid.R) ℕ} {n : ℕ} (spinning : Spinning s n) :
    Spinning ((spinFiring s n).result (frames rigid.levels) s) (n + 1) := by
  have label : ((spinFiring s n).result (frames rigid.levels) s).label (n + 1) =
      zeroRow.reindex (toEmpty s.frame) :=
    relabel_getElem? _ _ _ 0 (List.nodup_singleton _) rfl rfl
  refine ⟨?_, ?_, ?_, spin_information spinning⟩
  · simp [Firing.result, spinFiring, groundFiring, canonicalFiring, spinning.present, fire,
      Selection.commit]
  · rw [label]
    rfl
  · rw [label]
    rfl

/-- The states of the spin run. -/
def spinStates : ℕ → State (Terms rigid.R) ℕ
  | 0 => ⟨empty rigid.R, [], {0}, fun _ => zeroRow⟩
  | n + 1 => (spinFiring (spinStates n) n).result (frames rigid.levels) (spinStates n)

theorem spinStates_spinning : ∀ n, Spinning (spinStates n) n
  | 0 => ⟨rfl, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩
  | n + 1 => spin_result (spinStates_spinning n)

/-- **Typing does not give termination**: a well-typed program with an infinite run. -/
theorem spin_runs_forever :
    WellTypedProgram rigid.levels spinProgram (fun _ => [some 0]) ∧
      ∀ n, Succ (step (frames rigid.levels) ℕ helperExtensions spinProgram).toStep (spinStates n)
        (spinStates (n + 1)) :=
  ⟨spin_wellTyped, fun n => ⟨spinFiring (spinStates n) n, spin_admitted (spinStates_spinning n), rfl⟩⟩

/-! ### Uniqueness: two well-typed answers to one call -/

/-- Take the call `add 0 1`, answer it by the given natural. -/
def answerBody (made : TotalTerm (empty rigid.R)) : RuleInstance (TotalTerm (empty rigid.R)) :=
  ⟨[addRow], [], [], [], [made]⟩

/-- **Two rules for one call**: `add 0 1 ↦ 1` and `add 0 1 ↦ 0`. -/
def twoAnswers : Program (Terms rigid.R) := {groundRule (answerBody oneRow), groundRule (answerBody zeroRow)}

theorem twoAnswers_wellTyped : WellTypedProgram rigid.levels twoAnswers (fun _ => [some 0]) := by
  intro r member
  rcases member with rfl | member
  · exact nat_answer_wellTyped addRow oneRow [] rfl rfl
  · have same : r = groundRule (answerBody zeroRow) := member
    subst same
    exact nat_answer_wellTyped addRow zeroRow [] rfl rfl

/-- The call `add 0 1`, alone. -/
def callState : State (Terms rigid.R) ℕ := ⟨empty rigid.R, [], {0}, fun _ => addRow⟩

/-- The firing of the rule answering by `made`, taking row `0` and making row `1`. -/
def answerFiring (made : TotalTerm (empty rigid.R)) (member : groundRule (answerBody made) ∈ twoAnswers) :
    Firing ℕ (helperExtensions (rules := rigid.R)) twoAnswers callState.frame :=
  groundFiring (answerBody made) member callState.frame ⟨[0], [], [1]⟩

theorem answerFiring_admitted (made : TotalTerm (empty rigid.R))
    (member : groundRule (answerBody made) ∈ twoAnswers) :
    (step (frames rigid.levels) ℕ helperExtensions twoAnswers).Admits (s := callState)
      (answerFiring made member) := by
  refine (RuleSyntax.admits_iff _).mpr ⟨canonical_fresh rigid.levels _ _ _ _ _ _ _,
    ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨empty rigid.R, 𝟙 _, ?_⟩, fun c member => absurd member List.not_mem_nil,
    fun q member => absurd member List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [answerFiring, groundFiring, canonicalFiring, callState, Selection.commit]
  · have information : (answerFiring made member).information (frames rigid.levels) callState =
        [(addRow.reindex (toEmpty (empty rigid.R)), addRow.reindex (𝟙 (empty rigid.R)))] := rfl
    rw [information]
    intro e inside
    obtain rfl := List.mem_singleton.mp inside
    exact solves_same_code (𝟙 _) _ (addC zeroC one) (add_typed (zero_typed _) (one_typed _))
      rfl rfl rfl rfl

/-- **Typing does not give uniqueness of answers**: both rules are well typed, both firings on the call
are admitted, they answer by `1` and by `0`, and no substitution equates the two answers. -/
theorem answers_not_unique :
    WellTypedProgram rigid.levels twoAnswers (fun _ => [some 0]) ∧
      (step (frames rigid.levels) ℕ helperExtensions twoAnswers).Admits (s := callState)
        (answerFiring oneRow (Set.mem_insert _ _)) ∧
      (step (frames rigid.levels) ℕ helperExtensions twoAnswers).Admits (s := callState)
        (answerFiring zeroRow (Set.mem_insert_of_mem _ (Set.mem_singleton _))) ∧
      ((answerFiring oneRow (Set.mem_insert _ _)).result (frames rigid.levels) callState).label 1 =
        oneRow.reindex (toEmpty (empty rigid.R)) ∧
      ((answerFiring zeroRow (Set.mem_insert_of_mem _ (Set.mem_singleton _))).result
          (frames rigid.levels) callState).label 1 = zeroRow.reindex (toEmpty (empty rigid.R)) ∧
      ∀ (Θ : Context rigid.R) (σ : Θ ⟶ empty rigid.R),
        ¬ (frames rigid.levels).E ((oneRow.reindex (toEmpty (empty rigid.R))).reindex σ)
          ((zeroRow.reindex (toEmpty (empty rigid.R))).reindex σ) :=
  ⟨twoAnswers_wellTyped, answerFiring_admitted _ _, answerFiring_admitted _ _, rfl, rfl,
    fun _ _ same => rigid_one_ne_zero same.2⟩

/-! ### The none query beside another program -/

/-- Take `0`, ask that no row is `1`, make `2`. -/
def guardedBody : RuleInstance (TotalTerm (empty rigid.R)) := ⟨[zeroRow], [], [], [.predicate .none oneRow], [twoRow]⟩

/-- Take `0`, make `1`. -/
def makerBody : RuleInstance (TotalTerm (empty rigid.R)) := ⟨[zeroRow], [], [], [], [oneRow]⟩

/-- **The guarded program and the maker, side by side.** -/
def guardedProgram : Program (Terms rigid.R) := {groundRule guardedBody}
def makerProgram : Program (Terms rigid.R) := {groundRule makerBody}
def both : Program (Terms rigid.R) := guardedProgram ∪ makerProgram

/-- **The union is well typed with each made row the answer to the taken row**: `2 : nat` answers
`0 : nat` in the guarded rule, and `1 : nat` answers `0 : nat` in the maker. -/
theorem both_wellTyped : WellTypedProgram rigid.levels both (fun _ => [some 0]) :=
  WellTypedProgram.union rigid.levels
    (fun r member => by
      have same : r = groundRule guardedBody := member
      subst same
      exact nat_answer_wellTyped zeroRow twoRow [.predicate .none oneRow] rfl rfl)
    (fun r member => by
      have same : r = groundRule makerBody := member
      subst same
      exact nat_answer_wellTyped zeroRow oneRow [] rfl rfl)

/-- Two rows `0`, identities `0` and `5`. -/
def pairState : State (Terms rigid.R) ℕ := ⟨empty rigid.R, [], {0, 5}, fun _ => zeroRow⟩

/-- The guarded firing on row `0`, making row `9`, at a state of the empty frame. -/
def guardedFiring (s : State (Terms rigid.R) ℕ) :
    Firing ℕ (helperExtensions (rules := rigid.R)) both s.frame :=
  groundFiring guardedBody (Set.mem_union_left _ (Set.mem_singleton _)) s.frame ⟨[0], [], [9]⟩

/-- The maker's firing on row `5`, making row `6`. -/
def makerFiring : Firing ℕ (helperExtensions (rules := rigid.R)) both pairState.frame :=
  groundFiring makerBody (Set.mem_union_right _ (Set.mem_singleton _)) pairState.frame ⟨[5], [], [6]⟩

/-- The state after the maker. -/
def afterMaker : State (Terms rigid.R) ℕ := makerFiring.result (frames rigid.levels) pairState

theorem guarded_admitted :
    (step (frames rigid.levels) ℕ helperExtensions both).Admits (s := pairState) (guardedFiring pairState) := by
  refine (RuleSyntax.admits_iff _).mpr ⟨canonical_fresh rigid.levels _ _ _ _ _ _ _,
    ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨empty rigid.R, 𝟙 _, ?_⟩, fun c member => ?_, fun q member => absurd member List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [guardedFiring, groundFiring, canonicalFiring, pairState, Selection.commit]
  · have information : (guardedFiring pairState).information (frames rigid.levels) pairState =
        [(zeroRow.reindex (toEmpty (empty rigid.R)), zeroRow.reindex (𝟙 (empty rigid.R)))] := rfl
    rw [information]
    intro e inside
    obtain rfl := List.mem_singleton.mp inside
    exact solves_same_code (𝟙 _) _ zeroC (zero_typed _) rfl rfl rfl rfl
  · have single : c = .predicate .none (oneRow.reindex (toEmpty (empty rigid.R))) := List.mem_singleton.mp member
    subst single
    intro Θ σ _ o _ equated
    exact rigid_one_ne_zero equated.2

theorem maker_admitted :
    (step (frames rigid.levels) ℕ helperExtensions both).Admits (s := pairState) makerFiring := by
  refine (RuleSyntax.admits_iff _).mpr ⟨canonical_fresh rigid.levels _ _ _ _ _ _ _,
    ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨empty rigid.R, 𝟙 _, ?_⟩, fun c member => absurd member List.not_mem_nil,
    fun q member => absurd member List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [makerFiring, groundFiring, canonicalFiring, pairState, Selection.commit]
  · have information : makerFiring.information (frames rigid.levels) pairState =
        [(zeroRow.reindex (toEmpty (empty rigid.R)), zeroRow.reindex (𝟙 (empty rigid.R)))] := rfl
    rw [information]
    intro e inside
    obtain rfl := List.mem_singleton.mp inside
    exact solves_same_code (𝟙 _) _ zeroC (zero_typed _) rfl rfl rfl rfl

theorem afterMaker_present : 6 ∈ afterMaker.present := by
  simp [afterMaker, Firing.result, makerFiring, groundFiring, canonicalFiring, pairState, fire,
    Selection.commit]

/-- **Typing does not protect a none query beside another program**: the union of the guarded rule and
the maker is well typed with each made row designated as the answer to the taken row, a designation
that is checked (it rejects `Programs.appendNil` in this package, whose answer `vec 1` does not have
its call's type `vec (add 0 1)`); the guarded firing is admitted; after the maker makes `1`, inside the
none region, the same firing is refused. -/
theorem none_not_compositional :
    WellTypedProgram rigid.levels both (fun _ => [some 0]) ∧
      ¬ WellTypedRule rigid.levels (Programs.appendNil rigid) [some 0] ∧
      (step (frames rigid.levels) ℕ helperExtensions both).Admits (s := pairState)
        (guardedFiring pairState) ∧
      Succ (step (frames rigid.levels) ℕ helperExtensions both).toStep pairState afterMaker ∧
      ¬ (step (frames rigid.levels) ℕ helperExtensions both).Admits (s := afterMaker)
        (guardedFiring afterMaker) := by
  refine ⟨both_wellTyped, Programs.rigid_appendNil_not_wellTyped, guarded_admitted,
    ⟨makerFiring, maker_admitted, rfl⟩, fun admitted => ?_⟩
  obtain ⟨-, -, -, ⟨b, σ, solved⟩, checks, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have holds := checks _ (List.mem_singleton_self _) b σ solved 6 afterMaker_present
  exact holds (equivalent_of_eq rigid.levels (totalTerm_ext (TypeOver.ext rfl rfl) rfl))

/-! ### Locality: what such a change may do -/

open ProgrammingOnTheStep.VectorPackage (setting facts complete)
open ProgrammingOnTheStep.VectorPrograms (natTerm)

/-- **`1 ≐ add 0 1` is refuted in the rigid package**: their heads differ. -/
theorem rigid_one_ne_add {Θ : Context rigid.R} : ¬ Equal rigid.R Θ.raw one (addC zeroC one) natC := by
  intro equal
  have refuted : ¬ (frames rigid.levels).Solvable
      [(natTerm one (one_typed _), natTerm (addC zeroC one) (add_typed (zero_typed _) (one_typed _)))] :=
    ContextualDependentRigid.not_solvable_of_storeClashes (S := setting)
      ProgrammingOnTheStep.VectorPackage.rigid facts complete (by decide)
  apply refuted
  refine ⟨Θ, toEmpty Θ, fun e member => ?_⟩
  obtain rfl := List.mem_singleton.mp member
  exact ⟨⟨u0, .sort _, .refl (nat_typed _)⟩, equal⟩

/-- Rows `0` and `5` present, both `0`; row `6`, not present, labelled by the given row. -/
def withSix (six : TotalTerm (empty rigid.R)) : State (Terms rigid.R) ℕ :=
  ⟨empty rigid.R, [], {0, 5}, fun o => if o = 6 then six else zeroRow⟩

theorem guarded_admitted_withSix (six : TotalTerm (empty rigid.R)) :
    (step (frames rigid.levels) ℕ helperExtensions both).Admits (s := withSix six)
      (guardedFiring (withSix six)) := by
  refine (RuleSyntax.admits_iff _).mpr ⟨canonical_fresh rigid.levels _ _ _ _ _ _ _,
    ⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩, ?_,
    ⟨empty rigid.R, 𝟙 _, ?_⟩, fun c member => ?_, fun q member => absurd member List.not_mem_nil⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [guardedFiring, groundFiring, canonicalFiring, withSix, Selection.commit]
  · have information : (guardedFiring (withSix six)).information (frames rigid.levels) (withSix six) =
        [(zeroRow.reindex (toEmpty (empty rigid.R)), zeroRow.reindex (𝟙 (empty rigid.R)))] := rfl
    rw [information]
    intro e inside
    obtain rfl := List.mem_singleton.mp inside
    exact solves_same_code (𝟙 _) _ zeroC (zero_typed _) rfl rfl rfl rfl
  · have single : c = .predicate .none (oneRow.reindex (toEmpty (empty rigid.R))) := List.mem_singleton.mp member
    subst single
    intro Θ σ _ o present equated
    have zeroOrFive : o = 0 ∨ o = 5 := by simpa [withSix] using present
    rcases zeroOrFive with rfl | rfl
    · exact rigid_one_ne_zero equated.2
    · exact rigid_one_ne_zero equated.2

/-- **Outside the region, locality keeps the none query admitted**: making row `6` present with the label
`add 0 1`, which no solution equates with `1`, is a change outside the guarded firing's regions, so
`admits_of_outsideRegions` keeps it admitted. -/
theorem locality_outside :
    OutsideRegions (frames rigid.levels) (withSix addRow) {0, 5, 6} (guardedFiring (withSix addRow)) ∧
      (step (frames rigid.levels) ℕ helperExtensions both).Admits
        (s := (withSix addRow).withPresent {0, 5, 6}) (guardedFiring (withSix addRow)) := by
  have outside : OutsideRegions (frames rigid.levels) (withSix addRow) {0, 5, 6}
      (guardedFiring (withSix addRow)) := by
    refine ⟨fun o selected => ?_, fun b σ _ p member o changed => ?_⟩
    · have zeroOrNine : o = 0 ∨ o = 9 := by
        simpa [guardedFiring, groundFiring, canonicalFiring] using selected
      rcases zeroOrNine with rfl | rfl <;> simp [withSix]
    · have six : o = 6 := by
        by_contra other
        apply changed
        simp [withSix, other]
      subst six
      have single : p = oneRow.reindex (toEmpty (empty rigid.R)) := by
        rcases List.mem_append.mp member with checkPart | collectPart
        · exact List.mem_singleton.mp checkPart
        · exact absurd collectPart List.not_mem_nil
      subst single
      intro equated
      exact rigid_one_ne_add equated.2
  exact ⟨outside, admits_of_outsideRegions (guarded_admitted_withSix addRow) outside
    (canonical_fresh rigid.levels _ _ _ _ ((withSix addRow).withPresent {0, 5, 6}) _ _)⟩

/-- **Inside the region, the same change refuses it**: row `6` labelled `1`. -/
theorem locality_inside :
    (step (frames rigid.levels) ℕ helperExtensions both).Admits (s := withSix oneRow)
        (guardedFiring (withSix oneRow)) ∧
      ¬ (step (frames rigid.levels) ℕ helperExtensions both).Admits
        (s := (withSix oneRow).withPresent {0, 5, 6}) (guardedFiring (withSix oneRow)) := by
  refine ⟨guarded_admitted_withSix oneRow, fun admitted => ?_⟩
  obtain ⟨-, -, -, ⟨b, σ, solved⟩, checks, -⟩ := (RuleSyntax.admits_iff _).mp admitted
  have holds := checks _ (List.mem_singleton_self _) b σ solved 6 (by simp [State.withPresent])
  exact holds (equivalent_of_eq rigid.levels (totalTerm_ext (TypeOver.ext rfl rfl) rfl))

end Ground

#print axioms wellTypedRule_iff_of_initial
#print axioms rigid_one_ne_zero
#print axioms program_tells_nothing
#print axioms heterogeneous_take
#print axioms nat_answer_wellTyped
#print axioms spin_wellTyped
#print axioms spin_runs_forever
#print axioms answers_not_unique
#print axioms both_wellTyped
#print axioms guarded_admitted
#print axioms none_not_compositional
#print axioms rigid_one_ne_add
#print axioms locality_outside
#print axioms locality_inside

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Typing
