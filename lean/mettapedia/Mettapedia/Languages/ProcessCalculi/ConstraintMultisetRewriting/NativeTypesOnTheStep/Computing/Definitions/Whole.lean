import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.OnDefinitionsDouble

/-!
# The whole function: calls, their answers, and the uncovered calls

For every checked function (`Checked d b c`), with no proof about the particular definition:

* **Every call at arguments typed along the telescope is typed at the call's declared type**, and every
  answer it has is of that type, typed-equal to the call, and the only one (`call_typed`,
  `call_answer`). The call is the compiled function applied to the arguments in telescope order
  (`applyClosed`), in the base context: the empty context when the rows cover.
* **A call that is an instance of a row answers by that row**: it converts to the row's right side at
  the instance, and when that right side is normal it is the call's unique answer (`covered_call`).
* **The uncovered calls answer themselves.** When the rows do not cover, an instance of an uncovered
  case, at normal arguments and with the function's own name kept as a variable, has exactly one
  answer: the stuck call of that name, which is no answer computed by a row (`uncovered_call`).

**Existence.** An answer here is a normal form of the full reduction, which includes the equality of
universe heads, so a term whose normal forms contain a head has none. Existence is proved for the answers
of the directed reduction (`DirectedAnswers.DirectedAnswer`), call by call: a ground call of a closed
checked function, at arguments typed along its telescope, whose declared result type at those arguments
is a data type, has exactly one, a value of that type (`DirectedAnswers.ground_call_answer`). The
condition is on the call and not on the function: the declared result type of `append` is open, and its
calls at a data type of elements meet it. A value, having no head, is an answer here as well
(`DirectedAnswers.answer_iff_headFree`, whose two hypotheses, a constructor presentation and heads related
to themselves, hold of this package). The answers of the listed ground calls are found by the package's
executable reduction (`ground_answers`), and by the theorems above they are the only answers and have
the declared types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TelescopeAbstraction (closeType applyClosed)
open ConversionCoherence (StepStar)
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one two three single twoThree)
open Vectors (vecNormalize vecNormalize_sound const_normal succ_normal pair_normal)
open Vectors.Checker (Row Definition headDef evalDef appendDef)

/-! ## Calls are typed, their answers unique and typed -/

/-- The checker's dependent function type of a telescope is the tree's. -/
theorem closePi_eq_closeType : ∀ {n : Nat} (Γ : Ctx Tower.Head n) (C : Tower.Tm n),
    Vectors.Checker.closePi Γ C = closeType Γ C
  | _, .nil, _ => rfl
  | _, .snoc Γ A, C => closePi_eq_closeType Γ (.pi A C)

/-- **Every call is typed at its declared type**: the compiled function, applied in telescope order to
arguments typed along the telescope in the base context. -/
theorem call_typed {d : Definition} {b : Nat} {c : Tower.Tm b} (checked : Checked d b c)
    {σ : Sub Tower.Head d.arity b} (args : SubstMor pkg d.telescope (baseCtx d b) σ) :
    Typed pkg (baseCtx d b) (applyClosed d.telescope σ c) (subst σ d.result) := by
  have typed := checked.guarantee.1
  unfold Definition.type at typed
  rw [closePi_eq_closeType] at typed
  exact Typed.telescope_apply args typed

/-- **Every answer of a call is of the call's declared type, typed-equal to it, and the only one.** -/
theorem call_answer {d : Definition} {b : Nat} {c : Tower.Tm b} (checked : Checked d b c)
    (formed : CtxFormed pkg (baseCtx d b)) {σ : Sub Tower.Head d.arity b}
    (args : SubstMor pkg d.telescope (baseCtx d b) σ) {v : Tower.Tm b}
    (answer : Answer pkg (applyClosed d.telescope σ c) v) :
    Typed pkg (baseCtx d b) v (subst σ d.result) ∧
      Equal pkg (baseCtx d b) (applyClosed d.telescope σ c) v (subst σ d.result) ∧
      ∀ v', Answer pkg (applyClosed d.telescope σ c) v' → v' = v :=
  call_answers formed (call_typed checked args) answer

/-! ## Calls that are instances of rows -/

/-- **A covered call answers by its row**: at every instance of a row's pattern, the call converts to
the row's right side, and when that right side is normal it is the call's unique answer. -/
theorem covered_call {d : Definition} {b : Nat} {c : Tower.Tm b} (checked : Checked d b c)
    {shapes : List (Row × Bool × List Slot)} (found : shapesOf d = some shapes)
    {s : Row × Bool × List Slot} (member : s ∈ shapes) :
    ∃ l, lhs b c s.1 s.2.2 s.2.1 = some l ∧ ∀ {m : Nat} (σ : Sub Tower.Head (b + s.1.vars) m),
      Conv pkg.headEq (subst σ l) (subst σ (rhs b c s.1 s.2.2 s.2.1)) pkg.computation ∧
      (ConstructorSystem.Normal pkg (subst σ (rhs b c s.1 s.2.2 s.2.1)) →
        Answer pkg (subst σ l) (subst σ (rhs b c s.1 s.2.2 s.2.1)) ∧
          ∀ v, Answer pkg (subst σ l) v → v = subst σ (rhs b c s.1 s.2.2 s.2.1)) := by
  obtain ⟨-, ⟨shapes', found', -, rows⟩, -⟩ := checked.guarantee
  rw [found] at found'
  obtain rfl := Option.some.inj found'
  obtain ⟨l, hl, conv⟩ := rows s member
  refine ⟨l, hl, fun σ => ⟨conv σ, fun normal => ?_⟩⟩
  have answer : Answer pkg (subst σ l) (subst σ (rhs b c s.1 s.2.2 s.2.1)) :=
    (Vectors.vectors_answer_iff level1).mpr ⟨conv σ, normal⟩
  exact ⟨answer, fun v other => Vectors.vectors_answer_unique level1 other answer⟩

/-! ## The uncovered calls -/

/-- A variable applied to normal arguments. -/
inductive VarSpine : {n : Nat} → Tower.Tm n → Prop
  | var {n : Nat} (x : Fin n) : VarSpine (.var x)
  | app {n : Nat} {g a : Tower.Tm n} : VarSpine g → ConstructorSystem.Normal pkg a → VarSpine (.app g a)

theorem VarSpine.spineHead {n : Nat} {t : Tower.Tm n} (spine : VarSpine t) :
    ConstructorSystem.spineHead t = none := by
  induction spine with
  | var x => rfl
  | app _ _ ih => simp [ConstructorSystem.spineHead, ih]

/-- **A variable applied to normal arguments is normal**: no row of the package has a variable at the
head of its left side, and a variable is no abstraction. -/
theorem VarSpine.normal {n : Nat} {t : Tower.Tm n} (spine : VarSpine t) : ConstructorSystem.Normal pkg t := by
  induction spine with
  | var x =>
      intro target step
      cases step with
      | root h => exact (Vectors.vectorConstructors level1).no_root_of_spineHead h rfl
  | app sg na ih =>
      intro target step
      cases step with
      | root h => exact (Vectors.vectorConstructors level1).no_root_of_spineHead h (VarSpine.spineHead (.app sg na))
      | betaPi body arg => cases sg
      | congAppFun inner => exact ih inner
      | congAppArg inner => exact na inner

theorem subst_spine {n m : Nat} (σ : Sub Tower.Head n m) :
    ∀ (g : Tower.Tm n) (as : List (Tower.Tm n)), subst σ (spine g as) = spine (subst σ g) (as.map (subst σ))
  | _, [] => rfl
  | g, a :: as => subst_spine σ (.app g a) as

theorem varSpine_spine {n : Nat} (x : Fin n) :
    ∀ (as : List (Tower.Tm n)) {g : Tower.Tm n}, VarSpine g → (∀ a ∈ as, ConstructorSystem.Normal pkg a) →
      VarSpine (spine g as)
  | [], _, sg, _ => sg
  | a :: as, _, sg, normal =>
      varSpine_spine x as (.app sg (normal a (List.mem_cons_self ..)))
        (fun a' member => normal a' (List.mem_cons_of_mem _ member))

/-- **The uncovered calls answer themselves.** For a checked function over its own name and a case
without a row: at every instance that keeps the function's name a variable `y` and makes the case's
arguments normal, the call has exactly one answer, the stuck call `y args`. -/
theorem uncovered_call {d : Definition} {c : Tower.Tm 1} (checked : Checked d 1 c) {j : Nat} {kind : Kind}
    (hs : scrutinee d = some (j, kind)) {case : Bool} (uncov : case ∈ uncovered d) :
    ∃ (args : List (Tower.Tm (1 + caseVars d.arity j kind case))) (f : Tower.Tm (1 + caseVars d.arity j kind case)),
      baseName 1 (caseVars d.arity j kind case) = some f ∧
      ∀ {m : Nat} (σ : Sub Tower.Head (1 + caseVars d.arity j kind case) m) (y : Fin m),
        subst σ f = .var y → (∀ a ∈ args.map (subst σ), ConstructorSystem.Normal pkg a) →
        Answer pkg (subst σ (spine (rename (shiftBase 1 _) c) args)) (spine (.var y) (args.map (subst σ))) ∧
        ∀ v, Answer pkg (subst σ (spine (rename (shiftBase 1 _) c) args)) v → v = spine (.var y) (args.map (subst σ)) := by
  obtain ⟨-, -, stuck⟩ := checked.guarantee
  obtain ⟨fuel, ok⟩ := stuck j kind hs case uncov
  obtain ⟨slots, args, f, -, -, hf, conv⟩ := stuckConverts_holds ok
  refine ⟨args, f, hf, fun σ y named normal => ?_⟩
  have stuckForm : subst σ (spine f args) = spine (.var y) (args.map (subst σ)) := by
    rw [subst_spine, named]
  have stuckNormal : ConstructorSystem.Normal pkg (spine (.var y) (args.map (subst σ))) :=
    (varSpine_spine y _ (.var y) normal).normal
  have conversion := conv σ
  rw [stuckForm] at conversion
  have answer := (Vectors.vectors_answer_iff level1).mpr ⟨conversion, stuckNormal⟩
  exact ⟨answer, fun v other => Vectors.vectors_answer_unique level1 other answer⟩

/-- **`head`'s uncovered calls answer themselves**: the generic theorem, at `head`'s checked function. -/
theorem head_uncovered :
    ∃ c, Checked headDef 1 c ∧ ∀ j kind, scrutinee headDef = some (j, kind) → ∀ case ∈ uncovered headDef,
      ∃ (args : List (Tower.Tm (1 + caseVars headDef.arity j kind case))) (f : Tower.Tm (1 + caseVars headDef.arity j kind case)),
        baseName 1 (caseVars headDef.arity j kind case) = some f ∧
        ∀ {m : Nat} (σ : Sub Tower.Head (1 + caseVars headDef.arity j kind case) m) (y : Fin m),
          subst σ f = .var y → (∀ a ∈ args.map (subst σ), ConstructorSystem.Normal pkg a) →
          Answer pkg (subst σ (spine (rename (shiftBase 1 _) c) args)) (spine (.var y) (args.map (subst σ))) ∧
          ∀ v, Answer pkg (subst σ (spine (rename (shiftBase 1 _) c) args)) v →
            v = spine (.var y) (args.map (subst σ)) := by
  obtain ⟨c, checked⟩ := head_checked
  exact ⟨c, checked, fun j kind hs case uncov => uncovered_call checked hs uncov⟩

/-- `head`'s only uncovered case is length zero. -/
theorem head_uncovered_cases : scrutinee headDef = some (1, .vector 2) ∧ uncovered headDef = [false] := by
  constructor <;> rfl

/-! ## Rows that answer by their right side -/

/-- **Constructor terms**: variables under `zero`, `succ`, `tt` and pairs. -/
inductive ConTerm : {n : Nat} → Tower.Tm n → Prop
  | var {n : Nat} (x : Fin n) : ConTerm (.var x)
  | zero {n : Nat} : ConTerm (zeroC : Tower.Tm n)
  | tt {n : Nat} : ConTerm (ttC : Tower.Tm n)
  | succ {n : Nat} {t : Tower.Tm n} : ConTerm t → ConTerm (succC t)
  | pair {n : Nat} {a b : Tower.Tm n} : ConTerm a → ConTerm b → ConTerm (.pair a b)

/-- The decision of the constructor terms. -/
def conTerm? : {n : Nat} → Tower.Tm n → Bool
  | _, .var _ => true
  | _, .const c => c == TowerNumbersModel.zero || c == TowerVectorsModel.tt
  | _, .app g t =>
      match g with
      | .const c => c == TowerNumbersModel.succ && conTerm? t
      | _ => false
  | _, .pair a b => conTerm? a && conTerm? b
  | _, _ => false

theorem conTerm?_sound : ∀ {n : Nat} {t : Tower.Tm n}, conTerm? t = true → ConTerm t
  | _, .var x, _ => .var x
  | _, .const c, h => by
      simp only [conTerm?, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | rfl
      · exact .zero
      · exact .tt
  | _, .app (.const c) t, h => by
      simp only [conTerm?, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, ht⟩ := h
      exact .succ (conTerm?_sound ht)
  | _, .pair a b, h => by
      simp only [conTerm?, Bool.and_eq_true] at h
      exact .pair (conTerm?_sound h.1) (conTerm?_sound h.2)
  | _, .head _, h => by simp [conTerm?] at h
  | _, .pi _ _, h => by simp [conTerm?] at h
  | _, .sigma _ _, h => by simp [conTerm?] at h
  | _, .id _ _ _, h => by simp [conTerm?] at h
  | _, .lam _, h => by simp [conTerm?] at h
  | _, .app (.var _) _, h => by simp [conTerm?] at h
  | _, .app (.head _) _, h => by simp [conTerm?] at h
  | _, .app (.pi _ _) _, h => by simp [conTerm?] at h
  | _, .app (.sigma _ _) _, h => by simp [conTerm?] at h
  | _, .app (.id _ _ _) _, h => by simp [conTerm?] at h
  | _, .app (.lam _) _, h => by simp [conTerm?] at h
  | _, .app (.app _ _) _, h => by simp [conTerm?] at h
  | _, .app (.pair _ _) _, h => by simp [conTerm?] at h
  | _, .app (.fst _) _, h => by simp [conTerm?] at h
  | _, .app (.snd _) _, h => by simp [conTerm?] at h
  | _, .app (.refl _) _, h => by simp [conTerm?] at h
  | _, .fst _, h => by simp [conTerm?] at h
  | _, .snd _, h => by simp [conTerm?] at h
  | _, .refl _, h => by simp [conTerm?] at h

/-- **A constructor term at normal values is normal.** -/
theorem ConTerm.normal_subst {n m : Nat} {t : Tower.Tm n} (con : ConTerm t) {σ : Sub Tower.Head n m}
    (values : ∀ x, ConstructorSystem.Normal pkg (σ x)) : ConstructorSystem.Normal pkg (subst σ t) := by
  induction con with
  | var x => exact values x
  | zero => exact const_normal level1 (by decide)
  | tt => exact const_normal level1 (by decide)
  | succ _ ih => exact succ_normal level1 ih
  | pair _ _ iha ihb => exact pair_normal level1 iha ihb

/-- **A row whose right side is a constructor term answers by it**: at every instance by normal
terms, the call's unique answer is the row's right side there. -/
theorem constructor_row_answers {d : Definition} {b : Nat} {c : Tower.Tm b} (checked : Checked d b c)
    {shapes : List (Row × Bool × List Slot)} (found : shapesOf d = some shapes)
    {s : Row × Bool × List Slot} (member : s ∈ shapes) (con : conTerm? (rhs b c s.1 s.2.2 s.2.1) = true) :
    ∃ l, lhs b c s.1 s.2.2 s.2.1 = some l ∧ ∀ {m : Nat} (σ : Sub Tower.Head (b + s.1.vars) m),
      (∀ x, ConstructorSystem.Normal pkg (σ x)) →
      Answer pkg (subst σ l) (subst σ (rhs b c s.1 s.2.2 s.2.1)) ∧
        ∀ v, Answer pkg (subst σ l) v → v = subst σ (rhs b c s.1 s.2.2 s.2.1) := by
  obtain ⟨l, hl, rows⟩ := covered_call checked found member
  exact ⟨l, hl, fun σ values => (rows σ).2 ((conTerm?_sound con).normal_subst values)⟩

/-- **`head`, every call**: its one row answers by the head of the vector at every instance by normal
terms, and its uncovered case answers itself (`head_uncovered`). -/
theorem head_row_answers : ∃ c, Checked headDef 1 c ∧ ∀ s ∈ [(Vectors.Checker.headRow, true,
      [Slot.param 0, Slot.index, Slot.pred, Slot.head 2, Slot.tail 2])],
    ∃ l, lhs 1 c s.1 s.2.2 s.2.1 = some l ∧ ∀ {m : Nat} (σ : Sub Tower.Head (1 + s.1.vars) m),
      (∀ x, ConstructorSystem.Normal pkg (σ x)) →
      Answer pkg (subst σ l) (subst σ (rhs 1 c s.1 s.2.2 s.2.1)) ∧
        ∀ v, Answer pkg (subst σ l) v → v = subst σ (rhs 1 c s.1 s.2.2 s.2.1) := by
  obtain ⟨c, checked⟩ := head_checked
  have found : shapesOf headDef = some [(Vectors.Checker.headRow, true,
      [Slot.param 0, Slot.index, Slot.pred, Slot.head 2, Slot.tail 2])] := rfl
  refine ⟨c, checked, fun s member => constructor_row_answers checked found member ?_⟩
  obtain rfl := List.mem_singleton.mp member
  rfl

/-! ## Answers of listed ground calls -/

/-- **Ground calls, run by the package's executable reduction**, each by kernel evaluation:
* addition by rows, `add 2 1 = 3`;
* append on it, `append num 1 1 [2] [3] = [2, 3]`;
* doubling the append, `double num 1 [3] = [3, 3]`;
* map, `map num num succ 2 [2, 3] = [3, 4]`;
* `head num 1 [3] = 3`, and `head num 0 nil` stuck at the function's own name;
* the literal row, `eval 0 3 = 3`, and `eval 1 3` stuck at the function's own name. -/
theorem ground_answers :
    vecNormalize level1 40 (spine addTerm [two, one]) = some three ∧
    vecNormalize level1 60 (spine appendRTerm [numC, one, one, single two, single three]) = some twoThree ∧
    vecNormalize level1 80 (spine doubleOnAppend [numC, one, single three]) = some (.pair three (single three)) ∧
    ((compile 0 mapDef).bind fun c => vecNormalize level1 60
      (spine c [numC, numC, .lam (succC (.var 0)), two, twoThree])) =
        some (.pair three (single (succC three))) ∧
    ((compile 1 headDef).bind fun c => vecNormalize level1 40 (spine c [numC, one, single three])) =
      some three ∧
    ((compile 1 headDef).bind fun c => vecNormalize level1 40 (spine c [numC, zeroC, ttC])) =
      some (spine (.var 0) [numC, zeroC, ttC]) ∧
    ((compile 1 evalDef).bind fun c => vecNormalize level1 40 (spine c [zeroC, three])) = some three ∧
    ((compile 1 evalDef).bind fun c => vecNormalize level1 40 (spine c [one, three])) =
      some (spine (.var 0) [one, three]) := by
  decide +kernel

/-- **Addition's ground call `add 2 1` has exactly one answer, `3`, of type `num`.** -/
theorem add_ground : Answer pkg (spine addTerm [two, one]) three ∧
    (∀ v, Answer pkg (spine addTerm [two, one]) v → v = three) := by
  have answer : Answer pkg (spine addTerm [two, one]) three :=
    ⟨vecNormalize_sound level1 ground_answers.1,
      succ_normal level1 (succ_normal level1 (succ_normal level1 (const_normal level1 (by decide))))⟩
  exact ⟨answer, fun v other => Vectors.vectors_answer_unique level1 other answer⟩

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.closePi_eq_closeType
#print axioms NativeTypesOnTheStep.Computing.Definitions.call_typed
#print axioms NativeTypesOnTheStep.Computing.Definitions.call_answer
#print axioms NativeTypesOnTheStep.Computing.Definitions.covered_call
#print axioms NativeTypesOnTheStep.Computing.Definitions.VarSpine.normal
#print axioms NativeTypesOnTheStep.Computing.Definitions.subst_spine
#print axioms NativeTypesOnTheStep.Computing.Definitions.uncovered_call
#print axioms NativeTypesOnTheStep.Computing.Definitions.head_uncovered
#print axioms NativeTypesOnTheStep.Computing.Definitions.head_uncovered_cases
#print axioms NativeTypesOnTheStep.Computing.Definitions.conTerm?_sound
#print axioms NativeTypesOnTheStep.Computing.Definitions.ConTerm.normal_subst
#print axioms NativeTypesOnTheStep.Computing.Definitions.constructor_row_answers
#print axioms NativeTypesOnTheStep.Computing.Definitions.head_row_answers
#print axioms NativeTypesOnTheStep.Computing.Definitions.ground_answers
#print axioms NativeTypesOnTheStep.Computing.Definitions.add_ground

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
