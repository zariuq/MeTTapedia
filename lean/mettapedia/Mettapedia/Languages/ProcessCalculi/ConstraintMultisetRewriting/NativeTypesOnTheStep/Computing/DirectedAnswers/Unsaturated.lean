import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DirectedAnswers.Rows

/-!
# A recursive call passed on without its later arguments

The compiler replaces the recursive call prefix `f x₀ … x_{j-1} k` by the induction hypothesis, a
function of the later parameters (`Definitions.translate`). So a row may pass that prefix on as a
function, without the later arguments, and the definition stays in the class of checked functions.
Declared as a constant of an extended package, its rule at `succ k` then has the constant applied to
fewer arguments than its arity on the right side, and the conditions of `Definitions.Recursive`, under
which `rows_reach` is proved, fail.

The definition: `twist : Π (h : (num → num) → num → num) (n m : num). num`, with the rows
`twist h zero m = m` and `twist h (succ k) m = succ (h (twist h k) m)`.

* **It is a closed checked function** (`twist_verdict`, at budget 32; `twist_checked`), its development
  passes the declaration-time check (`twist_devCheck`), and its two rules, read at its compiled term,
  join (`twist_read`).
* **The reading is sound for it** (`twist_sound`, by `value_of_reading`): whenever its rows take a closed
  term to a value, that value is the answer of the reading.
* **Agreement by conversion fails for it, at a full call** (`twist_not_agree`): with variables for `h`
  and `m`, the call `twist h 1 m` by rows reduces to `succ (h (twist h zero) m)`, a normal form of the
  extended package that mentions the declared constant (`twistStuck_normal`); the compiled call does
  not mention it, and such a normal form is convertible with no term of the package
  (`Definitions.normal_not_conv_old`). So the definition is not in the class, at its own call index
  (`twist_not_recursive`); of the conditions of the class only saturation fails (`twist_control`).
* **The ground calls that were run agree** (`twist_ground`): at `h = λ f x. f x` and at
  `h = λ f x. f (f x)`, the call `twist h 2 1` by rows has exactly one answer, `3` and `4`, and it is
  the answer of the compiled call.

**What is not proved for such a definition**: that every ground call at a data type has an answer by
its rows. An answer that is a value is the compiled call's, by soundness; two answers are equal, by
confluence (`dev_directed_unique`). The induction on the numeral that gives agreement for saturated
calls would need its hypothesis at the partial call `twist h k`, and a partial call of a declared
constant is a normal form that mentions it (`Definitions.partial_not_convertible` for addition).

**The contrast, inside the class** (`acc_rowsReach`, `acc_rows_answer`): the accumulating sum
`sumAcc zero acc = acc`, `sumAcc (succ k) acc = sumAcc k (succ acc)` changes its later argument in the
recursive call and keeps the call saturated. It is in the class, and every ground call of its declared
constant has exactly one answer, the answer of the compiled call. What the class asks of a recursive
call is all its arguments, with the predecessor at the call index; the later arguments are free.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DirectedAnswers

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema (SchemaTable)
open ConstantExpansion (expand Bodies)
open TelescopeAbstraction (applyClosed)
open TowerVectorsModel (numC zeroC succC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one two three)
open Vectors.Checker (Pattern Row Definition)
open Definitions (Development devCheck devRules devPackage OldTerm Recursive genericCall reading Checked
  nat spine)

/-! ## The definition -/

/-- `twist h zero m = m`. -/
def twistZeroRow : Row := ⟨[.var, .zero, .var], 2, .var 0⟩

/-- `twist h (succ k) m = succ (h (twist h k) m)`; the function is variable 3. The recursive call
`twist h k` is passed to `h` without its last argument. -/
def twistSuccRow : Row := ⟨[.var, .succ .var, .var], 3,
  succC (.app (.app (.var 2) (.app (.app (.var 3) (.var 2)) (.var 1))) (.var 0))⟩

/-- **A recursive call passed on as a function**:
`twist : Π (h : (num → num) → num → num) (n m : num). num`. -/
def twistDef : Definition :=
  ⟨"twist", 3, .snoc (.snoc (.snoc .nil (.pi (.pi numC numC) (.pi numC numC))) numC) numC, numC,
    [twistZeroRow, twistSuccRow]⟩

/-- **It is a closed function**, at budget 32. -/
theorem twist_verdict : Definitions.qualify 32 twistDef = .function true := by decide +kernel

/-- Its compiled term: `λ h n. num-rec (λ n. num → num) (λ m. m) (λ k ih m. succ (h ih m)) n`. The
induction hypothesis `ih` is passed to `h` as a function. -/
def twistTerm : Tower.Tm 0 :=
  .lam (.lam (Vectors.numRecAt (.lam (.pi numC numC)) (.lam (.var 0))
    (.lam (.lam (.lam (succC (.app (.app (.var 4) (.var 1)) (.var 0)))))) (.var 0)))

theorem twist_compiles : Definitions.compile 0 twistDef = some twistTerm := by decide +kernel

theorem twist_checked : Checked twistDef 0 twistTerm := by
  obtain ⟨c, checked⟩ := Definitions.qualify_closed twist_verdict
  obtain rfl : c = twistTerm := Option.some.inj (checked.compiled.symm.trans twist_compiles)
  exact checked

/-! ## As a constant of an extended package -/

/-- The constant of `twist`. -/
def twistName : DeclName := .mkSimple "twist-by-rows"

/-- The development of `twist` alone. -/
abbrev twistDev : Development := [(twistName, twistDef)]

/-- Its rules: `twist h zero m ⟶ m` and `twist h (succ k) m ⟶ succ (h (twist h k) m)`. On the right
of the second the constant has two of its three arguments. -/
abbrev twistRows : SchemaTable Tower.Head :=
  [⟨2, (spine (.const twistName) [.var 1, zeroC, .var 0], .var 0)⟩,
    ⟨3, (spine (.const twistName) [.var 2, succC (.var 1), .var 0],
      succC (.app (.app (.var 2) (spine (.const twistName) [.var 2, .var 1])) (.var 0)))⟩]

/-- The package extended by `twist` by rows. -/
abbrev twistExt : Rules Tower.Head := devPackage twistDev twistRows

theorem twist_devCheck : devCheck twistDev = true := by decide +kernel

theorem twist_fresh : Definitions.devFresh twistDev = true := by decide +kernel

theorem twist_rules : devRules twistDev = some twistRows := by decide +kernel

/-- **Both rules, read at the compiled term, join.** -/
theorem twist_read : Definitions.rulesRead 60 (reading [(twistName, twistTerm)]) twistRows = true := by
  decide +kernel

/-- The reading reads every constant outside the development as itself. -/
theorem twist_others (d : DeclName) (absent : ∀ e ∈ twistDev, e.1 ≠ d) :
    reading [(twistName, twistTerm)] d = .const d :=
  Definitions.reading_single_other twistTerm (absent (twistName, twistDef) (List.mem_cons_self ..)).symm

/-- **The reading is sound for `twist`**: whenever its rows take a closed term to a value, that value is
the answer of the reading of the term. -/
theorem twist_sound {t v : Tower.Tm 0} (value : Value v)
    (steps : StrongNormalization.ReducesStar twistExt t v) :
    DirectedAnswer pkg (expand (reading [(twistName, twistTerm)]) t) v :=
  value_of_reading twist_devCheck twist_rules twist_others twist_read value steps

/-! ## Agreement by conversion fails at a full call -/

/-- The arguments of the call `twist h 1 m`, with variables for `h` and `m`. -/
def twistOpen : Sub Tower.Head (1 + 1 + 1) 2 := fun x =>
  if x.val = 0 then .var 0 else if x.val = 1 then nat 1 else .var 1

/-- `succ (h (twist h zero) m)`: what the call `twist h 1 m` by rows reduces to. -/
def twistStuck : Tower.Tm 2 :=
  succC (.app (.app (.var 1) (spine (.const twistName) [.var 1, zeroC])) (.var 0))

theorem twistOpen_runs :
    Definitions.devNormalize twistDev twistRows 20 (subst twistOpen (genericCall twistName 1 1)) =
      some twistStuck := by
  decide +kernel

/-- **`succ (h (twist h zero) m)` is a normal form of the extended package.** The constant has two of
its three arguments, so no rule of it applies; `h` is a variable; `succ` is not defined. -/
theorem twistStuck_normal : ConstructorSystem.Normal twistExt twistStuck := by
  have root : ∀ {t target : Tower.Tm 2}, twistExt.computation.step t target →
      ∃ name, ConstructorSystem.spineHead t = some (name, Definitions.devArity twistDev name) ∧
        0 < Definitions.devArity twistDev name ∧ Definitions.devDefined twistDev name = true :=
    fun step => Definitions.dev_root_spine twist_devCheck twist_rules step
  have varNormal : ∀ i : Fin 2, ConstructorSystem.Normal twistExt (.var i : Tower.Tm 2) := by
    intro i target step
    cases step with
    | root h => exact (Definitions.devConstructors twist_devCheck twist_rules).no_root_of_spineHead h rfl
  have constNormal : ∀ c : DeclName, ConstructorSystem.Normal twistExt (.const c : Tower.Tm 2) := by
    intro c
    refine ConstructorSystem.Normal.const c ?_
    intro target step
    obtain ⟨name, head, positive, -⟩ := root step
    have computed : ConstructorSystem.spineHead (.const c : Tower.Tm 2) = some (c, 0) := rfl
    rw [computed] at head
    simp only [Option.some.injEq, Prod.mk.injEq] at head
    obtain ⟨rfl, arity⟩ := head
    omega
  have oneArgument : ConstructorSystem.Normal twistExt (.app (.const twistName) (.var 1) : Tower.Tm 2) := by
    refine ConstructorSystem.Normal.app (constNormal _) (varNormal _) (fun body h => by cases h) ?_
    intro target step
    obtain ⟨name, head, -, -⟩ := root step
    have computed : ConstructorSystem.spineHead (.app (.const twistName) (.var 1) : Tower.Tm 2) =
        some (twistName, 1) := rfl
    rw [computed] at head
    simp only [Option.some.injEq, Prod.mk.injEq] at head
    obtain ⟨rfl, arity⟩ := head
    exact absurd arity (by decide)
  have twoArguments : ConstructorSystem.Normal twistExt
      (.app (.app (.const twistName) (.var 1)) zeroC : Tower.Tm 2) := by
    refine ConstructorSystem.Normal.app oneArgument (constNormal _) (fun body h => by cases h) ?_
    intro target step
    obtain ⟨name, head, -, -⟩ := root step
    have computed : ConstructorSystem.spineHead
        (.app (.app (.const twistName) (.var 1)) zeroC : Tower.Tm 2) = some (twistName, 2) := rfl
    rw [computed] at head
    simp only [Option.some.injEq, Prod.mk.injEq] at head
    obtain ⟨rfl, arity⟩ := head
    exact absurd arity (by decide)
  have inner : ConstructorSystem.Normal twistExt
      (.app (.var 1) (.app (.app (.const twistName) (.var 1)) zeroC) : Tower.Tm 2) :=
    ConstructorSystem.Normal.app (varNormal _) twoArguments (fun body h => by cases h)
      (fun step => (Definitions.devConstructors twist_devCheck twist_rules).no_root_of_spineHead step rfl)
  have outer : ConstructorSystem.Normal twistExt
      (.app (.app (.var 1) (.app (.app (.const twistName) (.var 1)) zeroC)) (.var 0) : Tower.Tm 2) :=
    ConstructorSystem.Normal.app inner (varNormal _) (fun body h => by cases h)
      (fun step => (Definitions.devConstructors twist_devCheck twist_rules).no_root_of_spineHead step rfl)
  intro target step
  have stuck : twistStuck = .app (.const TowerNumbersModel.succ)
      (.app (.app (.var 1) (.app (.app (.const twistName) (.var 1)) zeroC)) (.var 0)) := rfl
  rw [stuck] at step
  cases step with
  | root h =>
      obtain ⟨name, head, -, defined⟩ := root h
      have head' : (some (TowerNumbersModel.succ, 1) : Option (DeclName × Nat)) =
          some (name, Definitions.devArity twistDev name) := head
      simp only [Option.some.injEq, Prod.mk.injEq] at head'
      obtain ⟨rfl, -⟩ := head'
      rw [Definitions.succ_not_defined twist_devCheck] at defined
      cases defined
  | congAppFun inner => exact constNormal _ inner
  | congAppArg inner => exact outer inner

/-- It mentions the declared constant. -/
theorem twistStuck_new : ¬ OldTerm twistDev twistStuck :=
  fun old => (old (twistName, twistDef) (List.mem_cons_self ..)).2.1.2.1.1 rfl

/-- The compiled call `twist h 1 m` does not mention it. -/
theorem twistCompiled_old : OldTerm twistDev
    (subst twistOpen (expand (reading [(twistName, twistTerm)]) (genericCall twistName 1 1))) := by
  intro e member
  simp only [twistDev, List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  exact Definitions.constFreeB_sound (by decide +kernel)

/-- **Agreement by conversion fails at a full call**: with variables for `h` and `m`, the call
`twist h 1 m` of the declared constant and the same call of the compiled term are not convertible in
the extended package. -/
theorem twist_not_agree :
    ¬ Conv twistExt.headEq (subst twistOpen (genericCall twistName 1 1))
      (subst twistOpen (expand (reading [(twistName, twistTerm)]) (genericCall twistName 1 1)))
      twistExt.computation := by
  intro conversion
  have toStuck : Conv twistExt.headEq (subst twistOpen (genericCall twistName 1 1)) twistStuck
      twistExt.computation := conv_of_stepStar (Definitions.devNormalize_sound twistOpen_runs)
  exact Definitions.normal_not_conv_old twist_devCheck twist_rules twistStuck_normal twistStuck_new
    twistCompiled_old (.trans _ _ _ (.symm _ _ toStuck) conversion)

/-- **`twist` is not in the class of `rows_reach`**, at its own call index (one parameter before, one
after), whatever the right sides: the class gives agreement at every instance with a numeral at the call
index, and that fails. -/
theorem twist_not_recursive : ¬ ∃ (r0 : Tower.Tm (1 + 1)) (r1 : Tower.Tm (1 + 1 + 1)),
    Recursive twistRows (reading [(twistName, twistTerm)]) twistName 1 1 r0 r1 := by
  rintro ⟨r0, r1, recursive⟩
  exact twist_not_agree (recursive.agrees (dev := twistDev) 1 twistOpen rfl)

/-- **Of the conditions of the class, saturation alone fails for `twist`.** Its two rules are in the
table in the form the class asks for; both, read at the compiled term, join; the row at `zero` does not
mention the constant; and the row at `succ k` is saturated at no budget. -/
theorem twist_control :
    ((⟨1 + 1, (subst (Definitions.atZero 1 1) (genericCall twistName 1 1), .var 0)⟩ :
        Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ twistRows) ∧
      ((⟨1 + 1 + 1, (subst (Definitions.atSucc 1 1) (genericCall twistName 1 1),
          succC (.app (.app (.var 2) (spine (.const twistName) [.var 2, .var 1])) (.var 0)))⟩ :
        Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ twistRows) ∧
      (∃ fuel, Definitions.joins fuel
        (expand (reading [(twistName, twistTerm)])
          (subst (Definitions.atZero 1 1) (genericCall twistName 1 1)))
        (expand (reading [(twistName, twistTerm)]) (.var 0 : Tower.Tm (1 + 1))) = true) ∧
      (∃ fuel, Definitions.joins fuel
        (expand (reading [(twistName, twistTerm)])
          (subst (Definitions.atSucc 1 1) (genericCall twistName 1 1)))
        (expand (reading [(twistName, twistTerm)])
          (succC (.app (.app (.var 2) (spine (.const twistName) [.var 2, .var 1])) (.var 0)) :
            Tower.Tm (1 + 1 + 1))) = true) ∧
      expand (reading [(twistName, twistTerm)]) (.var 0 : Tower.Tm (1 + 1)) = .var 0 ∧
      ¬ ∃ fuel, Definitions.saturated? twistName 1 1 fuel (Definitions.idx 1 1)
        (succC (.app (.app (.var 2) (spine (.const twistName) [.var 2, .var 1])) (.var 0)) :
          Tower.Tm (1 + 1 + 1)) = true := by
  have zeroRule : (⟨1 + 1, (subst (Definitions.atZero 1 1) (genericCall twistName 1 1), .var 0)⟩ :
      Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ twistRows := by decide +kernel
  have succRule : (⟨1 + 1 + 1, (subst (Definitions.atSucc 1 1) (genericCall twistName 1 1),
      succC (.app (.app (.var 2) (spine (.const twistName) [.var 2, .var 1])) (.var 0)))⟩ :
      Σ arity : Nat, Tower.Tm arity × Tower.Tm arity) ∈ twistRows := by decide +kernel
  have zeroReads : ∃ fuel, Definitions.joins fuel
      (expand (reading [(twistName, twistTerm)])
        (subst (Definitions.atZero 1 1) (genericCall twistName 1 1)))
      (expand (reading [(twistName, twistTerm)]) (.var 0 : Tower.Tm (1 + 1))) = true :=
    ⟨60, by decide +kernel⟩
  have succReads : ∃ fuel, Definitions.joins fuel
      (expand (reading [(twistName, twistTerm)])
        (subst (Definitions.atSucc 1 1) (genericCall twistName 1 1)))
      (expand (reading [(twistName, twistTerm)])
        (succC (.app (.app (.var 2) (spine (.const twistName) [.var 2, .var 1])) (.var 0)) :
          Tower.Tm (1 + 1 + 1))) = true :=
    ⟨60, by decide +kernel⟩
  refine ⟨zeroRule, succRule, zeroReads, succReads, rfl, ?_⟩
  intro saturated
  exact twist_not_recursive ⟨_, _,
    { zeroRule := zeroRule
      succRule := succRule
      others := fun d ne => Definitions.reading_single_other twistTerm ne
      notZero := by decide
      notSucc := by decide
      zeroReads := zeroReads
      succReads := succReads
      zeroFree := rfl
      saturated := saturated }⟩

/-! ## The ground calls that were run -/

/-- `λ f x. f x`. -/
def applyOnce : Tower.Tm 0 := .lam (.lam (.app (.var 1) (.var 0)))

/-- `λ f x. f (f x)`. -/
def applyTwice : Tower.Tm 0 := .lam (.lam (.app (.var 1) (.app (.var 1) (.var 0))))

/-- A call `twist h 2 1` that both runs take to one value: by rows it has exactly that answer, and the
compiled call answers it. -/
theorem twist_ground_at {h v : Tower.Tm 0} (value : Value v) {fuelRows fuelTerm : Nat}
    (rows : Definitions.devNormalize twistDev twistRows fuelRows
      (spine (.const twistName) [h, two, one] : Tower.Tm 0) = some v)
    (term : Vectors.vecNormalize level1 fuelTerm (spine twistTerm [h, two, one]) = some v) :
    DirectedAnswer twistExt (spine (.const twistName) [h, two, one]) v ∧
      (∀ w, DirectedAnswer twistExt (spine (.const twistName) [h, two, one]) w → w = v) ∧
      DirectedAnswer pkg (spine twistTerm [h, two, one]) v := by
  have reached : DirectedAnswer twistExt (spine (.const twistName) [h, two, one]) v :=
    directedAnswer_of_answer (Definitions.devConstructors twist_devCheck twist_rules)
      ⟨Definitions.devNormalize_sound rows, value.normal_dev twist_devCheck twist_rules⟩ value.headFree
  exact ⟨reached,
    fun w other => DirectedAnswer.unique (Definitions.devConstructors twist_devCheck twist_rules) other reached,
    directedAnswer_of_answer (Vectors.vectorConstructors level1)
      ⟨Vectors.vecNormalize_sound level1 term, value.normal⟩ value.headFree⟩

/-- **The ground calls that were run agree.** `twist (λ f x. f x) 2 1` by rows has exactly one answer,
`3`, the answer of the compiled call; `twist (λ f x. f (f x)) 2 1` has exactly one, `4`, likewise. -/
theorem twist_ground :
    (DirectedAnswer twistExt (spine (.const twistName) [applyOnce, two, one]) three ∧
      (∀ w, DirectedAnswer twistExt (spine (.const twistName) [applyOnce, two, one]) w → w = three) ∧
      DirectedAnswer pkg (spine twistTerm [applyOnce, two, one]) three) ∧
    (DirectedAnswer twistExt (spine (.const twistName) [applyTwice, two, one]) (nat 4) ∧
      (∀ w, DirectedAnswer twistExt (spine (.const twistName) [applyTwice, two, one]) w → w = nat 4) ∧
      DirectedAnswer pkg (spine twistTerm [applyTwice, two, one]) (nat 4)) :=
  ⟨twist_ground_at (fuelRows := 80) (fuelTerm := 200) (nat_value 3) (by decide +kernel) (by decide +kernel),
    twist_ground_at (fuelRows := 200) (fuelTerm := 200) (nat_value 4) (by decide +kernel)
      (by decide +kernel)⟩

/-! ## The contrast: a later argument changed, the call saturated -/

/-- The constant of the accumulating sum `Definitions.accDef`. -/
def accName : DeclName := .mkSimple "sumAcc-by-rows"

/-- The development of the accumulating sum alone. -/
abbrev accDev : Development := [(accName, Definitions.accDef)]

/-- Its rules: `sumAcc zero acc ⟶ acc` and `sumAcc (succ k) acc ⟶ sumAcc k (succ acc)`. The recursive
call has both its arguments, the later one changed. -/
abbrev accRows : SchemaTable Tower.Head :=
  [⟨1, (spine (.const accName) [zeroC, .var 0], .var 0)⟩,
    ⟨2, (spine (.const accName) [succC (.var 1), .var 0],
      spine (.const accName) [.var 1, succC (.var 0)])⟩]

/-- The package extended by the accumulating sum by rows. -/
abbrev accExt : Rules Tower.Head := devPackage accDev accRows

theorem acc_devCheck : devCheck accDev = true := by decide +kernel

theorem acc_fresh : Definitions.devFresh accDev = true := by decide +kernel

theorem acc_rules : devRules accDev = some accRows := by decide +kernel

/-- **The accumulating sum is in the class**: one later parameter, no earlier one; its recursive call
is saturated, with the later argument changed. -/
theorem acc_rowsReach :
    ∃ c : Tower.Tm 0, Checked Definitions.accDef 0 c ∧ RowsReach Definitions.accDef c accName accRows 1 0 := by
  obtain ⟨c, checked⟩ := Definitions.qualify_closed Definitions.acc_verdict
  have zeroReads : ((Definitions.compile 0 Definitions.accDef).map fun c => Definitions.joins 40
      (expand (reading [(accName, c)]) (subst (Definitions.atZero 1 0) (genericCall accName 1 0)))
      (expand (reading [(accName, c)]) (.var 0 : Tower.Tm (1 + 0)))) = some true := by decide +kernel
  have succReads : ((Definitions.compile 0 Definitions.accDef).map fun c => Definitions.joins 40
      (expand (reading [(accName, c)]) (subst (Definitions.atSucc 1 0) (genericCall accName 1 0)))
      (expand (reading [(accName, c)])
        (spine (.const accName) [.var 1, succC (.var 0)] : Tower.Tm (1 + 1 + 0)))) = some true := by
    decide +kernel
  rw [checked.compiled] at zeroReads succReads
  exact ⟨c, checked, rfl, fun _ _ args => args _, _, _,
    { zeroRule := by decide +kernel
      succRule := by decide +kernel
      others := fun d ne => Definitions.reading_single_other c ne
      notZero := by decide
      notSucc := by decide
      zeroReads := ⟨40, Option.some.inj zeroReads⟩
      succReads := ⟨40, Option.some.inj succReads⟩
      zeroFree := rfl
      saturated := ⟨8, by decide +kernel⟩ }⟩

/-- **Every ground call of the declared constant of the accumulating sum has exactly one answer in the
extension, the one answer of the compiled call, a value of the numbers**: at arguments convertible in
the extension with closed numbers of the package. -/
theorem acc_rows_answer {σ τ : Sub Tower.Head 2 0}
    (args : SubstMor pkg Definitions.accDef.telescope .nil τ)
    (same : ∀ x, Conv accExt.headEq (σ x) (τ x) accExt.computation) :
    ∃ c : Tower.Tm 0, Checked Definitions.accDef 0 c ∧ ∃ v, Value v ∧ Typed pkg .nil v numC ∧
      DirectedAnswer pkg (applyClosed Definitions.accDef.telescope τ c) v ∧
      DirectedAnswer accExt (applyClosed Definitions.accDef.telescope σ (.const accName)) v ∧
      (∀ w, DirectedAnswer pkg (applyClosed Definitions.accDef.telescope τ c) w → w = v) ∧
      ∀ w, DirectedAnswer accExt (applyClosed Definitions.accDef.telescope σ (.const accName)) w → w = v := by
  obtain ⟨c, checked, reach⟩ := acc_rowsReach
  exact ⟨c, checked, rows_reach acc_devCheck acc_rules checked reach args same .num⟩

end NativeTypesOnTheStep.Computing.DirectedAnswers

section Audit
open NativeTypesOnTheStep.Computing.DirectedAnswers
#print axioms twist_verdict
#print axioms twist_compiles
#print axioms twist_checked
#print axioms twist_devCheck
#print axioms twist_rules
#print axioms twist_read
#print axioms twist_sound
#print axioms twistOpen_runs
#print axioms twistStuck_normal
#print axioms twist_not_agree
#print axioms twist_not_recursive
#print axioms twist_control
#print axioms twist_ground
#print axioms acc_rowsReach
#print axioms acc_rows_answer
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
