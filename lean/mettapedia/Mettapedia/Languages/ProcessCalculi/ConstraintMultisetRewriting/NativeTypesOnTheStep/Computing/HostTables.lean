import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.TwoReadings

/-!
# Host operations in types: when a host table may enter conversion

A host operation (a grounded `+` or `-`) is a table of ground equations: `op a b` answers `c` for
ground values `a`, `b`, `c` (`hostComputation`). Read definitionally, the table joins conversion.

**The condition: total and deterministic on ground values.**

* A **functional** table (one answer per ground call) is root-deterministic (`host_rootDeterministic`)
  and its rows form a **constructor system** (`hostConstructors`): ground left sides built from
  constructors, so it is Church–Rosser (`host_churchRosser`). Each ground call then has at most one
  answer (`host_answer_unique`).
* A **total** functional table gives every ground call exactly one answer, a value
  (`host_answer`): termination is immediate, since a row replaces the call by a value.
* A table with **two answers** for one call is not root-deterministic and identifies the two values in
  the typed equality (`host_identifies`), which the rigid package refutes.
* A **partial** table leaves calls without a row: such a call is stuck, a closed normal term of the
  value type that is no value (`host_stuck`). Partial subtraction at `0 - 1` is the smallest one
  (`partialSub_stuck`); truncated subtraction is total (`natSub_answer`).

**A host operation inside a pattern is outside the class.** A left side that matches on
`op x (succ 0)`, as a declared argument type `(VecN $t (+ $x 1))` does, contains a defined symbol at a
pattern position, so it is no constructor pattern (`host_call_not_pattern`): matching it would have
to invert the table, which conversion never does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.HostTables

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (System LeftSide Pattern ConstructorPresentation)
open ProgrammingOnTheStep.VectorPackage

/-- A host table for a binary operation on ground numerals: `table a b c` when the host may answer `c`
for the call on `a` and `b`. -/
abbrev HostTable := Nat → Nat → Nat → Prop

/-- The table answers at most once per call. -/
def Functional (table : HostTable) : Prop := ∀ a b c c', table a b c → table a b c' → c = c'

/-- The table answers every call. -/
def Total (table : HostTable) : Prop := ∀ a b, ∃ c, table a b c

/-- The host call `op a b` on numerals. -/
abbrev hostCall {n : Nat} (op : DeclName) (a b : Nat) : Tower.Tm n :=
  .app (.app (.const op) (numeral a)) (numeral b)

theorem rename_numeral {n m : Nat} (ρ : Ren n m) (k : Nat) :
    Presentation.rename ρ (numeral k : Tower.Tm n) = numeral k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show Tm.app (.const succN) (Presentation.rename ρ (numeral k)) = Tm.app (.const succN) (numeral k)
      rw [ih]

theorem subst_numeral {n m : Nat} (σ : Sub Tower.Head n m) (k : Nat) :
    Presentation.subst σ (numeral k : Tower.Tm n) = numeral k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show Tm.app (.const succN) (Presentation.subst σ (numeral k)) = Tm.app (.const succN) (numeral k)
      rw [ih]

theorem numeral_injective {n : Nat} : ∀ {a a' : Nat}, (numeral a : Tower.Tm n) = numeral a' → a = a'
  | 0, 0, _ => rfl
  | 0, _ + 1, same => by cases same
  | _ + 1, 0, same => by cases same
  | a + 1, a' + 1, same => by
      have inner : (numeral a : Tower.Tm n) = numeral a' := (Tm.app.inj same).2
      rw [numeral_injective inner]

/-- **The rows of a host table, as a root computation on the operation `op`.** -/
def hostComputation (op : DeclName) (table : HostTable) : RootComputation Tower.Head where
  step {n} l r := ∃ a b c, table a b c ∧ l = (hostCall op a b : Tower.Tm n) ∧ r = numeral c
  rename := by
    intro n m ρ l r step
    obtain ⟨a, b, c, row, rfl, rfl⟩ := step
    refine ⟨a, b, c, row, ?_, rename_numeral ρ c⟩
    show Tm.app (.app (.const op) (Presentation.rename ρ (numeral a))) (Presentation.rename ρ (numeral b)) =
      hostCall op a b
    rw [rename_numeral, rename_numeral]
  substitute := by
    intro n m σ l r step
    obtain ⟨a, b, c, row, rfl, rfl⟩ := step
    refine ⟨a, b, c, row, ?_, subst_numeral σ c⟩
    show Tm.app (.app (.const op) (Presentation.subst σ (numeral a))) (Presentation.subst σ (numeral b)) =
      hostCall op a b
    rw [subst_numeral, subst_numeral]

/-- **A functional table is root-deterministic.** -/
theorem host_rootDeterministic {op : DeclName} {table : HostTable} (functional : Functional table) :
    RootDeterministic (hostComputation op table) := by
  intro n l r r' step step'
  obtain ⟨a, b, c, row, rfl, rfl⟩ := step
  obtain ⟨a', b', c', row', same, rfl⟩ := step'
  obtain ⟨function, second⟩ := Tm.app.inj same
  obtain ⟨-, first⟩ := Tm.app.inj function
  obtain rfl := numeral_injective first
  obtain rfl := numeral_injective second
  rw [functional a b c c' row row']

/-! ## Functional tables are constructor systems -/

section Constructors

variable (op : DeclName) (table : HostTable)

/-- The rows, as ground equations. -/
inductive HostSchema : {arity : Nat} → Tower.Tm arity → Tower.Tm arity → Prop
  | row {a b c : Nat} : table a b c → HostSchema (arity := 0) (hostCall op a b) (numeral c)

def hostPresentation : SchemaPresentation (declare rules (hostComputation op table)) where
  schema := HostSchema op table
  sound := by
    intro arity ambient left right rule σ
    cases rule with
    | row row =>
        refine Or.inr ⟨_, _, _, row, ?_, subst_numeral σ _⟩
        show Tm.app (.app (.const op) (Presentation.subst σ (numeral _)))
          (Presentation.subst σ (numeral _)) = hostCall op _ _
        rw [subst_numeral, subst_numeral]
  cover := by
    intro n source target step
    rcases step with impossible | ⟨a, b, c, row, rfl, rfl⟩
    · exact impossible.elim
    · refine ⟨0, _, _, Fin.elim0, .row row, ?_, subst_numeral Fin.elim0 c⟩
      show Tm.app (.app (.const op) (Presentation.subst Fin.elim0 (numeral a)))
        (Presentation.subst Fin.elim0 (numeral b)) = hostCall op a b
      rw [subst_numeral, subst_numeral]

/-- Numerals are constructor patterns when `zero` and `succ` are not defined. -/
theorem numeral_pattern {defined : DeclName → Prop} (zeroFree : ¬ defined zeroN)
    (succFree : ¬ defined succN) {m : Nat} {flag : Bool} :
    ∀ k : Nat, Pattern defined flag (numeral k : Tower.Tm m)
  | 0 => .const zeroFree
  | k + 1 => .app (.const succFree) (numeral_pattern zeroFree succFree k)

variable {op table}

/-- **A functional table is a constructor system**, when its operation is not a constructor. -/
def hostSystem (functional : Functional table) (fresh : op ≠ zeroN ∧ op ≠ succN) :
    System Tower.Head where
  schema := HostSchema op table
  defined name := name = op
  arity _ := 2
  left := by
    intro m left right rule
    refine ⟨op, rfl, by decide, ?_⟩
    cases rule with
    | row _ =>
        exact .app (.app (.const op)
          (numeral_pattern (fun same => fresh.1 same.symm) (fun same => fresh.2 same.symm) _))
          (numeral_pattern (fun same => fresh.1 same.symm) (fun same => fresh.2 same.symm) _)
  linear := by
    intro arity left right rule
    cases rule with
    | row _ => exact fun index => index.elim0
  covered := by
    intro m left right rule
    cases rule with
    | row _ => exact fun index => index.elim0
  determined := by
    intro m m' n n' left right left' right' rule rule' σ σ' same develop
    cases rule with
    | row row =>
        cases rule' with
        | row row' =>
            have same' : Tm.app (.app (.const op) (Presentation.subst σ (numeral _)))
                (Presentation.subst σ (numeral _)) =
              Tm.app (.app (.const op) (Presentation.subst σ' (numeral _)))
                (Presentation.subst σ' (numeral _)) := same
            rw [subst_numeral, subst_numeral, subst_numeral, subst_numeral] at same'
            obtain ⟨function, second⟩ := Tm.app.inj same'
            obtain ⟨-, first⟩ := Tm.app.inj function
            obtain rfl := numeral_injective first
            obtain rfl := numeral_injective second
            rw [functional _ _ _ _ row row', subst_numeral, subst_numeral]

/-- Head equality of the vector package is symmetric. -/
theorem headEq_symm {h h' : Tower.Head} (same : rules.headEq h h') : rules.headEq h' h :=
  Interface.DependentFull.Controls.setting.levels.headEq_symm same

def hostConstructors (functional : Functional table) (fresh : op ≠ zeroN ∧ op ≠ succN) :
    ConstructorPresentation (declare rules (hostComputation op table)) where
  presentation := hostPresentation op table
  system := hostSystem functional fresh
  same _ _ := Iff.rfl
  symmetric := ⟨fun _ _ same => headEq_symm same⟩

/-- **A functional host table is Church–Rosser.** -/
theorem host_churchRosser (functional : Functional table) (fresh : op ≠ zeroN ∧ op ≠ succN) :
    ChurchRosser (declare rules (hostComputation op table)) :=
  (hostConstructors functional fresh).churchRosser

/-- Numerals are normal under a host table. -/
theorem numeral_normal_host {n : Nat} (k : Nat) :
    ConstructorSystem.Normal (declare rules (hostComputation op table)) (numeral k : Tower.Tm n) := by
  induction k with
  | zero =>
      intro t h
      cases h with
      | root h =>
          rcases h with h | ⟨a, b, c, row, same, rfl⟩
          · exact h.elim
          · cases same
  | succ k ih =>
      intro t h
      cases h with
      | root h =>
          rcases h with h | ⟨a, b, c, row, same, rfl⟩
          · exact h.elim
          · obtain ⟨function, -⟩ := Tm.app.inj same
            cases function
      | congAppFun h =>
          cases h with
          | root h =>
              rcases h with h | ⟨a, b, c, row, same, rfl⟩
              · exact h.elim
              · cases same
      | congAppArg h => exact ih h

/-- **Each ground call of a functional table has at most one answer.** -/
theorem host_answer_unique (functional : Functional table) (fresh : op ≠ zeroN ∧ op ≠ succN)
    {n : Nat} {t v v' : Tower.Tm n} (answer : Answer (declare rules (hostComputation op table)) t v)
    (answer' : Answer (declare rules (hostComputation op table)) t v') : v = v' :=
  answer_unique (host_churchRosser functional fresh) answer answer'

/-- **A total table answers every ground call with a value.** -/
theorem host_answer (total : Total table) {n : Nat} (a b : Nat) :
    ∃ c, table a b c ∧
      Answer (declare rules (hostComputation op table)) (hostCall op a b : Tower.Tm n) (numeral c) := by
  obtain ⟨c, row⟩ := total a b
  exact ⟨c, row, .single (.root (Or.inr ⟨a, b, c, row, rfl, rfl⟩)), numeral_normal_host c⟩

end Constructors

/-! ## Two answers, no answer -/

section Failures

/-- **A table with two answers for one call is not root-deterministic.** -/
theorem host_not_rootDeterministic {op : DeclName} {table : HostTable} {a b c c' : Nat}
    (row : table a b c) (row' : table a b c') (different : c ≠ c') :
    ¬ RootDeterministic (hostComputation op table) := by
  intro deterministic
  have same := deterministic (hostCall op a b : Tower.Tm 0) (numeral c) (numeral c')
    ⟨a, b, c, row, rfl, rfl⟩ ⟨a, b, c', row', rfl, rfl⟩
  exact different (numeral_injective same)

theorem numeral_typed {n : Nat} (Γ : Tower.Ctx n) (k : Nat) : Typed rules Γ (numeral k) natC := by
  induction k with
  | zero => exact zero_typed _
  | succ k ih => exact succ_typed ih

/-- **... and identifies the two values** in the typed equality of the package that declares the
operation `add : nat → nat → nat` with that table. -/
theorem host_identifies {table : HostTable} {a b c c' : Nat} (row : table a b c) (row' : table a b c') :
    Equal (declare rules (hostComputation addN table)) .nil (numeral c) (numeral c') natC := by
  have call : Typed (declare rules (hostComputation addN table)) .nil (hostCall addN a b) natC :=
    typed_declare _ (add_typed (numeral_typed _ a) (numeral_typed _ b))
  exact .trans (.symm (.root (declare_step ⟨a, b, c, row, rfl, rfl⟩) call
      (typed_declare _ (numeral_typed _ c))))
    (.root (declare_step ⟨a, b, c', row', rfl, rfl⟩) call (typed_declare _ (numeral_typed _ c')))

/-- **A call with no row is stuck**: normal, and no numeral. -/
theorem host_stuck {op : DeclName} {table : HostTable} {a b : Nat} (noRow : ∀ c, ¬ table a b c) :
    Answer (declare rules (hostComputation op table)) (hostCall op a b : Tower.Tm 0) (hostCall op a b) ∧
      ∀ k, hostCall op a b ≠ (numeral k : Tower.Tm 0) := by
  refine ⟨⟨.refl, ?_⟩, ?_⟩
  · intro t h
    cases h with
    | root h =>
        rcases h with h | ⟨a', b', c, row, same, rfl⟩
        · exact h.elim
        · obtain ⟨function, second⟩ := Tm.app.inj same
          obtain ⟨-, first⟩ := Tm.app.inj function
          obtain rfl := numeral_injective first
          obtain rfl := numeral_injective second
          exact noRow c row
    | congAppFun h =>
        cases h with
        | root h =>
            rcases h with h | ⟨a', b', c, row, same, rfl⟩
            · exact h.elim
            · cases same
        | congAppFun h =>
            cases h with
            | root h =>
                rcases h with h | ⟨a', b', c, row, same, rfl⟩
                · exact h.elim
                · cases same
        | congAppArg h => exact numeral_normal_host a h
    | congAppArg h => exact numeral_normal_host b h
  · intro k same
    cases k with
    | zero => cases same
    | succ k =>
        obtain ⟨function, -⟩ := Tm.app.inj same
        cases function

/-! ## Instances -/

/-- Truncated subtraction: total and functional. -/
def natSub : HostTable := fun a b c => c = a - b

/-- Partial subtraction: `a - b` only when `b ≤ a`. -/
def partialSub : HostTable := fun a b c => a = b + c

/-- A table with two answers: either argument. -/
def eitherArg : HostTable := fun a b c => c = a ∨ c = b

theorem natSub_functional : Functional natSub := fun _ _ _ _ first second => first.trans second.symm

theorem natSub_total : Total natSub := fun a b => ⟨a - b, rfl⟩

theorem partialSub_functional : Functional partialSub := fun _ b _ _ first second => by
  unfold partialSub at first second
  omega

/-- **Truncated subtraction answers `0 - 1` with `0`**, uniquely. -/
theorem natSub_answer :
    Answer (declare rules (hostComputation addN natSub)) (hostCall addN 0 1 : Tower.Tm 0) (numeral 0) ∧
      ∀ v, Answer (declare rules (hostComputation addN natSub)) (hostCall addN 0 1 : Tower.Tm 0) v →
        v = numeral 0 := by
  obtain ⟨c, row, answer⟩ := host_answer (op := addN) natSub_total (n := 0) 0 1
  have zero : c = 0 := row
  subst zero
  exact ⟨answer, fun v answer' => host_answer_unique natSub_functional (by decide) answer' answer⟩

/-- **Partial subtraction is stuck at `0 - 1`.** -/
theorem partialSub_stuck :
    Answer (declare rules (hostComputation addN partialSub)) (hostCall addN 0 1 : Tower.Tm 0)
        (hostCall addN 0 1) ∧
      ∀ k, hostCall addN 0 1 ≠ (numeral k : Tower.Tm 0) :=
  host_stuck fun c row => by
    unfold partialSub at row
    omega

/-- **The two-valued table identifies `0` and `1`**, which the rigid package refutes. -/
theorem eitherArg_identifies :
    ¬ RootDeterministic (hostComputation addN eitherArg) ∧
      Equal (declare rules (hostComputation addN eitherArg)) .nil (numeral 0) (numeral 1) natC ∧
      ¬ (frames levels).Solvable VectorAppend.rigidOneZero :=
  ⟨host_not_rootDeterministic (a := 0) (b := 1) (Or.inl rfl) (Or.inr rfl) (by decide),
    host_identifies (a := 0) (b := 1) (Or.inl rfl) (Or.inr rfl),
    VectorAppend.rigid_one_zero_unsolvable⟩

/-- **A host call inside a pattern is no constructor pattern**: `op x (succ 0)` has the defined
operation at a pattern position. -/
theorem host_call_not_pattern {defined : DeclName → Prop} {op : DeclName} (isDefined : defined op)
    {m : Nat} {flag : Bool} (x : Tower.Tm m) :
    ¬ Pattern defined flag (.app (.app (.const op) x) (numeral 1)) := by
  intro pattern
  cases pattern with
  | app function _ =>
      cases function with
      | app function' _ =>
          cases function' with
          | const notDefined => exact notDefined isDefined

end Failures

end NativeTypesOnTheStep.Computing.HostTables

#print axioms NativeTypesOnTheStep.Computing.HostTables.rename_numeral
#print axioms NativeTypesOnTheStep.Computing.HostTables.subst_numeral
#print axioms NativeTypesOnTheStep.Computing.HostTables.numeral_injective
#print axioms NativeTypesOnTheStep.Computing.HostTables.hostComputation
#print axioms NativeTypesOnTheStep.Computing.HostTables.host_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.HostTables.hostPresentation
#print axioms NativeTypesOnTheStep.Computing.HostTables.hostSystem
#print axioms NativeTypesOnTheStep.Computing.HostTables.hostConstructors
#print axioms NativeTypesOnTheStep.Computing.HostTables.host_churchRosser
#print axioms NativeTypesOnTheStep.Computing.HostTables.numeral_normal_host
#print axioms NativeTypesOnTheStep.Computing.HostTables.host_answer_unique
#print axioms NativeTypesOnTheStep.Computing.HostTables.host_answer
#print axioms NativeTypesOnTheStep.Computing.HostTables.host_not_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.HostTables.host_identifies
#print axioms NativeTypesOnTheStep.Computing.HostTables.host_stuck
#print axioms NativeTypesOnTheStep.Computing.HostTables.natSub_answer
#print axioms NativeTypesOnTheStep.Computing.HostTables.partialSub_stuck
#print axioms NativeTypesOnTheStep.Computing.HostTables.eitherArg_identifies
#print axioms NativeTypesOnTheStep.Computing.HostTables.host_call_not_pattern

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
