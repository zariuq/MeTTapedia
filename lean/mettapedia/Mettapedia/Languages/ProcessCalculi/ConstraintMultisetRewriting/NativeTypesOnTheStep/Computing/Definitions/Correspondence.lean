import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Acceptance

/-!
# Rows typed after their match, and the eliminator's methods: where the correspondence holds and breaks

**The observation tested.** A row typed after its match looks like an eliminator's method: the frame
after the match is the method's context, the declared type at what the match teaches is the motive at
the constructor. If that were exact, the row checker's admission would give the compiled function's
typing.

**Where it holds**, on every definition of the table and here: each definition the row checker admits
and the compiler accepts is certified typed in its compiled form, including

* **an accumulating parameter** (`accDef`): `sumAcc zero acc = acc`, `sumAcc (succ k) acc = sumAcc k
  (succ acc)`. The motive abstracts every parameter after the call index, so the recursive call may
  change them (`acc_verdict`);
* **a large elimination into the small universe** (`smallDef`): `small zero = num`,
  `small (succ k) = num → small k`, at `Π (n : num). U0` (`small_verdict`);
* **a result at a pair type** (`dupDef`): `dup n = pair n n`, at `Π (n : num). num × num`, one row with
  no call index (`dup_verdict`).

**Where it breaks.** The package's recursor of the numbers eliminates into level one. A definition
whose declared result lives above it, `big : Π (n : num). U1` with `big zero = U0` and
`big (succ k) = U0`, is admitted by the row checker (`big_rows_admitted`), is in the class
(`big_compiles`), and its compiled term is not certified, at budget 16 nor at 64 (`big_verdict`). The
motive `λ n. U1` is a family of types of level two, and the recursor's motive is a family of level-one
types. That the compiled term is not typed at all is not proved here; that the row checker's admission
does not give a certificate for it is. With the result type at the recursor's level, the
correspondence is a conjecture, tested on every definition here, not proved: its proof needs call
abstraction for the declarative typing with the function a variable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerVectorsModel (U0 numC zeroC succC ttC vecC)
open Vectors.Checker (Pattern Row Definition)

/-! ## An accumulating parameter -/

/-- `sumAcc zero acc = acc`. -/
def accZeroRow : Row := ⟨[.zero, .var], 1, .var 0⟩

/-- `sumAcc (succ k) acc = sumAcc k (succ acc)`. -/
def accSuccRow : Row := ⟨[.succ .var, .var], 2, .app (.app (.var 2) (.var 1)) (succC (.var 0))⟩

/-- **An accumulating parameter**: `sumAcc : Π (n acc : num). num`. -/
def accDef : Definition := ⟨"sumAcc", 2, .snoc (.snoc .nil numC) numC, numC, [accZeroRow, accSuccRow]⟩

theorem acc_verdict : qualify 16 accDef = .function true := by decide +kernel

/-! ## A large elimination into the small universe -/

/-- `small zero = num`. -/
def smallZeroRow : Row := ⟨[.zero], 0, numC⟩

/-- `small (succ k) = num → small k`. -/
def smallSuccRow : Row := ⟨[.succ .var], 1, .pi numC (.app (.var 2) (.var 1))⟩

/-- **A family of small types by rows**: `small : Π (n : num). U0`. -/
def smallDef : Definition := ⟨"small", 1, .snoc .nil numC, U0, [smallZeroRow, smallSuccRow]⟩

theorem small_verdict : qualify 16 smallDef = .function true := by decide +kernel

/-! ## A result at a pair type -/

/-- `dup n = pair n n`; the function is variable 1. -/
def dupRow : Row := ⟨[.var], 1, .pair (.var 0) (.var 0)⟩

/-- **A definition whose result type is a pair**: `dup : Π (n : num). num × num`. -/
def dupDef : Definition := ⟨"dup", 1, .snoc .nil numC, .sigma numC numC, [dupRow]⟩

theorem dup_verdict : qualify 16 dupDef = .function true := by decide +kernel

/-! ## Above the recursor's level -/

/-- The universe of level one. -/
abbrev U1 {n : Nat} : Tower.Tm n := .head (.sort (.succ (.const 0)))

/-- `big zero = U0`. -/
def bigZeroRow : Row := ⟨[.zero], 0, U0⟩

/-- `big (succ k) = U0`. -/
def bigSuccRow : Row := ⟨[.succ .var], 1, U0⟩

/-- **A family of level-one types by rows**: `big : Π (n : num). U1`. -/
def bigDef : Definition := ⟨"big", 1, .snoc .nil numC, U1, [bigZeroRow, bigSuccRow]⟩

/-- Its rows are admitted. -/
theorem big_rows_admitted : Vectors.Checker.checkDefinition 16 bigDef = .admitted := by decide +kernel

/-- It is in the class: `λ n. num-rec (λ _. U1) U0 (λ k ih. U0) n`. -/
theorem big_compiles :
    compile 0 bigDef = some (.lam (Vectors.numRecAt (.lam U1) U0 (.lam (.lam U0)) (.var 0))) := by
  decide +kernel

/-- **Its compiled term is not certified**, at budget 16 as at 64: the verdict is not decided. -/
theorem big_verdict : qualify 16 bigDef = .undecided .typing ∧
    (typed? 64 .nil (.lam (Vectors.numRecAt (.lam U1) U0 (.lam (.lam U0)) (.var 0)) : Tower.Tm 0)
      (liftClosed bigDef.type)).isSome = false := by
  decide +kernel

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.acc_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.small_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.dup_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.big_rows_admitted
#print axioms NativeTypesOnTheStep.Computing.Definitions.big_compiles
#print axioms NativeTypesOnTheStep.Computing.Definitions.big_verdict

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
