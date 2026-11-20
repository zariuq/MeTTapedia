import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Verdict

/-!
# A development: definitions by rows, each used by the next

In the checker's source form, over the vectors package:

* **addition by rows** (`addDef`): `add : Π (n m : num). num`, `add zero m = m`,
  `add (succ k) m = succ (add k m)`. It compiles to `addTerm`
  `λ n. num-rec (λ n. num → num) (λ m. m) (λ k ih m. succ (ih m)) n` (`add_compiles`), exported as
  `addExport` (`add_exported`);
* **append on that addition** (`appendRDef`): `append : Π (A : U0) (n m : num). vec A n → vec A m →
  vec A (add n m)` with the declared type written with `addExport`, and the rows of the checker's
  `append` (`nil` answering `ys`, `cons a v` answering `pair a (append A k m v ys)`). It compiles to
  `appendRTerm` (`appendR_compiles`), exported as `appendRExport`;
* **over that append** (`doubleDef`, `concatDef`), two definitions that use `append` only through its
  declared type, so they take it as their first parameter `app` (the type of `append` above):
  `double app A n xs = app A n n xs xs` at `vec A (add n n)`, and
  `concat3 app A n m l xs ys zs = app A (add n m) l (app A n m xs ys) zs` at
  `vec A (add (add n m) l)`, both with the exported addition in their types. They compile to
  `doubleTerm` and `concatTerm` (`double_compiles`, `concat_compiles`); the functions on the append
  above are their applications to `appendRTerm`. Written instead with the exported append inlined, the
  row checker re-checks `append`'s compiled body at each use, and one kernel evaluation of that check
  exceeded the memory the gate allows;
* **map with a function argument** (`mapDef`): `map : Π (A B : U0) (g : A → B) (n : num). vec A n →
  vec B n`, `map A B g n nil = nil`, `map A B g n (cons a v) = pair (g a) (map A B g k v)`.

**Controls**, each the smallest witness of one condition of the class:
* `overlapDef`: two rows for `zero`, `add zero m = m` and `add zero m = zero`;
* `loopDef`: a recursive call not on the predecessor, `loop (succ k) m = loop (succ k) m`;
* `selfDef`: a declared type that mentions the vector matched by `nil`, where the naive compilation of
  the `nil` row is not typed (`self : Π A n (xs : vec A n). Id (vec A n) xs xs`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerVectorsModel (U0 numC zeroC succC ttC vecC)
open Vectors (numRecAt)
open Vectors.Checker (Pattern Row Definition nilRow consRow)

/-! ## Addition by rows -/

/-- `add zero m = m`. -/
def addZeroRow : Row := ⟨[.zero, .var], 1, .var 0⟩

/-- `add (succ k) m = succ (add k m)`; the function is variable 2. -/
def addSuccRow : Row := ⟨[.succ .var, .var], 2, succC (.app (.app (.var 2) (.var 1)) (.var 0))⟩

/-- **Addition by rows.** -/
def addDef : Definition := ⟨"add", 2, .snoc (.snoc .nil numC) numC, numC, [addZeroRow, addSuccRow]⟩

/-- The compiled addition: `λ n. num-rec (λ n. num → num) (λ m. m) (λ k ih m. succ (ih m)) n`. -/
def addTerm : Tower.Tm 0 :=
  .lam (numRecAt (.lam (.pi numC numC)) (.lam (.var 0)) (.lam (.lam (.lam (succC (.app (.var 1) (.var 0))))))
    (.var 0))

theorem add_compiles : compile 0 addDef = some addTerm := by decide +kernel

/-- The exported addition: `num-rec (λ _. num → num → num) addTerm (λ k x. x) zero`. -/
def addExport : Tower.Tm 0 := numRecAt (.lam (.pi numC (.pi numC numC))) addTerm (.lam (.lam (.var 0))) zeroC

theorem add_exported : exported addDef.type addTerm = addExport := by decide +kernel

/-! ## Append on the addition by rows -/

/-- **Append**, its declared type written with the addition by rows. -/
def appendRDef : Definition :=
  ⟨"append", 5, TowerVectorsPrograms.appendCtx,
    vecC (.var 4) (spine (liftClosed addExport) [.var 3, .var 2]), [nilRow, consRow]⟩

/-- The compiled append: `λ A n. num-rec P (λ m xs ys. ys) (λ k ih m xs ys. pair (fst xs) (ih m (snd xs)
ys)) n`, `P = λ n. Π (m : num) (xs : vec A n) (ys : vec A m). vec A (add n m)`. -/
def appendRTerm : Tower.Tm 0 :=
  .lam (.lam (numRecAt
    (.lam (.pi numC (.pi (vecC (.var 3) (.var 1)) (.pi (vecC (.var 4) (.var 1))
      (vecC (.var 5) (spine (liftClosed addExport) [.var 3, .var 2]))))))
    (.lam (.lam (.lam (.var 0))))
    (.lam (.lam (.lam (.lam (.lam (.pair (.fst (.var 1))
      (.app (.app (.app (.var 3) (.var 2)) (.snd (.var 1))) (.var 0))))))))
    (.var 0)))

theorem appendR_compiles : compile 0 appendRDef = some appendRTerm := by decide +kernel

theorem appendR_covers : baseOf appendRDef = 0 := by decide +kernel

/-- The exported append. -/
def appendRExport : Tower.Tm 0 := exported appendRDef.type appendRTerm

/-! ## Over append: the earlier function as a parameter -/

/-- `app : (the type of append), A : U0, n : num, xs : vec A n`. -/
def doubleTelescope : Ctx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil appendRDef.type) U0) numC) (vecC (.var 1) (.var 0))

/-- `double app A n xs = app A n n xs xs`; `app` is variable 3, the function variable 4. -/
def doubleRow : Row := ⟨[.var, .var, .var, .var], 4, spine (.var 3) [.var 2, .var 1, .var 1, .var 0, .var 0]⟩

/-- **Doubling a vector, over append**: `Π (app : F_append) (A : U0) (n : num). vec A n → vec A (add n n)`. -/
def doubleDef : Definition :=
  ⟨"double", 4, doubleTelescope, vecC (.var 2) (spine (liftClosed addExport) [.var 1, .var 1]), [doubleRow]⟩

/-- The compiled doubling: the abstraction of its row. -/
def doubleTerm : Tower.Tm 0 := .lam (.lam (.lam (.lam (spine (.var 3) [.var 2, .var 1, .var 1, .var 0, .var 0]))))

theorem double_compiles : compile 0 doubleDef = some doubleTerm := by decide +kernel

/-- `app, A : U0, n m l : num, xs : vec A n, ys : vec A m, zs : vec A l`. -/
def concatTelescope : Ctx Tower.Head 8 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil appendRDef.type) U0) numC) numC) numC)
    (vecC (.var 3) (.var 2))) (vecC (.var 4) (.var 2))) (vecC (.var 5) (.var 2))

/-- `vec A (add (add n m) l)`. -/
def concatResult : Tower.Tm 8 :=
  vecC (.var 6) (spine (liftClosed addExport) [spine (liftClosed addExport) [.var 5, .var 4], .var 3])

/-- `concat3 app A n m l xs ys zs = app A (add n m) l (app A n m xs ys) zs`; `app` is variable 7. -/
def concatRow : Row :=
  ⟨[.var, .var, .var, .var, .var, .var, .var, .var], 8,
    spine (.var 7) [.var 6, spine (liftClosed addExport) [.var 5, .var 4], .var 3,
      spine (.var 7) [.var 6, .var 5, .var 4, .var 2, .var 1], .var 0]⟩

/-- **Concatenation of three vectors, over append.** -/
def concatDef : Definition := ⟨"concat3", 8, concatTelescope, concatResult, [concatRow]⟩

/-- The compiled concatenation: the abstraction of its row. -/
def concatTerm : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam (.lam (.lam (.lam
    (spine (.var 7) [.var 6, spine (liftClosed addExport) [.var 5, .var 4], .var 3,
      spine (.var 7) [.var 6, .var 5, .var 4, .var 2, .var 1], .var 0]))))))))

theorem concat_compiles : compile 0 concatDef = some concatTerm := by decide +kernel

theorem concat_covers : baseOf concatDef = 0 := by decide +kernel

theorem double_covers : baseOf doubleDef = 0 := by decide +kernel

/-! ## Map with a function argument -/

/-- `A B : U0, g : A → B, n : num, xs : vec A n`. -/
def mapTelescope : Ctx Tower.Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil U0) U0) (.pi (.var 1) (.var 1))) numC) (vecC (.var 3) (.var 0))

/-- `map A B g n nil = nil`. -/
def mapNilRow : Row := ⟨[.var, .var, .var, .var, .nil], 4, ttC⟩

/-- `map A B g n (cons a v) = pair (g a) (map A B g k v)`; the function is variable 7. -/
def mapConsRow : Row :=
  ⟨[.var, .var, .var, .var, .cons .var .var], 7,
    .pair (.app (.var 4) (.var 1)) (spine (.var 7) [.var 6, .var 5, .var 4, .var 2, .var 0])⟩

/-- **Map.** -/
def mapDef : Definition := ⟨"map", 5, mapTelescope, vecC (.var 3) (.var 1), [mapNilRow, mapConsRow]⟩

/-! ## Controls -/

/-- `add zero m = zero`, overlapping `add zero m = m`. -/
def overlapRow : Row := ⟨[.zero, .var], 1, zeroC⟩

/-- **Overlapping rows.** -/
def overlapDef : Definition :=
  ⟨"add", 2, .snoc (.snoc .nil numC) numC, numC, [addZeroRow, overlapRow, addSuccRow]⟩

/-- `loop (succ k) m = loop (succ k) m`: the recursive call is not on the predecessor. -/
def loopSuccRow : Row := ⟨[.succ .var, .var], 2, .app (.app (.var 2) (succC (.var 1))) (.var 0)⟩

/-- **Recursion not on the predecessor.** -/
def loopDef : Definition := ⟨"loop", 2, .snoc (.snoc .nil numC) numC, numC, [addZeroRow, loopSuccRow]⟩

/-- `A : U0, n : num, xs : vec A n`. -/
def selfTelescope : Ctx Tower.Head 3 := .snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (.var 0))

/-- `self A n nil = refl nil`. -/
def selfNilRow : Row := ⟨[.var, .var, .nil], 2, .refl ttC⟩

/-- `self A n (cons a v) = refl (pair a v)`. -/
def selfConsRow : Row := ⟨[.var, .var, .cons .var .var], 5, .refl (.pair (.var 1) (.var 0))⟩

/-- **A declared type that mentions the vector**: `self : Π A n (xs : vec A n). Id (vec A n) xs xs`. -/
def selfDef : Definition :=
  ⟨"self", 3, selfTelescope, .id (vecC (.var 2) (.var 1)) (.var 0) (.var 0), [selfNilRow, selfConsRow]⟩

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.add_compiles
#print axioms NativeTypesOnTheStep.Computing.Definitions.add_exported
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_compiles
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_covers
#print axioms NativeTypesOnTheStep.Computing.Definitions.concat_compiles
#print axioms NativeTypesOnTheStep.Computing.Definitions.concat_covers
#print axioms NativeTypesOnTheStep.Computing.Definitions.double_compiles
#print axioms NativeTypesOnTheStep.Computing.Definitions.double_covers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
