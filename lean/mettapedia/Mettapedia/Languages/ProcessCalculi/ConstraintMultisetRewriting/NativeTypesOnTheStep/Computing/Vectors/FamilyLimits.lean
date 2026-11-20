import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.NotUnitary

/-!
# Where a recursive family shows: two unification problems a user meets

The vectors of the package are a recursive family: `vec A zero ⟶ unit` and
`vec A (succ n) ⟶ Σ A (vec A n)`. Two of its properties differ from an inductive family with
constructors of its own. Each is visible in one unification problem.

**1. The type former is not injective at length zero.** The problem `vec X zero ≐ vec num zero`, over
`X : U0` (`emptyElemStore`), does not determine `X`. It is solved by the identity, `X` left open
(`emptyElem_identity`), and by the two closed solutions `X ↦ num` and `X ↦ unit`
(`emptyElem_num`, `emptyElem_unit`), which differ (`num_ne_unit`). The package's settler settles it by
conversion alone, by kernel evaluation (`emptyElem_settled`). For an inductive family the same
problem would teach `X ≐ num`. A user sees that **the element type of an empty vector is never
inferred**: an implicit element type fixed only by an empty vector stays open.

**2. At a successor length the eliminator unfolds on a variable vector.** The problem
`head A k v ≐ fst v`, over `A : U0, k : num, v : vec A (succ k)`, with `head` written with the
eliminator (`headStore`), is solved by the identity (`headStore_identity`), and the package's
settler settles it by conversion alone, by kernel evaluation (`headStore_settled`): the eliminator
fires on the variable `v`. For an inductive family the eliminator is stuck on a variable vector, and
the problem would need the case split `v ≐ cons a w`. A user sees that **programs on vectors of a
known successor length compute without matching**, and that no empty case arises there; at length
zero the eliminator is stuck on a variable vector as for an inductive family
(`TowerVectors.vecElim_stuck_zero_vector`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (U0 numC zeroC succC unitC ttC vecC)
open TowerVectorsHead (headTm)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D u0Type numType ctxA ctxK)

/-! ## 1. Not injective at length zero -/

/-- **`vec X zero ≐ vec num zero`**, over `X : U0`. -/
def emptyElemStore : EquationStore (TotalTerm ctxA) :=
  [(⟨u0Type _, ⟨vecC (.var 0) zeroC, D.vec_typed (Derivable.var (0 : Fin 1)) D.zero_typed⟩⟩,
    ⟨u0Type _, ⟨vecC numC zeroC, D.vec_typed D.num_typed D.zero_typed⟩⟩)]

/-- **The identity solves it**: `X` stays open. -/
theorem emptyElem_identity : (frames vecS.levels).Models (𝟙 ctxA) emptyElemStore := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact (equivalent_iff vecS.levels _ _).mpr ⟨⟨_, LevelTower.IsUniverse.sort _, .refl D.tower.u0_typed⟩,
    .trans (D.vec_zero (Derivable.var (0 : Fin 1))) (.symm (D.vec_zero D.num_typed))⟩

/-- `X ↦ num`. -/
def elemNum : empty pkg ⟶ ctxA := pair (toEmpty (empty pkg)) ⟨numC, D.num_typed⟩

/-- `X ↦ unit`. -/
def elemUnit : empty pkg ⟶ ctxA := pair (toEmpty (empty pkg)) ⟨unitC, D.unit_typed⟩

theorem emptyElem_num : (frames vecS.levels).Models elemNum emptyElemStore := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact (equivalent_iff vecS.levels _ _).mpr ⟨⟨_, LevelTower.IsUniverse.sort _, .refl D.tower.u0_typed⟩,
    .refl (D.vec_typed D.num_typed D.zero_typed)⟩

theorem emptyElem_unit : (frames vecS.levels).Models elemUnit emptyElemStore := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact (equivalent_iff vecS.levels _ _).mpr ⟨⟨_, LevelTower.IsUniverse.sort _, .refl D.tower.u0_typed⟩,
    .trans (D.vec_zero D.unit_typed) (.symm (D.vec_zero D.num_typed))⟩

/-- **The two closed solutions differ**: `num` and `unit` are different types. -/
theorem num_ne_unit : ¬ TypeEq pkg .nil numC unitC :=
  (TowerVectors.vec_zero_not_injective (lv := level1) .nil).2

/-- **The package's settler settles the problem by conversion alone**, by kernel evaluation. -/
theorem emptyElem_settled : (vecFamily 16 4 emptyElemStore).isSettled = true := by decide +kernel

/-! ## 2. At a successor length the eliminator unfolds on a variable vector -/

/-- `v : vec A (succ k)`, over `A, k`. -/
def vSuccType : TypeOver ctxK :=
  ⟨vecC (.var 1) (succC (.var 0)), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (1 : Fin 2)) (D.succ_typed (Derivable.var (0 : Fin 2)))⟩

/-- The frame `A : U0, k : num, v : vec A (succ k)`. -/
abbrev succFrame : Context pkg := extend ctxK vSuccType

/-- `A`, over the frame. -/
def elemType : TypeOver succFrame := ⟨.var 2, u, LevelTower.IsUniverse.sort _, Derivable.var (2 : Fin 3)⟩

/-- **`head A k v ≐ fst v`**, with `head` written with the eliminator, `v` a variable. -/
def headStore : EquationStore (TotalTerm succFrame) :=
  [(⟨elemType, ⟨headTm (.var 2) (.var 1) (.var 0), TowerVectorsHead.head_typed level1⟩⟩,
    ⟨elemType, ⟨.fst (.var 0),
      D.fst_typed (Derivable.var (2 : Fin 3)) (Derivable.var (1 : Fin 3)) (Derivable.var (0 : Fin 3))⟩⟩)]

/-- **The identity solves it**: no case split on `v`. -/
theorem headStore_identity : (frames vecS.levels).Models (𝟙 succFrame) headStore := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact (equivalent_iff vecS.levels _ _).mpr
    ⟨⟨u, LevelTower.IsUniverse.sort _, .refl (Derivable.var (2 : Fin 3))⟩, TowerVectorsHead.head_fst level1⟩

/-- **The package's settler settles it by conversion alone**, by kernel evaluation: the eliminator fires
on the variable vector. -/
theorem headStore_settled : (vecFamily 16 4 headStore).isSettled = true := by decide +kernel

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.emptyElem_identity
#print axioms NativeTypesOnTheStep.Computing.Vectors.emptyElem_num
#print axioms NativeTypesOnTheStep.Computing.Vectors.emptyElem_unit
#print axioms NativeTypesOnTheStep.Computing.Vectors.num_ne_unit
#print axioms NativeTypesOnTheStep.Computing.Vectors.emptyElem_settled
#print axioms NativeTypesOnTheStep.Computing.Vectors.headStore_identity
#print axioms NativeTypesOnTheStep.Computing.Vectors.headStore_settled

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
