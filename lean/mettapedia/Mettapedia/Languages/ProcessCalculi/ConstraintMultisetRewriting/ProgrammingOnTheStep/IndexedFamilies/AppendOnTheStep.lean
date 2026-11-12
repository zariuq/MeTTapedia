import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsPrograms

/-!
# The recursive case of append on the dependent step, with the eliminator package

The recursive equation of append, `append (succ k) m (cons a v) ys = cons a (append k m v ys)`, as
one firing of the dependent full step `Interface.DependentFull.step`, in two packages:

* **with vectors and their eliminator** (`TowerVectorsModel.rules`), where `append` is a program by
  the eliminator and addition computes in conversion: the firing takes the call
  `append A (succ k) m (pair a v) ys : vec A (add (succ k) m)`, makes its result
  `pair a (append A k m v ys)` **at the call's declared type** `vec A (add (succ k) m)`, and tells
  that the call equals its result. It is admitted (`recursive_admitted`), with every variable of the
  equation open; its made row has the declared type (`recursive_result_type`);
* **in the all-rigid package** (`VectorPackage`), where `append`, `cons` and `add` are rigid heads:
  the same firing, taking the call `append (succ n) m (cons n x xs) ys`, making
  `cons (add n m) x (append n m xs ys)` and telling that the call equals it, is refused whatever
  type the made row is given (`rigid_refused`): the told equation relates spines of two different
  rigid constants, so the information has no solution. The lengths `add (succ n) m` of the call's
  declared type and `succ (add n m)` of the result's type have no common instance there
  (`Rigid.lengths_apart`), where in the eliminator package they are equal
  (`Eliminator.lengths_meet`).

So the eliminator package admits what the rigid package refuses: the recursive call meets its
result, at its declared type, in the knowledge of the step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.IndexedFamilies

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull

/-! ## With vectors and their eliminator -/

namespace Eliminator

open TowerVectorsModel TowerVectorsPrograms
open TowerNumbersModel (u)

/-- The recursors land in level 1. -/
abbrev level1 : LevelExpr Nat := .succ (.const 0)

/-- **The package with vectors and their eliminator.** -/
abbrev pkg : Rules Tower.Head := TowerVectorsModel.rules level1

abbrev pkgLevels : LevelModel pkg ℕ := TowerVectorsModel.levels level1 (fun _ => 0)

theorem D : VecDeclared pkg := vecDeclared_rules level1

/-- `U0`, over any frame. -/
def u0Type (Γ : Context pkg) : TypeOver Γ :=
  ⟨U0, .sort (.succ (.const 0)), LevelTower.IsUniverse.sort _, D.tower.u0_typed⟩

/-- `num`, over any frame. -/
def numType (Γ : Context pkg) : TypeOver Γ := ⟨numC, u, LevelTower.IsUniverse.sort _, D.num_typed⟩

abbrev ctxA : Context pkg := extend (empty pkg) (u0Type _)
abbrev ctxK : Context pkg := extend ctxA (numType _)
abbrev ctxM : Context pkg := extend ctxK (numType _)

/-- `a : A`. -/
def aType : TypeOver ctxM := ⟨.var 2, u, LevelTower.IsUniverse.sort _, Derivable.var (2 : Fin 3)⟩

abbrev ctxa : Context pkg := extend ctxM aType

/-- `v : vec A k`. -/
def vType : TypeOver ctxa :=
  ⟨vecC (.var 3) (.var 2), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (3 : Fin 4)) (Derivable.var (2 : Fin 4))⟩

abbrev ctxv : Context pkg := extend ctxa vType

/-- `ys : vec A m`. -/
def ysType : TypeOver ctxv :=
  ⟨vecC (.var 4) (.var 2), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (4 : Fin 5)) (Derivable.var (2 : Fin 5))⟩

/-- **The frame of the equation**: `A : U0, k m : num, a : A, v : vec A k, ys : vec A m`; every
variable of the equation is open. -/
abbrev frame : Context pkg := extend ctxv ysType

/-- The call's declared type `vec A (add (succ k) m)`. -/
def callType : TypeOver frame :=
  ⟨vecC (.var 5) (addC (succC (.var 4)) (.var 3)), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (5 : Fin 6))
      (add_typed level1 (D.succ_typed (Derivable.var (4 : Fin 6))) (Derivable.var (3 : Fin 6)))⟩

/-- The result's own type `vec A (succ (add k m))`. -/
def resultType : TypeOver frame :=
  ⟨vecC (.var 5) (succC (addC (.var 4) (.var 3))), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (5 : Fin 6))
      (D.succ_typed (add_typed level1 (Derivable.var (4 : Fin 6)) (Derivable.var (3 : Fin 6))))⟩

/-- **The call** `append A (succ k) m (pair a v) ys : vec A (add (succ k) m)`. -/
def callRow : TotalTerm frame := ⟨callType, ⟨consCall, consCall_typed level1⟩⟩

theorem result_typed_own : Typed pkg frame.raw consResult resultType.code :=
  Typed.convType (consResult_typed level1) (cons_types level1)

/-- **Its result** `pair a (append A k m v ys)`, at its own type. -/
def resultRow : TotalTerm frame := ⟨resultType, ⟨consResult, result_typed_own⟩⟩

/-- The state of the call: one present row, the call, and no knowledge. -/
def callState : State pkg Nat := ⟨frame, [], {0}, fun _ => callRow⟩

/-- **The recursive equation of append, firing on the call**: it takes the call, makes its result
at the call's declared type, and tells that the call equals its result. -/
def recursiveFiring : Firing pkgLevels callState where
  helpers := .nil _
  taken := [0]
  read := []
  takes := [callRow]
  reads := []
  makes := [(1, ⟨callType, consResult⟩)]
  tells := [(callRow, resultRow)]
  guards := []
  queries := []

theorem recursiveFiring_information :
    recursiveFiring.information =
      [(callRow, recursiveFiring.row 0), (callRow, resultRow)] := rfl

/-- At the identity solution, the take pattern is the row it takes. -/
theorem take_identifies :
    callRow.reindex (𝟙 frame) = (recursiveFiring.row 0).reindex (𝟙 frame) :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem call_reindex : callRow.reindex (𝟙 frame) = callRow := reindex_id _

theorem result_reindex : resultRow.reindex (𝟙 frame) = resultRow := reindex_id _

/-- **The call equals its result, in the knowledge**: their types are equal by addition and `vec`'s
equation, and the terms by the eliminator's computation. -/
theorem call_meets_result : (frames pkgLevels).E callRow resultRow :=
  (equivalent_iff pkgLevels _ _).mpr ⟨cons_types level1, append_cons level1⟩

/-- The length in the call's declared type, `add (succ k) m`. -/
def callLength : TotalTerm frame :=
  ⟨numType _, ⟨addC (succC (.var 4)) (.var 3),
    add_typed level1 (D.succ_typed (Derivable.var (4 : Fin 6))) (Derivable.var (3 : Fin 6))⟩⟩

/-- The length in the result's own type, `succ (add k m)`. -/
def resultLength : TotalTerm frame :=
  ⟨numType _, ⟨succC (addC (.var 4) (.var 3)),
    D.succ_typed (add_typed level1 (Derivable.var (4 : Fin 6)) (Derivable.var (3 : Fin 6)))⟩⟩

/-- **The two lengths meet in the knowledge**: addition computes in conversion. -/
theorem lengths_meet : (frames pkgLevels).E callLength resultLength :=
  (equivalent_iff pkgLevels _ _).mpr
    ⟨⟨u, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩,
      TowerVectors.add_succ (Derivable.var (4 : Fin 6)) (Derivable.var (3 : Fin 6))⟩

/-- **The recursive firing is admitted**, at the identity solution: every variable stays open. -/
theorem recursive_admitted : (step pkgLevels Nat).Admits recursiveFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff recursiveFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨frame, 𝟙 _, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact consResult_typed level1
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [recursiveFiring_information]
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · show (frames pkgLevels).E (callRow.reindex (𝟙 frame)) ((recursiveFiring.row 0).reindex (𝟙 frame))
      rw [take_identifies]
      exact ((frames pkgLevels).equivalence _).refl _
    · obtain rfl := List.mem_singleton.mp member
      show (frames pkgLevels).E (callRow.reindex (𝟙 frame)) (resultRow.reindex (𝟙 frame))
      rw [call_reindex, result_reindex]
      exact call_meets_result
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The made row has the call's declared type**: `vec A (add (succ k) m)`, and its term is the
result `pair a (append A k m v ys)`. -/
theorem recursive_result_type :
    (((step pkgLevels Nat).result recursiveFiring recursive_admitted).label 1).1.code =
        (vecC (.var 5) (addC (succC (.var 4)) (.var 3)) : Tower.Tm 6) ∧
      (((step pkgLevels Nat).result recursiveFiring recursive_admitted).label 1).2.code =
        (consResult : Tower.Tm 6) :=
  ⟨rfl, rfl⟩

end Eliminator

/-! ## In the all-rigid package -/

namespace Rigid

open VectorPackage VectorPrograms

/-- The frame `n m x : nat, xs : vec n, ys : vec m`. -/
abbrev frame₃ : Context rules := extend (extend (extend (empty rules) (natType _)) (natType _)) (natType _)

def xsType : TypeOver frame₃ := ⟨vecC (.var 2), u0, .sort _, vec_typed (Derivable.var (2 : Fin 3))⟩

abbrev frame₄ : Context rules := extend frame₃ xsType

def ysType : TypeOver frame₄ := ⟨vecC (.var 2), u0, .sort _, vec_typed (Derivable.var (2 : Fin 4))⟩

/-- **The frame of the equation**, every variable open. -/
abbrev frame : Context rules := extend frame₄ ysType

/-- The call `append (succ n) m (cons n x xs) ys`. -/
def callCode : Tower.Tm 5 :=
  appendC (succC (.var 4)) (.var 3) (consC (.var 4) (.var 2) (.var 1)) (.var 0)

/-- The result `cons (add n m) x (append n m xs ys)`. -/
def resultCode : Tower.Tm 5 :=
  consC (addC (.var 4) (.var 3)) (.var 2) (appendC (.var 4) (.var 3) (.var 1) (.var 0))

theorem call_typed : Typed rules frame.raw callCode (vecC (addC (succC (.var 4)) (.var 3))) := by
  have n : Typed rules frame.raw (.var 4) natC := Derivable.var (4 : Fin 5)
  have m : Typed rules frame.raw (.var 3) natC := Derivable.var (3 : Fin 5)
  have x : Typed rules frame.raw (.var 2) natC := Derivable.var (2 : Fin 5)
  have xs : Typed rules frame.raw (.var 1) (vecC (.var 4)) := Derivable.var (1 : Fin 5)
  have ys : Typed rules frame.raw (.var 0) (vecC (.var 3)) := Derivable.var (0 : Fin 5)
  have list := Derivable.appElim (Derivable.appElim (Derivable.appElim (cons_const_typed frame.raw) n) x) xs
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (append_const_typed frame.raw) (succ_typed n)) m) list) ys
  exact typed

theorem result_typed : Typed rules frame.raw resultCode (vecC (succC (addC (.var 4) (.var 3)))) := by
  have n : Typed rules frame.raw (.var 4) natC := Derivable.var (4 : Fin 5)
  have m : Typed rules frame.raw (.var 3) natC := Derivable.var (3 : Fin 5)
  have x : Typed rules frame.raw (.var 2) natC := Derivable.var (2 : Fin 5)
  have xs : Typed rules frame.raw (.var 1) (vecC (.var 4)) := Derivable.var (1 : Fin 5)
  have ys : Typed rules frame.raw (.var 0) (vecC (.var 3)) := Derivable.var (0 : Fin 5)
  have rest := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (append_const_typed frame.raw) n) m) xs) ys
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (cons_const_typed frame.raw)
    (add_typed n m)) x) rest
  exact typed

def callType : TypeOver frame :=
  ⟨vecC (addC (succC (.var 4)) (.var 3)), u0, .sort _,
    vec_typed (add_typed (succ_typed (Derivable.var (4 : Fin 5))) (Derivable.var (3 : Fin 5)))⟩

def resultType : TypeOver frame :=
  ⟨vecC (succC (addC (.var 4) (.var 3))), u0, .sort _,
    vec_typed (succ_typed (add_typed (Derivable.var (4 : Fin 5)) (Derivable.var (3 : Fin 5))))⟩

/-- The call, at its declared type `vec (add (succ n) m)`. -/
def callRow : TotalTerm frame := ⟨callType, ⟨callCode, call_typed⟩⟩

/-- The result, at its type `vec (succ (add n m))`. -/
def resultRow : TotalTerm frame := ⟨resultType, ⟨resultCode, result_typed⟩⟩

def callState : State rules Nat := ⟨frame, [], {0}, fun _ => callRow⟩

/-- **The same recursive firing, in the rigid package**: take the call, make its result at a given
type, and tell that the call equals its result. At `callType` it is the firing the eliminator
package admits, row for row. -/
def recursiveFiring (madeType : TypeOver frame) : Firing levels callState where
  helpers := .nil _
  taken := [0]
  read := []
  takes := [callRow]
  reads := []
  makes := [(1, ⟨madeType, resultCode⟩)]
  tells := [(callRow, resultRow)]
  guards := []
  queries := []

/-- **The rigid package refuses it, whatever type the made row is given**, the call's declared
type and the result's own type included: the told equation relates spines of the different rigid
constants `append` and `cons`, so no solution of the information exists. -/
theorem rigid_refused (madeType : TypeOver frame) :
    ¬ (step levels Nat).Admits (recursiveFiring madeType) := by
  rintro ⟨-, -, solvable, -⟩
  have atCallType : (frames levels).Solvable (recursiveFiring callType).information := solvable
  exact ContextualDependentRigid.not_solvable_of_storeClashes (S := setting) rigid facts complete
    (by decide) atCallType

/-- The length in the call's declared type, `add (succ n) m`. -/
def callLength : TotalTerm frame :=
  ⟨natType _, ⟨addC (succC (.var 4)) (.var 3),
    add_typed (succ_typed (Derivable.var (4 : Fin 5))) (Derivable.var (3 : Fin 5))⟩⟩

/-- The length in the result's own type, `succ (add n m)`. -/
def resultLength : TotalTerm frame :=
  ⟨natType _, ⟨succC (addC (.var 4) (.var 3)),
    succ_typed (add_typed (Derivable.var (4 : Fin 5)) (Derivable.var (3 : Fin 5)))⟩⟩

/-- **In the rigid package the two lengths are apart**: `add (succ n) m ≐ succ (add n m)` has no
solution at any instance of the frame. In the eliminator package they meet
(`Eliminator.lengths_meet`). -/
theorem lengths_apart : ¬ (frames levels).Solvable [(callLength, resultLength)] :=
  ContextualDependentRigid.not_solvable_of_storeClashes (S := setting) rigid facts complete
    (by decide)

end Rigid

end ProgrammingOnTheStep.IndexedFamilies

#print axioms ProgrammingOnTheStep.IndexedFamilies.Eliminator.call_meets_result
#print axioms ProgrammingOnTheStep.IndexedFamilies.Eliminator.recursive_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.Eliminator.recursive_result_type
#print axioms ProgrammingOnTheStep.IndexedFamilies.Rigid.rigid_refused
#print axioms ProgrammingOnTheStep.IndexedFamilies.Eliminator.lengths_meet
#print axioms ProgrammingOnTheStep.IndexedFamilies.Rigid.lengths_apart

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
