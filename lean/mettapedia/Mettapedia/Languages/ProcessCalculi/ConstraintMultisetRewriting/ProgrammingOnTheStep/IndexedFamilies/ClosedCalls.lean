import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.AppendOnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.LookupOnTheStep

/-!
# Program equations with fresh telescopes, fired on closed calls

The programs of `VectorPrograms`, in the package with vectors, finite types and their eliminators
(`TowerVectorsModel.rules`). A program equation is a firing whose fresh helper telescope holds the
equation's variables, whose take pattern is its left side, and whose made row is its right side;
the solution of its information instantiates the telescope.

* **The recursive equation of append** (`rule_admitted`). The state holds the closed call
  `append num 1 1 [2] [3] : vec num (add 1 1)`. The rule
  `append A (succ k) m (pair a v) ys = pair a (append A k m v ys)` has the telescope
  `A : U0, k m : num, a : A, v : vec A k, ys : vec A m`; it takes the call, makes its right side at
  the left side's type, and tells that the two sides are equal. The solution sets
  `A ↦ num, k ↦ 0, m ↦ 1, a ↦ 2, v ↦ tt, ys ↦ [3]` (`rule_solution`), and reads the made row as
  `pair 2 (append num 0 1 tt [3])` at the call's declared type `vec num (add 1 1)` (`rule_answer`).
  The answer is the value `[2, 3]` there (`answer_value`), so the closed call computes to its value
  (`call_value`), and meets it at the type `vec num 2` in the knowledge (`call_meets_value`).

* **Lookup at the first index** (`lookup_admitted`). The state holds the closed call
  `lookup num 1 [2] fz : num`; the rule `lookup A (succ k) (pair a w) fz = a` fires on it, and the
  solution reads the made row as `2` (`lookup_answer`).

* **Addition's equations are in the knowledge** (`add_in_knowledge`,
  `add_equation_in_knowledge`): `add 0 1 ≐ 1` and `add (succ 0) 1 ≐ succ (add 0 1)` hold, where a
  package that evaluates addition by firings refutes both
  (`VectorPrograms.add_not_in_knowledge`, `VectorPrograms.add_equation_not_in_knowledge`).
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

namespace ClosedCalls

open TowerVectorsModel TowerVectorsPrograms TowerVectorsLookup
open TowerNumbersModel (u)
open Eliminator (level1 pkg pkgLevels D u0Type numType ctxA ctxK ctxM aType vType ysType frame callType
  resultType callRow resultRow call_meets_result)

/-! ## Closed values -/

def one {n : Nat} : Tower.Tm n := succC zeroC
def two {n : Nat} : Tower.Tm n := succC one
def three {n : Nat} : Tower.Tm n := succC two

/-- The vector `[x]`, of length `1`. -/
def single {n : Nat} (x : Tower.Tm n) : Tower.Tm n := .pair x ttC

/-- The vector `[2, 3]`, of length `2`. -/
def twoThree {n : Nat} : Tower.Tm n := .pair two (single three)

theorem one_typed {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ one numC := D.succ_typed D.zero_typed

theorem two_typed {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ two numC := D.succ_typed (one_typed Γ)

theorem three_typed {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ three numC := D.succ_typed (two_typed Γ)

theorem single_typed {n : Nat} {Γ : Tower.Ctx n} {x : Tower.Tm n} (typed : Typed pkg Γ x numC) :
    Typed pkg Γ (single x) (vecC numC one) :=
  D.cons_typed D.num_typed D.zero_typed typed (D.nil_typed D.num_typed)

theorem twoThree_typed {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ twoThree (vecC numC two) :=
  D.cons_typed D.num_typed (one_typed Γ) (two_typed Γ) (single_typed (three_typed Γ))

/-! ## The recursive equation of append, on a closed call -/

/-- The solution `A ↦ num, k ↦ 0, m ↦ 1, a ↦ 2, v ↦ tt, ys ↦ [3]`, closed. -/
def solution : empty pkg ⟶ frame :=
  pair (pair (pair (pair (pair (pair (toEmpty (empty pkg)) ⟨numC, D.num_typed⟩) ⟨zeroC, D.zero_typed⟩)
    ⟨one, one_typed _⟩) ⟨two, two_typed _⟩) ⟨ttC, D.nil_typed D.num_typed⟩)
    ⟨single three, single_typed (three_typed _)⟩

/-- The closed call is typed at its declared type: it is the left side of the equation at the
solution. -/
theorem closedCall_typed :
    Typed pkg .nil (appendTm numC one one (single two) (single three)) (vecC numC (addC one one)) :=
  (callRow.reindex solution).2.typed

/-- **The closed call** `append num 1 1 [2] [3] : vec num (add 1 1)`. -/
def closedCall : TotalTerm (empty pkg) :=
  ⟨⟨vecC numC (addC one one), u, LevelTower.IsUniverse.sort _,
      D.vec_typed D.num_typed (add_typed level1 (one_typed _) (one_typed _))⟩,
    ⟨appendTm numC one one (single two) (single three), closedCall_typed⟩⟩

/-- One present row, the closed call, and no knowledge. -/
def state : State pkg Nat := ⟨empty pkg, [], {0}, fun _ => closedCall⟩

/-- **The recursive equation of append as a rule**, firing on the closed call. Its telescope is
`A : U0, k m : num, a : A, v : vec A k, ys : vec A m`; it takes the call with the left side, makes
the right side at the left side's type, and tells that the two sides are equal. -/
def ruleFiring : Firing pkgLevels state where
  helpers := .cons (u0Type _) (.cons (numType _) (.cons (numType _) (.cons aType (.cons vType
    (.cons ysType (.nil _))))))
  taken := [0]
  read := []
  takes := [callRow]
  reads := []
  makes := [(1, ⟨callType, consResult⟩)]
  tells := [(callRow, resultRow)]
  guards := []
  queries := []

theorem ruleFiring_information :
    ruleFiring.information = [(callRow, ruleFiring.row 0), (callRow, resultRow)] := rfl

/-- At the solution, the left side is the call. -/
theorem rule_identifies : callRow.reindex solution = (ruleFiring.row 0).reindex solution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The rule fires on the closed call**: the step admits it, with a closed solution of its
information. The told equation holds at the solution because the eliminator computes in
conversion. -/
theorem rule_admitted : (step pkgLevels Nat).Admits ruleFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff ruleFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty pkg, solution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact consResult_typed level1
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [ruleFiring_information]
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · show (frames pkgLevels).E (callRow.reindex solution) ((ruleFiring.row 0).reindex solution)
      rw [rule_identifies]
      exact ((frames pkgLevels).equivalence _).refl _
    · obtain rfl := List.mem_singleton.mp member
      exact (frames pkgLevels).preserves solution call_meets_result
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The telescope at the solution.** -/
theorem rule_solution :
    solution.substitution 5 = numC ∧ solution.substitution 4 = zeroC ∧
      solution.substitution 3 = one ∧ solution.substitution 2 = two ∧
      solution.substitution 1 = ttC ∧ solution.substitution 0 = single three :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The answer**: the solution reads the made row as `pair 2 (append num 0 1 tt [3])`, at the
call's declared type `vec num (add 1 1)`. -/
theorem rule_answer :
    subst solution.substitution
        (((step pkgLevels Nat).result ruleFiring rule_admitted).label 1).2.code =
        .pair two (appendTm numC zeroC one ttC (single three)) ∧
      subst solution.substitution
        (((step pkgLevels Nat).result ruleFiring rule_admitted).label 1).1.code =
        vecC numC (addC one one) :=
  ⟨rfl, rfl⟩

/-! ## The value -/

/-- `ys : vec A m`, over `A : U0, m : num`. -/
def baseYsType : TypeOver ctxK :=
  ⟨vecC (.var 1) (.var 0), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (1 : Fin 2)) (Derivable.var (0 : Fin 2))⟩

/-- The frame of append's base equation: `A : U0, m : num, ys : vec A m`. -/
abbrev baseFrame : Context pkg := extend ctxK baseYsType

/-- `A ↦ num, m ↦ 1, ys ↦ [3]`. -/
def baseSolution : empty pkg ⟶ baseFrame :=
  pair (pair (pair (toEmpty (empty pkg)) ⟨numC, D.num_typed⟩) ⟨one, one_typed _⟩)
    ⟨single three, single_typed (three_typed _)⟩

/-- The base equation at the solution: `append num 0 1 tt [3] ≡ [3]`. -/
theorem inner_value :
    Equal pkg .nil (appendTm numC zeroC one ttC (single three)) (single three)
      (vecC numC (addC zeroC one)) :=
  (append_nil level1).substitute baseSolution.typed

/-- `add 1 1 ≡ 2`, by addition's two equations. -/
theorem one_plus_one {n : Nat} (Γ : Tower.Ctx n) : Equal pkg Γ (addC one one) two numC := by
  have tSucc : Typed pkg Γ (.const TowerNumbersModel.succ) (.pi numC numC) :=
    .const D.dSucc (D.tower.pi_small D.num_typed D.num_typed) (D.tower.isUniverse _)
  exact .trans (TowerVectors.add_succ D.zero_typed (one_typed Γ))
    (.appCong (.refl tSucc) (TowerVectors.add_zero (one_typed Γ)))

/-- **The answer is the value `[2, 3]`**, at the call's declared type: the inner call computes by
the base equation. -/
theorem answer_value :
    Equal pkg .nil (.pair two (appendTm numC zeroC one ttC (single three))) twoThree
      (vecC numC (addC one one)) := by
  have tInner : Typed pkg .nil (addC zeroC one) numC := add_typed level1 D.zero_typed (one_typed _)
  have tS : Typed pkg .nil (.sigma numC (Presentation.rename wk (vecC numC (addC zeroC one)))) U0 :=
    D.tower.sigma_small D.num_typed (D.vec_typed D.num_typed.weaken tInner.weaken)
  have tail : Equal pkg .nil (appendTm numC zeroC one ttC (single three)) (single three)
      (inst0 two (Presentation.rename wk (vecC numC (addC zeroC one)))) := by
    rw [inst0_rename_wk]
    exact inner_value
  have pairs := Derivable.pairCong tS (D.tower.isUniverse _) (.refl (two_typed .nil)) tail
  have types : TypeEq pkg .nil (.sigma numC (Presentation.rename wk (vecC numC (addC zeroC one))))
      (vecC numC (addC one one)) :=
    TypeEq.trans pkgLevels (D.vec_succ_eq D.num_typed tInner).symm
      (vec_congr level1 D.num_typed (TowerVectors.add_succ D.zero_typed (one_typed _))).symm
  exact Equal.convType pairs types

/-- **The closed call computes to its value**: `append num 1 1 [2] [3] ≡ [2, 3]`, at its declared
type, by the eliminator's two equations. -/
theorem call_value :
    Equal pkg .nil (appendTm numC one one (single two) (single three)) twoThree
      (vecC numC (addC one one)) :=
  .trans ((equivalent_iff pkgLevels _ _).mp ((frames pkgLevels).preserves solution call_meets_result)).2
    answer_value

/-- The value `[2, 3] : vec num 2`. -/
def valueRow : TotalTerm (empty pkg) :=
  ⟨⟨vecC numC two, u, LevelTower.IsUniverse.sort _, D.vec_typed D.num_typed (two_typed _)⟩,
    ⟨twoThree, twoThree_typed _⟩⟩

/-- **The closed call meets its value in the knowledge**, the call at `vec num (add 1 1)` and the
value at `vec num 2`. -/
theorem call_meets_value : (frames pkgLevels).E closedCall valueRow :=
  (equivalent_iff pkgLevels _ _).mpr ⟨vec_congr level1 D.num_typed (one_plus_one _), call_value⟩

/-! ## Lookup at the first index, on a closed call -/

/-- The solution `A ↦ num, k ↦ 0, a ↦ 2, w ↦ tt`, closed. -/
def lookupSolution : empty pkg ⟶ Lookup.frame :=
  pair (pair (pair (pair (toEmpty (empty pkg)) ⟨numC, D.num_typed⟩) ⟨zeroC, D.zero_typed⟩)
    ⟨two, two_typed _⟩) ⟨ttC, D.nil_typed D.num_typed⟩

/-- The closed call is typed: it is the left side of the equation at the solution. -/
theorem closedLookup_typed : Typed pkg .nil (lookupTm numC one (single two) fzC) numC :=
  (Lookup.callRow.reindex lookupSolution).2.typed

/-- **The closed call** `lookup num 1 [2] fz : num`. -/
def closedLookup : TotalTerm (empty pkg) :=
  ⟨numType _, ⟨lookupTm numC one (single two) fzC, closedLookup_typed⟩⟩

def lookupState : State pkg Nat := ⟨empty pkg, [], {0}, fun _ => closedLookup⟩

/-- **The rule `lookup A (succ k) (pair a w) fz = a`**, firing on the closed call: its telescope is
`A : U0, k : num, a : A, w : vec A k`, and it makes the row `a : A`. -/
def lookupFiring : Firing pkgLevels lookupState where
  helpers := .cons (u0Type _) (.cons (numType _) (.cons Lookup.aType (.cons Lookup.wType (.nil _))))
  taken := [0]
  read := []
  takes := [Lookup.callRow]
  reads := []
  makes := [(1, ⟨Lookup.elementType, (.var 1 : Tower.Tm 4)⟩)]
  tells := [(Lookup.callRow, Lookup.answerRow)]
  guards := []
  queries := []

theorem lookupFiring_information :
    lookupFiring.information =
      [(Lookup.callRow, lookupFiring.row 0), (Lookup.callRow, Lookup.answerRow)] := rfl

theorem lookup_identifies :
    Lookup.callRow.reindex lookupSolution = (lookupFiring.row 0).reindex lookupSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The rule fires on the closed call.** -/
theorem lookup_admitted : (step pkgLevels Nat).Admits lookupFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff lookupFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty pkg, lookupSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Derivable.var (1 : Fin 4)
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [lookupFiring_information]
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · show (frames pkgLevels).E (Lookup.callRow.reindex lookupSolution)
        ((lookupFiring.row 0).reindex lookupSolution)
      rw [lookup_identifies]
      exact ((frames pkgLevels).equivalence _).refl _
    · obtain rfl := List.mem_singleton.mp member
      exact (frames pkgLevels).preserves lookupSolution Lookup.call_meets_answer
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The answer**: the solution reads the made row as `2`. -/
theorem lookup_answer :
    subst lookupSolution.substitution
      (((step pkgLevels Nat).result lookupFiring lookup_admitted).label 1).2.code = two := rfl

/-- **The closed call computes to its answer**: `lookup num 1 [2] fz ≡ 2`. -/
theorem lookup_value : Equal pkg .nil (lookupTm numC one (single two) fzC) two numC :=
  ((equivalent_iff pkgLevels _ _).mp
    ((frames pkgLevels).preserves lookupSolution Lookup.call_meets_answer)).2

/-! ## Addition's equations are in the knowledge -/

/-- `n : num`, as a typed term of the empty frame. -/
def numTerm (code : Tower.Tm 0) (typed : Typed pkg .nil code numC) : TotalTerm (empty pkg) :=
  ⟨numType _, ⟨code, typed⟩⟩

/-- **`add 0 1 ≐ 1` holds in the knowledge**: addition computes in conversion. -/
theorem add_in_knowledge :
    (frames pkgLevels).E (numTerm (addC zeroC one) (add_typed level1 D.zero_typed (one_typed _)))
      (numTerm one (one_typed _)) :=
  (equivalent_iff pkgLevels _ _).mpr
    ⟨⟨u, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩, TowerVectors.add_zero (one_typed _)⟩

/-- **So does the recursion equation** `add (succ 0) 1 ≐ succ (add 0 1)`. -/
theorem add_equation_in_knowledge :
    (frames pkgLevels).E (numTerm (addC one one) (add_typed level1 (one_typed _) (one_typed _)))
      (numTerm (succC (addC zeroC one))
        (D.succ_typed (add_typed level1 D.zero_typed (one_typed _)))) :=
  (equivalent_iff pkgLevels _ _).mpr
    ⟨⟨u, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩,
      TowerVectors.add_succ D.zero_typed (one_typed _)⟩

end ClosedCalls

end ProgrammingOnTheStep.IndexedFamilies

#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.rule_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.rule_answer
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.answer_value
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.call_value
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.call_meets_value
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.lookup_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.lookup_answer
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.lookup_value
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.add_in_knowledge
#print axioms ProgrammingOnTheStep.IndexedFamilies.ClosedCalls.add_equation_in_knowledge

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
