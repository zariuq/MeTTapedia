import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.IndexedFamilies.ClosedCalls

/-!
# The recursive lookup, run end to end with the eliminator package

The program `RecursiveRun.lookupRun`, in the package with vectors, finite types and their
eliminators (`TowerVectorsModel.rules`). `lookup` by its two equations:

* `lookup A (succ k) (pair a w) (fs i) = lookup A k w i` (the recursive equation);
* `lookup A (succ k) (pair a w) fz = a`.

On the closed call `lookup num 2 [1, 2] (fs fz)`, the recursive equation fires first
(`tail_admitted`), with the fresh telescope `A : U0, k : num, a : A, w : vec A k, i : fin k`; its
made row is the recursive call. Then the base equation fires on that row in the state the first
firing reached (`head_admitted`), with a fresh telescope of its own. Together they form a run of
the step (`lookupRun`), whose last state holds the answer, which the solution reads as `2`
(`lookupRun_answer`), and the solution solves the whole knowledge of the run (`lookupRun_solved`).

Each firing also tells its equation, which holds in the knowledge because the eliminator
computes in conversion; so the closed call is equal to `2` without any run (`call_value`).
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

namespace Run

open TowerVectorsModel TowerVectorsPrograms TowerVectorsLookup
open TowerNumbersModel (u)
open Eliminator (level1 pkg pkgLevels D u0Type numType)
open ClosedCalls (one two single one_typed two_typed single_typed)

/-! ## The call -/

/-- The vector `[1, 2]`, of length `2`. -/
def vec12 {n : Nat} : Tower.Tm n := .pair one (single two)

theorem vec12_typed {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ vec12 (vecC numC two) :=
  D.cons_typed D.num_typed (one_typed Γ) (one_typed Γ) (single_typed (two_typed Γ))

/-- The index `fs fz : fin 2`. -/
def idx {n : Nat} : Tower.Tm n := fsC fzC

theorem idx_typed {n : Nat} (Γ : Tower.Ctx n) : Typed pkg Γ idx (finC two) :=
  fs_typed level1 (one_typed Γ) (fz_typed level1 D.zero_typed)

theorem call_typed : Typed pkg .nil (lookupTm numC two vec12 idx) numC := by
  have m₀ : SubstMor pkg .nil .nil fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor pkg lookupCtx .nil
      (consSub idx (consSub vec12 (consSub two (consSub numC fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ D.num_typed) (two_typed _))
      (vec12_typed _)) (idx_typed _)
  exact (lookup_typed level1).substitute mor

/-- **The call** `lookup num 2 [1, 2] (fs fz) : num`, closed. -/
def callRow : TotalTerm (empty pkg) := ⟨numType _, ⟨lookupTm numC two vec12 idx, call_typed⟩⟩

def start : State pkg Nat := ⟨empty pkg, [], {0}, fun _ => callRow⟩

/-! ## The recursive equation -/

/-- `i : fin k`, over `A : U0, k : num, a : A, w : vec A k`. -/
def iType : TypeOver Lookup.frame :=
  ⟨finC (.var 2), u, LevelTower.IsUniverse.sort _, fin_typed level1 (Derivable.var (2 : Fin 4))⟩

/-- The frame of the recursive equation: `A : U0, k : num, a : A, w : vec A k, i : fin k`. -/
abbrev tailFrame : Context pkg := extend Lookup.frame iType

/-- The element type `A`, over the recursive frame. -/
def elemType : TypeOver tailFrame :=
  ⟨.var 4, u, LevelTower.IsUniverse.sort _, Derivable.var (4 : Fin 5)⟩

/-- The left side `lookup A (succ k) (pair a w) (fs i)`. -/
def tailPattern : TotalTerm tailFrame :=
  ⟨elemType, ⟨lookupTm (.var 4) (succC (.var 3)) (.pair (.var 2) (.var 1)) (fsC (.var 0)),
    (Equal.typed (S := setting level1 fun _ => 0) (lookup_fs level1) (fsCtx_formed level1)).1⟩⟩

/-- The right side, the recursive call `lookup A k w i`. -/
def recursiveCall : TotalTerm tailFrame :=
  ⟨elemType, ⟨lookupTm (.var 4) (.var 3) (.var 1) (.var 0),
    (Equal.typed (S := setting level1 fun _ => 0) (lookup_fs level1) (fsCtx_formed level1)).2⟩⟩

/-- **The recursive equation holds in the knowledge.** -/
theorem tail_meets : (frames pkgLevels).E tailPattern recursiveCall :=
  (equivalent_iff pkgLevels _ _).mpr
    ⟨⟨u, LevelTower.IsUniverse.sort _, .refl (Derivable.var (4 : Fin 5))⟩, lookup_fs level1⟩

/-- **The recursive equation, firing on the call**: it makes row `1`, the recursive call, and
tells the equation. -/
def tailFiring : Firing pkgLevels start where
  helpers := .cons (u0Type _) (.cons (numType _) (.cons Lookup.aType (.cons Lookup.wType
    (.cons iType (.nil _)))))
  taken := [0]
  read := []
  takes := [tailPattern]
  reads := []
  makes := [(1, ⟨elemType, (lookupTm (.var 4) (.var 3) (.var 1) (.var 0) : Tower.Tm 5)⟩)]
  tells := [(tailPattern, recursiveCall)]
  guards := []
  queries := []

/-- `A ↦ num, k ↦ 1, a ↦ 1, w ↦ [2], i ↦ fz`. -/
def tailSolution : empty pkg ⟶ tailFrame :=
  pair (pair (pair (pair (pair (toEmpty (empty pkg)) ⟨numC, D.num_typed⟩) ⟨one, one_typed _⟩)
    ⟨one, one_typed _⟩) ⟨single two, single_typed (two_typed _)⟩)
    ⟨fzC, fz_typed level1 D.zero_typed⟩

theorem tailFiring_information :
    tailFiring.information = [(tailPattern, tailFiring.row 0), (tailPattern, recursiveCall)] := rfl

theorem tail_identifies : tailPattern.reindex tailSolution = (tailFiring.row 0).reindex tailSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The recursive equation fires.** -/
theorem tail_admitted : (step pkgLevels Nat).Admits tailFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff tailFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty pkg, tailSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact recursiveCall.2.typed
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [tailFiring_information]
    intro e member
    rcases List.mem_cons.mp member with rfl | member
    · show (frames pkgLevels).E (tailPattern.reindex tailSolution)
        ((tailFiring.row 0).reindex tailSolution)
      rw [tail_identifies]
      exact ((frames pkgLevels).equivalence _).refl _
    · obtain rfl := List.mem_singleton.mp member
      exact (frames pkgLevels).preserves tailSolution tail_meets
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- The state the recursive equation reaches. -/
abbrev middle : State pkg Nat := (step pkgLevels Nat).result tailFiring tail_admitted

/-! ## The base equation, in the state reached -/

/-- `a' : A'`, over the recursive frame extended by `A' : U0, k' : num`. -/
def aType' : TypeOver (extend (extend tailFrame (u0Type _)) (numType _)) :=
  ⟨.var 1, u, LevelTower.IsUniverse.sort _, Derivable.var (1 : Fin 7)⟩

/-- `w' : vec A' k'`. -/
def wType' : TypeOver (extend (extend (extend tailFrame (u0Type _)) (numType _)) aType') :=
  ⟨vecC (.var 2) (.var 1), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (2 : Fin 8)) (Derivable.var (1 : Fin 8))⟩

/-- The frame of the base equation: the recursive frame, then
`A' : U0, k' : num, a' : A', w' : vec A' k'`. -/
abbrev headFrame : Context pkg :=
  extend (extend (extend (extend tailFrame (u0Type _)) (numType _)) aType') wType'

/-- The element type `A'`, over the base frame. -/
def elemType' : TypeOver headFrame :=
  ⟨.var 3, u, LevelTower.IsUniverse.sort _, Derivable.var (3 : Fin 9)⟩

/-- The base equation over its frame: `lookup A' (succ k') (pair a' w') fz ≡ a'`. -/
theorem head_equation :
    Equal pkg headFrame.raw (lookupTm (.var 3) (succC (.var 2)) (.pair (.var 1) (.var 0)) fzC) (.var 1)
      (.var 3) := by
  have tA : Typed pkg headFrame.raw (.var 3) U0 := Derivable.var (3 : Fin 9)
  have tk : Typed pkg headFrame.raw (.var 2) numC := Derivable.var (2 : Fin 9)
  have ta : Typed pkg headFrame.raw (.var 1) (.var 3) := Derivable.var (1 : Fin 9)
  have tw : Typed pkg headFrame.raw (.var 0) (vecC (.var 3) (.var 2)) := Derivable.var (0 : Fin 9)
  have m₀ : SubstMor pkg .nil headFrame.raw fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor pkg fzCtx headFrame.raw
      (consSub (.var 0) (consSub (.var 1) (consSub (.var 2) (consSub (.var 3)
        fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) tk) ta) tw
  exact (lookup_fz level1).substitute mor

/-- The left side `lookup A' (succ k') (pair a' w') fz`. -/
def headPattern : TotalTerm headFrame :=
  ⟨elemType', ⟨lookupTm (.var 3) (succC (.var 2)) (.pair (.var 1) (.var 0)) fzC,
    (Equal.typed (S := setting level1 fun _ => 0) head_equation headFrame.formed).1⟩⟩

/-- The right side `a'`. -/
def answerRow : TotalTerm headFrame := ⟨elemType', ⟨.var 1, Derivable.var (1 : Fin 9)⟩⟩

/-- **The base equation holds in the knowledge.** -/
theorem head_meets : (frames pkgLevels).E headPattern answerRow :=
  (equivalent_iff pkgLevels _ _).mpr
    ⟨⟨u, LevelTower.IsUniverse.sort _, .refl (Derivable.var (3 : Fin 9))⟩, head_equation⟩

/-- **The base equation, firing on the recursive call** in the state reached: it takes row `1`,
makes row `2 : a'`, and tells the equation. -/
def headFiring : Firing pkgLevels middle where
  helpers := .cons (u0Type _) (.cons (numType _) (.cons aType' (.cons wType' (.nil _))))
  taken := [1]
  read := []
  takes := [headPattern]
  reads := []
  makes := [(2, ⟨elemType', (.var 1 : Tower.Tm 9)⟩)]
  tells := [(headPattern, answerRow)]
  guards := []
  queries := []

/-- The first solution, then `A' ↦ num, k' ↦ 0, a' ↦ 2, w' ↦ tt`. -/
def headSolution : empty pkg ⟶ headFrame :=
  pair (pair (pair (pair tailSolution ⟨numC, D.num_typed⟩) ⟨zeroC, D.zero_typed⟩) ⟨two, two_typed _⟩)
    ⟨ttC, D.nil_typed D.num_typed⟩

theorem headFiring_information :
    headFiring.information =
      [((frames pkgLevels).act headFiring.helpers.weaken tailPattern,
          (frames pkgLevels).act headFiring.helpers.weaken (tailFiring.row 0)),
       ((frames pkgLevels).act headFiring.helpers.weaken tailPattern,
          (frames pkgLevels).act headFiring.helpers.weaken recursiveCall),
       (headPattern, headFiring.row 1), (headPattern, answerRow)] := rfl

theorem head_carried :
    ((frames pkgLevels).act headFiring.helpers.weaken tailPattern).reindex headSolution =
      ((frames pkgLevels).act headFiring.helpers.weaken (tailFiring.row 0)).reindex headSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem head_identifies :
    headPattern.reindex headSolution = (headFiring.row 1).reindex headSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The solution solves the information of the second firing**: the knowledge of the first,
carried along the weakening, the take equation, and the told equation. -/
theorem head_models : (frames pkgLevels).Models headSolution headFiring.information := by
  rw [headFiring_information]
  intro e member
  rcases List.mem_cons.mp member with rfl | member
  · show (frames pkgLevels).E
      (((frames pkgLevels).act headFiring.helpers.weaken tailPattern).reindex headSolution)
      (((frames pkgLevels).act headFiring.helpers.weaken (tailFiring.row 0)).reindex headSolution)
    rw [head_carried]
    exact ((frames pkgLevels).equivalence _).refl _
  rcases List.mem_cons.mp member with rfl | member
  · exact (frames pkgLevels).preserves headSolution
      ((frames pkgLevels).preserves headFiring.helpers.weaken tail_meets)
  rcases List.mem_cons.mp member with rfl | member
  · show (frames pkgLevels).E (headPattern.reindex headSolution)
      ((headFiring.row 1).reindex headSolution)
    rw [head_identifies]
    exact ((frames pkgLevels).equivalence _).refl _
  · obtain rfl := List.mem_singleton.mp member
    exact (frames pkgLevels).preserves headSolution head_meets

/-- **The base equation fires on the recursive call.** -/
theorem head_admitted : (step pkgLevels Nat).Admits headFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff headFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty pkg, headSolution, head_models⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Derivable.var (1 : Fin 9)
  · obtain rfl := List.mem_singleton.mp member
    show 1 ∈ middle.present
    decide
  · obtain rfl := List.mem_singleton.mp member
    revert inside
    show 2 ∉ middle.present
    decide
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-! ## The run -/

/-- **The run**: the recursive equation, then the base equation. -/
def lookupRun : (step pkgLevels Nat).Run start :=
  .cons tailFiring tail_admitted (.cons headFiring head_admitted (.nil _))

/-- The run's last state holds the answer row `2 : a'`. -/
theorem lookupRun_answer_row : (lookupRun.last.label 2).2.code = (.var 1 : Tower.Tm 9) := rfl

/-- **The answer**: the solution reads the answer row as `2`. -/
theorem lookupRun_answer : subst headSolution.substitution (.var 1 : Tower.Tm 9) = two := rfl

/-- **The solution solves the last knowledge**: it is a solution of the whole run. -/
theorem lookupRun_solved : (frames pkgLevels).Models headSolution lookupRun.last.knowledge :=
  head_models

/-- **The closed call is equal to its answer, in conversion**: `lookup num 2 [1, 2] (fs fz) ≡ 2`,
by the two equations of lookup at the two solutions. -/
theorem call_value : Equal pkg .nil (lookupTm numC two vec12 idx) two numC :=
  .trans ((equivalent_iff pkgLevels _ _).mp ((frames pkgLevels).preserves tailSolution tail_meets)).2
    ((equivalent_iff pkgLevels _ _).mp ((frames pkgLevels).preserves headSolution head_meets)).2

end Run

end ProgrammingOnTheStep.IndexedFamilies

#print axioms ProgrammingOnTheStep.IndexedFamilies.Run.tail_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.Run.head_admitted
#print axioms ProgrammingOnTheStep.IndexedFamilies.Run.lookupRun
#print axioms ProgrammingOnTheStep.IndexedFamilies.Run.lookupRun_answer
#print axioms ProgrammingOnTheStep.IndexedFamilies.Run.lookupRun_solved
#print axioms ProgrammingOnTheStep.IndexedFamilies.Run.call_value

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
