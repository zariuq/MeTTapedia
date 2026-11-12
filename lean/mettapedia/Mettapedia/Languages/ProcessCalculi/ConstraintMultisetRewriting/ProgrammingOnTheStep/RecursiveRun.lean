import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPrograms

/-!
# A recursive program run end to end on the dependent full step

`lookup` by two pattern equations over the package `VectorPackage`:

* `lookup (succ n) (cons n x xs) (fs n i) = lookup n xs i` (the recursive equation);
* `lookup (succ n) (cons n x xs) (fz n) = x` (`VectorPrograms.lookupFiring`'s equation).

On the call `lookup 2 [1, 2] (fs 1 (fz 0))`, the recursive equation fires first (`tail_admitted`):
its made row is the recursive call `lookup n xs i`, over the fresh telescope
`n : nat, x : nat, xs : vec n, i : fin n`, and the knowledge relates the telescope to the call. Then
the second equation fires on that row in the state the first firing reached (`head_admitted`); its
information holds the first firing's knowledge, carried along the weakening. Together they form a
run of the step (`lookupRun`), whose last state holds the answer `x'`, which the solution reads as
`2` (`lookupRun_answer`).

The arguments of the recursive call are never computed: they are unknowns of the frame, determined
only by the knowledge. Each firing is admitted because the whole knowledge so far stays solvable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.RecursiveRun

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull
open VectorPackage VectorPrograms

/-! ## The call -/

/-- The vector `[1, 2]`, of length `2`. -/
def vec2 {n : Nat} : Tower.Tm n := consC one one (consC zeroC two nilC)

/-- The index `fs 1 (fz 0) : fin 2`. -/
def idx {n : Nat} : Tower.Tm n := fsC one (fzC zeroC)

theorem vec2_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ vec2 (vecC two) := by
  have inner := Derivable.appElim (Derivable.appElim (Derivable.appElim (cons_const_typed Γ) (zero_typed Γ))
    (two_typed Γ)) (nil_typed Γ)
  have outer := Derivable.appElim (Derivable.appElim (Derivable.appElim (cons_const_typed Γ) (one_typed Γ))
    (one_typed Γ)) inner
  exact outer

theorem idx_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ idx (finC two) := by
  have typed := Derivable.appElim (Derivable.appElim (fs_const_typed Γ) (one_typed Γ)) (fzZero_typed Γ)
  exact typed

theorem call_typed : Typed rules Ctx.nil (lookupC two vec2 idx) natC := by
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (lookup_const_typed Ctx.nil)
    (two_typed Ctx.nil)) (vec2_typed Ctx.nil)) (idx_typed Ctx.nil)
  exact typed

/-- The call `lookup 2 [1, 2] (fs 1 (fz 0)) : nat`. -/
def callRow : TotalTerm (empty rules) := ⟨natType _, ⟨lookupC two vec2 idx, call_typed⟩⟩

def start : State rules Nat := ⟨empty rules, [], {0}, fun _ => callRow⟩

/-! ## The recursive equation -/

/-- `fin n`, over `n : nat, x : nat, xs : vec n`. -/
def finOfThird : TypeOver ctxNXXs := ⟨finC (.var 2), u0, .sort _, fin_typed (.var 2)⟩

/-- The frame of the recursive equation: `n : nat, x : nat, xs : vec n, i : fin n`. -/
abbrev tailFrame : Context rules := extend ctxNXXs finOfThird

theorem tailPattern_typed :
    Typed rules tailFrame.raw (lookupC (succC (.var 3)) (consC (.var 3) (.var 2) (.var 1)) (fsC (.var 3) (.var 0)))
      natC := by
  have n : Typed rules tailFrame.raw (.var 3) natC := Derivable.var (3 : Fin 4)
  have x : Typed rules tailFrame.raw (.var 2) natC := Derivable.var (2 : Fin 4)
  have xs : Typed rules tailFrame.raw (.var 1) (vecC (.var 3)) := Derivable.var (1 : Fin 4)
  have i : Typed rules tailFrame.raw (.var 0) (finC (.var 3)) := Derivable.var (0 : Fin 4)
  have list := Derivable.appElim (Derivable.appElim (Derivable.appElim (cons_const_typed tailFrame.raw) n) x) xs
  have index := Derivable.appElim (Derivable.appElim (fs_const_typed tailFrame.raw) n) i
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (lookup_const_typed tailFrame.raw)
    (succ_typed n)) list) index
  exact typed

theorem recursiveCall_typed : Typed rules tailFrame.raw (lookupC (.var 3) (.var 1) (.var 0)) natC := by
  have n : Typed rules tailFrame.raw (.var 3) natC := Derivable.var (3 : Fin 4)
  have xs : Typed rules tailFrame.raw (.var 1) (vecC (.var 3)) := Derivable.var (1 : Fin 4)
  have i : Typed rules tailFrame.raw (.var 0) (finC (.var 3)) := Derivable.var (0 : Fin 4)
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (lookup_const_typed tailFrame.raw) n) xs) i
  exact typed

/-- The left side `lookup (succ n) (cons n x xs) (fs n i)`. -/
def tailPattern : TotalTerm tailFrame :=
  ⟨natType _, ⟨lookupC (succC (.var 3)) (consC (.var 3) (.var 2) (.var 1)) (fsC (.var 3) (.var 0)),
    tailPattern_typed⟩⟩

/-- **The recursive equation, firing on the call**: it makes row `1 : lookup n xs i`. -/
def tailFiring : Firing levels start where
  helpers := .cons (natType _) (.cons (natType _) (.cons vecOfSecond (.cons finOfThird (.nil _))))
  taken := [0]
  read := []
  takes := [tailPattern]
  reads := []
  makes := [(1, ⟨natType _, (lookupC (.var 3) (.var 1) (.var 0) : Tower.Tm 4)⟩)]
  tells := []
  guards := []
  queries := []

/-- `n ↦ 1, x ↦ 1, xs ↦ [2], i ↦ fz 0`. -/
def tailSolution : empty rules ⟶ tailFrame :=
  pair (pair (pair (pair (toEmpty (empty rules)) ⟨one, one_typed _⟩) ⟨one, one_typed _⟩)
    ⟨consC zeroC two nilC, oneVec_typed _⟩) ⟨fzC zeroC, fzZero_typed _⟩

theorem tailFiring_information : tailFiring.information = [(tailPattern, tailFiring.row 0)] := rfl

theorem tail_identifies : tailPattern.reindex tailSolution = (tailFiring.row 0).reindex tailSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The recursive equation fires.** -/
theorem tail_admitted : (step levels Nat).Admits tailFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff tailFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty rules, tailSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact recursiveCall_typed
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [tailFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames levels).E (tailPattern.reindex tailSolution) ((tailFiring.row 0).reindex tailSolution)
    rw [tail_identifies]
    exact ((frames levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- The state the recursive equation reaches. -/
abbrev middle : State rules Nat := (step levels Nat).result tailFiring tail_admitted

/-! ## The base equation, in the state reached -/

/-- `vec n'`, over the recursive frame extended by `n' : nat, x' : nat`. -/
def vecOfSecond' : TypeOver (extend (extend tailFrame (natType _)) (natType _)) :=
  ⟨vecC (.var 1), u0, .sort _, vec_typed (.var 1)⟩

/-- The frame of the base equation: the recursive frame, `n' : nat, x' : nat, xs' : vec n'`. -/
abbrev headFrame : Context rules := extend (extend (extend tailFrame (natType _)) (natType _)) vecOfSecond'

theorem headPattern_typed :
    Typed rules headFrame.raw (lookupC (succC (.var 2)) (consC (.var 2) (.var 1) (.var 0)) (fzC (.var 2)))
      natC := by
  have n : Typed rules headFrame.raw (.var 2) natC := Derivable.var (2 : Fin 7)
  have x : Typed rules headFrame.raw (.var 1) natC := Derivable.var (1 : Fin 7)
  have xs : Typed rules headFrame.raw (.var 0) (vecC (.var 2)) := Derivable.var (0 : Fin 7)
  have list := Derivable.appElim (Derivable.appElim (Derivable.appElim (cons_const_typed headFrame.raw) n) x) xs
  have index := Derivable.appElim (fz_const_typed headFrame.raw) n
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (lookup_const_typed headFrame.raw)
    (succ_typed n)) list) index
  exact typed

/-- The left side `lookup (succ n') (cons n' x' xs') (fz n')`. -/
def headPattern : TotalTerm headFrame :=
  ⟨natType _, ⟨lookupC (succC (.var 2)) (consC (.var 2) (.var 1) (.var 0)) (fzC (.var 2)), headPattern_typed⟩⟩

/-- **The base equation, firing on the recursive call** in the state reached: it takes row `1` and
makes row `2 : x'`. -/
def headFiring : Firing levels middle where
  helpers := .cons (natType _) (.cons (natType _) (.cons vecOfSecond' (.nil _)))
  taken := [1]
  read := []
  takes := [headPattern]
  reads := []
  makes := [(2, ⟨natType _, (.var 1 : Tower.Tm 7)⟩)]
  tells := []
  guards := []
  queries := []

/-- `n ↦ 1, x ↦ 1, xs ↦ [2], i ↦ fz 0, n' ↦ 0, x' ↦ 2, xs' ↦ nil`. -/
def headSolution : empty rules ⟶ headFrame :=
  pair (pair (pair tailSolution ⟨zeroC, zero_typed _⟩) ⟨two, two_typed _⟩) ⟨nilC, nil_typed _⟩

theorem headFiring_information :
    headFiring.information =
      [((frames levels).act headFiring.helpers.weaken tailPattern,
          (frames levels).act headFiring.helpers.weaken (tailFiring.row 0)),
        (headPattern, headFiring.row 1)] := rfl

theorem head_carried :
    ((frames levels).act headFiring.helpers.weaken tailPattern).reindex headSolution =
      ((frames levels).act headFiring.helpers.weaken (tailFiring.row 0)).reindex headSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem head_identifies : headPattern.reindex headSolution = (headFiring.row 1).reindex headSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The base equation fires on the recursive call.** -/
theorem head_admitted : (step levels Nat).Admits headFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff headFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty rules, headSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Derivable.var (1 : Fin 7)
  · obtain rfl := List.mem_singleton.mp member
    show 1 ∈ middle.present
    decide
  · obtain rfl := List.mem_singleton.mp member
    revert inside
    show 2 ∉ middle.present
    decide
  · rw [headFiring_information]
    intro e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · show (frames levels).E (((frames levels).act headFiring.helpers.weaken tailPattern).reindex headSolution)
        (((frames levels).act headFiring.helpers.weaken (tailFiring.row 0)).reindex headSolution)
      rw [head_carried]
      exact ((frames levels).equivalence _).refl _
    · show (frames levels).E (headPattern.reindex headSolution) ((headFiring.row 1).reindex headSolution)
      rw [head_identifies]
      exact ((frames levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-! ## The run -/

/-- **The run**: the recursive equation, then the base equation. -/
def lookupRun : (step levels Nat).Run start :=
  .cons tailFiring tail_admitted (.cons headFiring head_admitted (.nil _))

/-- The run's last state holds the answer row `2 : x'`. -/
theorem lookupRun_answer_row : (lookupRun.last.label 2).2.code = (.var 1 : Tower.Tm 7) := rfl

/-- **The answer**: the solution reads the answer row as `2`. -/
theorem lookupRun_answer : subst headSolution.substitution (.var 1 : Tower.Tm 7) = two := rfl

/-- **The solution solves the last knowledge**: it is a solution of the whole run. -/
theorem lookupRun_solved : (frames levels).Models headSolution lookupRun.last.knowledge := by
  intro e member
  have inside : e ∈ headFiring.information := member
  rw [headFiring_information] at inside
  rcases List.mem_cons.mp inside with rfl | rest
  · show (frames levels).E (((frames levels).act headFiring.helpers.weaken tailPattern).reindex headSolution)
      (((frames levels).act headFiring.helpers.weaken (tailFiring.row 0)).reindex headSolution)
    rw [head_carried]
    exact ((frames levels).equivalence _).refl _
  · obtain rfl := List.mem_singleton.mp rest
    show (frames levels).E (headPattern.reindex headSolution) ((headFiring.row 1).reindex headSolution)
    rw [head_identifies]
    exact ((frames levels).equivalence _).refl _

end ProgrammingOnTheStep.RecursiveRun

#print axioms ProgrammingOnTheStep.RecursiveRun.tail_admitted
#print axioms ProgrammingOnTheStep.RecursiveRun.head_admitted
#print axioms ProgrammingOnTheStep.RecursiveRun.lookupRun
#print axioms ProgrammingOnTheStep.RecursiveRun.lookupRun_answer
#print axioms ProgrammingOnTheStep.RecursiveRun.lookupRun_solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
