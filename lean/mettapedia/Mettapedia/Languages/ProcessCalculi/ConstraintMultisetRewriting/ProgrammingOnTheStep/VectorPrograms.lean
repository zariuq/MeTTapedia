import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.VectorPackage

/-!
# Vector programs on the dependent full step

Programs over the package `VectorPackage` (rigid naturals, vectors and finite indices), run by the
tree's dependent full step `Interface.DependentFull.step`. A program equation is a firing whose
fresh helper telescope holds the equation's variables, whose take pattern is the equation's
left side, and whose made row is its right side; admission asks the take equation, together with
the state's knowledge, to be solvable.

**Lookup by a finite index** (`lookup_admitted`). The rule
`lookup (succ n) (cons n x xs) (fz n) = x` has the dependent telescope `n : nat, x : nat,
xs : vec n`. It fires on the closed call `lookup 1 [2] (fz 0)`, and the made row is `x`, which the
solution reads as `2` (`lookup_answer`).

**Append with implicit lengths** (`append_admitted`). The state's frame holds the implicit lengths
`m k : nat` and the arguments `xs : vec m`, `ys : vec k`, and its knowledge says, heterogeneously,
`(xs : vec m) ≐ (nil : vec 0)` and `(ys : vec k) ≐ ([2] : vec 1)`; the lengths are unknowns that only
the knowledge determines. The call row is `append m k xs ys : vec (add m k)`. The rule
`append 0 p nil ys' = ys'`, with the telescope `p : nat, ys' : vec p`, fires on it; the solution sets
`m ↦ 0, k ↦ 1` (`append_solution_lengths`).

**The made row has the rule's type, not the call's.** The made row is `ys' : vec p`, while the call
has type `vec (add m k)`. Since `add` is evaluated by firings, the knowledge can never identify a
call of `add` with its value: `add 0 1 ≐ 1` is refuted outright (`add_not_in_knowledge`), as is the
recursion equation `add (succ 0) 1 ≐ succ (add 0 1)` (`add_equation_not_in_knowledge`). So types
that mention a function evaluated by firings never meet the types of its values: a type-level
function must compute in conversion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.VectorPrograms

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull
open VectorPackage

/-! ## Closed values -/

def one {n : Nat} : Tower.Tm n := succC zeroC
def two {n : Nat} : Tower.Tm n := succC one

/-- The vector `[2]` of length `1`. -/
def oneVec {n : Nat} : Tower.Tm n := consC zeroC two nilC

theorem one_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ one natC := succ_typed (zero_typed Γ)

theorem two_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ two natC := succ_typed (one_typed Γ)

theorem oneVec_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ oneVec (vecC one) :=
  .appElim (.appElim (.appElim (cons_const_typed Γ) (zero_typed Γ)) (two_typed Γ)) (nil_typed Γ)

theorem fzZero_typed {n : Nat} (Γ : Tower.Ctx n) : Typed rules Γ (fzC zeroC) (finC one) :=
  .appElim (fz_const_typed Γ) (zero_typed Γ)

/-! ## Formed types over frames -/

/-- `nat`, as a formed type over any frame. -/
def natType (Γ : Context rules) : TypeOver Γ := ⟨natC, u0, .sort _, nat_typed _⟩

/-- The frame `n : nat`. -/
abbrev ctxN : Context rules := extend (empty rules) (natType _)

/-- The frame `n : nat, x : nat`. -/
abbrev ctxNX : Context rules := extend ctxN (natType _)

/-- `vec n`, over `n : nat, x : nat`. -/
def vecOfSecond : TypeOver ctxNX := ⟨vecC (.var 1), u0, .sort _, vec_typed (.var 1)⟩

/-- The frame `n : nat, x : nat, xs : vec n`. -/
abbrev ctxNXXs : Context rules := extend ctxNX vecOfSecond

/-! ## Lookup by a finite index -/

theorem lookupRow_typed : Typed rules Ctx.nil (lookupC one oneVec (fzC zeroC)) natC := by
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (lookup_const_typed Ctx.nil)
    (one_typed Ctx.nil)) (oneVec_typed Ctx.nil)) (fzZero_typed Ctx.nil)
  exact typed

/-- The call `lookup 1 [2] (fz 0) : nat`, closed. -/
def lookupRow : TotalTerm (empty rules) := ⟨natType _, ⟨lookupC one oneVec (fzC zeroC), lookupRow_typed⟩⟩

/-- One present row, `0 : lookup 1 [2] (fz 0)`, and no knowledge. -/
def lookupState : State rules Nat := ⟨empty rules, [], {0}, fun _ => lookupRow⟩

theorem lookupPattern_typed :
    Typed rules ctxNXXs.raw (lookupC (succC (.var 2)) (consC (.var 2) (.var 1) (.var 0)) (fzC (.var 2)))
      natC := by
  have n : Typed rules ctxNXXs.raw (.var 2) natC := Derivable.var (2 : Fin 3)
  have x : Typed rules ctxNXXs.raw (.var 1) natC := Derivable.var (1 : Fin 3)
  have xs : Typed rules ctxNXXs.raw (.var 0) (vecC (.var 2)) := Derivable.var (0 : Fin 3)
  have list := Derivable.appElim (Derivable.appElim (Derivable.appElim (cons_const_typed ctxNXXs.raw) n) x) xs
  have index := Derivable.appElim (fz_const_typed ctxNXXs.raw) n
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (lookup_const_typed ctxNXXs.raw)
    (succ_typed n)) list) index
  exact typed

/-- The left side `lookup (succ n) (cons n x xs) (fz n)` of the rule, over its telescope. -/
def lookupPattern : TotalTerm ctxNXXs :=
  ⟨natType _, ⟨lookupC (succC (.var 2)) (consC (.var 2) (.var 1) (.var 0)) (fzC (.var 2)),
    lookupPattern_typed⟩⟩

/-- **The rule `lookup (succ n) (cons n x xs) (fz n) = x`, firing on row `0`**: its telescope is
`n : nat, x : nat, xs : vec n`, it takes row `0` with the left side, and makes row `1 : x`. -/
def lookupFiring : Firing levels lookupState where
  helpers := .cons (natType _) (.cons (natType _) (.cons vecOfSecond (.nil _)))
  taken := [0]
  read := []
  takes := [lookupPattern]
  reads := []
  makes := [(1, ⟨natType _, (.var 1 : Tower.Tm 3)⟩)]
  tells := []
  guards := []
  queries := []

/-- The solution `n ↦ 0, x ↦ 2, xs ↦ nil`, closed. -/
def lookupSolution : empty rules ⟶ ctxNXXs :=
  pair (pair (pair (toEmpty (empty rules)) ⟨zeroC, zero_typed _⟩) ⟨two, two_typed _⟩) ⟨nilC, nil_typed _⟩

theorem lookupFiring_information :
    lookupFiring.information = [(lookupPattern, lookupFiring.row 0)] := rfl

/-- At the solution, the left side is the call. -/
theorem lookup_identifies :
    lookupPattern.reindex lookupSolution = (lookupFiring.row 0).reindex lookupSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The rule fires on the call**: the step admits it, with a closed solution of its information. -/
theorem lookup_admitted : (step levels Nat).Admits lookupFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff lookupFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty rules, lookupSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Derivable.var (1 : Fin 3)
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [lookupFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    show (frames levels).E (lookupPattern.reindex lookupSolution) ((lookupFiring.row 0).reindex lookupSolution)
    rw [lookup_identifies]
    exact ((frames levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- The made row of the result is the helper `x : nat`. -/
theorem lookup_result_row :
    (((step levels Nat).result lookupFiring lookup_admitted).label 1).2.code = (.var 1 : Tower.Tm 3) := rfl

/-- **The answer**: the solution reads the made row as `2`. -/
theorem lookup_answer : subst lookupSolution.substitution (.var 1 : Tower.Tm 3) = two := rfl

/-! ## Append with implicit lengths -/

/-- The frame `m : nat, k : nat, xs : vec m`. -/
abbrev ctxMKX : Context rules := ctxNXXs

/-- `vec k`, over `m : nat, k : nat, xs : vec m`. -/
def vecOfSecondLast : TypeOver ctxMKX := ⟨vecC (.var 1), u0, .sort _, vec_typed (.var 1)⟩

/-- **The frame of the call**: `m : nat, k : nat, xs : vec m, ys : vec k`. -/
abbrev frame0 : Context rules := extend ctxMKX vecOfSecondLast

/-- `xs : vec m`. -/
def xsRow : TotalTerm frame0 :=
  ⟨⟨vecC (.var 3), u0, .sort _, vec_typed (.var 3)⟩, ⟨.var 1, Derivable.var (1 : Fin 4)⟩⟩

/-- `ys : vec k`. -/
def ysRow : TotalTerm frame0 :=
  ⟨⟨vecC (.var 2), u0, .sort _, vec_typed (.var 2)⟩, ⟨.var 0, Derivable.var (0 : Fin 4)⟩⟩

/-- `nil : vec 0`. -/
def nilRow : TotalTerm frame0 := ⟨⟨vecC zeroC, u0, .sort _, vec_typed (zero_typed _)⟩, ⟨nilC, nil_typed _⟩⟩

/-- `[2] : vec 1`. -/
def oneVecRow : TotalTerm frame0 := ⟨⟨vecC one, u0, .sort _, vec_typed (one_typed _)⟩, ⟨oneVec, oneVec_typed _⟩⟩

theorem callRow_typed :
    Typed rules frame0.raw (appendC (.var 3) (.var 2) (.var 1) (.var 0)) (vecC (addC (.var 3) (.var 2))) := by
  have m : Typed rules frame0.raw (.var 3) natC := Derivable.var (3 : Fin 4)
  have k : Typed rules frame0.raw (.var 2) natC := Derivable.var (2 : Fin 4)
  have xs : Typed rules frame0.raw (.var 1) (vecC (.var 3)) := Derivable.var (1 : Fin 4)
  have ys : Typed rules frame0.raw (.var 0) (vecC (.var 2)) := Derivable.var (0 : Fin 4)
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (append_const_typed frame0.raw) m) k) xs) ys
  exact typed

/-- **The call** `append m k xs ys : vec (add m k)`. -/
def callRow : TotalTerm frame0 :=
  ⟨⟨vecC (addC (.var 3) (.var 2)), u0, .sort _, vec_typed (add_typed (.var 3) (.var 2))⟩,
    ⟨appendC (.var 3) (.var 2) (.var 1) (.var 0), callRow_typed⟩⟩

/-- **The state of the call**: the lengths are unknowns; the knowledge relates the arguments to their
values, heterogeneously. -/
def callState : State rules Nat := ⟨frame0, [(xsRow, nilRow), (ysRow, oneVecRow)], {0}, fun _ => callRow⟩

/-- `vec p`, over the call's frame extended by `p : nat`. -/
def vecOfNewest : TypeOver (extend frame0 (natType _)) := ⟨vecC (.var 0), u0, .sort _, vec_typed (.var 0)⟩

/-- The rule's frame: the call's frame, `p : nat`, `ys' : vec p`. -/
abbrev appendFrame : Context rules := extend (extend frame0 (natType _)) vecOfNewest

theorem appendPattern_typed :
    Typed rules appendFrame.raw (appendC zeroC (.var 1) nilC (.var 0)) (vecC (addC zeroC (.var 1))) := by
  have p : Typed rules appendFrame.raw (.var 1) natC := Derivable.var (1 : Fin 6)
  have ys : Typed rules appendFrame.raw (.var 0) (vecC (.var 1)) := Derivable.var (0 : Fin 6)
  have typed := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (append_const_typed appendFrame.raw) (zero_typed appendFrame.raw)) p) (nil_typed appendFrame.raw)) ys
  exact typed

/-- The left side `append 0 p nil ys' : vec (add 0 p)` of the rule. -/
def appendPattern : TotalTerm appendFrame :=
  ⟨⟨vecC (addC zeroC (.var 1)), u0, .sort _, vec_typed (add_typed (zero_typed _) (.var 1))⟩,
    ⟨appendC zeroC (.var 1) nilC (.var 0), appendPattern_typed⟩⟩

/-- `vec p`, over the rule's frame. -/
def vecOfP : TypeOver appendFrame := ⟨vecC (.var 1), u0, .sort _, vec_typed (.var 1)⟩

/-- **The rule `append 0 p nil ys' = ys'`, firing on the call**: it makes row `1 : ys' : vec p`. -/
def appendFiring : Firing levels callState where
  helpers := .cons (natType _) (.cons vecOfNewest (.nil _))
  taken := [0]
  read := []
  takes := [appendPattern]
  reads := []
  makes := [(1, ⟨vecOfP, (.var 0 : Tower.Tm 6)⟩)]
  tells := []
  guards := []
  queries := []

/-- The solution `m ↦ 0, k ↦ 1, xs ↦ nil, ys ↦ [2], p ↦ 1, ys' ↦ [2]`, closed. -/
def appendSolution : empty rules ⟶ appendFrame :=
  pair (pair (pair (pair (pair (pair (toEmpty (empty rules)) ⟨zeroC, zero_typed _⟩) ⟨one, one_typed _⟩)
    ⟨nilC, nil_typed _⟩) ⟨oneVec, oneVec_typed _⟩) ⟨one, one_typed _⟩) ⟨oneVec, oneVec_typed _⟩

theorem appendFiring_information :
    appendFiring.information =
      [((frames levels).act appendFiring.helpers.weaken xsRow, (frames levels).act appendFiring.helpers.weaken nilRow),
       ((frames levels).act appendFiring.helpers.weaken ysRow,
         (frames levels).act appendFiring.helpers.weaken oneVecRow),
       (appendPattern, appendFiring.row 0)] := rfl

theorem append_xs :
    ((frames levels).act appendFiring.helpers.weaken xsRow).reindex appendSolution =
      ((frames levels).act appendFiring.helpers.weaken nilRow).reindex appendSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem append_ys :
    ((frames levels).act appendFiring.helpers.weaken ysRow).reindex appendSolution =
      ((frames levels).act appendFiring.helpers.weaken oneVecRow).reindex appendSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

theorem append_identifies :
    appendPattern.reindex appendSolution = (appendFiring.row 0).reindex appendSolution :=
  totalTerm_ext (TypeOver.ext rfl rfl) rfl

/-- **The rule fires on the call with implicit lengths.** -/
theorem append_admitted : (step levels Nat).Admits appendFiring := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff appendFiring).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun o member inside => ?_⟩,
    ⟨empty rules, appendSolution, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Derivable.var (0 : Fin 6)
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · obtain rfl := List.mem_singleton.mp member
    exact absurd (Finset.mem_singleton.mp inside) (by decide)
  · rw [appendFiring_information]
    intro e member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · show (frames levels).E (((frames levels).act appendFiring.helpers.weaken xsRow).reindex appendSolution)
        (((frames levels).act appendFiring.helpers.weaken nilRow).reindex appendSolution)
      rw [append_xs]
      exact ((frames levels).equivalence _).refl _
    · show (frames levels).E (((frames levels).act appendFiring.helpers.weaken ysRow).reindex appendSolution)
        (((frames levels).act appendFiring.helpers.weaken oneVecRow).reindex appendSolution)
      rw [append_ys]
      exact ((frames levels).equivalence _).refl _
    · show (frames levels).E (appendPattern.reindex appendSolution)
        ((appendFiring.row 0).reindex appendSolution)
      rw [append_identifies]
      exact ((frames levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **The implicit lengths**: the solution sets `m ↦ 0` and `k ↦ 1`. -/
theorem append_solution_lengths :
    appendSolution.substitution 5 = zeroC ∧ appendSolution.substitution 4 = one := ⟨rfl, rfl⟩

/-- **The made row has the rule's type**: at the solution, the made row `ys' : vec p` has type
`vec 1`, while the call it answers has type `vec (add 0 1)`. -/
theorem append_result_types :
    subst appendSolution.substitution vecOfP.code = vecC one ∧
      subst appendSolution.substitution (appendFiring.row 0).1.code = vecC (addC zeroC one) := ⟨rfl, rfl⟩

/-! ## A function evaluated by firings is invisible to the knowledge -/

/-- `n : nat` as a typed term of the empty frame. -/
def natTerm (code : Tower.Tm 0) (typed : Typed rules .nil code natC) : TotalTerm (empty rules) :=
  ⟨natType _, ⟨code, typed⟩⟩

/-- `add 0 1 ≐ 1`. -/
def addStore : EquationStore (TotalTerm (empty rules)) :=
  [(natTerm (addC zeroC one) (add_typed (zero_typed _) (one_typed _)), natTerm one (one_typed _))]

/-- `add (succ 0) 1 ≐ succ (add 0 1)`: the recursion equation of addition on its first argument. -/
def addEquationStore : EquationStore (TotalTerm (empty rules)) :=
  [(natTerm (addC one one) (add_typed (one_typed _) (one_typed _)),
    natTerm (succC (addC zeroC one)) (succ_typed (add_typed (zero_typed _) (one_typed _))))]

/-- **`add 0 1 ≐ 1` has no solution**: the two sides are spines of different rigid constants. -/
theorem add_not_in_knowledge : ¬ (frames levels).Solvable addStore :=
  ContextualDependentRigid.not_solvable_of_storeClashes (S := setting) rigid facts complete (by decide)

/-- **Nor does the recursion equation of `add`.** -/
theorem add_equation_not_in_knowledge : ¬ (frames levels).Solvable addEquationStore :=
  ContextualDependentRigid.not_solvable_of_storeClashes (S := setting) rigid facts complete (by decide)

end ProgrammingOnTheStep.VectorPrograms

#print axioms ProgrammingOnTheStep.VectorPrograms.lookup_admitted
#print axioms ProgrammingOnTheStep.VectorPrograms.lookup_answer
#print axioms ProgrammingOnTheStep.VectorPrograms.append_admitted
#print axioms ProgrammingOnTheStep.VectorPrograms.append_solution_lengths
#print axioms ProgrammingOnTheStep.VectorPrograms.append_result_types
#print axioms ProgrammingOnTheStep.VectorPrograms.add_not_in_knowledge
#print axioms ProgrammingOnTheStep.VectorPrograms.add_equation_not_in_knowledge

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
