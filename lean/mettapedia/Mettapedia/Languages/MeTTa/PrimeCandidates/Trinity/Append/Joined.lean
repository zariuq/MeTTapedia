import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Operational
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Intensional
import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Extensional
import Mettapedia.GSLT.Core.NonFactorization

/-!
# The three faces of `append`, joined

`append` on lists of numbers has been treated three times, each on its own: run by its two
equations (`Operational.lean`), typed in the judgment of the program (`Intensional.lean`), and
defined on sets by recursion on the set of lists (`Extensional.lean`). This module joins them.

**Three maps, built separately.**
* `typing`: what runs is typed. An expression goes to its term with the proof that the term
  is a list.
* `meaning`: what is typed means a set. A typed term goes to its value in the set model of
  the program.
* `direct`: what runs reaches a set. An expression is run to its value by the two equations
  (`ListExpr.eval`), and the constructors of the value are read as sets (`constructorsSet`).
  This map uses neither the typed term nor the append on sets: a value has no `append` left.

**The triangle commutes by proof** (`meaning_typing`): the value of the typed term in the
model is the set reached by running. The proof has two independent halves. The typed term
means the set of the expression with `append` read as the append on sets (`toTerm_value`),
because the model satisfies the two typed equations and on sets those have exactly one
solution. And running does not change that set (`direct_eq_toSet`), because each equation
holds between sets. `appendTriangle` is the resulting triangle of three faces.

**The theorem `append l nil = l` on all three faces** (`appendNil_three_faces`): run, both
sides have one value; typed, there is a closed proof term; as sets, the two sides are equal.

**The triangle is not exact.** Different expressions reach one set
(`appendTriangle_loses`), and the number of steps of a run is not a function of the set
reached: the two ways of nesting three appends reach one set in five and in four steps
(`cost_not_from_set`, an instance of the general criterion in
`Mettapedia.GSLT.Core.NonFactorization`).

Negative example: read on the set side with the two arguments of every append exchanged,
the two ways to a set disagree, so those three maps form no triangle
(`exchanged_disagrees`). The agreement depends on the equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Presentation Presentation.TypedEquality.Annotated
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open CodeModel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Core.NonFactorization

universe u

/-! ## The three maps -/

/-- A closed term of the program that is a list, with its typing. -/
abbrev TypedList : Type := { t : CTm Tower.Head 0 // CTyped objectProgram .nil t clist }

/-- **What runs is typed**: the term of an expression, with the proof that it is a list. -/
def typing (e : ListExpr) : TypedList := ⟨e.toTerm, e.toTerm_typed⟩

/-- **What is typed means a set**: the value of a typed term in the set model of the
program. -/
noncomputable def meaning (h : CofinalInaccessibles.{u}) (t : TypedList) : ZFSet.{u} :=
  ev (objHeads h) (objectDeclarationsConsts h listProgram) t.1 Fin.elim0

/-- **The set of a value**: only the two constructors are read. An expression with an
`append` left in it has no such reading; the empty set, which is not a list, stands for
that. -/
noncomputable def constructorsSet : ListExpr → ZFSet.{u}
  | .nil => nilSet
  | .cons head tail => consSet head.toSet (constructorsSet tail)
  | .append _ _ => ∅

/-- **What runs reaches a set**: the expression is run to its value by the two equations, and
the constructors of the value are read as sets. -/
noncomputable def direct (e : ListExpr) : ZFSet.{u} := constructorsSet e.eval

/-- On a value the reading of the constructors is the set of the expression. -/
theorem constructorsSet_of_isValue : ∀ {e : ListExpr}, e.IsValue →
    (constructorsSet e : ZFSet.{u}) = e.toSet
  | .nil, _ => rfl
  | .cons head tail, value => by
      show consSet head.toSet (constructorsSet tail) = consSet head.toSet tail.toSet
      rw [constructorsSet_of_isValue (e := tail) value]
  | .append _ _, value => value.elim

/-! ## The triangle commutes by proof -/

/-- **Running agrees with the append defined on sets**: the set reached by running an
expression is the set of the expression, with `append` read as the append on sets. -/
theorem direct_eq_toSet (e : ListExpr) : (direct e : ZFSet.{u}) = e.toSet :=
  (constructorsSet_of_isValue (ListExpr.eval_isValue e)).trans
    (ListExpr.toSet_eq_of_steps (ListExpr.reaches_eval e)).symm

section Model

variable (h : CofinalInaccessibles.{u})

/-- **The three ways to a set agree**: the value of the typed term of an expression, in the
set model of the program, is the set reached by running the expression. -/
theorem meaning_typing (e : ListExpr) : meaning h (typing e) = direct e :=
  (toTerm_value h e).trans (direct_eq_toSet e).symm

/-- **The triangle of the three faces of `append`**: running, typing and sets, with the map
from running to sets built on its own and the commutation proved. -/
noncomputable def appendTriangle : Comparison.{0, 0, u + 1} Closed :=
  triangleOfThree
    (fun e : ULift.{u + 1} ListExpr => (ULift.up (typing e.down) : ULift.{u + 1} TypedList))
    (fun t => meaning h t.down) (fun e => direct e.down) fun e => meaning_typing h e.down

/-- **A step changes none of the three faces**: the terms are equal in the judgment, their
values in the model are equal, and the sets reached by running are equal. -/
theorem step_three_faces {e e' : ListExpr} (step : ListExpr.Step e e') :
    CEqual objectProgram .nil e.toTerm e'.toTerm clist ∧
      meaning h (typing e) = meaning h (typing e') ∧ (direct e : ZFSet.{u}) = direct e' :=
  ⟨step.typedEqual, step_value h step, congrArg constructorsSet (ListExpr.eval_step step)⟩

/-- **`append l nil = l` on the three faces**: run, both sides have one value; typed, the
constant `append-nil` of the program gives a closed proof; as sets, the two sides are
equal. -/
theorem appendNil_three_faces (e : ListExpr) :
    (ListExpr.append e .nil).eval = e.eval ∧
      CTyped objectProgram .nil (.app (.const appendNilN) e.toTerm) (appendNilAt e.toTerm) ∧
      setAppend (e.toSet : ZFSet.{u}) nilSet = e.toSet :=
  ⟨ListExpr.eval_append_nil e, appendNil_proof e, setAppend_nil_right _ e.toSet_mem⟩

/-! ## The triangle is not exact -/

/-- **Different expressions reach one set**: `one ++ two` and the value it runs to are
different expressions with one set, so the triangle loses program information. -/
theorem appendTriangle_loses : (appendTriangle h).LosesProgramInformation :=
  triangleOfThree_loses _ _ _ _ (left := ⟨.append one two⟩)
    (right := ⟨(ListExpr.append one two).eval⟩)
    (fun same => absurd (congrArg ULift.down same) (by decide))
    (by
      show (direct (ListExpr.append one two) : ZFSet.{u}) = direct (ListExpr.append one two).eval
      unfold direct
      rw [ListExpr.eval_of_isValue (ListExpr.eval_isValue _)])

end Model

/-- The two ways of nesting three appends reach one set and take different numbers of
steps. -/
noncomputable def costFiber :
    NonTrivialFiber (fun e : ListExpr => (direct e : ZFSet.{u})) ListExpr.cost where
  left := .append (.append one two) one
  right := .append one (.append two one)
  sameShadow := congrArg constructorsSet (ListExpr.eval_append_assoc one two one)
  differentValue := by decide

/-- **The cost of running is not a function of the set reached.** -/
theorem cost_not_from_set :
    ¬ Factors (fun e : ListExpr => (direct e : ZFSet.{u})) ListExpr.cost :=
  costFiber.not_factors

/-! ## The agreement depends on the equations -/

/-- The set of an expression with the two arguments of every append exchanged. -/
noncomputable def ListExpr.toSetExchanged : ListExpr → ZFSet.{u}
  | .nil => nilSet
  | .cons head tail => consSet head.toSet tail.toSetExchanged
  | .append left right => setAppend right.toSetExchanged left.toSetExchanged

/-- Negative example: **with the append read in the other order on the set side, the typed
term does not mean that set.** At `one ++ two` the typed term means the list of `0` and `1`,
and the exchanged reading gives the list of `1` and `0`. -/
theorem exchanged_disagrees (h : CofinalInaccessibles.{u}) :
    ¬ ∀ e : ListExpr, meaning h (typing e) = e.toSetExchanged := by
  intro agree
  have exchanged : ((ListExpr.append one two).toSetExchanged : ZFSet.{u}) =
      (ListExpr.append two one).toSet := rfl
  exact append_not_commutative
    ((toTerm_value h (.append one two)).symm.trans ((agree (.append one two)).trans exchanged))

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append
