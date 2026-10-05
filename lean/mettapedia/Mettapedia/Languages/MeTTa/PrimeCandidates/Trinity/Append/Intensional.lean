import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Source

/-!
# What typing gives for lists and their append

The typed face of the source of `Source.lean`. Its closed expressions are read as terms of the
package of the program: the lists of numbers, `append` by its two written equations, and the
proof `append-nil` as a definition by recursion (`objectProgram`). The judgment of that package
says what is built and checked.

* **Every term is typed**: a numeral's term is a number (`NumExpr.toTerm_typed`) and a list
  expression's term is a list (`ListExpr.toTerm_typed`).
* **What runs is typed**: a step of the source is a derivable typed equality between the terms
  of the two expressions at the type of lists (`ListExpr.Step.typedEqual`), and so is a run of
  any number of steps (`ListExpr.typedEqual_of_steps`). The two equations of the source are
  equations of the judgment, and a step inside a list or inside an `append` is a congruence.
* **The theorem as a typed proof**: for every expression `e`, the constant `append-nil` of the
  program applied to the term of `e` is a closed term of the identity type
  `Id list (append e nil) e` (`appendNil_proof`).

Positive example: the terms of `one ++ two` and of `zero` before `two` are equal in the
judgment, by the two steps that run the first to the second (`one_append_two_typedEqual`).

Negative examples.

* The terms of the two values `one` and `two` are not equal in the judgment
  (`one_not_typedEqual_two`). The judgment alone does not show this; its set model does: there
  the two are lists whose first numbers are zero and the successor of zero, and these differ.
  The set model exists relative to the hypothesis `CofinalInaccessibles` (cofinally many
  inaccessible cardinals), so this negative example is proved under that hypothesis.
* Typed equality is coarser than running. `nil ++ one` and `one ++ nil` are equal in the
  judgment (`nilAppendOne_typedEqual`), but neither runs to the other
  (`nilAppendOne_not_runs_to`, `oneAppendNil_not_runs_to`): they only meet at their common
  value. Every step lowers a weight of the expressions (`ListExpr.Step.weight_lt`), and the two
  have the same weight.
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
open ZFSetTraceProducts (traceApp)

universe u

/-! ## Every term is typed -/

/-- A numeral's term is a number in the object package. -/
theorem NumExpr.toTerm_typed_object : ∀ number : NumExpr,
    CTyped objectChurch .nil number.toTerm cnum
  | .zero => czero_typed
  | .suc number => csuc_typed number.toTerm_typed_object

/-- **A numeral's term is a number** in the package of the program. -/
theorem NumExpr.toTerm_typed (number : NumExpr) : CTyped objectProgram .nil number.toTerm cnum :=
  ofAppend (ofListsAppend (ofObject number.toTerm_typed_object))

/-- The term of "a number before a list" applied to the number: a function from lists to
lists, in the package with the append. -/
theorem NumExpr.consBefore_typed (number : NumExpr) :
    CTyped objectAppend .nil (.app (.const consN) number.toTerm) (.pi clist clist) :=
  .appElim (B := .pi clist clist) (ofListsAppend consConst_typed)
    (ofListsAppend (ofObject number.toTerm_typed_object))

/-- A list expression's term is a list in the package with the append. -/
theorem ListExpr.toTerm_typed_append : ∀ e : ListExpr, CTyped objectAppend .nil e.toTerm clist
  | .nil => ofListsAppend nil_typed
  | .cons head tail => .appElim (B := clist) head.consBefore_typed tail.toTerm_typed_append
  | .append left right => cappend_typed left.toTerm_typed_append right.toTerm_typed_append

/-- **A list expression's term is a list** in the package of the program. -/
theorem ListExpr.toTerm_typed (e : ListExpr) : CTyped objectProgram .nil e.toTerm clist :=
  ofAppend e.toTerm_typed_append

/-! ## What runs is typed -/

/-- A step of the source is a typed equality in the package with the append: the two
equations are its equations, and a step inside is a congruence. -/
theorem ListExpr.Step.typedEqual_append {e e' : ListExpr} (step : ListExpr.Step e e') :
    CEqual objectAppend .nil e.toTerm e'.toTerm clist := by
  induction step with
  | appendNil right => exact append_nil_rule right.toTerm_typed_append
  | appendCons head tail right =>
    exact append_cons_rule (ofListsAppend (ofObject head.toTerm_typed_object))
      tail.toTerm_typed_append right.toTerm_typed_append
  | @consTail head tail tail' _ inside =>
    exact .appCong (B := clist) (.refl head.consBefore_typed) inside
  | @appendLeft left left' right _ inside =>
    exact .appCong (B := clist) (.appCong (B := clistFn) (.refl append_typed) inside)
      (.refl right.toTerm_typed_append)
  | @appendRight left right right' _ inside =>
    exact .appCong (B := clist)
      (.refl (.appElim (B := clistFn) append_typed left.toTerm_typed_append)) inside

/-- **What runs is typed**: a step of the source between two expressions is a derivable typed
equality between their terms at the type of lists, in the package of the program. -/
theorem ListExpr.Step.typedEqual {e e' : ListExpr} (step : ListExpr.Step e e') :
    CEqual objectProgram .nil e.toTerm e'.toTerm clist :=
  ofAppend step.typedEqual_append

/-- **A run of any number of steps is typed**: its first and last expressions have equal
terms at the type of lists. -/
theorem ListExpr.typedEqual_of_steps {e e' : ListExpr}
    (steps : Relation.ReflTransGen ListExpr.Step e e') :
    CEqual objectProgram .nil e.toTerm e'.toTerm clist := by
  induction steps with
  | refl => exact .refl e.toTerm_typed
  | tail _ step earlier => exact .trans earlier step.typedEqual

/-- Positive example: the terms of `one ++ two` and of `zero` before `two` are equal in the
judgment, by the second equation and then the first inside the list. -/
theorem one_append_two_typedEqual :
    CEqual objectProgram .nil (ListExpr.append one two).toTerm (ListExpr.cons .zero two).toTerm
      clist :=
  ListExpr.typedEqual_of_steps
    (.tail (.single (.appendCons .zero .nil two)) (.consTail (.appendNil two)))

/-! ## The theorem as a typed proof -/

/-- **The theorem as a typed proof**: for every expression `e`, the constant `append-nil` of
the program applied to the term of `e` is a closed term of `Id list (append e nil) e`. -/
theorem appendNil_proof (e : ListExpr) :
    CTyped objectProgram .nil (.app (.const appendNilN) e.toTerm) (appendNilAt e.toTerm) :=
  .appElim (B := appendNilAt (.var 0)) appendNilDef_typed e.toTerm_typed

/-- Positive example: at `one ++ two` the proof is a closed term of
`Id list (append (one ++ two) nil) (one ++ two)`. -/
example :
    CTyped objectProgram .nil (.app (.const appendNilN) (ListExpr.append one two).toTerm)
      (.id clist (cappend (ListExpr.append one two).toTerm cnil) (ListExpr.append one two).toTerm) :=
  appendNil_proof (.append one two)

/-! ## Two different values are not equal -/

/-- The model of the program keeps the values of the names it does not declare. -/
theorem programConsts_kept (h : CofinalInaccessibles.{u}) {c : DeclName}
    (notProof : c ≠ appendNilN) (notAppend : c ≠ appendN) (notList : c ≠ listN)
    (notCtor : c ∉ listCtors.map (·.1)) (notRec : c ≠ listRecN) :
    objectDeclarationsConsts h listProgram c = objectSetConsts h c := by
  show Function.update (Function.update
      (inductiveConsts (objHeads h) (objectSetConsts h) listN listMotives listCtors listRecN)
      appendN _) appendNilN _ c = _
  rw [Function.update_of_ne notProof, Function.update_of_ne notAppend]
  exact inductiveConsts_agrees (objHeads h) (objectSetConsts h) listN listMotives listCtors
    listRecN c notList notCtor notRec

/-- **The terms of the two values `one` and `two` are not equal in the judgment.** In the set
model of the program they are lists whose first numbers are zero and its successor, and no set
is its own successor. Relative to `CofinalInaccessibles`, under which the model exists. -/
theorem one_not_typedEqual_two (h : CofinalInaccessibles.{u}) :
    ¬ CEqual objectProgram .nil one.toTerm two.toTerm clist := fun equal => by
  have reading := declarations_reading (heads := objHeads h) (base := objectSetConsts h)
    objectChurch listProgram listProgram_admissible listDecl
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (objectDeclarationsConsts h listProgram) fun _ _ => rfl
  have same : ev (objHeads h) (objectDeclarationsConsts h listProgram) (ccons czero cnil)
        Fin.elim0 =
      ev (objHeads h) (objectDeclarationsConsts h listProgram) (ccons (csuc czero) cnil)
        Fin.elim0 :=
    (objectDeclarations_sound h listProgram_admissible equal Fin.elim0 (sat_nil _ _ _)).1
  have zero := objectDeclarations_sound h listProgram_admissible
    (NumExpr.toTerm_typed .zero) Fin.elim0 (sat_nil _ _ _)
  have one := objectDeclarations_sound h listProgram_admissible
    (NumExpr.toTerm_typed (.suc .zero)) Fin.elim0 (sat_nil _ _ _)
  have empty := objectDeclarations_sound h listProgram_admissible
    (ListExpr.toTerm_typed .nil) Fin.elim0 (sat_nil _ _ _)
  have zeroValue : ev (objHeads h) (objectDeclarationsConsts h listProgram) (ccons czero cnil)
        Fin.elim0 =
      ZFSetInductive.constructorValue (ZFSetInductive.nameCode consN)
        [ev (objHeads h) (objectDeclarationsConsts h listProgram) czero Fin.elim0,
          ev (objHeads h) (objectDeclarationsConsts h listProgram) cnil Fin.elim0] :=
    ctor_apply (reading.ctor (i := 1) rfl)
      (args := [ev (objHeads h) (objectDeclarationsConsts h listProgram) czero Fin.elim0,
        ev (objHeads h) (objectDeclarationsConsts h listProgram) cnil Fin.elim0])
      ((fits_iff _ _ _ _).mpr ⟨rfl, fun j below => by
      match j, below with
      | 0, _ => exact zero
      | 1, _ => exact empty⟩)
  have oneValue : ev (objHeads h) (objectDeclarationsConsts h listProgram)
        (ccons (csuc czero) cnil) Fin.elim0 =
      ZFSetInductive.constructorValue (ZFSetInductive.nameCode consN)
        [ev (objHeads h) (objectDeclarationsConsts h listProgram) (csuc czero) Fin.elim0,
          ev (objHeads h) (objectDeclarationsConsts h listProgram) cnil Fin.elim0] :=
    ctor_apply (reading.ctor (i := 1) rfl)
      (args := [ev (objHeads h) (objectDeclarationsConsts h listProgram) (csuc czero) Fin.elim0,
        ev (objHeads h) (objectDeclarationsConsts h listProgram) cnil Fin.elim0])
      ((fits_iff _ _ _ _).mpr ⟨rfl, fun j below => by
      match j, below with
      | 0, _ => exact one
      | 1, _ => exact empty⟩)
  rw [zeroValue, oneValue] at same
  have firstNumbers := List.head_eq_of_cons_eq (ZFSetInductive.constructorValue_injective.mp same).2
  have numbers : ev (objHeads h) (objectDeclarationsConsts h listProgram) (cnum : CTm Tower.Head 0)
      Fin.elim0 = ZFSet.omega := by
    show objectDeclarationsConsts h listProgram numN = ZFSet.omega
    rw [programConsts_kept h (by decide) (by decide) (by decide) (by decide) (by decide),
      setConst_num]
  have zeroNumber : ev (objHeads h) (objectDeclarationsConsts h listProgram)
      (czero : CTm Tower.Head 0) Fin.elim0 ∈ ZFSet.omega := by
    have member : ev (objHeads h) (objectDeclarationsConsts h listProgram)
        (czero : CTm Tower.Head 0) Fin.elim0 ∈
          ev (objHeads h) (objectDeclarationsConsts h listProgram) (cnum : CTm Tower.Head 0)
            Fin.elim0 := zero
    rwa [numbers] at member
  have successor : ev (objHeads h) (objectDeclarationsConsts h listProgram)
        (csuc czero : CTm Tower.Head 0) Fin.elim0 =
      insert (ev (objHeads h) (objectDeclarationsConsts h listProgram) (czero : CTm Tower.Head 0)
          Fin.elim0)
        (ev (objHeads h) (objectDeclarationsConsts h listProgram) (czero : CTm Tower.Head 0)
          Fin.elim0) := by
    show traceApp (objectDeclarationsConsts h listProgram sucN)
      (ev (objHeads h) (objectDeclarationsConsts h listProgram) (czero : CTm Tower.Head 0)
        Fin.elim0) = _
    rw [programConsts_kept h (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact suc_apply h zeroNumber
  rw [successor] at firstNumbers
  have inside := ZFSet.mem_insert
    (ev (objHeads h) (objectDeclarationsConsts h listProgram) (czero : CTm Tower.Head 0) Fin.elim0)
    (ev (objHeads h) (objectDeclarationsConsts h listProgram) (czero : CTm Tower.Head 0) Fin.elim0)
  rw [← firstNumbers] at inside
  exact ZFSet.mem_irrefl _ inside

/-! ## Typed equality is coarser than running -/

/-- A weight of a list expression that every step lowers: each side of an `append` counts
twice. -/
def ListExpr.weight : ListExpr → Nat
  | .nil => 1
  | .cons _ tail => tail.weight + 1
  | .append left right => 2 * left.weight + 2 * right.weight

/-- Every step lowers the weight. -/
theorem ListExpr.Step.weight_lt {e e' : ListExpr} (step : ListExpr.Step e e') :
    e'.weight < e.weight := by
  induction step with
  | appendNil right => simp only [ListExpr.weight]; omega
  | appendCons head tail right => simp only [ListExpr.weight]; omega
  | consTail _ inside => simp only [ListExpr.weight]; omega
  | appendLeft _ inside => simp only [ListExpr.weight]; omega
  | appendRight _ inside => simp only [ListExpr.weight]; omega

/-- A run never raises the weight. -/
theorem ListExpr.weight_le_of_steps {e e' : ListExpr}
    (steps : Relation.ReflTransGen ListExpr.Step e e') : e'.weight ≤ e.weight := by
  induction steps with
  | refl => exact le_refl _
  | tail _ step earlier => exact le_of_lt (lt_of_lt_of_le step.weight_lt earlier)

/-- A run that keeps the weight takes no step. -/
theorem ListExpr.eq_of_steps_of_weight {e e' : ListExpr}
    (steps : Relation.ReflTransGen ListExpr.Step e e') (same : e'.weight = e.weight) : e = e' := by
  cases steps with
  | refl => rfl
  | tail earlier last =>
    have below := Nat.lt_of_lt_of_le last.weight_lt (ListExpr.weight_le_of_steps earlier)
    omega

/-- `nil ++ one` runs to `one`. -/
theorem nilAppendOne_runs : Relation.ReflTransGen ListExpr.Step (.append .nil one) one :=
  .single (.appendNil one)

/-- `one ++ nil` runs to `one`. -/
theorem oneAppendNil_runs : Relation.ReflTransGen ListExpr.Step (.append one .nil) one :=
  .tail (.single (.appendCons .zero .nil .nil)) (.consTail (.appendNil .nil))

/-- `nil ++ one` and `one ++ nil` are equal in the judgment: both run to `one`. -/
theorem nilAppendOne_typedEqual :
    CEqual objectProgram .nil (ListExpr.append .nil one).toTerm (ListExpr.append one .nil).toTerm
      clist :=
  .trans (ListExpr.typedEqual_of_steps nilAppendOne_runs)
    (.symm (ListExpr.typedEqual_of_steps oneAppendNil_runs))

/-- Negative example: `nil ++ one` does not run to `one ++ nil`. -/
theorem nilAppendOne_not_runs_to :
    ¬ Relation.ReflTransGen ListExpr.Step (.append .nil one) (.append one .nil) := fun steps =>
  absurd (ListExpr.eq_of_steps_of_weight steps rfl) (by decide)

/-- Negative example: `one ++ nil` does not run to `nil ++ one`. -/
theorem oneAppendNil_not_runs_to :
    ¬ Relation.ReflTransGen ListExpr.Step (.append one .nil) (.append .nil one) := fun steps =>
  absurd (ListExpr.eq_of_steps_of_weight steps rfl) (by decide)

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append
