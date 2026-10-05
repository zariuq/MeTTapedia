import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectAppendByEquations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetLaterArguments

/-!
# Definitions by structural recursion over the lists of the object package

The general statement is in `ObjectDatatypes.lean`: every admissible list of declarations over
the object package, datatypes and definitions by structural recursion in any order of
dependency, has a set model and is consistent (`objectDeclarations_model`,
`objectDeclarations_consistent`). This module gives single definitions over the declared
lists of numbers, each by the theorem of its form. No term is written for a function and
nothing is checked beyond the typing of the right sides and of their contexts.

**The length of a list**, by its two equations (`objectLength`):

    length nil ⟶ zero
    length (cons a as) ⟶ suc (length as)

The right sides are given with the recursive call as a hypothesis (`lengthBody`); they are
typed (`lengthBodies`), so the package has a set model and is consistent
(`objectLength_model`, `objectLength_consistent`). In its judgment each equation holds at
typed arguments (`length_nil_rule`, `length_cons_rule`), and the length of the one-element
list is one (`length_one`), also in the set model.

**The append of two lists**, with the second list taken by the right sides as an abstraction
(`objectAppendFn`):

    append nil ⟶ λ ys. ys
    append (cons a as) ⟶ λ ys. cons a (append as ys)

Its result family is the type of functions from lists to lists. The equations a programmer
writes, `append nil ys ≡ ys` and `append (cons a as) ys ≡ cons a (append as ys)`, hold in the
judgment by one further β-step each (`appendFn_nil_applied`, `appendFn_cons_applied`). So the
package in which `append` computes by those two equations (`objectAppend`,
`ObjectAppendByEquations.lean`) has a set model by this route too
(`objectAppend_model_by_recursion`, by `definition_setModel_of_derived`), without the witness
term and the hand derivations of that module.

**The written equations by the general theorem** (`SetLaterArguments.lean`): the two written
equations of the append are the instance of `laterEquations` at one later argument
(`appendWritten_equations`, by computation), their right sides are typed in their contexts
(`appendWritten_bodies`), and the package has its set model from the theorem with nothing else
supplied (`objectAppend_model_general`); in that model the list of one appended to the list
of two is the list of one and two (`append_one_two_holds_general`).

**A later argument whose type depends on the inspected list** (`objectProvedLength`): the
function `provedLength : Π (l : list). Π (q : Id list l l). num` with

    provedLength nil q ⟶ zero
    provedLength (cons a as) q ⟶ suc (provedLength as (refl as))

Its two written equations are generated from the right sides (`provedLength_equations`, by
computation): in each the proof argument has its type at the equation's constructor, and the
recursive call stands at the rest of the list with another proof. The package has a set model
and is consistent (`objectProvedLength_model`, `objectProvedLength_consistent`); in its
judgment the function at the one-element list is one (`provedLength_one`), also in the set
model.

Negative examples: a right side that is not typed in the method's context gives no instance of
the theorem: `lengthBodies` is its hypothesis, and the constant `bad` of
`ObjectAppendByEquations.lean` has an equation that is not of this form and no set model. A
written equation whose left side has the form of `laterEquations` and whose right side calls
the function at the same list, `spin nil n ⟶ suc (spin nil n)`, has no set model either
(`spin_no_setModel`): the right sides may call the function only through the hypotheses at the
recursive fields.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProducts (traceApp)

universe u

namespace CodeModel

/-! ## The lists as the datatype -/

section Lists

variable (h : CofinalInaccessibles.{u})

/-- The lists of numbers are read at every assignment that agrees with the lists' own on the
names the package with the lists declares. -/
theorem listReadings (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectLists.constantType c ≠ none → consts c = listConsts h c) :
    InductiveReading (objHeads h) consts listN listMotives listCtors listRecN :=
  declarations_reading (heads := objHeads h) (base := objectSetConsts h) objectChurch
    [.datatype listDecl] ⟨trivial, listDecl_admissible⟩ listDecl List.mem_cons_self consts agrees

end Lists

/-- The type of lists is declared in the package with the lists. -/
theorem list_declared : objectLists.constantType listN ≠ none := by
  rw [show objectLists.constantType listN = some (.head (.sort Tower.zero)) from
    sum_type_declared objectChurch lists_new]
  exact Option.some_ne_none _

/-- The closed field types of the lists are types of the package with the lists. -/
theorem lists_fieldsFormedHere : FieldsFormed objectLists listCtors :=
  fun entry member F field =>
    let ⟨w, hw, typed⟩ := lists_fieldsFormed entry member F field
    ⟨w, hw, ofObject typed⟩

/-! ## The length of a list by its equations -/

/-- The name of the defined function. -/
def lengthN : DeclName := .str .anonymous "length"

/-- **The right sides of the length**, with the recursive call as a hypothesis: zero at the
empty list, and the successor of the hypothesis at a longer one. -/
def lengthBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head (fields.length + (recPositions fields).length)
  | _, [] => czero
  | _, [.closed _, .recursive] => (csuc (.var 0) : CTm Tower.Head 3)
  | _, _ => .const .anonymous

/-- **The object package with the lists and the length defined by its two equations.** -/
abbrev objectLength :=
  withDefinition objectLists lengthN (.pi clist (cnum : CTm Tower.Head 1))
    (recursionEquations lengthN listN listCtors lengthBody)

theorem length_new : objectLists.constantType lengthN = none := by decide

/-- The result family of the length, the numbers, is a type over a list. -/
theorem lengthMotive_typed :
    CTyped objectLists (.snoc .nil clist) (cnum : CTm Tower.Head 1) cU0 :=
  ofObject cnum_typed

/-- **The right sides of the length are typed** in the contexts of their methods. -/
theorem lengthBodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped objectLists (methodCtx listN (cnum : CTm Tower.Head 1) fields
        (recPositions fields).length) (lengthBody k fields)
      ((cnum : CTm Tower.Head 1).subst fun _ =>
        ctorAt k fields.length (recPositions fields).length) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact ofObject czero_typed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectLists (CCtx.snoc (.snoc (.snoc .nil cnum) clist) cnum)
        (csuc (.var 0) : CTm Tower.Head 3) cnum := ofObject (csuc_typed (.var 0))
    exact typed
  | i + 2, entry => exact nomatch entry

section LengthModel

variable (h : CofinalInaccessibles.{u})

/-- The assignment of the model: the lists', and the length as the recursion's value. -/
noncomputable def lengthConsts : DeclName → ZFSet.{u} :=
  Function.update (listConsts h) lengthN
    (recursionValue (objHeads h) (listConsts h) listN (cnum : CTm Tower.Head 1) listCtors
      lengthBody)

/-- **The package with the length defined by its equations has a set model**, relative to
`CofinalInaccessibles`. -/
theorem objectLength_model : SetModel (objHeads h) (lengthConsts h) objectLength :=
  recursion_setModel objectLists (objectLists_baseModel h) lists_distinct.ctorsNodup
    (listReadings h) length_new
    list_declared lengthMotive_typed lists_fieldsFormedHere lengthBodies _ fun _ _ => rfl

include h in
/-- **Consistency**: no closed term of the package with the length has the type
`Π (X : U₀). X`. -/
theorem objectLength_consistent (t : CTm Tower.Head 0) :
    ¬ CTyped objectLength .nil t emptyType :=
  CDerivable.no_closed_inhabitant (objectLength_model h)
    (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (lengthConsts h)) t

end LengthModel

section LengthRules

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A derivation of the package with the lists is one of the package with the length. -/
theorem ofListsLength {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) :
    CDerivable objectLength s :=
  CDerivable.sum_left _ derivation

/-- The length applied to a term. -/
abbrev clength (l : CTm Tower.Head n) : CTm Tower.Head n := .app (.const lengthN) l

/-- **The length has its declared type.** -/
theorem length_typed : CTyped objectLength Γ (.const lengthN) (.pi clist cnum) :=
  definition_typed (withDefinition_defined objectLists length_new)
    (ofListsLength (lpiT list_typed_one num_typed_one)) (LevelTower.IsUniverse.sort _)

theorem clength_typed {l : CTm Tower.Head n} (hl : CTyped objectLength Γ l clist) :
    CTyped objectLength Γ (clength l) cnum :=
  .appElim (B := cnum) length_typed hl

/-- **The first equation**: the length of the empty list is zero. -/
theorem length_nil_rule : CEqual objectLength Γ (clength cnil) czero cnum := by
  have typed : CSubstMor objectLength (CCtx.nil : CCtx Tower.Head 0) Γ (fun i => i.elim0) :=
    fun i => i.elim0
  exact equation_holds _ (StepsWithin.sum_right _ _)
    (e := recursionEquation lengthN listN nilN [] (lengthBody nilN [])) List.mem_cons_self
    (fun i => i.elim0) typed (clength_typed (ofListsLength nil_typed))
    (ofListsLength (ofObject czero_typed))

/-- **The second equation**: the length of a longer list is the successor of the length of
the rest. -/
theorem length_cons_rule {a as : CTm Tower.Head n} (ha : CTyped objectLength Γ a cnum)
    (has : CTyped objectLength Γ as clist) :
    CEqual objectLength Γ (clength (ccons a as)) (csuc (clength as)) cnum := by
  have typed : CSubstMor objectLength (CCtx.snoc (.snoc .nil cnum) clist) Γ
      (fun i : Fin 2 => [as, a].getD i.val a) :=
    fun j => match j with
      | ⟨0, _⟩ => has
      | ⟨1, _⟩ => ha
  have consTyped : CTyped objectLength Γ (ccons a as) clist :=
    .appElim (B := clist) (.appElim (B := .pi clist clist) (ofListsLength consConst_typed) ha) has
  exact equation_holds _ (StepsWithin.sum_right _ _)
    (e := recursionEquation lengthN listN consN [.closed (.const numN), .recursive]
      (lengthBody consN [.closed (.const numN), .recursive]))
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun i => [as, a].getD i.val a) typed
    (clength_typed consTyped)
    (.appElim (B := cnum) (ofListsLength (ofObject csucConst_typed)) (clength_typed has))

/-- **The length of the one-element list is one**: the two equations. -/
theorem length_one :
    CEqual objectLength .nil (clength (ccons (csuc czero) cnil)) (csuc czero) cnum := by
  have one : CTyped objectLength .nil (csuc czero) cnum :=
    ofListsLength (ofObject (csuc_typed czero_typed))
  have first := length_cons_rule one (ofListsLength nil_typed)
  have second : CEqual objectLength .nil (clength cnil) czero cnum := length_nil_rule
  exact .trans first
    (.appCong (B := cnum) (.refl (ofListsLength (ofObject csucConst_typed))) second)

/-- In the set model the equation holds. -/
theorem length_one_holds (h : CofinalInaccessibles.{u}) :
    Holds (objHeads h) (lengthConsts h)
      (.equality .nil (clength (ccons (csuc czero) cnil)) (csuc czero) cnum) :=
  CDerivable.sound (objectLength_model h) length_one

end LengthRules

/-! ## The append of two lists, the second taken by the right sides -/

/-- **The right sides of the append**, each a function of the second list: the identity at
the empty list, and at a longer one the function that puts the first number before the
hypothesis' value. -/
def appendFnBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head (fields.length + (recPositions fields).length)
  | _, [] => .lam clist (.var 0)
  | _, [.closed _, .recursive] =>
      (.lam clist (ccons (.var 3) (.app (.var 1) (.var 0))) : CTm Tower.Head 3)
  | _, _ => .const .anonymous

/-- **The object package with the lists and the append defined by recursion on its first
list.** -/
abbrev objectAppendFn :=
  withDefinition objectLists appendN (.pi clist (clistFn : CTm Tower.Head 1))
    (recursionEquations appendN listN listCtors appendFnBody)

/-- The result family, the functions from lists to lists, is a type over a list. -/
theorem appendFnMotive_typed :
    CTyped objectLists (.snoc .nil clist) (clistFn : CTm Tower.Head 1) cU1 :=
  listFn_typed_one

/-- **The right sides of the append are typed** in the contexts of their methods. -/
theorem appendFnBodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped objectLists (methodCtx listN (clistFn : CTm Tower.Head 1) fields
        (recPositions fields).length) (appendFnBody k fields)
      ((clistFn : CTm Tower.Head 1).subst fun _ =>
        ctorAt k fields.length (recPositions fields).length) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectLists (CCtx.nil : CCtx Tower.Head 0) (.lam clist (.var 0))
        clistFn := appendBase_plain
    exact typed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectLists (CCtx.snoc (.snoc (.snoc .nil cnum) clist) clistFn)
        (.lam clist (ccons (.var 3) (.app (.var 1) (.var 0))) : CTm Tower.Head 3) clistFn :=
      .lamIntro list_typed (LevelTower.IsUniverse.sort _) listFn_typed_one
        (LevelTower.IsUniverse.sort _)
        (cons_typed (.var 3) (.appElim (B := clist) (.var 1) (.var 0)))
    exact typed
  | i + 2, entry => exact nomatch entry

section AppendFnModel

variable (h : CofinalInaccessibles.{u})

/-- The assignment of the model: the lists', and the append as the recursion's value. -/
noncomputable def appendFnConsts : DeclName → ZFSet.{u} :=
  Function.update (listConsts h) appendN
    (recursionValue (objHeads h) (listConsts h) listN (clistFn : CTm Tower.Head 1) listCtors
      appendFnBody)

/-- **The package with the append defined by recursion has a set model**, relative to
`CofinalInaccessibles`. No term was written for the function. -/
theorem objectAppendFn_model : SetModel (objHeads h) (appendFnConsts h) objectAppendFn :=
  recursion_setModel objectLists (objectLists_baseModel h) lists_distinct.ctorsNodup
    (listReadings h) append_new
    list_declared appendFnMotive_typed lists_fieldsFormedHere appendFnBodies _ fun _ _ => rfl

include h in
/-- **Consistency**: no closed term of the package has the type `Π (X : U₀). X`. -/
theorem objectAppendFn_consistent (t : CTm Tower.Head 0) :
    ¬ CTyped objectAppendFn .nil t emptyType :=
  CDerivable.no_closed_inhabitant (objectAppendFn_model h)
    (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (appendFnConsts h)) t

end AppendFnModel

section AppendFnRules

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem ofListsAppendFn {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) :
    CDerivable objectAppendFn s :=
  CDerivable.sum_left _ derivation

/-- **The append has its declared type.** -/
theorem appendFn_typed : CTyped objectAppendFn Γ (.const appendN) (.pi clist clistFn) :=
  definition_typed (withDefinition_defined objectLists append_new)
    (ofListsAppendFn appendType_formed) (LevelTower.IsUniverse.sort _)

/-- **The first equation**: the append at the empty list is the identity. -/
theorem appendFn_nil_rule :
    CEqual objectAppendFn Γ (.app (.const appendN) cnil) (.lam clist (.var 0)) clistFn := by
  have typed : CSubstMor objectAppendFn (CCtx.nil : CCtx Tower.Head 0) Γ (fun i => i.elim0) :=
    fun i => i.elim0
  exact equation_holds _ (StepsWithin.sum_right _ _)
    (e := recursionEquation appendN listN nilN [] (appendFnBody nilN [])) List.mem_cons_self
    (fun i => i.elim0) typed
    (.appElim (B := clistFn) appendFn_typed (ofListsAppendFn nil_typed))
    (ofListsAppendFn appendBase_plain)

/-- **The first equation as a programmer writes it**: the empty list appended to a list is the
list. One β-step after the rule. -/
theorem appendFn_nil_applied {ys : CTm Tower.Head n} (hys : CTyped objectAppendFn Γ ys clist) :
    CEqual objectAppendFn Γ (.app (.app (.const appendN) cnil) ys) ys clist := by
  have applied : CEqual objectAppendFn Γ (.app (.app (.const appendN) cnil) ys)
      (.app (.lam clist (.var 0)) ys) clist :=
    .appCong (B := clist) appendFn_nil_rule (.refl hys)
  have beta : CEqual objectAppendFn Γ (.app (.lam clist (.var 0)) ys) ys clist :=
    .betaPi (A := clist) (B := clist) (body := .var 0) (a := ys)
      (ofListsAppendFn listFn_typed_one) (LevelTower.IsUniverse.sort _) (.var 0) hys
  exact .trans applied beta

/-- **The second equation**: the append at a longer list is the function that puts the first
number before the append at the rest. -/
theorem appendFn_cons_rule {a as : CTm Tower.Head n} (ha : CTyped objectAppendFn Γ a cnum)
    (has : CTyped objectAppendFn Γ as clist) :
    CEqual objectAppendFn Γ (.app (.const appendN) (ccons a as))
      (.lam clist (ccons (a.rename wk)
        (.app (.app (.const appendN) (as.rename wk)) (.var 0)))) clistFn := by
  have typed : CSubstMor objectAppendFn (CCtx.snoc (.snoc .nil cnum) clist) Γ
      (fun i : Fin 2 => [as, a].getD i.val a) :=
    fun j => match j with
      | ⟨0, _⟩ => has
      | ⟨1, _⟩ => ha
  have consTyped : CTyped objectAppendFn Γ (ccons a as) clist :=
    .appElim (B := clist)
      (.appElim (B := .pi clist clist) (ofListsAppendFn consConst_typed) ha) has
  have restTyped : CTyped objectAppendFn (Γ.snoc clist)
      (.app (.app (.const appendN) (as.rename wk)) (.var 0)) clist :=
    .appElim (B := clist) (.appElim (B := clistFn) appendFn_typed
      (CTyped.rename has fun i => rfl)) (.var 0)
  have right : CTyped objectAppendFn Γ
      (.lam clist (ccons (a.rename wk)
        (.app (.app (.const appendN) (as.rename wk)) (.var 0)))) clistFn :=
    .lamIntro (ofListsAppendFn list_typed) (LevelTower.IsUniverse.sort _)
      (ofListsAppendFn listFn_typed_one) (LevelTower.IsUniverse.sort _)
      (.appElim (B := clist)
        (.appElim (B := .pi clist clist) (ofListsAppendFn consConst_typed)
          (CTyped.rename ha fun i => rfl)) restTyped)
  exact equation_holds _ (StepsWithin.sum_right _ _)
    (e := recursionEquation appendN listN consN [.closed (.const numN), .recursive]
      (appendFnBody consN [.closed (.const numN), .recursive]))
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun i => [as, a].getD i.val a) typed
    (.appElim (B := clistFn) appendFn_typed consTyped) right

/-- **The equation as a programmer writes it**: the append of a longer list and a list is the
first number before the append of the rest and the list. One β-step after the rule. -/
theorem appendFn_cons_applied {a as ys : CTm Tower.Head n} (ha : CTyped objectAppendFn Γ a cnum)
    (has : CTyped objectAppendFn Γ as clist) (hys : CTyped objectAppendFn Γ ys clist) :
    CEqual objectAppendFn Γ (.app (.app (.const appendN) (ccons a as)) ys)
      (ccons a (.app (.app (.const appendN) as) ys)) clist := by
  have rule := appendFn_cons_rule ha has
  have applied : CEqual objectAppendFn Γ (.app (.app (.const appendN) (ccons a as)) ys)
      (.app (.lam clist (ccons (a.rename wk)
        (.app (.app (.const appendN) (as.rename wk)) (.var 0)))) ys) clist :=
    .appCong (B := clist) rule (.refl hys)
  have body : CTyped objectAppendFn (Γ.snoc clist)
      (ccons (a.rename wk) (.app (.app (.const appendN) (as.rename wk)) (.var 0))) clist :=
    .appElim (B := clist)
      (.appElim (B := .pi clist clist) (ofListsAppendFn consConst_typed)
        (CTyped.rename ha fun i => rfl))
      (.appElim (B := clist) (.appElim (B := clistFn) appendFn_typed
        (CTyped.rename has fun i => rfl)) (.var 0))
  have beta : CEqual objectAppendFn Γ
      (.app (.lam clist (ccons (a.rename wk)
        (.app (.app (.const appendN) (as.rename wk)) (.var 0)))) ys)
      (CTm.inst0 ys (ccons (a.rename wk)
        (.app (.app (.const appendN) (as.rename wk)) (.var 0))))
      (CTm.inst0 ys (clist : CTm Tower.Head (n + 1))) :=
    .betaPi (ofListsAppendFn listFn_typed_one) (LevelTower.IsUniverse.sort _) body hys
  have computed : CTm.inst0 ys (ccons (a.rename wk)
      (.app (.app (.const appendN) (as.rename wk)) (.var 0))) =
      ccons a (.app (.app (.const appendN) as) ys) := by
    show CTm.app (CTm.app (.const consN) (CTm.inst0 ys (a.rename wk)))
      (CTm.app (CTm.app (.const appendN) (CTm.inst0 ys (as.rename wk))) ys) = _
    rw [CTm.inst0_rename_wk, CTm.inst0_rename_wk]
  rw [computed] at beta
  exact .trans applied beta

end AppendFnRules

/-! ## The equations a programmer writes, by this route -/

/-- The first authored equation is derivable from the definition by recursion. -/
theorem appendNil_derived :
    CEqual objectAppendFn (CCtx.snoc .nil clist)
      (.app (.app (.const appendN) cnil) (.var 0) : CTm Tower.Head 1) (.var 0) clist :=
  appendFn_nil_applied (.var 0)

/-- The second authored equation is derivable from the definition by recursion. -/
theorem appendCons_derived :
    CEqual objectAppendFn (CCtx.snoc (.snoc (.snoc .nil cnum) clist) clist)
      (.app (.app (.const appendN) (ccons (.var 2) (.var 1))) (.var 0) : CTm Tower.Head 3)
      (ccons (.var 2) (.app (.app (.const appendN) (.var 1)) (.var 0))) clist :=
  appendFn_cons_applied (.var 2) (.var 1) (.var 0)

/-- **The package in which the append computes by the two equations a programmer writes has a
set model by this route**: the equations are derivable from the definition by recursion, whose
model the theorem gives. The witness term of `ObjectAppendByEquations.lean` and its hand
derivations are not used. -/
theorem objectAppend_model_by_recursion (h : CofinalInaccessibles.{u}) :
    SetModel (objHeads h) (appendFnConsts h) objectAppend :=
  definition_setModel_of_derived append_new (objectAppendFn_model h) (by
    intro e member
    have cases : e = appendNilEquation ∨ e = appendConsEquation := by
      simpa [appendEquations] using member
    rcases cases with rfl | rfl
    · exact ⟨clist, appendNil_derived⟩
    · exact ⟨clist, appendCons_derived⟩)

/-! ## The written equations by the general theorem -/

/-- The later argument of the append: a list. -/
abbrev appendLater : CTele Tower.Head 1 2 := .cons clist .nil

/-- **The right sides of the written equations of the append**: the second list at the empty
list; at a longer one the first number before the hypothesis applied to the second list. -/
def appendWrittenBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head (appendLater.endAt (fields.length + (recPositions fields).length))
  | _, [] => (.var 0 : CTm Tower.Head 1)
  | _, [.closed _, .recursive] =>
      (ccons (.var 3) (.app (.var 1) (.var 0)) : CTm Tower.Head 4)
  | _, _ => .const .anonymous

/-- **The written equations of the append are those of `ObjectAppendByEquations.lean`**:
`append nil ys ⟶ ys` and `append (cons a as) ys ⟶ cons a (append as ys)`. -/
theorem appendWritten_equations :
    laterEquations appendN listN appendLater listCtors appendWrittenBody = appendEquations :=
  rfl

theorem appendWritten_formed {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CCtxFormed objectLists (laterCtx listN appendLater clist k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have formed : CCtxFormed objectLists (CCtx.snoc .nil clist) :=
      .snoc .nil ⟨_, LevelTower.IsUniverse.sort _, list_typed_one⟩
    exact formed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact appendStepCtx_formed
  | i + 2, entry => exact nomatch entry

theorem appendWritten_resultType {i : Nat} {k : DeclName} {fields : List CtorField}
    (_entry : listCtors[i]? = some (k, fields)) :
    CIsType objectLists (laterCtx listN appendLater clist k fields)
      (laterResult appendLater clist k fields) :=
  ⟨_, LevelTower.IsUniverse.sort _, list_typed_one⟩

/-- **The right sides of the written equations are typed** in their contexts. -/
theorem appendWritten_bodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped objectLists (laterCtx listN appendLater clist k fields) (appendWrittenBody k fields)
      (laterResult appendLater clist k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectLists (CCtx.snoc .nil clist) (.var 0 : CTm Tower.Head 1) clist :=
      .var 0
    exact typed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectLists appendStepCtx
        (ccons (.var 3) (.app (.var 1) (.var 0)) : CTm Tower.Head 4) clist :=
      cons_typed (.var 3) (.appElim (B := clist) (.var 1) (.var 0))
    exact typed
  | i + 2, entry => exact nomatch entry

/-- The assignment of the model: the lists', and the append as the recursion's value. -/
noncomputable def appendWrittenConsts (h : CofinalInaccessibles.{u}) : DeclName → ZFSet.{u} :=
  Function.update (listConsts h) appendN
    (recursionValue (objHeads h) (listConsts h) listN (appendLater.pis clist) listCtors
      fun k fields => abstractedBody appendLater k fields (appendWrittenBody k fields))

/-- **The package in which the append computes by its two written equations has a set model
by the general theorem**, relative to `CofinalInaccessibles`: the equations are the instance
of `laterEquations`, and only the typing of the two right sides is supplied. -/
theorem objectAppend_model_general (h : CofinalInaccessibles.{u}) :
    SetModel (objHeads h) (appendWrittenConsts h) objectAppend :=
  laterArguments_setModel (Ξ := appendLater) (C := clist) (body := appendWrittenBody)
    (LevelModel.sum ConvRules.objectLevels _) objectLists
    (objectLists_baseModel h) lists_distinct.ctorsNodup (listReadings h) append_new list_declared
    (motive := (listFn_typed_one : CTyped objectLists (.snoc .nil clist)
      (clistFn : CTm Tower.Head 1) cU1))
    lists_fieldsFormedHere appendWritten_formed appendWritten_resultType appendWritten_bodies _
    fun _ _ => rfl

/-- In that model the one-element list of one appended to the one-element list of two is the
list of one and two. -/
theorem append_one_two_holds_general (h : CofinalInaccessibles.{u}) :
    Holds (objHeads h) (appendWrittenConsts h)
      (.equality .nil (cappend (ccons (csuc czero) cnil) (ccons (csuc (csuc czero)) cnil))
        (ccons (csuc czero) (ccons (csuc (csuc czero)) cnil)) clist) :=
  CDerivable.sound (objectAppend_model_general h) append_one_two

/-! ## A later argument whose type depends on the inspected list -/

/-- The later argument: a proof that the inspected list is itself. -/
abbrev selfIdentity : CTele Tower.Head 1 2 := .cons (.id clist (.var 0) (.var 0)) .nil

/-- The name of the defined function. -/
def provedLengthN : DeclName := .str .anonymous "provedLength"

/-- **The right sides**: zero at the empty list; at a longer one the successor of the
hypothesis at the proof by reflexivity that the rest is itself. -/
def provedLengthBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head (selfIdentity.endAt (fields.length + (recPositions fields).length))
  | _, [] => (czero : CTm Tower.Head 1)
  | _, [.closed _, .recursive] =>
      (csuc (.app (.var 1) (.refl (.var 2))) : CTm Tower.Head 4)
  | _, _ => .const .anonymous

/-- `provedLength nil q ⟶ zero`, over a proof `q` that the empty list is itself. -/
def provedLengthNilEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil (.id clist cnil cnil)
  left := .app (.app (.const provedLengthN) cnil) (.var 0)
  right := czero

/-- `provedLength (cons a as) q ⟶ suc (provedLength as (refl as))`, over a number, a list and
a proof `q` that the longer list is itself. -/
def provedLengthConsEquation : DefiningEquation Tower.Head where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil cnum) clist)
    (.id clist (ccons (.var 1) (.var 0)) (ccons (.var 1) (.var 0)))
  left := .app (.app (.const provedLengthN) (ccons (.var 2) (.var 1))) (.var 0)
  right := csuc (.app (.app (.const provedLengthN) (.var 1)) (.refl (.var 1)))

/-- **The written equations generated from the right sides are those two**: the type of the
proof argument is taken at the constructor of each equation, and the recursive call stands at
the rest and its proof by reflexivity. -/
theorem provedLength_equations :
    laterEquations provedLengthN listN selfIdentity listCtors provedLengthBody =
      [provedLengthNilEquation, provedLengthConsEquation] :=
  rfl

/-- **The object package with the lists and `provedLength`**, of type
`Π (l : list). Π (q : Id list l l). num`, computing by its two written equations. -/
abbrev objectProvedLength :=
  withDefinition objectLists provedLengthN
    (.pi clist (.pi (.id clist (.var 0) (.var 0)) (cnum : CTm Tower.Head 2)))
    [provedLengthNilEquation, provedLengthConsEquation]

theorem provedLength_new : objectLists.constantType provedLengthN = none := by decide

/-- The identity type of a list with itself is a type. -/
theorem selfIdentity_typed {n : Nat} {Γ : CCtx Tower.Head n} {l : CTm Tower.Head n}
    (hl : CTyped objectLists Γ l clist) : CTyped objectLists Γ (.id clist l l) cU1 :=
  lraise (.idForm list_typed (LevelTower.IsUniverse.sort _) hl hl) zero_le_one

/-- The result family: functions from the proofs that a list is itself to the numbers. -/
theorem provedLengthMotive_typed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectLists (.snoc Γ clist)
      (.pi (.id clist (.var 0) (.var 0)) (cnum : CTm Tower.Head (n + 2))) cU1 :=
  lpiT (selfIdentity_typed (.var 0)) num_typed_one

theorem provedLength_formed {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CCtxFormed objectLists (laterCtx listN selfIdentity (cnum : CTm Tower.Head 2) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have formed : CCtxFormed objectLists (CCtx.snoc .nil (.id clist cnil cnil)) :=
      .snoc .nil ⟨_, LevelTower.IsUniverse.sort _, selfIdentity_typed nil_typed⟩
    exact formed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have formed : CCtxFormed objectLists
        (CCtx.snoc (.snoc (.snoc (.snoc .nil cnum) clist)
            (.pi (.id clist (.var 0) (.var 0)) cnum))
          (.id clist (ccons (.var 2) (.var 1)) (ccons (.var 2) (.var 1)))) :=
      .snoc
        (.snoc
          (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, num_typed_one⟩)
            ⟨_, LevelTower.IsUniverse.sort _, list_typed_one⟩)
          ⟨_, LevelTower.IsUniverse.sort _, provedLengthMotive_typed⟩)
        ⟨_, LevelTower.IsUniverse.sort _, selfIdentity_typed (cons_typed (.var 2) (.var 1))⟩
    exact formed
  | i + 2, entry => exact nomatch entry

theorem provedLength_resultType {i : Nat} {k : DeclName} {fields : List CtorField}
    (_entry : listCtors[i]? = some (k, fields)) :
    CIsType objectLists (laterCtx listN selfIdentity (cnum : CTm Tower.Head 2) k fields)
      (laterResult selfIdentity (cnum : CTm Tower.Head 2) k fields) :=
  ⟨_, LevelTower.IsUniverse.sort _, num_typed_one⟩

/-- **The right sides are typed** in their contexts: at a longer list the hypothesis is a
function of the proofs that the rest is itself, and it is applied to the proof by
reflexivity. -/
theorem provedLength_bodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped objectLists (laterCtx listN selfIdentity (cnum : CTm Tower.Head 2) k fields)
      (provedLengthBody k fields) (laterResult selfIdentity (cnum : CTm Tower.Head 2) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectLists (CCtx.snoc .nil (.id clist cnil cnil))
        (czero : CTm Tower.Head 1) cnum := ofObject czero_typed
    exact typed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectLists
        (CCtx.snoc (.snoc (.snoc (.snoc .nil cnum) clist)
            (.pi (.id clist (.var 0) (.var 0)) cnum))
          (.id clist (ccons (.var 2) (.var 1)) (ccons (.var 2) (.var 1))))
        (csuc (.app (.var 1) (.refl (.var 2))) : CTm Tower.Head 4) cnum :=
      .appElim (B := cnum) (ofObject csucConst_typed)
        (.appElim (B := cnum) (.var 1) (.reflIntro (.var 2)))
    exact typed
  | i + 2, entry => exact nomatch entry

section ProvedLengthModel

variable (h : CofinalInaccessibles.{u})

/-- The assignment of the model: the lists', and the function as the recursion's value. -/
noncomputable def provedLengthConsts : DeclName → ZFSet.{u} :=
  Function.update (listConsts h) provedLengthN
    (recursionValue (objHeads h) (listConsts h) listN
      (selfIdentity.pis (cnum : CTm Tower.Head 2)) listCtors
      fun k fields => abstractedBody selfIdentity k fields (provedLengthBody k fields))

/-- **The package with `provedLength` has a set model**, relative to `CofinalInaccessibles`:
the general theorem at a later argument whose type depends on the inspected list. -/
theorem objectProvedLength_model :
    SetModel (objHeads h) (provedLengthConsts h) objectProvedLength :=
  laterArguments_setModel (Ξ := selfIdentity) (C := (cnum : CTm Tower.Head 2))
    (body := provedLengthBody) (LevelModel.sum ConvRules.objectLevels _) objectLists
    (objectLists_baseModel h) lists_distinct.ctorsNodup (listReadings h) provedLength_new
    list_declared
    (motive := (provedLengthMotive_typed : CTyped objectLists (.snoc .nil clist)
      (.pi (.id clist (.var 0) (.var 0)) (cnum : CTm Tower.Head 2)) cU1))
    lists_fieldsFormedHere provedLength_formed provedLength_resultType provedLength_bodies _
    fun _ _ => rfl

include h in
/-- **Consistency**: no closed term of the package has the type `Π (X : U₀). X`. -/
theorem objectProvedLength_consistent (t : CTm Tower.Head 0) :
    ¬ CTyped objectProvedLength .nil t emptyType :=
  CDerivable.no_closed_inhabitant (objectProvedLength_model h)
    (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (provedLengthConsts h)) t

end ProvedLengthModel

section ProvedLengthRules

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A derivation of the package with the lists is one of the package with the function. -/
theorem ofListsProvedLength {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) :
    CDerivable objectProvedLength s :=
  CDerivable.sum_left _ derivation

/-- The function applied to a list and a proof. -/
abbrev cprovedLength (l q : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.const provedLengthN) l) q

/-- **The function has its declared type.** -/
theorem provedLength_typed :
    CTyped objectProvedLength Γ (.const provedLengthN)
      (.pi clist (.pi (.id clist (.var 0) (.var 0)) cnum)) :=
  definition_typed (withDefinition_defined objectLists provedLength_new)
    (ofListsProvedLength (lpiT list_typed_one provedLengthMotive_typed))
    (LevelTower.IsUniverse.sort _)

/-- The function at a list and a proof that the list is itself is a number. -/
theorem cprovedLength_typed {l q : CTm Tower.Head n} (hl : CTyped objectProvedLength Γ l clist)
    (hq : CTyped objectProvedLength Γ q (.id clist l l)) :
    CTyped objectProvedLength Γ (cprovedLength l q) cnum :=
  .appElim (B := cnum)
    (.appElim (B := .pi (.id clist (.var 0) (.var 0)) cnum) provedLength_typed hl) hq

/-- **The first equation in the judgment.** -/
theorem provedLength_nil_rule {q : CTm Tower.Head n}
    (hq : CTyped objectProvedLength Γ q (.id clist cnil cnil)) :
    CEqual objectProvedLength Γ (cprovedLength cnil q) czero cnum :=
  have typed : CSubstMor objectProvedLength (CCtx.snoc .nil (.id clist cnil cnil)) Γ
      (fun _ : Fin 1 => q) :=
    fun j => match j with
      | ⟨0, _⟩ => hq
  equation_holds _ (StepsWithin.sum_right _ _) (e := provedLengthNilEquation) List.mem_cons_self
    (fun _ => q) typed (cprovedLength_typed (ofListsProvedLength nil_typed) hq)
    (ofListsProvedLength (ofObject czero_typed))

/-- **The second equation in the judgment**: the premise for the proof argument is its typing
at the longer list. -/
theorem provedLength_cons_rule {a as q : CTm Tower.Head n}
    (ha : CTyped objectProvedLength Γ a cnum) (has : CTyped objectProvedLength Γ as clist)
    (hq : CTyped objectProvedLength Γ q (.id clist (ccons a as) (ccons a as))) :
    CEqual objectProvedLength Γ (cprovedLength (ccons a as) q)
      (csuc (cprovedLength as (.refl as))) cnum :=
  have typed : CSubstMor objectProvedLength
      (CCtx.snoc (.snoc (.snoc .nil cnum) clist)
        (.id clist (ccons (.var 1) (.var 0)) (ccons (.var 1) (.var 0)))) Γ
      (fun i : Fin 3 => [q, as, a].getD i.val a) :=
    fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => has
      | ⟨2, _⟩ => ha
  have consTyped : CTyped objectProvedLength Γ (ccons a as) clist :=
    .appElim (B := clist)
      (.appElim (B := .pi clist clist) (ofListsProvedLength consConst_typed) ha) has
  equation_holds _ (StepsWithin.sum_right _ _) (e := provedLengthConsEquation)
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun i => [q, as, a].getD i.val a) typed
    (cprovedLength_typed consTyped hq)
    (.appElim (B := cnum) (ofListsProvedLength (ofObject csucConst_typed))
      (cprovedLength_typed has (.reflIntro has)))

/-- **At the one-element list and its proof by reflexivity the function is one**: the two
equations, the second at a proof argument of another type than the first. -/
theorem provedLength_one :
    CEqual objectProvedLength .nil
      (cprovedLength (ccons czero cnil) (.refl (ccons czero cnil))) (csuc czero) cnum := by
  have zero : CTyped objectProvedLength .nil czero cnum :=
    ofListsProvedLength (ofObject czero_typed)
  have empty : CTyped objectProvedLength .nil cnil clist := ofListsProvedLength nil_typed
  have one : CTyped objectProvedLength .nil (ccons czero cnil) clist :=
    ofListsProvedLength (cons_typed (ofObject czero_typed) nil_typed)
  have first := provedLength_cons_rule zero empty (.reflIntro one)
  have second := provedLength_nil_rule (.reflIntro empty)
  exact .trans first
    (.appCong (B := cnum) (.refl (ofListsProvedLength (ofObject csucConst_typed))) second)

/-- In the set model the equation holds. -/
theorem provedLength_one_holds (h : CofinalInaccessibles.{u}) :
    Holds (objHeads h) (provedLengthConsts h)
      (.equality .nil (cprovedLength (ccons czero cnil) (.refl (ccons czero cnil)))
        (csuc czero) cnum) :=
  CDerivable.sound (objectProvedLength_model h) provedLength_one

end ProvedLengthRules

/-! ## A written equation that calls the function at the same list -/

/-- The name of a function with a written equation that no value satisfies. -/
def spinN : DeclName := .str .anonymous "spin"

/-- `spin nil n ⟶ suc (spin nil n)`: a later argument on the left, and on the right a call at
the same list, which is not a recursive field of its constructor. -/
def spinEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil cnum
  left := .app (.app (.const spinN) cnil) (.var 0)
  right := csuc (.app (.app (.const spinN) cnil) (.var 0))

/-- The package with `spin : Π (l : list). Π (n : num). num` and that equation. -/
abbrev objectSpin :=
  withDefinition objectLists spinN (.pi clist (.pi cnum cnum)) [spinEquation]

/-- Negative example: **the function `spin` with the written equation
`spin nil n ⟶ suc (spin nil n)` has no set model** at an assignment that agrees with the
object package's on the names it declares. The left side has the form of a written equation;
the right side calls the function at the list of the left side, which no hypothesis of
`laterEquations` provides. The value of `spin nil zero` would be a number equal to its own
successor, which contains it. -/
theorem spin_no_setModel (h : CofinalInaccessibles.{u}) (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectDeclared c = true → objectSetConsts h c = consts c) :
    ¬ SetModel (objHeads h) consts objectSpin := by
  intro model
  have lift : ∀ {s : CStatement Tower.Head}, CDerivable objectLists s →
      CDerivable objectSpin s := fun derivation => CDerivable.sum_left _ derivation
  have spinTyped : CTyped objectSpin .nil (.const spinN) (.pi clist (.pi cnum cnum)) :=
    definition_typed (withDefinition_defined objectLists (by decide))
      (lift (lpiT list_typed_one (lpiT num_typed_one num_typed_one)))
      (LevelTower.IsUniverse.sort _)
  have zero : CTyped objectSpin .nil czero cnum := lift (ofObject czero_typed)
  have applied : CTyped objectSpin .nil (.app (.app (.const spinN) cnil) czero) cnum :=
    .appElim (B := cnum) (.appElim (B := .pi cnum cnum) spinTyped (lift nil_typed)) zero
  have after : CTyped objectSpin .nil (csuc (.app (.app (.const spinN) cnil) czero)) cnum :=
    .appElim (B := cnum) (lift (ofObject csucConst_typed)) applied
  have typed : CSubstMor objectSpin (CCtx.snoc .nil cnum) .nil (fun _ : Fin 1 => czero) :=
    fun j => match j with
      | ⟨0, _⟩ => zero
  have equal : CEqual objectSpin .nil (.app (.app (.const spinN) cnil) czero)
      (csuc (.app (.app (.const spinN) cnil) czero)) cnum :=
    equation_holds _ (StepsWithin.sum_right _ _) (e := spinEquation) List.mem_cons_self
      (fun _ => czero) typed applied after
  have number := CDerivable.sound model applied Fin.elim0 (sat_nil _ _ _)
  have same := (CDerivable.sound model equal Fin.elim0 (sat_nil _ _ _)).1
  have numbers : ev (objHeads h) consts (cnum : CTm Tower.Head 0) Fin.elim0 = ZFSet.omega := by
    show consts numN = ZFSet.omega
    rw [← agrees numN (by decide), setConst_num]
  rw [numbers] at number
  have successor :
      ev (objHeads h) consts (csuc (.app (.app (.const spinN) cnil) czero) : CTm Tower.Head 0)
          Fin.elim0 =
        insert (ev (objHeads h) consts (.app (.app (.const spinN) cnil) czero) Fin.elim0)
          (ev (objHeads h) consts (.app (.app (.const spinN) cnil) czero) Fin.elim0) := by
    show traceApp (consts sucN) _ = _
    rw [← agrees sucN (by decide)]
    exact suc_apply h number
  rw [successor] at same
  have inside := ZFSet.mem_insert
    (ev (objHeads h) consts (.app (.app (.const spinN) cnil) czero : CTm Tower.Head 0) Fin.elim0)
    (ev (objHeads h) consts (.app (.app (.const spinN) cnil) czero : CTm Tower.Head 0) Fin.elim0)
  rw [← same] at inside
  exact ZFSet.mem_irrefl _ inside

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
