import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectDatatypes
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDefinitions
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.TelescopeAbstractions

/-!
# A function defined by pattern equations: the append of two lists

Over the object package with the lists of numbers, `append : list → list → list` is defined by
its two pattern equations,

    append nil ys ⟶ ys
    append (cons a as) ys ⟶ cons a (append as ys)

as a programmer writes it. The second equation calls `append` again, at the rest of the list
and with the second argument passed along. The constant computes by these equations
(`objectAppend`, a `withDefinition`); an instance requires the typings of its variables.

**The witness** (`appendTerm`): the function built from the recursor of the lists at the
motive "a function from lists to lists", with the identity at the empty list and, at a longer
list, the function that puts the first number before the result. It has the type of `append`
in the package with the lists (`appendTerm_typed`), and it satisfies both equations there
(`appendTerm_nil`, `appendTerm_cons`): the recursor's computation rules and β-steps, the four
of the step by β over its telescope (`lamsCtx_apply`). So the definition is satisfied by a
term (`append_satisfied`).

**Consequences**, relative to `CofinalInaccessibles`: the package with `append` has a set
model (`objectAppend_model`) and is consistent (`objectAppend_consistent`). In its judgment
`append` has its type (`append_typed`), each equation holds at typed arguments
(`append_nil_rule`, `append_cons_rule`), and the one-element list of one appended to the
one-element list of two is the list of one and two (`append_one_two`), also in the set model
(`append_one_two_holds`).

Negative example: the constant `bad : num` with the equation `bad ⟶ suc bad`. No number is its
own successor, so the package with it has no set model at any assignment that agrees with the
object package's on its names (`bad_no_setModel`): an equation without a solution is not
admitted by this criterion.
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

/-! ## The witness: append by the recursor -/

section Witness

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The type of functions from lists to lists. -/
abbrev clistFn : CTm Tower.Head n := .pi clist clist

/-- The motive: every list gives a function from lists to lists. -/
abbrev appendMotive : CTm Tower.Head n := .lam clist clistFn

/-- The value at the empty list: the identity. -/
abbrev appendBase : CTm Tower.Head n := .lam clist (.var 0)

/-- The step: from a number, a list and the function at that list, the function that puts
the number before the result. -/
abbrev appendStep : CTm Tower.Head n :=
  .lam cnum (.lam clist (.lam clistFn (.lam clist (ccons (.var 3) (.app (.var 1) (.var 0))))))

/-- The recursor of the lists at the motive, the base and the step. -/
abbrev appendRec (l : CTm Tower.Head n) : CTm Tower.Head n :=
  listRecApp appendMotive appendBase appendStep l

/-- **The witness**: append by recursion on the first list. -/
abbrev appendTerm : CTm Tower.Head n := .lam clist (appendRec (.var 0))

theorem listFn_typed_one : CTyped objectLists Γ clistFn cU1 := lpiT list_typed_one list_typed_one

theorem appendMotive_typed : CTyped objectLists Γ appendMotive (.pi clist cU1) :=
  .lamIntro (u := LevelTower.Head.sort (.succ (.succ Tower.zero)))
    (w := LevelTower.Head.sort Tower.zero) list_typed (LevelTower.IsUniverse.sort _)
    motiveType_formed (LevelTower.IsUniverse.sort _) listFn_typed_one

/-- The motive at a list is the type of functions from lists to lists. -/
theorem appendMotive_at {l : CTm Tower.Head n} (hl : CTyped objectLists Γ l clist) :
    CEqual objectLists Γ (.app appendMotive l) clistFn cU1 :=
  .betaPi (A := clist) (B := cU1) (body := clistFn) (a := l)
    (u := LevelTower.Head.sort (.succ (.succ Tower.zero))) motiveType_formed
    (LevelTower.IsUniverse.sort _) listFn_typed_one hl

theorem appendBase_plain : CTyped objectLists Γ appendBase clistFn :=
  .lamIntro list_typed (LevelTower.IsUniverse.sort _) listFn_typed_one
    (LevelTower.IsUniverse.sort _) (.var 0)

theorem appendBase_typed : CTyped objectLists Γ appendBase (.app appendMotive cnil) :=
  .conv appendBase_plain (.symm (appendMotive_at nil_typed)) (LevelTower.IsUniverse.sort _)

/-- The step at the plain function type. -/
theorem appendStep_plain :
    CTyped objectLists Γ appendStep (.pi cnum (.pi clist (.pi clistFn clistFn))) := by
  have inner : CTyped objectLists (.snoc (.snoc Γ cnum) clist) (.pi clistFn clistFn) cU1 :=
    lpiT listFn_typed_one listFn_typed_one
  have middle : CTyped objectLists (.snoc Γ cnum) (.pi clist (.pi clistFn clistFn)) cU1 :=
    lpiT list_typed_one inner
  have outer : CTyped objectLists Γ (.pi cnum (.pi clist (.pi clistFn clistFn))) cU1 :=
    lpiT num_typed_one middle
  exact .lamIntro (ofObject cnum_typed) (LevelTower.IsUniverse.sort _) outer
    (LevelTower.IsUniverse.sort _)
    (.lamIntro list_typed (LevelTower.IsUniverse.sort _) middle (LevelTower.IsUniverse.sort _)
      (.lamIntro listFn_typed_one (LevelTower.IsUniverse.sort _) inner
        (LevelTower.IsUniverse.sort _)
        (.lamIntro list_typed (LevelTower.IsUniverse.sort _) listFn_typed_one
          (LevelTower.IsUniverse.sort _)
          (cons_typed (.var 3) (.appElim (B := clist) (.var 1) (.var 0))))))

/-- The type of the step over the motive is the plain function type. -/
theorem appendStepType_eq :
    CEqual objectLists Γ (.pi cnum (.pi clist (.pi clistFn clistFn))) (listStepType appendMotive)
      (CU (.max (.succ Tower.zero) (.max (.succ Tower.zero)
        (.max (.succ Tower.zero) (.succ Tower.zero))))) := by
  have atList : CEqual objectLists (.snoc (.snoc Γ cnum) clist) clistFn
      (.app (.lam clist clistFn) (.var 0)) cU1 := .symm (appendMotive_at (.var 0))
  have atCons : CEqual objectLists (.snoc (.snoc (.snoc Γ cnum) clist) clistFn) clistFn
      (.app (.lam clist clistFn) (ccons (.var 2) (.var 1))) cU1 :=
    .symm (appendMotive_at (cons_typed (.var 2) (.var 1)))
  exact .piCong (.refl num_typed_one) (LevelTower.IsUniverse.sort _)
    (.piCong (.refl list_typed_one) (LevelTower.IsUniverse.sort _)
      (.piCong atList (LevelTower.IsUniverse.sort _) atCons (LevelTower.IsUniverse.sort _)
        (.sorts _ _))
      (LevelTower.IsUniverse.sort _) (.sorts _ _))
    (LevelTower.IsUniverse.sort _) (.sorts _ _)

theorem appendStep_typed : CTyped objectLists Γ appendStep (listStepType appendMotive) :=
  .conv appendStep_plain appendStepType_eq (LevelTower.IsUniverse.sort _)

/-- The recursor at a list is a function from lists to lists. -/
theorem appendRec_typed {l : CTm Tower.Head n} (hl : CTyped objectLists Γ l clist) :
    CTyped objectLists Γ (appendRec l) clistFn :=
  .conv (listRec_typed appendMotive_typed appendBase_typed appendStep_typed hl)
    (appendMotive_at hl) (LevelTower.IsUniverse.sort _)

/-- The type of `append` is a type. -/
theorem appendType_formed : CTyped objectLists Γ (.pi clist clistFn) cU1 :=
  lpiT list_typed_one listFn_typed_one

/-- **The witness has the type of `append`.** -/
theorem appendTerm_typed : CTyped objectLists Γ appendTerm (.pi clist clistFn) :=
  .lamIntro list_typed (LevelTower.IsUniverse.sort _) appendType_formed
    (LevelTower.IsUniverse.sort _) (appendRec_typed (.var 0))

/-- The witness applied to a list is the recursor at the list: one β-step. -/
theorem appendTerm_apply {xs : CTm Tower.Head n} (hxs : CTyped objectLists Γ xs clist) :
    CEqual objectLists Γ (.app appendTerm xs) (appendRec xs) clistFn :=
  .betaPi (A := clist) (B := clistFn) (body := appendRec (.var 0)) (a := xs) appendType_formed
    (LevelTower.IsUniverse.sort _) (appendRec_typed (.var 0)) hxs

/-- The context of a number, a list, a function from lists to lists, and a list. -/
abbrev appendStepCtx : CCtx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil cnum) clist) clistFn) clist

/-- That context is formed. -/
theorem appendStepCtx_formed : CCtxFormed objectLists appendStepCtx :=
  .snoc
    (.snoc
      (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, num_typed_one⟩)
        ⟨_, LevelTower.IsUniverse.sort _, list_typed_one⟩)
      ⟨_, LevelTower.IsUniverse.sort _, listFn_typed_one⟩)
    ⟨_, LevelTower.IsUniverse.sort _, list_typed_one⟩

/-- The step applied to a number, a list, a function and a list is the number before the
function's value: β over the telescope of the step's four arguments. -/
theorem appendStep_apply {a as r ys : CTm Tower.Head n} (ha : CTyped objectLists Γ a cnum)
    (has : CTyped objectLists Γ as clist) (hr : CTyped objectLists Γ r clistFn)
    (hys : CTyped objectLists Γ ys clist) :
    CEqual objectLists Γ (.app (.app (.app (.app appendStep a) as) r) ys)
      (ccons a (.app r ys)) clist :=
  lamsCtx_apply (LevelModel.sum ConvRules.objectLevels _) appendStepCtx_formed (C := clist)
    ⟨_, LevelTower.IsUniverse.sort _, list_typed_one⟩
    (body := ccons (.var 3) (.app (.var 1) (.var 0)))
    (cons_typed (.var 3) (.appElim (B := clist) (.var 1) (.var 0)))
    (fun i => [ys, r, as, a].getD i.val a)
    (fun j => match j with
      | ⟨0, _⟩ => hys
      | ⟨1, _⟩ => hr
      | ⟨2, _⟩ => has
      | ⟨3, _⟩ => ha)

/-- **The witness satisfies the first equation**: at the empty list it gives the second
list. -/
theorem appendTerm_nil {ys : CTm Tower.Head n} (hys : CTyped objectLists Γ ys clist) :
    CEqual objectLists Γ (.app (.app appendTerm cnil) ys) ys clist := by
  have atNil : CEqual objectLists Γ (appendRec cnil) appendBase clistFn :=
    .convEq (listRec_nil appendMotive_typed appendBase_typed appendStep_typed)
      (appendMotive_at nil_typed) (LevelTower.IsUniverse.sort _)
  have function : CEqual objectLists Γ (.app appendTerm cnil) appendBase clistFn :=
    .trans (appendTerm_apply nil_typed) atNil
  have applied : CEqual objectLists Γ (.app (.app appendTerm cnil) ys) (.app appendBase ys)
      clist := .appCong (B := clist) function (.refl hys)
  have beta : CEqual objectLists Γ (.app appendBase ys) ys clist :=
    .betaPi (A := clist) (B := clist) (body := .var 0) (a := ys) listFn_typed_one
      (LevelTower.IsUniverse.sort _) (.var 0) hys
  exact .trans applied beta

/-- **The witness satisfies the second equation**: at a longer list it gives the first number
before its value at the rest. -/
theorem appendTerm_cons {a as ys : CTm Tower.Head n} (ha : CTyped objectLists Γ a cnum)
    (has : CTyped objectLists Γ as clist) (hys : CTyped objectLists Γ ys clist) :
    CEqual objectLists Γ (.app (.app appendTerm (ccons a as)) ys)
      (ccons a (.app (.app appendTerm as) ys)) clist := by
  have atCons : CEqual objectLists Γ (appendRec (ccons a as))
      (.app (.app (.app appendStep a) as) (appendRec as)) clistFn :=
    .convEq (listRec_cons appendMotive_typed appendBase_typed appendStep_typed ha has)
      (appendMotive_at (cons_typed ha has)) (LevelTower.IsUniverse.sort _)
  have function : CEqual objectLists Γ (.app appendTerm (ccons a as))
      (.app (.app (.app appendStep a) as) (appendRec as)) clistFn :=
    .trans (appendTerm_apply (cons_typed ha has)) atCons
  have applied : CEqual objectLists Γ (.app (.app appendTerm (ccons a as)) ys)
      (.app (.app (.app (.app appendStep a) as) (appendRec as)) ys) clist :=
    .appCong (B := clist) function (.refl hys)
  have computed : CEqual objectLists Γ
      (.app (.app (.app (.app appendStep a) as) (appendRec as)) ys)
      (ccons a (.app (appendRec as) ys)) clist :=
    appendStep_apply ha has (appendRec_typed has) hys
  have rest : CEqual objectLists Γ (.app (appendRec as) ys) (.app (.app appendTerm as) ys)
      clist := .appCong (B := clist) (.symm (appendTerm_apply has)) (.refl hys)
  have before : CTyped objectLists Γ (.app (.const consN) a) clistFn :=
    .appElim (B := .pi clist clist) consConst_typed ha
  have back : CEqual objectLists Γ (ccons a (.app (appendRec as) ys))
      (ccons a (.app (.app appendTerm as) ys)) clist :=
    .appCong (B := clist) (.refl before) rest
  exact .trans applied (.trans computed back)

end Witness

/-! ## The definition by pattern equations -/

/-- The name of the defined function. -/
def appendN : DeclName := .str .anonymous "append"

/-- The type of `append`. -/
abbrev appendType : CTm Tower.Head 0 := .pi clist clistFn

/-- `append nil ys ⟶ ys`, over a list `ys`. -/
def appendNilEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil clist
  left := .app (.app (.const appendN) cnil) (.var 0)
  right := .var 0

/-- `append (cons a as) ys ⟶ cons a (append as ys)`, over a number `a` and lists `as`, `ys`. -/
def appendConsEquation : DefiningEquation Tower.Head where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil cnum) clist) clist
  left := .app (.app (.const appendN) (ccons (.var 2) (.var 1))) (.var 0)
  right := ccons (.var 2) (.app (.app (.const appendN) (.var 1)) (.var 0))

/-- The two pattern equations of `append`. -/
def appendEquations : List (DefiningEquation Tower.Head) := [appendNilEquation, appendConsEquation]

/-- **The object package with the lists and `append` defined by its pattern equations.** -/
abbrev objectAppend :=
  withDefinition objectLists appendN appendType appendEquations

/-- The name is new to the package with the lists. -/
theorem append_new : objectLists.constantType appendN = none := by decide

/-- The witness lifted into a context is the witness there. -/
theorem liftClosed_appendTerm {m : Nat} :
    ((appendTerm : CTm Tower.Head 0).liftClosed : CTm Tower.Head m) = appendTerm := rfl

/-- The first equation with the witness in place of `append`. -/
theorem appendNil_satisfied :
    CEqual objectLists
      ((CCtx.snoc .nil clist : CCtx Tower.Head 1).instConsts (defineBy appendN appendTerm))
      ((.app (.app (.const appendN) cnil) (.var 0) : CTm Tower.Head 1).instConsts
        (defineBy appendN appendTerm))
      ((.var 0 : CTm Tower.Head 1).instConsts (defineBy appendN appendTerm)) clist := by
  have listType : ∀ {m : Nat}, (CTm.const listN : CTm Tower.Head m).instConsts
      (defineBy appendN appendTerm) = .const listN :=
    instConsts_other appendTerm (by decide)
  have nilTerm : ∀ {m : Nat}, (CTm.const nilN : CTm Tower.Head m).instConsts
      (defineBy appendN appendTerm) = .const nilN :=
    instConsts_other appendTerm (by decide)
  show CEqual objectLists
    (CCtx.snoc .nil ((CTm.const listN).instConsts (defineBy appendN appendTerm)))
    (CTm.app (CTm.app ((CTm.const appendN).instConsts (defineBy appendN appendTerm))
      ((CTm.const nilN).instConsts (defineBy appendN appendTerm))) (.var 0))
    (.var 0) clist
  rw [listType, nilTerm, instConsts_defined, liftClosed_appendTerm]
  exact appendTerm_nil (.var 0)

/-- The second equation with the witness in place of `append`. -/
theorem appendCons_satisfied :
    CEqual objectLists
      ((CCtx.snoc (.snoc (.snoc .nil cnum) clist) clist : CCtx Tower.Head 3).instConsts
        (defineBy appendN appendTerm))
      ((.app (.app (.const appendN) (ccons (.var 2) (.var 1))) (.var 0) :
        CTm Tower.Head 3).instConsts (defineBy appendN appendTerm))
      ((ccons (.var 2) (.app (.app (.const appendN) (.var 1)) (.var 0)) :
        CTm Tower.Head 3).instConsts (defineBy appendN appendTerm)) clist := by
  have listType : ∀ {m : Nat}, (CTm.const listN : CTm Tower.Head m).instConsts
      (defineBy appendN appendTerm) = .const listN :=
    instConsts_other appendTerm (by decide)
  have numType : ∀ {m : Nat}, (CTm.const numN : CTm Tower.Head m).instConsts
      (defineBy appendN appendTerm) = .const numN :=
    instConsts_other appendTerm (by decide)
  have consTerm : ∀ {m : Nat}, (CTm.const consN : CTm Tower.Head m).instConsts
      (defineBy appendN appendTerm) = .const consN :=
    instConsts_other appendTerm (by decide)
  show CEqual objectLists
    (CCtx.snoc (.snoc (.snoc .nil ((CTm.const numN).instConsts (defineBy appendN appendTerm)))
      ((CTm.const listN).instConsts (defineBy appendN appendTerm)))
      ((CTm.const listN).instConsts (defineBy appendN appendTerm)))
    (CTm.app (CTm.app ((CTm.const appendN).instConsts (defineBy appendN appendTerm))
      (CTm.app (CTm.app ((CTm.const consN).instConsts (defineBy appendN appendTerm)) (.var 2))
        (.var 1))) (.var 0))
    (CTm.app (CTm.app ((CTm.const consN).instConsts (defineBy appendN appendTerm)) (.var 2))
      (CTm.app (CTm.app ((CTm.const appendN).instConsts (defineBy appendN appendTerm)) (.var 1))
        (.var 0))) clist
  rw [numType, listType, listType, consTerm, instConsts_defined, liftClosed_appendTerm]
  exact appendTerm_cons (.var 2) (.var 1) (.var 0)

/-- **The definition is satisfied by the witness**: with the witness in place of `append`, both
equations hold in the package with the lists. -/
theorem append_satisfied : SatisfiedBy objectLists appendN appendEquations appendTerm := by
  intro e member
  have cases : e = appendNilEquation ∨ e = appendConsEquation := by
    simpa [appendEquations] using member
  rcases cases with rfl | rfl
  · exact ⟨clist, appendNil_satisfied⟩
  · exact ⟨clist, appendCons_satisfied⟩

/-! ## The set model -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- The package with the lists has a set model at every assignment that agrees with its own
on the names it declares. -/
theorem objectLists_baseModel (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectLists.constantType c ≠ none → consts c = listConsts h c) :
    SetModel (objHeads h) consts objectLists :=
  declarations_setModel ConvRules.objectLevels objectChurch (object_baseModel h)
    [.datatype listDecl] ⟨trivial, listDecl_admissible⟩
    (objectDeclarations_universes h (ds := [.datatype listDecl]) ⟨trivial, listDecl_admissible⟩)
    consts
    agrees

/-- The assignment of the model: the lists', and `append` as the value of the witness. -/
noncomputable def appendConsts : DeclName → ZFSet.{u} :=
  Function.update (listConsts h) appendN
    (ev (objHeads h) (listConsts h) (appendTerm : CTm Tower.Head 0) Fin.elim0)

/-- **The package with `append` defined by its pattern equations has a set model**, relative
to `CofinalInaccessibles`. -/
theorem objectAppend_model : SetModel (objHeads h) (appendConsts h) objectAppend :=
  definition_setModel_read objectLists (objectLists_baseModel h) append_new appendTerm_typed
    append_satisfied

/-- **Soundness**: every derivable statement of the package holds in the model. -/
theorem objectAppend_sound {s : CStatement Tower.Head} (derivation : CDerivable objectAppend s) :
    Holds (objHeads h) (appendConsts h) s :=
  CDerivable.sound (objectAppend_model h) derivation

include h in
/-- **Consistency**, relative to `CofinalInaccessibles`: no closed term of the package with
`append` has the type `Π (X : U₀). X`. -/
theorem objectAppend_consistent (t : CTm Tower.Head 0) :
    ¬ CTyped objectAppend .nil t emptyType :=
  CDerivable.no_closed_inhabitant (objectAppend_model h)
    (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (appendConsts h)) t

end Model

/-! ## `append` in the judgment -/

section Rules

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A derivation of the package with the lists is one of the package with `append`. -/
theorem ofListsAppend {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) :
    CDerivable objectAppend s :=
  CDerivable.sum_left _ derivation

/-- `append` applied to two terms. -/
abbrev cappend (xs ys : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.const appendN) xs) ys

/-- **`append` has its declared type.** -/
theorem append_typed : CTyped objectAppend Γ (.const appendN) (.pi clist clistFn) :=
  definition_typed (withDefinition_defined objectLists append_new)
    (ofListsAppend appendType_formed) (LevelTower.IsUniverse.sort _)

/-- The append of two lists is a list. -/
theorem cappend_typed {xs ys : CTm Tower.Head n} (hxs : CTyped objectAppend Γ xs clist)
    (hys : CTyped objectAppend Γ ys clist) : CTyped objectAppend Γ (cappend xs ys) clist :=
  .appElim (B := clist) (.appElim (B := clistFn) append_typed hxs) hys

/-- **The first equation in the judgment**: the empty list appended to a list is the list. -/
theorem append_nil_rule {ys : CTm Tower.Head n} (hys : CTyped objectAppend Γ ys clist) :
    CEqual objectAppend Γ (cappend cnil ys) ys clist :=
  have typed : CSubstMor objectAppend (CCtx.snoc .nil clist) Γ (fun _ : Fin 1 => ys) :=
    fun j => match j with
      | ⟨0, _⟩ => hys
  equation_holds _ (StepsWithin.sum_right _ _) (e := appendNilEquation) List.mem_cons_self
    (fun _ => ys) typed (cappend_typed (ofListsAppend nil_typed) hys) hys

/-- **The second equation in the judgment**: a longer list appended to a list is its first
number before the rest appended to the list. -/
theorem append_cons_rule {a as ys : CTm Tower.Head n} (ha : CTyped objectAppend Γ a cnum)
    (has : CTyped objectAppend Γ as clist) (hys : CTyped objectAppend Γ ys clist) :
    CEqual objectAppend Γ (cappend (ccons a as) ys) (ccons a (cappend as ys)) clist :=
  have typed : CSubstMor objectAppend (CCtx.snoc (.snoc (.snoc .nil cnum) clist) clist) Γ
      (fun i : Fin 3 => [ys, as, a].getD i.val a) :=
    fun j => match j with
      | ⟨0, _⟩ => hys
      | ⟨1, _⟩ => has
      | ⟨2, _⟩ => ha
  equation_holds _ (StepsWithin.sum_right _ _) (e := appendConsEquation)
    (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun i => [ys, as, a].getD i.val a) typed
    (cappend_typed
      (.appElim (B := clist) (.appElim (B := .pi clist clist) (ofListsAppend consConst_typed) ha)
        has) hys)
    (.appElim (B := clist) (.appElim (B := .pi clist clist) (ofListsAppend consConst_typed) ha)
      (cappend_typed has hys))

/-- **The list of one appended to the list of two is the list of one and two**: the two
equations, one after the other. -/
theorem append_one_two :
    CEqual objectAppend .nil
      (cappend (ccons (csuc czero) cnil) (ccons (csuc (csuc czero)) cnil))
      (ccons (csuc czero) (ccons (csuc (csuc czero)) cnil)) clist := by
  have one : CTyped objectAppend .nil (csuc czero) cnum :=
    ofListsAppend (ofObject (csuc_typed czero_typed))
  have two : CTyped objectAppend .nil (csuc (csuc czero)) cnum :=
    ofListsAppend (ofObject (csuc_typed (csuc_typed czero_typed)))
  have nil : CTyped objectAppend .nil cnil clist := ofListsAppend nil_typed
  have twoList : CTyped objectAppend .nil (ccons (csuc (csuc czero)) cnil) clist :=
    ofListsAppend (cons_typed (ofObject (csuc_typed (csuc_typed czero_typed))) nil_typed)
  have first := append_cons_rule one nil twoList
  have second := append_nil_rule twoList
  have before : CTyped objectAppend .nil (.app (.const consN) (csuc czero)) (.pi clist clist) :=
    .appElim (B := .pi clist clist) (ofListsAppend consConst_typed) one
  exact .trans first (.appCong (B := clist) (.refl before) second)

/-- In the set model the equation holds. -/
theorem append_one_two_holds (h : CofinalInaccessibles.{u}) :
    Holds (objHeads h) (appendConsts h)
      (.equality .nil (cappend (ccons (csuc czero) cnil) (ccons (csuc (csuc czero)) cnil))
        (ccons (csuc czero) (ccons (csuc (csuc czero)) cnil)) clist) :=
  objectAppend_sound h append_one_two

end Rules

/-! ## An equation without a solution -/

/-- The name of a constant with an equation that no number satisfies. -/
def badN : DeclName := .str .anonymous "bad"

/-- `bad ⟶ suc bad`. -/
def badEquation : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := .const badN
  right := csuc (.const badN)

/-- Negative example: **the constant `bad : num` with the equation `bad ⟶ suc bad` has no set
model** at an assignment that agrees with the object package's on the names it declares. The
value of `bad` would be a number equal to its own successor, which contains it. -/
theorem bad_no_setModel (h : CofinalInaccessibles.{u}) (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectDeclared c = true → objectSetConsts h c = consts c) :
    ¬ SetModel (objHeads h) consts (withDefinition objectChurch badN cnum [badEquation]) := by
  intro model
  have declared : (withDefinition objectChurch badN cnum [badEquation]).constantType badN =
      some cnum := withDefinition_defined objectChurch (by decide)
  have number : consts badN ∈ ZFSet.omega := by
    have member := model.constants declared
    have value : ev (objHeads h) consts (cnum : CTm Tower.Head 0) Fin.elim0 = ZFSet.omega := by
      show consts numN = ZFSet.omega
      rw [← agrees numN (by decide), setConst_num]
    rwa [value] at member
  have step : (withDefinition objectChurch badN cnum [badEquation]).computation.step
      (CTm.const badN : CTm Tower.Head 0) (csuc (.const badN)) :=
    .inr ⟨badEquation, List.mem_cons_self, fun i => i.elim0, rfl, rfl⟩
  have required : (withDefinition objectChurch badN cnum [badEquation]).computation.requires
      (CTm.const badN : CTm Tower.Head 0) (csuc (.const badN))
      (telescopePremises (.nil : CCtx Tower.Head 0) fun i => i.elim0) :=
    .inr ⟨⟨badEquation, List.mem_cons_self, fun i => i.elim0, rfl, rfl⟩,
      ⟨badEquation, List.mem_cons_self, fun i => i.elim0, rfl, rfl, rfl⟩⟩
  have equal := model.steps (Γ := .nil) step required
    (fun premise member => by
      obtain ⟨i, -⟩ := mem_telescopePremises.mp member
      exact i.elim0)
    Fin.elim0 (sat_nil _ _ _)
  have successor : ev (objHeads h) consts (csuc (.const badN) : CTm Tower.Head 0) Fin.elim0 =
      insert (consts badN) (consts badN) := by
    show traceApp (consts sucN) (consts badN) = _
    rw [← agrees sucN (by decide)]
    exact suc_apply h number
  have same : consts badN = insert (consts badN) (consts badN) := equal.trans successor
  have inside : consts badN ∈ insert (consts badN) (consts badN) := ZFSet.mem_insert _ _
  rw [← same] at inside
  exact ZFSet.mem_irrefl _ inside

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
