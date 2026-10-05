import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectRecursiveDefinitions

/-!
# A program over the object package: lists, their append, and a proof by induction

A program is a list of declarations that use each other (`withDeclarations`). This module
gives one with three declarations over the object package of the candidate
(`listProgram`):

1. the datatype of lists of numbers (`listDecl`);
2. the append of two lists, by its two written equations (`appendDef`):

       append nil ys ⟶ ys
       append (cons a as) ys ⟶ cons a (append as ys)

3. the proof by induction that a list appended to the empty list is the list, as a definition
   by structural recursion (`appendNilDef`), of type
   `Π (l : list). Id list (append l nil) l`:

       append-nil nil ⟶ refl nil
       append-nil (cons a as) ⟶ cong (cons a) (append-nil as)

The third declaration is typed only in the package with the second: its statement mentions
the append, and its right sides are typed because the append computes there (the base by
`append nil nil ≡ nil`, the step by `append (cons a as) nil ≡ cons a (append as nil)` and the
congruence of the induction hypothesis). The induction hypothesis is the hypothesis for the
recursive field; the written equation has the recursive call in its place
(`appendNilDef_equations`, by computation).

The list is admissible (`listProgram_admissible`), so by the general theorem
(`objectDeclarations_model`) the package has a set model and is consistent
(`objectProgram_model`, `objectProgram_consistent`), relative to `CofinalInaccessibles`. In its
judgment the proof has its type (`appendNilDef_typed`) and computes at the empty list
(`appendNilDef_nil_rule`); in the model every closed list of the judgment appended to the empty
list has the value of the list (`append_nil_value`).

Negative examples: the proof before the function is not admissible, because its statement is
not a type of the package without the append (`proof_before_function_not_admissible`); and the
append without the lists before it is not admissible (`append_without_lists_not_admissible`).

**An authored order of arguments** (`reverseProgram`). The reversal of a list onto an
accumulator is written with the accumulator first:

    rev-onto acc nil ⟶ acc
    rev-onto acc (cons x xs) ⟶ rev-onto (cons x acc) xs

It recurses on its second argument and changes its first. The draft kernel admits it through
a form with the list first (`tests/prime/scoped/scrutinee_first_recursion.metta` of the C
draft); here that form is a definition by recursion (`revOntoFirstDef`, with the accumulator
as a later argument that the recursive call changes), and `rev-onto` is an explicit definition
over it (`revOntoDef`):

    rev-onto~scrutinee-first nil acc ⟶ acc
    rev-onto~scrutinee-first (cons x xs) acc ⟶ rev-onto~scrutinee-first xs (cons x acc)
    rev-onto acc l ⟶ rev-onto~scrutinee-first l acc

The list of the three declarations is admissible (`reverseProgram_admissible`), so the package
has a set model and is consistent. The two authored equations hold in its judgment
(`revOnto_nil`, `revOnto_cons`), and the list of zero and one reversed onto the empty list is
the list of one and zero (`revOnto_zero_one`). Negative example: the one-element list reversed
onto the empty list is not the empty list (`revOnto_one_not_nil`); the two have different
values in the model.
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
open Presentation.TypedEquality.Impredicative.Domain (termConsts)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetTraceProofDecoding (mem_truthCode)
open ZFSetInductive (constructorValue)

universe u

namespace CodeModel

/-! ## The append as a declaration -/

/-- **The append of two lists as a declaration**: a definition by structural recursion on its
first argument, with the second list as its later argument. -/
def appendDef : RecursiveDefinition Tower.Head where
  name := appendN
  datatype := listDecl
  width := 2
  later := appendLater
  result := clist
  body := appendWrittenBody

/-- The append is admissible over the package with the lists. -/
theorem appendDef_admissible :
    appendDef.Admissible (withDeclarations objectChurch [.datatype listDecl]) where
  new := append_new
  typeFormed := ⟨_, LevelTower.IsUniverse.sort _, appendType_formed⟩
  family := ⟨_, LevelTower.IsUniverse.sort _, listFn_typed_one⟩
  formed := appendWritten_formed
  resultType := appendWritten_resultType
  bodies := appendWritten_bodies

/-- The package with the lists and the append as declarations is the package of
`ObjectAppendByEquations.lean`. -/
theorem lists_append_package :
    withDeclarations objectChurch [.definition (.recursive appendDef), .datatype listDecl] = objectAppend :=
  rfl

/-! ## The statement, and its proof by induction as a definition -/

/-- The name of the proof. -/
def appendNilN : DeclName := .str .anonymous "append-nil"

/-- The statement at a list: the list appended to the empty list is identical to the list. -/
abbrev appendNilAt {n : Nat} (l : CTm Tower.Head n) : CTm Tower.Head n :=
  .id clist (cappend l cnil) l

/-- **The right sides of the proof**: reflexivity at the empty list; at a longer list the
congruence of the induction hypothesis under "the number before". -/
def appendNilBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head
      ((CTele.nil : CTele Tower.Head 1 1).endAt (fields.length + (recPositions fields).length))
  | _, [] => (.refl cnil : CTm Tower.Head 0)
  | _, [.closed _, .recursive] =>
      (congOf clist clist (.app (.const consN) (.var 2)) (cappend (.var 1) cnil) (.var 1)
        (.var 0) : CTm Tower.Head 3)
  | _, _ => .const .anonymous

/-- **The proof by induction as a declaration**: a definition by structural recursion on the
list, with no later argument, whose result family is the statement. -/
def appendNilDef : RecursiveDefinition Tower.Head where
  name := appendNilN
  datatype := listDecl
  width := 1
  later := .nil
  result := appendNilAt (.var 0)
  body := appendNilBody

/-- `append-nil nil ⟶ refl nil`. -/
def appendNilNilEquation : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := .app (.const appendNilN) cnil
  right := .refl cnil

/-- `append-nil (cons a as) ⟶ cong (cons a) (append-nil as)`, over a number and a list. -/
def appendNilConsEquation : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cnum) clist
  left := .app (.const appendNilN) (ccons (.var 1) (.var 0))
  right := congOf clist clist (.app (.const consN) (.var 1)) (cappend (.var 0) cnil) (.var 0)
    (.app (.const appendNilN) (.var 0))

/-- **The written equations of the proof are those two**: the recursive call stands where the
right side has the induction hypothesis. -/
theorem appendNilDef_equations :
    appendNilDef.equations = [appendNilNilEquation, appendNilConsEquation] :=
  rfl

/-- **The program**: the lists, then the append, then the proof. The head of the list is the
declaration added last. -/
abbrev listProgram : List (Declaration Tower.Head) :=
  [.definition (.recursive appendNilDef), .definition (.recursive appendDef), .datatype listDecl]

/-- **The object package with the program.** -/
abbrev objectProgram := withDeclarations objectChurch listProgram

/-! ## The proof is admissible over the package with the append -/

section InAppend

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The statement at a list is a type of the lowest universe, in the package with the
append. -/
theorem appendNilAt_typed {l : CTm Tower.Head n} (hl : CTyped objectAppend Γ l clist) :
    CTyped objectAppend Γ (appendNilAt l) cU0 :=
  .idForm (ofListsAppend list_typed) (LevelTower.IsUniverse.sort _)
    (cappend_typed hl (ofListsAppend nil_typed)) hl

/-- The type of the proof is a type of the lowest universe. -/
theorem appendNilType_formed :
    CTyped objectAppend Γ (.pi clist (appendNilAt (.var 0))) cU0 :=
  CDerivable.cumul
    (.piForm (ofListsAppend list_typed) (.sort _) (appendNilAt_typed (.var 0)) (.sort _)
      (.sorts _ _))
    (fun valuation => by simp [LevelExpr.eval])

/-- **The base of the induction**: reflexivity at the empty list, since the empty list
appended to the empty list computes to the empty list. -/
theorem appendNilBase_typed :
    CTyped objectAppend Γ (.refl cnil) (appendNilAt cnil) := by
  have empty : CTyped objectAppend Γ cnil clist := ofListsAppend nil_typed
  have computed : CEqual objectAppend Γ (appendNilAt cnil) (.id clist cnil cnil) cU0 :=
    .idCong (.refl (ofListsAppend list_typed)) (LevelTower.IsUniverse.sort _)
      (append_nil_rule empty) (.refl empty)
  exact .conv (.reflIntro empty) (.symm computed) (LevelTower.IsUniverse.sort _)

/-- **The step of the induction**: over a number, a list and the induction hypothesis for the
list, an identity proof for the longer list. The longer list appended to the empty list
computes to the number before the rest appended to the empty list, and the hypothesis is
carried under "the number before" by the congruence derived from the identity eliminator. -/
theorem appendNilStep_typed :
    CTyped objectAppend (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0)))
      (congOf clist clist (.app (.const consN) (.var 2)) (cappend (.var 1) cnil) (.var 1)
        (.var 0))
      (appendNilAt (ccons (.var 2) (.var 1))) := by
  have number : CTyped objectAppend (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0)))
      (.var 2) cnum := .var 2
  have rest : CTyped objectAppend (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0)))
      (.var 1) clist := .var 1
  have empty : CTyped objectAppend (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0)))
      cnil clist := ofListsAppend nil_typed
  have hypothesis : CTyped objectAppend
      (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0))) (.var 0)
      (appendNilAt (.var 1)) := .var 0
  have before : CTyped objectAppend (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0)))
      (.app (.const consN) (.var 2)) (.pi clist clist) :=
    .appElim (B := .pi clist clist) (ofListsAppend consConst_typed) number
  have longer : CTyped objectAppend (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0)))
      (ccons (.var 2) (.var 1)) clist := .appElim (B := clist) before rest
  have congruent : CTyped objectAppend
      (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0)))
      (congOf clist clist (.app (.const consN) (.var 2)) (cappend (.var 1) cnil) (.var 1)
        (.var 0))
      (.id clist (ccons (.var 2) (cappend (.var 1) cnil)) (ccons (.var 2) (.var 1))) :=
    CTyped.substitute (ofListsAppend (ofObject congTerm_typed))
      (σ := fun i => ([.var 0, .var 1, cappend (.var 1) cnil, .app (.const consN) (.var 2),
        clist, clist] : List (CTm Tower.Head (n + 3))).getD i.val clist)
      (fun j => match j with
        | ⟨0, _⟩ => hypothesis
        | ⟨1, _⟩ => rest
        | ⟨2, _⟩ => cappend_typed rest empty
        | ⟨3, _⟩ => before
        | ⟨4, _⟩ => ofListsAppend list_typed
        | ⟨5, _⟩ => ofListsAppend list_typed)
  have computed : CEqual objectAppend
      (.snoc (.snoc (.snoc Γ cnum) clist) (appendNilAt (.var 0)))
      (appendNilAt (ccons (.var 2) (.var 1)))
      (.id clist (ccons (.var 2) (cappend (.var 1) cnil)) (ccons (.var 2) (.var 1))) cU0 :=
    .idCong (.refl (ofListsAppend list_typed)) (LevelTower.IsUniverse.sort _)
      (append_cons_rule number rest empty) (.refl longer)
  exact .conv congruent (.symm computed) (LevelTower.IsUniverse.sort _)

end InAppend

theorem appendNilDef_new : objectAppend.constantType appendNilN = none := by decide

theorem appendNilDef_formed {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CCtxFormed objectAppend
      (laterCtx listN (CTele.nil : CTele Tower.Head 1 1) (appendNilAt (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact .nil
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have formed : CCtxFormed objectAppend
        (CCtx.snoc (.snoc (.snoc .nil cnum) clist) (appendNilAt (.var 0))) :=
      .snoc
        (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, ofListsAppend num_typed_one⟩)
          ⟨_, LevelTower.IsUniverse.sort _, ofListsAppend list_typed_one⟩)
        ⟨_, LevelTower.IsUniverse.sort _, appendNilAt_typed (.var 0)⟩
    exact formed
  | i + 2, entry => exact nomatch entry

theorem appendNilDef_resultType {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CIsType objectAppend
      (laterCtx listN (CTele.nil : CTele Tower.Head 1 1) (appendNilAt (.var 0)) k fields)
      (laterResult (CTele.nil : CTele Tower.Head 1 1) (appendNilAt (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectAppend (.nil : CCtx Tower.Head 0) (appendNilAt cnil) cU0 :=
      appendNilAt_typed (ofListsAppend nil_typed)
    exact ⟨_, LevelTower.IsUniverse.sort _, typed⟩
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectAppend
        (CCtx.snoc (.snoc (.snoc .nil cnum) clist) (appendNilAt (.var 0)))
        (appendNilAt (ccons (.var 2) (.var 1))) cU0 :=
      appendNilAt_typed (ofListsAppend (cons_typed (.var 2) (.var 1)))
    exact ⟨_, LevelTower.IsUniverse.sort _, typed⟩
  | i + 2, entry => exact nomatch entry

/-- **The right sides of the proof are typed**: the base and the step of the induction. -/
theorem appendNilDef_bodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped objectAppend
      (laterCtx listN (CTele.nil : CTele Tower.Head 1 1) (appendNilAt (.var 0)) k fields)
      (appendNilBody k fields)
      (laterResult (CTele.nil : CTele Tower.Head 1 1) (appendNilAt (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectAppend (.nil : CCtx Tower.Head 0) (.refl cnil)
        (appendNilAt cnil) := appendNilBase_typed
    exact typed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectAppend
        (CCtx.snoc (.snoc (.snoc .nil cnum) clist) (appendNilAt (.var 0)))
        (congOf clist clist (.app (.const consN) (.var 2)) (cappend (.var 1) cnil) (.var 1)
          (.var 0))
        (appendNilAt (ccons (.var 2) (.var 1))) := appendNilStep_typed
    exact typed
  | i + 2, entry => exact nomatch entry

/-- **The proof is admissible over the package with the lists and the append.** -/
theorem appendNilDef_admissible :
    appendNilDef.Admissible
      (withDeclarations objectChurch [.definition (.recursive appendDef), .datatype listDecl]) where
  new := appendNilDef_new
  typeFormed := ⟨_, LevelTower.IsUniverse.sort _, appendNilType_formed⟩
  family := ⟨_, LevelTower.IsUniverse.sort _, appendNilAt_typed (.var 0)⟩
  formed := appendNilDef_formed
  resultType := appendNilDef_resultType
  bodies := appendNilDef_bodies

/-- **The program is an admissible list of declarations.** -/
theorem listProgram_admissible : AdmissibleDeclarations objectChurch listProgram :=
  ⟨⟨⟨trivial, listDecl_admissible⟩, List.mem_cons_self, appendDef_admissible⟩,
    List.mem_cons_of_mem _ List.mem_cons_self, appendNilDef_admissible⟩

/-! ## The model, and the proof in the judgment -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- **The object package with the program has a set model**, relative to
`CofinalInaccessibles`: the general theorem at the admissible list. -/
theorem objectProgram_model :
    SetModel (objHeads h) (objectDeclarationsConsts h listProgram) objectProgram :=
  objectDeclarations_model h listProgram_admissible

include h in
/-- **Consistency**: no closed term of the package with the program has the type
`Π (X : U₀). X`. -/
theorem objectProgram_consistent (t : CTm Tower.Head 0) :
    ¬ CTyped objectProgram .nil t emptyType :=
  objectDeclarations_consistent h listProgram_admissible t

end Model

section Rules

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A derivation of the package with the append is one of the package with the program. -/
theorem ofAppend {s : CStatement Tower.Head} (derivation : CDerivable objectAppend s) :
    CDerivable objectProgram s :=
  CDerivable.mono
    (withDeclarations_sub objectChurch [.definition (.recursive appendDef), .datatype listDecl]
      [.definition (.recursive appendNilDef)])
    derivation

/-- **The proof has its type**: for every list, the list appended to the empty list is
identical to the list. -/
theorem appendNilDef_typed :
    CTyped objectProgram Γ (.const appendNilN) (.pi clist (appendNilAt (.var 0))) :=
  listProgram_admissible.definition_typed ConvRules.objectLevels
    (D := .recursive appendNilDef) List.mem_cons_self

/-- **The proof computes at the empty list**: its first written equation. -/
theorem appendNilDef_nil_rule :
    CEqual objectProgram Γ (.app (.const appendNilN) cnil) (.refl cnil) (appendNilAt cnil) := by
  have typed : CSubstMor objectProgram (CCtx.nil : CCtx Tower.Head 0) Γ (fun i => i.elim0) :=
    fun i => i.elim0
  exact definition_equation_holds (ds := listProgram) (D := .recursive appendNilDef)
    List.mem_cons_self
    (e := appendNilNilEquation) List.mem_cons_self (fun i => i.elim0) typed
    (.appElim (B := appendNilAt (.var 0)) appendNilDef_typed (ofAppend (ofListsAppend nil_typed)))
    (ofAppend appendNilBase_typed)

end Rules

/-- **In the set model, a list appended to the empty list has the value of the list**, for
every closed list of the judgment of the program: the proof by induction is sound. -/
theorem append_nil_value (h : CofinalInaccessibles.{u}) {l : CTm Tower.Head 0}
    (hl : CTyped objectProgram .nil l clist) :
    ev (objHeads h) (objectDeclarationsConsts h listProgram) (cappend l cnil) Fin.elim0 =
      ev (objHeads h) (objectDeclarationsConsts h listProgram) l Fin.elim0 := by
  have member := objectDeclarations_sound h listProgram_admissible
    (CDerivable.appElim (B := appendNilAt (.var 0)) appendNilDef_typed hl) Fin.elim0 (sat_nil _ _ _)
  exact ((mem_truthCode _ _).mp member).2

/-! ## Lists that are not admissible -/

/-- Negative example: **the proof before the function is not admissible.** The statement of
the proof mentions the append, which the package with the lists alone does not declare. -/
theorem proof_before_function_not_admissible :
    ¬ AdmissibleDeclarations objectChurch
      [.definition (.recursive appendDef), .definition (.recursive appendNilDef), .datatype listDecl] := by
  rintro ⟨⟨-, -, proof⟩, -⟩
  obtain ⟨u, -, typed⟩ := proof.typeFormed
  exact CDerivable.consts_declared typed appendN (by decide) append_new

/-- Negative example: the append without the lists before it is not admissible. -/
theorem append_without_lists_not_admissible :
    ¬ AdmissibleDeclarations objectChurch [.definition (.recursive appendDef)] :=
  not_admissible_without_datatype appendDef

/-! ## An authored order of arguments: reversal onto an accumulator -/

/-- The name of the reversal with the list first. -/
def revOntoFirstN : DeclName := .str .anonymous "rev-onto~scrutinee-first"

/-- The name of the reversal as authored, with the accumulator first. -/
def revOntoN : DeclName := .str .anonymous "rev-onto"

/-- The later argument of the reversal with the list first: the accumulator. -/
abbrev accumulator : CTele Tower.Head 1 2 := .cons clist .nil

/-- **The right sides of the reversal with the list first**: the accumulator at the empty
list; at a longer one the hypothesis at the first number before the accumulator. -/
def revOntoFirstBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head (accumulator.endAt (fields.length + (recPositions fields).length))
  | _, [] => (.var 0 : CTm Tower.Head 1)
  | _, [.closed _, .recursive] => (.app (.var 1) (ccons (.var 3) (.var 0)) : CTm Tower.Head 4)
  | _, _ => .const .anonymous

/-- **The reversal with the list first**, by structural recursion on the list; the recursive
call changes the accumulator. -/
def revOntoFirstDef : RecursiveDefinition Tower.Head where
  name := revOntoFirstN
  datatype := listDecl
  width := 2
  later := accumulator
  result := clist
  body := revOntoFirstBody

/-- **The reversal as authored**, an explicit definition: it passes its arguments to the form
with the list first. -/
def revOntoDef : ExplicitDefinition Tower.Head where
  name := revOntoN
  width := 2
  arguments := .cons clist (.cons clist .nil)
  result := clist
  body := (.app (.app (.const revOntoFirstN) (.var 0)) (.var 1) : CTm Tower.Head 2)

/-- `rev-onto~scrutinee-first nil acc ⟶ acc`. -/
def revOntoFirstNilEquation : DefiningEquation Tower.Head where
  arity := 1
  telescope := .snoc .nil clist
  left := .app (.app (.const revOntoFirstN) cnil) (.var 0)
  right := .var 0

/-- `rev-onto~scrutinee-first (cons x xs) acc ⟶ rev-onto~scrutinee-first xs (cons x acc)`. -/
def revOntoFirstConsEquation : DefiningEquation Tower.Head where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil cnum) clist) clist
  left := .app (.app (.const revOntoFirstN) (ccons (.var 2) (.var 1))) (.var 0)
  right := .app (.app (.const revOntoFirstN) (.var 1)) (ccons (.var 2) (.var 0))

/-- `rev-onto acc l ⟶ rev-onto~scrutinee-first l acc`. -/
def revOntoEquation : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil clist) clist
  left := .app (.app (.const revOntoN) (.var 1)) (.var 0)
  right := .app (.app (.const revOntoFirstN) (.var 0)) (.var 1)

/-- The written equations of the reversal with the list first are those two. -/
theorem revOntoFirst_equations :
    revOntoFirstDef.equations = [revOntoFirstNilEquation, revOntoFirstConsEquation] :=
  rfl

/-- The equation of the authored reversal is that one. -/
theorem revOnto_equations : revOntoDef.equations = [revOntoEquation] :=
  rfl

/-- The lists and the reversal with the list first. -/
abbrev objectReverseFirst :=
  withDeclarations objectChurch [.definition (.recursive revOntoFirstDef), .datatype listDecl]

/-- **The program**: the lists, the reversal with the list first, and the authored reversal. -/
abbrev reverseProgram : List (Declaration Tower.Head) :=
  [.definition (.explicit revOntoDef), .definition (.recursive revOntoFirstDef),
    .datatype listDecl]

/-- **The object package with the reversal program.** -/
abbrev objectReverse := withDeclarations objectChurch reverseProgram

theorem revOntoFirst_new : objectLists.constantType revOntoFirstN = none := by decide

/-- **The right sides of the reversal with the list first are typed**: at a longer list the
hypothesis is a function of the accumulator, applied to the longer accumulator. -/
theorem revOntoFirst_bodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped objectLists (laterCtx listN accumulator clist k fields) (revOntoFirstBody k fields)
      (laterResult accumulator clist k fields) := by
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
        (.app (.var 1) (ccons (.var 3) (.var 0)) : CTm Tower.Head 4) clist :=
      .appElim (B := clist) (.var 1) (cons_typed (.var 3) (.var 0))
    exact typed
  | i + 2, entry => exact nomatch entry

/-- The reversal with the list first is admissible over the package with the lists. -/
theorem revOntoFirstDef_admissible :
    revOntoFirstDef.Admissible (withDeclarations objectChurch [.datatype listDecl]) where
  new := revOntoFirst_new
  typeFormed := ⟨_, LevelTower.IsUniverse.sort _, appendType_formed⟩
  family := ⟨_, LevelTower.IsUniverse.sort _, listFn_typed_one⟩
  formed := appendWritten_formed
  resultType := appendWritten_resultType
  bodies := revOntoFirst_bodies

theorem reverseFirst_admissible :
    AdmissibleDeclarations objectChurch
      [.definition (.recursive revOntoFirstDef), .datatype listDecl] :=
  ⟨⟨trivial, listDecl_admissible⟩, List.mem_cons_self, revOntoFirstDef_admissible⟩

section InReverseFirst

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A derivation of the package with the lists is one of the package with the reversal with
the list first. -/
theorem ofListsReverseFirst {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) :
    CDerivable objectReverseFirst s :=
  CDerivable.mono
    (withDeclarations_sub objectChurch [.datatype listDecl]
      [.definition (.recursive revOntoFirstDef)])
    derivation

/-- The reversal with the list first has its declared type. -/
theorem revOntoFirst_typed :
    CTyped objectReverseFirst Γ (.const revOntoFirstN) (.pi clist clistFn) :=
  reverseFirst_admissible.definition_typed ConvRules.objectLevels
    (D := .recursive revOntoFirstDef) List.mem_cons_self

end InReverseFirst

theorem revOnto_new : objectReverseFirst.constantType revOntoN = none := by decide

/-- The body of the authored reversal is a list, over an accumulator and a list. -/
theorem revOntoBody_typed :
    CTyped objectReverseFirst (CCtx.snoc (.snoc .nil clist) clist)
      (.app (.app (.const revOntoFirstN) (.var 0)) (.var 1) : CTm Tower.Head 2) clist :=
  .appElim (B := clist) (.appElim (B := clistFn) revOntoFirst_typed (.var 0)) (.var 1)

/-- **The authored reversal is admissible** over the package with the form it unfolds to. -/
theorem revOntoDef_admissible : revOntoDef.Admissible objectReverseFirst where
  new := revOnto_new
  formed :=
    .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, ofListsReverseFirst list_typed_one⟩)
      ⟨_, LevelTower.IsUniverse.sort _, ofListsReverseFirst list_typed_one⟩
  resultType := ⟨_, LevelTower.IsUniverse.sort _, ofListsReverseFirst list_typed_one⟩
  body := revOntoBody_typed

/-- **The reversal program is an admissible list of declarations.** -/
theorem reverseProgram_admissible : AdmissibleDeclarations objectChurch reverseProgram :=
  ⟨reverseFirst_admissible, revOntoDef_admissible⟩

section ReverseModel

variable (h : CofinalInaccessibles.{u})

/-- **The object package with the reversal program has a set model**, relative to
`CofinalInaccessibles`. -/
theorem objectReverse_model :
    SetModel (objHeads h) (objectDeclarationsConsts h reverseProgram) objectReverse :=
  objectDeclarations_model h reverseProgram_admissible

include h in
/-- **Consistency**: no closed term of the package with the reversal program has the type
`Π (X : U₀). X`. -/
theorem objectReverse_consistent (t : CTm Tower.Head 0) :
    ¬ CTyped objectReverse .nil t emptyType :=
  objectDeclarations_consistent h reverseProgram_admissible t

end ReverseModel

section ReverseRules

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A derivation of the package with the lists is one of the package with the program. -/
theorem ofListsReverse {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) :
    CDerivable objectReverse s :=
  CDerivable.mono
    (withDeclarations_sub objectChurch [.datatype listDecl]
      [.definition (.explicit revOntoDef), .definition (.recursive revOntoFirstDef)])
    derivation

/-- The authored reversal applied to an accumulator and a list. -/
abbrev crevOnto (acc l : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.const revOntoN) acc) l

/-- The reversal with the list first applied to a list and an accumulator. -/
abbrev crevOntoFirst (l acc : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.const revOntoFirstN) l) acc

/-- **The authored reversal has its declared type.** -/
theorem revOnto_typed :
    CTyped objectReverse Γ (.const revOntoN) (.pi clist (.pi clist clist)) :=
  reverseProgram_admissible.definition_typed ConvRules.objectLevels
    (D := .explicit revOntoDef) List.mem_cons_self

theorem crevOnto_typed {acc l : CTm Tower.Head n} (hacc : CTyped objectReverse Γ acc clist)
    (hl : CTyped objectReverse Γ l clist) : CTyped objectReverse Γ (crevOnto acc l) clist :=
  .appElim (B := clist) (.appElim (B := .pi clist clist) revOnto_typed hacc) hl

theorem crevOntoFirst_typed {l acc : CTm Tower.Head n} (hl : CTyped objectReverse Γ l clist)
    (hacc : CTyped objectReverse Γ acc clist) :
    CTyped objectReverse Γ (crevOntoFirst l acc) clist :=
  .appElim (B := clist)
    (.appElim (B := clistFn)
      (reverseProgram_admissible.definition_typed ConvRules.objectLevels
        (D := .recursive revOntoFirstDef) (List.mem_cons_of_mem _ List.mem_cons_self))
      hl)
    hacc

theorem cons_typedReverse {x xs : CTm Tower.Head n} (hx : CTyped objectReverse Γ x cnum)
    (hxs : CTyped objectReverse Γ xs clist) : CTyped objectReverse Γ (ccons x xs) clist :=
  .appElim (B := clist)
    (.appElim (B := .pi clist clist) (ofListsReverse consConst_typed) hx) hxs

/-- **The authored reversal unfolds** to the form with the list first: its one equation. -/
theorem revOnto_unfold {acc l : CTm Tower.Head n} (hacc : CTyped objectReverse Γ acc clist)
    (hl : CTyped objectReverse Γ l clist) :
    CEqual objectReverse Γ (crevOnto acc l) (crevOntoFirst l acc) clist :=
  have typed : CSubstMor objectReverse (CCtx.snoc (.snoc .nil clist) clist) Γ
      (fun i : Fin 2 => [l, acc].getD i.val acc) :=
    fun j => match j with
      | ⟨0, _⟩ => hl
      | ⟨1, _⟩ => hacc
  definition_equation_holds (ds := reverseProgram) (D := .explicit revOntoDef)
    List.mem_cons_self (e := revOntoEquation) List.mem_cons_self
    (fun i => [l, acc].getD i.val acc) typed (crevOnto_typed hacc hl)
    (crevOntoFirst_typed hl hacc)

/-- The first equation of the form with the list first. -/
theorem revOntoFirst_nil_rule {acc : CTm Tower.Head n}
    (hacc : CTyped objectReverse Γ acc clist) :
    CEqual objectReverse Γ (crevOntoFirst cnil acc) acc clist :=
  have typed : CSubstMor objectReverse (CCtx.snoc .nil clist) Γ (fun _ : Fin 1 => acc) :=
    fun j => match j with
      | ⟨0, _⟩ => hacc
  definition_equation_holds (ds := reverseProgram) (D := .recursive revOntoFirstDef)
    (List.mem_cons_of_mem _ List.mem_cons_self) (e := revOntoFirstNilEquation)
    List.mem_cons_self (fun _ => acc) typed
    (crevOntoFirst_typed (ofListsReverse nil_typed) hacc) hacc

/-- The second equation of the form with the list first. -/
theorem revOntoFirst_cons_rule {x xs acc : CTm Tower.Head n}
    (hx : CTyped objectReverse Γ x cnum) (hxs : CTyped objectReverse Γ xs clist)
    (hacc : CTyped objectReverse Γ acc clist) :
    CEqual objectReverse Γ (crevOntoFirst (ccons x xs) acc) (crevOntoFirst xs (ccons x acc))
      clist :=
  have typed : CSubstMor objectReverse (CCtx.snoc (.snoc (.snoc .nil cnum) clist) clist) Γ
      (fun i : Fin 3 => [acc, xs, x].getD i.val x) :=
    fun j => match j with
      | ⟨0, _⟩ => hacc
      | ⟨1, _⟩ => hxs
      | ⟨2, _⟩ => hx
  definition_equation_holds (ds := reverseProgram) (D := .recursive revOntoFirstDef)
    (List.mem_cons_of_mem _ List.mem_cons_self) (e := revOntoFirstConsEquation)
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun i => [acc, xs, x].getD i.val x) typed
    (crevOntoFirst_typed (cons_typedReverse hx hxs) hacc)
    (crevOntoFirst_typed hxs (cons_typedReverse hx hacc))

/-- **The first authored equation**: the empty list reversed onto an accumulator is the
accumulator. -/
theorem revOnto_nil {acc : CTm Tower.Head n} (hacc : CTyped objectReverse Γ acc clist) :
    CEqual objectReverse Γ (crevOnto acc cnil) acc clist :=
  .trans (revOnto_unfold hacc (ofListsReverse nil_typed)) (revOntoFirst_nil_rule hacc)

/-- **The second authored equation**: a longer list reversed onto an accumulator is its rest
reversed onto the first number before the accumulator. The recursive call changes the first
argument. -/
theorem revOnto_cons {acc x xs : CTm Tower.Head n} (hacc : CTyped objectReverse Γ acc clist)
    (hx : CTyped objectReverse Γ x cnum) (hxs : CTyped objectReverse Γ xs clist) :
    CEqual objectReverse Γ (crevOnto acc (ccons x xs)) (crevOnto (ccons x acc) xs) clist :=
  .trans (revOnto_unfold hacc (cons_typedReverse hx hxs))
    (.trans (revOntoFirst_cons_rule hx hxs hacc)
      (.symm (revOnto_unfold (cons_typedReverse hx hacc) hxs)))

/-- The one-element list reversed onto the empty list is the list. -/
theorem revOnto_one :
    CEqual objectReverse .nil (crevOnto cnil (ccons czero cnil)) (ccons czero cnil) clist := by
  have zero : CTyped objectReverse .nil czero cnum := ofListsReverse (ofObject czero_typed)
  have empty : CTyped objectReverse .nil cnil clist := ofListsReverse nil_typed
  exact .trans (revOnto_cons empty zero empty) (revOnto_nil (cons_typedReverse zero empty))

/-- **The list of zero and one reversed onto the empty list is the list of one and zero**:
the second authored equation twice, then the first. -/
theorem revOnto_zero_one :
    CEqual objectReverse .nil
      (crevOnto cnil (ccons czero (ccons (csuc czero) cnil)))
      (ccons (csuc czero) (ccons czero cnil)) clist := by
  have zero : CTyped objectReverse .nil czero cnum := ofListsReverse (ofObject czero_typed)
  have one : CTyped objectReverse .nil (csuc czero) cnum :=
    ofListsReverse (ofObject (csuc_typed czero_typed))
  have empty : CTyped objectReverse .nil cnil clist := ofListsReverse nil_typed
  have first := revOnto_cons empty zero (cons_typedReverse one empty)
  have second := revOnto_cons (cons_typedReverse zero empty) one empty
  have third := revOnto_nil (cons_typedReverse one (cons_typedReverse zero empty))
  exact .trans first (.trans second third)

/-- In the set model the equation holds. -/
theorem revOnto_zero_one_holds (h : CofinalInaccessibles.{u}) :
    Holds (objHeads h) (objectDeclarationsConsts h reverseProgram)
      (.equality .nil (crevOnto cnil (ccons czero (ccons (csuc czero) cnil)))
        (ccons (csuc czero) (ccons czero cnil)) clist) :=
  objectDeclarations_sound h reverseProgram_admissible revOnto_zero_one

end ReverseRules

/-- Negative example: **the one-element list reversed onto the empty list is not the empty
list.** It is the one-element list, and in the set model the two are values of different
constructors. -/
theorem revOnto_one_not_nil (h : CofinalInaccessibles.{u}) :
    ¬ CEqual objectReverse .nil (crevOnto cnil (ccons czero cnil)) cnil clist := fun equal => by
  have reading := declarations_reading (heads := objHeads h) (base := objectSetConsts h)
    objectChurch reverseProgram reverseProgram_admissible listDecl
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (objectDeclarationsConsts h reverseProgram) fun _ _ => rfl
  have same : ev (objHeads h) (objectDeclarationsConsts h reverseProgram) (ccons czero cnil)
        Fin.elim0 =
      ev (objHeads h) (objectDeclarationsConsts h reverseProgram) cnil Fin.elim0 :=
    (objectDeclarations_sound h reverseProgram_admissible (.trans (.symm revOnto_one) equal)
      Fin.elim0 (sat_nil _ _ _)).1
  have zero := objectDeclarations_sound h reverseProgram_admissible
    (ofListsReverse (ofObject (czero_typed (Γ := .nil)))) Fin.elim0 (sat_nil _ _ _)
  have empty := objectDeclarations_sound h reverseProgram_admissible
    (ofListsReverse (nil_typed (Γ := .nil))) Fin.elim0 (sat_nil _ _ _)
  have nilValue : ev (objHeads h) (objectDeclarationsConsts h reverseProgram) cnil Fin.elim0 =
      constructorValue (ZFSetInductive.nameCode nilN) [] :=
    ctor_apply (reading.ctor (i := 0) rfl) (args := [])
      ((fits_iff _ _ _ _).mpr ⟨rfl, fun j below => absurd below (Nat.not_lt_zero j)⟩)
  have consValue : ev (objHeads h) (objectDeclarationsConsts h reverseProgram)
        (ccons czero cnil) Fin.elim0 =
      constructorValue (ZFSetInductive.nameCode consN)
        [ev (objHeads h) (objectDeclarationsConsts h reverseProgram) czero Fin.elim0,
          ev (objHeads h) (objectDeclarationsConsts h reverseProgram) cnil Fin.elim0] :=
    ctor_apply (reading.ctor (i := 1) rfl)
      (args := [ev (objHeads h) (objectDeclarationsConsts h reverseProgram) czero Fin.elim0,
        ev (objHeads h) (objectDeclarationsConsts h reverseProgram) cnil Fin.elim0])
      ((fits_iff _ _ _ _).mpr ⟨rfl, fun j below => by
      match j, below with
      | 0, _ => exact zero
      | 1, _ => exact empty⟩)
  rw [nilValue, consValue] at same
  exact ZFSetInductive.constructorValue_ne_of_tag_ne
    (ZFSetInductive.nameCode_injective.ne (by decide)) _ _ same

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
