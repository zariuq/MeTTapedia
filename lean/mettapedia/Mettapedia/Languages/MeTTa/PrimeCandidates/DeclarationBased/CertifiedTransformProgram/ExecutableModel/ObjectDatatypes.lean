import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectLists

/-!
# The object package with any admissible list of declarations

`ObjectLists.lean` adds one declared datatype to the object package of the candidate. This
module adds a list of declarations (`withDeclarations`): datatypes, and definitions by
structural recursion on them, each admissible over the package with the declarations before
it (`AdmissibleDeclarations`).

**For every admissible list** over the object package, relative to `CofinalInaccessibles`:
the package has a set model (`objectDeclarations_model`), every derivable statement holds in
it (`objectDeclarations_sound`), and no closed term has the type `Π (X : U₀). X`
(`objectDeclarations_consistent`). Admissibility is what a declaration checker verifies; the
universe of a datatype of the object package is a sort, and every sort is read as a closed
set that holds the natural numbers.

**Two datatypes together** (`datatypes`): the lists of numbers, and then the trees whose tips
hold a list, `tip : list → tree` and `fork : tree → tree → tree`. The second declaration uses
the first in a field. The list is admissible (`datatypes_admissible`). The set of the trees is
the least set closed under a tip of each list and a fork of two trees (`treeValue`).

**A recursor at a motive that mentions a later datatype.** `spineOf l` is the recursor of the
lists at the constant motive `tree`: the tip of the empty list at the empty list, and a fork of
the tip of the tail and the result at a longer list. The trees are declared after the lists,
so the motive and the methods are typed only in the package with both; the recursor's typing
rule and computation rule are used there (`AdmissibleDeclarations.rec_applied`,
`AdmissibleDeclarations.iota_holds`). `spineOf l` is a tree (`spineOf_typed`), and at the empty
list it is the tip of the empty list (`spineOf_nil`), also in the set model
(`spineOf_nil_holds`).

Negative example: the same two declarations in the other order are not admissible, because the
package before the trees does not have the type of lists (`trees_before_lists_not_admissible`).
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
open ZFSetInterpretation (universeSet universeSet_closed)
open ZFSetInductive (carrier)

universe u

namespace CodeModel

/-! ## Every admissible list of declarations over the object package -/

section General

variable (h : CofinalInaccessibles.{u})

/-- A name the object package declares has a declared type in its annotated package. -/
theorem objectChurch_constantType_ne_none {c : DeclName} (declared : objectDeclared c = true) :
    objectChurch.constantType c ≠ none := by
  rw [objectChurch_constantType]
  unfold elabDeclarations
  unfold objectDeclared at declared
  cases found : objectRules.constantType c with
  | none =>
    rw [found] at declared
    exact nomatch declared
  | some type => exact Option.some_ne_none _

/-- The object package has a set model at every assignment that agrees with its own on the
names it declares. -/
theorem object_baseModel (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, objectChurch.constantType c ≠ none → consts c = objectSetConsts h c) :
    SetModel (objHeads h) consts objectChurch :=
  objectSetModel_agreeing h fun c declared => (agrees c (objectChurch_constantType_ne_none declared)).symm

variable {ds : List (Declaration Tower.Head)}

/-- The universe of every datatype of an admissible list is read as a closed set that holds
the natural numbers. -/
theorem objectDeclarations_universes (admissible : AdmissibleDeclarations objectChurch ds) :
    ∀ d : Datatype Tower.Head, Declaration.datatype d ∈ ds →
      ZFSetUniverseClosure.Closed (objHeads h d.typeUniverse) ∧
        ZFSet.omega ∈ objHeads h d.typeUniverse := by
  intro d member
  have isUniverse : LevelTower.IsUniverse d.typeUniverse := admissible.typeUniverse member
  cases found : d.typeUniverse with
  | sort level => exact ⟨universeSet_closed h ZFSet.omega _, omega_mem_level h _⟩
  | _ =>
    rw [found] at isUniverse
    exact nomatch isUniverse

/-- The assignment of the model: the object package's values, and the declarations read over
them one after the other. -/
noncomputable abbrev objectDeclarationsConsts (ds : List (Declaration Tower.Head)) :
    DeclName → ZFSet.{u} :=
  declarationsConsts (objHeads h) (objectSetConsts h) ds

/-- **The object package with an admissible list of declarations has a set model**, relative
to `CofinalInaccessibles`. -/
theorem objectDeclarations_model (admissible : AdmissibleDeclarations objectChurch ds) :
    SetModel (objHeads h) (objectDeclarationsConsts h ds) (withDeclarations objectChurch ds) :=
  declarations_setModel_read ConvRules.objectLevels objectChurch (object_baseModel h) admissible
    (objectDeclarations_universes h admissible)

/-- **Soundness**: every derivable statement of the package holds in the model. -/
theorem objectDeclarations_sound (admissible : AdmissibleDeclarations objectChurch ds)
    {s : CStatement Tower.Head} (derivation : CDerivable (withDeclarations objectChurch ds) s) :
    Holds (objHeads h) (objectDeclarationsConsts h ds) s :=
  CDerivable.sound (objectDeclarations_model h admissible) derivation

include h in
/-- **Consistency**, relative to `CofinalInaccessibles`: no closed term of the object package
with an admissible list of declarations has the type `Π (X : U₀). X`. -/
theorem objectDeclarations_consistent (admissible : AdmissibleDeclarations objectChurch ds)
    (t : CTm Tower.Head 0) :
    ¬ CTyped (withDeclarations objectChurch ds) .nil t emptyType :=
  CDerivable.no_closed_inhabitant (objectDeclarations_model h admissible)
    (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (objectDeclarationsConsts h ds)) t

end General

/-! ## Lists, and trees whose tips hold lists -/

/-- The type of the trees. -/
def treeN : DeclName := .str .anonymous "tree"

/-- A tip, which holds a list. -/
def tipN : DeclName := .str .anonymous "tip"

/-- A fork of two trees. -/
def forkN : DeclName := .str .anonymous "fork"

/-- The recursor of the trees. -/
def treeRecN : DeclName := .str .anonymous "tree-rec"

/-- The constructors of the trees: `tip` of a list, and `fork` of two trees. -/
def treeCtors : List (DeclName × List CtorField) :=
  [(tipN, [.closed (.const listN)]), (forkN, [.recursive, .recursive])]

/-- The declaration of the lists of numbers. -/
def listDecl : Datatype Tower.Head where
  type := listN
  typeUniverse := .sort Tower.zero
  ctors := listCtors
  recursor := listRecN
  motiveUniverse := listMotives

/-- The declaration of the trees. -/
def treeDecl : Datatype Tower.Head where
  type := treeN
  typeUniverse := .sort Tower.zero
  ctors := treeCtors
  recursor := treeRecN
  motiveUniverse := listMotives

/-- The two declarations: the lists first, then the trees. -/
abbrev datatypes : List (Declaration Tower.Head) := [.datatype treeDecl, .datatype listDecl]

/-- **The object package with the lists and the trees.** -/
abbrev objectDatatypes : ChurchRules (rulesWith objectRules datatypes) :=
  withDeclarations objectChurch datatypes

/-- The declaration of the lists is admissible over the object package. -/
theorem listDecl_admissible : listDecl.Admissible objectChurch where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct := lists_distinct
  new := lists_new
  lamFree := lists_lamFree
  fields := by
    intro entry member F field
    have member' : entry ∈ listCtors := member
    simp only [listCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact nomatch field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with same | impossible
      · obtain rfl : F = .const numN := by injection same
        exact cnum_typed
      · exact nomatch impossible

/-- The names of the trees are distinct. -/
theorem trees_distinct : DistinctNames treeN treeCtors treeRecN where
  ctorsNodup := by decide
  typeNotCtor := by decide
  recNotType := by decide
  recNotCtor := by decide

/-- The names of the trees are new to the package with the lists. -/
theorem trees_new : NewNames (withDeclarations objectChurch [.datatype listDecl]) treeN
    treeCtors treeRecN where
  typeNew := by decide
  ctorsNew := by decide
  recNew := by decide

/-- The declaration of the trees is admissible over the package with the lists. -/
theorem treeDecl_admissible :
    treeDecl.Admissible (withDeclarations objectChurch [.datatype listDecl]) where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct := trees_distinct
  new := trees_new
  lamFree := by
    intro entry member F field
    have member' : entry ∈ treeCtors := member
    simp only [treeCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      obtain rfl : F = .const listN := by injection field
      rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with impossible | impossible <;> exact nomatch impossible
  fields := by
    intro entry member F field
    have member' : entry ∈ treeCtors := member
    simp only [treeCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      obtain rfl : F = .const listN := by injection field
      exact list_typed
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with impossible | impossible <;> exact nomatch impossible

/-- **The lists and then the trees are an admissible list of declarations.** -/
theorem datatypes_admissible : AdmissibleDeclarations objectChurch datatypes :=
  ⟨⟨trivial, listDecl_admissible⟩, treeDecl_admissible⟩

/-- Negative example: the trees before the lists are not admissible. The package before the
trees is the object package, which does not have the type of lists. -/
theorem trees_before_lists_not_admissible :
    ¬ AdmissibleDeclarations objectChurch [.datatype listDecl, .datatype treeDecl] := by
  rintro ⟨⟨-, tree⟩, -⟩
  have typed : CTyped objectChurch .nil (.const listN) (.head (.sort Tower.zero)) :=
    tree.fields (tipN, [.closed (.const listN)]) List.mem_cons_self (.const listN)
      List.mem_cons_self
  exact CDerivable.consts_declared typed listN (List.mem_singleton_self listN) lists_new.typeNew

theorem listDecl_mem : Declaration.datatype listDecl ∈ datatypes :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem treeDecl_mem : Declaration.datatype treeDecl ∈ datatypes := List.mem_cons_self

/-! ## The constants of the two declarations in the package with both -/

section Formation

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The type of trees and its constructors, as annotated terms. -/
abbrev ctree : CTm Tower.Head n := .const treeN
abbrev ctip (l : CTm Tower.Head n) : CTm Tower.Head n := .app (.const tipN) l
abbrev cfork (s t : CTm Tower.Head n) : CTm Tower.Head n := .app (.app (.const forkN) s) t

/-- A derivation of the package with the lists is one of the package with both. -/
theorem ofLists {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) :
    CDerivable objectDatatypes s :=
  CDerivable.mono
    (withDeclarations_sub objectChurch [.datatype listDecl] [.datatype treeDecl]) derivation

/-- A type of a universe is a type of every universe above it. -/
theorem draise {T : CTm Tower.Head n} {l l' : LevelExpr Nat}
    (typed : CTyped objectDatatypes Γ T (CU l))
    (above : ∀ valuation, l.eval valuation ≤ l'.eval valuation) :
    CTyped objectDatatypes Γ T (CU l') :=
  CDerivable.cumul typed above

/-- A dependent function type between two types of one universe is a type of it. -/
theorem dpiT {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr Nat}
    (domain : CTyped objectDatatypes Γ D (CU l))
    (codomain : CTyped objectDatatypes (.snoc Γ D) B (CU l)) :
    CTyped objectDatatypes Γ (.pi D B) (CU l) :=
  CDerivable.cumul (.piForm domain (.sort l) codomain (.sort l) (.sorts l l))
    (fun valuation => by simp [LevelExpr.eval])

/-- Positive: the type of trees is a type of the lowest universe. -/
theorem tree_typed : CTyped objectDatatypes Γ ctree cU0 :=
  datatypes_admissible.type_typed ConvRules.objectLevels treeDecl_mem

/-- The constructor of tips at its declared type. -/
theorem tipConst_typed : CTyped objectDatatypes Γ (.const tipN) (.pi clist ctree) :=
  datatypes_admissible.ctor_typed ConvRules.objectLevels treeDecl_mem (i := 0) rfl

/-- The constructor of forks at its declared type. -/
theorem forkConst_typed : CTyped objectDatatypes Γ (.const forkN) (.pi ctree (.pi ctree ctree)) :=
  datatypes_admissible.ctor_typed ConvRules.objectLevels treeDecl_mem (i := 1) rfl

/-- Positive: the tip of a list is a tree. -/
theorem tip_typed {l : CTm Tower.Head n} (hl : CTyped objectDatatypes Γ l clist) :
    CTyped objectDatatypes Γ (ctip l) ctree :=
  .appElim (B := ctree) tipConst_typed hl

/-- Positive: the fork of two trees is a tree. -/
theorem fork_typed {s t : CTm Tower.Head n} (hs : CTyped objectDatatypes Γ s ctree)
    (ht : CTyped objectDatatypes Γ t ctree) : CTyped objectDatatypes Γ (cfork s t) ctree :=
  .appElim (B := ctree) (.appElim (B := .pi ctree ctree) forkConst_typed hs) ht

/-- The lists and the trees as types of the second universe. -/
theorem list_typed_one' : CTyped objectDatatypes Γ clist cU1 := ofLists list_typed_one

theorem tree_typed_one : CTyped objectDatatypes Γ ctree cU1 := draise tree_typed zero_le_one

theorem num_typed_one' : CTyped objectDatatypes Γ cnum cU1 := ofLists num_typed_one

end Formation

/-! ## A recursor of the lists at a motive into the trees -/

section Spine

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The motive: every list gives a tree. -/
abbrev spineMotive : CTm Tower.Head n := .lam clist ctree

/-- The step: the fork of the tip of the tail and the result. -/
abbrev spineStep : CTm Tower.Head n :=
  .lam cnum (.lam clist (.lam ctree (cfork (ctip (.var 1)) (.var 0))))

/-- **The spine of a list**: the recursor of the lists at the constant motive of trees, with
the tip of the empty list at the empty list and the step at a longer one. -/
abbrev spineOf (l : CTm Tower.Head n) : CTm Tower.Head n :=
  listRecApp spineMotive (ctip cnil) spineStep l

/-- The motive is a motive of the recursor of the lists, in the package with the trees. -/
theorem spineMotive_typed : CTyped objectDatatypes Γ spineMotive (.pi clist cU1) :=
  .lamIntro (u := LevelTower.Head.sort (.succ (.succ Tower.zero)))
    (w := LevelTower.Head.sort Tower.zero) (ofLists list_typed) (LevelTower.IsUniverse.sort _)
    (ofLists motiveType_formed) (LevelTower.IsUniverse.sort _) tree_typed_one

/-- The motive at a list is the type of trees. -/
theorem spineMotive_at {l : CTm Tower.Head n} (hl : CTyped objectDatatypes Γ l clist) :
    CEqual objectDatatypes Γ (.app (.lam clist ctree) l) ctree cU1 :=
  .betaPi (A := clist) (B := cU1) (body := ctree) (a := l)
    (u := LevelTower.Head.sort (.succ (.succ Tower.zero))) (ofLists motiveType_formed)
    (LevelTower.IsUniverse.sort _) tree_typed_one hl

/-- The tip of the empty list is a value of the motive at the empty list. -/
theorem spineNil_typed : CTyped objectDatatypes Γ (ctip cnil) (.app spineMotive cnil) :=
  .conv (tip_typed (ofLists nil_typed)) (.symm (spineMotive_at (ofLists nil_typed)))
    (LevelTower.IsUniverse.sort _)

/-- The step at the type of functions from a number, a list and a tree to a tree. -/
theorem spineStep_plain :
    CTyped objectDatatypes Γ spineStep (.pi cnum (.pi clist (.pi ctree ctree))) := by
  have inner : CTyped objectDatatypes (.snoc (.snoc Γ cnum) clist) (.pi ctree ctree) cU1 :=
    dpiT tree_typed_one tree_typed_one
  have middle : CTyped objectDatatypes (.snoc Γ cnum) (.pi clist (.pi ctree ctree)) cU1 :=
    dpiT list_typed_one' inner
  have outer : CTyped objectDatatypes Γ (.pi cnum (.pi clist (.pi ctree ctree))) cU1 :=
    dpiT num_typed_one' middle
  exact .lamIntro (ofLists (ofObject cnum_typed)) (LevelTower.IsUniverse.sort _) outer
    (LevelTower.IsUniverse.sort _)
    (.lamIntro (ofLists list_typed) (LevelTower.IsUniverse.sort _) middle
      (LevelTower.IsUniverse.sort _)
      (.lamIntro tree_typed (LevelTower.IsUniverse.sort _) inner (LevelTower.IsUniverse.sort _)
        (fork_typed (tip_typed (.var 1)) (.var 0))))

/-- The type of the step over the motive is the plain function type. -/
theorem spineStepType_eq :
    CEqual objectDatatypes Γ (.pi cnum (.pi clist (.pi ctree ctree))) (listStepType spineMotive)
      (CU (.max (.succ Tower.zero) (.max (.succ Tower.zero)
        (.max (.succ Tower.zero) (.succ Tower.zero))))) := by
  have atList : CEqual objectDatatypes (.snoc (.snoc Γ cnum) clist) ctree
      (.app (.lam clist ctree) (.var 0)) cU1 := .symm (spineMotive_at (.var 0))
  have atCons : CEqual objectDatatypes (.snoc (.snoc (.snoc Γ cnum) clist) ctree) ctree
      (.app (.lam clist ctree) (ccons (.var 2) (.var 1))) cU1 :=
    .symm (spineMotive_at (ofLists (cons_typed (.var 2) (.var 1))))
  exact .piCong (.refl num_typed_one') (LevelTower.IsUniverse.sort _)
    (.piCong (.refl list_typed_one') (LevelTower.IsUniverse.sort _)
      (.piCong atList (LevelTower.IsUniverse.sort _) atCons (LevelTower.IsUniverse.sort _)
        (.sorts _ _))
      (LevelTower.IsUniverse.sort _) (.sorts _ _))
    (LevelTower.IsUniverse.sort _) (.sorts _ _)

/-- The step is a step of the recursor of the lists over the motive. -/
theorem spineStep_typed : CTyped objectDatatypes Γ spineStep (listStepType spineMotive) :=
  .conv spineStep_plain spineStepType_eq (LevelTower.IsUniverse.sort _)

/-- **The spine of a list is a tree.** The recursor of the lists is applied at a motive and at
methods that are typed only in the package with the trees. -/
theorem spineOf_typed {l : CTm Tower.Head n} (hl : CTyped objectDatatypes Γ l clist) :
    CTyped objectDatatypes Γ (spineOf l) ctree :=
  .conv
    (datatypes_admissible.rec_applied ConvRules.objectLevels listDecl_mem
      (σ := fun i => [l, spineStep, ctip cnil, spineMotive].getD i.val spineMotive)
      (fun j => match j with
        | ⟨0, _⟩ => hl
        | ⟨1, _⟩ => spineStep_typed
        | ⟨2, _⟩ => spineNil_typed
        | ⟨3, _⟩ => spineMotive_typed))
    (spineMotive_at hl) (LevelTower.IsUniverse.sort _)

/-- **The spine of the empty list is the tip of the empty list**: the computation rule of the
recursor of the lists, used in the package with the trees. -/
theorem spineOf_nil : CEqual objectDatatypes Γ (spineOf cnil) (ctip cnil) ctree :=
  .convEq
    (datatypes_admissible.iota_holds ConvRules.objectLevels listDecl_mem (i := 0) (k := nilN)
      (fields := []) rfl (nilSub spineMotive (ctip cnil) spineStep)
      (fun j => match j with
        | ⟨0, _⟩ => spineStep_typed
        | ⟨1, _⟩ => spineNil_typed
        | ⟨2, _⟩ => spineMotive_typed
        | ⟨k + 3, below⟩ => absurd below (Nat.not_lt.mpr (Nat.le_add_left 3 k))))
    (spineMotive_at (ofLists nil_typed)) (LevelTower.IsUniverse.sort _)

end Spine

/-! ## The set model of the two datatypes -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- The names of the trees are distinct, and their one closed field type, the lists, keeps its
set at every assignment that agrees with the lists' outside the names of the trees. -/
theorem trees_fresh :
    FreshDeclaration (objHeads h) (listConsts h) treeN treeCtors treeRecN where
  toDistinctNames := trees_distinct
  fields := by
    intro consts agrees entry member F field
    simp only [treeCtors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      obtain rfl : F = .const listN := by injection field
      exact agrees listN (by decide) (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with impossible | impossible <;> exact nomatch impossible

/-- **The set of the type of trees** is the least set closed under a tip of each list and a
fork of two trees, the two read by their names: the field of the tips is read as the set of
the lists. -/
theorem treeValue : objectDeclarationsConsts h datatypes treeN =
    carrier [⟨ZFSetInductive.nameCode tipN,
        [ZFSetInductive.Field.ofSet (carrier [⟨ZFSetInductive.nameCode nilN, []⟩,
          ⟨ZFSetInductive.nameCode consN,
            [ZFSetInductive.Field.ofSet ZFSet.omega, .recursive]⟩])]⟩,
      ⟨ZFSetInductive.nameCode forkN, [.recursive, .recursive]⟩] := by
  have reading := inductiveConsts_reading (v := listMotives) (trees_fresh h)
  have signatures := signature_of_agrees (trees_fresh h)
    (inductiveConsts_agrees (objHeads h) (listConsts h) treeN listMotives treeCtors treeRecN)
  show inductiveConsts (objHeads h) (listConsts h) treeN listMotives treeCtors treeRecN treeN = _
  rw [reading.type, signatures]
  show carrier [⟨ZFSetInductive.nameCode tipN,
      [ZFSetInductive.Field.ofSet (listConsts h listN)]⟩,
    ⟨ZFSetInductive.nameCode forkN, [.recursive, .recursive]⟩] = _
  rw [listValue]

/-- In the set model the spine of the empty list has the value of the tip of the empty list. -/
theorem spineOf_nil_holds :
    Holds (objHeads h) (objectDeclarationsConsts h datatypes)
      (.equality .nil (spineOf cnil) (ctip cnil) ctree) :=
  objectDeclarations_sound h datatypes_admissible spineOf_nil

end Model

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
