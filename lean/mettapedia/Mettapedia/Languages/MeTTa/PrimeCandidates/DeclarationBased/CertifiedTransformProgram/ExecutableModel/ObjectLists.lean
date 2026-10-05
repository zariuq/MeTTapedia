import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSetSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDeclarationLists
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectCongruence

/-!
# The object package with the lists of numbers

The object package of the candidate declares one inductive type, the numbers. This module adds
a second one by declaration: the lists of numbers, with the constructors `nil` and
`cons : num → list → list` and a recursor into the second universe. The package
(`objectLists`) is the sum of the object package and the package of the declaration
(`inductiveChurch`), over the universe rules of the object package.

It has a set model in the tower seeded with the natural numbers, relative to
`CofinalInaccessibles` (`objectLists_model`): the object package keeps its values, the type of
lists is read as the least set closed under the two constructors, and the recursor as the
recursion on that set. Every derivation of the package holds in the model
(`objectLists_sound`), and no closed term has the type `Π (X : U₀). X`
(`objectLists_consistent`).

The typings of the declaration's constants are instances of the general theorems on
declarations (`type_typed`, `ctor_typed`, `rec_applied`): the names are distinct and new to the
object package, and the one closed field type, the numbers, is a type of it (`lists_distinct`,
`lists_new`, `lists_fieldsFormed`).

Positive examples: the type of lists is a type of the lowest universe, and the empty list
and the one-element list of the numeral one are lists (`list_typed`, `nil_typed`,
`cons_one_nil_typed`); the recursor is typed (`listRec_typed`) and its two computation rules
hold in the judgment with the typings of the motive, the value, the step and the fields as
their premises (`listRec_nil`, `listRec_cons`); the recursor computes on the one-element list
of the numeral one (`listRec_one`); the length of a list, defined by the recursor, is a number
(`lengthOf_typed`), and the length of that list is one (`lengthOf_one`), so the equation also
holds in the set model; and the set of the type of lists is the least set closed
under the empty list and a number before a list (`listValue`), each read by its name: the
carrier of the two constructors that carry the codes of the names `nil` and `cons`. Negative
example: no set model of the package reads the type of lists as the empty set
(`no_setModel_of_empty_lists`).

**A proof by induction in the judgment** (`appendNil_identity`): every list appended to the
empty list is identical to the list. Appending is a second program by the recursor
(`appendNil`), with its two computation rules in the judgment (`appendNil_nil`,
`appendNil_cons`). The proof term is the recursor at the family of identity types (`appId`):
reflexivity at the empty list (`appIdNil_typed`), and at a longer list the congruence of the
induction hypothesis under "the number before", which is derived from the identity eliminator
of the object package (`appIdStepBody_typed`, `ObjectCongruence.lean`). The judgment's
conversion carries the computation rules into the identity types. Positive example: the proof
at the one-element list (`appendNil_identity_one`); in the set model a closed list appended to
the empty list has the value of the list (`appendNil_value`). Negative example: no closed term
is an identity proof that the empty list is the one-element list
(`nil_not_identical_to_one`).
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
open ZFSetInterpretation (universeSet universeSet_closed)
open ZFSetInductive (carrier)
open ZFSetTraceProofDecoding (mem_truthCode)

universe u

namespace CodeModel

/-! ## The declaration -/

/-- The type of the lists of numbers. -/
def listN : DeclName := .str .anonymous "list"

/-- The empty list. -/
def nilN : DeclName := .str .anonymous "nil"

/-- A number before a list. -/
def consN : DeclName := .str .anonymous "cons"

/-- The recursor of the lists of numbers. -/
def listRecN : DeclName := .str .anonymous "list-rec"

/-- The constructors of the lists of numbers: `nil`, and `cons` of a number and a list. -/
def listCtors : List (DeclName × List CtorField) :=
  [(nilN, []), (consN, [.closed (.const numN), .recursive])]

/-- The universe of the motives of the recursor: the second one, so that a motive may be a
family of small types or the lowest universe itself. -/
abbrev listMotives : Tower.Head := .sort (.succ Tower.zero)

/-- **The object package with the lists of numbers.** -/
def objectLists : ChurchRules
    (Rules.sum objectRules
      (inductiveRules objectRules listN (.sort Tower.zero) listCtors listRecN listMotives)) :=
  objectChurch.sum
    (inductiveChurch objectRules listN (.sort Tower.zero) listCtors listRecN listMotives)

/-- The names of the declaration are distinct. -/
theorem lists_distinct : DistinctNames listN listCtors listRecN where
  ctorsNodup := by decide
  typeNotCtor := by decide
  recNotType := by decide
  recNotCtor := by decide

/-- The names of the declaration are new to the object package. -/
theorem lists_new : NewNames objectChurch listN listCtors listRecN where
  typeNew := by decide
  ctorsNew := by decide
  recNew := by decide

/-- The one closed field type of the declaration, the numbers, has no abstraction. -/
theorem lists_lamFree : FieldsLamFree listCtors := by
  intro entry member F field
  simp only [listCtors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact nomatch field
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
    rcases field with same | impossible
    · obtain rfl : F = .const numN := by injection same
      rfl
    · exact nomatch impossible

/-- It is a type of the object package. -/
theorem lists_fieldsFormed : FieldsFormed objectChurch listCtors := by
  intro entry member F field
  simp only [listCtors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact nomatch field
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
    rcases field with same | impossible
    · obtain rfl : F = .const numN := by injection same
      exact ⟨_, LevelTower.IsUniverse.sort _, cnum_typed⟩
    · exact nomatch impossible

/-! ## The set model -/

section Model

variable (h : CofinalInaccessibles.{u})

/-- The assignment of the model: the object package's values, and the declaration read over
them. -/
noncomputable def listConsts : DeclName → ZFSet.{u} :=
  inductiveConsts (objHeads h) (objectSetConsts h) listN listMotives listCtors listRecN

/-- The names of the declaration are distinct, and its one closed field type, the numbers,
is a name of the object package. -/
theorem lists_fresh :
    FreshDeclaration (objHeads h) (objectSetConsts h) listN listCtors listRecN where
  toDistinctNames := lists_distinct
  fields := by
    intro consts agrees entry member F field
    simp only [listCtors, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact nomatch field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with same | impossible
      · obtain rfl : F = .const numN := by injection same
        exact agrees numN (by decide) (by decide) (by decide)
      · exact nomatch impossible

/-- **The object package with the lists of numbers has a set model**, relative to
`CofinalInaccessibles`. -/
theorem objectLists_model : SetModel (objHeads h) (listConsts h) objectLists :=
  extension_setModel objectChurch
    (fun consts agrees => objectSetModel_agreeing h fun c declared =>
      (agrees c (fun same => by rw [same] at declared; exact absurd declared (by decide))
        (fun member => by
          simp only [listCtors, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
            or_false] at member
          rcases member with rfl | rfl
          · exact absurd declared (by decide)
          · exact absurd declared (by decide))
        (fun same => by rw [same] at declared; exact absurd declared (by decide))).symm)
    (lists_fresh h) lists_lamFree (universeSet_closed h ZFSet.omega 0) (omega_mem_level h 0)
    (fun entry member F field => by
      simp only [listCtors, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact nomatch field
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
        rcases field with same | impossible
        · obtain rfl : F = .const numN := by injection same
          show objectSetConsts h numN ∈ universeSet h ZFSet.omega 0
          rw [setConst_num]
          exact omega_mem_level h 0
        · exact nomatch impossible)

/-- **Soundness**: every derivable statement of the package holds in the model. -/
theorem objectLists_sound {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) :
    Holds (objHeads h) (listConsts h) s :=
  CDerivable.sound (objectLists_model h) derivation

include h in
/-- **Consistency**, relative to `CofinalInaccessibles`: no closed term of the package has the
type `Π (X : U₀). X`. -/
theorem objectLists_consistent (t : CTm Tower.Head 0) :
    ¬ CDerivable objectLists (.typing .nil t emptyType) :=
  CDerivable.no_closed_inhabitant (objectLists_model h)
    (ev_emptyType h ZFSet.omega ∅ (fun _ => 0) (listConsts h)) t

/-- **The set of the type of lists** is the least set closed under the empty list and a
number before a list, the two read by their names: the carrier of the signature whose
constructors carry the codes of the names `nil` and `cons`. -/
theorem listValue : listConsts h listN =
    carrier [⟨ZFSetInductive.nameCode nilN, []⟩,
      ⟨ZFSetInductive.nameCode consN, [ZFSetInductive.Field.ofSet ZFSet.omega, .recursive]⟩] := by
  have reading := inductiveConsts_reading (v := listMotives) (lists_fresh h)
  have signatures := signature_of_agrees (lists_fresh h)
    (inductiveConsts_agrees (objHeads h) (objectSetConsts h) listN listMotives listCtors listRecN)
  show inductiveConsts (objHeads h) (objectSetConsts h) listN listMotives listCtors listRecN
    listN = _
  rw [reading.type, signatures]
  show carrier [⟨ZFSetInductive.nameCode nilN, []⟩, ⟨ZFSetInductive.nameCode consN,
    [ZFSetInductive.Field.ofSet (objectSetConsts h numN), .recursive]⟩] = _
  rw [setConst_num]

end Model

/-! ## The constants of the declaration in the judgment -/

section Formation

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The type of lists and its constructors, as annotated terms. -/
abbrev clist : CTm Tower.Head n := .const listN
abbrev cnil : CTm Tower.Head n := .const nilN
abbrev ccons (a as : CTm Tower.Head n) : CTm Tower.Head n := .app (.app (.const consN) a) as

/-- The second universe above the lowest. -/
abbrev cU2 : CTm Tower.Head n := CU (.succ (.succ Tower.zero))

/-- A derivation of the object package is a derivation of the package with lists. -/
theorem ofObject {s : CStatement Tower.Head} (derivation : CDerivable objectChurch s) :
    CDerivable objectLists s :=
  CDerivable.sum_left _ derivation

/-- A type of a universe is a type of every universe above it. -/
theorem lraise {T : CTm Tower.Head n} {l l' : LevelExpr Nat}
    (typed : CTyped objectLists Γ T (CU l))
    (above : ∀ valuation, l.eval valuation ≤ l'.eval valuation) :
    CTyped objectLists Γ T (CU l') :=
  CDerivable.cumul typed above

/-- A dependent function type between two types of one universe is a type of it. -/
theorem lpiT {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr Nat}
    (domain : CTyped objectLists Γ D (CU l))
    (codomain : CTyped objectLists (.snoc Γ D) B (CU l)) :
    CTyped objectLists Γ (.pi D B) (CU l) :=
  CDerivable.cumul (.piForm domain (.sort l) codomain (.sort l) (.sorts l l))
    (fun valuation => by simp [LevelExpr.eval])

/-- Positive: the type of lists is a type of the lowest universe. -/
theorem list_typed : CTyped objectLists Γ clist cU0 :=
  type_typed ConvRules.objectLevels objectChurch (LevelTower.IsUniverse.sort _) lists_new

/-- Positive: the empty list is a list. -/
theorem nil_typed : CTyped objectLists Γ cnil clist :=
  ctor_typed ConvRules.objectLevels objectChurch (LevelTower.IsUniverse.sort _) lists_distinct
    lists_lamFree lists_new lists_fieldsFormed (i := 0) rfl

/-- The constructor of longer lists at its declared type. -/
theorem consConst_typed : CTyped objectLists Γ (.const consN) (.pi cnum (.pi clist clist)) :=
  ctor_typed ConvRules.objectLevels objectChurch (LevelTower.IsUniverse.sort _) lists_distinct
    lists_lamFree lists_new lists_fieldsFormed (i := 1) rfl

/-- Positive: a number before a list is a list. -/
theorem cons_typed {a as : CTm Tower.Head n} (ta : CTyped objectLists Γ a cnum)
    (tas : CTyped objectLists Γ as clist) : CTyped objectLists Γ (ccons a as) clist :=
  .appElim (B := clist) (.appElim (B := .pi clist clist) consConst_typed ta) tas

/-- The one-element list of the numeral one is a list. -/
theorem cons_one_nil_typed : CTyped objectLists Γ (ccons (csuc czero) cnil) clist :=
  cons_typed (ofObject (csuc_typed czero_typed)) nil_typed

end Formation

/-! ## The recursor's computation rules in the judgment -/

/-- The recursor applied to a motive, the value at the empty list, the step, and a list. -/
def listRecApp {n : Nat} (P z s l : CTm Tower.Head n) : CTm Tower.Head n :=
  .app (.app (.app (.app (.const listRecN) P) z) s) l

/-- The type of the step of the recursor over a motive: from a number, a list and the motive
at the list to the motive at the longer list. -/
def listStepType {n : Nat} (P : CTm Tower.Head n) : CTm Tower.Head n :=
  .pi (.const numN) (.pi (.const listN)
    (.pi (.app ((P.rename wk).rename wk) (.var 0))
      (.app (((P.rename wk).rename wk).rename wk)
        (.app (.app (.const consN) (.var 2)) (.var 1)))))

/-- The instances of the metavariables of the rule at the empty list: the motive, the value at
the empty list and the step. -/
def nilSub {n : Nat} (P z s : CTm Tower.Head n) :
    CSub Tower.Head (1 + listCtors.length + ([] : List CtorField).length) n :=
  fun i => [s, z, P].getD i.val P

/-- **The recursor at the empty list**: with a typed motive, value and step, `list-rec P z s nil`
equals `z` at the motive's type at the empty list. The premises of the rule are the three
typings. -/
theorem listRec_nil {n : Nat} {Γ : CCtx Tower.Head n} {P z s : CTm Tower.Head n}
    (hP : CTyped objectLists Γ P (.pi (.const listN) (.head listMotives)))
    (hz : CTyped objectLists Γ z (.app P (.const nilN)))
    (hs : CTyped objectLists Γ s (listStepType P)) :
    CEqual objectLists Γ (listRecApp P z s (.const nilN)) z (.app P (.const nilN)) :=
  iota_holds ConvRules.objectLevels objectChurch (LevelTower.IsUniverse.sort _)
    (LevelTower.IsUniverse.sort _) lists_distinct lists_lamFree lists_new lists_fieldsFormed
    (i := 0) (k := nilN) (fields := []) rfl (nilSub P z s)
    (fun j => match j with
      | ⟨0, _⟩ => hs
      | ⟨1, _⟩ => hz
      | ⟨2, _⟩ => hP
      | ⟨k + 3, below⟩ => absurd below (Nat.not_lt.mpr (Nat.le_add_left 3 k)))

/-- The instances of the metavariables of the rule at a longer list: the motive, the value at
the empty list, the step, the number and the list. -/
def consSub {n : Nat} (P z s a as : CTm Tower.Head n) :
    CSub Tower.Head
      (1 + listCtors.length + ([.closed (.const numN), .recursive] : List CtorField).length) n :=
  fun i => [as, a, s, z, P].getD i.val P

/-- **The recursor at a longer list**: with a typed motive, value, step, number and list,
`list-rec P z s (cons a as)` equals `s a as (list-rec P z s as)` at the motive's type at the
longer list. The premises of the rule are the five typings. -/
theorem listRec_cons {n : Nat} {Γ : CCtx Tower.Head n} {P z s a as : CTm Tower.Head n}
    (hP : CTyped objectLists Γ P (.pi (.const listN) (.head listMotives)))
    (hz : CTyped objectLists Γ z (.app P (.const nilN)))
    (hs : CTyped objectLists Γ s (listStepType P))
    (ha : CTyped objectLists Γ a cnum) (has : CTyped objectLists Γ as clist) :
    CEqual objectLists Γ (listRecApp P z s (ccons a as))
      (.app (.app (.app s a) as) (listRecApp P z s as)) (.app P (ccons a as)) :=
  iota_holds ConvRules.objectLevels objectChurch (LevelTower.IsUniverse.sort _)
    (LevelTower.IsUniverse.sort _) lists_distinct lists_lamFree lists_new lists_fieldsFormed
    (i := 1) (k := consN) (fields := [.closed (.const numN), .recursive]) rfl
    (consSub P z s a as)
    (fun j => match j with
      | ⟨0, _⟩ => has
      | ⟨1, _⟩ => ha
      | ⟨2, _⟩ => hs
      | ⟨3, _⟩ => hz
      | ⟨4, _⟩ => hP
      | ⟨k + 5, below⟩ => absurd below (Nat.not_lt.mpr (Nat.le_add_left 5 k)))

/-! ## The recursor's typing, and a computation -/

section Typing

/-- The context of a motive, a value at the empty list and a step. -/
abbrev methodsCtx : CCtx Tower.Head 3 :=
  .snoc (.snoc (.snoc .nil (.pi clist cU1)) (.app (.var 0) cnil)) (listStepType (.var 1))

/-- **The typing of the recursor**: with a typed motive, value, step and list,
`list-rec P z s l` has the type `P l`. -/
theorem listRec_typed {n : Nat} {Γ : CCtx Tower.Head n} {P z s l : CTm Tower.Head n}
    (hP : CTyped objectLists Γ P (.pi (.const listN) (.head listMotives)))
    (hz : CTyped objectLists Γ z (.app P (.const nilN)))
    (hs : CTyped objectLists Γ s (listStepType P)) (hl : CTyped objectLists Γ l clist) :
    CTyped objectLists Γ (listRecApp P z s l) (.app P l) :=
  rec_applied ConvRules.objectLevels objectChurch (LevelTower.IsUniverse.sort _)
    (LevelTower.IsUniverse.sort _) lists_distinct lists_lamFree lists_new lists_fieldsFormed
    (σ := fun i => [l, s, z, P].getD i.val P)
    (fun j => match j with
      | ⟨0, _⟩ => hl
      | ⟨1, _⟩ => hs
      | ⟨2, _⟩ => hz
      | ⟨3, _⟩ => hP)

/-- **A computation with the recursor in the judgment**: for a motive `P`, a value `z` and a
step `s`, the recursor at the one-element list of the numeral one equals the step applied to
the numeral, the empty list and `z`. Two rule instances and one congruence. -/
theorem listRec_one :
    CEqual objectLists methodsCtx
      (listRecApp (.var 2) (.var 1) (.var 0) (ccons (csuc czero) cnil))
      (.app (.app (.app (.var 0) (csuc czero)) cnil) (.var 1))
      (.app (.var 2) (ccons (csuc czero) cnil)) := by
  have hP : CTyped objectLists methodsCtx (.var 2) (.pi clist cU1) := .var 2
  have hz : CTyped objectLists methodsCtx (.var 1) (.app (.var 2) cnil) := .var 1
  have hs : CTyped objectLists methodsCtx (.var 0) (listStepType (.var 2)) := .var 0
  have one : CTyped objectLists methodsCtx (csuc czero) cnum :=
    ofObject (csuc_typed czero_typed)
  have stepApplied : CTyped objectLists methodsCtx (.app (.app (.var 0) (csuc czero)) cnil)
      (.pi (.app (.var 2) cnil) (.app (.var 3) (ccons (csuc czero) cnil))) :=
    .appElim (.appElim hs one) nil_typed
  have first := listRec_cons hP hz hs one nil_typed
  have second : CEqual objectLists methodsCtx
      (.app (.app (.app (.var 0) (csuc czero)) cnil)
        (listRecApp (.var 2) (.var 1) (.var 0) cnil))
      (.app (.app (.app (.var 0) (csuc czero)) cnil) (.var 1))
      (.app (.var 2) (ccons (csuc czero) cnil)) :=
    .appCong (.refl stepApplied) (listRec_nil hP hz hs)
  exact .trans first second

end Typing

/-! ## A program: the length of a list -/

section Length

/-- The motive of the length: every list gives a number. -/
abbrev lenMotive : CTm Tower.Head 0 := .lam clist cnum

/-- The step of the length: the successor of the length of the shorter list. -/
abbrev lenStep : CTm Tower.Head 0 := .lam cnum (.lam clist (.lam cnum (csuc (.var 0))))

/-- **The length of a list**: the recursor with the constant motive, zero at the empty list
and the successor at a longer one. -/
abbrev lengthOf (l : CTm Tower.Head 0) : CTm Tower.Head 0 := listRecApp lenMotive czero lenStep l

theorem zero_le_one (valuation : Nat → Nat) :
    (Tower.zero : LevelExpr Nat).eval valuation ≤ (LevelExpr.succ Tower.zero).eval valuation := by
  show (0 : Nat) ≤ 1
  decide

theorem zero_le_two (valuation : Nat → Nat) : (Tower.zero : LevelExpr Nat).eval valuation ≤
    (LevelExpr.succ (.succ Tower.zero)).eval valuation := by
  show (0 : Nat) ≤ 2
  decide

/-- The numbers and the lists as types of the second universe. -/
theorem num_typed_one {n : Nat} {Γ : CCtx Tower.Head n} : CTyped objectLists Γ cnum cU1 :=
  lraise (ofObject cnum_typed) zero_le_one

theorem list_typed_one {n : Nat} {Γ : CCtx Tower.Head n} : CTyped objectLists Γ clist cU1 :=
  lraise list_typed zero_le_one

/-- The type of motives is a type of the third universe. -/
theorem motiveType_formed {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped objectLists Γ (.pi clist cU1) cU2 :=
  lpiT (lraise list_typed zero_le_two) (.headType (LevelTower.HeadTyping.sort (.succ Tower.zero)))

/-- The motive of the length is a motive. -/
theorem lenMotive_typed : CTyped objectLists .nil lenMotive (.pi clist cU1) :=
  .lamIntro (u := LevelTower.Head.sort (.succ (.succ Tower.zero)))
    (w := LevelTower.Head.sort Tower.zero) list_typed (LevelTower.IsUniverse.sort _)
    motiveType_formed (LevelTower.IsUniverse.sort _) num_typed_one

/-- The motive of the length at a list is the type of the numbers. -/
theorem lenMotive_at {n : Nat} {Γ : CCtx Tower.Head n} {l : CTm Tower.Head n}
    (hl : CTyped objectLists Γ l clist) :
    CEqual objectLists Γ (.app (.lam clist cnum) l) cnum cU1 :=
  .betaPi (A := clist) (B := cU1) (body := cnum) (a := l)
    (u := LevelTower.Head.sort (.succ (.succ Tower.zero))) motiveType_formed
    (LevelTower.IsUniverse.sort _) num_typed_one hl

/-- Zero is a value of the motive at the empty list. -/
theorem lenZero_typed : CTyped objectLists .nil czero (.app lenMotive cnil) :=
  .conv (ofObject czero_typed) (.symm (lenMotive_at nil_typed)) (LevelTower.IsUniverse.sort _)

/-- The step of the length, at the type of functions from a number, a list and a number to a
number. -/
theorem lenStep_plain :
    CTyped objectLists .nil lenStep (.pi cnum (.pi clist (.pi cnum cnum))) := by
  have inner : CTyped objectLists (.snoc (.snoc .nil cnum) clist) (.pi cnum cnum) cU1 :=
    lpiT num_typed_one num_typed_one
  have middle : CTyped objectLists (.snoc .nil cnum) (.pi clist (.pi cnum cnum)) cU1 :=
    lpiT list_typed_one inner
  have outer : CTyped objectLists .nil (.pi cnum (.pi clist (.pi cnum cnum))) cU1 :=
    lpiT num_typed_one middle
  exact .lamIntro (ofObject cnum_typed) (LevelTower.IsUniverse.sort _) outer
    (LevelTower.IsUniverse.sort _)
    (.lamIntro list_typed (LevelTower.IsUniverse.sort _) middle (LevelTower.IsUniverse.sort _)
      (.lamIntro (ofObject cnum_typed) (LevelTower.IsUniverse.sort _) inner
        (LevelTower.IsUniverse.sort _) (ofObject (csuc_typed (.var 0)))))

/-- The type of the step over the motive of the length is the plain function type. -/
theorem lenStepType_eq :
    CEqual objectLists .nil (.pi cnum (.pi clist (.pi cnum cnum))) (listStepType lenMotive)
      (CU (.max (.succ Tower.zero) (.max (.succ Tower.zero)
        (.max (.succ Tower.zero) (.succ Tower.zero))))) := by
  have atList : CEqual objectLists (.snoc (.snoc .nil cnum) clist) cnum
      (.app (.lam clist cnum) (.var 0)) cU1 := .symm (lenMotive_at (.var 0))
  have atCons : CEqual objectLists (.snoc (.snoc (.snoc .nil cnum) clist) cnum) cnum
      (.app (.lam clist cnum) (ccons (.var 2) (.var 1))) cU1 :=
    .symm (lenMotive_at (cons_typed (.var 2) (.var 1)))
  exact .piCong (.refl num_typed_one) (LevelTower.IsUniverse.sort _)
    (.piCong (.refl list_typed_one) (LevelTower.IsUniverse.sort _)
      (.piCong atList (LevelTower.IsUniverse.sort _) atCons (LevelTower.IsUniverse.sort _)
        (.sorts _ _))
      (LevelTower.IsUniverse.sort _) (.sorts _ _))
    (LevelTower.IsUniverse.sort _) (.sorts _ _)

/-- The step of the length is a step over its motive. -/
theorem lenStep_typed : CTyped objectLists .nil lenStep (listStepType lenMotive) :=
  .conv lenStep_plain lenStepType_eq (LevelTower.IsUniverse.sort _)

/-- **The length of a list is a number.** -/
theorem lengthOf_typed {l : CTm Tower.Head 0} (hl : CTyped objectLists .nil l clist) :
    CTyped objectLists .nil (lengthOf l) cnum :=
  .conv (listRec_typed lenMotive_typed lenZero_typed lenStep_typed hl) (lenMotive_at hl)
    (LevelTower.IsUniverse.sort _)

/-- The step of the length applied to a number, a list and a number is the successor of the
last: three β-steps. -/
theorem lenStep_apply {a as m : CTm Tower.Head 0} (ha : CTyped objectLists .nil a cnum)
    (has : CTyped objectLists .nil as clist) (hm : CTyped objectLists .nil m cnum) :
    CEqual objectLists .nil (.app (.app (.app lenStep a) as) m) (csuc m) cnum := by
  have inner : CTyped objectLists (.snoc (.snoc .nil cnum) clist) (.pi cnum cnum) cU1 :=
    lpiT num_typed_one num_typed_one
  have middle : CTyped objectLists (.snoc .nil cnum) (.pi clist (.pi cnum cnum)) cU1 :=
    lpiT list_typed_one inner
  have outer : CTyped objectLists .nil (.pi cnum (.pi clist (.pi cnum cnum))) cU1 :=
    lpiT num_typed_one middle
  have thirdBody : CTyped objectLists (.snoc (.snoc (.snoc .nil cnum) clist) cnum)
      (csuc (.var 0)) cnum := ofObject (csuc_typed (.var 0))
  have secondBody : CTyped objectLists (.snoc (.snoc .nil cnum) clist)
      (.lam cnum (csuc (.var 0))) (.pi cnum cnum) :=
    .lamIntro (ofObject cnum_typed) (LevelTower.IsUniverse.sort _) inner
      (LevelTower.IsUniverse.sort _) thirdBody
  have firstBody : CTyped objectLists (.snoc .nil cnum)
      (.lam clist (.lam cnum (csuc (.var 0)))) (.pi clist (.pi cnum cnum)) :=
    .lamIntro list_typed (LevelTower.IsUniverse.sort _) middle (LevelTower.IsUniverse.sort _)
      secondBody
  -- The number.
  have beta₁ : CEqual objectLists .nil (.app lenStep a)
      (.lam clist (.lam cnum (csuc (.var 0)))) (.pi clist (.pi cnum cnum)) :=
    .betaPi (A := cnum) (B := .pi clist (.pi cnum cnum))
      (body := .lam clist (.lam cnum (csuc (.var 0)))) (a := a) outer
      (LevelTower.IsUniverse.sort _) firstBody ha
  -- The list.
  have middle₀ : CTyped objectLists .nil (.pi clist (.pi cnum cnum)) cU1 :=
    lpiT list_typed_one (lpiT num_typed_one num_typed_one)
  have secondBody₀ : CTyped objectLists (.snoc .nil clist) (.lam cnum (csuc (.var 0)))
      (.pi cnum cnum) :=
    .lamIntro (ofObject cnum_typed) (LevelTower.IsUniverse.sort _)
      (lpiT num_typed_one num_typed_one) (LevelTower.IsUniverse.sort _)
      (ofObject (csuc_typed (.var 0)))
  have beta₂ : CEqual objectLists .nil (.app (.lam clist (.lam cnum (csuc (.var 0)))) as)
      (.lam cnum (csuc (.var 0))) (.pi cnum cnum) :=
    .betaPi (A := clist) (B := .pi cnum cnum) (body := .lam cnum (csuc (.var 0))) (a := as)
      middle₀ (LevelTower.IsUniverse.sort _) secondBody₀ has
  have applied₂ : CEqual objectLists .nil (.app (.app lenStep a) as)
      (.lam cnum (csuc (.var 0))) (.pi cnum cnum) :=
    .trans (.appCong (B := .pi cnum cnum) beta₁ (.refl has)) beta₂
  -- The length of the shorter list.
  have inner₀ : CTyped objectLists .nil (.pi cnum cnum) cU1 := lpiT num_typed_one num_typed_one
  have beta₃ : CEqual objectLists .nil (.app (.lam cnum (csuc (.var 0))) m) (csuc m) cnum :=
    .betaPi (A := cnum) (B := cnum) (body := csuc (.var 0)) (a := m) inner₀
      (LevelTower.IsUniverse.sort _) (ofObject (csuc_typed (.var 0))) hm
  exact .trans (.appCong (B := cnum) applied₂ (.refl hm)) beta₃

/-- **The length of the one-element list of the numeral one is one**, in the judgment: the
recursor's two computation rules, a congruence, and three β-steps. -/
theorem lengthOf_one :
    CEqual objectLists .nil (lengthOf (ccons (csuc czero) cnil)) (csuc czero) cnum := by
  have one : CTyped objectLists .nil (csuc czero) cnum := ofObject (csuc_typed czero_typed)
  have unfolded : CEqual objectLists .nil (lengthOf (ccons (csuc czero) cnil))
      (.app (.app (.app lenStep (csuc czero)) cnil) czero)
      (.app lenMotive (ccons (csuc czero) cnil)) :=
    listRec_one.substitute (σ := fun i => [lenStep, czero, lenMotive].getD i.val lenMotive)
      (fun j => match j with
        | ⟨0, _⟩ => lenStep_typed
        | ⟨1, _⟩ => lenZero_typed
        | ⟨2, _⟩ => lenMotive_typed)
  exact .trans
    (.convEq unfolded (lenMotive_at (cons_typed one nil_typed)) (LevelTower.IsUniverse.sort _))
    (lenStep_apply one nil_typed (ofObject czero_typed))

/-- In the set model the equation holds: the value of the length of that list is the value of
the numeral one. -/
theorem lengthOf_one_holds (h : CofinalInaccessibles.{u}) :
    Holds (objHeads h) (listConsts h)
      (.equality .nil (lengthOf (ccons (csuc czero) cnil)) (csuc czero) cnum) :=
  objectLists_sound h lengthOf_one

end Length

/-! ## A second program, and a proof by induction -/

section Append

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The motive of appending: every list gives a list. -/
abbrev appMotive : CTm Tower.Head n := .lam clist clist

/-- The step of appending: the first number before the result at the rest. -/
abbrev appStep : CTm Tower.Head n :=
  .lam cnum (.lam clist (.lam clist (ccons (.var 2) (.var 0))))

/-- **A list appended to the empty list**, by recursion on the list. -/
abbrev appendNil (l : CTm Tower.Head n) : CTm Tower.Head n :=
  listRecApp appMotive cnil appStep l

theorem appMotive_typed : CTyped objectLists Γ appMotive (.pi clist cU1) :=
  .lamIntro (u := LevelTower.Head.sort (.succ (.succ Tower.zero)))
    (w := LevelTower.Head.sort Tower.zero) list_typed (LevelTower.IsUniverse.sort _)
    motiveType_formed (LevelTower.IsUniverse.sort _) list_typed_one

/-- The motive of appending at a list is the type of lists. -/
theorem appMotive_at {l : CTm Tower.Head n} (hl : CTyped objectLists Γ l clist) :
    CEqual objectLists Γ (.app appMotive l) clist cU1 :=
  .betaPi (A := clist) (B := cU1) (body := clist) (a := l)
    (u := LevelTower.Head.sort (.succ (.succ Tower.zero))) motiveType_formed
    (LevelTower.IsUniverse.sort _) list_typed_one hl

theorem appNil_typed : CTyped objectLists Γ cnil (.app appMotive cnil) :=
  .conv nil_typed (.symm (appMotive_at nil_typed)) (LevelTower.IsUniverse.sort _)

/-- The step of appending at the plain function type. -/
theorem appStep_plain :
    CTyped objectLists Γ appStep (.pi cnum (.pi clist (.pi clist clist))) := by
  have inner : CTyped objectLists (.snoc (.snoc Γ cnum) clist) (.pi clist clist) cU1 :=
    lpiT list_typed_one list_typed_one
  have middle : CTyped objectLists (.snoc Γ cnum) (.pi clist (.pi clist clist)) cU1 :=
    lpiT list_typed_one inner
  have outer : CTyped objectLists Γ (.pi cnum (.pi clist (.pi clist clist))) cU1 :=
    lpiT num_typed_one middle
  exact .lamIntro (ofObject cnum_typed) (LevelTower.IsUniverse.sort _) outer
    (LevelTower.IsUniverse.sort _)
    (.lamIntro list_typed (LevelTower.IsUniverse.sort _) middle (LevelTower.IsUniverse.sort _)
      (.lamIntro list_typed (LevelTower.IsUniverse.sort _) inner
        (LevelTower.IsUniverse.sort _) (cons_typed (.var 2) (.var 0))))

/-- The type of the step over the motive of appending is the plain function type. -/
theorem appStepType_eq :
    CEqual objectLists Γ (.pi cnum (.pi clist (.pi clist clist))) (listStepType appMotive)
      (CU (.max (.succ Tower.zero) (.max (.succ Tower.zero)
        (.max (.succ Tower.zero) (.succ Tower.zero))))) := by
  have atList : CEqual objectLists (.snoc (.snoc Γ cnum) clist) clist
      (.app (.lam clist clist) (.var 0)) cU1 := .symm (appMotive_at (.var 0))
  have atCons : CEqual objectLists (.snoc (.snoc (.snoc Γ cnum) clist) clist) clist
      (.app (.lam clist clist) (ccons (.var 2) (.var 1))) cU1 :=
    .symm (appMotive_at (cons_typed (.var 2) (.var 1)))
  exact .piCong (.refl num_typed_one) (LevelTower.IsUniverse.sort _)
    (.piCong (.refl list_typed_one) (LevelTower.IsUniverse.sort _)
      (.piCong atList (LevelTower.IsUniverse.sort _) atCons (LevelTower.IsUniverse.sort _)
        (.sorts _ _))
      (LevelTower.IsUniverse.sort _) (.sorts _ _))
    (LevelTower.IsUniverse.sort _) (.sorts _ _)

theorem appStep_typed : CTyped objectLists Γ appStep (listStepType appMotive) :=
  .conv appStep_plain appStepType_eq (LevelTower.IsUniverse.sort _)

/-- **A list appended to the empty list is a list.** -/
theorem appendNil_typed {l : CTm Tower.Head n} (hl : CTyped objectLists Γ l clist) :
    CTyped objectLists Γ (appendNil l) clist :=
  .conv (listRec_typed appMotive_typed appNil_typed appStep_typed hl) (appMotive_at hl)
    (LevelTower.IsUniverse.sort _)

/-- The context of a number and two lists. -/
abbrev appStepCtx : CCtx Tower.Head 3 := .snoc (.snoc (.snoc .nil cnum) clist) clist

/-- The step of appending applied to the variables of a number, a list and a result: the
number before the result. Three β-steps. -/
theorem appStep_apply_variables :
    CEqual objectLists appStepCtx (.app (.app (.app appStep (.var 2)) (.var 1)) (.var 0))
      (ccons (.var 2) (.var 0)) clist := by
  have inner : ∀ {m : Nat} {Δ : CCtx Tower.Head m}, CTyped objectLists Δ (.pi clist clist) cU1 :=
    lpiT list_typed_one list_typed_one
  have middle : ∀ {m : Nat} {Δ : CCtx Tower.Head m},
      CTyped objectLists Δ (.pi clist (.pi clist clist)) cU1 := lpiT list_typed_one inner
  have outer : CTyped objectLists appStepCtx (.pi cnum (.pi clist (.pi clist clist))) cU1 :=
    lpiT num_typed_one middle
  -- The number.
  have firstBody : CTyped objectLists (.snoc appStepCtx cnum)
      (.lam clist (.lam clist (ccons (.var 2) (.var 0)))) (.pi clist (.pi clist clist)) :=
    .lamIntro list_typed (LevelTower.IsUniverse.sort _) middle (LevelTower.IsUniverse.sort _)
      (.lamIntro list_typed (LevelTower.IsUniverse.sort _) inner
        (LevelTower.IsUniverse.sort _) (cons_typed (.var 2) (.var 0)))
  have beta₁ : CEqual objectLists appStepCtx (.app appStep (.var 2))
      (.lam clist (.lam clist (ccons (.var 4) (.var 0)))) (.pi clist (.pi clist clist)) :=
    .betaPi (A := cnum) (B := .pi clist (.pi clist clist))
      (body := .lam clist (.lam clist (ccons (.var 2) (.var 0)))) (a := .var 2) outer
      (LevelTower.IsUniverse.sort _) firstBody (.var 2)
  -- The list.
  have secondBody : CTyped objectLists (.snoc appStepCtx clist)
      (.lam clist (ccons (.var 4) (.var 0))) (.pi clist clist) :=
    .lamIntro list_typed (LevelTower.IsUniverse.sort _) inner (LevelTower.IsUniverse.sort _)
      (cons_typed (.var 4) (.var 0))
  have beta₂ : CEqual objectLists appStepCtx
      (.app (.lam clist (.lam clist (ccons (.var 4) (.var 0)))) (.var 1))
      (.lam clist (ccons (.var 3) (.var 0))) (.pi clist clist) :=
    .betaPi (A := clist) (B := .pi clist clist) (body := .lam clist (ccons (.var 4) (.var 0)))
      (a := .var 1) middle (LevelTower.IsUniverse.sort _) secondBody (.var 1)
  have applied₂ : CEqual objectLists appStepCtx (.app (.app appStep (.var 2)) (.var 1))
      (.lam clist (ccons (.var 3) (.var 0))) (.pi clist clist) :=
    .trans (.appCong (B := .pi clist clist) beta₁ (.refl (.var 1))) beta₂
  -- The result at the rest.
  have beta₃ : CEqual objectLists appStepCtx
      (.app (.lam clist (ccons (.var 3) (.var 0))) (.var 0)) (ccons (.var 2) (.var 0)) clist :=
    .betaPi (A := clist) (B := clist) (body := ccons (.var 3) (.var 0)) (a := .var 0) inner
      (LevelTower.IsUniverse.sort _) (cons_typed (.var 3) (.var 0)) (.var 0)
  exact .trans (.appCong (B := clist) applied₂ (.refl (.var 0))) beta₃

/-- The step of appending applied to a number, a list and a result is the number before the
result. -/
theorem appStep_apply {a as r : CTm Tower.Head n} (ha : CTyped objectLists Γ a cnum)
    (has : CTyped objectLists Γ as clist) (hr : CTyped objectLists Γ r clist) :
    CEqual objectLists Γ (.app (.app (.app appStep a) as) r) (ccons a r) clist :=
  appStep_apply_variables.substitute (σ := fun i => [r, as, a].getD i.val a)
    (fun j => match j with
      | ⟨0, _⟩ => hr
      | ⟨1, _⟩ => has
      | ⟨2, _⟩ => ha)

/-- **The empty list appended to the empty list is the empty list**, by the recursor's rule at
the empty list. -/
theorem appendNil_nil : CEqual objectLists Γ (appendNil cnil) cnil clist :=
  .convEq (listRec_nil appMotive_typed appNil_typed appStep_typed) (appMotive_at nil_typed)
    (LevelTower.IsUniverse.sort _)

/-- **A longer list appended to the empty list** is its first number before the rest appended
to the empty list: the recursor's rule at a longer list and three β-steps. -/
theorem appendNil_cons {a as : CTm Tower.Head n} (ha : CTyped objectLists Γ a cnum)
    (has : CTyped objectLists Γ as clist) :
    CEqual objectLists Γ (appendNil (ccons a as)) (ccons a (appendNil as)) clist :=
  .trans
    (.convEq (listRec_cons appMotive_typed appNil_typed appStep_typed ha has)
      (appMotive_at (cons_typed ha has)) (LevelTower.IsUniverse.sort _))
    (appStep_apply ha has (appendNil_typed has))

/-! ## A proof by induction -/

/-- The statement as a family over the lists: the list appended to the empty list is
identical to the list. -/
abbrev appId : CTm Tower.Head n := .lam clist (.id clist (appendNil (.var 0)) (.var 0))

theorem appIdBody_typed :
    CTyped objectLists (.snoc Γ clist) (.id clist (appendNil (.var 0)) (.var 0)) cU0 :=
  .idForm list_typed (LevelTower.IsUniverse.sort _) (appendNil_typed (.var 0)) (.var 0)

/-- The family is a motive of the recursor. -/
theorem appId_typed : CTyped objectLists Γ appId (.pi clist cU1) :=
  .lamIntro (u := LevelTower.Head.sort (.succ (.succ Tower.zero)))
    (w := LevelTower.Head.sort Tower.zero) list_typed (LevelTower.IsUniverse.sort _)
    motiveType_formed (LevelTower.IsUniverse.sort _) (lraise appIdBody_typed zero_le_one)

/-- The family at a list is the identity type of the appended list and the list. -/
theorem appId_at {l : CTm Tower.Head n} (hl : CTyped objectLists Γ l clist) :
    CEqual objectLists Γ (.app appId l) (.id clist (appendNil l) l) cU1 :=
  .betaPi (A := clist) (B := cU1) (body := .id clist (appendNil (.var 0)) (.var 0)) (a := l)
    (u := LevelTower.Head.sort (.succ (.succ Tower.zero))) motiveType_formed
    (LevelTower.IsUniverse.sort _) (lraise appIdBody_typed zero_le_one) hl

/-- **The base of the induction**: reflexivity at the empty list, since the empty list
appended to the empty list computes to the empty list. -/
theorem appIdNil_typed : CTyped objectLists Γ (.refl cnil) (.app appId cnil) := by
  have computed : CEqual objectLists Γ (.id clist (appendNil cnil) cnil) (.id clist cnil cnil)
      cU0 :=
    .idCong (.refl list_typed) (LevelTower.IsUniverse.sort _) appendNil_nil (.refl nil_typed)
  have atNil : CEqual objectLists Γ (.app appId cnil) (.id clist cnil cnil) cU1 :=
    .trans (appId_at nil_typed) (.cumulEq computed zero_le_one)
  exact .conv (.reflIntro nil_typed) (.symm atNil) (LevelTower.IsUniverse.sort _)

/-- The step of the induction over a number, a list and the induction hypothesis: the
congruence of the hypothesis under "the number before". -/
abbrev appIdStepBody : CTm Tower.Head (n + 3) :=
  congOf clist clist (.app (.const consN) (.var 2)) (appendNil (.var 1)) (.var 1) (.var 0)

/-- **The step of the induction**: from an identity proof for the rest, an identity proof for
the longer list. The longer list appended to the empty list computes to the number before the
rest appended to the empty list, and the hypothesis is carried under "the number before" by
the congruence derived from the identity eliminator. -/
theorem appIdStepBody_typed :
    CTyped objectLists (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0))) appIdStepBody
      (.app appId (ccons (.var 2) (.var 1))) := by
  have number : CTyped objectLists (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0)))
      (.var 2) cnum := .var 2
  have rest : CTyped objectLists (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0)))
      (.var 1) clist := .var 1
  have hypothesis : CTyped objectLists
      (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0))) (.var 0)
      (.id clist (appendNil (.var 1)) (.var 1)) :=
    .conv (.var 0) (appId_at rest) (LevelTower.IsUniverse.sort _)
  have before : CTyped objectLists (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0)))
      (.app (.const consN) (.var 2)) (.pi clist clist) :=
    .appElim (B := .pi clist clist) consConst_typed number
  have congruent : CTyped objectLists
      (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0))) appIdStepBody
      (.id clist (ccons (.var 2) (appendNil (.var 1))) (ccons (.var 2) (.var 1))) :=
    CTyped.substitute (ofObject congTerm_typed)
      (σ := fun i => ([.var 0, .var 1, appendNil (.var 1), .app (.const consN) (.var 2),
        clist, clist] : List (CTm Tower.Head (n + 3))).getD i.val clist)
      (fun j => match j with
        | ⟨0, _⟩ => hypothesis
        | ⟨1, _⟩ => rest
        | ⟨2, _⟩ => appendNil_typed rest
        | ⟨3, _⟩ => before
        | ⟨4, _⟩ => list_typed
        | ⟨5, _⟩ => list_typed)
  have computed : CEqual objectLists (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0)))
      (.id clist (appendNil (ccons (.var 2) (.var 1))) (ccons (.var 2) (.var 1)))
      (.id clist (ccons (.var 2) (appendNil (.var 1))) (ccons (.var 2) (.var 1))) cU0 :=
    .idCong (.refl list_typed) (LevelTower.IsUniverse.sort _) (appendNil_cons number rest)
      (.refl (cons_typed number rest))
  have atCons : CEqual objectLists (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0)))
      (.app appId (ccons (.var 2) (.var 1)))
      (.id clist (ccons (.var 2) (appendNil (.var 1))) (ccons (.var 2) (.var 1))) cU1 :=
    .trans (appId_at (cons_typed number rest)) (.cumulEq computed zero_le_one)
  exact .conv congruent (.symm atCons) (LevelTower.IsUniverse.sort _)

/-- The step of the induction as a term. -/
abbrev appIdStep : CTm Tower.Head n :=
  .lam cnum (.lam clist (.lam (.app appId (.var 0)) appIdStepBody))

theorem appIdStep_typed : CTyped objectLists Γ appIdStep (listStepType appId) := by
  have hypType : CTyped objectLists (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0)) cU1 :=
    .appElim (B := cU1) appId_typed (.var 0)
  have goalType : CTyped objectLists (.snoc (.snoc (.snoc Γ cnum) clist) (.app appId (.var 0)))
      (.app appId (ccons (.var 2) (.var 1))) cU1 :=
    .appElim (B := cU1) appId_typed (cons_typed (.var 2) (.var 1))
  have inner : CTyped objectLists (.snoc (.snoc Γ cnum) clist)
      (.pi (.app appId (.var 0)) (.app appId (ccons (.var 2) (.var 1)))) cU1 :=
    lpiT hypType goalType
  have middle : CTyped objectLists (.snoc Γ cnum)
      (.pi clist (.pi (.app appId (.var 0)) (.app appId (ccons (.var 2) (.var 1))))) cU1 :=
    lpiT list_typed_one inner
  have outer : CTyped objectLists Γ
      (.pi cnum (.pi clist (.pi (.app appId (.var 0)) (.app appId (ccons (.var 2) (.var 1))))))
      cU1 := lpiT num_typed_one middle
  exact .lamIntro (ofObject cnum_typed) (LevelTower.IsUniverse.sort _) outer
    (LevelTower.IsUniverse.sort _)
    (.lamIntro list_typed (LevelTower.IsUniverse.sort _) middle (LevelTower.IsUniverse.sort _)
      (.lamIntro hypType (LevelTower.IsUniverse.sort _) inner (LevelTower.IsUniverse.sort _)
        appIdStepBody_typed))

/-- The proof by induction, as a term: the recursor at the family, at reflexivity for the
empty list, and at the step. -/
abbrev appendNilProof : CTm Tower.Head n :=
  .lam clist (listRecApp appId (.refl cnil) appIdStep (.var 0))

/-- **A proof by induction in the judgment: every list appended to the empty list is identical
to the list.** The proof term is the recursor of the declared type of lists, at the family of
identity types, with reflexivity for the empty list and the congruence of the induction
hypothesis for a longer list. -/
theorem appendNil_identity :
    CTyped objectLists Γ appendNilProof
      (.pi clist (.id clist (appendNil (.var 0)) (.var 0))) :=
  .lamIntro list_typed (LevelTower.IsUniverse.sort _) (lpiT list_typed appIdBody_typed)
    (LevelTower.IsUniverse.sort _)
    (.conv (listRec_typed appId_typed appIdNil_typed appIdStep_typed (.var 0)) (appId_at (.var 0))
      (LevelTower.IsUniverse.sort _))

/-- Positive: at the one-element list of the numeral one, the proof applied to the list is an
identity proof that the list appended to the empty list is the list. -/
theorem appendNil_identity_one :
    CTyped objectLists .nil (.app appendNilProof (ccons (csuc czero) cnil))
      (.id clist (appendNil (ccons (csuc czero) cnil)) (ccons (csuc czero) cnil)) :=
  .appElim appendNil_identity cons_one_nil_typed

end Append

/-- **In the set model, a list appended to the empty list has the value of the list**, for
every closed list of the judgment: the proof by induction is sound. -/
theorem appendNil_value (h : CofinalInaccessibles.{u})
    {l : CTm Tower.Head 0} (hl : CTyped objectLists .nil l clist) :
    ev (objHeads h) (listConsts h) (appendNil l) Fin.elim0 =
      ev (objHeads h) (listConsts h) l Fin.elim0 := by
  have member := objectLists_sound h (CDerivable.appElim appendNil_identity hl) Fin.elim0
    (sat_nil _ _ _)
  exact ((mem_truthCode _ _).mp member).2

/-- Negative: **no closed term is an identity proof that the empty list is the one-element
list**: in the set model the two are values of different constructors. -/
theorem nil_not_identical_to_one (h : CofinalInaccessibles.{u})
    (t : CTm Tower.Head 0) :
    ¬ CTyped objectLists .nil t (.id clist cnil (ccons (csuc czero) cnil)) := fun typed => by
  have reading := inductiveConsts_reading (v := listMotives) (lists_fresh h)
  have member := objectLists_sound h typed Fin.elim0 (sat_nil _ _ _)
  have same : ev (objHeads h) (listConsts h) cnil Fin.elim0 =
      ev (objHeads h) (listConsts h) (ccons (csuc czero) cnil) Fin.elim0 :=
    ((mem_truthCode _ _).mp member).2
  have one := objectLists_sound h
    (ofObject (csuc_typed (czero_typed (Γ := .nil)))) Fin.elim0 (sat_nil _ _ _)
  have empty := objectLists_sound h (nil_typed (Γ := .nil)) Fin.elim0 (sat_nil _ _ _)
  have nilValue : ev (objHeads h) (listConsts h) cnil Fin.elim0 =
      ZFSetInductive.constructorValue (ZFSetInductive.nameCode nilN) [] :=
    ctor_apply (reading.ctor (i := 0) rfl) (args := [])
      ((fits_iff _ _ _ _).mpr ⟨rfl, fun j below => absurd below (Nat.not_lt_zero j)⟩)
  have consValue : ev (objHeads h) (listConsts h) (ccons (csuc czero) cnil) Fin.elim0 =
      ZFSetInductive.constructorValue (ZFSetInductive.nameCode consN)
        [ev (objHeads h) (listConsts h) (csuc czero) Fin.elim0,
          ev (objHeads h) (listConsts h) cnil Fin.elim0] :=
    ctor_apply (reading.ctor (i := 1) rfl)
      (args := [ev (objHeads h) (listConsts h) (csuc czero) Fin.elim0,
        ev (objHeads h) (listConsts h) cnil Fin.elim0])
      ((fits_iff _ _ _ _).mpr ⟨rfl, fun j below => by
      match j, below with
      | 0, _ => exact one
      | 1, _ => exact empty⟩)
  rw [nilValue, consValue] at same
  exact ZFSetInductive.constructorValue_ne_of_tag_ne
    (ZFSetInductive.nameCode_injective.ne (by decide)) _ _ same

/-- Negative: **no set model of the package reads the type of lists as the empty set**: the
empty list is a member. -/
theorem no_setModel_of_empty_lists (h : CofinalInaccessibles.{u}) {consts : DeclName → ZFSet.{u}}
    (empty : consts listN = ∅) : ¬ SetModel (objHeads h) consts objectLists := fun model => by
  have member : consts nilN ∈ consts listN :=
    model.constants (c := nilN) (T := .const listN) (by decide)
  rw [empty] at member
  exact ZFSet.notMem_empty _ member

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
