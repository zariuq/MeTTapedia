import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetTheory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetDeclarationLists

/-!
# Declared datatypes are sets

Over the tower inside the sets with the constants of set theory (`MegalodonHOTG.SetTheory`), a
program declares datatypes and definitions one after the other (`withDeclarations`). The
universe of a datatype is a parameter of its declaration, and the type of all sets is a
universe. So a datatype can be declared **at the type of all sets**: `list : set`.

**For every admissible list of declarations** over the package of set theory, relative to
cofinally many inaccessible cardinals in two universes: the package has a set model
(`ambientDeclarations_model`) in which the constants of set theory keep their reading
(`ambientDeclarations_reads`), and no closed term has the type `Π (A : set). A`
(`ambientDeclarations_consistent`).

**A datatype declared at the type of all sets is a set** (`datatype_isSet`), and a term of it
is a member of it, with a proof term (`datatype_member`): typing and membership are two
readings of one fact.

**What the sets refuse**: in the model nothing is a member of the empty set, so for a term `a`
of a type `A` that is a set, no closed term proves `In (elem A a) Empty`
(`no_proof_in_empty`).

The example (`Declared`): the natural numbers and the lists of numbers, both declared at the
type of all sets, the second with a field of the first. The list is admissible
(`Declared.datatypes_admissible`). Positive examples: `num` and `list` are sets
(`Declared.num_isSet`, `Declared.list_isSet`); `zero` is a member of `num` and `nil` is a
member of `list`, each with a proof term (`Declared.zero_member`, `Declared.nil_member`).
Negative examples: no closed term proves that `zero` is a member of the empty set
(`Declared.zero_not_in_empty`), and none proves that `zero` is a member of the lists
(`Declared.zero_not_in_list`).

**Constructors of different datatypes are different sets.** A constructor is read by its
name: the value of `zero` is the constructor value of the code of the name `zero` at no
argument, and the value of `nil` that of the name `nil` (`Declared.zero_value`,
`Declared.nil_value`). So the values of `zero` and `nil` differ
(`Declared.zero_value_ne_nil_value`), the numbers and the lists are disjoint sets in the model
(`Declared.num_list_disjoint`), the proposition that `zero` is a member of the lists is false
in the model (`Declared.zero_in_list_false`), and no closed term of the package proves it
(`Declared.zero_not_in_list`). The two constants are two symbols when run, and two sets here.

**A typed data term means its set.** The list whose one member is `zero`, written as a data
term, is typed as a list (`Declared.zeroList_typed`), and the value of its term in the model
is the set of the data term: the code of the name `cons` paired with the tuple of the sets of
`zero` and `nil` (`Declared.zeroList_value`). Negative example: the term of `cons nil nil` is
not typed, its arguments do not fit the fields of `cons`, and its value is the empty set and
not the set of the data term (`Declared.nilList_value`, `Declared.nilList_value_ne_toSet`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated

universe u

namespace MegalodonHOTG

open Presentation.TypedEquality.Normalization (LevelModel)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles Closed univOf)
open ZFSetUniverseLift (carrierCode carrierCode_closed omega_mem_carrierCode)
open ZFSetInterpretation (universeSet seed_mem_universeSet)
open ZFSetTraceProducts (traceApp tracePiSet)
open ZFSetTraceProofDecoding (mem_truthCode)
open ZFSetInductive (constructorValue nameCode DataTerm)

variable {L : Type} [LevelOrder L]

/-- The universe of the sets, as a head. -/
abbrev setsHead : Head L := .sort (.const (.above 0))

/-- The universe above the sets, as a head. -/
abbrev classesHead : Head L := .sort (.const (.above 1))

/-- The universe rules of the package of set theory, read at levels. -/
abbrev setTheoryLevels (L : Type) [LevelOrder L] :
    LevelModel (Rules.sum (rules L) (familyRules (rules L) (setDecls L) (setEquations L)))
      (Above L) :=
  Annotated.LevelModel.sum
    (Normalization.TowerModel.levels fun _ => (LevelOrder.bot : Above L)) _

/-- The type of the members of every set. -/
def everySet : CTm (Head L) 0 := .pi allSets (.var 0)

/-! ## Every admissible list of declarations -/

/-- The assignment of the constants of set theory at the stages. -/
noncomputable abbrev setTheoryConsts (L : Type) [LevelOrder L]
    (large : CofinalInaccessibles.{u + 1}) (base : DeclName → ZFSet.{u + 1}) :
    DeclName → ZFSet.{u + 1} :=
  familyConsts base (setDecls L)
    (setValues (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      (univOf large))

/-- The assignment of the model: the constants of set theory, and the declarations read over
them one after the other. -/
noncomputable abbrev ambientConsts (large : CofinalInaccessibles.{u + 1}) (ν : Nat → Above L)
    (ground : ZFSet.{u + 1}) (base : DeclName → ZFSet.{u + 1})
    (ds : List (Declaration (Head L))) : DeclName → ZFSet.{u + 1} :=
  declarationsConsts (lowerSetsHeads (L := L) large ground ν) (setTheoryConsts L large base) ds

section General

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} (ν : Nat → Above L) {ds : List (Declaration (Head L))}

include small in
/-- The universe of every datatype of an admissible list is read as a closed set that holds
the natural numbers. -/
theorem ambientDeclarations_universes (admissible : AdmissibleDeclarations (setTheory L) ds) :
    ∀ d : Datatype (Head L), Declaration.datatype d ∈ ds →
      Closed (lowerSetsHeads (L := L) large ground ν d.typeUniverse) ∧
        ZFSet.omega ∈ lowerSetsHeads (L := L) large ground ν d.typeUniverse := by
  intro d member
  have isUniverse : LevelTower.IsUniverse d.typeUniverse := admissible.typeUniverse member
  have chain := stages_closedChain (L := L) small large
  cases found : d.typeUniverse with
  | sort level =>
    exact ⟨chain.closed _, chain.mono (LevelOrder.bot_le _)
      (seed_mem_universeSet large ZFSet.omega (LevelOrder.bot : L))⟩
  | legacyGround =>
    rw [found] at isUniverse
    exact nomatch isUniverse

variable {ν}

include small in
/-- **The tower inside the sets with the constants of set theory and an admissible list of
declarations has a set model**, relative to cofinally many inaccessible cardinals in two
universes. -/
theorem ambientDeclarations_model
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) (admissible : AdmissibleDeclarations (setTheory L) ds) :
    SetModel (lowerSetsHeads (L := L) large ground ν) (ambientConsts large ν ground base ds)
      (withDeclarations (setTheory L) ds) :=
  declarations_setModel_read (setTheoryLevels L) (setTheory L)
    (fun consts agrees =>
      lowerSets_setTheory_setModel_of_agreeing small large ν groundTyped base consts agrees)
    admissible (ambientDeclarations_universes small large ν admissible)

/-- **The constants of set theory keep their reading** in the model of an admissible list of
declarations. -/
theorem ambientDeclarations_reads (base : DeclName → ZFSet.{u + 1})
    (admissible : AdmissibleDeclarations (setTheory L) ds) :
    Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1)) (univOf large)
      (ambientConsts large ν ground base ds) := by
  intro c declared
  have inPackage : (setTheory L).constantType c ≠ none := by
    cases found : setDecls L c with
    | none => exact absurd found declared
    | some T =>
      rw [setTheory_declared found]
      exact Option.some_ne_none T
  exact (declarationsConsts_base (setTheory L) inPackage ds admissible).trans
    (familyConsts_declared declared)

/-- The type of the members of every set has no member in the model. -/
theorem ev_everySet (consts : DeclName → ZFSet.{u + 1}) (z : ZFSet.{u + 1}) :
    z ∉ ev (lowerSetsHeads (L := L) large ground ν) consts everySet Fin.elim0 := by
  intro member
  change z ∈ tracePiSet carrierCode.{u} (fun x => x) at member
  exact ZFSet.notMem_empty _
    (traceApp_mem_fibre member (carrierCode_closed.empty_mem omega_mem_carrierCode))

include small large in
/-- **Consistency**, relative to cofinally many inaccessible cardinals in two universes: no
closed term of the package with an admissible list of declarations has the type
`Π (A : set). A`. -/
theorem ambientDeclarations_consistent (admissible : AdmissibleDeclarations (setTheory L) ds)
    (t : CTm (Head L) 0) : ¬ CTyped (withDeclarations (setTheory L) ds) .nil t everySet :=
  CDerivable.no_closed_inhabitant
    (ambientDeclarations_model small large (ν := fun _ => LevelOrder.bot)
      (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) (fun _ => ∅) admissible)
    (ev_everySet large _) t

end General

/-! ## Datatypes at the type of all sets -/

section Sets

variable {ds : List (Declaration (Head L))} {n : Nat} {Γ : CCtx (Head L) n}

/-- The package with a list of declarations is over the set theory. -/
theorem withDeclarations_over (ds : List (Declaration (Head L))) :
    OverSetTheory (withDeclarations (setTheory L) ds) :=
  OverSetTheory.of_sub (withDeclarations_base (setTheory L) ds)

variable (admissible : AdmissibleDeclarations (setTheory L) ds)

include admissible

/-- **A datatype declared at the type of all sets is a set.** -/
theorem datatype_isSet {d : Datatype (Head L)} (member : Declaration.datatype d ∈ ds)
    (atSets : d.typeUniverse = setsHead) :
    CTyped (withDeclarations (setTheory L) ds) Γ (.const d.type) allSets := by
  have typed := AdmissibleDeclarations.type_typed (setTheoryLevels L) admissible member (Γ := Γ)
  rwa [atSets] at typed

/-- **A term of a datatype declared at the type of all sets is a member of the datatype**,
with a proof term. -/
theorem datatype_member {d : Datatype (Head L)} (member : Declaration.datatype d ∈ ds)
    (atSets : d.typeUniverse = setsHead) {t : CTm (Head L) n}
    (typed : CTyped (withDeclarations (setTheory L) ds) Γ t (.const d.type)) :
    CTyped (withDeclarations (setTheory L) ds) Γ (cMember (.const d.type) t)
      (cHolds (cIn (cElem (.const d.type) t) (.const d.type))) :=
  member_typed (withDeclarations_over ds) (datatype_isSet admissible member atSets) typed

omit admissible

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})

include small large admissible in
/-- **What the sets refuse**: for a closed term of a closed type that is a set, no closed term
proves that it is a member of the empty set. -/
theorem no_proof_in_empty {A a : CTm (Head L) 0}
    (hA : CTyped (withDeclarations (setTheory L) ds) .nil A allSets)
    (ha : CTyped (withDeclarations (setTheory L) ds) .nil a A) (t : CTm (Head L) 0) :
    ¬ CTyped (withDeclarations (setTheory L) ds) .nil t (cHolds (cIn (cElem A a) cEmpty)) := by
  have model := ambientDeclarations_model small large (L := L) (ν := fun _ => LevelOrder.bot)
    (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) (fun _ => ∅) admissible
  have reads := ambientDeclarations_reads large (L := L) (ν := fun _ => LevelOrder.bot)
    (ground := ∅) (fun _ => ∅) admissible
  have chain := stages_closedChain (L := L) small large
  have setA : ev (lowerSetsHeads (L := L) large ∅ fun _ => LevelOrder.bot)
      (ambientConsts large (fun _ => LevelOrder.bot) ∅ (fun _ => ∅) ds) A Fin.elim0 ∈
      stages (L := L) large (.above 0) :=
    CDerivable.sound model hA Fin.elim0 (sat_nil _ _ Fin.elim0)
  have memberA := CDerivable.sound model ha Fin.elim0 (sat_nil _ _ Fin.elim0)
  have emptyAll : (∅ : ZFSet.{u + 1}) ∈ stages (L := L) large (.above 0) :=
    carrierCode_closed.empty_mem omega_mem_carrierCode
  refine CDerivable.no_closed_inhabitant model (fun z inside => ?_) t
  change z ∈ traceApp (ambientConsts large (fun _ => LevelOrder.bot) ∅ (fun _ => ∅) ds holdsN)
    (traceApp (traceApp (ambientConsts large (fun _ => LevelOrder.bot) ∅ (fun _ => ∅) ds inN)
      (traceApp (traceApp (ambientConsts large (fun _ => LevelOrder.bot) ∅ (fun _ => ∅) ds elemN)
        (ev _ _ A Fin.elim0)) (ev _ _ a Fin.elim0)))
      (ambientConsts large (fun _ => LevelOrder.bot) ∅ (fun _ => ∅) ds emptyN)) at inside
  rw [reads.holds, reads.in, reads.elem, reads.empty, elemValue_apply setA memberA,
    inValue_apply ((chain.closed _).transitive _ setA memberA) emptyAll,
    holdsValue_apply (truthCode_mem_truthValues _)] at inside
  exact ZFSet.notMem_empty _ ((mem_truthCode _ _).mp inside).2

end Sets

/-! ## The numbers and the lists of numbers, declared at the type of all sets -/

namespace Declared

/-- The type of the natural numbers. -/
def numN : DeclName := .str .anonymous "num"
/-- Zero. -/
def zeroN : DeclName := .str .anonymous "zero"
/-- The successor. -/
def sucN : DeclName := .str .anonymous "suc"
/-- The recursor of the natural numbers. -/
def numRecN : DeclName := .str .anonymous "num-rec"
/-- The type of the lists of numbers. -/
def listN : DeclName := .str .anonymous "list"
/-- The empty list. -/
def nilN : DeclName := .str .anonymous "nil"
/-- A number in front of a list. -/
def consN : DeclName := .str .anonymous "cons"
/-- The recursor of the lists. -/
def listRecN : DeclName := .str .anonymous "list-rec"

variable (L) in
/-- The constructors of the natural numbers. -/
def numCtors : List (DeclName × List (Normalization.Field (Head L))) :=
  [(zeroN, []), (sucN, [.recursive])]

variable (L) in
/-- The constructors of the lists: the field of `cons` is a number. -/
def listCtors : List (DeclName × List (Normalization.Field (Head L))) :=
  [(nilN, []), (consN, [.closed (.const numN), .recursive])]

variable (L) in
/-- **The natural numbers, declared at the type of all sets.** -/
def numDecl : Datatype (Head L) where
  type := numN
  typeUniverse := setsHead
  ctors := numCtors L
  recursor := numRecN
  motiveUniverse := classesHead

variable (L) in
/-- **The lists of numbers, declared at the type of all sets.** -/
def listDecl : Datatype (Head L) where
  type := listN
  typeUniverse := setsHead
  ctors := listCtors L
  recursor := listRecN
  motiveUniverse := classesHead

variable (L) in
/-- The two declarations: the numbers first, then the lists. -/
abbrev datatypes : List (Declaration (Head L)) := [.datatype (listDecl L), .datatype (numDecl L)]

variable (L) in
/-- **The package of set theory with the numbers and the lists.** -/
abbrev declared := withDeclarations (setTheory L) (datatypes L)

/-- The declaration of the numbers is admissible over the package of set theory. -/
theorem numDecl_admissible : (numDecl L).Admissible (setTheory L) where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct :=
    { ctorsNodup := by
        show [zeroN, sucN].Nodup
        decide
      typeNotCtor := by
        show numN ∉ [zeroN, sucN]
        decide
      recNotType := by
        show numRecN ≠ numN
        decide
      recNotCtor := by
        show numRecN ∉ [zeroN, sucN]
        decide }
  new :=
    { typeNew := rfl
      ctorsNew := by
        intro entry member
        have member' : entry ∈ numCtors L := member
        simp only [numCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
        rcases member' with rfl | rfl <;> rfl
      recNew := rfl }
  lamFree := by
    intro entry member F field
    have member' : entry ∈ numCtors L := member
    simp only [numCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact nomatch field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      exact nomatch field
  fields := by
    intro entry member F field
    have member' : entry ∈ numCtors L := member
    simp only [numCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact nomatch field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      exact nomatch field

/-- The numbers alone are an admissible list. -/
theorem numbers_admissible : AdmissibleDeclarations (setTheory L) [.datatype (numDecl L)] :=
  ⟨trivial, numDecl_admissible⟩

/-- The declaration of the lists is admissible over the package with the numbers. -/
theorem listDecl_admissible :
    (listDecl L).Admissible (withDeclarations (setTheory L) [.datatype (numDecl L)]) where
  typeUniverse := LevelTower.IsUniverse.sort _
  motiveUniverse := LevelTower.IsUniverse.sort _
  distinct :=
    { ctorsNodup := by
        show [nilN, consN].Nodup
        decide
      typeNotCtor := by
        show listN ∉ [nilN, consN]
        decide
      recNotType := by
        show listRecN ≠ listN
        decide
      recNotCtor := by
        show listRecN ∉ [nilN, consN]
        decide }
  new :=
    { typeNew := rfl
      ctorsNew := by
        intro entry member
        have member' : entry ∈ listCtors L := member
        simp only [listCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
        rcases member' with rfl | rfl <;> rfl
      recNew := rfl }
  lamFree := by
    intro entry member F field
    have member' : entry ∈ listCtors L := member
    simp only [listCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact nomatch field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with same | impossible
      · obtain rfl : F = .const numN := by injection same
        rfl
      · exact nomatch impossible
  fields := by
    intro entry member F field
    have member' : entry ∈ listCtors L := member
    simp only [listCtors, List.mem_cons, List.not_mem_nil, or_false] at member'
    rcases member' with rfl | rfl
    · exact nomatch field
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at field
      rcases field with same | impossible
      · obtain rfl : F = .const numN := by injection same
        exact AdmissibleDeclarations.type_typed (setTheoryLevels L) numbers_admissible
          List.mem_cons_self
      · exact nomatch impossible

/-- **The numbers and then the lists are an admissible list of declarations.** -/
theorem datatypes_admissible : AdmissibleDeclarations (setTheory L) (datatypes L) :=
  ⟨numbers_admissible, listDecl_admissible⟩

omit [LevelOrder L] in
/-- The numbers are among the two declarations. -/
theorem numDecl_mem : Declaration.datatype (numDecl L) ∈ datatypes L :=
  List.mem_cons_of_mem _ List.mem_cons_self

omit [LevelOrder L] in
/-- The lists are among the two declarations. -/
theorem listDecl_mem : Declaration.datatype (listDecl L) ∈ datatypes L := List.mem_cons_self

section Judgment

variable {n : Nat} {Γ : CCtx (Head L) n}

/-- The type of the numbers. -/
abbrev cnum : CTm (Head L) n := .const numN
/-- Zero. -/
abbrev czero : CTm (Head L) n := .const zeroN
/-- The type of the lists. -/
abbrev clist : CTm (Head L) n := .const listN
/-- The empty list. -/
abbrev cnil : CTm (Head L) n := .const nilN

/-- Positive example: **the numbers are a set.** -/
theorem num_isSet : CTyped (declared L) Γ cnum allSets :=
  datatype_isSet datatypes_admissible numDecl_mem rfl

/-- Positive example: **the lists are a set.** -/
theorem list_isSet : CTyped (declared L) Γ clist allSets :=
  datatype_isSet datatypes_admissible listDecl_mem rfl

/-- Zero is a number. -/
theorem zero_typed : CTyped (declared L) Γ czero cnum :=
  AdmissibleDeclarations.ctor_typed (setTheoryLevels L) datatypes_admissible numDecl_mem
    (i := 0) rfl

/-- The empty list is a list. -/
theorem nil_typed : CTyped (declared L) Γ cnil clist :=
  AdmissibleDeclarations.ctor_typed (setTheoryLevels L) datatypes_admissible listDecl_mem
    (i := 0) rfl

/-- Positive example: **zero is a member of the numbers**, with a proof term. -/
theorem zero_member :
    CTyped (declared L) Γ (cMember cnum czero) (cHolds (cIn (cElem cnum czero) cnum)) :=
  datatype_member datatypes_admissible numDecl_mem rfl zero_typed

/-- Positive example: **the empty list is a member of the lists**, with a proof term. -/
theorem nil_member :
    CTyped (declared L) Γ (cMember clist cnil) (cHolds (cIn (cElem clist cnil) clist)) :=
  datatype_member datatypes_admissible listDecl_mem rfl nil_typed

end Judgment

/-- Negative example: **no closed term proves that zero is a member of the empty set**,
relative to cofinally many inaccessible cardinals in two universes. -/
theorem zero_not_in_empty (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) (t : CTm (Head L) 0) :
    ¬ CTyped (declared L) .nil t (cHolds (cIn (cElem cnum czero) cEmpty)) :=
  no_proof_in_empty datatypes_admissible small large num_isSet zero_typed t

/-! ## The two datatypes are apart -/

section Reading

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} {ν : Nat → Above L} (base : DeclName → ZFSet.{u + 1})

/-- The model reads the declaration of the numbers. -/
theorem num_reading :
    InductiveReading (lowerSetsHeads (L := L) large ground ν)
      (ambientConsts large ν ground base (datatypes L)) numN classesHead (numCtors L) numRecN :=
  declarations_reading (heads := lowerSetsHeads (L := L) large ground ν)
    (base := setTheoryConsts L large base) (setTheory L) (datatypes L) datatypes_admissible
    (numDecl L) numDecl_mem _ fun _ _ => rfl

/-- The model reads the declaration of the lists. -/
theorem list_reading :
    InductiveReading (lowerSetsHeads (L := L) large ground ν)
      (ambientConsts large ν ground base (datatypes L)) listN classesHead (listCtors L)
      listRecN :=
  declarations_reading (heads := lowerSetsHeads (L := L) large ground ν)
    (base := setTheoryConsts L large base) (setTheory L) (datatypes L) datatypes_admissible
    (listDecl L) listDecl_mem _ fun _ _ => rfl

/-- **The value of `zero`**: the constructor value of the code of its name at no argument. -/
theorem zero_value :
    ambientConsts large ν ground base (datatypes L) zeroN = constructorValue (nameCode zeroN) [] :=
  (num_reading large base).constant_value (i := 0) rfl

/-- **The value of `nil`**: the constructor value of the code of its name at no argument. -/
theorem nil_value :
    ambientConsts large ν ground base (datatypes L) nilN = constructorValue (nameCode nilN) [] :=
  (list_reading large base).constant_value (i := 0) rfl

/-- **The values of `zero` and `nil` differ**: the two constants have different names, and a
constructor is read by its name. -/
theorem zero_value_ne_nil_value :
    ambientConsts large ν ground base (datatypes L) zeroN ≠
      ambientConsts large ν ground base (datatypes L) nilN := by
  rw [zero_value large base, nil_value large base]
  exact ZFSetInductive.constructorValue_ne_of_tag_ne
    (ZFSetInductive.nameCode_injective.ne (by decide)) [] []

omit [LevelOrder L] in
/-- The numbers and the lists have no constructor name in common. -/
theorem num_list_apart : ∀ k, k ∈ (numCtors L).map (·.1) → k ∉ (listCtors L).map (·.1) := by
  show ∀ k, k ∈ [zeroN, sucN] → k ∉ [nilN, consN]
  decide

/-- **The numbers and the lists are disjoint sets** in the model: no set is a member of both. -/
theorem num_list_disjoint {x : ZFSet.{u + 1}}
    (member : x ∈ ambientConsts large ν ground base (datatypes L) numN) :
    x ∉ ambientConsts large ν ground base (datatypes L) listN :=
  (num_reading large base).disjoint (list_reading large base) num_list_apart member

/-- **In the model the value of `zero` is not a member of the lists.** -/
theorem zero_value_not_mem_list :
    ambientConsts large ν ground base (datatypes L) zeroN ∉
      ambientConsts large ν ground base (datatypes L) listN := by
  rw [zero_value large base]
  exact (list_reading large base).foreign_not_mem
    (by show zeroN ∉ [nilN, consN]; decide) []

include small in
/-- **The proposition that `zero` is a member of the lists is false in the model**: its set of
proofs is empty. `zero` is declared a number, and the two datatypes have no constructor name
in common. -/
theorem zero_in_list_false
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (z : ZFSet.{u + 1}) :
    z ∉ ev (lowerSetsHeads (L := L) large ground ν)
      (ambientConsts large ν ground base (datatypes L))
      (cHolds (cIn (cElem cnum czero) clist) : CTm (Head L) 0) Fin.elim0 := by
  intro inside
  have model := ambientDeclarations_model small large (ν := ν) groundTyped base
    (datatypes_admissible (L := L))
  have reads := ambientDeclarations_reads large (ν := ν) (ground := ground) base
    (datatypes_admissible (L := L))
  have chain := stages_closedChain (L := L) small large
  have setNum : ambientConsts large ν ground base (datatypes L) numN ∈
      stages (L := L) large (.above 0) :=
    CDerivable.sound model (num_isSet (Γ := .nil)) Fin.elim0 (sat_nil _ _ Fin.elim0)
  have setList : ambientConsts large ν ground base (datatypes L) listN ∈
      stages (L := L) large (.above 0) :=
    CDerivable.sound model (list_isSet (Γ := .nil)) Fin.elim0 (sat_nil _ _ Fin.elim0)
  have zeroNum : ambientConsts large ν ground base (datatypes L) zeroN ∈
      ambientConsts large ν ground base (datatypes L) numN :=
    CDerivable.sound model (zero_typed (Γ := .nil)) Fin.elim0 (sat_nil _ _ Fin.elim0)
  change z ∈ traceApp (ambientConsts large ν ground base (datatypes L) holdsN)
    (traceApp (traceApp (ambientConsts large ν ground base (datatypes L) inN)
      (traceApp (traceApp (ambientConsts large ν ground base (datatypes L) elemN)
        (ambientConsts large ν ground base (datatypes L) numN))
        (ambientConsts large ν ground base (datatypes L) zeroN)))
      (ambientConsts large ν ground base (datatypes L) listN)) at inside
  rw [reads.holds, reads.in, reads.elem, elemValue_apply setNum zeroNum,
    inValue_apply ((chain.closed _).transitive _ setNum zeroNum) setList,
    holdsValue_apply (truthCode_mem_truthValues _)] at inside
  exact zero_value_not_mem_list large base ((mem_truthCode _ _).mp inside).2

/-! ## A typed data term means its set -/

/-- The list whose one member is `zero`, as a data term. -/
def zeroList : DataTerm := .app consN [.app zeroN [], .app nilN []]

/-- `cons nil nil`, as a data term: the first argument of `cons` is not a number. -/
def nilList : DataTerm := .app consN [.app nilN [], .app nilN []]

omit [LevelOrder L] in
/-- `zero` is a data term over the two datatypes. -/
theorem zero_over : DataOver (datatypes L) (.app zeroN []) :=
  .app (d := numDecl L) (i := 0) numDecl_mem rfl rfl (fun _ member => nomatch member)
    (fun _ member => nomatch member)

omit [LevelOrder L] in
/-- `nil` is a data term over the two datatypes. -/
theorem nil_over : DataOver (datatypes L) (.app nilN []) :=
  .app (d := listDecl L) (i := 0) listDecl_mem rfl rfl (fun _ member => nomatch member)
    (fun _ member => nomatch member)

omit [LevelOrder L] in
/-- `cons` at two data terms over the two datatypes is a data term over them. -/
theorem cons_over {a l : DataTerm} (ha : DataOver (datatypes L) a)
    (hl : DataOver (datatypes L) l) : DataOver (datatypes L) (.app consN [a, l]) :=
  .app (d := listDecl L) (i := 1) listDecl_mem rfl rfl
    (fun F member => by
      rcases List.mem_cons.mp member with same | member
      · obtain rfl : F = .const numN := by injection same
        exact ⟨numDecl L, numDecl_mem, rfl⟩
      · rcases List.mem_cons.mp member with bad | member
        · exact nomatch bad
        · exact nomatch member)
    (fun x member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact ha
      · rcases List.mem_cons.mp member with rfl | member
        · exact hl
        · exact nomatch member)

/-- The term of the list whose one member is `zero` is a list. -/
theorem zeroList_typed {n : Nat} {Γ : CCtx (Head L) n} :
    CTyped (declared L) Γ (liftTm (dataTm zeroList)) clist := by
  have spine : (dataTm zeroList : Tm (Head L) n) =
      Normalization.appSpine (.const consN) [.const zeroN, .const nilN] := by
    simp only [zeroList, dataTm_app, dataTms_eq_map, List.map_cons, List.map_nil,
      Normalization.appSpine_nil]
  rw [spine]
  exact AdmissibleDeclarations.ctor_spine_typed (setTheoryLevels L) datatypes_admissible
    listDecl_mem (i := 1) rfl (.cons zero_typed (.cons nil_typed .nil))

include small in
/-- Positive example: **the value of the list whose one member is `zero` is its set**: the
code of the name `cons` paired with the tuple of the sets of `zero` and `nil`. -/
theorem zeroList_value
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L)) :
    ev (lowerSetsHeads (L := L) large ground ν)
        (ambientConsts large ν ground base (datatypes L)) (liftTm (dataTm zeroList)) Fin.elim0 =
      zeroList.toSet :=
  declarations_dataTerm_value (heads := lowerSetsHeads (L := L) large ground ν)
    (base := setTheoryConsts L large base) (setTheory L) datatypes_admissible (fun _ _ => rfl)
    (ambientDeclarations_model small large (ν := ν) groundTyped base datatypes_admissible)
    (cons_over zero_over nil_over) listDecl_mem zeroList_typed

/-- Negative example: **the term of `cons nil nil` means nothing.** The empty list is not a
number, so the arguments do not fit the fields of `cons`, and the value of the term is the
empty set. -/
theorem nilList_value :
    ev (lowerSetsHeads (L := L) large ground ν)
        (ambientConsts large ν ground base (datatypes L)) (liftTm (dataTm nilList)) Fin.elim0 =
      ∅ := by
  rw [nilList, ev_dataTm]
  refine ctor_apply_outside ((list_reading large base).ctor (i := 1) rfl) rfl fun fits => ?_
  have inNum : ambientConsts large ν ground base (datatypes L) nilN ∈
      ambientConsts large ν ground base (datatypes L) numN :=
    ((fits_iff _ _ _ _).mp fits).2 0 (by show 0 < 2; decide)
  rw [nil_value large base] at inNum
  exact (num_reading large base).foreign_not_mem (by show nilN ∉ [zeroN, sucN]; decide) [] inNum

/-- So the value of that term is not the set of the data term. -/
theorem nilList_value_ne_toSet :
    ev (lowerSetsHeads (L := L) large ground ν)
        (ambientConsts large ν ground base (datatypes L)) (liftTm (dataTm nilList)) Fin.elim0 ≠
      nilList.toSet := by
  rw [nilList_value large base, nilList, DataTerm.toSet_app]
  exact (ZFSetInductive.constructorValue_ne_empty _ _).symm

end Reading

/-- Negative example: **no closed term proves that `zero` is a member of the lists**, relative
to cofinally many inaccessible cardinals in two universes. -/
theorem zero_not_in_list (small : CofinalInaccessibles.{u})
    (large : CofinalInaccessibles.{u + 1}) (t : CTm (Head L) 0) :
    ¬ CTyped (declared L) .nil t (cHolds (cIn (cElem cnum czero) clist)) :=
  CDerivable.no_closed_inhabitant
    (ambientDeclarations_model small large (ν := fun _ => LevelOrder.bot)
      (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) (fun _ => ∅)
      datatypes_admissible)
    (zero_in_list_false small large (fun _ => ∅)
      (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L))) t

end Declared

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
