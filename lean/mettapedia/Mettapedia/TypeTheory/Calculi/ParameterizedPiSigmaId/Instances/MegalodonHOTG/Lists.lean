import Mettapedia.Logic.HOL.Embedding.ZFSetPolymorphicLists
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetsModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetConstantFamilies

/-!
# Lists over a set, declared once in the tower inside the sets

Over the tower inside the sets, one family declares lists at a set, with no universe level
written:

* `List : set → set`
* `nil : Π (A : set). List A`
* `cons : Π (A : set). A → List A → List A`
* `append : Π (A : set). List A → List A → List A`

with the two equations of append. `set` is the type of all sets. A member of it is a type, so
the arrow after a set variable is a function type over that variable.

The set model reads `List` as the trace function `A ↦ listSet nilTag consTag A` on the
universe of all sets, and the other three constants as the trace-coded empty list, cons and
append. The two constructors are read by their names: the empty list and an element before a
list carry the codes of the names `nil` and `cons` as their tags (`nilTag`, `consTag`), so
`nil A` is the same set at every `A`, and a `cons` is never a `nil`
(`nil_not_convertible_with_cons`). The model holds over
every chain of closed universes that has `ω` in the universe of the sets, and in particular
over the stages that read the type of all sets as every set of the lower universe.

In that reading, a set that belongs to the universe at a level of the tower has its lists in
the same universe. The declaration itself says only `List A : set`. No closed term inhabits
`Π (A : set). A`. The same family with `List : set → U₀` has no set model on those stages
when `List` is read as the set of lists.

The typings of the four constants hold in every package over the family (`OverLists`), so
they hold where further constants, datatypes and definitions are declared. In a package that
also contains the steps of the family (`ComputesAsLists`), the two equations of append hold at
all typed instances (`append_nil_rule`, `append_cons_rule`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace Lists

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetPolymorphicLists
open ZFSetUniverseClosure (Closed CofinalInaccessibles)
open ZFSetUniverseLift (carrierCode carrierCode_closed omega_mem_carrierCode)
open ZFSetInterpretation (universeSet universeSet_closed seed_mem_universeSet)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta tracePiSet_congr)

universe u

variable {L : Type}

/-! ## The constants and their types -/

/-- The set of lists over a set. -/
def listN : DeclName := .str .anonymous "List"

/-- The empty list. -/
def nilN : DeclName := .str .anonymous "nil"

/-- An element before a list. -/
def consN : DeclName := .str .anonymous "cons"

/-- Append of two lists. -/
def appendN : DeclName := .str .anonymous "append"

section Terms

variable [LevelOrder L] {n : Nat}

/-- `List A`. -/
abbrev cList (A : CTm (Head L) n) : CTm (Head L) n := .app (.const listN) A

/-- `nil A`. -/
abbrev cNil (A : CTm (Head L) n) : CTm (Head L) n := .app (.const nilN) A

/-- `cons A x xs`. -/
abbrev cCons (A x xs : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const consN) A) x) xs

/-- `append A xs ys`. -/
abbrev cAppend (A xs ys : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const appendN) A) xs) ys

/-- The type of `List`: a set gives a set. -/
abbrev listType : CTm (Head L) n := .pi allSets allSets

/-- The type of `nil`. -/
abbrev nilType : CTm (Head L) n := .pi allSets (cList (.var 0))

/-- The type of `cons`. -/
abbrev consType : CTm (Head L) n :=
  .pi allSets (.pi (.var 0) (.pi (cList (.var 1)) (cList (.var 2))))

/-- The type of `append`. -/
abbrev appendType : CTm (Head L) n :=
  .pi allSets (.pi (cList (.var 0)) (.pi (cList (.var 1)) (cList (.var 2))))

/-- The type that sends every set into the least universe. -/
abbrev intoU0 : CTm (Head L) n := .pi allSets U0

end Terms

variable [LevelOrder L]

variable (L) in
/-- The table of the family: each constant with its type. -/
def listTable : List (DeclName × CTm (Head L) 0) :=
  [(listN, listType), (nilN, nilType), (consN, consType), (appendN, appendType)]

variable (L) in
/-- The declarations of the family. -/
def listDecls : DeclName → Option (CTm (Head L) 0) := tableLookup (listTable L)

variable (L) in
/-- `append A (nil A) ys ⟶ ys`. -/
def appendNil : DefiningEquation (Head L) where
  arity := 2
  telescope := .snoc (.snoc .nil allSets) (cList (.var 0))
  left := cAppend (.var 1) (cNil (.var 1)) (.var 0)
  right := .var 0

variable (L) in
/-- `append A (cons A x xs) ys ⟶ cons A x (append A xs ys)`. -/
def appendCons : DefiningEquation (Head L) where
  arity := 4
  telescope := .snoc (.snoc (.snoc (.snoc .nil allSets) (.var 0))
    (cList (.var 1))) (cList (.var 2))
  left := cAppend (.var 3) (cCons (.var 3) (.var 2) (.var 1)) (.var 0)
  right := cCons (.var 3) (.var 2) (cAppend (.var 3) (.var 1) (.var 0))

variable (L) in
/-- The equations of the family. -/
def listEquations : List (DefiningEquation (Head L)) := [appendNil L, appendCons L]

variable (L) in
/-- The tower inside the sets with the list family. -/
abbrev listFamily := withFamily (bare L) (listDecls L) (listEquations L)

section Declared

omit [LevelOrder L]

/-- `List` is declared at `set → set`. -/
theorem listDecls_list : listDecls L listN = some listType := rfl

/-- `nil` is declared at its type. -/
theorem listDecls_nil : listDecls L nilN = some nilType := rfl

/-- `cons` is declared at its type. -/
theorem listDecls_cons : listDecls L consN = some consType := rfl

/-- `append` is declared at its type. -/
theorem listDecls_append : listDecls L appendN = some appendType := rfl

/-- The first equation is one of the family's equations. -/
theorem appendNil_member : appendNil L ∈ listEquations L :=
  List.mem_cons_self

/-- The second equation is one of the family's equations. -/
theorem appendCons_member : appendCons L ∈ listEquations L :=
  List.mem_cons_of_mem _ List.mem_cons_self

end Declared

variable (L) in
/-- The same table with `List` declared at `set → U₀`. -/
def smallListTable : List (DeclName × CTm (Head L) 0) :=
  [(listN, intoU0), (nilN, nilType), (consN, consType), (appendN, appendType)]

variable (L) in
/-- The declarations of the family whose `List` lands in the least universe. -/
def smallListDecls : DeclName → Option (CTm (Head L) 0) := tableLookup (smallListTable L)

variable (L) in
/-- The list family with `List : set → U₀`. -/
abbrev smallListFamily := withFamily (bare L) (smallListDecls L) (listEquations L)

/-- In the small family, `List` is declared at `set → U₀`. -/
theorem smallListDecls_list : smallListDecls L listN = some intoU0 := rfl

/-! ## The values -/

/-- The tag of the empty list: the code of its name. -/
def nilTag : ZFSet.{u} := ZFSetInductive.nameCode nilN

/-- The tag of an element before a list: the code of its name. -/
def consTag : ZFSet.{u} := ZFSetInductive.nameCode consN

/-- The two constructors have different names, so their tags differ. -/
theorem nilTag_ne_consTag : nilTag.{u} ≠ consTag :=
  ZFSetInductive.nameCode_injective.ne (by decide)

/-- The tag of the empty list is a member of every closed universe that has `ω`. -/
theorem nilTag_mem {U : ZFSet.{u}} (closed : Closed U) (omegaMem : ZFSet.omega ∈ U) :
    nilTag ∈ U :=
  ZFSetInductive.nameCode_mem closed omegaMem nilN

/-- The tag of an element before a list is a member of every closed universe that has `ω`. -/
theorem consTag_mem {U : ZFSet.{u}} (closed : Closed U) (omegaMem : ZFSet.omega ∈ U) :
    consTag ∈ U :=
  ZFSetInductive.nameCode_mem closed omegaMem consN

section Values

variable (all : ZFSet.{u})

/-- `List` as a set: the trace function sending a set to its lists. -/
noncomputable def listValue : ZFSet.{u} := traceLam (graph all (listSet nilTag consTag))

/-- `nil` as a set: at every set, the empty list. -/
noncomputable def nilValue : ZFSet.{u} := traceLam (graph all fun _ => nilSet nilTag)

/-- `cons` as a set. -/
noncomputable def consValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph A fun a =>
    traceLam (graph (listSet nilTag consTag A) fun l => consSet consTag a l)))

/-- `append` as a set. -/
noncomputable def appendValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph (listSet nilTag consTag A) fun xs =>
    traceLam (graph (listSet nilTag consTag A) fun ys => setAppend nilTag consTag A xs ys)))

/-- The table of the values. -/
noncomputable def listValueTable : List (DeclName × ZFSet.{u}) :=
  [(listN, listValue all), (nilN, nilValue all), (consN, consValue all),
    (appendN, appendValue all)]

/-- The values of the constants. -/
noncomputable def listValues : DeclName → ZFSet.{u} := fun c =>
  (tableLookup (listValueTable all) c).getD ∅

/-- The value of `List`. -/
theorem listValues_list : listValues all listN = listValue all := rfl

/-- The value of `nil`. -/
theorem listValues_nil : listValues all nilN = nilValue all := rfl

/-- The value of `cons`. -/
theorem listValues_cons : listValues all consN = consValue all := rfl

/-- The value of `append`. -/
theorem listValues_append : listValues all appendN = appendValue all := rfl

end Values

/-! ## The set model -/

section Model

variable {V : Above L → ZFSet.{u}} {ground : ZFSet.{u}} {ν : Nat → Above L}
  {consts : DeclName → ZFSet.{u}}

/-- An assignment that gives the constants of the family their values on a universe of sets. -/
abbrev Reads (all : ZFSet.{u}) (consts : DeclName → ZFSet.{u}) : Prop :=
  ∀ c, listDecls L c ≠ none → consts c = listValues all c

omit [LevelOrder L] in
/-- The value an assignment gives a constant of the family. -/
theorem Reads.at {all : ZFSet.{u}} (reads : Reads (L := L) all consts) {c : DeclName}
    {T : CTm (Head L) 0} {value : ZFSet.{u}} (declared : listDecls L c = some T)
    (known : listValues all c = value) : consts c = value :=
  (reads c (by rw [declared]; exact Option.some_ne_none T)).trans known

section Readings

variable {all : ZFSet.{u}} (reads : Reads (L := L) all consts)

include reads

omit [LevelOrder L] in
/-- The assignment reads `List` as the trace function of the sets of lists. -/
theorem Reads.list : consts listN = listValue all := Reads.at reads listDecls_list rfl

omit [LevelOrder L] in
/-- The assignment reads `nil` as the empty list. -/
theorem Reads.nil : consts nilN = nilValue all := Reads.at reads listDecls_nil rfl

omit [LevelOrder L] in
/-- The assignment reads `cons` as cons. -/
theorem Reads.cons : consts consN = consValue all := Reads.at reads listDecls_cons rfl

omit [LevelOrder L] in
/-- The assignment reads `append` as append. -/
theorem Reads.append : consts appendN = appendValue all := Reads.at reads listDecls_append rfl

include reads in
omit [LevelOrder L] in
/-- `List` applied to a set is the set of lists over it. -/
theorem Reads.listBeta {x : ZFSet.{u}} (hx : x ∈ all) :
    traceApp (consts listN) x = listSet nilTag consTag x := by
  rw [reads.list]
  unfold listValue
  rw [traceApp_graph_beta _ hx]

include reads in
omit [LevelOrder L] in
/-- `nil` applied to a set is the empty list. -/
theorem Reads.nilBeta {x : ZFSet.{u}} (hx : x ∈ all) :
    traceApp (consts nilN) x = nilSet nilTag := by
  rw [reads.nil]
  unfold nilValue
  rw [traceApp_graph_beta _ hx]

end Readings

variable (reads : Reads (L := L) (V (.above 0)) consts) (chain : ClosedChain V)
  (omegaMem : ZFSet.omega ∈ V (.above 0))

include reads chain omegaMem in
/-- Every value lies in the set of its constant's type. -/
theorem listValues_typed {c : DeclName} {T : CTm (Head L) 0}
    (declared : listDecls L c = some T) :
    listValues (V (.above 0)) c ∈ ev (chainHead V ground ν) consts T Fin.elim0 := by
  have row := tableLookup_mem declared
  simp only [listTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | row
  · exact traceLam_graph_mem fun A hA =>
      listSet_mem_of_closed (chain.closed (.above 0)) omegaMem
        (nilTag_mem (chain.closed (.above 0)) omegaMem)
        (consTag_mem (chain.closed (.above 0)) omegaMem) hA
  rcases row with ⟨rfl, rfl⟩ | row
  · show nilValue (V (.above 0)) ∈
      tracePiSet (V (.above 0)) (fun A => traceApp (consts listN) A)
    rw [reads.list]
    unfold nilValue listValue
    exact traceLam_graph_mem fun A hA => by
      rw [traceApp_graph_beta _ hA]
      exact nilSet_mem
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · change consValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun A =>
      tracePiSet A (fun _ => tracePiSet (traceApp (consts listN) A)
        (fun _ => traceApp (consts listN) A)))
    rw [reads.list]
    exact traceLam_graph_mem fun A hA => by
      have beta : traceApp (listValue (V (.above 0))) A = listSet nilTag consTag A :=
        traceApp_graph_beta _ hA
      have fibres : tracePiSet (traceApp (listValue (V (.above 0))) A)
          (fun _ => traceApp (listValue (V (.above 0))) A) =
          tracePiSet (listSet nilTag consTag A) (fun _ => listSet nilTag consTag A) := by
        rw [beta]
      refine traceLam_graph_mem fun a ha => ?_
      rw [fibres]
      exact traceLam_graph_mem fun l hl => consSet_mem ha hl
  · change appendValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun A =>
      tracePiSet (traceApp (consts listN) A) (fun _ =>
        tracePiSet (traceApp (consts listN) A) (fun _ => traceApp (consts listN) A)))
    rw [reads.list]
    exact traceLam_graph_mem fun A hA => by
      have beta : traceApp (listValue (V (.above 0))) A = listSet nilTag consTag A :=
        traceApp_graph_beta _ hA
      have outer : tracePiSet (traceApp (listValue (V (.above 0))) A) (fun xs =>
          tracePiSet (traceApp (listValue (V (.above 0))) A)
            (fun _ => traceApp (listValue (V (.above 0))) A)) =
          tracePiSet (listSet nilTag consTag A) (fun xs =>
            tracePiSet (listSet nilTag consTag A) (fun _ => listSet nilTag consTag A)) := by
        rw [beta]
      rw [outer]
      exact traceLam_graph_mem fun xs hxs =>
        traceLam_graph_mem fun ys hys => setAppend_mem nilTag_ne_consTag xs hxs ys hys

include reads in
/-- Append of the empty list is the list, as values. -/
theorem appendNil_valid (η : Env.{u} 2)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc .nil allSets) (cList (.var 0)) : CCtx (Head L) 2) η) :
    ev (chainHead V ground ν) consts
        (cAppend (.var 1) (cNil (.var 1)) (.var 0) : CTm (Head L) 2) η =
      ev (chainHead V ground ν) consts (.var (0 : Fin 2)) η := by
  have hA : η 1 ∈ V (.above 0) := sat 1
  have hys : η 0 ∈ listSet nilTag consTag (η 1) := by
    have member := sat 0
    change η 0 ∈ traceApp (consts listN) (η 1) at member
    rw [reads.listBeta hA] at member
    exact member
  show traceApp (traceApp (traceApp (consts appendN) (η 1))
      (traceApp (consts nilN) (η 1))) (η 0) = η 0
  rw [reads.append, reads.nilBeta hA]
  unfold appendValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ nilSet_mem, traceApp_graph_beta _ hys]
  exact setAppend_nil nilTag_ne_consTag hys

include reads in
/-- Append of cons is cons of append, as values. -/
theorem appendCons_valid (η : Env.{u} 4)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc (.snoc (.snoc .nil allSets) (.var 0)) (cList (.var 1))) (cList (.var 2)) :
        CCtx (Head L) 4) η) :
    ev (chainHead V ground ν) consts
        (cAppend (.var 3) (cCons (.var 3) (.var 2) (.var 1)) (.var 0) : CTm (Head L) 4) η =
      ev (chainHead V ground ν) consts
        (cCons (.var 3) (.var 2) (cAppend (.var 3) (.var 1) (.var 0)) : CTm (Head L) 4) η := by
  have hA : η 3 ∈ V (.above 0) := sat 3
  have hx : η 2 ∈ η 3 := sat 2
  have hxs : η 1 ∈ listSet nilTag consTag (η 3) := by
    have member := sat 1
    change η 1 ∈ traceApp (consts listN) (η 3) at member
    rw [reads.listBeta hA] at member
    exact member
  have hys : η 0 ∈ listSet nilTag consTag (η 3) := by
    have member := sat 0
    change η 0 ∈ traceApp (consts listN) (η 3) at member
    rw [reads.listBeta hA] at member
    exact member
  have joined : setAppend nilTag consTag (η 3) (η 1) (η 0) ∈ listSet nilTag consTag (η 3) :=
    setAppend_mem nilTag_ne_consTag (η 1) hxs (η 0) hys
  have consed : consSet consTag (η 2) (η 1) ∈ listSet nilTag consTag (η 3) :=
    consSet_mem hx hxs
  show traceApp (traceApp (traceApp (consts appendN) (η 3))
        (traceApp (traceApp (traceApp (consts consN) (η 3)) (η 2)) (η 1))) (η 0) =
      traceApp (traceApp (traceApp (consts consN) (η 3)) (η 2))
        (traceApp (traceApp (traceApp (consts appendN) (η 3)) (η 1)) (η 0))
  rw [reads.append, reads.cons]
  unfold appendValue consValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hA]
  rw [traceApp_graph_beta _ hx, traceApp_graph_beta _ hxs]
  rw [traceApp_graph_beta _ hxs, traceApp_graph_beta _ hys, traceApp_graph_beta _ consed,
    traceApp_graph_beta _ joined]
  rw [traceApp_graph_beta _ hys, setAppend_cons nilTag_ne_consTag hx hxs hys]

include reads in
/-- Both equations hold between sets, at every environment of their telescope. -/
theorem listEquations_valid :
    ∀ e ∈ listEquations L, ∀ η : Env.{u} e.arity,
      Sat (chainHead V ground ν) consts e.telescope η →
        ev (chainHead V ground ν) consts e.left η =
          ev (chainHead V ground ν) consts e.right η := by
  intro e member η sat
  have cases : e = appendNil L ∨ e = appendCons L := by
    simpa [listEquations] using member
  rcases cases with rfl | rfl
  · exact appendNil_valid reads η sat
  · exact appendCons_valid reads η sat

include chain omegaMem in
/-- The list family has a set model over every chain of closed universes that has `ω` in the
universe of the sets. -/
theorem listFamily_setModel (groundTyped : ground ∈ V LevelOrder.bot) (base : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν)
      (familyConsts base (listDecls L) (listValues (V (.above 0)))) (listFamily L) :=
  family_setModel_read (bare L)
    (fun consts _ => chain_setModel chain groundTyped ν consts) (fun _ _ => rfl)
    (listValues (V (.above 0)))
    (fun _ _ reads {_ _} declared => listValues_typed reads chain omegaMem declared)
    (fun _ _ reads => listEquations_valid reads)

include chain omegaMem in
/-- `nil A` is not convertible with `cons A x l` at `List A`. `A`, `x` and `l`
are closed, and their values lie in the universe of sets, in the value of `A`,
and in the lists over that value. -/
theorem nil_not_convertible_with_cons
    (groundTyped : ground ∈ V LevelOrder.bot) (base : DeclName → ZFSet.{u})
    {A x l : CTm (Head L) 0}
    (hA : ev (chainHead V ground ν)
        (familyConsts base (listDecls L) (listValues (V (.above 0)))) A Fin.elim0 ∈
        V (.above 0))
    (hx : ev (chainHead V ground ν)
        (familyConsts base (listDecls L) (listValues (V (.above 0)))) x Fin.elim0 ∈
        ev (chainHead V ground ν)
          (familyConsts base (listDecls L) (listValues (V (.above 0)))) A Fin.elim0)
    (hl : ev (chainHead V ground ν)
        (familyConsts base (listDecls L) (listValues (V (.above 0)))) l Fin.elim0 ∈
        listSet nilTag consTag
          (ev (chainHead V ground ν)
            (familyConsts base (listDecls L) (listValues (V (.above 0)))) A Fin.elim0)) :
    ¬ CEqual (listFamily L) .nil (cNil A) (cCons A x l) (cList A) := by
  intro eq
  let heads := chainHead V ground ν
  let consts := familyConsts base (listDecls L) (listValues (V (.above 0)))
  have model : SetModel heads consts (listFamily L) :=
    listFamily_setModel chain omegaMem groundTyped base
  have reads : Reads (L := L) (V (.above 0)) consts :=
    fun _ declared => familyConsts_declared declared
  have same := CDerivable.sound_equality model eq Fin.elim0 (sat_nil heads consts Fin.elim0)
  have nilEv : ev heads consts (cNil A) Fin.elim0 = nilSet nilTag := by
    show traceApp (consts nilN) (ev heads consts A Fin.elim0) = nilSet nilTag
    exact reads.nilBeta hA
  have consEv : ev heads consts (cCons A x l) Fin.elim0 =
      consSet consTag (ev heads consts x Fin.elim0) (ev heads consts l Fin.elim0) := by
    show traceApp (traceApp (traceApp (consts consN) (ev heads consts A Fin.elim0))
        (ev heads consts x Fin.elim0)) (ev heads consts l Fin.elim0) = _
    rw [reads.cons]
    unfold consValue
    rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hx, traceApp_graph_beta _ hl]
  have tags : nilSet nilTag =
      consSet consTag (ev heads consts x Fin.elim0) (ev heads consts l Fin.elim0) := by
    rw [← nilEv, ← consEv]
    exact same
  unfold nilSet consSet at tags
  exact ZFSetInductive.constructorValue_ne_of_tag_ne nilTag_ne_consTag []
    [ev heads consts x Fin.elim0, ev heads consts l Fin.elim0] tags

include chain omegaMem ν in
/-- No closed term has type `Π (A : set). A`: the empty set is a set, so no trace function
picks an element of every set. -/
theorem no_closed_element_of_every_set (groundTyped : ground ∈ V LevelOrder.bot)
    (base : DeclName → ZFSet.{u}) (t : CTm (Head L) 0) :
    ¬ CTyped (listFamily L) .nil t (.pi allSets (.var 0)) := by
  refine family_no_closed_inhabitant (base := base) (bare L)
    (fun consts _ => chain_setModel chain groundTyped ν consts) (fun _ _ => rfl)
    (listValues (V (.above 0)))
    (fun _ _ reads {_ _} declared => listValues_typed reads chain omegaMem declared)
    (fun _ _ reads => listEquations_valid reads) (fun z hz => ?_) t
  change z ∈ tracePiSet (V (.above 0)) (fun A => A) at hz
  exact ZFSet.notMem_empty _
    (traceApp_mem_fibre hz (chain.empty_mem groundTyped (.above 0)))

end Model

/-! ## The stages -/

section LowerSets

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} (ν : Nat → Above L)

include small in
/-- The list family has a set model on the stages that read the type of all sets as every set
of the lower universe. -/
theorem lowerSets_listFamily_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts base (listDecls L) (listValues carrierCode.{u})) (listFamily L) :=
  listFamily_setModel (stages_closedChain small large) omega_mem_carrierCode groundTyped base

include large in
/-- A set in the universe at a level of the tower has its lists in that same universe. -/
theorem lowerSets_listSet_mem (d : L) {A : ZFSet.{u + 1}}
    (hA : A ∈ lowerSetsHeads (L := L) large ground ν (.sort (.const (.below d)))) :
    listSet nilTag consTag A ∈
      lowerSetsHeads (L := L) large ground ν (.sort (.const (.below d))) :=
  listSet_mem_of_closed (universeSet_closed large ZFSet.omega d)
    (seed_mem_universeSet large ZFSet.omega d)
    (nilTag_mem (universeSet_closed large ZFSet.omega d)
      (seed_mem_universeSet large ZFSet.omega d))
    (consTag_mem (universeSet_closed large ZFSet.omega d)
      (seed_mem_universeSet large ZFSet.omega d)) hA

include small in
/-- The family with `List : set → U₀` has no set model on the stages when `List` is read as
the set of lists: the lists over the singleton of the least universe are not in that
universe. -/
theorem smallList_no_setModel (consts : DeclName → ZFSet.{u + 1})
    (reads : consts listN = listValue carrierCode.{u}) :
    ¬ SetModel (lowerSetsHeads (L := L) large ground ν) consts (smallListFamily L) := by
  intro model
  have declared : (smallListFamily L).constantType listN = some intoU0 :=
    (withFamily_declared (bare L) rfl).trans smallListDecls_list
  have mem := model.constants declared
  rw [reads] at mem
  let U : ZFSet.{u + 1} := universeSet large ZFSet.omega (LevelOrder.bot : L)
  have hU : U ∈ carrierCode.{u} := universeSet_mem_carrierCode small large LevelOrder.bot
  have hSing : ({U} : ZFSet.{u + 1}) ∈ carrierCode.{u} := carrierCode_closed.singleton_mem hU
  have setsEval : ev (lowerSetsHeads (L := L) large ground ν) consts allSets Fin.elim0 =
      carrierCode.{u} := by
    unfold allSets ev lowerSetsHeads chainHead LevelExpr.eval stages
    rfl
  have leastEval (x : ZFSet.{u + 1}) :
      ev (lowerSetsHeads (L := L) large ground ν) consts U0 (extend Fin.elim0 x) = U := by
    unfold U0 universeAt ev lowerSetsHeads chainHead LevelExpr.eval stages
    rfl
  have inside : listValue carrierCode.{u} ∈ tracePiSet carrierCode.{u} (fun _ => U) := by
    have raw : listValue carrierCode.{u} ∈
        tracePiSet (ev (lowerSetsHeads (L := L) large ground ν) consts allSets Fin.elim0)
          (fun x => ev (lowerSetsHeads (L := L) large ground ν) consts U0
            (extend Fin.elim0 x)) := by
      change _ at mem
      exact mem
    rw [setsEval] at raw
    rwa [tracePiSet_congr fun _ _ => leastEval _] at raw
  have landed : listSet nilTag consTag ({U} : ZFSet.{u + 1}) ∈ U := by
    unfold listValue at inside
    have app := traceApp_mem_fibre inside hSing
    rwa [traceApp_graph_beta _ hSing] at app
  exact listSet_singleton_not_mem (universeSet_closed large ZFSet.omega (LevelOrder.bot : L))
    landed

end LowerSets

/-! ## In the judgment -/

section Judgment

/-- A constant of the family is declared in the package as the family declares it. -/
theorem listFamily_declared {c : DeclName} {T : CTm (Head L) 0}
    (declared : listDecls L c = some T) : (listFamily L).constantType c = some T :=
  (withFamily_declared (bare L) rfl).trans declared

/-- **A package over the list family**: it contains the rules of the tower and declares the
four constants at their types. The typings of this section hold in every such package, so they
hold where further constants, datatypes and definitions are declared. -/
structure OverLists {R' : Rules (Head L)} (Q : ChurchRules R') : Prop where
  contains : Contains R'
  declared : ∀ {c : DeclName} {T : CTm (Head L) 0}, listDecls L c = some T →
    Q.constantType c = some T

/-- The package of the family is over the list family. -/
theorem listFamily_over : OverLists (listFamily L) :=
  ⟨package_contains, listFamily_declared⟩

/-- A package that contains the package of the family is over the list family. -/
theorem OverLists.of_sub {R' : Rules (Head L)} {Q : ChurchRules R'}
    (sub : ChurchRulesSub (listFamily L) Q) : OverLists Q :=
  ⟨⟨sub.headTyping, sub.isUniverse, sub.join, sub.cumulative⟩,
    fun declared => sub.constantType (listFamily_declared declared)⟩

/-- **A package computes as the list family** when it contains the steps of the two equations
of append, with their premises. -/
abbrev ComputesAsLists {R' : Rules (Head L)} (Q : ChurchRules R') : Prop :=
  StepsWithin (familyChurch (rules L) (listDecls L) (listEquations L)) Q

/-- The package of the family computes as the list family. -/
theorem listFamily_computes : ComputesAsLists (listFamily L) :=
  StepsWithin.sum_right (bare L) (familyChurch (rules L) (listDecls L) (listEquations L))

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}
  (covers : OverLists Q)

include covers in
/-- The type of `List` is a type of `allClasses`. -/
theorem listType_formed : CTyped Q Γ listType allClasses :=
  setFunctions_typed covers.contains

include covers in
/-- `List` has its type. -/
theorem listConst_typed : CTyped Q Γ (.const listN) listType :=
  definition_typed (covers.declared listDecls_list) (listType_formed covers)
    (covers.contains.isUniverse (.sort _))

include covers in
/-- For `A : set`, `List A : set`. -/
theorem cList_typed {A : CTm (Head L) n} (hA : CTyped Q Γ A allSets) :
    CTyped Q Γ (cList A) allSets :=
  .appElim (listConst_typed covers) hA

include covers in
/-- The type of `nil` is a type of `allClasses`. -/
theorem nilType_formed : CTyped Q Γ nilType allClasses :=
  classToSet_typed covers.contains (sets_typed covers.contains)
    (cList_typed covers (n := n + 1) (Γ := .snoc Γ allSets)
      (CDerivable.var (P := Q) 0))

include covers in
/-- `nil` has its type. -/
theorem nilConst_typed : CTyped Q Γ (.const nilN) nilType :=
  definition_typed (covers.declared listDecls_nil) (nilType_formed covers)
    (covers.contains.isUniverse (.sort _))

include covers in
/-- `nil A` is a list over `A`. -/
theorem cNil_typed {A : CTm (Head L) n} (hA : CTyped Q Γ A allSets) :
    CTyped Q Γ (cNil A) (cList A) :=
  .appElim (nilConst_typed covers) hA

include covers in
/-- The type of `cons` is a type of `allClasses`. -/
theorem consType_formed : CTyped Q Γ consType allClasses :=
  classToSet_typed covers.contains (sets_typed covers.contains)
    (family_isSet (n := n + 1) (Γ := .snoc Γ allSets) covers.contains
      (CDerivable.var (P := Q) 0)
      (family_isSet (n := n + 2) (Γ := .snoc (.snoc Γ allSets) (.var 0))
        covers.contains
        (cList_typed covers (n := n + 2) (Γ := .snoc (.snoc Γ allSets) (.var 0))
          (CDerivable.var (P := Q) 1))
        (cList_typed covers (n := n + 3)
          (Γ := .snoc (.snoc (.snoc Γ allSets) (.var 0)) (cList (.var 1)))
          (CDerivable.var (P := Q) 2))))

include covers in
/-- `cons` has its type. -/
theorem consConst_typed : CTyped Q Γ (.const consN) consType :=
  definition_typed (covers.declared listDecls_cons) (consType_formed covers)
    (covers.contains.isUniverse (.sort _))

include covers in
/-- `cons A x xs` is a list over `A`. -/
theorem cCons_typed {A x xs : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hx : CTyped Q Γ x A) (hxs : CTyped Q Γ xs (cList A)) :
    CTyped Q Γ (cCons A x xs) (cList A) := by
  have first : CTyped Q Γ (.app (.const consN) A)
      (.pi A (.pi (cList (A.rename wk))
        (cList ((A.rename wk).rename wk)))) :=
    .appElim (B := .pi (.var 0) (.pi (cList (.var 1)) (cList (.var 2))))
      (consConst_typed covers) hA
  have second := CDerivable.appElim first hx
  have same : CTm.inst0 x (.pi (cList (A.rename wk))
        (cList ((A.rename wk).rename wk))) =
      .pi (cList A) (cList (A.rename wk)) := by
    show CTm.pi (cList (CTm.inst0 x (CTm.rename wk A)))
        (cList (CTm.subst (CTm.liftSub (CTm.subst0 x))
          (CTm.rename wk (CTm.rename wk A)))) = _
    rw [CTm.inst0_rename_wk x A, CTm.subst_liftSub_wk (CTm.subst0 x) (A.rename wk)]
    change (cList A).pi (cList (CTm.rename wk (CTm.inst0 x (CTm.rename wk A)))) = _
    rw [CTm.inst0_rename_wk x A]
  rw [same] at second
  have third := CDerivable.appElim (B := cList (A.rename wk)) second hxs
  have last : CTm.inst0 xs (cList (A.rename wk)) = cList A := by
    show cList (CTm.inst0 xs (CTm.rename wk A)) = _
    rw [CTm.inst0_rename_wk xs A]
  rw [last] at third
  exact third

include covers in
/-- The type of `append` is a type of `allClasses`. -/
theorem appendType_formed : CTyped Q Γ appendType allClasses :=
  classToSet_typed covers.contains (sets_typed covers.contains)
    (family_isSet (n := n + 1) (Γ := .snoc Γ allSets) covers.contains
      (cList_typed covers (n := n + 1) (Γ := .snoc Γ allSets)
        (CDerivable.var (P := Q) 0))
      (family_isSet (n := n + 2) (Γ := .snoc (.snoc Γ allSets) (cList (.var 0)))
        covers.contains
        (cList_typed covers (n := n + 2) (Γ := .snoc (.snoc Γ allSets) (cList (.var 0)))
          (CDerivable.var (P := Q) 1))
        (cList_typed covers (n := n + 3)
          (Γ := .snoc (.snoc (.snoc Γ allSets) (cList (.var 0))) (cList (.var 1)))
          (CDerivable.var (P := Q) 2))))

include covers in
/-- `append` has its type. -/
theorem appendConst_typed : CTyped Q Γ (.const appendN) appendType :=
  definition_typed (covers.declared listDecls_append) (appendType_formed covers)
    (covers.contains.isUniverse (.sort _))

include covers in
/-- `append A xs ys` is a list over `A`. -/
theorem cAppend_typed {A xs ys : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hxs : CTyped Q Γ xs (cList A)) (hys : CTyped Q Γ ys (cList A)) :
    CTyped Q Γ (cAppend A xs ys) (cList A) := by
  have first : CTyped Q Γ (.app (.const appendN) A)
      (.pi (cList A) (.pi (cList (A.rename wk))
        (cList ((A.rename wk).rename wk)))) :=
    .appElim (B := .pi (cList (.var 0)) (.pi (cList (.var 1)) (cList (.var 2))))
      (appendConst_typed covers) hA
  have second := CDerivable.appElim first hxs
  have same : CTm.inst0 xs (.pi (cList (A.rename wk))
        (cList ((A.rename wk).rename wk))) =
      .pi (cList A) (cList (A.rename wk)) := by
    show CTm.pi (cList (CTm.inst0 xs (CTm.rename wk A)))
        (cList (CTm.subst (CTm.liftSub (CTm.subst0 xs))
          (CTm.rename wk (CTm.rename wk A)))) = _
    rw [CTm.inst0_rename_wk xs A, CTm.subst_liftSub_wk (CTm.subst0 xs) (A.rename wk)]
    change (cList A).pi (cList (CTm.rename wk (CTm.inst0 xs (CTm.rename wk A)))) = _
    rw [CTm.inst0_rename_wk xs A]
  rw [same] at second
  have third := CDerivable.appElim (B := cList (A.rename wk)) second hys
  have last : CTm.inst0 ys (cList (A.rename wk)) = cList A := by
    show cList (CTm.inst0 ys (CTm.rename wk A)) = _
    rw [CTm.inst0_rename_wk ys A]
  rw [last] at third
  exact third

variable (computes : ComputesAsLists Q)

include covers computes in
/-- **Append of the empty list is the list**, at every typed instance. -/
theorem append_nil_rule {A ys : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hys : CTyped Q Γ ys (cList A)) :
    CEqual Q Γ (cAppend A (cNil A) ys) ys (cList A) :=
  have typed : CSubstMor Q (appendNil L).telescope Γ
      (fun j : Fin 2 => match j with
        | ⟨0, _⟩ => ys
        | ⟨1, _⟩ => A) :=
    fun j => match j with
      | ⟨0, _⟩ => hys
      | ⟨1, _⟩ => hA
  family_equation_holds (rules L) computes appendNil_member _ typed
    (cAppend_typed covers hA (cNil_typed covers hA) hys) hys

include covers computes in
/-- **Append of an element before a list is the element before the append**, at every typed
instance. -/
theorem append_cons_rule {A x xs ys : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hx : CTyped Q Γ x A) (hxs : CTyped Q Γ xs (cList A)) (hys : CTyped Q Γ ys (cList A)) :
    CEqual Q Γ (cAppend A (cCons A x xs) ys) (cCons A x (cAppend A xs ys)) (cList A) :=
  have typed : CSubstMor Q (appendCons L).telescope Γ
      (fun j : Fin 4 => match j with
        | ⟨0, _⟩ => ys
        | ⟨1, _⟩ => xs
        | ⟨2, _⟩ => x
        | ⟨3, _⟩ => A) :=
    fun j => match j with
      | ⟨0, _⟩ => hys
      | ⟨1, _⟩ => hxs
      | ⟨2, _⟩ => hx
      | ⟨3, _⟩ => hA
  family_equation_holds (rules L) computes appendCons_member _ typed
    (cAppend_typed covers hA (cCons_typed covers hA hx hxs) hys)
    (cCons_typed covers hA hx (cAppend_typed covers hA hxs hys))

/-- The telescope of the first equation. -/
abbrev appendNilTelescope : CCtx (Head L) 2 :=
  .snoc (.snoc .nil allSets) (cList (.var 0))

include covers computes in
/-- Positive example: the first equation at its own telescope, `(A : set) (ys : List A)`. -/
theorem appendNil_equation :
    CEqual Q appendNilTelescope
      (cAppend (.var 1) (cNil (.var 1)) (.var 0)) (.var 0) (cList (.var 1)) :=
  append_nil_rule covers computes (CDerivable.var (P := Q) 1) (CDerivable.var (P := Q) 0)

end Judgment

end Lists
end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
