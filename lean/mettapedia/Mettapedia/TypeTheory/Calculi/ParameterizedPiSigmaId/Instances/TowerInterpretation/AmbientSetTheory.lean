import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.AmbientSetsModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Square
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetConstantFamilies

/-!
# The constants of set theory over the tower inside the sets

Over the tower inside the sets (`AmbientSets`), where every type is a set, this file declares
as one family (`setTheory`) the constants that make the sets a language of their own.

* **The logic.** `prop : U₀`, the type of propositions; `holds : prop → U₀`, the type of the
  proofs of a proposition; `imp : prop → prop → prop`; `all : Π (A : set). (A → prop) → prop`,
  quantification over a set; `allSets : (set → prop) → prop`, quantification over all sets.
* **The sets.** `In : set → set → prop`; `Empty : set`; `Union`, `Power`, `UnivOf : set → set`.
* **Types are sets.** `elem : Π (A : set). A → set`: a term of a type is a set.
  `member : Π (A : set). Π (a : A). holds (In (elem A a) A)`: typing gives membership.
  `the : Π (A : set). Π (x : set). holds (In x A) → A`: membership gives typing. A set proved to
  be a member of a type is a term of the type.

The equations (`setEquations`): the proofs of an implication are the functions between the
proofs, and the proofs of a quantification are the dependent functions into the proofs, also
over all sets; `elem` and `the` undo each other.

**The set model** (`setTheory_setModel`), over every stage with a universe operation
(`UniverseStage`): the propositions are the truth values, `holds` is the identity on them,
membership is membership, the operations are those of the sets, `UnivOf` is the stage's
universe operation, and `elem` and `the` are the identity on the underlying sets. Every
equation holds. The equation for quantification over all sets holds although its right side
is a function type over all sets: a trace function into truth values is a truth value, over
a domain of any size.

The sets of one universe of Lean, as one set of the next, are such a stage
(`lowerSets_universeStage`), relative to cofinally many inaccessible cardinals in both
universes; so the package has a set model (`lowerSets_setTheory_setModel`) and is consistent
(`setTheory_consistent`).

In the judgment (section `Judgment`): the declared types are formed and the constants have
them; a term of a type that is a set gives a set (`elem_typed`) and a proof that the set is a
member of the type (`member_typed`).

Positive examples: the universe at a level, as a set, is a member of the universe at the next
level, with a proof term (`universe_member`); `Power Empty` is a set (`powerEmpty_typed`).
Negative examples: in the model nothing is a member of the empty set (`in_empty_false`), and
the type of the proofs that the empty set is a member of itself has no closed term
(`no_proof_empty_in_empty`, `setTheory_consistent`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace AmbientSets

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (Closed)
open ZFSetReplayInterpretation (UniverseModel)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta traceLam_graph_empty
  tracePiSet_subterminal tracePiSet_congr)
open ZFSetTraceProofDecoding (truthCode mem_truthCode truthCode_subset)

universe u

variable {L : Type}

/-! ## The constants and their types -/

/-- The type of propositions. -/
def propN : DeclName := .str .anonymous "prop"
/-- The proofs of a proposition. -/
def holdsN : DeclName := .str .anonymous "holds"
/-- Implication. -/
def impN : DeclName := .str .anonymous "imp"
/-- Quantification over a set. -/
def allN : DeclName := .str .anonymous "all"
/-- Quantification over all sets. -/
def allSetsN : DeclName := .str .anonymous "allSets"
/-- Membership. -/
def inN : DeclName := .str .anonymous "In"
/-- The empty set. -/
def emptyN : DeclName := .str .anonymous "Empty"
/-- The union of a set. -/
def unionN : DeclName := .str .anonymous "Union"
/-- The power set. -/
def powerN : DeclName := .str .anonymous "Power"
/-- The universe around a set. -/
def univOfN : DeclName := .str .anonymous "UnivOf"
/-- A term of a type, as a set. -/
def elemN : DeclName := .str .anonymous "elem"
/-- The membership of a term in its type. -/
def memberN : DeclName := .str .anonymous "member"
/-- A set with a proof of membership, as a term of the type. -/
def theN : DeclName := .str .anonymous "the"

section Terms

variable [LevelOrder L] {n : Nat}

/-- The least universe, where the propositions and their proofs live. -/
abbrev U0 : CTm (Head L) n := universeAt LevelTower.zero

/-- The type of propositions. -/
abbrev cProp : CTm (Head L) n := .const propN

/-- `holds p`. -/
abbrev cHolds (p : CTm (Head L) n) : CTm (Head L) n := .app (.const holdsN) p

/-- `imp p q`. -/
abbrev cImp (p q : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const impN) p) q

/-- `all A P`. -/
abbrev cAll (A P : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const allN) A) P

/-- `allSets P`. -/
abbrev cAllSets (P : CTm (Head L) n) : CTm (Head L) n := .app (.const allSetsN) P

/-- `In x y`. -/
abbrev cIn (x y : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const inN) x) y

/-- The empty set. -/
abbrev cEmpty : CTm (Head L) n := .const emptyN

/-- `Union x`. -/
abbrev cUnion (x : CTm (Head L) n) : CTm (Head L) n := .app (.const unionN) x

/-- `Power x`. -/
abbrev cPower (x : CTm (Head L) n) : CTm (Head L) n := .app (.const powerN) x

/-- `UnivOf x`. -/
abbrev cUnivOf (x : CTm (Head L) n) : CTm (Head L) n := .app (.const univOfN) x

/-- `elem A a`. -/
abbrev cElem (A a : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const elemN) A) a

/-- `member A a`. -/
abbrev cMember (A a : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const memberN) A) a

/-- `the A x p`. -/
abbrev cThe (A x p : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const theN) A) x) p

/-- The type of `holds`. -/
abbrev holdsType : CTm (Head L) n := .pi cProp U0

/-- The type of `imp`. -/
abbrev impType : CTm (Head L) n := .pi cProp (.pi cProp cProp)

/-- The type of `all`: a set, and a predicate on its members. -/
abbrev allType : CTm (Head L) n := .pi allSets (.pi (.pi (.var 0) cProp) cProp)

/-- The type of `allSets`: a predicate on all sets. -/
abbrev allSetsType : CTm (Head L) n := .pi (.pi allSets cProp) cProp

/-- The type of membership: two sets give a proposition. -/
abbrev inType : CTm (Head L) n := .pi allSets (.pi allSets cProp)

/-- The type of an operation on the sets. -/
abbrev opType : CTm (Head L) n := .pi allSets allSets

/-- The type of `elem`. -/
abbrev elemType : CTm (Head L) n := .pi allSets (.pi (.var 0) allSets)

/-- The type of `member`. -/
abbrev memberType : CTm (Head L) n :=
  .pi allSets (.pi (.var 0) (cHolds (cIn (cElem (.var 1) (.var 0)) (.var 1))))

/-- The type of `the`. -/
abbrev theType : CTm (Head L) n :=
  .pi allSets (.pi allSets (.pi (cHolds (cIn (.var 0) (.var 1))) (.var 2)))

end Terms

variable [LevelOrder L]

variable (L) in
/-- **The table of the family**: each constant with its type. -/
def setTable : List (DeclName × CTm (Head L) 0) :=
  [(propN, U0), (holdsN, holdsType), (impN, impType), (allN, allType),
    (allSetsN, allSetsType), (inN, inType), (emptyN, allSets), (unionN, opType),
    (powerN, opType), (univOfN, opType), (elemN, elemType), (memberN, memberType),
    (theN, theType)]

variable (L) in
/-- The declarations of the family. -/
def setDecls : DeclName → Option (CTm (Head L) 0) := tableLookup (setTable L)

variable (L) in
/-- `holds (imp p q) ⟶ holds p → holds q`. -/
def holdsImp : DefiningEquation (Head L) where
  arity := 2
  telescope := .snoc (.snoc .nil cProp) cProp
  left := cHolds (cImp (.var 1) (.var 0))
  right := .pi (cHolds (.var 1)) (cHolds (.var 1))

variable (L) in
/-- `holds (all A P) ⟶ Π (x : A). holds (P x)`. -/
def holdsAll : DefiningEquation (Head L) where
  arity := 2
  telescope := .snoc (.snoc .nil allSets) (.pi (.var 0) cProp)
  left := cHolds (cAll (.var 1) (.var 0))
  right := .pi (.var 1) (cHolds (.app (.var 1) (.var 0)))

variable (L) in
/-- `holds (allSets P) ⟶ Π (x : set). holds (P x)`: the proofs of a statement about all sets
are the dependent functions on all sets. -/
def holdsAllSets : DefiningEquation (Head L) where
  arity := 1
  telescope := .snoc .nil (.pi allSets cProp)
  left := cHolds (cAllSets (.var 0))
  right := .pi allSets (cHolds (.app (.var 1) (.var 0)))

variable (L) in
/-- `elem A (the A x p) ⟶ x`. -/
def elemThe : DefiningEquation (Head L) where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil allSets) allSets) (cHolds (cIn (.var 0) (.var 1)))
  left := cElem (.var 2) (cThe (.var 2) (.var 1) (.var 0))
  right := .var 1

variable (L) in
/-- `the A (elem A a) q ⟶ a`. -/
def theElem : DefiningEquation (Head L) where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil allSets) (.var 0))
    (cHolds (cIn (cElem (.var 1) (.var 0)) (.var 1)))
  left := cThe (.var 2) (cElem (.var 2) (.var 1)) (.var 0)
  right := .var 1

variable (L) in
/-- The equations of the family. -/
def setEquations : List (DefiningEquation (Head L)) :=
  [holdsImp L, holdsAll L, holdsAllSets L, elemThe L, theElem L]

variable (L) in
/-- **The tower inside the sets with the constants of set theory.** -/
abbrev setTheory := withFamily (bare L) (setDecls L) (setEquations L)

theorem setDecls_prop : setDecls L propN = some U0 := rfl
theorem setDecls_holds : setDecls L holdsN = some holdsType := rfl
theorem setDecls_imp : setDecls L impN = some impType := rfl
theorem setDecls_all : setDecls L allN = some allType := rfl
theorem setDecls_allSets : setDecls L allSetsN = some allSetsType := rfl
theorem setDecls_in : setDecls L inN = some inType := rfl
theorem setDecls_empty : setDecls L emptyN = some allSets := rfl
theorem setDecls_union : setDecls L unionN = some opType := rfl
theorem setDecls_power : setDecls L powerN = some opType := rfl
theorem setDecls_univOf : setDecls L univOfN = some opType := rfl
theorem setDecls_elem : setDecls L elemN = some elemType := rfl
theorem setDecls_member : setDecls L memberN = some memberType := rfl
theorem setDecls_the : setDecls L theN = some theType := rfl

/-! ## The values -/

section Values

/-- The truth values. -/
noncomputable abbrev truthValues : ZFSet.{u} := Square.omega

variable (all : ZFSet.{u}) (around : ZFSet.{u} → ZFSet.{u})

/-- `holds` as a set: the identity on the truth values. -/
noncomputable def holdsValue : ZFSet.{u} := traceLam (graph truthValues fun p => p)

/-- Implication as a set: the trace functions from the proofs to the proofs. -/
noncomputable def impValue : ZFSet.{u} :=
  traceLam (graph truthValues fun p => traceLam (graph truthValues fun q =>
    tracePiSet p fun _ => q))

/-- Quantification over a set, as a set. -/
noncomputable def allValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph (tracePiSet A fun _ => truthValues) fun P =>
    tracePiSet A fun x => traceApp P x))

/-- Quantification over all sets, as a set. -/
noncomputable def allSetsValue : ZFSet.{u} :=
  traceLam (graph (tracePiSet all fun _ => truthValues) fun P =>
    tracePiSet all fun x => traceApp P x)

/-- Membership as a set: two sets give the truth value of the membership. -/
noncomputable def inValue : ZFSet.{u} :=
  traceLam (graph all fun x => traceLam (graph all fun y => truthCode (x ∈ y)))

/-- An operation on the sets as a set. -/
noncomputable def opValue (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} := traceLam (graph all f)

/-- `elem` as a set: at a set, the identity on its members. -/
noncomputable def elemValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph A fun a => a))

/-- `the` as a set: at a set `A`, a set `x` and a proof that `x` is a member of `A`, the set
`x`. -/
noncomputable def theValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph all fun x =>
    traceLam (graph (truthCode (x ∈ A)) fun _ => x)))

/-- The table of the values. -/
noncomputable def setValueTable : List (DeclName × ZFSet.{u}) :=
  [(propN, truthValues), (holdsN, holdsValue), (impN, impValue), (allN, allValue all),
    (allSetsN, allSetsValue all), (inN, inValue all), (emptyN, ∅),
    (unionN, opValue all ZFSet.sUnion), (powerN, opValue all ZFSet.powerset),
    (univOfN, opValue all around), (elemN, elemValue all), (memberN, ∅),
    (theN, theValue all)]

/-- **The values of the constants.** -/
noncomputable def setValues : DeclName → ZFSet.{u} := fun c =>
  (tableLookup (setValueTable all around) c).getD ∅

theorem setValues_prop : setValues all around propN = truthValues := rfl
theorem setValues_holds : setValues all around holdsN = holdsValue := rfl
theorem setValues_imp : setValues all around impN = impValue := rfl
theorem setValues_all : setValues all around allN = allValue all := rfl
theorem setValues_allSets : setValues all around allSetsN = allSetsValue all := rfl
theorem setValues_in : setValues all around inN = inValue all := rfl
theorem setValues_empty : setValues all around emptyN = ∅ := rfl
theorem setValues_union : setValues all around unionN = opValue all ZFSet.sUnion := rfl
theorem setValues_power : setValues all around powerN = opValue all ZFSet.powerset := rfl
theorem setValues_univOf : setValues all around univOfN = opValue all around := rfl
theorem setValues_elem : setValues all around elemN = elemValue all := rfl
theorem setValues_member : setValues all around memberN = ∅ := rfl
theorem setValues_the : setValues all around theN = theValue all := rfl

variable {all}

/-- A truth value of a proposition is a truth value. -/
theorem truthCode_mem_truthValues (P : Prop) : truthCode P ∈ truthValues.{u} :=
  ZFSet.mem_powerset.mpr (truthCode_subset P)

/-- **A family of truth values over any set has a truth value as its set of trace
functions.** -/
theorem tracePiSet_mem_truthValues {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (truth : ∀ x ∈ a, b x ∈ truthValues) : tracePiSet a b ∈ truthValues :=
  ZFSet.mem_powerset.mpr (tracePiSet_subterminal fun x hx => ZFSet.mem_powerset.mp (truth x hx))

/-- `holds` applied to a truth value is the truth value. -/
theorem holdsValue_apply {p : ZFSet.{u}} (hp : p ∈ truthValues) :
    traceApp holdsValue p = p :=
  traceApp_graph_beta (fun p => p) hp

/-- Implication applied to two truth values. -/
theorem impValue_apply {p q : ZFSet.{u}} (hp : p ∈ truthValues) (hq : q ∈ truthValues) :
    traceApp (traceApp impValue p) q = tracePiSet p fun _ => q := by
  unfold impValue
  rw [traceApp_graph_beta _ hp, traceApp_graph_beta _ hq]

/-- Quantification over a set applied to a predicate. -/
theorem allValue_apply {A P : ZFSet.{u}} (hA : A ∈ all)
    (hP : P ∈ tracePiSet A fun _ => truthValues) :
    traceApp (traceApp (allValue all) A) P = tracePiSet A fun x => traceApp P x := by
  unfold allValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hP]

/-- Quantification over all sets applied to a predicate. -/
theorem allSetsValue_apply {P : ZFSet.{u}} (hP : P ∈ tracePiSet all fun _ => truthValues) :
    traceApp (allSetsValue all) P = tracePiSet all fun x => traceApp P x :=
  traceApp_graph_beta _ hP

/-- Membership applied to two sets is the truth value of the membership. -/
theorem inValue_apply {x y : ZFSet.{u}} (hx : x ∈ all) (hy : y ∈ all) :
    traceApp (traceApp (inValue all) x) y = truthCode (x ∈ y) := by
  unfold inValue
  rw [traceApp_graph_beta _ hx, traceApp_graph_beta _ hy]

/-- An operation applied to a set. -/
theorem opValue_apply (f : ZFSet.{u} → ZFSet.{u}) {x : ZFSet.{u}} (hx : x ∈ all) :
    traceApp (opValue all f) x = f x :=
  traceApp_graph_beta f hx

/-- **`elem` is the identity**: a member of a set, as a set, is itself. -/
theorem elemValue_apply {A a : ZFSet.{u}} (hA : A ∈ all) (ha : a ∈ A) :
    traceApp (traceApp (elemValue all) A) a = a := by
  unfold elemValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ ha]

/-- **`the` is the identity**: a set with a proof of membership, as a term, is itself. -/
theorem theValue_apply {A x p : ZFSet.{u}} (hA : A ∈ all) (hx : x ∈ all)
    (hp : p ∈ truthCode (x ∈ A)) :
    traceApp (traceApp (traceApp (theValue all) A) x) p = x := by
  unfold theValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hx, traceApp_graph_beta _ hp]

/-- The empty set is a trace function into every family of sets that have it as a member. -/
theorem empty_mem_tracePiSet {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (inside : ∀ x ∈ a, (∅ : ZFSet.{u}) ∈ b x) : (∅ : ZFSet.{u}) ∈ tracePiSet a b := by
  rw [← traceLam_graph_empty a]
  exact traceLam_graph_mem inside

end Values

/-! ## A stage with a universe operation -/

/-- **A stage with a universe operation**: a stage whose least universe is closed, with an
operation on its sets that gives a set of the stage around each of them, such that the
universe of the tower at a successor level is the operation at the universe of the level. -/
structure UniverseStage (towerValue : LevelTower.Head L → ZFSet.{u}) (all classes : ZFSet.{u})
    (around : ZFSet.{u} → ZFSet.{u}) : Prop extends Stage towerValue all classes where
  zero_closed : Closed (towerValue (.sort LevelTower.zero))
  around_mem : ∀ {x : ZFSet.{u}}, x ∈ all → around x ∈ all
  around_contains : ∀ {x : ZFSet.{u}}, x ∈ all → x ∈ around x
  universe_succ : ∀ e : LevelExpr L, towerValue (.sort (.succ e)) = around (towerValue (.sort e))

/-! ## The set model -/

section Model

variable {towerValue : LevelTower.Head L → ZFSet.{u}} {all classes : ZFSet.{u}}
  {around : ZFSet.{u} → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}

/-- An assignment that gives the constants of the family their values. -/
abbrev Reads (L : Type) [LevelOrder L] (all : ZFSet.{u}) (around : ZFSet.{u} → ZFSet.{u})
    (consts : DeclName → ZFSet.{u}) : Prop :=
  ∀ c, setDecls L c ≠ none → consts c = setValues all around c

/-- The value an assignment gives a constant of the family. -/
theorem Reads.at (reads : Reads L all around consts) {c : DeclName} {T : CTm (Head L) 0}
    {value : ZFSet.{u}} (declared : setDecls L c = some T)
    (known : setValues all around c = value) : consts c = value :=
  (reads c (by rw [declared]; exact Option.some_ne_none T)).trans known

variable (reads : Reads L all around consts)

include reads

theorem Reads.prop : consts propN = truthValues := reads.at setDecls_prop rfl
theorem Reads.holds : consts holdsN = holdsValue := reads.at setDecls_holds rfl
theorem Reads.imp : consts impN = impValue := reads.at setDecls_imp rfl
theorem Reads.allOver : consts allN = allValue all := reads.at setDecls_all rfl
theorem Reads.allSets : consts allSetsN = allSetsValue all := reads.at setDecls_allSets rfl
theorem Reads.in : consts inN = inValue all := reads.at setDecls_in rfl
theorem Reads.empty : consts emptyN = ∅ := reads.at setDecls_empty rfl
theorem Reads.union : consts unionN = opValue all ZFSet.sUnion := reads.at setDecls_union rfl
theorem Reads.power : consts powerN = opValue all ZFSet.powerset := reads.at setDecls_power rfl
theorem Reads.univOf : consts univOfN = opValue all around := reads.at setDecls_univOf rfl
theorem Reads.elem : consts elemN = elemValue all := reads.at setDecls_elem rfl
theorem Reads.the : consts theN = theValue all := reads.at setDecls_the rfl

omit reads

variable (tower : UniverseModel (LevelTower.rules L) towerValue)
  (stage : UniverseStage towerValue all classes around)

include tower stage in
/-- The truth values form a set of the least universe. -/
theorem truthValues_mem_zero : truthValues.{u} ∈ towerValue (.sort LevelTower.zero) :=
  stage.zero_closed.power_mem (stage.zero_closed.singleton_mem
    (stage.zero_closed.empty_mem (tower.identity_mem (LevelTower.IsUniverse.sort _) True)))

include tower stage in
/-- A truth value is a member of the least universe. -/
theorem truthValue_mem_zero {p : ZFSet.{u}} (hp : p ∈ truthValues) :
    p ∈ towerValue (.sort LevelTower.zero) :=
  stage.zero_closed.transitive _ (truthValues_mem_zero tower stage) hp

include stage in
/-- The empty set is a set of the stage. -/
theorem empty_mem_all : (∅ : ZFSet.{u}) ∈ all :=
  stage.all_closed.empty_mem (stage.universe_mem LevelTower.zero)

include tower stage reads in
/-- **Every value lies in the set of its constant's type.** -/
theorem setValues_typed {c : DeclName} {T : CTm (Head L) 0} (declared : setDecls L c = some T) :
    setValues all around c ∈ ev (headValue towerValue all classes) consts T Fin.elim0 := by
  have row := tableLookup_mem declared
  simp only [setTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact truthValues_mem_zero tower stage
  · show holdsValue ∈ tracePiSet (consts propN) (fun _ => towerValue (.sort LevelTower.zero))
    rw [reads.prop]
    exact traceLam_graph_mem fun p hp => truthValue_mem_zero tower stage hp
  · show impValue ∈ tracePiSet (consts propN) (fun _ => tracePiSet (consts propN)
      (fun _ => consts propN))
    rw [reads.prop]
    exact traceLam_graph_mem fun p _ => traceLam_graph_mem fun q hq =>
      tracePiSet_mem_truthValues fun _ _ => hq
  · show allValue all ∈ tracePiSet all (fun A => tracePiSet
      (tracePiSet A (fun _ => consts propN)) (fun _ => consts propN))
    rw [reads.prop]
    exact traceLam_graph_mem fun A _ => traceLam_graph_mem fun P hP =>
      tracePiSet_mem_truthValues fun x hx => traceApp_mem_fibre hP hx
  · show allSetsValue all ∈ tracePiSet (tracePiSet all (fun _ => consts propN))
      (fun _ => consts propN)
    rw [reads.prop]
    exact traceLam_graph_mem fun P hP =>
      tracePiSet_mem_truthValues fun x hx => traceApp_mem_fibre hP hx
  · show inValue all ∈ tracePiSet all (fun _ => tracePiSet all (fun _ => consts propN))
    rw [reads.prop]
    exact traceLam_graph_mem fun x _ => traceLam_graph_mem fun y _ =>
      truthCode_mem_truthValues _
  · exact empty_mem_all stage
  · show opValue all ZFSet.sUnion ∈ tracePiSet all (fun _ => all)
    exact traceLam_graph_mem fun x hx => stage.all_closed.union_mem hx
  · show opValue all ZFSet.powerset ∈ tracePiSet all (fun _ => all)
    exact traceLam_graph_mem fun x hx => stage.all_closed.power_mem hx
  · show opValue all around ∈ tracePiSet all (fun _ => all)
    exact traceLam_graph_mem fun x hx => stage.around_mem hx
  · show elemValue all ∈ tracePiSet all (fun A => tracePiSet A (fun _ => all))
    exact traceLam_graph_mem fun A hA => traceLam_graph_mem fun a ha =>
      stage.all_closed.transitive _ hA ha
  · show (∅ : ZFSet.{u}) ∈ tracePiSet all (fun A => tracePiSet A (fun a =>
      traceApp (consts holdsN)
        (traceApp (traceApp (consts inN) (traceApp (traceApp (consts elemN) A) a)) A)))
    refine empty_mem_tracePiSet fun A hA => empty_mem_tracePiSet fun a ha => ?_
    rw [reads.holds, reads.in, reads.elem, elemValue_apply hA ha,
      inValue_apply (stage.all_closed.transitive _ hA ha) hA,
      holdsValue_apply (truthCode_mem_truthValues _)]
    exact (mem_truthCode _ _).mpr ⟨rfl, ha⟩
  · show theValue all ∈ tracePiSet all (fun A => tracePiSet all (fun x =>
      tracePiSet (traceApp (consts holdsN) (traceApp (traceApp (consts inN) x) A))
        (fun _ => A)))
    refine traceLam_graph_mem fun A hA => traceLam_graph_mem fun x hx => ?_
    rw [reads.holds, reads.in, inValue_apply hx hA,
      holdsValue_apply (truthCode_mem_truthValues _)]
    exact traceLam_graph_mem fun p hp => ((mem_truthCode _ _).mp hp).2

include reads in
/-- The proofs of an implication are the functions between the proofs. -/
theorem holdsImp_valid (η : Env.{u} 2)
    (sat : Sat (headValue towerValue all classes) consts
      (.snoc (.snoc .nil cProp) cProp : CCtx (Head L) 2) η) :
    ev (headValue towerValue all classes) consts
        (cHolds (cImp (.var 1) (.var 0)) : CTm (Head L) 2) η =
      ev (headValue towerValue all classes) consts
        (.pi (cHolds (.var 1)) (cHolds (.var 1)) : CTm (Head L) 2) η := by
  have hp : η 1 ∈ truthValues := by
    have member := sat 1
    change η 1 ∈ consts propN at member
    rwa [reads.prop] at member
  have hq : η 0 ∈ truthValues := by
    have member := sat 0
    change η 0 ∈ consts propN at member
    rwa [reads.prop] at member
  show traceApp (consts holdsN) (traceApp (traceApp (consts impN) (η 1)) (η 0)) =
    tracePiSet (traceApp (consts holdsN) (η 1)) (fun _ => traceApp (consts holdsN) (η 0))
  rw [reads.holds, reads.imp, impValue_apply hp hq,
    holdsValue_apply (tracePiSet_mem_truthValues fun _ _ => hq), holdsValue_apply hp,
    holdsValue_apply hq]

include reads in
/-- The proofs of a quantification over a set are the dependent functions into the proofs. -/
theorem holdsAll_valid (η : Env.{u} 2)
    (sat : Sat (headValue towerValue all classes) consts
      (.snoc (.snoc .nil allSets) (.pi (.var 0) cProp) : CCtx (Head L) 2) η) :
    ev (headValue towerValue all classes) consts
        (cHolds (cAll (.var 1) (.var 0)) : CTm (Head L) 2) η =
      ev (headValue towerValue all classes) consts
        (.pi (.var 1) (cHolds (.app (.var 1) (.var 0))) : CTm (Head L) 2) η := by
  have hA : η 1 ∈ all := sat 1
  have hP : η 0 ∈ tracePiSet (η 1) (fun _ => truthValues) := by
    have member := sat 0
    change η 0 ∈ tracePiSet (η 1) (fun _ => consts propN) at member
    rwa [reads.prop] at member
  have values : ∀ x ∈ η 1, traceApp (η 0) x ∈ truthValues :=
    fun x hx => traceApp_mem_fibre hP hx
  have truth : tracePiSet (η 1) (fun x => traceApp (η 0) x) ∈ truthValues :=
    tracePiSet_mem_truthValues values
  have left : traceApp (consts holdsN) (traceApp (traceApp (consts allN) (η 1)) (η 0)) =
      tracePiSet (η 1) (fun x => traceApp (η 0) x) := by
    rw [reads.holds, reads.allOver, allValue_apply hA hP]
    exact holdsValue_apply truth
  have right : tracePiSet (η 1) (fun x => traceApp (consts holdsN) (traceApp (η 0) x)) =
      tracePiSet (η 1) (fun x => traceApp (η 0) x) := by
    rw [reads.holds]
    exact tracePiSet_congr fun x hx => holdsValue_apply (values x hx)
  exact left.trans right.symm

include reads in
/-- **The proofs of a statement about all sets are the dependent functions on all sets**:
both sides are one truth value, although the function type is over all sets. -/
theorem holdsAllSets_valid (η : Env.{u} 1)
    (sat : Sat (headValue towerValue all classes) consts
      (.snoc .nil (.pi allSets cProp) : CCtx (Head L) 1) η) :
    ev (headValue towerValue all classes) consts
        (cHolds (cAllSets (.var 0)) : CTm (Head L) 1) η =
      ev (headValue towerValue all classes) consts
        (.pi allSets (cHolds (.app (.var 1) (.var 0))) : CTm (Head L) 1) η := by
  have hP : η 0 ∈ tracePiSet all (fun _ => truthValues) := by
    have member := sat 0
    change η 0 ∈ tracePiSet all (fun _ => consts propN) at member
    rwa [reads.prop] at member
  have values : ∀ x ∈ all, traceApp (η 0) x ∈ truthValues :=
    fun x hx => traceApp_mem_fibre hP hx
  have truth : tracePiSet all (fun x => traceApp (η 0) x) ∈ truthValues :=
    tracePiSet_mem_truthValues values
  have left : traceApp (consts holdsN) (traceApp (consts allSetsN) (η 0)) =
      tracePiSet all (fun x => traceApp (η 0) x) := by
    rw [reads.holds, reads.allSets, allSetsValue_apply hP]
    exact holdsValue_apply truth
  have right : tracePiSet all (fun x => traceApp (consts holdsN) (traceApp (η 0) x)) =
      tracePiSet all (fun x => traceApp (η 0) x) := by
    rw [reads.holds]
    exact tracePiSet_congr fun x hx => holdsValue_apply (values x hx)
  exact left.trans right.symm

include reads in
/-- A set with a proof of membership, taken as a term and back as a set, is the set. -/
theorem elemThe_valid (η : Env.{u} 3)
    (sat : Sat (headValue towerValue all classes) consts
      (.snoc (.snoc (.snoc .nil allSets) allSets) (cHolds (cIn (.var 0) (.var 1))) :
        CCtx (Head L) 3) η) :
    ev (headValue towerValue all classes) consts
        (cElem (.var 2) (cThe (.var 2) (.var 1) (.var 0)) : CTm (Head L) 3) η =
      ev (headValue towerValue all classes) consts (.var 1 : CTm (Head L) 3) η := by
  have hA : η 2 ∈ all := sat 2
  have hx : η 1 ∈ all := sat 1
  have hp : η 0 ∈ truthCode (η 1 ∈ η 2) := by
    have member := sat 0
    change η 0 ∈ traceApp (consts holdsN) (traceApp (traceApp (consts inN) (η 1)) (η 2))
      at member
    rwa [reads.holds, reads.in, inValue_apply hx hA,
      holdsValue_apply (truthCode_mem_truthValues _)] at member
  show traceApp (traceApp (consts elemN) (η 2))
      (traceApp (traceApp (traceApp (consts theN) (η 2)) (η 1)) (η 0)) = η 1
  rw [reads.the, reads.elem, theValue_apply hA hx hp,
    elemValue_apply hA ((mem_truthCode _ _).mp hp).2]

include stage reads in
/-- A term of a type, taken as a set and back as a term, is the term. -/
theorem theElem_valid (η : Env.{u} 3)
    (sat : Sat (headValue towerValue all classes) consts
      (.snoc (.snoc (.snoc .nil allSets) (.var 0))
        (cHolds (cIn (cElem (.var 1) (.var 0)) (.var 1))) : CCtx (Head L) 3) η) :
    ev (headValue towerValue all classes) consts
        (cThe (.var 2) (cElem (.var 2) (.var 1)) (.var 0) : CTm (Head L) 3) η =
      ev (headValue towerValue all classes) consts (.var 1 : CTm (Head L) 3) η := by
  have hA : η 2 ∈ all := sat 2
  have ha : η 1 ∈ η 2 := sat 1
  have haAll : η 1 ∈ all := stage.all_closed.transitive _ hA ha
  have hq : η 0 ∈ truthCode (η 1 ∈ η 2) := by
    have member := sat 0
    change η 0 ∈ traceApp (consts holdsN) (traceApp (traceApp (consts inN)
      (traceApp (traceApp (consts elemN) (η 2)) (η 1))) (η 2)) at member
    rwa [reads.holds, reads.in, reads.elem, elemValue_apply hA ha, inValue_apply haAll hA,
      holdsValue_apply (truthCode_mem_truthValues _)] at member
  show traceApp (traceApp (traceApp (consts theN) (η 2))
      (traceApp (traceApp (consts elemN) (η 2)) (η 1))) (η 0) = η 1
  rw [reads.the, reads.elem, elemValue_apply hA ha, theValue_apply hA haAll hq]

include stage reads in
/-- **Every equation holds between sets.** -/
theorem setEquations_valid :
    ∀ e ∈ setEquations L, ∀ η : Env.{u} e.arity,
      Sat (headValue towerValue all classes) consts e.telescope η →
        ev (headValue towerValue all classes) consts e.left η =
          ev (headValue towerValue all classes) consts e.right η := by
  intro e member η sat
  have cases : e = holdsImp L ∨ e = holdsAll L ∨ e = holdsAllSets L ∨ e = elemThe L ∨
      e = theElem L := by
    simpa [setEquations] using member
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact holdsImp_valid reads η sat
  · exact holdsAll_valid reads η sat
  · exact holdsAllSets_valid reads η sat
  · exact elemThe_valid reads η sat
  · exact theElem_valid reads stage η sat

variable (towerEq : ∀ {h h' : LevelTower.Head L}, LevelTower.HeadEq h h' →
  towerValue h = towerValue h')

include tower towerEq stage in
/-- **The tower inside the sets with the constants of set theory has a set model**, over
every stage with a universe operation: the propositions are the truth values, membership is
membership, the operations are those of the sets, and the two coercions are the identity. -/
theorem setTheory_setModel (base : DeclName → ZFSet.{u}) :
    SetModel (headValue towerValue all classes)
      (familyConsts base (setDecls L) (setValues all around)) (setTheory L) :=
  family_setModel_read (bare L)
    (fun consts _ => bare_setModel tower towerEq stage.toStage consts)
    (fun _ _ => rfl) (setValues all around)
    (fun _ _ reads {_ _} declared => setValues_typed reads tower stage declared)
    (fun _ _ reads => setEquations_valid reads stage)

include tower towerEq stage in
/-- Negative example: **the type of the proofs that the empty set is a member of itself has
no closed term.** -/
theorem no_proof_empty_in_empty (base : DeclName → ZFSet.{u}) (t : CTm (Head L) 0) :
    ¬ CTyped (setTheory L) .nil t (cHolds (cIn cEmpty cEmpty)) := by
  have reads : Reads L all around (familyConsts base (setDecls L) (setValues all around)) :=
    fun c declared => familyConsts_declared declared
  refine CDerivable.no_closed_inhabitant (setTheory_setModel tower stage towerEq base)
    (fun z inside => ?_) t
  change z ∈ traceApp (familyConsts base (setDecls L) (setValues all around) holdsN)
    (traceApp (traceApp (familyConsts base (setDecls L) (setValues all around) inN)
      (familyConsts base (setDecls L) (setValues all around) emptyN))
      (familyConsts base (setDecls L) (setValues all around) emptyN)) at inside
  rw [reads.holds, reads.in, reads.empty,
    inValue_apply (empty_mem_all stage) (empty_mem_all stage),
    holdsValue_apply (truthCode_mem_truthValues _)] at inside
  exact ZFSet.notMem_empty _ ((mem_truthCode _ _).mp inside).2

end Model

/-- Negative example: in the model **nothing is a member of the empty set**: the proposition
that a set is a member of the empty set is the false truth value. -/
theorem in_empty_false {all x : ZFSet.{u}} (hx : x ∈ all) (hEmpty : (∅ : ZFSet.{u}) ∈ all) :
    traceApp (traceApp (inValue all) x) ∅ = (∅ : ZFSet.{u}) := by
  rw [inValue_apply hx hEmpty]
  apply ZFSet.ext
  intro z
  constructor
  · intro inside
    exact absurd ((mem_truthCode _ _).mp inside).2 (ZFSet.notMem_empty x)
  · intro inside
    exact absurd inside (ZFSet.notMem_empty z)

/-! ## The sets of the lower universe are a stage with a universe operation -/

section LowerSets

open ZFSetUniverseClosure (CofinalInaccessibles univOf mem_univOf)
open ZFSetUniverseLift (carrierCode univOf_mem_carrierCode)
open ZFSetInterpretation (universeSet universeSet_closed universeSet_succ)
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ZFSetTraceUniverseInterpretation (interpretHead)

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  (ground : ZFSet.{u + 1}) (ν : Nat → L)

include small in
/-- **The sets of the lower universe, with the least closed universe around a set as the
universe operation, are a stage with a universe operation** for the tower over the natural
numbers. -/
theorem lowerSets_universeStage :
    UniverseStage (interpretHead large ZFSet.omega ground ν) carrierCode.{u}
      (univOf large carrierCode.{u}) (univOf large) where
  toStage := lowerSets_stage small large ground ν
  zero_closed := universeSet_closed large ZFSet.omega _
  around_mem := fun hx => univOf_mem_carrierCode small large hx
  around_contains := fun _ => mem_univOf large _
  universe_succ := fun e => universeSet_succ large ZFSet.omega (e.eval ν)

variable {ground}

include small in
/-- **The tower inside the sets with the constants of set theory has a set model**, relative
to cofinally many inaccessible cardinals in two universes: the type of all sets is read as
all the sets of the lower universe, `UnivOf` as the least closed universe around a set. -/
theorem lowerSets_setTheory_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts base (setDecls L) (setValues carrierCode.{u} (univOf large)))
      (setTheory L) :=
  setTheory_setModel
    (ZFSetReplayUniverseModel.universeModel large ZFSet.omega ground ν groundTyped)
    (lowerSets_universeStage small large ground ν)
    (fun same => ZFSetReplayUniverseFormation.headEq_values large ZFSet.omega ground ν same)
    base

include small large in
/-- **Consistency**, relative to cofinally many inaccessible cardinals in two universes: in
the tower inside the sets with the constants of set theory, no closed term proves that the
empty set is a member of itself. -/
theorem setTheory_consistent (t : CTm (Head L) 0) :
    ¬ CTyped (setTheory L) .nil t (cHolds (cIn cEmpty cEmpty)) :=
  no_proof_empty_in_empty
    (ZFSetReplayUniverseModel.universeModel large ZFSet.omega ∅ (fun _ => (LevelOrder.bot : L))
      (empty_mem_universeSet large ZFSet.omega _))
    (lowerSets_universeStage small large ∅ fun _ => LevelOrder.bot)
    (fun same => ZFSetReplayUniverseFormation.headEq_values large ZFSet.omega ∅ _ same)
    (fun _ => ∅) t

end LowerSets

/-! ## In the judgment -/

section Judgment

variable {n : Nat} {Γ : CCtx (Head L) n}

/-- The rules of the package contain the rules of the heads. -/
theorem setTheory_contains :
    Contains (Rules.sum (rules L) (familyRules (rules L) (setDecls L) (setEquations L))) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id

/-- A constant of the family is declared in the package as the family declares it. -/
theorem setTheory_declared {c : DeclName} {T : CTm (Head L) 0}
    (declared : setDecls L c = some T) : (setTheory L).constantType c = some T :=
  (withFamily_declared (bare L) rfl).trans declared

/-- The least universe is a set. -/
theorem U0_isSet : CTyped (setTheory L) Γ U0 allSets :=
  universe_isSet setTheory_contains _

/-- **The type of propositions is a type of the least universe.** -/
theorem prop_typed : CTyped (setTheory L) Γ cProp U0 :=
  definition_typed (setTheory_declared setDecls_prop)
    (.headType (HeadTyping.tower (LevelTower.HeadTyping.sort _)))
    (IsUniverse.tower (LevelTower.IsUniverse.sort _))

/-- The type of propositions is a set. -/
theorem prop_isSet : CTyped (setTheory L) Γ cProp allSets :=
  small_isSet setTheory_contains prop_typed

/-- `holds` takes a proposition to a type of the least universe. -/
theorem holds_typed : CTyped (setTheory L) Γ (.const holdsN) holdsType :=
  definition_typed (setTheory_declared setDecls_holds)
    (family_isSet setTheory_contains prop_isSet U0_isSet) IsUniverse.sets

/-- The proofs of a proposition form a type of the least universe. -/
theorem cHolds_typed {p : CTm (Head L) n} (hp : CTyped (setTheory L) Γ p cProp) :
    CTyped (setTheory L) Γ (cHolds p) U0 :=
  .appElim (B := U0) holds_typed hp

/-- The proofs of a proposition form a set. -/
theorem cHolds_isSet {p : CTm (Head L) n} (hp : CTyped (setTheory L) Γ p cProp) :
    CTyped (setTheory L) Γ (cHolds p) allSets :=
  small_isSet setTheory_contains (cHolds_typed hp)

/-- **Membership takes two sets to a proposition.** -/
theorem in_typed : CTyped (setTheory L) Γ (.const inN) inType :=
  definition_typed (setTheory_declared setDecls_in)
    (classToClass_typed setTheory_contains (sets_typed setTheory_contains)
      (classToSet_typed setTheory_contains (sets_typed setTheory_contains) prop_isSet))
    IsUniverse.classes

/-- The membership of two sets is a proposition. -/
theorem cIn_typed {x y : CTm (Head L) n} (hx : CTyped (setTheory L) Γ x allSets)
    (hy : CTyped (setTheory L) Γ y allSets) : CTyped (setTheory L) Γ (cIn x y) cProp :=
  .appElim (B := cProp) (.appElim (B := .pi allSets cProp) in_typed hx) hy

/-- The empty set is a set. -/
theorem empty_typed : CTyped (setTheory L) Γ cEmpty allSets :=
  definition_typed (setTheory_declared setDecls_empty) (sets_typed setTheory_contains)
    IsUniverse.classes

/-- The power set is an operation on the sets. -/
theorem power_typed : CTyped (setTheory L) Γ (.const powerN) opType :=
  definition_typed (setTheory_declared setDecls_power) (setFunctions_typed setTheory_contains)
    IsUniverse.classes

/-- The universe around a set is an operation on the sets. -/
theorem univOf_typed : CTyped (setTheory L) Γ (.const univOfN) opType :=
  definition_typed (setTheory_declared setDecls_univOf)
    (setFunctions_typed setTheory_contains) IsUniverse.classes

/-- Positive example: `Power Empty` is a set. -/
theorem powerEmpty_typed : CTyped (setTheory L) Γ (cPower cEmpty) allSets :=
  .appElim (B := allSets) power_typed empty_typed

/-- The type of `elem` is a type of `classes`. -/
theorem elemType_formed : CTyped (setTheory L) Γ elemType allClasses :=
  classToClass_typed setTheory_contains (sets_typed setTheory_contains)
    (setToClass_typed setTheory_contains (.var 0) (sets_typed setTheory_contains))

/-- `elem` has its type. -/
theorem elemConst_typed : CTyped (setTheory L) Γ (.const elemN) elemType :=
  definition_typed (setTheory_declared setDecls_elem) elemType_formed IsUniverse.classes

/-- **A term of a type that is a set is a set.** -/
theorem elem_typed {A a : CTm (Head L) n} (hA : CTyped (setTheory L) Γ A allSets)
    (ha : CTyped (setTheory L) Γ a A) : CTyped (setTheory L) Γ (cElem A a) allSets :=
  .appElim (B := allSets) (.appElim (B := .pi (.var 0) allSets) elemConst_typed hA) ha

/-- The type of `member` is a type of `classes`. -/
theorem memberType_formed : CTyped (setTheory L) Γ memberType allClasses :=
  classToSet_typed setTheory_contains (sets_typed setTheory_contains)
    (family_isSet setTheory_contains (.var 0)
      (cHolds_isSet (cIn_typed (elem_typed (.var 1) (.var 0)) (.var 1))))

/-- `member` has its type. -/
theorem memberConst_typed : CTyped (setTheory L) Γ (.const memberN) memberType :=
  definition_typed (setTheory_declared setDecls_member) memberType_formed IsUniverse.classes

/-- **Typing gives membership**: a term of a type that is a set has a proof that, as a set,
it is a member of the type. -/
theorem member_typed {A a : CTm (Head L) n} (hA : CTyped (setTheory L) Γ A allSets)
    (ha : CTyped (setTheory L) Γ a A) :
    CTyped (setTheory L) Γ (cMember A a) (cHolds (cIn (cElem A a) A)) := by
  have first : CTyped (setTheory L) Γ (.app (.const memberN) A)
      (.pi A (cHolds (cIn (cElem (A.rename Fin.succ) (.var 0)) (A.rename Fin.succ)))) :=
    .appElim (B := .pi (.var 0) (cHolds (cIn (cElem (.var 1) (.var 0)) (.var 1))))
      memberConst_typed hA
  have second := CDerivable.appElim first ha
  have back : CTm.inst0 a (CTm.rename Fin.succ A) = A := CTm.inst0_rename_wk a A
  have same : CTm.inst0 a (cHolds (cIn (cElem (A.rename Fin.succ) (.var 0)) (A.rename Fin.succ))) =
      cHolds (cIn (cElem A a) A) := by
    show cHolds (cIn (cElem (CTm.inst0 a (CTm.rename Fin.succ A)) a)
      (CTm.inst0 a (CTm.rename Fin.succ A))) = _
    rw [back]
  rw [same] at second
  exact second

/-- The type of `the` is a type of `classes`. -/
theorem theType_formed : CTyped (setTheory L) Γ theType allClasses :=
  classToClass_typed setTheory_contains (sets_typed setTheory_contains)
    (classToSet_typed setTheory_contains (sets_typed setTheory_contains)
      (family_isSet setTheory_contains (cHolds_isSet (cIn_typed (.var 0) (.var 1))) (.var 2)))

/-- `the` has its type. -/
theorem theConst_typed : CTyped (setTheory L) Γ (.const theN) theType :=
  definition_typed (setTheory_declared setDecls_the) theType_formed IsUniverse.classes

/-- Positive example: **the universe at a level, as a set, is a member of the universe at the
next level**, with a proof term. -/
theorem universe_member (e : LevelExpr L) :
    CTyped (setTheory L) Γ (cMember (universeAt (.succ e)) (universeAt e))
      (cHolds (cIn (cElem (universeAt (.succ e)) (universeAt e)) (universeAt (.succ e)))) :=
  member_typed (universe_isSet setTheory_contains _)
    (.headType (HeadTyping.tower (LevelTower.HeadTyping.sort e)))

end Judgment

end AmbientSets
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
