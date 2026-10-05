import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetsModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerInterpretation.Square
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetConstantFamilies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetsMetatheory

/-!
# The constants of set theory over the tower inside the sets

Over the tower inside the sets (`MegalodonHOTG`), where every type is a set, this file declares
as one family (`setTheory`) the constants that make the sets a language of their own, and,
beside it, the same constants with rule constants for the logic in place of the equations
(`setTheoryRules`).

* **The logic.** `prop : U₀`, the type of propositions; `holds : prop → U₀`, the type of the
  proofs of a proposition; `imp : prop → prop → prop`; and one quantifier,
  `all : Π (T : class). (T → prop) → prop`, over any type of `allClasses`: a set, the type of
  all sets (`cAllSets`), or a type of predicates or functions on the sets.
* **Equality.** `eq : Π (T : class). T → T → prop`, at any type of `allClasses`.
* **The sets.** `In : set → set → prop`; `Empty : set`; `Union`, `Power`, `UnivOf : set → set`;
  `Sep : set → (set → prop) → set`, the subset of a set given by a predicate;
  `Repl : set → (set → set) → set`, the image of a set under a function;
  `Eps : (set → prop) → set`, a set of which a predicate is true, if there is one.
* **Types are sets.** `elem : Π (A : set). A → set`: a term of a type is a set.
  `member : Π (A : set). Π (a : A). holds (In (elem A a) A)`: typing gives membership.
  `the : Π (A : set). Π (x : set). holds (In x A) → A`: membership gives typing. A set proved to
  be a member of a type is a term of the type.

The equations (`setEquations`): the proofs of an implication are the functions between the
proofs, and the proofs of a quantification are the dependent functions into the proofs,
whatever the size of the type quantified over; the proofs of an equality are the proofs of
the identity; `elem` and `the` undo each other.

**The set model** (`setTheory_setModel`), over every chain of closed universes whose universe
of the sets is closed under an operation on its members: the propositions are the truth
values, `holds` is the identity on them, membership is membership, the operations are those
of the sets, `UnivOf` is the operation, and `elem` and `the` are the identity on the
underlying sets. Every equation holds. The equation for quantification holds although its
right side may be a function type over all sets, or over all predicates on them: a trace
function into truth values is a truth value, over a domain of any size. At every assignment that reads the
family, the values of `holds`, `imp`, `all`, `eq` and `In` at truth values and sets are the
truth values of the proposition, the implication, the universal statement, the equality and
the membership (`ev_cHolds`, `ev_cImp`, `ev_cAll`, `ev_cEq`, `ev_cIn`).

The chain that reads the type of all sets as the sets of one universe of Lean
(`MegalodonHOTG.SetsModel.stages`) is such a chain, with the least closed universe around a set as
the operation, relative to cofinally many inaccessible cardinals in both universes; so the
package has a set model (`lowerSets_setTheory_setModel`) and is consistent
(`setTheory_consistent`).

In the judgment (section `Judgment`), in every package over the set theory
(`OverSetTheory`: it contains the rules and declares the constants, as a package with further
constants, datatypes or definitions does): the declared types are formed and the constants
have them; a quantification over a type of `allClasses` is a proposition (`cAll_typed`), so a
statement about all sets is one (`cAllSets_typed`); a term of a type that is a set gives a
set (`elem_typed`) and a proof that the set is a member of the type (`member_typed`). Equal
propositions have equal types of proofs (`cHolds_congr`). Equal implications, quantifications
and equalities are equal propositions (`cImp_congr`, `cAll_congr`, `cAll_lam_congr`,
`cEq_congr`); an abstraction of equal propositions is an equal predicate (`predicate_congr`),
and applied to the newest variable it is its body (`predicate_apply_var`). Where the package
contains the steps of the equations, the proofs of an implication are the functions between
the proofs (`holds_imp_rule`) and the proofs of a quantification are the dependent functions
into the proofs (`holds_all_rule`, `holds_all_lam_rule`).

Positive examples: the universe at a level, as a set, is a member of the universe at the next
level, with a proof term (`universe_member`); `Power Empty` is a set (`powerEmpty_typed`);
"for every set `N`, `Power N` is a member of `UnivOf N`" is a proposition
(`powerInUniverse_typed`) and is true in the model (`powerInUniverse_true`), a statement
about all sets in which nothing computes.
Negative examples: in the model nothing is a member of the empty set (`in_empty_false`), and
the type of the proofs that the empty set is a member of itself has no closed term
(`no_proof_empty_in_empty`, `setTheory_consistent`).

**Not admitted for running** (section `Admission`): the package does not have both injective
type formers and declared steps that are equalities at the types of their left sides, the
hypotheses under which every step keeps the type (`setTheory_not_admitted`). The proofs of
"the empty set is a member of every set" are a type of the least universe, and the equation
for the proofs of a quantification steps them to a function type over all the sets, which
is a type of no universe at a level of `L`. The set model holds all the same: there the
proofs of any statement are a truth value.

**The set theory on rule constants** (`setTheoryRules`): the same declarations, no equation,
and a constant for each rule of the logic (`ruleTable`), with `T : allClasses` and
`P : T → prop`:

    impI : Π (p q : prop). (holds p → holds q) → holds (imp p q)
    impE : Π (p q : prop). holds (imp p q) → holds p → holds q
    allI : Π (T : class). Π (P : T → prop). (Π (x : T). holds (P x)) → holds (all T P)
    allE : Π (T : class). Π (P : T → prop). holds (all T P) → Π (x : T). holds (P x)
    eqI  : Π (T : class). Π (a b : T). Id T a b → holds (eq T a b)
    eqE  : Π (T : class). Π (a b : T). holds (eq T a b) → Id T a b
    elemTheLaw : Π (A x : set). Π (p : holds (In x A)). Id set (elem A (the A x p)) x
    theElemLaw : Π (A : set). Π (a : A). Π (q : holds (In (elem A a) A)).
                   Id A (the A (elem A a) q) a

It is a family of declared constants with no equation (`withRules`, here with no further
constant) and it declares the constants of set theory, so every typing of section `Judgment`
holds in it (`setTheoryRules_over`). Its set model, over every chain whose universe of the
sets is closed under the operation, reads every rule constant as the empty set: the
conclusion of each rule is true whenever the types of its premises have members
(`ruleTable_typed`, `setTheoryRules_setModel`, `lowerSets_setTheoryRules_setModel`). No closed
term proves that the empty set is a member of itself, and none has the type `Π (X : U₀). X`
(`setTheoryRules_consistent`, `setTheoryRules_consistent_emptyType`). Its type formers are
injective, and every step of a typed term keeps its type and its set value
(`setTheoryRules_formerFacts`, `setTheoryRules_reduces_typed`,
`setTheoryRules_reduction_keeps_value`): it has both properties that `setTheory` lacks
(`setTheoryRules_admitted`). **Every term typed in a formed context of it is strongly
normalizing**, and so with further declared constants (`setTheoryRules_sn`, `withRules_sn`),
since its constants never compute (`constants_sn`). The proofs of a proposition form a type of
`allClasses` (`cHolds_isClass`). The typings of the rule constants, and the
proofs built from them, are in `MegalodonHOTG.SetProofs`.

Positive examples: in the set theory on rule constants the proofs of "the empty set is a
member of every set" take no step (`holdsEmptyIn_no_step_rules`), and the type of the proofs
that the empty set is a member of a set, as a function on the sets applied to `Power Empty`,
is strongly normalizing (`holdsEmptyInPower_sn`). Negative examples: the
proofs that the empty set is a member of itself, and `Π (X : U₀). X`, have no closed term there
(`setTheoryRules_no_proof_empty_in_empty`, `setTheoryRules_no_closed_emptyType`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (Closed)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta traceLam_graph_empty
  tracePiSet_subterminal tracePiSet_congr)
open ZFSetTraceProofDecoding (truthCode mem_truthCode truthCode_subset)
open ZFSetHenkinInterpretation (replacement mem_replacement)

universe u

variable {L : Type}

/-! ## The constants and their types -/

/-- The type of propositions. -/
def propN : DeclName := .str .anonymous "prop"
/-- The proofs of a proposition. -/
def holdsN : DeclName := .str .anonymous "holds"
/-- Implication. -/
def impN : DeclName := .str .anonymous "imp"
/-- Quantification over a type of `allClasses`. -/
def allN : DeclName := .str .anonymous "all"
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
/-- Equality of two terms of a type of `allClasses`. -/
def eqN : DeclName := .str .anonymous "eq"
/-- The subset of a set given by a predicate on the sets. -/
def sepN : DeclName := .str .anonymous "Sep"
/-- The image of a set under a function on the sets. -/
def replN : DeclName := .str .anonymous "Repl"
/-- A set of which a predicate on the sets is true, if there is one. -/
def epsN : DeclName := .str .anonymous "Eps"

section Terms

variable [LevelOrder L] {n : Nat}

/-- The type of propositions. -/
abbrev cProp : CTm (Head L) n := .const propN

/-- `holds p`. -/
abbrev cHolds (p : CTm (Head L) n) : CTm (Head L) n := .app (.const holdsN) p

/-- `imp p q`. -/
abbrev cImp (p q : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const impN) p) q

/-- `all T P`. -/
abbrev cAll (T P : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const allN) T) P

/-- Quantification over all sets: `all set P`. -/
abbrev cAllSets (P : CTm (Head L) n) : CTm (Head L) n := cAll allSets P

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

/-- `eq T a b`. -/
abbrev cEq (T a b : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const eqN) T) a) b

/-- `Sep A P`. -/
abbrev cSep (A P : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const sepN) A) P

/-- `Repl A F`. -/
abbrev cRepl (A F : CTm (Head L) n) : CTm (Head L) n := .app (.app (.const replN) A) F

/-- `Eps P`. -/
abbrev cEps (P : CTm (Head L) n) : CTm (Head L) n := .app (.const epsN) P

/-- The type of `holds`. -/
abbrev holdsType : CTm (Head L) n := .pi cProp U0

/-- The type of `imp`. -/
abbrev impType : CTm (Head L) n := .pi cProp (.pi cProp cProp)

/-- The type of `all`: a type of `allClasses`, and a predicate on its terms. -/
abbrev allType : CTm (Head L) n := .pi allClasses (.pi (.pi (.var 0) cProp) cProp)

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

/-- The type of `eq`: a type of `allClasses` and two of its terms. -/
abbrev eqType : CTm (Head L) n := .pi allClasses (.pi (.var 0) (.pi (.var 1) cProp))

/-- The type of `Sep`: a set and a predicate on the sets. -/
abbrev sepType : CTm (Head L) n := .pi allSets (.pi (.pi allSets cProp) allSets)

/-- The type of `Repl`: a set and a function on the sets. -/
abbrev replType : CTm (Head L) n := .pi allSets (.pi (.pi allSets allSets) allSets)

/-- The type of `Eps`: a predicate on the sets. -/
abbrev epsType : CTm (Head L) n := .pi (.pi allSets cProp) allSets

end Terms

variable [LevelOrder L]

variable (L) in
/-- **The table of the family**: each constant with its type. -/
def setTable : List (DeclName × CTm (Head L) 0) :=
  [(propN, U0), (holdsN, holdsType), (impN, impType), (allN, allType), (inN, inType),
    (emptyN, allSets), (unionN, opType), (powerN, opType), (univOfN, opType),
    (elemN, elemType), (memberN, memberType), (theN, theType), (eqN, eqType),
    (sepN, sepType), (replN, replType), (epsN, epsType)]

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
/-- `holds (all T P) ⟶ Π (x : T). holds (P x)`: the proofs of a quantification are the
dependent functions into the proofs. At the type of all sets: the proofs of a statement about
all sets are the dependent functions on all sets. -/
def holdsAll : DefiningEquation (Head L) where
  arity := 2
  telescope := .snoc (.snoc .nil allClasses) (.pi (.var 0) cProp)
  left := cHolds (cAll (.var 1) (.var 0))
  right := .pi (.var 1) (cHolds (.app (.var 1) (.var 0)))

variable (L) in
/-- `holds (eq T a b) ⟶ Id T a b`: the proofs of an equality are the proofs of the identity. -/
def holdsEq : DefiningEquation (Head L) where
  arity := 3
  telescope := .snoc (.snoc (.snoc .nil allClasses) (.var 0)) (.var 1)
  left := cHolds (cEq (.var 2) (.var 1) (.var 0))
  right := .id (.var 2) (.var 1) (.var 0)

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
  [holdsImp L, holdsAll L, holdsEq L, elemThe L, theElem L]

variable (L) in
/-- **The tower inside the sets with the constants of set theory.** -/
abbrev setTheory := withFamily (bare L) (setDecls L) (setEquations L)

theorem setDecls_prop : setDecls L propN = some U0 := rfl
theorem setDecls_holds : setDecls L holdsN = some holdsType := rfl
theorem setDecls_imp : setDecls L impN = some impType := rfl
theorem setDecls_all : setDecls L allN = some allType := rfl
theorem setDecls_in : setDecls L inN = some inType := rfl
theorem setDecls_empty : setDecls L emptyN = some allSets := rfl
theorem setDecls_union : setDecls L unionN = some opType := rfl
theorem setDecls_power : setDecls L powerN = some opType := rfl
theorem setDecls_univOf : setDecls L univOfN = some opType := rfl
theorem setDecls_elem : setDecls L elemN = some elemType := rfl
theorem setDecls_member : setDecls L memberN = some memberType := rfl
theorem setDecls_the : setDecls L theN = some theType := rfl
theorem setDecls_eq : setDecls L eqN = some eqType := rfl
theorem setDecls_sep : setDecls L sepN = some sepType := rfl
theorem setDecls_repl : setDecls L replN = some replType := rfl
theorem setDecls_eps : setDecls L epsN = some epsType := rfl

/-! ## The values -/

section Values

/-- The truth values. -/
noncomputable abbrev truthValues : ZFSet.{u} := Square.omega

variable (all classes : ZFSet.{u}) (around : ZFSet.{u} → ZFSet.{u})

/-- `holds` as a set: the identity on the truth values. -/
noncomputable def holdsValue : ZFSet.{u} := traceLam (graph truthValues fun p => p)

/-- Implication as a set: the trace functions from the proofs to the proofs. -/
noncomputable def impValue : ZFSet.{u} :=
  traceLam (graph truthValues fun p => traceLam (graph truthValues fun q =>
    tracePiSet p fun _ => q))

/-- Quantification, as a set: at a set of the sort of the sets and a predicate on its
members, the trace functions into the truth values of the predicate. -/
noncomputable def allValue : ZFSet.{u} :=
  traceLam (graph classes fun A => traceLam (graph (tracePiSet A fun _ => truthValues) fun P =>
    tracePiSet A fun x => traceApp P x))

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

/-- Equality as a set: at a set of the sort of the sets and two of its members, the truth
value of their equality. -/
noncomputable def eqValue : ZFSet.{u} :=
  traceLam (graph classes fun T => traceLam (graph T fun a => traceLam (graph T fun b =>
    truthCode (a = b))))

/-- `Sep` as a set: at a set and a predicate on the sets, the members of the set at which the
predicate is true. -/
noncomputable def sepValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph (tracePiSet all fun _ => truthValues) fun P =>
    ZFSet.sep (fun x => (∅ : ZFSet.{u}) ∈ traceApp P x) A))

/-- `Repl` as a set: at a set and a function on the sets, the set of the values of the function
at the members of the set. -/
noncomputable def replValue : ZFSet.{u} :=
  traceLam (graph all fun A => traceLam (graph (tracePiSet all fun _ => all) fun F =>
    replacement A fun x => traceApp F x))

/-- A member of `all` at which a predicate, coded as a set, is true, when there is one, and the
empty set otherwise. -/
noncomputable def epsChoice (P : ZFSet.{u}) : ZFSet.{u} :=
  haveI := Classical.propDecidable (∃ x, x ∈ all ∧ (∅ : ZFSet.{u}) ∈ traceApp P x)
  if h : ∃ x, x ∈ all ∧ (∅ : ZFSet.{u}) ∈ traceApp P x then Classical.choose h else ∅

/-- `Eps` as a set: at a predicate on the sets, a set at which it is true, if there is one. -/
noncomputable def epsValue : ZFSet.{u} :=
  traceLam (graph (tracePiSet all fun _ => truthValues) fun P => epsChoice all P)

/-- The table of the values. -/
noncomputable def setValueTable : List (DeclName × ZFSet.{u}) :=
  [(propN, truthValues), (holdsN, holdsValue), (impN, impValue), (allN, allValue classes),
    (inN, inValue all), (emptyN, ∅), (unionN, opValue all ZFSet.sUnion),
    (powerN, opValue all ZFSet.powerset), (univOfN, opValue all around),
    (elemN, elemValue all), (memberN, ∅), (theN, theValue all), (eqN, eqValue classes),
    (sepN, sepValue all), (replN, replValue all), (epsN, epsValue all)]

/-- **The values of the constants.** -/
noncomputable def setValues : DeclName → ZFSet.{u} := fun c =>
  (tableLookup (setValueTable all classes around) c).getD ∅

theorem setValues_prop : setValues all classes around propN = truthValues := rfl
theorem setValues_holds : setValues all classes around holdsN = holdsValue := rfl
theorem setValues_imp : setValues all classes around impN = impValue := rfl
theorem setValues_all : setValues all classes around allN = allValue classes := rfl
theorem setValues_in : setValues all classes around inN = inValue all := rfl
theorem setValues_empty : setValues all classes around emptyN = ∅ := rfl
theorem setValues_union :
    setValues all classes around unionN = opValue all ZFSet.sUnion := rfl
theorem setValues_power :
    setValues all classes around powerN = opValue all ZFSet.powerset := rfl
theorem setValues_univOf : setValues all classes around univOfN = opValue all around := rfl
theorem setValues_elem : setValues all classes around elemN = elemValue all := rfl
theorem setValues_member : setValues all classes around memberN = ∅ := rfl
theorem setValues_the : setValues all classes around theN = theValue all := rfl
theorem setValues_eq : setValues all classes around eqN = eqValue classes := rfl
theorem setValues_sep : setValues all classes around sepN = sepValue all := rfl
theorem setValues_repl : setValues all classes around replN = replValue all := rfl
theorem setValues_eps : setValues all classes around epsN = epsValue all := rfl

variable {all classes}

/-- A truth value of a proposition is a truth value. -/
theorem truthCode_mem_truthValues (P : Prop) : truthCode P ∈ truthValues.{u} :=
  ZFSet.mem_powerset.mpr (truthCode_subset P)

/-- Every truth value of the package is the truth value of a statement. -/
theorem truthValue_eq {x : ZFSet.{u}} (hx : x ∈ truthValues) :
    truthCode ((∅ : ZFSet.{u}) ∈ x) = x :=
  Square.truthCode_empty_mem (ZFSet.mem_powerset.mp hx)

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

/-- Quantification applied to a set of the sort of the sets and a predicate on its members. -/
theorem allValue_apply {A P : ZFSet.{u}} (hA : A ∈ classes)
    (hP : P ∈ tracePiSet A fun _ => truthValues) :
    traceApp (traceApp (allValue classes) A) P = tracePiSet A fun x => traceApp P x := by
  unfold allValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hP]

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

/-- Equality applied to a set of the sort of the sets and two of its members. -/
theorem eqValue_apply {T a b : ZFSet.{u}} (hT : T ∈ classes) (ha : a ∈ T) (hb : b ∈ T) :
    traceApp (traceApp (traceApp (eqValue classes) T) a) b = truthCode (a = b) := by
  unfold eqValue
  rw [traceApp_graph_beta _ hT, traceApp_graph_beta _ ha, traceApp_graph_beta _ hb]

/-- `Sep` applied to a set and a predicate on the sets. -/
theorem sepValue_apply {A P : ZFSet.{u}} (hA : A ∈ all)
    (hP : P ∈ tracePiSet all fun _ => truthValues) :
    traceApp (traceApp (sepValue all) A) P =
      ZFSet.sep (fun x => (∅ : ZFSet.{u}) ∈ traceApp P x) A := by
  unfold sepValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hP]

/-- **A set is a member of the subset given by a predicate exactly when it is a member of the
set and the predicate is true of it.** -/
theorem mem_sepValue {A P x : ZFSet.{u}} (hA : A ∈ all)
    (hP : P ∈ tracePiSet all fun _ => truthValues) :
    x ∈ traceApp (traceApp (sepValue all) A) P ↔ x ∈ A ∧ (∅ : ZFSet.{u}) ∈ traceApp P x := by
  rw [sepValue_apply hA hP, ZFSet.mem_sep]

/-- `Repl` applied to a set and a function on the sets. -/
theorem replValue_apply {A F : ZFSet.{u}} (hA : A ∈ all) (hF : F ∈ tracePiSet all fun _ => all) :
    traceApp (traceApp (replValue all) A) F = replacement A fun x => traceApp F x := by
  unfold replValue
  rw [traceApp_graph_beta _ hA, traceApp_graph_beta _ hF]

/-- **A set is a member of the image of a set under a function exactly when it is the value of
the function at a member of the set.** -/
theorem mem_replValue {A F y : ZFSet.{u}} (hA : A ∈ all) (hF : F ∈ tracePiSet all fun _ => all) :
    y ∈ traceApp (traceApp (replValue all) A) F ↔ ∃ x ∈ A, traceApp F x = y := by
  rw [replValue_apply hA hF, mem_replacement]

/-- The chosen set is a member of `all`, when the empty set is. -/
theorem epsChoice_mem (emptyAll : (∅ : ZFSet.{u}) ∈ all) (P : ZFSet.{u}) :
    epsChoice all P ∈ all := by
  unfold epsChoice
  split
  · next h => exact (Classical.choose_spec h).1
  · exact emptyAll

/-- **The predicate is true at the chosen set, when it is true at some set.** -/
theorem epsChoice_spec {P x : ZFSet.{u}} (hx : x ∈ all)
    (holds : (∅ : ZFSet.{u}) ∈ traceApp P x) :
    (∅ : ZFSet.{u}) ∈ traceApp P (epsChoice all P) := by
  have witness : ∃ y, y ∈ all ∧ (∅ : ZFSet.{u}) ∈ traceApp P y := ⟨x, hx, holds⟩
  unfold epsChoice
  split
  · next h => exact (Classical.choose_spec h).2
  · next h => exact absurd witness h

/-- `Eps` applied to a predicate on the sets. -/
theorem epsValue_apply {P : ZFSet.{u}} (hP : P ∈ tracePiSet all fun _ => truthValues) :
    traceApp (epsValue all) P = epsChoice all P :=
  traceApp_graph_beta _ hP

/-- The empty set is a trace function into every family of sets that have it as a member. -/
theorem empty_mem_tracePiSet {a : ZFSet.{u}} {b : ZFSet.{u} → ZFSet.{u}}
    (inside : ∀ x ∈ a, (∅ : ZFSet.{u}) ∈ b x) : (∅ : ZFSet.{u}) ∈ tracePiSet a b := by
  rw [← traceLam_graph_empty a]
  exact traceLam_graph_mem inside

end Values

/-! ## The set model -/

section Model

variable {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
  {ν : Nat → Above L} {consts : DeclName → ZFSet.{u}}

/-- An assignment that gives the constants of the family their values. -/
abbrev Reads (L : Type) [LevelOrder L] (all classes : ZFSet.{u})
    (around : ZFSet.{u} → ZFSet.{u}) (consts : DeclName → ZFSet.{u}) : Prop :=
  ∀ c, setDecls L c ≠ none → consts c = setValues all classes around c

/-- The value an assignment gives a constant of the family. -/
theorem Reads.at {all classes : ZFSet.{u}} (reads : Reads L all classes around consts)
    {c : DeclName} {T : CTm (Head L) 0} {value : ZFSet.{u}} (declared : setDecls L c = some T)
    (known : setValues all classes around c = value) : consts c = value :=
  (reads c (by rw [declared]; exact Option.some_ne_none T)).trans known

section Readings

variable {all classes : ZFSet.{u}} (reads : Reads L all classes around consts)

include reads

theorem Reads.prop : consts propN = truthValues := reads.at setDecls_prop rfl
theorem Reads.holds : consts holdsN = holdsValue := reads.at setDecls_holds rfl
theorem Reads.imp : consts impN = impValue := reads.at setDecls_imp rfl
theorem Reads.allOver : consts allN = allValue classes := reads.at setDecls_all rfl
theorem Reads.in : consts inN = inValue all := reads.at setDecls_in rfl
theorem Reads.empty : consts emptyN = ∅ := reads.at setDecls_empty rfl
theorem Reads.union : consts unionN = opValue all ZFSet.sUnion := reads.at setDecls_union rfl
theorem Reads.power : consts powerN = opValue all ZFSet.powerset := reads.at setDecls_power rfl
theorem Reads.univOf : consts univOfN = opValue all around := reads.at setDecls_univOf rfl
theorem Reads.elem : consts elemN = elemValue all := reads.at setDecls_elem rfl
theorem Reads.the : consts theN = theValue all := reads.at setDecls_the rfl
theorem Reads.eq : consts eqN = eqValue classes := reads.at setDecls_eq rfl
theorem Reads.sep : consts sepN = sepValue all := reads.at setDecls_sep rfl
theorem Reads.repl : consts replN = replValue all := reads.at setDecls_repl rfl
theorem Reads.eps : consts epsN = epsValue all := reads.at setDecls_eps rfl

/-- **The choice law.** A trace predicate true of a set is true of the set `Eps` chooses. -/
theorem epsI_holds {P x : ZFSet.{u}}
    (hP : P ∈ tracePiSet all (fun _ => truthValues))
    (hx : x ∈ all)
    (hPx : (∅ : ZFSet.{u}) ∈ traceApp P x) :
    (∅ : ZFSet.{u}) ∈ traceApp P (traceApp (consts epsN) P) := by
  rw [reads.eps, epsValue_apply hP]
  exact epsChoice_spec hx hPx

end Readings

variable (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (chain : ClosedChain V)
  (groundTyped : ground ∈ V LevelOrder.bot)
  (aroundMem : ∀ {x : ZFSet.{u}}, x ∈ V (.above 0) → around x ∈ V (.above 0))

include chain groundTyped in
/-- The truth values form a set of the least universe. -/
theorem truthValues_mem_zero : truthValues.{u} ∈ V (.below LevelOrder.bot) :=
  (chain.closed _).power_mem ((chain.closed _).singleton_mem
    (chain.empty_mem groundTyped (.below LevelOrder.bot)))

include chain groundTyped in
/-- A truth value is a member of the least universe. -/
theorem truthValue_mem_zero {p : ZFSet.{u}} (hp : p ∈ truthValues) :
    p ∈ V (.below LevelOrder.bot) :=
  (chain.closed _).transitive _ (truthValues_mem_zero chain groundTyped) hp

include chain groundTyped in
/-- The empty set is a set. -/
theorem empty_mem_all : (∅ : ZFSet.{u}) ∈ V (.above 0) :=
  chain.empty_mem groundTyped (.above 0)

include reads chain groundTyped aroundMem in
/-- **Every value lies in the set of its constant's type.** -/
theorem setValues_typed {c : DeclName} {T : CTm (Head L) 0} (declared : setDecls L c = some T) :
    setValues (V (.above 0)) (V (.above 1)) around c ∈
      ev (chainHead V ground ν) consts T Fin.elim0 := by
  have row := tableLookup_mem declared
  simp only [setTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact truthValues_mem_zero chain groundTyped
  · show holdsValue ∈ tracePiSet (consts propN) (fun _ => V (.below LevelOrder.bot))
    rw [reads.prop]
    exact traceLam_graph_mem fun p hp => truthValue_mem_zero chain groundTyped hp
  · show impValue ∈ tracePiSet (consts propN) (fun _ => tracePiSet (consts propN)
      (fun _ => consts propN))
    rw [reads.prop]
    exact traceLam_graph_mem fun p _ => traceLam_graph_mem fun q hq =>
      tracePiSet_mem_truthValues fun _ _ => hq
  · show allValue (V (.above 1)) ∈ tracePiSet (V (.above 1)) (fun A => tracePiSet
      (tracePiSet A (fun _ => consts propN)) (fun _ => consts propN))
    rw [reads.prop]
    exact traceLam_graph_mem fun A _ => traceLam_graph_mem fun P hP =>
      tracePiSet_mem_truthValues fun x hx => traceApp_mem_fibre hP hx
  · show inValue (V (.above 0)) ∈
      tracePiSet (V (.above 0)) (fun _ => tracePiSet (V (.above 0)) (fun _ => consts propN))
    rw [reads.prop]
    exact traceLam_graph_mem fun x _ => traceLam_graph_mem fun y _ =>
      truthCode_mem_truthValues _
  · exact empty_mem_all chain groundTyped
  · show opValue (V (.above 0)) ZFSet.sUnion ∈ tracePiSet (V (.above 0)) (fun _ => V (.above 0))
    exact traceLam_graph_mem fun x hx => (chain.closed _).union_mem hx
  · show opValue (V (.above 0)) ZFSet.powerset ∈
      tracePiSet (V (.above 0)) (fun _ => V (.above 0))
    exact traceLam_graph_mem fun x hx => (chain.closed _).power_mem hx
  · show opValue (V (.above 0)) around ∈ tracePiSet (V (.above 0)) (fun _ => V (.above 0))
    exact traceLam_graph_mem fun x hx => aroundMem hx
  · show elemValue (V (.above 0)) ∈
      tracePiSet (V (.above 0)) (fun A => tracePiSet A (fun _ => V (.above 0)))
    exact traceLam_graph_mem fun A hA => traceLam_graph_mem fun a ha =>
      (chain.closed _).transitive _ hA ha
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (V (.above 0)) (fun A => tracePiSet A (fun a =>
      traceApp (consts holdsN)
        (traceApp (traceApp (consts inN) (traceApp (traceApp (consts elemN) A) a)) A)))
    refine empty_mem_tracePiSet fun A hA => empty_mem_tracePiSet fun a ha => ?_
    rw [reads.holds, reads.in, reads.elem, elemValue_apply hA ha,
      inValue_apply ((chain.closed _).transitive _ hA ha) hA,
      holdsValue_apply (truthCode_mem_truthValues _)]
    exact (mem_truthCode _ _).mpr ⟨rfl, ha⟩
  · show theValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun A =>
      tracePiSet (V (.above 0)) (fun x =>
        tracePiSet (traceApp (consts holdsN) (traceApp (traceApp (consts inN) x) A))
          (fun _ => A)))
    refine traceLam_graph_mem fun A hA => traceLam_graph_mem fun x hx => ?_
    rw [reads.holds, reads.in, inValue_apply hx hA,
      holdsValue_apply (truthCode_mem_truthValues _)]
    exact traceLam_graph_mem fun p hp => ((mem_truthCode _ _).mp hp).2
  · show eqValue (V (.above 1)) ∈ tracePiSet (V (.above 1)) (fun T =>
      tracePiSet T (fun _ => tracePiSet T (fun _ => consts propN)))
    rw [reads.prop]
    exact traceLam_graph_mem fun T _ => traceLam_graph_mem fun a _ =>
      traceLam_graph_mem fun b _ => truthCode_mem_truthValues _
  · show sepValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun _ =>
      tracePiSet (tracePiSet (V (.above 0)) (fun _ => consts propN)) (fun _ => V (.above 0)))
    rw [reads.prop]
    exact traceLam_graph_mem fun A hA => traceLam_graph_mem fun P _ =>
      (chain.closed _).separation_mem hA _
  · show replValue (V (.above 0)) ∈ tracePiSet (V (.above 0)) (fun _ =>
      tracePiSet (tracePiSet (V (.above 0)) (fun _ => V (.above 0))) (fun _ => V (.above 0)))
    exact traceLam_graph_mem fun A hA => traceLam_graph_mem fun F hF =>
      (chain.closed _).replacement_mem hA _ fun x hx =>
        traceApp_mem_fibre hF ((chain.closed _).transitive _ hA hx)
  · show epsValue (V (.above 0)) ∈ tracePiSet
      (tracePiSet (V (.above 0)) (fun _ => consts propN)) (fun _ => V (.above 0))
    rw [reads.prop]
    exact traceLam_graph_mem fun P _ => epsChoice_mem (empty_mem_all chain groundTyped) P

include reads in
/-- The proofs of an implication are the functions between the proofs. -/
theorem holdsImp_valid (η : Env.{u} 2)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc .nil cProp) cProp : CCtx (Head L) 2) η) :
    ev (chainHead V ground ν) consts
        (cHolds (cImp (.var 1) (.var 0)) : CTm (Head L) 2) η =
      ev (chainHead V ground ν) consts
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
/-- **The proofs of a quantification are the dependent functions into the proofs**: both
sides are one truth value, although the function type may be over all sets or over all
predicates on them. -/
theorem holdsAll_valid (η : Env.{u} 2)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc .nil allClasses) (.pi (.var 0) cProp) : CCtx (Head L) 2) η) :
    ev (chainHead V ground ν) consts
        (cHolds (cAll (.var 1) (.var 0)) : CTm (Head L) 2) η =
      ev (chainHead V ground ν) consts
        (.pi (.var 1) (cHolds (.app (.var 1) (.var 0))) : CTm (Head L) 2) η := by
  have hA : η 1 ∈ V (.above 1) := sat 1
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
/-- The proofs of an equality are the proofs of the identity. -/
theorem holdsEq_valid (η : Env.{u} 3)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc (.snoc .nil allClasses) (.var 0)) (.var 1) : CCtx (Head L) 3) η) :
    ev (chainHead V ground ν) consts
        (cHolds (cEq (.var 2) (.var 1) (.var 0)) : CTm (Head L) 3) η =
      ev (chainHead V ground ν) consts (.id (.var 2) (.var 1) (.var 0) : CTm (Head L) 3) η := by
  have hT : η 2 ∈ V (.above 1) := sat 2
  have ha : η 1 ∈ η 2 := sat 1
  have hb : η 0 ∈ η 2 := sat 0
  show traceApp (consts holdsN)
      (traceApp (traceApp (traceApp (consts eqN) (η 2)) (η 1)) (η 0)) = truthCode (η 1 = η 0)
  rw [reads.holds, reads.eq, eqValue_apply hT ha hb,
    holdsValue_apply (truthCode_mem_truthValues _)]

include reads in
/-- A set with a proof of membership, taken as a term and back as a set, is the set. -/
theorem elemThe_valid (η : Env.{u} 3)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc (.snoc .nil allSets) allSets) (cHolds (cIn (.var 0) (.var 1))) :
        CCtx (Head L) 3) η) :
    ev (chainHead V ground ν) consts
        (cElem (.var 2) (cThe (.var 2) (.var 1) (.var 0)) : CTm (Head L) 3) η =
      ev (chainHead V ground ν) consts (.var 1 : CTm (Head L) 3) η := by
  have hA : η 2 ∈ V (.above 0) := sat 2
  have hx : η 1 ∈ V (.above 0) := sat 1
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

include reads chain in
/-- A term of a type, taken as a set and back as a term, is the term. -/
theorem theElem_valid (η : Env.{u} 3)
    (sat : Sat (chainHead V ground ν) consts
      (.snoc (.snoc (.snoc .nil allSets) (.var 0))
        (cHolds (cIn (cElem (.var 1) (.var 0)) (.var 1))) : CCtx (Head L) 3) η) :
    ev (chainHead V ground ν) consts
        (cThe (.var 2) (cElem (.var 2) (.var 1)) (.var 0) : CTm (Head L) 3) η =
      ev (chainHead V ground ν) consts (.var 1 : CTm (Head L) 3) η := by
  have hA : η 2 ∈ V (.above 0) := sat 2
  have ha : η 1 ∈ η 2 := sat 1
  have haAll : η 1 ∈ V (.above 0) := (chain.closed _).transitive _ hA ha
  have hq : η 0 ∈ truthCode (η 1 ∈ η 2) := by
    have member := sat 0
    change η 0 ∈ traceApp (consts holdsN) (traceApp (traceApp (consts inN)
      (traceApp (traceApp (consts elemN) (η 2)) (η 1))) (η 2)) at member
    rwa [reads.holds, reads.in, reads.elem, elemValue_apply hA ha, inValue_apply haAll hA,
      holdsValue_apply (truthCode_mem_truthValues _)] at member
  show traceApp (traceApp (traceApp (consts theN) (η 2))
      (traceApp (traceApp (consts elemN) (η 2)) (η 1))) (η 0) = η 1
  rw [reads.the, reads.elem, elemValue_apply hA ha, theValue_apply hA haAll hq]

include reads chain in
/-- **Every equation holds between sets.** -/
theorem setEquations_valid :
    ∀ e ∈ setEquations L, ∀ η : Env.{u} e.arity,
      Sat (chainHead V ground ν) consts e.telescope η →
        ev (chainHead V ground ν) consts e.left η =
          ev (chainHead V ground ν) consts e.right η := by
  intro e member η sat
  have cases : e = holdsImp L ∨ e = holdsAll L ∨ e = holdsEq L ∨ e = elemThe L ∨
      e = theElem L := by
    simpa [setEquations] using member
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact holdsImp_valid reads η sat
  · exact holdsAll_valid reads η sat
  · exact holdsEq_valid reads η sat
  · exact elemThe_valid reads η sat
  · exact theElem_valid reads chain η sat

omit reads

include chain groundTyped aroundMem in
/-- **The tower inside the sets with the constants of set theory has a set model**, over
every chain of closed universes whose universe of the sets is closed under the operation: the
propositions are the truth values, membership is membership, the operations are those of the
sets, and the two coercions are the identity. The model is at every assignment that gives the
constants of the family their values. -/
theorem setTheory_setModel_of_agreeing (ν : Nat → Above L) (base : DeclName → ZFSet.{u})
    (consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (setTheory L).constantType c ≠ none →
      consts c = familyConsts base (setDecls L)
        (setValues (V (.above 0)) (V (.above 1)) around) c) :
    SetModel (chainHead V ground ν) consts (setTheory L) :=
  family_setModel_of_values (bare L)
    (fun consts _ => chain_setModel chain groundTyped ν consts)
    (fun _ _ => rfl) (setValues (V (.above 0)) (V (.above 1)) around)
    (fun _ _ reads {_ _} declared => setValues_typed reads chain groundTyped aroundMem declared)
    (fun _ _ reads => setEquations_valid reads chain) consts agrees

include chain groundTyped aroundMem in
/-- The model at the assignment that gives the constants of the family their values and reads
every other name as the base assignment does. -/
theorem setTheory_setModel (ν : Nat → Above L) (base : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν)
      (familyConsts base (setDecls L) (setValues (V (.above 0)) (V (.above 1)) around))
      (setTheory L) :=
  setTheory_setModel_of_agreeing chain groundTyped aroundMem ν base _ fun _ _ => rfl

include chain groundTyped aroundMem in
/-- Negative example: **the type of the proofs that the empty set is a member of itself has
no closed term.** -/
theorem no_proof_empty_in_empty (ν : Nat → Above L) (base : DeclName → ZFSet.{u})
    (t : CTm (Head L) 0) : ¬ CTyped (setTheory L) .nil t (cHolds (cIn cEmpty cEmpty)) := by
  have reads : Reads L (V (.above 0)) (V (.above 1)) around
      (familyConsts base (setDecls L) (setValues (V (.above 0)) (V (.above 1)) around)) :=
    fun c declared => familyConsts_declared declared
  refine CDerivable.no_closed_inhabitant
    (setTheory_setModel chain groundTyped aroundMem ν base) (fun z inside => ?_) t
  change z ∈ traceApp
    (familyConsts base (setDecls L) (setValues (V (.above 0)) (V (.above 1)) around) holdsN)
    (traceApp (traceApp
      (familyConsts base (setDecls L) (setValues (V (.above 0)) (V (.above 1)) around) inN)
      (familyConsts base (setDecls L) (setValues (V (.above 0)) (V (.above 1)) around) emptyN))
      (familyConsts base (setDecls L) (setValues (V (.above 0)) (V (.above 1)) around) emptyN))
    at inside
  rw [reads.holds, reads.in, reads.empty,
    inValue_apply (empty_mem_all chain groundTyped) (empty_mem_all chain groundTyped),
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

/-! ## The values of the connectives -/

section Connectives

variable {n : Nat} {heads : Head L → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
  {all classes : ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}}
  (reads : Reads L all classes around consts)

include reads

/-- **The proofs of a proposition**: the value of `holds p` is the truth value of `p`. -/
theorem ev_cHolds {p : CTm (Head L) n} {ρ : Env.{u} n} {P : Prop}
    (hp : ev heads consts p ρ = truthCode P) : ev heads consts (cHolds p) ρ = truthCode P := by
  show traceApp (consts holdsN) (ev heads consts p ρ) = _
  rw [reads.holds, hp]
  exact holdsValue_apply (truthCode_mem_truthValues P)

/-- **Implication**: at the truth values of two statements, the value of `imp p q` is the
truth value of the implication. -/
theorem ev_cImp {p q : CTm (Head L) n} {ρ : Env.{u} n} {P Q : Prop}
    (hp : ev heads consts p ρ = truthCode P) (hq : ev heads consts q ρ = truthCode Q) :
    ev heads consts (cImp p q) ρ = truthCode (P → Q) := by
  show traceApp (traceApp (consts impN) (ev heads consts p ρ)) (ev heads consts q ρ) = _
  rw [reads.imp, hp, hq,
    impValue_apply (truthCode_mem_truthValues P) (truthCode_mem_truthValues Q),
    Controls.tracePiSet_truthCode]
  congr 1
  exact propext ⟨fun h hP => h ∅ ((Square.square_truth_iff P).mpr hP),
    fun h x hx => h ((mem_truthCode _ _).mp hx).2⟩

/-- **Quantification**: over a type of `allClasses`, of a predicate whose values on the type
are the truth values of statements, the value of `all T P` is the truth value of the
universal statement. -/
theorem ev_cAll {T P : CTm (Head L) n} {ρ : Env.{u} n} {Q : ZFSet.{u} → Prop}
    (hT : ev heads consts T ρ ∈ classes)
    (hP : ev heads consts P ρ ∈ tracePiSet (ev heads consts T ρ) fun _ => truthValues)
    (value : ∀ x ∈ ev heads consts T ρ, traceApp (ev heads consts P ρ) x = truthCode (Q x)) :
    ev heads consts (cAll T P) ρ = truthCode (∀ x ∈ ev heads consts T ρ, Q x) := by
  show traceApp (traceApp (consts allN) (ev heads consts T ρ)) (ev heads consts P ρ) = _
  rw [reads.allOver, allValue_apply hT hP, ← Controls.tracePiSet_truthCode]
  exact tracePiSet_congr value

/-- Quantification of an abstraction over the type quantified over. -/
theorem ev_cAll_lam {T : CTm (Head L) n} {body : CTm (Head L) (n + 1)} {ρ : Env.{u} n}
    {Q : ZFSet.{u} → Prop} (hT : ev heads consts T ρ ∈ classes)
    (value : ∀ x ∈ ev heads consts T ρ, ev heads consts body (extend ρ x) = truthCode (Q x)) :
    ev heads consts (cAll T (.lam T body)) ρ = truthCode (∀ x ∈ ev heads consts T ρ, Q x) :=
  ev_cAll reads hT
    (traceLam_graph_mem fun x hx => by
      rw [value x hx]
      exact truthCode_mem_truthValues (Q x))
    fun x hx => (traceApp_graph_beta _ hx).trans (value x hx)

/-- **Equality**: at a type of `allClasses` and two of its terms, the value of `eq T a b` is
the truth value of the equality of their values. -/
theorem ev_cEq {T a b : CTm (Head L) n} {ρ : Env.{u} n} (hT : ev heads consts T ρ ∈ classes)
    (ha : ev heads consts a ρ ∈ ev heads consts T ρ)
    (hb : ev heads consts b ρ ∈ ev heads consts T ρ) :
    ev heads consts (cEq T a b) ρ = truthCode (ev heads consts a ρ = ev heads consts b ρ) := by
  show traceApp (traceApp (traceApp (consts eqN) (ev heads consts T ρ)) (ev heads consts a ρ))
    (ev heads consts b ρ) = _
  rw [reads.eq, eqValue_apply hT ha hb]

/-- **Membership**: at two sets, the value of `In x y` is the truth value of the membership
of their values. -/
theorem ev_cIn {x y : CTm (Head L) n} {ρ : Env.{u} n} (hx : ev heads consts x ρ ∈ all)
    (hy : ev heads consts y ρ ∈ all) :
    ev heads consts (cIn x y) ρ = truthCode (ev heads consts x ρ ∈ ev heads consts y ρ) := by
  show traceApp (traceApp (consts inN) (ev heads consts x ρ)) (ev heads consts y ρ) = _
  rw [reads.in, inValue_apply hx hy]

end Connectives

section FamilyReadings

variable {all classes : ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}}

/-- An assignment that extends the values of the constants of set theory by values for
further names, new to the family, reads the family. -/
theorem reads_familyConsts (base : DeclName → ZFSet.{u})
    {decls : DeclName → Option (CTm (Head L) 0)} (values : DeclName → ZFSet.{u})
    (fresh : ∀ c, decls c ≠ none → setDecls L c = none) :
    Reads L all classes around
      (familyConsts (familyConsts base (setDecls L) (setValues all classes around)) decls
        values) := by
  intro c declared
  have undeclared : decls c = none := by
    cases found : decls c with
    | none => rfl
    | some T => exact absurd (fresh c (by rw [found]; exact Option.some_ne_none T)) declared
  rw [familyConsts_undeclared undeclared, familyConsts_declared declared]

/-- The type of the proofs that the empty set is a member of itself has no member, at every
assignment that reads the family. -/
theorem notMem_holds_empty_in_empty {heads : Head L → ZFSet.{u}} {consts : DeclName → ZFSet.{u}}
    (reads : Reads L all classes around consts) (emptyAll : (∅ : ZFSet.{u}) ∈ all)
    (z : ZFSet.{u}) : z ∉ ev heads consts (cHolds (cIn cEmpty cEmpty)) Fin.elim0 := by
  have empty : ev heads consts (cEmpty : CTm (Head L) 0) Fin.elim0 = ∅ := reads.empty
  have value := ev_cHolds reads
    (ev_cIn reads (heads := heads) (x := cEmpty) (y := cEmpty) (ρ := Fin.elim0)
      (by rw [empty]; exact emptyAll) (by rw [empty]; exact emptyAll))
  rw [value, empty]
  intro inside
  exact ZFSet.notMem_empty _ ((mem_truthCode _ _).mp inside).2

end FamilyReadings

/-! ## The sets of the lower universe -/

section LowerSets

open ZFSetUniverseClosure (CofinalInaccessibles univOf)
open ZFSetUniverseLift (carrierCode univOf_mem_carrierCode)
open ZFSetInterpretation (universeSet)

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} (ν : Nat → Above L)

include small in
/-- **The tower inside the sets with the constants of set theory has a set model**, relative
to cofinally many inaccessible cardinals in two universes: the type of all sets is read as
all the sets of the lower universe, `UnivOf` as the least closed universe around a set. The
model is at every assignment that gives the constants of the family their values. -/
theorem lowerSets_setTheory_setModel_of_agreeing
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base consts : DeclName → ZFSet.{u + 1})
    (agrees : ∀ c, (setTheory L).constantType c ≠ none →
      consts c = familyConsts base (setDecls L)
        (setValues (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
          (univOf large)) c) :
    SetModel (lowerSetsHeads (L := L) large ground ν) consts (setTheory L) :=
  setTheory_setModel_of_agreeing (stages_closedChain small large) groundTyped
    (fun hx => univOf_mem_carrierCode small large hx) ν base consts agrees

include small in
/-- The model at the assignment that gives the constants of the family their values and reads
every other name as the base assignment does. -/
theorem lowerSets_setTheory_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts base (setDecls L)
        (setValues (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
          (univOf large)))
      (setTheory L) :=
  lowerSets_setTheory_setModel_of_agreeing small large ν groundTyped base _ fun _ _ => rfl

include small large in
/-- **Consistency**, relative to cofinally many inaccessible cardinals in two universes: in
the tower inside the sets with the constants of set theory, no closed term proves that the
empty set is a member of itself. -/
theorem setTheory_consistent (t : CTm (Head L) 0) :
    ¬ CTyped (setTheory L) .nil t (cHolds (cIn cEmpty cEmpty)) :=
  no_proof_empty_in_empty (stages_closedChain (L := L) small large)
    (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L))
    (fun hx => univOf_mem_carrierCode small large hx) (fun _ => LevelOrder.bot) (fun _ => ∅) t

/-- **For every set `N`, the power set of `N` is a member of the universe around `N`.** The
proposition quantifies over all sets and nothing in it computes. -/
abbrev powerInUniverse : CTm (Head L) 0 :=
  cAllSets (.lam allSets (cIn (cPower (.var 0)) (cUnivOf (.var 0))))

include small in
/-- Positive example: **`Power N` is a member of `UnivOf N` for every set `N`** is true in the
model: the least closed universe around a set has the power set of the set as a member. -/
theorem powerInUniverse_true (ground : ZFSet.{u + 1}) {consts : DeclName → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      (univOf large) consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (powerInUniverse (L := L))) Fin.elim0 := by
  have chain := stages_closedChain (L := L) small large
  have setsInClasses : stages (L := L) large (.above 0) ∈ stages (L := L) large (.above 1) :=
    chain.mem_of_lt (Above.above_lt_above.mpr Nat.zero_lt_one)
  have body : ∀ x ∈ stages (L := L) large (.above 0),
      traceApp (traceApp (inValue (stages (L := L) large (.above 0)))
          (traceApp (opValue (stages (L := L) large (.above 0)) ZFSet.powerset) x))
          (traceApp (opValue (stages (L := L) large (.above 0)) (univOf large)) x) =
        truthCode (ZFSet.powerset x ∈ univOf large x) := by
    intro x hx
    rw [opValue_apply _ hx, opValue_apply _ hx,
      inValue_apply ((chain.closed _).power_mem hx) (univOf_mem_carrierCode small large hx)]
  have predicate : traceLam (graph (stages (L := L) large (.above 0)) fun x =>
      traceApp (traceApp (inValue (stages (L := L) large (.above 0)))
        (traceApp (opValue (stages (L := L) large (.above 0)) ZFSet.powerset) x))
        (traceApp (opValue (stages (L := L) large (.above 0)) (univOf large)) x)) ∈
      tracePiSet (stages (L := L) large (.above 0)) (fun _ => truthValues) :=
    traceLam_graph_mem fun x hx => by
      rw [body x hx]
      exact truthCode_mem_truthValues _
  show (∅ : ZFSet.{u + 1}) ∈ traceApp (consts holdsN)
    (traceApp (traceApp (consts allN) (stages (L := L) large (.above 0)))
      (traceLam (graph (stages (L := L) large (.above 0)) fun x =>
        traceApp (traceApp (consts inN) (traceApp (consts powerN) x))
          (traceApp (consts univOfN) x))))
  have values : ∀ x ∈ stages (L := L) large (.above 0),
      traceApp (traceLam (graph (stages (L := L) large (.above 0)) fun x =>
        traceApp (traceApp (inValue (stages (L := L) large (.above 0)))
          (traceApp (opValue (stages (L := L) large (.above 0)) ZFSet.powerset) x))
          (traceApp (opValue (stages (L := L) large (.above 0)) (univOf large)) x))) x ∈
        truthValues :=
    fun x hx => traceApp_mem_fibre predicate hx
  have truth : tracePiSet (stages (L := L) large (.above 0)) (fun x =>
      traceApp (traceLam (graph (stages (L := L) large (.above 0)) fun x =>
        traceApp (traceApp (inValue (stages (L := L) large (.above 0)))
          (traceApp (opValue (stages (L := L) large (.above 0)) ZFSet.powerset) x))
          (traceApp (opValue (stages (L := L) large (.above 0)) (univOf large)) x))) x) ∈
      truthValues :=
    tracePiSet_mem_truthValues values
  rw [reads.holds, reads.allOver, reads.in, reads.power, reads.univOf,
    allValue_apply setsInClasses predicate, holdsValue_apply truth]
  refine empty_mem_tracePiSet fun x hx => ?_
  rw [traceApp_graph_beta _ hx, body x hx]
  exact (mem_truthCode _ _).mpr
    ⟨rfl, (ZFSetUniverseClosure.univOf_closed large x).power_mem
      (ZFSetUniverseClosure.mem_univOf large x)⟩

end LowerSets

/-! ## In the judgment -/

section Judgment

/-- A constant of the family is declared in the package as the family declares it. -/
theorem setTheory_declared {c : DeclName} {T : CTm (Head L) 0}
    (declared : setDecls L c = some T) : (setTheory L).constantType c = some T :=
  (withFamily_declared (bare L) rfl).trans declared

/-- The package of the constants of set theory declares a name as the family does. -/
theorem setTheory_constantType (c : DeclName) : (setTheory L).constantType c = setDecls L c :=
  withFamily_declared (bare L) rfl

/-- **A package over the set theory**: it contains the rules of the tower and declares the
constants of the family at their types. The typings of this section hold in every such
package, so they hold where further constants, datatypes and definitions are declared. -/
structure OverSetTheory {R' : Rules (Head L)} (Q : ChurchRules R') : Prop where
  contains : Contains R'
  declared : ∀ {c : DeclName} {T : CTm (Head L) 0}, setDecls L c = some T →
    Q.constantType c = some T

/-- The package of the family is over the set theory. -/
theorem setTheory_over : OverSetTheory (setTheory L) :=
  ⟨package_contains, setTheory_declared⟩

/-- A package that contains the package of the family is over the set theory. -/
theorem OverSetTheory.of_sub {R' : Rules (Head L)} {Q : ChurchRules R'}
    (sub : ChurchRulesSub (setTheory L) Q) : OverSetTheory Q :=
  ⟨⟨sub.headTyping, sub.isUniverse, sub.join, sub.cumulative⟩,
    fun declared => sub.constantType (setTheory_declared declared)⟩

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}
  (covers : OverSetTheory Q)

include covers

/-- The least universe is a set. -/
theorem U0_isSet : CTyped Q Γ U0 allSets :=
  universe_isSet covers.contains _

/-- **The type of propositions is a type of the least universe.** -/
theorem prop_typed : CTyped Q Γ cProp U0 :=
  definition_typed (covers.declared setDecls_prop)
    (.headType (covers.contains.headTyping (.sort _))) (covers.contains.isUniverse (.sort _))

/-- The type of propositions is a set. -/
theorem prop_isSet : CTyped Q Γ cProp allSets :=
  small_isSet covers.contains (prop_typed covers)

/-- `holds` takes a proposition to a type of the least universe. -/
theorem holds_typed : CTyped Q Γ (.const holdsN) holdsType :=
  definition_typed (covers.declared setDecls_holds)
    (family_isSet covers.contains (prop_isSet covers) (U0_isSet covers))
    (covers.contains.isUniverse (.sort _))

/-- The proofs of a proposition form a type of the least universe. -/
theorem cHolds_typed {p : CTm (Head L) n} (hp : CTyped Q Γ p cProp) :
    CTyped Q Γ (cHolds p) U0 :=
  .appElim (B := U0) (holds_typed covers) hp

/-- The proofs of a proposition form a set. -/
theorem cHolds_isSet {p : CTm (Head L) n} (hp : CTyped Q Γ p cProp) :
    CTyped Q Γ (cHolds p) allSets :=
  small_isSet covers.contains (cHolds_typed covers hp)

/-- Implication takes two propositions to a proposition. -/
theorem imp_typed : CTyped Q Γ (.const impN) impType :=
  definition_typed (covers.declared setDecls_imp)
    (family_isSet covers.contains (prop_isSet covers)
      (family_isSet covers.contains (prop_isSet covers) (prop_isSet covers)))
    (covers.contains.isUniverse (.sort _))

/-- The implication of two propositions is a proposition. -/
theorem cImp_typed {p q : CTm (Head L) n} (hp : CTyped Q Γ p cProp) (hq : CTyped Q Γ q cProp) :
    CTyped Q Γ (cImp p q) cProp :=
  .appElim (B := cProp) (.appElim (B := .pi cProp cProp) (imp_typed covers) hp) hq

/-- The type of propositions is a type of `allClasses`. -/
theorem prop_isClass : CTyped Q Γ cProp allClasses :=
  set_isClass covers.contains (prop_isSet covers)

/-- The type of the quantifier is formed, one universe above `allClasses`. -/
theorem allType_formed :
    CTyped Q Γ allType
      (.head (.sort (.max (.succ (.const (.above 1))) (.const (.above 1))))) :=
  .piForm (.headType (covers.contains.headTyping (.sort _))) (covers.contains.isUniverse (.sort _))
    (classToClass_typed covers.contains
      (classToClass_typed covers.contains (.var 0) (prop_isClass covers)) (prop_isClass covers))
    (covers.contains.isUniverse (.sort _)) (covers.contains.join (.sorts _ _))

/-- **The quantifier takes a type of `allClasses` and a predicate on it to a proposition.** -/
theorem all_typed : CTyped Q Γ (.const allN) allType :=
  definition_typed (covers.declared setDecls_all) (allType_formed covers)
    (covers.contains.isUniverse (.sort _))

/-- A quantification over a type of `allClasses` is a proposition. -/
theorem cAll_typed {T P : CTm (Head L) n} (hT : CTyped Q Γ T allClasses)
    (hP : CTyped Q Γ P (.pi T cProp)) : CTyped Q Γ (cAll T P) cProp :=
  .appElim (B := cProp)
    (.appElim (B := .pi (.pi (.var 0) cProp) cProp) (all_typed covers) hT) hP

/-- Positive example: **a statement about all sets is a proposition.** -/
theorem cAllSets_typed {P : CTm (Head L) n} (hP : CTyped Q Γ P (.pi allSets cProp)) :
    CTyped Q Γ (cAllSets P) cProp :=
  cAll_typed covers (sets_typed covers.contains) hP

/-- The type of `eq` is formed, one universe above `allClasses`. -/
theorem eqType_formed :
    CTyped Q Γ eqType
      (.head (.sort (.max (.succ (.const (.above 1))) (.const (.above 1))))) :=
  .piForm (.headType (covers.contains.headTyping (.sort _))) (covers.contains.isUniverse (.sort _))
    (classToClass_typed covers.contains (.var 0)
      (classToClass_typed covers.contains (.var 1) (prop_isClass covers)))
    (covers.contains.isUniverse (.sort _)) (covers.contains.join (.sorts _ _))

/-- `eq` has its type. -/
theorem eq_typed : CTyped Q Γ (.const eqN) eqType :=
  definition_typed (covers.declared setDecls_eq) (eqType_formed covers)
    (covers.contains.isUniverse (.sort _))

/-- **The equality of two terms of a type of `allClasses` is a proposition.** -/
theorem cEq_typed {T a b : CTm (Head L) n} (hT : CTyped Q Γ T allClasses)
    (ha : CTyped Q Γ a T) (hb : CTyped Q Γ b T) : CTyped Q Γ (cEq T a b) cProp := by
  have first : CTyped Q Γ (.app (.const eqN) T) (.pi T (.pi (T.rename Fin.succ) cProp)) :=
    .appElim (B := .pi (.var 0) (.pi (.var 1) cProp)) (eq_typed covers) hT
  have second := CDerivable.appElim first ha
  have back : CTm.inst0 a (CTm.rename Fin.succ T) = T := CTm.inst0_rename_wk a T
  have same : CTm.inst0 a (.pi (T.rename Fin.succ) cProp) = .pi T cProp := by
    show CTm.pi (CTm.inst0 a (CTm.rename Fin.succ T)) cProp = _
    rw [back]
  rw [same] at second
  exact .appElim (B := cProp) second hb

/-- **Membership takes two sets to a proposition.** -/
theorem in_typed : CTyped Q Γ (.const inN) inType :=
  definition_typed (covers.declared setDecls_in)
    (classToClass_typed covers.contains (sets_typed covers.contains)
      (classToSet_typed covers.contains (sets_typed covers.contains) (prop_isSet covers)))
    (covers.contains.isUniverse (.sort _))

/-- The membership of two sets is a proposition. -/
theorem cIn_typed {x y : CTm (Head L) n} (hx : CTyped Q Γ x allSets)
    (hy : CTyped Q Γ y allSets) : CTyped Q Γ (cIn x y) cProp :=
  .appElim (B := cProp) (.appElim (B := .pi allSets cProp) (in_typed covers) hx) hy

/-- The empty set is a set. -/
theorem empty_typed : CTyped Q Γ cEmpty allSets :=
  definition_typed (covers.declared setDecls_empty) (sets_typed covers.contains)
    (covers.contains.isUniverse (.sort _))

/-- The union is an operation on the sets. -/
theorem union_typed : CTyped Q Γ (.const unionN) opType :=
  definition_typed (covers.declared setDecls_union) (setFunctions_typed covers.contains)
    (covers.contains.isUniverse (.sort _))

/-- The power set is an operation on the sets. -/
theorem power_typed : CTyped Q Γ (.const powerN) opType :=
  definition_typed (covers.declared setDecls_power) (setFunctions_typed covers.contains)
    (covers.contains.isUniverse (.sort _))

/-- The universe around a set is an operation on the sets. -/
theorem univOf_typed : CTyped Q Γ (.const univOfN) opType :=
  definition_typed (covers.declared setDecls_univOf) (setFunctions_typed covers.contains)
    (covers.contains.isUniverse (.sort _))

/-- The type of `Sep` is a type of `allClasses`. -/
theorem sepType_formed : CTyped Q Γ sepType allClasses :=
  classToClass_typed covers.contains (sets_typed covers.contains)
    (classToClass_typed covers.contains
      (classToSet_typed covers.contains (sets_typed covers.contains) (prop_isSet covers))
      (sets_typed covers.contains))

/-- `Sep` has its type. -/
theorem sep_typed : CTyped Q Γ (.const sepN) sepType :=
  definition_typed (covers.declared setDecls_sep) (sepType_formed covers)
    (covers.contains.isUniverse (.sort _))

/-- **The subset of a set given by a predicate on the sets is a set.** -/
theorem cSep_typed {A P : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hP : CTyped Q Γ P (.pi allSets cProp)) : CTyped Q Γ (cSep A P) allSets :=
  .appElim (B := allSets)
    (.appElim (B := .pi (.pi allSets cProp) allSets) (sep_typed covers) hA) hP

/-- The type of `Repl` is a type of `allClasses`. -/
theorem replType_formed : CTyped Q Γ replType allClasses :=
  classToClass_typed covers.contains (sets_typed covers.contains)
    (classToClass_typed covers.contains (setFunctions_typed covers.contains)
      (sets_typed covers.contains))

/-- `Repl` has its type. -/
theorem repl_typed : CTyped Q Γ (.const replN) replType :=
  definition_typed (covers.declared setDecls_repl) (replType_formed covers)
    (covers.contains.isUniverse (.sort _))

/-- **The image of a set under a function on the sets is a set.** -/
theorem cRepl_typed {A F : CTm (Head L) n} (hA : CTyped Q Γ A allSets)
    (hF : CTyped Q Γ F (.pi allSets allSets)) : CTyped Q Γ (cRepl A F) allSets :=
  .appElim (B := allSets)
    (.appElim (B := .pi (.pi allSets allSets) allSets) (repl_typed covers) hA) hF

/-- The type of `Eps` is a type of `allClasses`. -/
theorem epsType_formed : CTyped Q Γ epsType allClasses :=
  classToClass_typed covers.contains
    (classToSet_typed covers.contains (sets_typed covers.contains) (prop_isSet covers))
    (sets_typed covers.contains)

/-- `Eps` has its type. -/
theorem eps_typed : CTyped Q Γ (.const epsN) epsType :=
  definition_typed (covers.declared setDecls_eps) (epsType_formed covers)
    (covers.contains.isUniverse (.sort _))

/-- **The set chosen for a predicate on the sets is a set.** -/
theorem cEps_typed {P : CTm (Head L) n} (hP : CTyped Q Γ P (.pi allSets cProp)) :
    CTyped Q Γ (cEps P) allSets :=
  .appElim (B := allSets) (eps_typed covers) hP

/-- Positive example: `Power Empty` is a set. -/
theorem powerEmpty_typed : CTyped Q Γ (cPower cEmpty) allSets :=
  .appElim (B := allSets) (power_typed covers) (empty_typed covers)

/-- The type of `elem` is a type of `allClasses`. -/
theorem elemType_formed : CTyped Q Γ elemType allClasses :=
  classToClass_typed covers.contains (sets_typed covers.contains)
    (setToClass_typed covers.contains (.var 0) (sets_typed covers.contains))

/-- `elem` has its type. -/
theorem elemConst_typed : CTyped Q Γ (.const elemN) elemType :=
  definition_typed (covers.declared setDecls_elem) (elemType_formed covers)
    (covers.contains.isUniverse (.sort _))

/-- **A term of a type that is a set is a set.** -/
theorem elem_typed {A a : CTm (Head L) n} (hA : CTyped Q Γ A allSets) (ha : CTyped Q Γ a A) :
    CTyped Q Γ (cElem A a) allSets :=
  .appElim (B := allSets) (.appElim (B := .pi (.var 0) allSets) (elemConst_typed covers) hA) ha

/-- The type of `member` is a type of `allClasses`. -/
theorem memberType_formed : CTyped Q Γ memberType allClasses :=
  classToSet_typed covers.contains (sets_typed covers.contains)
    (family_isSet covers.contains (.var 0)
      (cHolds_isSet covers (cIn_typed covers (elem_typed covers (.var 1) (.var 0)) (.var 1))))

/-- `member` has its type. -/
theorem memberConst_typed : CTyped Q Γ (.const memberN) memberType :=
  definition_typed (covers.declared setDecls_member) (memberType_formed covers)
    (covers.contains.isUniverse (.sort _))

/-- **Typing gives membership**: a term of a type that is a set has a proof that, as a set,
it is a member of the type. -/
theorem member_typed {A a : CTm (Head L) n} (hA : CTyped Q Γ A allSets) (ha : CTyped Q Γ a A) :
    CTyped Q Γ (cMember A a) (cHolds (cIn (cElem A a) A)) := by
  have first : CTyped Q Γ (.app (.const memberN) A)
      (.pi A (cHolds (cIn (cElem (A.rename Fin.succ) (.var 0)) (A.rename Fin.succ)))) :=
    .appElim (B := .pi (.var 0) (cHolds (cIn (cElem (.var 1) (.var 0)) (.var 1))))
      (memberConst_typed covers) hA
  have second := CDerivable.appElim first ha
  have back : CTm.inst0 a (CTm.rename Fin.succ A) = A := CTm.inst0_rename_wk a A
  have same : CTm.inst0 a (cHolds (cIn (cElem (A.rename Fin.succ) (.var 0)) (A.rename Fin.succ))) =
      cHolds (cIn (cElem A a) A) := by
    show cHolds (cIn (cElem (CTm.inst0 a (CTm.rename Fin.succ A)) a)
      (CTm.inst0 a (CTm.rename Fin.succ A))) = _
    rw [back]
  rw [same] at second
  exact second

/-- The type of `the` is a type of `allClasses`. -/
theorem theType_formed : CTyped Q Γ theType allClasses :=
  classToClass_typed covers.contains (sets_typed covers.contains)
    (classToSet_typed covers.contains (sets_typed covers.contains)
      (family_isSet covers.contains (cHolds_isSet covers (cIn_typed covers (.var 0) (.var 1)))
        (.var 2)))

/-- `the` has its type. -/
theorem theConst_typed : CTyped Q Γ (.const theN) theType :=
  definition_typed (covers.declared setDecls_the) (theType_formed covers)
    (covers.contains.isUniverse (.sort _))

/-- Positive example: **the universe at a level, as a set, is a member of the universe at the
next level**, with a proof term. -/
theorem universe_member (d : L) :
    CTyped Q Γ (cMember (universeAt (LevelOrder.succ d)) (universeAt d))
      (cHolds (cIn (cElem (universeAt (LevelOrder.succ d)) (universeAt d))
        (universeAt (LevelOrder.succ d)))) :=
  member_typed covers (universe_isSet covers.contains _) (universe_typed covers.contains d)

/-- Positive example: the statement that the power set of every set is a member of the
universe around the set is a proposition. -/
theorem powerInUniverse_typed : CTyped Q .nil (powerInUniverse (L := L)) cProp :=
  cAllSets_typed covers
    (.lamIntro (sets_typed covers.contains) (covers.contains.isUniverse (.sort _))
      (classToSet_typed covers.contains (sets_typed covers.contains) (prop_isSet covers))
      (covers.contains.isUniverse (.sort _))
      (cIn_typed covers (.appElim (B := allSets) (power_typed covers) (.var 0))
        (.appElim (B := allSets) (univOf_typed covers) (.var 0))))

/-! ## Equal propositions -/

/-- **The proofs of equal propositions are equal types.** -/
theorem cHolds_congr {p q : CTm (Head L) n} (equal : CEqual Q Γ p q cProp) :
    CEqual Q Γ (cHolds p) (cHolds q) U0 :=
  .appCong (B := U0) (.refl (holds_typed covers)) equal

/-- Implications of equal propositions are equal. -/
theorem cImp_congr {p p' q q' : CTm (Head L) n} (hp : CEqual Q Γ p p' cProp)
    (hq : CEqual Q Γ q q' cProp) : CEqual Q Γ (cImp p q) (cImp p' q') cProp :=
  .appCong (B := cProp) (.appCong (B := .pi cProp cProp) (.refl (imp_typed covers)) hp) hq

/-- Quantifications of equal predicates are equal. -/
theorem cAll_congr {T P P' : CTm (Head L) n} (hT : CTyped Q Γ T allClasses)
    (hP : CEqual Q Γ P P' (.pi T cProp)) : CEqual Q Γ (cAll T P) (cAll T P') cProp :=
  .appCong (B := cProp)
    (.refl (.appElim (B := .pi (.pi (.var 0) cProp) cProp) (all_typed covers) hT)) hP

/-- Abstractions of equal propositions are equal predicates. -/
theorem predicate_congr {T : CTm (Head L) n} {body body' : CTm (Head L) (n + 1)}
    (hT : CTyped Q Γ T allClasses) (equal : CEqual Q (.snoc Γ T) body body' cProp) :
    CEqual Q Γ (.lam T body) (.lam T body') (.pi T cProp) :=
  .lamCong (.refl hT) (covers.contains.isUniverse (.sort _))
    (classToClass_typed covers.contains hT (prop_isClass covers))
    (covers.contains.isUniverse (.sort _)) equal

/-- Quantifications of equal propositions are equal. -/
theorem cAll_lam_congr {T : CTm (Head L) n} {body body' : CTm (Head L) (n + 1)}
    (hT : CTyped Q Γ T allClasses) (equal : CEqual Q (.snoc Γ T) body body' cProp) :
    CEqual Q Γ (cAll T (.lam T body)) (cAll T (.lam T body')) cProp :=
  cAll_congr covers hT (predicate_congr covers hT equal)

/-- Equalities of equal terms are equal propositions. -/
theorem cEq_congr {T a a' b b' : CTm (Head L) n} (hT : CTyped Q Γ T allClasses)
    (ha : CEqual Q Γ a a' T) (hb : CEqual Q Γ b b' T) :
    CEqual Q Γ (cEq T a b) (cEq T a' b') cProp := by
  have first : CTyped Q Γ (.app (.const eqN) T) (.pi T (.pi (T.rename Fin.succ) cProp)) :=
    .appElim (B := .pi (.var 0) (.pi (.var 1) cProp)) (eq_typed covers) hT
  have second := CDerivable.appCong (.refl first) ha
  have back : CTm.inst0 a (CTm.rename Fin.succ T) = T := CTm.inst0_rename_wk a T
  have same : CTm.inst0 a (.pi (T.rename Fin.succ) cProp) = .pi T cProp := by
    show CTm.pi (CTm.inst0 a (CTm.rename Fin.succ T)) cProp = _
    rw [back]
  rw [same] at second
  exact .appCong (B := cProp) second hb

/-- **A predicate given by an abstraction, applied to the newest variable, is its body.** -/
theorem predicate_apply_var {T : CTm (Head L) n} {body : CTm (Head L) (n + 1)}
    (hT : CTyped Q Γ T allClasses) (hbody : CTyped Q (.snoc Γ T) body cProp) :
    CEqual Q (.snoc Γ T) (.app ((CTm.lam T body).rename wk) (.var 0)) body cProp := by
  have domain : CTyped Q (.snoc Γ T) (T.rename wk) allClasses := hT.weaken (E := T)
  have step := CDerivable.betaPi (B := cProp)
    (classToClass_typed covers.contains domain (prop_isClass covers))
    (covers.contains.isUniverse (.sort _)) (hbody.rename ((CCtxRen.wk Γ T).snoc T))
    (CDerivable.var (P := Q) (Γ := .snoc Γ T) 0)
  rw [CTm.inst0_var_rename_liftRen_wk] at step
  exact step

/-! ## The proofs of an implication and of a quantification -/

section Equations

variable (computes : StepsWithin (familyChurch (rules L) (setDecls L) (setEquations L)) Q)

include computes

/-- **The proofs of an implication are the functions between the proofs**, in every package
over the set theory that contains the steps of its equations. -/
theorem holds_imp_rule {p q : CTm (Head L) n} (hp : CTyped Q Γ p cProp)
    (hq : CTyped Q Γ q cProp) :
    CEqual Q Γ (cHolds (cImp p q)) (.pi (cHolds p) (cHolds (q.rename wk))) U0 :=
  have typed : CSubstMor Q (holdsImp L).telescope Γ
      (fun j : Fin 2 => match j with
        | ⟨0, _⟩ => q
        | ⟨1, _⟩ => p) :=
    fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => hp
  family_equation_holds (rules L) computes List.mem_cons_self _ typed
    (cHolds_typed covers (cImp_typed covers hp hq))
    (smallFunctions_typed covers.contains (cHolds_typed covers hp)
      (cHolds_typed covers (hq.weaken (E := cHolds p))))

/-- **The proofs of a quantification are the dependent functions into the proofs**, at a
type of `allClasses` and a predicate on it. -/
theorem holds_all_rule {T P : CTm (Head L) n} (hT : CTyped Q Γ T allClasses)
    (hP : CTyped Q Γ P (.pi T cProp)) :
    CEqual Q Γ (cHolds (cAll T P)) (.pi T (cHolds (.app (P.rename wk) (.var 0)))) allClasses :=
  have typed : CSubstMor Q (holdsAll L).telescope Γ
      (fun j : Fin 2 => match j with
        | ⟨0, _⟩ => P
        | ⟨1, _⟩ => T) :=
    fun j => match j with
      | ⟨0, _⟩ => hP
      | ⟨1, _⟩ => hT
  family_equation_holds (rules L) computes (List.mem_cons_of_mem _ List.mem_cons_self) _ typed
    (set_isClass covers.contains (cHolds_isSet covers (cAll_typed covers hT hP)))
    (classToSet_typed covers.contains hT
      (cHolds_isSet covers (.appElim (B := cProp) (hP.weaken (E := T)) (.var 0))))

/-- **The proofs of a quantification of an abstraction are the dependent functions into the
proofs of its body.** -/
theorem holds_all_lam_rule {T : CTm (Head L) n} {body : CTm (Head L) (n + 1)}
    (hT : CTyped Q Γ T allClasses) (hbody : CTyped Q (.snoc Γ T) body cProp) :
    CEqual Q Γ (cHolds (cAll T (.lam T body))) (.pi T (cHolds body)) allClasses := by
  have predicate : CTyped Q Γ (.lam T body) (.pi T cProp) :=
    .lamIntro hT (covers.contains.isUniverse (.sort _))
      (classToClass_typed covers.contains hT (prop_isClass covers))
      (covers.contains.isUniverse (.sort _)) hbody
  have first := holds_all_rule covers computes hT predicate
  have inner : CEqual Q (.snoc Γ T) (cHolds (.app ((CTm.lam T body).rename wk) (.var 0)))
      (cHolds body) allSets :=
    CDerivable.cumulEq (cHolds_congr covers (predicate_apply_var covers hT hbody))
      (covers.contains.cumulative (u := .sort (.const (.below LevelOrder.bot)))
        (v := .sort (.const (.above 0))) fun _ => Above.below_le_above _ 0)
  have second : CEqual Q Γ (.pi T (cHolds (.app ((CTm.lam T body).rename wk) (.var 0))))
      (.pi T (cHolds body)) allClasses :=
    CDerivable.cumulEq
      (.piCong (.refl hT) (covers.contains.isUniverse (.sort _)) inner
        (covers.contains.isUniverse (.sort _)) (covers.contains.join (.sorts _ _)))
      (covers.contains.cumulative
        (u := .sort (.max (.const (.above 1)) (.const (.above 0))))
        (v := .sort (.const (.above 1)))
        fun _ => max_le (le_refl _) (Above.above_le_above.mpr (Nat.zero_le 1)))
  exact .trans first second

end Equations

end Judgment

/-! ## The set theory on rule constants

The same declarations, no equation, and a constant for each rule of the logic: the
introduction and the elimination of implication, of the quantifier and of equality, and the
two laws of `elem` and `the` as proofs of identities. A proof is built from these constants;
`holds p` never unfolds.
-/

/-- The introduction of an implication. -/
def impIN : DeclName := .str .anonymous "impI"
/-- The elimination of an implication. -/
def impEN : DeclName := .str .anonymous "impE"
/-- The introduction of a quantification. -/
def allIN : DeclName := .str .anonymous "allI"
/-- The elimination of a quantification. -/
def allEN : DeclName := .str .anonymous "allE"
/-- The introduction of an equality. -/
def eqIN : DeclName := .str .anonymous "eqI"
/-- The elimination of an equality. -/
def eqEN : DeclName := .str .anonymous "eqE"
/-- A set with a proof of membership, as a term and back as a set, is the set. -/
def elemTheLawN : DeclName := .str .anonymous "elemTheLaw"
/-- A term, as a set and back as a term, is the term. -/
def theElemLawN : DeclName := .str .anonymous "theElemLaw"

section RuleTerms

variable {n : Nat}

/-- `impI p q f`. -/
abbrev cImpI (p q f : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const impIN) p) q) f

/-- `impE p q h a`. -/
abbrev cImpE (p q h a : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.app (.const impEN) p) q) h) a

/-- `allI T P f`. -/
abbrev cAllI (T P f : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const allIN) T) P) f

/-- `allE T P h x`. -/
abbrev cAllE (T P h x : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.app (.const allEN) T) P) h) x

/-- `eqI T a b e`. -/
abbrev cEqI (T a b e : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.app (.const eqIN) T) a) b) e

/-- `eqE T a b h`. -/
abbrev cEqE (T a b h : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.app (.const eqEN) T) a) b) h

/-- `elemTheLaw A x p`. -/
abbrev cElemTheLaw (A x p : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const elemTheLawN) A) x) p

/-- `theElemLaw A a q`. -/
abbrev cTheElemLaw (A a q : CTm (Head L) n) : CTm (Head L) n :=
  .app (.app (.app (.const theElemLawN) A) a) q

/-- `Π (p q : prop). (holds p → holds q) → holds (imp p q)`. -/
abbrev impIType : CTm (Head L) n :=
  .pi cProp (.pi cProp
    (.pi (.pi (cHolds (.var 1)) (cHolds (.var 1))) (cHolds (cImp (.var 2) (.var 1)))))

/-- `Π (p q : prop). holds (imp p q) → holds p → holds q`. -/
abbrev impEType : CTm (Head L) n :=
  .pi cProp (.pi cProp
    (.pi (cHolds (cImp (.var 1) (.var 0))) (.pi (cHolds (.var 2)) (cHolds (.var 2)))))

/-- `Π (T : class). Π (P : T → prop). (Π (x : T). holds (P x)) → holds (all T P)`. -/
abbrev allIType : CTm (Head L) n :=
  .pi allClasses (.pi (.pi (.var 0) cProp)
    (.pi (.pi (.var 1) (cHolds (.app (.var 1) (.var 0)))) (cHolds (cAll (.var 2) (.var 1)))))

/-- `Π (T : class). Π (P : T → prop). holds (all T P) → Π (x : T). holds (P x)`. -/
abbrev allEType : CTm (Head L) n :=
  .pi allClasses (.pi (.pi (.var 0) cProp)
    (.pi (cHolds (cAll (.var 1) (.var 0))) (.pi (.var 2) (cHolds (.app (.var 2) (.var 0))))))

/-- `Π (T : class). Π (a b : T). Id T a b → holds (eq T a b)`. -/
abbrev eqIType : CTm (Head L) n :=
  .pi allClasses (.pi (.var 0) (.pi (.var 1)
    (.pi (.id (.var 2) (.var 1) (.var 0)) (cHolds (cEq (.var 3) (.var 2) (.var 1))))))

/-- `Π (T : class). Π (a b : T). holds (eq T a b) → Id T a b`. -/
abbrev eqEType : CTm (Head L) n :=
  .pi allClasses (.pi (.var 0) (.pi (.var 1)
    (.pi (cHolds (cEq (.var 2) (.var 1) (.var 0))) (.id (.var 3) (.var 2) (.var 1)))))

/-- `Π (A x : set). Π (p : holds (In x A)). Id set (elem A (the A x p)) x`. -/
abbrev elemTheLawType : CTm (Head L) n :=
  .pi allSets (.pi allSets (.pi (cHolds (cIn (.var 0) (.var 1)))
    (.id allSets (cElem (.var 2) (cThe (.var 2) (.var 1) (.var 0))) (.var 1))))

/-- `Π (A : set). Π (a : A). Π (q : holds (In (elem A a) A)). Id A (the A (elem A a) q) a`. -/
abbrev theElemLawType : CTm (Head L) n :=
  .pi allSets (.pi (.var 0) (.pi (cHolds (cIn (cElem (.var 1) (.var 0)) (.var 1)))
    (.id (.var 2) (cThe (.var 2) (cElem (.var 2) (.var 1)) (.var 0)) (.var 1))))

end RuleTerms

variable (L) in
/-- **The table of the rule constants**: each with its type. -/
def ruleTable : List (DeclName × CTm (Head L) 0) :=
  [(impIN, impIType), (impEN, impEType), (allIN, allIType), (allEN, allEType),
    (eqIN, eqIType), (eqEN, eqEType), (elemTheLawN, elemTheLawType),
    (theElemLawN, theElemLawType)]

variable (L) in
/-- The declarations of the rule constants. -/
def ruleDecls : DeclName → Option (CTm (Head L) 0) := tableLookup (ruleTable L)

variable (L) in
/-- The constants of set theory, the rule constants and further rows, in this order. -/
def rulesTable (extra : List (DeclName × CTm (Head L) 0)) : List (DeclName × CTm (Head L) 0) :=
  setTable L ++ ruleTable L ++ extra

variable (L) in
/-- **The tower inside the sets with the constants of set theory, the rule constants and
further declared constants**, and no equation. -/
abbrev withRules (extra : List (DeclName × CTm (Head L) 0)) :=
  withConstants L (tableLookup (rulesTable L extra))

variable (L) in
/-- **The set theory on rule constants**: the constants of set theory and the rule constants,
and no equation. -/
abbrev setTheoryRules := withRules L []

/-! ### Tables -/

/-- A name the constants of set theory do not declare has the empty set as its value. -/
theorem setValues_undeclared (all classes : ZFSet.{u}) (around : ZFSet.{u} → ZFSet.{u})
    {c : DeclName} (undeclared : setDecls L c = none) : setValues all classes around c = ∅ := by
  have missing : tableLookup (setValueTable all classes around) c = none :=
    tableLookup_eq_none_of_names (first := setTable L)
      (second := setValueTable all classes around) rfl undeclared
  unfold setValues
  rw [missing]
  rfl

/-- The names of the rule constants are new to the constants of set theory. -/
theorem ruleDecls_new {c : DeclName} {T : CTm (Head L) 0} (declared : ruleDecls L c = some T) :
    setDecls L c = none := by
  have row := tableLookup_mem declared
  simp only [ruleTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- A constant of set theory is declared in the table with the rules as the family declares
it. -/
theorem rulesTable_set {extra : List (DeclName × CTm (Head L) 0)} {c : DeclName}
    {T : CTm (Head L) 0} (declared : setDecls L c = some T) :
    tableLookup (rulesTable L extra) c = some T := by
  unfold rulesTable
  rw [tableLookup_append, tableLookup_append]
  have known : tableLookup (setTable L) c = some T := declared
  rw [known]
  rfl

/-- A rule constant is declared in the table with the rules at its type. -/
theorem rulesTable_rule {extra : List (DeclName × CTm (Head L) 0)} {c : DeclName}
    {T : CTm (Head L) 0} (declared : ruleDecls L c = some T) :
    tableLookup (rulesTable L extra) c = some T := by
  unfold rulesTable
  rw [tableLookup_append, tableLookup_append]
  have missing : tableLookup (setTable L) c = none := ruleDecls_new declared
  have known : tableLookup (ruleTable L) c = some T := declared
  rw [missing, known]
  rfl

/-- What the table with the rules declares is a constant of set theory, a rule constant, or a
further row. -/
theorem rulesTable_cases {extra : List (DeclName × CTm (Head L) 0)} {c : DeclName}
    {T : CTm (Head L) 0} (declared : tableLookup (rulesTable L extra) c = some T) :
    setDecls L c = some T ∨ (setDecls L c = none ∧ ruleDecls L c = some T) ∨
      (setDecls L c = none ∧ ruleDecls L c = none ∧ (c, T) ∈ extra) := by
  unfold rulesTable at declared
  rw [tableLookup_append, tableLookup_append] at declared
  cases first : tableLookup (setTable L) c with
  | some T' =>
    rw [first] at declared
    exact Or.inl (first.trans declared)
  | none =>
    rw [first] at declared
    cases second : tableLookup (ruleTable L) c with
    | some T' =>
      rw [second] at declared
      exact Or.inr (Or.inl ⟨first, second.trans declared⟩)
    | none =>
      rw [second] at declared
      exact Or.inr (Or.inr ⟨first, second, tableLookup_mem declared⟩)

/-- **A package over the set theory with the rule constants**: over the set theory, and it
declares the rule constants at their types. -/
structure OverSetTheoryRules {R' : Rules (Head L)} (Q : ChurchRules R') : Prop where
  sets : OverSetTheory Q
  declared : ∀ {c : DeclName} {T : CTm (Head L) 0}, ruleDecls L c = some T →
    Q.constantType c = some T

/-- A constant of the table with the rules is declared in its package as the table declares
it. -/
theorem withRules_declared {extra : List (DeclName × CTm (Head L) 0)} {c : DeclName} :
    (withRules L extra).constantType c = tableLookup (rulesTable L extra) c :=
  withFamily_declared (bare L) rfl

/-- The package with the rules is over the set theory with the rule constants. -/
theorem withRules_over (extra : List (DeclName × CTm (Head L) 0)) :
    OverSetTheoryRules (withRules L extra) where
  sets := ⟨package_contains, fun declared => withRules_declared.trans (rulesTable_set declared)⟩
  declared := fun declared => withRules_declared.trans (rulesTable_rule declared)

/-- The set theory on rule constants is over the set theory with the rule constants. -/
theorem setTheoryRules_over : OverSetTheoryRules (setTheoryRules L) := withRules_over []

section HoldsClass

variable {R' : Rules (Head L)} {Q : ChurchRules R'} {n : Nat} {Γ : CCtx (Head L) n}
  (covers : OverSetTheoryRules Q)

include covers

/-- The proofs of a proposition form a type of `allClasses`. -/
theorem cHolds_isClass {p : CTm (Head L) n} (hp : CTyped Q Γ p cProp) :
    CTyped Q Γ (cHolds p) allClasses :=
  set_isClass covers.sets.contains (cHolds_isSet covers.sets hp)

end HoldsClass

/-! ### The set model of the rule constants -/

section RulesModel

/-- A truth value with a member is the true truth value: it has the empty set as a member. -/
theorem empty_mem_of_mem_truthValue {p z : ZFSet.{u}} (hp : p ∈ truthValues) (hz : z ∈ p) :
    (∅ : ZFSet.{u}) ∈ p := by
  have inside : z ∈ ({∅} : ZFSet.{u}) := ZFSet.mem_powerset.mp hp hz
  rw [ZFSet.mem_singleton.mp inside] at hz
  exact hz

variable {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
  {ν : Nat → Above L} {consts : DeclName → ZFSet.{u}}
  (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) (chain : ClosedChain V)

include reads chain in
/-- **Every rule constant is a proof**: the empty set is a member of the value of its type.
The conclusion of each rule is true whenever the types of its premises have members. -/
theorem ruleTable_typed {c : DeclName} {T : CTm (Head L) 0} (row : (c, T) ∈ ruleTable L) :
    (∅ : ZFSet.{u}) ∈ ev (chainHead V ground ν) consts T Fin.elim0 := by
  simp only [ruleTable, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (consts propN) (fun p => tracePiSet (consts propN) (fun q =>
      tracePiSet (tracePiSet (traceApp (consts holdsN) p) (fun _ => traceApp (consts holdsN) q))
        (fun _ => traceApp (consts holdsN) (traceApp (traceApp (consts impN) p) q))))
    rw [reads.prop]
    refine empty_mem_tracePiSet fun p hp => empty_mem_tracePiSet fun q hq =>
      empty_mem_tracePiSet fun f hf => ?_
    have truth : (tracePiSet p fun _ => q) ∈ truthValues := tracePiSet_mem_truthValues fun _ _ => hq
    rw [reads.holds, holdsValue_apply hp, holdsValue_apply hq] at hf
    rw [reads.holds, reads.imp, impValue_apply hp hq, holdsValue_apply truth]
    exact empty_mem_of_mem_truthValue truth hf
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (consts propN) (fun p => tracePiSet (consts propN) (fun q =>
      tracePiSet (traceApp (consts holdsN) (traceApp (traceApp (consts impN) p) q))
        (fun _ => tracePiSet (traceApp (consts holdsN) p) (fun _ => traceApp (consts holdsN) q))))
    rw [reads.prop]
    refine empty_mem_tracePiSet fun p hp => empty_mem_tracePiSet fun q hq =>
      empty_mem_tracePiSet fun h hh => empty_mem_tracePiSet fun a ha => ?_
    have truth : (tracePiSet p fun _ => q) ∈ truthValues := tracePiSet_mem_truthValues fun _ _ => hq
    rw [reads.holds, reads.imp, impValue_apply hp hq, holdsValue_apply truth] at hh
    rw [reads.holds, holdsValue_apply hp] at ha
    rw [reads.holds, holdsValue_apply hq]
    exact empty_mem_of_mem_truthValue hq (traceApp_mem_fibre hh ha)
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (V (.above 1)) (fun A =>
      tracePiSet (tracePiSet A (fun _ => consts propN)) (fun P =>
        tracePiSet (tracePiSet A (fun x => traceApp (consts holdsN) (traceApp P x)))
          (fun _ => traceApp (consts holdsN) (traceApp (traceApp (consts allN) A) P))))
    rw [reads.prop]
    refine empty_mem_tracePiSet fun A hA => empty_mem_tracePiSet fun P hP =>
      empty_mem_tracePiSet fun f hf => ?_
    have values : ∀ x ∈ A, traceApp P x ∈ truthValues := fun x hx => traceApp_mem_fibre hP hx
    have truth : tracePiSet A (fun x => traceApp P x) ∈ truthValues :=
      tracePiSet_mem_truthValues values
    rw [reads.holds, tracePiSet_congr fun x hx => holdsValue_apply (values x hx)] at hf
    rw [reads.holds, reads.allOver, allValue_apply hA hP, holdsValue_apply truth]
    exact empty_mem_of_mem_truthValue truth hf
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (V (.above 1)) (fun A =>
      tracePiSet (tracePiSet A (fun _ => consts propN)) (fun P =>
        tracePiSet (traceApp (consts holdsN) (traceApp (traceApp (consts allN) A) P))
          (fun _ => tracePiSet A (fun x => traceApp (consts holdsN) (traceApp P x)))))
    rw [reads.prop]
    refine empty_mem_tracePiSet fun A hA => empty_mem_tracePiSet fun P hP =>
      empty_mem_tracePiSet fun h hh => empty_mem_tracePiSet fun x hx => ?_
    have values : ∀ x ∈ A, traceApp P x ∈ truthValues := fun x hx => traceApp_mem_fibre hP hx
    rw [reads.holds, reads.allOver, allValue_apply hA hP,
      holdsValue_apply (tracePiSet_mem_truthValues values)] at hh
    rw [reads.holds, holdsValue_apply (values x hx)]
    exact empty_mem_of_mem_truthValue (values x hx) (traceApp_mem_fibre hh hx)
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (V (.above 1)) (fun A => tracePiSet A (fun a =>
      tracePiSet A (fun b => tracePiSet (truthCode (a = b)) (fun _ =>
        traceApp (consts holdsN) (traceApp (traceApp (traceApp (consts eqN) A) a) b)))))
    refine empty_mem_tracePiSet fun A hA => empty_mem_tracePiSet fun a ha =>
      empty_mem_tracePiSet fun b hb => empty_mem_tracePiSet fun e he => ?_
    rw [reads.holds, reads.eq, eqValue_apply hA ha hb,
      holdsValue_apply (truthCode_mem_truthValues _)]
    exact (mem_truthCode _ _).mpr ⟨rfl, ((mem_truthCode _ _).mp he).2⟩
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (V (.above 1)) (fun A => tracePiSet A (fun a =>
      tracePiSet A (fun b => tracePiSet
        (traceApp (consts holdsN) (traceApp (traceApp (traceApp (consts eqN) A) a) b))
        (fun _ => truthCode (a = b)))))
    refine empty_mem_tracePiSet fun A hA => empty_mem_tracePiSet fun a ha =>
      empty_mem_tracePiSet fun b hb => empty_mem_tracePiSet fun h hh => ?_
    rw [reads.holds, reads.eq, eqValue_apply hA ha hb,
      holdsValue_apply (truthCode_mem_truthValues _)] at hh
    exact (mem_truthCode _ _).mpr ⟨rfl, ((mem_truthCode _ _).mp hh).2⟩
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (V (.above 0)) (fun A => tracePiSet (V (.above 0)) (fun x =>
      tracePiSet (traceApp (consts holdsN) (traceApp (traceApp (consts inN) x) A)) (fun p =>
        truthCode (traceApp (traceApp (consts elemN) A)
          (traceApp (traceApp (traceApp (consts theN) A) x) p) = x))))
    refine empty_mem_tracePiSet fun A hA => empty_mem_tracePiSet fun x hx =>
      empty_mem_tracePiSet fun p hp => ?_
    rw [reads.holds, reads.in, inValue_apply hx hA,
      holdsValue_apply (truthCode_mem_truthValues _)] at hp
    rw [reads.the, reads.elem, theValue_apply hA hx hp,
      elemValue_apply hA ((mem_truthCode _ _).mp hp).2]
    exact (mem_truthCode _ _).mpr ⟨rfl, rfl⟩
  · show (∅ : ZFSet.{u}) ∈ tracePiSet (V (.above 0)) (fun A => tracePiSet A (fun a =>
      tracePiSet (traceApp (consts holdsN)
        (traceApp (traceApp (consts inN) (traceApp (traceApp (consts elemN) A) a)) A)) (fun q =>
        truthCode (traceApp (traceApp (traceApp (consts theN) A)
          (traceApp (traceApp (consts elemN) A) a)) q = a))))
    refine empty_mem_tracePiSet fun A hA => empty_mem_tracePiSet fun a ha =>
      empty_mem_tracePiSet fun q hq => ?_
    have haAll : a ∈ V (.above 0) := (chain.closed _).transitive _ hA ha
    rw [reads.holds, reads.in, reads.elem, elemValue_apply hA ha, inValue_apply haAll hA,
      holdsValue_apply (truthCode_mem_truthValues _)] at hq
    rw [reads.the, reads.elem, elemValue_apply hA ha, theValue_apply hA haAll hq]
    exact (mem_truthCode _ _).mpr ⟨rfl, rfl⟩

end RulesModel

section RulesModelFull

variable {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
  (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)
  (aroundMem : ∀ {x : ZFSet.{u}}, x ∈ V (.above 0) → around x ∈ V (.above 0))
  {extra : List (DeclName × CTm (Head L) 0)}

/-- An assignment that gives the constants of the table with the rules the values of the
constants of set theory reads the constants of set theory. -/
theorem reads_of_rulesTable {consts : DeclName → ZFSet.{u}} {all classes : ZFSet.{u}}
    (agrees : ∀ c, tableLookup (rulesTable L extra) c ≠ none →
      consts c = setValues all classes around c) : Reads L all classes around consts :=
  fun c known => agrees c (by
    obtain ⟨T, found⟩ := Option.ne_none_iff_exists'.mp known
    rw [rulesTable_set found]
    exact Option.some_ne_none T)

include chain groundTyped aroundMem in
/-- **The tower inside the sets with the constants of set theory, the rule constants and
further constants has a set model**, over every chain of closed universes whose universe of
the sets is closed under the operation, when the further constants are proofs: the constants
of set theory at their values, and every rule constant and every further constant read as the
empty set. The model is at every assignment that gives the constants these values. -/
theorem withRules_setModel_of_agreeing (ν : Nat → Above L)
    (extraTyped : ∀ consts : DeclName → ZFSet.{u},
      Reads L (V (.above 0)) (V (.above 1)) around consts →
        ∀ {c : DeclName} {T : CTm (Head L) 0}, (c, T) ∈ extra →
          (∅ : ZFSet.{u}) ∈ ev (chainHead V ground ν) consts T Fin.elim0)
    (base consts : DeclName → ZFSet.{u})
    (agrees : ∀ c, (withRules L extra).constantType c ≠ none →
      consts c = familyConsts base (tableLookup (rulesTable L extra))
        (setValues (V (.above 0)) (V (.above 1)) around) c) :
    SetModel (chainHead V ground ν) consts (withRules L extra) :=
  family_setModel_of_values (bare L)
    (fun consts _ => chain_setModel chain groundTyped ν consts) (fun _ _ => rfl)
    (setValues (V (.above 0)) (V (.above 1)) around)
    (fun consts _ agreesFamily {c T} declared => by
      have reads : Reads L (V (.above 0)) (V (.above 1)) around consts :=
        reads_of_rulesTable agreesFamily
      rcases rulesTable_cases declared with known | ⟨new, rule⟩ | ⟨new, _, row⟩
      · exact setValues_typed reads chain groundTyped aroundMem known
      · rw [setValues_undeclared _ _ _ new]
        exact ruleTable_typed reads chain (tableLookup_mem rule)
      · rw [setValues_undeclared _ _ _ new]
        exact extraTyped consts reads row)
    (fun _ _ _ _ member => absurd member List.not_mem_nil) consts agrees

include chain groundTyped aroundMem in
/-- **The set theory on rule constants has a set model**, over every chain of closed universes
whose universe of the sets is closed under the operation: the constants of set theory at
their values and every rule constant read as the empty set. -/
theorem setTheoryRules_setModel (ν : Nat → Above L) (base : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν)
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (V (.above 0)) (V (.above 1)) around))
      (setTheoryRules L) :=
  withRules_setModel_of_agreeing chain groundTyped aroundMem ν
    (fun _ _ _ _ row => absurd row List.not_mem_nil) base _ fun _ _ => rfl

include chain groundTyped aroundMem in
/-- Negative example: in the set theory on rule constants, **the type of the proofs that the
empty set is a member of itself has no closed term.** -/
theorem setTheoryRules_no_proof_empty_in_empty (ν : Nat → Above L)
    (base : DeclName → ZFSet.{u}) (t : CTm (Head L) 0) :
    ¬ CTyped (setTheoryRules L) .nil t (cHolds (cIn cEmpty cEmpty)) := by
  have reads : Reads L (V (.above 0)) (V (.above 1)) around
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (V (.above 0)) (V (.above 1)) around)) :=
    reads_of_rulesTable fun _ declared => familyConsts_declared declared
  refine CDerivable.no_closed_inhabitant
    (setTheoryRules_setModel chain groundTyped aroundMem ν base) (fun z inside => ?_) t
  change z ∈ traceApp
    (familyConsts base (tableLookup (rulesTable L []))
      (setValues (V (.above 0)) (V (.above 1)) around) holdsN)
    (traceApp (traceApp
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (V (.above 0)) (V (.above 1)) around) inN)
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (V (.above 0)) (V (.above 1)) around) emptyN))
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (V (.above 0)) (V (.above 1)) around) emptyN)) at inside
  rw [reads.holds, reads.in, reads.empty,
    inValue_apply (empty_mem_all chain groundTyped) (empty_mem_all chain groundTyped),
    holdsValue_apply (truthCode_mem_truthValues _)] at inside
  exact ZFSet.notMem_empty _ ((mem_truthCode _ _).mp inside).2

include chain groundTyped aroundMem in
/-- Negative example: in the set theory on rule constants, **no closed term has the type
`Π (X : U₀). X`**: the least universe has the empty set as a member. -/
theorem setTheoryRules_no_closed_emptyType (ν : Nat → Above L) (base : DeclName → ZFSet.{u})
    (t : CTm (Head L) 0) : ¬ CTyped (setTheoryRules L) .nil t (.pi U0 (.var 0)) := by
  refine CDerivable.no_closed_inhabitant
    (setTheoryRules_setModel chain groundTyped aroundMem ν base) (fun z inside => ?_) t
  change z ∈ tracePiSet (V (.below LevelOrder.bot)) (fun x => x) at inside
  exact ZFSet.notMem_empty _
    (traceApp_mem_fibre inside (chain.empty_mem groundTyped (.below LevelOrder.bot)))

end RulesModelFull

section RulesLowerSets

open ZFSetUniverseClosure (CofinalInaccessibles univOf)
open ZFSetUniverseLift (univOf_mem_carrierCode)
open ZFSetInterpretation (universeSet)

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})
  {ground : ZFSet.{u + 1}} (ν : Nat → Above L)

include small in
/-- **The set theory on rule constants has a set model**, relative to cofinally many
inaccessible cardinals in two universes: the type of all sets is read as all the sets of the
lower universe, `UnivOf` as the least closed universe around a set, every rule constant as the
empty set. -/
theorem lowerSets_setTheoryRules_setModel
    (groundTyped : ground ∈ universeSet large ZFSet.omega (LevelOrder.bot : L))
    (base : DeclName → ZFSet.{u + 1}) :
    SetModel (lowerSetsHeads (L := L) large ground ν)
      (familyConsts base (tableLookup (rulesTable L []))
        (setValues (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
          (univOf large)))
      (setTheoryRules L) :=
  setTheoryRules_setModel (stages_closedChain small large) groundTyped
    (fun hx => univOf_mem_carrierCode small large hx) ν base

include small large in
/-- **Consistency of the set theory on rule constants**, relative to cofinally many
inaccessible cardinals in two universes: no closed term proves that the empty set is a member
of itself. -/
theorem setTheoryRules_consistent (t : CTm (Head L) 0) :
    ¬ CTyped (setTheoryRules L) .nil t (cHolds (cIn cEmpty cEmpty)) :=
  setTheoryRules_no_proof_empty_in_empty (stages_closedChain (L := L) small large)
    (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L))
    (fun hx => univOf_mem_carrierCode small large hx) (fun _ => LevelOrder.bot) (fun _ => ∅) t

include small large in
/-- **No closed term of the set theory on rule constants has the type `Π (X : U₀). X`**,
relative to cofinally many inaccessible cardinals in two universes. -/
theorem setTheoryRules_consistent_emptyType (t : CTm (Head L) 0) :
    ¬ CTyped (setTheoryRules L) .nil t (.pi U0 (.var 0)) :=
  setTheoryRules_no_closed_emptyType (stages_closedChain (L := L) small large)
    (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L))
    (fun hx => univOf_mem_carrierCode small large hx) (fun _ => LevelOrder.bot) (fun _ => ∅) t

end RulesLowerSets

/-! ### Steps keep types and set values -/

section RulesSteps

variable {n : Nat} {Θ : CCtx (Head L) n}

/-- **The type formers of the set theory on rule constants are injective and distinct.** -/
theorem setTheoryRules_formerFacts : CFormerFacts (setTheoryRules L) := constants_formerFacts

/-- The set theory on rule constants has no declared step. -/
theorem setTheoryRules_noSteps {l r : CTm (Head L) n} :
    ¬ (setTheoryRules L).computation.step l r := constants_noSteps

/-- **Every reduction of a term typed in the set theory on rule constants keeps its type**, at
any position of the term. -/
theorem setTheoryRules_reduces_typed {t s T : CTm (Head L) n}
    (formed : CCtxFormed (setTheoryRules L) Θ) (reduces : CReduces (setTheoryRules L) t s)
    (typing : CTyped (setTheoryRules L) Θ t T) : CTyped (setTheoryRules L) Θ s T :=
  constants_reduces_typed formed reduces typing

/-- **A term typed in the set theory on rule constants keeps its set value along every
reduction**, in every set model. -/
theorem setTheoryRules_reduction_keeps_value {heads : Head L → ZFSet.{u}}
    {consts : DeclName → ZFSet.{u}} (model : SetModel heads consts (setTheoryRules L))
    {t s T : CTm (Head L) n} (formed : CCtxFormed (setTheoryRules L) Θ)
    (typing : CTyped (setTheoryRules L) Θ t T) (reduces : CReduces (setTheoryRules L) t s)
    (ρ : Env.{u} n) (sat : Sat heads consts Θ ρ) : ev heads consts t ρ = ev heads consts s ρ :=
  constants_reduction_keeps_value model formed typing reduces ρ sat

/-! ### Strong normalization -/

/-- **Strong normalization of the set theory on rule constants with further declared
constants**: every term typed in a formed context is strongly normalizing, whatever the
further constants and their types. -/
theorem withRules_sn {extra : List (DeclName × CTm (Head L) 0)} {t T : CTm (Head L) n}
    (formed : CCtxFormed (withRules L extra) Θ) (typing : CTyped (withRules L extra) Θ t T) :
    StrongNormalization.SN
      (Rules.sum (rules L) (familyRules (rules L) (tableLookup (rulesTable L extra)) [])) t.erase :=
  constants_sn formed typing

/-- **Strong normalization of the set theory on rule constants**: every term typed in a formed
context is strongly normalizing. -/
theorem setTheoryRules_sn {t T : CTm (Head L) n} (formed : CCtxFormed (setTheoryRules L) Θ)
    (typing : CTyped (setTheoryRules L) Θ t T) :
    StrongNormalization.SN
      (Rules.sum (rules L) (familyRules (rules L) (tableLookup (rulesTable L [])) [])) t.erase :=
  withRules_sn formed typing

/-- Positive example: the type of the proofs that the empty set is a member of a set, as a
function on the sets applied to `Power Empty`, is strongly normalizing. -/
theorem holdsEmptyInPower_sn :
    StrongNormalization.SN
      (Rules.sum (rules L) (familyRules (rules L) (tableLookup (rulesTable L [])) []))
      ((.app (.lam allSets (cHolds (cIn cEmpty (.var 0)))) (cPower cEmpty) :
        CTm (Head L) 0).erase) :=
  setTheoryRules_sn .nil
    (.appElim (B := U0)
      (.lamIntro (sets_typed setTheoryRules_over.sets.contains)
        (setTheoryRules_over.sets.contains.isUniverse (.sort _))
        (classToSet_typed setTheoryRules_over.sets.contains
          (sets_typed setTheoryRules_over.sets.contains)
          (U0_isSet setTheoryRules_over.sets))
        (setTheoryRules_over.sets.contains.isUniverse (.sort _))
        (cHolds_typed setTheoryRules_over.sets
          (cIn_typed setTheoryRules_over.sets (empty_typed setTheoryRules_over.sets) (.var 0))))
      (powerEmpty_typed setTheoryRules_over.sets))

end RulesSteps

/-! ## The unfolding of the proofs of a statement about all sets is not admitted -/

section Admission

/-- The predicate `y ↦ Empty ∈ y` on the sets. -/
abbrev emptyIn {n : Nat} : CTm (Head L) n := .app (.const inN) cEmpty

/-- `y ↦ Empty ∈ y` is a predicate on the sets. -/
theorem emptyIn_typed : CTyped (setTheory L) (.nil : CCtx (Head L) 0) emptyIn (.pi allSets cProp) :=
  .appElim (B := .pi allSets cProp) (in_typed setTheory_over) (empty_typed setTheory_over)

/-- The proofs of "the empty set is a member of every set" form a type of the least
universe. -/
theorem holdsEmptyIn_typed :
    CTyped (setTheory L) (.nil : CCtx (Head L) 0) (cHolds (cAllSets emptyIn)) U0 :=
  cHolds_typed setTheory_over (cAllSets_typed setTheory_over emptyIn_typed)

/-- **The equation for the proofs of a quantification steps them to a function type over
all the sets.** -/
theorem holdsEmptyIn_step :
    (setTheory L).computation.step (cHolds (cAllSets emptyIn) : CTm (Head L) 0)
      (.pi allSets (cHolds (.app (emptyIn.rename wk) (.var 0)))) :=
  .inr ⟨holdsAll L, List.mem_cons_of_mem _ List.mem_cons_self, ![emptyIn, allSets], rfl, rfl⟩

/-- **The package of set theory does not have both properties under which steps keep types**:
injective type formers, and declared steps that are equalities at the types of their left
sides. The proofs of "the empty set is a member of every set" are a type of the least
universe, and the equation for the proofs of a quantification steps them to a function type
over all the sets, which is a type of no universe at a level of `L`
(`not_admitted_of_small_step`). -/
theorem setTheory_not_admitted :
    ¬ (CFormerFacts (setTheory L) ∧ CRootAdmitted (setTheory L)) := fun ⟨facts, admitted⟩ =>
  not_admitted_of_small_step facts .nil holdsEmptyIn_typed holdsEmptyIn_step admitted

/-- **The set theory on rule constants has both properties under which steps keep types**:
injective type formers, and declared steps that are equalities at the types of their left
sides. It has no declared step. -/
theorem setTheoryRules_admitted :
    CFormerFacts (setTheoryRules L) ∧ CRootAdmitted (setTheoryRules L) :=
  ⟨constants_formerFacts, constants_admitted⟩

/-- Positive example: in the set theory on rule constants **the proofs of "the empty set is a
member of every set" take no step**: they are a type of the least universe there as in
`setTheory`, and nothing unfolds them. -/
theorem holdsEmptyIn_no_step_rules {r : CTm (Head L) 0} :
    ¬ (setTheoryRules L).computation.step (cHolds (cAllSets emptyIn)) r :=
  constants_noSteps

end Admission

end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
