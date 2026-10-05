import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetsModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetConstantFamilies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.ReductionValues
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetProofs

/-!
# Steps, set values and set models: two controls

`TowerInterpretation.ReductionValues` shows that a typed term keeps its set value along every
reduction, in a package with a set model whose type formers are injective. This file shows
that the hypothesis on the type formers cannot be dropped, and that keeping types along steps
says nothing about a set model.

The set model reads a function as its trace, and the trace of a function does not record its
domain: over any set, the only function into a one-element type has the empty trace. So the
functions from a one-element set into a one-element set and the functions from a two-element
set into that one-element set are one set of traces, and a package may declare the two
function types equal while its equations still hold between sets.

**The package** (`twoDomains`), over the tower inside the sets: two types `one` and `two` of
the least universe, a term `point` of `two`, and one equation between closed types,
`Π (x : one). one ⟶ Π (x : two). one`.

* It has a set model over every chain of closed universes (`twoDomains_setModel`): `one` is
  `{∅}`, `two` is `{∅, {∅}}`, `point` is `{∅}`, and both function types are `{∅}`.
* The identity on `one`, applied to `point`, is typed at `one` (`redex_typed`): the identity
  is retyped along the declared equation.
* It takes a step to `point` (`redex_reduces`).
* **The step changes the value** (`redex_value_ne`): the term denotes `∅`, the application of
  a trace outside its domain, and `point` denotes `{∅}`.
* The reduct is not typed at the type of the term (`point_not_one`), and the type formers of
  the package are not injective (`not_formerFacts`): it proves two function types equal
  whose domains the sets tell apart.

So an equation between two function types with different domains is not admissible for
running, although the sets satisfy it. Positive example for contrast: without the declared
equation the same term is not typed, and in the tower with no declared equation every typed
term keeps its value (`MegalodonHOTG.reduction_keeps_value`).

**Preservation is not soundness** (`withFalsum`): the set theory on rule constants with one
more declared constant, a proof of falsity, and no equation.

* It is a family of declared constants with no equation, so its type formers are injective
  and every step of a typed term keeps its type (`withFalsum_admitted`,
  `withFalsum_reduces_typed`).
* It proves that the empty set is a member of itself, by the elimination of the quantifier at
  the proof of falsity (`withFalsum_proves_empty_in_empty`).
* It has no set model over any chain of closed universes, at any assignment that reads the
  constants of set theory: the proofs of falsity are the false truth value
  (`withFalsum_no_setModel`, `preservation_not_soundness`).

Positive example for contrast: the set theory on rule constants without that constant keeps
types along steps and has a set model (`MegalodonHOTG.setTheoryRules_admitted`,
`MegalodonHOTG.setTheoryRules_setModel`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace ValueControls

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (Closed CofinalInaccessibles)
open ZFSetInterpretation (universeSet)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_outside
  tracePiSet_eq_unit_iff)

universe u

variable {L : Type}

/-- A type with one term. -/
def oneN : DeclName := .str .anonymous "one"

/-- A type with two terms. -/
def twoN : DeclName := .str .anonymous "two"

/-- A term of the type with two terms. -/
def pointN : DeclName := .str .anonymous "point"

section Terms

variable [LevelOrder L] {n : Nat}


/-- `one`. -/
abbrev cOne : CTm (Head L) n := .const oneN

/-- `two`. -/
abbrev cTwo : CTm (Head L) n := .const twoN

/-- `point`. -/
abbrev cPoint : CTm (Head L) n := .const pointN

/-- The functions from `one` to `one`. -/
abbrev fromOne : CTm (Head L) n := .pi cOne cOne

/-- The functions from `two` to `one`. -/
abbrev fromTwo : CTm (Head L) n := .pi cTwo cOne

/-- The identity on `one`. -/
abbrev identityOne : CTm (Head L) n := .lam cOne (.var 0)

/-- The identity on `one`, applied to `point`. -/
abbrev redex : CTm (Head L) n := .app identityOne cPoint

end Terms

variable [LevelOrder L]

variable (L) in
/-- The table of the constants: each with its type. -/
def table : List (DeclName × CTm (Head L) 0) :=
  [(oneN, U0), (twoN, U0), (pointN, cTwo)]

variable (L) in
/-- The declarations of the constants. -/
def decls : DeclName → Option (CTm (Head L) 0) := tableLookup (table L)

variable (L) in
/-- The equation between the two function types: `Π (x : one). one ⟶ Π (x : two). one`. -/
def domains : DefiningEquation (Head L) where
  arity := 0
  telescope := .nil
  left := fromOne
  right := fromTwo

variable (L) in
/-- The tower inside the sets with the three constants and the equation between the two
function types. -/
abbrev twoDomains := withFamily (bare L) (decls L) [domains L]

/-- `one` is declared at the least universe. -/
theorem decls_one : decls L oneN = some U0 := rfl

/-- `two` is declared at the least universe. -/
theorem decls_two : decls L twoN = some U0 := rfl

/-- `point` is declared at `two`. -/
theorem decls_point : decls L pointN = some cTwo := rfl

/-! ## In the judgment -/

section Judgment

variable {n : Nat} {Γ : CCtx (Head L) n}

/-- A constant is declared in the package as the table declares it. -/
theorem declared {c : DeclName} {T : CTm (Head L) 0} (known : decls L c = some T) :
    (twoDomains L).constantType c = some T :=
  (withFamily_declared (bare L) rfl).trans known

/-- The least universe is a type. -/
theorem least_typed :
    CTyped (twoDomains L) Γ U0 (universeAt (LevelOrder.succ LevelOrder.bot)) :=
  universe_typed package_contains LevelOrder.bot

/-- `one` is a type of the least universe. -/
theorem one_typed : CTyped (twoDomains L) Γ cOne U0 :=
  definition_typed (declared decls_one) (least_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

/-- `two` is a type of the least universe. -/
theorem two_typed : CTyped (twoDomains L) Γ cTwo U0 :=
  definition_typed (declared decls_two) (least_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

/-- `point` is a term of `two`. -/
theorem point_typed : CTyped (twoDomains L) Γ cPoint cTwo :=
  definition_typed (declared decls_point) (two_typed (Γ := .nil))
    (package_contains.isUniverse (.sort _))

/-- The functions from `one` to `one` are a type of the least universe. -/
theorem fromOne_typed : CTyped (twoDomains L) Γ fromOne U0 :=
  CDerivable.cumul
    (.piForm one_typed (package_contains.isUniverse (.sort _)) one_typed (package_contains.isUniverse (.sort _))
      (package_contains.join (.sorts _ _)))
    (package_contains.cumulative
      (u := .sort (.max (.const (.below LevelOrder.bot)) (.const (.below LevelOrder.bot))))
      (v := .sort (.const (.below LevelOrder.bot))) fun _ => max_le (le_refl _) (le_refl _))

/-- The functions from `two` to `one` are a type of the least universe. -/
theorem fromTwo_typed : CTyped (twoDomains L) Γ fromTwo U0 :=
  CDerivable.cumul
    (.piForm two_typed (package_contains.isUniverse (.sort _)) one_typed (package_contains.isUniverse (.sort _))
      (package_contains.join (.sorts _ _)))
    (package_contains.cumulative
      (u := .sort (.max (.const (.below LevelOrder.bot)) (.const (.below LevelOrder.bot))))
      (v := .sort (.const (.below LevelOrder.bot))) fun _ => max_le (le_refl _) (le_refl _))

/-- The identity on `one` is a function from `one` to `one`. -/
theorem identity_typed : CTyped (twoDomains L) Γ identityOne fromOne :=
  .lamIntro one_typed (package_contains.isUniverse (.sort _)) fromOne_typed
    (package_contains.isUniverse (.sort _)) (.var 0)

/-- The package contains the step of its equation. -/
theorem computes :
    StepsWithin (familyChurch (rules L) (decls L) [domains L]) (twoDomains L) :=
  StepsWithin.sum_right (bare L) (familyChurch (rules L) (decls L) [domains L])

/-- **The two function types are equal in the judgment**, by the declared equation. -/
theorem domains_equal : CEqual (twoDomains L) Γ fromOne fromTwo U0 :=
  family_equation_holds (rules L) computes (e := domains L) (List.mem_singleton.mpr rfl)
    (fun i => i.elim0) (fun i => i.elim0) fromOne_typed fromTwo_typed

/-- The identity on `one` is a function from `two` to `one`, by the declared equation. -/
theorem identity_fromTwo : CTyped (twoDomains L) Γ identityOne fromTwo :=
  .conv identity_typed domains_equal (package_contains.isUniverse (.sort _))

/-- **The identity on `one`, applied to `point`, is typed at `one`.** -/
theorem redex_typed : CTyped (twoDomains L) Γ redex cOne :=
  .appElim (B := cOne) identity_fromTwo point_typed

/-- **It takes a step to `point`.** -/
theorem redex_reduces : CReduces (twoDomains L) (redex : CTm (Head L) n) cPoint :=
  .single (.betaPi cOne (.var 0) cPoint)

end Judgment

/-! ## In the sets -/

section Model

/-- The table of the values: `one` is `{∅}`, `two` is `{∅, {∅}}`, `point` is `{∅}`. -/
noncomputable def valueTable : List (DeclName × ZFSet.{u}) :=
  [(oneN, {∅}), (twoN, {∅, {∅}}), (pointN, {∅})]

/-- The values of the constants. -/
noncomputable def values : DeclName → ZFSet.{u} := fun c =>
  (tableLookup valueTable c).getD ∅

/-- The value of `one`. -/
theorem values_one : values.{u} oneN = {∅} := rfl

/-- The value of `two`. -/
theorem values_two : values.{u} twoN = {∅, {∅}} := rfl

/-- The value of `point`. -/
theorem values_point : values.{u} pointN = {∅} := rfl

/-- An assignment that gives the constants their values reads `one` as `{∅}`. -/
theorem reads_one (base : DeclName → ZFSet.{u}) :
    familyConsts base (decls L) values oneN = {∅} :=
  (familyConsts_declared (by rw [decls_one]; exact Option.some_ne_none _)).trans values_one

/-- It reads `two` as `{∅, {∅}}`. -/
theorem reads_two (base : DeclName → ZFSet.{u}) :
    familyConsts base (decls L) values twoN = {∅, {∅}} :=
  (familyConsts_declared (by rw [decls_two]; exact Option.some_ne_none _)).trans values_two

/-- It reads `point` as `{∅}`. -/
theorem reads_point (base : DeclName → ZFSet.{u}) :
    familyConsts base (decls L) values pointN = {∅} :=
  (familyConsts_declared (by rw [decls_point]; exact Option.some_ne_none _)).trans values_point

/-- Over any set, the functions into the one-element set `{∅}` are the one-element set
`{∅}`: the trace of every such function is empty. -/
theorem functions_into_unit (a : ZFSet.{u}) :
    tracePiSet a (fun _ => ({∅} : ZFSet.{u})) = {∅} :=
  (tracePiSet_eq_unit_iff (a := a) (b := fun _ => ({∅} : ZFSet.{u}))
    (fun _ _ _ member => member)).mpr (fun _ _ => rfl)

variable {V : Above L → ZFSet.{u}} {ground : ZFSet.{u}} {ν : Nat → Above L}

/-- The value of the term: the trace of the identity on `{∅}`, applied to `{∅}`, which is
outside `{∅}`. It is empty. -/
theorem redex_value (base : DeclName → ZFSet.{u}) {n : Nat} (ρ : Env.{u} n) :
    ev (chainHead V ground ν) (familyConsts base (decls L) values) (redex : CTm (Head L) n) ρ =
      ∅ := by
  show traceApp (traceLam (graph (familyConsts base (decls L) values oneN) fun x => x))
    (familyConsts base (decls L) values pointN) = ∅
  rw [reads_one, reads_point]
  exact traceApp_graph_outside (fun x => x) (ZFSet.mem_irrefl _)

/-- **The step changes the value**: the term denotes `∅` and `point` denotes `{∅}`. -/
theorem redex_value_ne (base : DeclName → ZFSet.{u}) {n : Nat} (ρ : Env.{u} n) :
    ev (chainHead V ground ν) (familyConsts base (decls L) values) (redex : CTm (Head L) n) ρ ≠
      ev (chainHead V ground ν) (familyConsts base (decls L) values)
        (cPoint : CTm (Head L) n) ρ := by
  rw [redex_value]
  show (∅ : ZFSet.{u}) ≠ familyConsts base (decls L) values pointN
  rw [reads_point]
  exact ZFSetTraceProducts.Controls.distinct_domains

variable (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)

include chain groundTyped in
/-- Every value lies in the set of its constant's type. -/
theorem values_typed {consts : DeclName → ZFSet.{u}}
    (reads : ∀ c, decls L c ≠ none → consts c = values c) {c : DeclName}
    {T : CTm (Head L) 0} (known : decls L c = some T) :
    values c ∈ ev (chainHead V ground ν) consts T Fin.elim0 := by
  have empty : (∅ : ZFSet.{u}) ∈ V (.below LevelOrder.bot) :=
    chain.empty_mem groundTyped (.below LevelOrder.bot)
  have closed : Closed (V (.below LevelOrder.bot)) := chain.closed (.below LevelOrder.bot)
  have row := tableLookup_mem known
  simp only [table, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show ({∅} : ZFSet.{u}) ∈ V (.below LevelOrder.bot)
    exact closed.singleton_mem empty
  · show ({∅, {∅}} : ZFSet.{u}) ∈ V (.below LevelOrder.bot)
    exact closed.unorderedPair_mem empty (closed.singleton_mem empty)
  · show ({∅} : ZFSet.{u}) ∈ consts twoN
    rw [reads twoN (by rw [decls_two]; exact Option.some_ne_none _), values_two]
    exact ZFSet.mem_pair.mpr (Or.inr rfl)

/-- The declared equation holds between sets: both function types are `{∅}`. -/
theorem domains_valid {consts : DeclName → ZFSet.{u}}
    (reads : ∀ c, decls L c ≠ none → consts c = values c) :
    ∀ e ∈ [domains L], ∀ η : Env.{u} e.arity,
      Sat (chainHead V ground ν) consts e.telescope η →
        ev (chainHead V ground ν) consts e.left η =
          ev (chainHead V ground ν) consts e.right η := by
  intro e member η _
  obtain rfl := List.mem_singleton.mp member
  show tracePiSet (consts oneN) (fun _ => consts oneN) =
    tracePiSet (consts twoN) (fun _ => consts oneN)
  rw [reads oneN (by rw [decls_one]; exact Option.some_ne_none _), values_one,
    functions_into_unit, functions_into_unit]

include chain groundTyped in
/-- **The package has a set model**, over every chain of closed universes. -/
theorem twoDomains_setModel (base : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν) (familyConsts base (decls L) values) (twoDomains L) :=
  family_setModel_read (bare L)
    (fun consts _ => chain_setModel chain groundTyped ν consts) (fun _ _ => rfl) values
    (fun _ _ reads {_ _} known => values_typed chain groundTyped reads known)
    (fun _ _ reads => domains_valid reads)

include chain groundTyped in
/-- **The reduct is not typed at the type of the term**: `point` is not a term of `one`. -/
theorem point_not_one : ¬ CTyped (twoDomains L) .nil (cPoint : CTm (Head L) 0) cOne := by
  intro typing
  have member := CDerivable.inhabited
    (twoDomains_setModel (ν := fun _ => LevelOrder.bot) chain groundTyped fun _ => ∅) typing
  change familyConsts (fun _ => ∅) (decls L) values pointN ∈
    familyConsts (fun _ => ∅) (decls L) values oneN at member
  rw [reads_point, reads_one] at member
  exact ZFSet.mem_irrefl _ member

include chain groundTyped in
/-- **The type formers of the package are not injective**: it proves the two function types
equal, and their domains have different sets. -/
theorem not_formerFacts : ¬ CFormerFacts (twoDomains L) := by
  intro facts
  have equal : CTypeEq (twoDomains L) .nil (fromOne : CTm (Head L) 0) fromTwo :=
    ⟨_, package_contains.isUniverse (.sort _), domains_equal⟩
  obtain ⟨⟨_, _, sameDomain⟩, _⟩ := CTypeEq.pi_injective facts equal .nil
  have same := CDerivable.sound_equality
    (twoDomains_setModel (ν := fun _ => LevelOrder.bot) chain groundTyped fun _ => ∅)
    sameDomain Fin.elim0 (sat_nil _ _ Fin.elim0)
  change familyConsts (fun _ => ∅) (decls L) values oneN =
    familyConsts (fun _ => ∅) (decls L) values twoN at same
  rw [reads_one, reads_two] at same
  have member : ({∅} : ZFSet.{u}) ∈ ({∅, {∅}} : ZFSet.{u}) :=
    ZFSet.mem_pair.mpr (Or.inr rfl)
  rw [← same] at member
  exact ZFSet.mem_irrefl _ member

include chain groundTyped in
/-- **A set model does not make a step keep the value.** The package has a set model, the
term is typed and takes a step, and the step changes the value. -/
theorem value_not_kept (base : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν) (familyConsts base (decls L) values) (twoDomains L) ∧
      CTyped (twoDomains L) .nil (redex : CTm (Head L) 0) cOne ∧
      CReduces (twoDomains L) (redex : CTm (Head L) 0) cPoint ∧
      ev (chainHead V ground ν) (familyConsts base (decls L) values)
          (redex : CTm (Head L) 0) Fin.elim0 ≠
        ev (chainHead V ground ν) (familyConsts base (decls L) values)
          (cPoint : CTm (Head L) 0) Fin.elim0 :=
  ⟨twoDomains_setModel chain groundTyped base, redex_typed, redex_reduces,
    redex_value_ne base Fin.elim0⟩

end Model

/-! ## On the stages -/

section LowerSets

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})

include small large in
/-- The type formers of the package are not injective, relative to cofinally many inaccessible
cardinals in two universes. -/
theorem lowerSets_not_formerFacts : ¬ CFormerFacts (twoDomains L) :=
  not_formerFacts (stages_closedChain small large)
    (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L))

include small large in
/-- Subject reduction fails in the package, relative to cofinally many inaccessible cardinals
in two universes: the term is typed at `one`, it takes a step to `point`, and `point` is not
typed at `one`. -/
theorem lowerSets_typing_not_kept :
    CTyped (twoDomains L) .nil (redex : CTm (Head L) 0) cOne ∧
      CReduces (twoDomains L) (redex : CTm (Head L) 0) cPoint ∧
      ¬ CTyped (twoDomains L) .nil (cPoint : CTm (Head L) 0) cOne :=
  ⟨redex_typed, redex_reduces,
    point_not_one (stages_closedChain small large)
      (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L))⟩

end LowerSets

/-! ## Preservation is not soundness -/

section Falsum

/-- A proof of falsity. -/
def falsumProofN : DeclName := .str .anonymous "falsumProof"

variable (L) in
/-- **The set theory on rule constants with a proof of falsity**: one more declared constant,
at the type of the proofs of falsity, and no equation. -/
abbrev withFalsum := withRules L [(falsumProofN, cHolds cFalse)]

/-- **Steps keep types in the package with a proof of falsity**: it is a family of declared
constants with no equation, so its type formers are injective and it has no declared step. -/
theorem withFalsum_admitted : CFormerFacts (withFalsum L) ∧ CRootAdmitted (withFalsum L) :=
  ⟨constants_formerFacts, constants_admitted⟩

/-- Every reduction of a term typed in the package with a proof of falsity keeps its type. -/
theorem withFalsum_reduces_typed {n : Nat} {Θ : CCtx (Head L) n} {t s T : CTm (Head L) n}
    (formed : CCtxFormed (withFalsum L) Θ) (reduces : CReduces (withFalsum L) t s)
    (typing : CTyped (withFalsum L) Θ t T) : CTyped (withFalsum L) Θ s T :=
  constants_reduces_typed formed reduces typing

/-- The proof of falsity is a closed term of the package. -/
theorem falsumProof_typed :
    CTyped (withFalsum L) .nil (.const falsumProofN) (cHolds cFalse) := by
  have typed := definition_typed (Γ := (.nil : CCtx (Head L) 0))
    ((withRules_declared (c := falsumProofN)).trans rfl)
    (cHolds_typed (withRules_over (L := L) _).sets (cFalse_typed (withRules_over _).sets))
    ((withRules_over (L := L) [(falsumProofN, cHolds cFalse)]).sets.contains.isUniverse (.sort _))
  rwa [CTm.liftClosed_zero] at typed

/-- **The package with a proof of falsity proves that the empty set is a member of itself**:
the elimination of the quantifier at the proof of falsity. -/
theorem withFalsum_proves_empty_in_empty :
    CTyped (withFalsum L) .nil
      (cAllE cProp (.lam cProp (.var 0)) (.const falsumProofN) (cIn cEmpty cEmpty))
      (cHolds (cIn cEmpty cEmpty)) :=
  (ruleOps_lawful (withRules_over _)).allE (prop_isClass (withRules_over _).sets) (.var 0)
    falsumProof_typed
    (cIn_typed (withRules_over _).sets (empty_typed (withRules_over _).sets)
      (empty_typed (withRules_over _).sets))

variable {V : Above L → ZFSet.{u}} {around : ZFSet.{u} → ZFSet.{u}} {ground : ZFSet.{u}}
  (chain : ClosedChain V) (groundTyped : ground ∈ V LevelOrder.bot)

include chain groundTyped in
/-- **The package with a proof of falsity has no set model** over any chain of closed
universes, at any assignment that reads the constants of set theory: the proofs of falsity are
the false truth value, which has no member. -/
theorem withFalsum_no_setModel (ν : Nat → Above L) {consts : DeclName → ZFSet.{u}}
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) :
    ¬ SetModel (chainHead V ground ν) consts (withFalsum L) := by
  have propClass : truthValues.{u} ∈ V (.above 1) :=
    chain.mono (Above.below_le_above LevelOrder.bot 1) (truthValues_mem_zero chain groundTyped)
  refine family_no_setModel_of_empty (bare L) (c := falsumProofN) rfl rfl consts
    fun z inside => ?_
  rw [ev_cHolds reads (ev_cFalse reads propClass Fin.elim0)] at inside
  exact ((ZFSetTraceProofDecoding.mem_truthCode _ _).mp inside).2

include chain groundTyped in
/-- **Preservation is not soundness.** The package with a proof of falsity has both
properties under which steps keep types, and it proves that the empty set is a member of
itself; it has no set model at the reading of the constants of set theory. Contrast the set
theory on rule constants, which has both properties and a set model
(`setTheoryRules_admitted`, `setTheoryRules_setModel`). -/
theorem preservation_not_soundness (ν : Nat → Above L) {consts : DeclName → ZFSet.{u}}
    (reads : Reads L (V (.above 0)) (V (.above 1)) around consts) :
    (CFormerFacts (withFalsum L) ∧ CRootAdmitted (withFalsum L)) ∧
      CTyped (withFalsum L) .nil
        (cAllE cProp (.lam cProp (.var 0)) (.const falsumProofN) (cIn cEmpty cEmpty))
        (cHolds (cIn cEmpty cEmpty)) ∧
      ¬ SetModel (chainHead V ground ν) consts (withFalsum L) :=
  ⟨withFalsum_admitted, withFalsum_proves_empty_in_empty,
    withFalsum_no_setModel chain groundTyped ν reads⟩

end Falsum

end ValueControls
end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
