import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentAcceptance4Under

/-!
# Reading a dead binder under live binders

**Opening both sides at one binder** (`openPair`): an equation with equal annotation codes, a Π annotation and
abstractions on both sides is read over the binder's declaration, the binder's type and the codomain formed once by the
checker for both sides, the bodies typed by inversion (R119's `openedOf`). **Closing** (`closePair`) forms the Π type of
the reduced opened equation by the checker and abstracts both sides again.

**Reading a dead binder under at most `depth` live binders** (`readDead`): R119's dead binder in front; otherwise open
one live binder, read under it one level down, and close. Every reading is a `DropsDead`, and reading is eventually
constant in the budget (`readDead_const`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentAcceptance4

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentEtaLong
open ContextualDependentIntersection ContextualDependentDynamicFragment ContextualDependentInPlace
open ContextualDependentIntersectionGeneral

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **An equation read over one binder of both sides.** -/
structure OpenedPair {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  domain : TypeOver Θ
  opened : Equation (TotalTerm (extend Θ domain))
  abstracts : Abstracts equation domain opened
  same : opened.2.1.code = opened.1.1.code

/-- Both sides opened at one formed binder type and codomain. -/
def pairOf {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {P : Tm Head Θ.arity}
    {C M N : Tm Head (Θ.arity + 1)} (sameCode : equation.2.1.code = equation.1.1.code)
    (typeCode : equation.1.1.code = .pi P C) (leftCode : equation.1.2.code = .lam M)
    (rightCode : equation.2.2.code = .lam N) (domain : {type : TypeOver Θ // type.code = P})
    (codomain : {type : TypeOver (extend Θ domain.val) // type.code = C}) : OpenedPair equation where
  domain := domain.val
  opened := ((openedOf facts equation.1 typeCode leftCode domain codomain).body,
    (openedOf facts equation.2 (sameCode.trans typeCode) rightCode domain codomain).body)
  abstracts :=
    ⟨(openedOf facts equation.1 typeCode leftCode domain codomain).typeCode,
      (openedOf facts equation.2 (sameCode.trans typeCode) rightCode domain codomain).typeCode,
      (openedOf facts equation.1 typeCode leftCode domain codomain).termCode,
      (openedOf facts equation.2 (sameCode.trans typeCode) rightCode domain codomain).termCode⟩
  same := rfl

/-- Open both sides at one binder, once the binder's type and the codomain are formed. -/
def openPairWith (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {P : Tm Head Θ.arity}
    {C M N : Tm Head (Θ.arity + 1)} (sameCode : equation.2.1.code = equation.1.1.code)
    (typeCode : equation.1.1.code = .pi P C) (leftCode : equation.1.2.code = .lam M)
    (rightCode : equation.2.2.code = .lam N) : Option (OpenedPair equation) :=
  match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ P with
  | none => none
  | some domain =>
      (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
        (extend Θ domain.val) C).map (pairOf facts equation sameCode typeCode leftCode rightCode domain)

/-- **Open both sides of an equation at one binder**, at each budget. -/
def openPair {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) : Nat → Option (OpenedPair equation) :=
  if sameCode : equation.2.1.code = equation.1.1.code then
    match typeCode : equation.1.1.code, leftCode : equation.1.2.code, rightCode : equation.2.2.code with
    | .pi _ _, .lam _, .lam _ => fun fuel =>
        openPairWith facts roots heads algebra declared choices reducer fuel equation sameCode typeCode leftCode
          rightCode
    | _, _, _ => fun _ => none
  else fun _ => none

/-- An abstraction of a reduced opened equation at its formed Π type. -/
def closedOf {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (pair : OpenedPair equation)
    (inner : {reduced : Equation (TotalTerm (extend Θ pair.domain)) // DropsDead pair.opened reduced})
    (type : {type : TypeOver Θ // type.code = .pi pair.domain.code inner.val.1.1.code}) :
    {reduced : Equation (TotalTerm Θ) // DropsDead equation reduced} :=
  have formed : Typed S.R Θ.raw (.pi pair.domain.code inner.val.1.1.code) (.head type.val.level) := by
    have typed := type.val.formed
    rw [type.property] at typed
    exact typed
  have rightTyped : Typed S.R (extend Θ pair.domain).raw inner.val.2.2.code inner.val.1.1.code := by
    have typed := inner.val.2.2.typed
    rw [inner.property.sameType] at typed
    exact typed
  let closed : Equation (TotalTerm Θ) :=
    (⟨type.val, ⟨.lam inner.val.1.2.code, by
        rw [type.property]
        exact Derivable.lamIntro formed type.val.universeWitness inner.val.1.2.typed⟩⟩,
      ⟨type.val, ⟨.lam inner.val.2.2.code, by
        rw [type.property]
        exact Derivable.lamIntro formed type.val.universeWitness rightTyped⟩⟩)
  ⟨closed, .under pair.domain pair.abstracts pair.same
    ⟨type.property, type.property.trans (by rw [inner.property.sameType]), rfl, rfl⟩ inner.property.sameType
    inner.property⟩

/-- **Close a reduced opened equation** at the Π type formed by the checker. -/
def closePair (fuel : Nat) {Θ : Context S.R} {equation : Equation (TotalTerm Θ)} (pair : OpenedPair equation)
    (inner : {reduced : Equation (TotalTerm (extend Θ pair.domain)) // DropsDead pair.opened reduced}) :
    Option {reduced : Equation (TotalTerm Θ) // DropsDead equation reduced} :=
  (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ
    (.pi pair.domain.code inner.val.1.1.code)).map (closedOf pair inner)

/-- **Read a dead binder under at most `depth` live binders.** -/
def readDead (fuel : Nat) : Nat → {Θ : Context S.R} → (equation : Equation (TotalTerm Θ)) →
    Option {reduced : Equation (TotalTerm Θ) // DropsDead equation reduced}
  | 0, _, equation => (deadBinder facts roots heads algebra declared choices reducer fuel equation).map
      fun dead => ⟨dead.reduced, .front dead⟩
  | depth + 1, _, equation =>
      match deadBinder facts roots heads algebra declared choices reducer fuel equation with
      | some dead => some ⟨dead.reduced, .front dead⟩
      | none => (openPair facts roots heads algebra declared choices reducer equation fuel).bind fun pair =>
          (readDead fuel depth pair.opened).bind
            (closePair facts roots heads algebra declared choices reducer fuel pair)

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem openPairWith_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) {P : Tm Head Θ.arity}
    {C M N : Tm Head (Θ.arity + 1)} (sameCode : equation.2.1.code = equation.1.1.code)
    (typeCode : equation.1.1.code = .pi P C) (leftCode : equation.1.2.code = .lam M)
    (rightCode : equation.2.2.code = .lam N) :
    EventuallyConst fun fuel => openPairWith facts roots heads algebra declared choices reducer fuel equation sameCode
      typeCode leftCode rightCode := by
  unfold openPairWith
  exact EventuallyConst.dep (h := fun fuel =>
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ P)
    (k := fun fuel domain => match domain with
      | none => none
      | some domain => (ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel
          (extend Θ domain.val) C).map (pairOf facts equation sameCode typeCode leftCode rightCode domain))
    (formType_const facts roots heads algebra declared choices reducer stable P)
    (fun domain => by
      cases domain with
      | none => exact EventuallyConst.const _
      | some domain =>
          exact EventuallyConst.comp (Option.map (pairOf facts equation sameCode typeCode leftCode rightCode domain))
            (formType_const facts roots heads algebra declared choices reducer stable (Γ := extend Θ domain.val) C))

include stable in
theorem openPair_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst (openPair facts roots heads algebra declared choices reducer equation) := by
  unfold openPair
  split
  · split
    · exact openPairWith_const facts roots heads algebra declared choices reducer stable equation _ _ _ _
    · exact EventuallyConst.const _
  · exact EventuallyConst.const _

include stable in
/-- **Reading a dead binder under live binders is eventually constant**, at every depth. -/
theorem readDead_const : ∀ (depth : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)),
    EventuallyConst fun fuel => readDead facts roots heads algebra declared choices reducer fuel depth equation
  | 0, _, equation => EventuallyConst.comp _
      (deadBinder_const facts roots heads algebra declared choices reducer stable equation)
  | depth + 1, Θ, equation =>
      EventuallyConst.dep (h := fun fuel => deadBinder facts roots heads algebra declared choices reducer fuel equation)
        (k := fun fuel (found : Option (DeadBinder equation)) =>
          (match found with
            | some dead => some ⟨dead.reduced, .front dead⟩
            | none => (openPair facts roots heads algebra declared choices reducer equation fuel).bind fun pair =>
                (readDead facts roots heads algebra declared choices reducer fuel depth pair.opened).bind
                  (closePair facts roots heads algebra declared choices reducer fuel pair) :
            Option {reduced : Equation (TotalTerm Θ) // DropsDead equation reduced}))
        (deadBinder_const facts roots heads algebra declared choices reducer stable equation)
        (fun found => by
          cases found with
          | some dead => exact EventuallyConst.const _
          | none =>
              exact EventuallyConst.dep (h := openPair facts roots heads algebra declared choices reducer equation)
                (k := fun fuel (pair? : Option (OpenedPair equation)) => pair?.bind fun pair =>
                  (readDead facts roots heads algebra declared choices reducer fuel depth pair.opened).bind
                    (closePair facts roots heads algebra declared choices reducer fuel pair))
                (openPair_const facts roots heads algebra declared choices reducer stable equation)
                (fun pair? => by
                  cases pair? with
                  | none => exact EventuallyConst.const _
                  | some pair =>
                      exact EventuallyConst.dep
                        (h := fun fuel => readDead facts roots heads algebra declared choices reducer fuel depth
                          pair.opened)
                        (k := fun fuel inner? => inner?.bind
                          (closePair facts roots heads algebra declared choices reducer fuel pair))
                        (readDead_const depth pair.opened)
                        (fun inner? => by
                          cases inner? with
                          | none => exact EventuallyConst.const _
                          | some inner =>
                              exact EventuallyConst.of_eq (fun _ => rfl)
                                (EventuallyConst.comp (Option.map (closedOf pair inner))
                                  (formType_const facts roots heads algebra declared choices reducer stable (Γ := Θ)
                                    (.pi pair.domain.code inner.val.1.1.code))))))

end ContextualDependentAcceptance4
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
