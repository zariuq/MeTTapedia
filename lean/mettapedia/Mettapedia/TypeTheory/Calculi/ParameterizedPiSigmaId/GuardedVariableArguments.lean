import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedApplicationSpines

/-!
# Supplying actual guarded variables to dependent products

The variable positions retain their native carriers and original source
lookup types. The receiver opens each dependent product at that same variable
and constructs the existing guarded argument spine. Exact source-domain and
carrier checks may refuse; general converted arguments still use the existing
SuppliedArguments interface. No method-closure premise is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading

open Mettapedia.Logic
open Presentation TypedEquality.Annotated
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Head : Type} {Base : Type u} {Const : HOL.Ty Base → Type v}
    {R : Rules Head} {P : ChurchRules R} {lex : LexicalReading Head Base Const}
    {Γ : HOL.Ctx Base}

abbrev VariablePositions (Γ : HOL.Ctx Base) := List (Σ carrier : HOL.Ty Base, HOL.Var Γ carrier)

def variableSources (positions : VariablePositions Γ) : List (CTm Head Γ.length) :=
  positions.map fun position => .var position.2.toFin

/-- A declarative dependent-product spine at the given variable positions.
Its domains are the original context lookups, with no conversion assumption. -/
inductive VariablesSupply (context : GuardedContext P lex Γ) :
    VariablePositions Γ → CTm Head Γ.length → HOL.Ty Base → CTm Head Γ.length → HOL.Ty Base → Prop where
  | done (type : CTm Head Γ.length) (carrier : HOL.Ty Base) :
      VariablesSupply context [] type carrier type carrier
  | step {domain codomain result : HOL.Ty Base} {A : CTm Head Γ.length} {B : CTm Head (Γ.length + 1)}
      {rest : VariablePositions Γ} {target : CTm Head Γ.length} (index : HOL.Var Γ domain)
      (lookup : context.source.lookup index.toFin = A)
      (remaining : VariablesSupply context rest (CTm.inst0 (.var index.toFin) B) codomain target result) :
      VariablesSupply context (⟨domain, index⟩ :: rest) (.pi A B) (domain ⇒ codomain) target result

namespace VariablesSupply
variable {context : GuardedContext P lex Γ}

theorem unique {positions : VariablePositions Γ} {source first second : CTm Head Γ.length}
    {carrier firstCarrier secondCarrier : HOL.Ty Base}
    (one : VariablesSupply context positions source carrier first firstCarrier)
    (two : VariablesSupply context positions source carrier second secondCarrier) :
    first = second ∧ firstCarrier = secondCarrier := by
  induction one with
  | done => cases two; exact ⟨rfl, rfl⟩
  | step index lookup remaining previous =>
      cases two with
      | step _ _ other => exact previous other

theorem instantiate {positions : VariablePositions Γ} {source target : CTm Head Γ.length}
    {carrier result : HOL.Ty Base} (supplied : VariablesSupply context positions source carrier target result) :
    instantiateProducts (variableSources positions) source = some target := by
  induction supplied with
  | done => rfl
  | step index _ _ previous => exact previous

end VariablesSupply

namespace SuppliedArguments

def variableAt (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ)
    {carrier : HOL.Ty Base} (index : HOL.Var Γ carrier) (type : CTm Head Γ.length)
    (same : context.source.lookup index.toFin = type) :
    GuardedRealizer roots context (.var index.toFin) type carrier :=
  same ▸ GuardedRealizer.ofVariable roots context index

theorem variableAt_free (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ)
    {carrier : HOL.Ty Base} (index : HOL.Var Γ carrier) (type : CTm Head Γ.length)
    (same : context.source.lookup index.toFin = type) :
    (variableAt roots context index type same).Free := by
  cases same
  exact GuardedRealizer.ofVariable_free roots context index

structure VariableResult (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ)
    (positions : VariablePositions Γ) (source : CTm Head Γ.length) (carrier : HOL.Ty Base) where
  target : CTm Head Γ.length
  resultCarrier : HOL.Ty Base
  arguments : SuppliedArguments roots context (variableSources positions) source carrier target resultCarrier
  shape : VariablesSupply context positions source carrier target resultCarrier
  free : arguments.Free

def VariableResult.argumentsAt {roots : List (HOL.ClosedFormula Const)}
    {context : GuardedContext P lex Γ} {positions : VariablePositions Γ}
    {source : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (received : VariableResult roots context positions source carrier)
    (target : CTm Head Γ.length) (result : HOL.Ty Base)
    (sameType : received.target = target) (sameCarrier : received.resultCarrier = result) :
    SuppliedArguments roots context (variableSources positions) source carrier target result :=
  sameType ▸ sameCarrier ▸ received.arguments

theorem VariableResult.argumentsAt_free {roots : List (HOL.ClosedFormula Const)}
    {context : GuardedContext P lex Γ} {positions : VariablePositions Γ}
    {source : CTm Head Γ.length} {carrier : HOL.Ty Base}
    (received : VariableResult roots context positions source carrier)
    (target : CTm Head Γ.length) (result : HOL.Ty Base)
    (sameType : received.target = target) (sameCarrier : received.resultCarrier = result) :
    (received.argumentsAt target result sameType sameCarrier).Free := by
  cases sameType
  cases sameCarrier
  exact received.free

variable [DecidableEq Head] [DecidableEq Base]

def readVariables? (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ) :
    (positions : VariablePositions Γ) → (source : CTm Head Γ.length) → (carrier : HOL.Ty Base) →
      Option (VariableResult roots context positions source carrier)
  | [], source, carrier => some ⟨source, carrier, .nil source carrier, .done source carrier, True.intro⟩
  | ⟨actual, index⟩ :: rest, .pi A B, .arr domain codomain =>
      if same : actual = domain then by
        subst actual
        exact if lookup : context.source.lookup index.toFin = A then do
          let remaining ← readVariables? roots context rest (CTm.inst0 (.var index.toFin) B) codomain
          let value := variableAt roots context index A lookup
          pure ⟨remaining.target, remaining.resultCarrier, .cons value remaining.arguments,
            .step index lookup remaining.shape, variableAt_free roots context index A lookup, remaining.free⟩
        else none
      else none
  | _ :: _, _, _ => none
termination_by structural positions _ _ => positions

theorem readVariables?_complete {roots : List (HOL.ClosedFormula Const)} {context : GuardedContext P lex Γ}
    {positions : VariablePositions Γ} {source target : CTm Head Γ.length} {carrier result : HOL.Ty Base}
    (supplied : VariablesSupply context positions source carrier target result) :
    (readVariables? roots context positions source carrier).isSome = true := by
  induction supplied with
  | done => rfl
  | step index lookup remaining previous =>
      simp only [readVariables?, ↓reduceDIte, lookup]
      cases found : readVariables? roots context _ _ _ with
      | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at previous
      | some value => rfl

theorem readVariables?_isSome_iff (roots : List (HOL.ClosedFormula Const)) (context : GuardedContext P lex Γ)
    (positions : VariablePositions Γ) (source : CTm Head Γ.length) (carrier : HOL.Ty Base) :
    (readVariables? roots context positions source carrier).isSome = true ↔
      ∃ target result, VariablesSupply context positions source carrier target result := by
  constructor
  · intro accepted
    exact ⟨_, _, ((readVariables? roots context positions source carrier).get accepted).shape⟩
  · rintro ⟨target, result, supplied⟩
    exact readVariables?_complete supplied

#print axioms readVariables?
#print axioms readVariables?_isSome_iff

end SuppliedArguments
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
