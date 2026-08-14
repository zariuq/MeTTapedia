import Mettapedia.GSLT.LanguageDef.ExactRuleSelectorCompilation
import Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation

/-!
# Prepared equation compilation

An exactly selected equation with a flat, linear parameter vector and a
range-restricted body can be lowered to positional slots.  The compiled
machine reads argument slots directly; it does not construct or search a
substitution environment.

The source semantics is independent: an arbitrary substitution models the
ordered parameter/argument relation.  The main theorem proves that slot
execution agrees with template instantiation for every such model.  Missing
body variables and repeated parameters fail closed during compilation.
-/

namespace Mettapedia.GSLT.LanguageDef.PreparedEquationCompilation

open Mettapedia.GSLT.LanguageDef.FirstOrderFrameCompilation

universe uKey uToken uVar

variable {Key : Type uKey} {Token : Type uToken} {Var : Type uVar}

/-- A physical body cell after parameter names have been erased. -/
inductive SlotAtom (Token : Type uToken) where
  | literal (token : Token)
  | slot (index : Nat)
deriving DecidableEq, Repr

abbrev SlotTemplate (Token : Type uToken) := List (SlotAtom Token)

/-- First position of a parameter in the authored ordered vector. -/
def findPosition? [DecidableEq Var] (needle : Var) : List Var → Option Nat
  | [] => none
  | parameter :: parameters =>
      if needle = parameter then some 0
      else (findPosition? needle parameters).map Nat.succ

/-- Lower every body variable to its admitted positional slot. -/
def lowerTemplate? [DecidableEq Var] (parameters : List Var) :
    Template Token Var → Option (SlotTemplate Token)
  | [] => some []
  | .literal token :: body =>
      match lowerTemplate? parameters body with
      | none => none
      | some tail => some (.literal token :: tail)
  | .hole holeId :: body =>
      match findPosition? holeId parameters with
      | none => none
      | some slot =>
          match lowerTemplate? parameters body with
          | none => none
          | some tail => some (.slot slot :: tail)

/-- Read one physical positional slot. -/
def getSlot? : List (Formula Token) → Nat → Option (Formula Token)
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: values, index + 1 => getSlot? values index

/-- Execute the compact positional body. -/
def runSlots (arguments : List (Formula Token)) :
    SlotTemplate Token → Option (Formula Token)
  | [] => some []
  | .literal token :: body => do
      let tail ← runSlots arguments body
      pure (token :: tail)
  | .slot index :: body => do
      let image ← getSlot? arguments index
      let tail ← runSlots arguments body
      pure (image ++ tail)

/-- Declarative source relation between ordered parameters, arguments, and an
otherwise arbitrary substitution. -/
def ModelsArguments (σ : Substitution Var Token) :
    List Var → List (Formula Token) → Prop
  | [], [] => True
  | parameter :: parameters, argument :: arguments =>
      σ parameter = some argument ∧
        ModelsArguments σ parameters arguments
  | _, _ => False

theorem ModelsArguments.length_eq
    (σ : Substitution Var Token) (parameters : List Var)
    (arguments : List (Formula Token))
    (models : ModelsArguments σ parameters arguments) :
    parameters.length = arguments.length := by
  induction parameters generalizing arguments with
  | nil =>
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          simp [ModelsArguments] at models
  | cons parameter parameters ih =>
      cases arguments with
      | nil => simp [ModelsArguments] at models
      | cons argument arguments =>
          simp only [ModelsArguments] at models
          simp [ih arguments models.2]

theorem findPosition?_models_getSlot?
    [DecidableEq Var]
    (σ : Substitution Var Token) (parameters : List Var)
    (arguments : List (Formula Token)) (holeId : Var) (index : Nat)
    (models : ModelsArguments σ parameters arguments)
    (found : findPosition? holeId parameters = some index) :
    σ holeId = getSlot? arguments index := by
  induction parameters generalizing arguments index with
  | nil => simp [findPosition?] at found
  | cons parameter parameters ih =>
      cases arguments with
      | nil => simp [ModelsArguments] at models
      | cons argument arguments =>
          obtain ⟨headModel, tailModels⟩ := models
          by_cases same : holeId = parameter
          · subst holeId
            simp [findPosition?] at found
            cases found
            simpa [getSlot?] using headModel
          · simp only [findPosition?, same, ↓reduceIte] at found
            cases tailFound : findPosition? holeId parameters with
            | none => simp [tailFound] at found
            | some tailIndex =>
                simp [tailFound] at found
                cases found
                simpa [getSlot?] using
                  ih arguments tailIndex tailModels tailFound

/-- Positional lowering preserves the independent source substitution
semantics. -/
theorem runSlots_eq_instantiate_of_lowerTemplate?
    [DecidableEq Var]
    (σ : Substitution Var Token) (parameters : List Var)
    (arguments : List (Formula Token)) (body : Template Token Var)
    (compiled : SlotTemplate Token)
    (models : ModelsArguments σ parameters arguments)
    (accepted : lowerTemplate? parameters body = some compiled) :
    runSlots arguments compiled = instantiate σ body := by
  induction body generalizing compiled with
  | nil =>
      simp [lowerTemplate?] at accepted
      subst compiled
      rfl
  | cons atom body ih =>
      cases atom with
      | literal token =>
          simp only [lowerTemplate?] at accepted
          cases tailEq : lowerTemplate? parameters body with
          | none => simp [tailEq] at accepted
          | some tail =>
              simp [tailEq] at accepted
              subst compiled
              rw [runSlots, instantiate, ih tail tailEq]
      | hole holeId =>
          simp only [lowerTemplate?] at accepted
          cases positionEq : findPosition? holeId parameters with
          | none => simp [positionEq] at accepted
          | some position =>
              cases tailEq : lowerTemplate? parameters body with
              | none => simp [positionEq, tailEq] at accepted
              | some tail =>
                  simp [positionEq, tailEq] at accepted
                  subst compiled
                  have imageEq := findPosition?_models_getSlot?
                    σ parameters arguments holeId position models positionEq
                  rw [runSlots, instantiate, imageEq]
                  rw [ih tail tailEq]

/-- Authored singleton-equation fragment. -/
structure SourceEquation (Key : Type uKey) (Token : Type uToken)
    (Var : Type uVar) where
  key : Key
  parameters : List Var
  body : Template Token Var

/-- Physical equation plan: names are erased from the hot body. -/
structure PreparedEquation (Key : Type uKey) (Token : Type uToken) where
  key : Key
  arity : Nat
  body : SlotTemplate Token
deriving DecidableEq, Repr

/-- Admit only flat linear heads whose bodies mention declared parameters. -/
def compileEquation? [DecidableEq Var]
    (source : SourceEquation Key Token Var) :
    Option (PreparedEquation Key Token) :=
  if source.parameters.Nodup then
    match lowerTemplate? source.parameters source.body with
    | none => none
    | some body =>
        some { key := source.key,
               arity := source.parameters.length,
               body := body }
  else none

/-- One physical equation accepts only its exact call arity. -/
def runPrepared (prepared : PreparedEquation Key Token)
    (arguments : List (Formula Token)) : Option (Formula Token) :=
  if arguments.length = prepared.arity then
    runSlots arguments prepared.body
  else none

/-- The compiled equation returns exactly source instantiation under every
substitution satisfying its ordered parameter relation. -/
theorem runPrepared_eq_instantiate_of_compileEquation?
    [DecidableEq Var]
    (source : SourceEquation Key Token Var)
    (prepared : PreparedEquation Key Token)
    (accepted : compileEquation? source = some prepared)
    (σ : Substitution Var Token) (arguments : List (Formula Token))
    (models : ModelsArguments σ source.parameters arguments) :
    runPrepared prepared arguments = instantiate σ source.body := by
  unfold compileEquation? at accepted
  split at accepted
  · rename_i linear
    cases bodyEq : lowerTemplate? source.parameters source.body with
    | none => simp [bodyEq] at accepted
    | some body =>
        simp [bodyEq] at accepted
        cases accepted
        have lengths : arguments.length = source.parameters.length :=
          (ModelsArguments.length_eq
            σ source.parameters arguments models).symm
        unfold runPrepared
        rw [if_pos lengths]
        exact runSlots_eq_instantiate_of_lowerTemplate?
          σ source.parameters arguments source.body body models bodyEq
  · contradiction

/-! ## Generated admission contract and canonical fallback -/

/-- Evidence carried by the generated CeTTa admission contract.  The first
three fields describe the equation fragment; the latter three describe the
current store and call boundary. -/
structure AdmissionEvidence where
  singletonHead : Bool
  flatLinearLhs : Bool
  rangeRestrictedRhs : Bool
  revisionCurrent : Bool
  groundCall : Bool
  callPolicySupported : Bool
deriving DecidableEq, Repr

/-- Plan admission mirrors the generated rule-machine contract.  Groundness
is intentionally absent: it is evidence about a particular call, not the
prepared equation. -/
def planAdmitted (evidence : AdmissionEvidence) : Bool :=
  evidence.singletonHead &&
  evidence.flatLinearLhs &&
  evidence.rangeRestrictedRhs &&
  evidence.revisionCurrent &&
  evidence.callPolicySupported

/-- A direct call additionally requires a ground argument vector. -/
def callAdmitted (evidence : AdmissionEvidence) : Bool :=
  planAdmitted evidence && evidence.groundCall

/-- Execute the positional plan only when the generated contract admits this
call.  Otherwise retain the canonical substitution semantics. -/
def runAdmittedOrSource
    (evidence : AdmissionEvidence)
    (source : SourceEquation Key Token Var)
    (prepared : PreparedEquation Key Token)
    (σ : Substitution Var Token)
    (arguments : List (Formula Token)) : Option (Formula Token) :=
  if callAdmitted evidence then
    runPrepared prepared arguments
  else
    instantiate σ source.body

/-- The admission decision changes the implementation route, never the
observable equation result. -/
theorem runAdmittedOrSource_eq_instantiate_of_compileEquation?
    [DecidableEq Var]
    (evidence : AdmissionEvidence)
    (source : SourceEquation Key Token Var)
    (prepared : PreparedEquation Key Token)
    (accepted : compileEquation? source = some prepared)
    (σ : Substitution Var Token) (arguments : List (Formula Token))
    (models : ModelsArguments σ source.parameters arguments) :
    runAdmittedOrSource evidence source prepared σ arguments =
      instantiate σ source.body := by
  unfold runAdmittedOrSource
  split
  · exact runPrepared_eq_instantiate_of_compileEquation?
      source prepared accepted σ arguments models
  · rfl

/-! ## Exact-selector composition and fail-closed witnesses -/

/-- Compiled equations use their authored head as the exact selector key. -/
def preparedKey? (prepared : PreparedEquation Key Token) : Option Key :=
  some prepared.key

private def sample : SourceEquation Nat Nat Nat where
  key := 17
  parameters := [0, 1]
  body := [.literal 9, .hole 0, .hole 0, .hole 1]

private def samplePrepared : PreparedEquation Nat Nat where
  key := 17
  arity := 2
  body := [.literal 9, .slot 0, .slot 0, .slot 1]

private def fullEvidence : AdmissionEvidence where
  singletonHead := true
  flatLinearLhs := true
  rangeRestrictedRhs := true
  revisionCurrent := true
  groundCall := true
  callPolicySupported := true

/-- The complete generated evidence package admits the direct route. -/
example : callAdmitted fullEvidence = true := by decide

/-- Every individual plan fact is load-bearing and fails closed. -/
example :
    planAdmitted { fullEvidence with singletonHead := false } = false ∧
    planAdmitted { fullEvidence with flatLinearLhs := false } = false ∧
    planAdmitted { fullEvidence with rangeRestrictedRhs := false } = false ∧
    planAdmitted { fullEvidence with revisionCurrent := false } = false ∧
    planAdmitted { fullEvidence with callPolicySupported := false } = false := by
  decide

/-- A prepared plan is not enough to license a nonground call. -/
example :
    callAdmitted { fullEvidence with groundCall := false } = false := by
  decide

/-- A linear, range-restricted equation lowers to slots. -/
example : compileEquation? sample = some samplePrepared := by decide

/-- Repeated parameters are equality constraints, not positional slots. -/
example :
    compileEquation?
      ({ key := 17, parameters := [0, 0], body := [.hole 0] } :
        SourceEquation Nat Nat Nat) = none := by decide

/-- An open body cannot enter the direct machine. -/
example :
    compileEquation?
      ({ key := 17, parameters := [0, 1], body := [.hole 2] } :
        SourceEquation Nat Nat Nat) = none := by decide

/-- Exact selection rejects two prepared equations with the same head. -/
example :
    ExactRuleSelectorCompilation.compile? preparedKey?
      [samplePrepared, samplePrepared] = none := by decide

/-- A wrong call arity fails closed. -/
example : runPrepared samplePrepared [[3]] = none := by decide

end Mettapedia.GSLT.LanguageDef.PreparedEquationCompilation
