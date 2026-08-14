import Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation
import Mettapedia.GSLT.LanguageDef.ConstructorGuidedUnificationCompilation

/-!
# Open activation views for compiled plans

`CompiledPlanActivationViewCompilation` proves exactness for range-restricted
producers, whose body slots are all ground after matching the rule head.  A
finite-Horn body may also introduce rule-local logic variables.  The native
machine represents such a variable by its rule-instance generation and dense
slot rather than materializing the whole body.

This module isolates that extra semantic case.  It gives open instantiation a
typed carrier, proves that it conservatively extends the existing ground
semantics, and supplies a decidable structural recognizer.  It also connects
rigid open roots to the existing proved Martelli--Montanari decomposition.
The recognizer is intentionally not wired into physical admission here: that
requires the separate recursive matcher/rollback refinement.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation

open CompiledPlanAdmission
open CompiledPlanLowering
open CompiledPlanTermSemantics
open CompiledPlanActivationViewCompilation

/-! ## Generation-qualified open values -/

/-- A rule-local variable is identified by both the rule-instance generation
and its dense plan slot.  Reusing the same slot in two generations cannot
alias the variables. -/
structure LogicVariable where
  generation : UInt32
  slot : UInt32
  deriving DecidableEq, Repr

mutual

/-- A first-order value that may retain generation-qualified logic variables. -/
inductive OpenTerm where
  | symbol (name : List UInt8)
  | variable (name : LogicVariable)
  | string (value : List UInt8)
  | integer (value : Int64)
  | application (head : List UInt8) (arguments : OpenTerms)
  deriving DecidableEq, Repr

inductive OpenTerms where
  | nil
  | cons (head : OpenTerm) (tail : OpenTerms)
  deriving DecidableEq, Repr

end

/-- A frozen rule-instance environment.  Missing entries remain open at the
current generation instead of failing instantiation. -/
abbrev OpenEnvironment := UInt32 -> Option OpenTerm

mutual

/-- Instantiate a plan term without forcing unbound rule-local variables. -/
def instantiateOpen (generation : UInt32) (environment : OpenEnvironment) :
    Term -> OpenTerm
  | .symbol name => .symbol name
  | .variable slot =>
      match environment slot with
      | some value => value
      | none => .variable { generation, slot }
  | .string value => .string value
  | .integer value => .integer value
  | .application head arguments =>
      .application head (instantiateOpenTerms generation environment arguments)

def instantiateOpenTerms (generation : UInt32)
    (environment : OpenEnvironment) : Terms -> OpenTerms
  | .nil => .nil
  | .cons head tail =>
      .cons (instantiateOpen generation environment head)
        (instantiateOpenTerms generation environment tail)

end

mutual

/-- Embed one existing closed value into the open carrier. -/
def groundToOpen : GroundTerm -> OpenTerm
  | .symbol name => .symbol name
  | .string value => .string value
  | .integer value => .integer value
  | .application head arguments =>
      .application head (groundTermsToOpen arguments)

def groundTermsToOpen : GroundTerms -> OpenTerms
  | .nil => .nil
  | .cons head tail => .cons (groundToOpen head) (groundTermsToOpen tail)

end

/-- Lift the old ground substitution into the open environment. -/
def liftGround (substitution : Substitution) : OpenEnvironment :=
  fun slot => (substitution slot).map groundToOpen

mutual

/-- Open instantiation agrees with ground instantiation whenever the latter
succeeds.  This is the conservative-extension boundary for the new carrier. -/
theorem instantiateOpen_of_instantiateTerm
    (generation : UInt32) (substitution : Substitution)
    (source : Term) (ground : GroundTerm)
    (materialized : instantiateTerm substitution source = some ground) :
    instantiateOpen generation (liftGround substitution) source =
      groundToOpen ground := by
  cases source with
  | symbol name =>
      simp [instantiateTerm] at materialized
      cases materialized
      rfl
  | «variable» slot =>
      simp [instantiateTerm] at materialized
      simp [instantiateOpen, liftGround, materialized]
  | string value =>
      simp [instantiateTerm] at materialized
      cases materialized
      rfl
  | integer value =>
      simp [instantiateTerm] at materialized
      cases materialized
      rfl
  | application head arguments =>
      simp only [instantiateTerm] at materialized
      cases groundedArguments : instantiateTerms substitution arguments with
      | none => simp [groundedArguments] at materialized
      | some values =>
          simp [groundedArguments] at materialized
          cases materialized
          simp [instantiateOpen, groundToOpen,
            instantiateOpenTerms_of_instantiateTerms generation substitution
              arguments values groundedArguments]

theorem instantiateOpenTerms_of_instantiateTerms
    (generation : UInt32) (substitution : Substitution)
    (sources : Terms) (grounds : GroundTerms)
    (materialized : instantiateTerms substitution sources = some grounds) :
    instantiateOpenTerms generation (liftGround substitution) sources =
      groundTermsToOpen grounds := by
  cases sources with
  | nil =>
      simp [instantiateTerms] at materialized
      cases materialized
      rfl
  | cons sourceHead sourceTail =>
      simp only [instantiateTerms] at materialized
      cases headResult : instantiateTerm substitution sourceHead with
      | none => simp [headResult] at materialized
      | some groundHead =>
          cases tailResult : instantiateTerms substitution sourceTail with
          | none => simp [headResult, tailResult] at materialized
          | some groundTail =>
              simp [headResult, tailResult] at materialized
              cases materialized
              rw [instantiateOpenTerms]
              rw [instantiateOpen_of_instantiateTerm generation substitution
                sourceHead groundHead headResult]
              rw [instantiateOpenTerms_of_instantiateTerms generation substitution
                sourceTail groundTail tailResult]
              rfl

end

/-- An unbound slot remains present and generation-qualified. -/
example :
    instantiateOpen 7 (liftGround emptySubstitution) (.variable 3) =
      .variable { generation := 7, slot := 3 } := by
  rfl

/-- Equal dense slots from different rule instances remain distinct. -/
example :
    instantiateOpen 7 (liftGround emptySubstitution) (.variable 3) !=
      instantiateOpen 8 (liftGround emptySubstitution) (.variable 3) := by
  decide

/-! ## Decidable structural recognition -/

/-- The open recognizer removes only the ground/range-restriction premise.
Fixed outer construction and the no-capture consumer condition remain
mandatory. -/
structure OpenActivationViewPlan where
  source : Term
  deriving DecidableEq, Repr

def compileOpen? (source : Term) (consumerHeads : List Term) :
    Option OpenActivationViewPlan :=
  if (fixedApplicationHead? source).isSome &&
      consumerHeads.all (consumerSafe source) then
    some { source }
  else
    none

theorem compileOpen?_success
    (source : Term) (consumerHeads : List Term)
    (plan : OpenActivationViewPlan)
    (accepted : compileOpen? source consumerHeads = some plan) :
    (fixedApplicationHead? source).isSome = true ∧
      consumerHeads.all (consumerSafe source) = true ∧
      plan.source = source := by
  simp only [compileOpen?] at accepted
  split at accepted
  · rename_i admitted
    simp only [Bool.and_eq_true] at admitted
    cases accepted
    exact ⟨admitted.1, admitted.2, rfl⟩
  · contradiction

/-! ## Composition with speculative candidate effects -/

/-- Two environments agree on every slot read by one source term. -/
def AgreesOn (source : Term) (left right : OpenEnvironment) : Prop :=
  ∀ slot, slot ∈ usedSlots source -> left slot = right slot

mutual

/-- Open instantiation depends only on the slots named by its source. -/
theorem instantiateOpen_eq_of_agreesOn
    (generation : UInt32) (left right : OpenEnvironment)
    (source : Term) (agrees : AgreesOn source left right) :
    instantiateOpen generation left source =
      instantiateOpen generation right source := by
  cases source with
  | symbol name => rfl
  | «variable» slot =>
      have slotAgreement : left slot = right slot :=
        agrees slot (by simp [usedSlots])
      simp [instantiateOpen, slotAgreement]
  | string value => rfl
  | integer value => rfl
  | application head arguments =>
      rw [instantiateOpen, instantiateOpen]
      rw [instantiateOpenTerms_eq_of_agreesOn generation left right arguments]
      intro slot member
      exact agrees slot (by simpa [usedSlots] using member)

theorem instantiateOpenTerms_eq_of_agreesOn
    (generation : UInt32) (left right : OpenEnvironment)
    (sources : Terms)
    (agrees : ∀ slot, slot ∈ usedSlotsTerms sources ->
      left slot = right slot) :
    instantiateOpenTerms generation left sources =
      instantiateOpenTerms generation right sources := by
  cases sources with
  | nil => rfl
  | cons sourceHead sourceTail =>
      rw [instantiateOpenTerms, instantiateOpenTerms]
      rw [instantiateOpen_eq_of_agreesOn generation left right sourceHead]
      · rw [instantiateOpenTerms_eq_of_agreesOn generation left right sourceTail]
        intro slot member
        exact agrees slot (by simp [usedSlotsTerms, member])
      · intro slot member
        exact agrees slot (by simp [usedSlotsTerms, member])

end

/-- Candidate effects extend an environment when they preserve every binding
that was already present. -/
def Extends (before after : OpenEnvironment) : Prop :=
  ∀ slot value, before slot = some value -> after slot = some value

/-- Every source slot already denotes a closed-over open value before a
candidate begins.  This is the semantic license needed to inspect later
candidates under the post-match environment. -/
def FrozenAt (environment : OpenEnvironment) (source : Term) : Prop :=
  ∀ slot, slot ∈ usedSlots source -> ∃ value, environment slot = some value

/-- Executable pre-candidate recognizer for the composition license. -/
def frozen? (environment : OpenEnvironment) (source : Term) : Bool :=
  (usedSlots source).all fun slot => (environment slot).isSome

theorem frozen?_sound
    (environment : OpenEnvironment) (source : Term)
    (accepted : frozen? environment source = true) :
    FrozenAt environment source := by
  intro slot member
  have present := (List.all_eq_true.mp accepted) slot member
  cases result : environment slot with
  | none => simp [result] at present
  | some value => exact ⟨value, rfl⟩

theorem frozen_agrees_with_extension
    (before after : OpenEnvironment) (source : Term)
    (frozen : FrozenAt before source) (extension : Extends before after) :
    AgreesOn source before after := by
  intro slot member
  obtain ⟨value, present⟩ := frozen slot member
  rw [present, extension slot value present]

/-- A frozen activation view is invariant under append-only candidate effects.
This is why tail-determinism may be composed with the view only after the
pre-candidate `frozen?` gate succeeds. -/
theorem instantiateOpen_stable_of_frozen?
    (generation : UInt32) (before after : OpenEnvironment)
    (source : Term) (accepted : frozen? before source = true)
    (extension : Extends before after) :
    instantiateOpen generation before source =
      instantiateOpen generation after source :=
  instantiateOpen_eq_of_agreesOn generation before after source
    (frozen_agrees_with_extension before after source
      (frozen?_sound before source accepted) extension)

def emptyOpenEnvironment : OpenEnvironment := fun _ => none

def writeOpen (environment : OpenEnvironment) (slot : UInt32)
    (value : OpenTerm) : OpenEnvironment :=
  fun candidate => if candidate = slot then some value else environment candidate

/-- Without the frozen license, one speculative candidate can change the view
observed by a later-candidate classifier. -/
example :
    instantiateOpen 7 emptyOpenEnvironment (.variable 3) !=
      instantiateOpen 7
        (writeOpen emptyOpenEnvironment 3 (.symbol [9])) (.variable 3) := by
  decide

/-- The executable composition recognizer rejects that unfrozen slot. -/
example : frozen? emptyOpenEnvironment (.variable 3) = false := by
  decide

private def frozenCanaryEnvironment : OpenEnvironment
  | 3 => some (.symbol [9])
  | _ => none

/-- A source whose complete support is present earns the composition license. -/
example : frozen? frozenCanaryEnvironment
    (.application [1] (.cons (.variable 3) .nil)) = true := by
  decide

/-! ## Open rigid-root decomposition -/

inductive OpenConstant where
  | symbol (name : List UInt8)
  | string (value : List UInt8)
  | integer (value : Int64)
  deriving DecidableEq, Repr

structure OpenFunctionSymbol where
  head : List UInt8
  arity : Nat
  deriving DecidableEq, Repr

structure OpenRelationSymbol where
  head : List UInt8
  arity : Nat
  deriving DecidableEq, Repr

abbrev openSignature : Mettapedia.Logic.LP.LPSignature where
  constants := OpenConstant
  vars := LogicVariable
  relationSymbols := OpenRelationSymbol
  relationArity := OpenRelationSymbol.arity
  functionSymbols := OpenFunctionSymbol
  functionArity := OpenFunctionSymbol.arity

mutual

def encodeOpenTerm : OpenTerm -> Mettapedia.Logic.LP.Term openSignature
  | .symbol name => .const (.symbol name)
  | .variable name => .var name
  | .string value => .const (.string value)
  | .integer value => .const (.integer value)
  | .application head arguments =>
      let encoded := encodeOpenTerms arguments
      .app { head, arity := encoded.length } fun index => encoded.get index

def encodeOpenTerms : OpenTerms ->
    List (Mettapedia.Logic.LP.Term openSignature)
  | .nil => []
  | .cons head tail => encodeOpenTerm head :: encodeOpenTerms tail

end

abbrev OpenEquation :=
  ConstructorGuidedUnificationCompilation.Equation openSignature

def decomposeOpenRoot? (left right : OpenTerm)
    (rest : List OpenEquation) : Option (List OpenEquation) :=
  ConstructorGuidedUnificationCompilation.decompose?
    (encodeOpenTerm left) (encodeOpenTerm right) rest

/-- A recognized open rigid root performs exactly the ordinary unifier's
constructor step.  The theorem is independent of whether descendants are
ground, bound, or generation-qualified variables. -/
theorem unifyFuel_decomposeOpenRoot?
    (fuel : Nat) (left right : OpenTerm)
    (rest equations : List OpenEquation)
    (accepted : decomposeOpenRoot? left right rest = some equations) :
    Mettapedia.Logic.LP.unifyFuel (fuel + 1)
        ((encodeOpenTerm left, encodeOpenTerm right) :: rest) =
      Mettapedia.Logic.LP.unifyFuel fuel equations :=
  ConstructorGuidedUnificationCompilation.unifyFuel_decompose?
    fuel (encodeOpenTerm left) (encodeOpenTerm right) rest equations accepted

/-! ## Independent witnesses and rejection boundaries -/

private def parserOpenBody : Term :=
  .application [11]
    (.cons (.variable 0) (.cons (.variable 1) .nil))

private def parserConsumer : Term :=
  .application [11]
    (.cons (.variable 0) (.cons (.symbol [2]) .nil))

private def proofOpenBody : Term :=
  .application [21]
    (.cons (.symbol [4]) (.cons (.variable 9) .nil))

private def proofConsumer : Term :=
  .application [21]
    (.cons (.symbol [4]) (.cons (.variable 0) .nil))

/-- A parser-like body with a rule-local variable is structurally admitted. -/
example : (compileOpen? parserOpenBody [parserConsumer]).isSome = true := by
  decide

/-- The same recognizer admits an independently shaped proof-step body. -/
example : (compileOpen? proofOpenBody [proofConsumer]).isSome = true := by
  decide

/-- A consumer that captures a variable-bearing constructed subtree is
rejected. -/
example :
    (compileOpen?
      (.application [11]
        (.cons (.application [12] (.cons (.variable 1) .nil)) .nil))
      [.application [11] (.cons (.variable 0) .nil)]).isSome = false := by
  decide

/-- A variable-headed consumer remains outside open activation admission. -/
example : (compileOpen? parserOpenBody [.variable 0]).isSome = false := by
  decide

private def openParserLeft : OpenTerm :=
  .application [11]
    (.cons (.variable { generation := 7, slot := 0 })
      (.cons (.symbol [2]) .nil))

private def openParserRight : OpenTerm :=
  .application [11]
    (.cons (.symbol [3])
      (.cons (.variable { generation := 8, slot := 0 }) .nil))

/-- Open descendants do not prevent rigid-root decomposition. -/
example :
    (decomposeOpenRoot? openParserLeft openParserRight []).isSome = true := by
  decide

/-- A rigid head disagreement fails closed before unification. -/
example :
    (decomposeOpenRoot? openParserLeft
      (.application [99]
        (.cons (.symbol [3])
          (.cons (.variable { generation := 8, slot := 0 }) .nil)))
      []).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation
