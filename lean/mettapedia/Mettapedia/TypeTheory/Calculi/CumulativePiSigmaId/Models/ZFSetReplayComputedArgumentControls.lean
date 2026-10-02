import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayIdentityComparisonControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputedArgument

/-!
# Computed universe arguments at arbitrary finite depth

Nested identity applications have two independently checked certificate
families: lower-universe applications followed by result cumulativity, or
upper-universe applications whose initial variable was raised. Each root beta
step computes the preceding certificate in its family. The depth parameter
is arbitrary; no fixed normalization bound is substituted for the induction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedArgumentControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetDependentProducts (graph sigmaSet)
open ZFSetTraceProducts (traceLam traceApp traceApp_graph_beta)
open ZFSetTraceProofDecoding (truthCode mem_truthCode)
open ZFSetReplayApplicationComparisonControls (context contextCode context_checked context_assembles valid)

universe u

private abbrev zero : Tower.Head := .sort Tower.zero
private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def program : Nat → Tower.Tm 1
  | 0 => .var 0
  | depth + 1 => .app (.lam (.var 0)) (program depth)

def identityCode (level : LevelExpr Nat) : Replay 1 :=
  .lamIntro (.sort (.max (.succ level) (.succ level)))
    (.piForm (.sort (.succ level)) (.sort (.succ level)) .headType .headType) .var

def lowerCode : Nat → Replay 1
  | 0 => .var
  | depth + 1 => .appElim (.head zero) (.head zero) (identityCode Tower.zero) (lowerCode depth)

def raisedLowerCode (depth : Nat) : Replay 1 := .cumul zero (lowerCode depth)

def upperCode : Nat → Replay 1
  | 0 => .cumul zero .var
  | depth + 1 => .appElim (.head one) (.head one) (identityCode (.succ Tower.zero)) (upperCode depth)

theorem lower_checked (depth : Nat) : check Tower.rules noConversionCheck context
    (program depth) (.head zero) (lowerCode depth) = true := by
  induction depth with
  | zero => decide
  | succ depth ih =>
      change ((true && check Tower.rules noConversionCheck context (program depth)
        (.head zero) (lowerCode depth)) && true) = true
      simpa only [Bool.true_and, Bool.and_true] using ih

theorem raised_lower_checked (depth : Nat) : check Tower.rules noConversionCheck context
    (program depth) (.head one) (raisedLowerCode depth) = true := by
  change (check Tower.rules noConversionCheck context (program depth) (.head zero) (lowerCode depth) && true) = true
  simpa only [Bool.and_true] using lower_checked depth

theorem upper_checked (depth : Nat) : check Tower.rules noConversionCheck context
    (program depth) (.head one) (upperCode depth) = true := by
  induction depth with
  | zero => decide
  | succ depth ih =>
      change ((true && check Tower.rules noConversionCheck context (program depth)
        (.head one) (upperCode depth)) && true) = true
      simpa only [Bool.true_and, Bool.and_true] using ih

theorem lower_contracts (depth : Nat) :
    (lowerCode (depth + 1)).contractBeta (.var 0) (program depth) (.head zero) =
      some (lowerCode depth) := rfl

theorem raised_lower_contracts (depth : Nat) :
    (raisedLowerCode (depth + 1)).contractBeta (.var 0) (program depth) (.head one) =
      some (raisedLowerCode depth) := rfl

theorem upper_contracts (depth : Nat) :
    (upperCode (depth + 1)).contractBeta (.var 0) (program depth) (.head one) =
      some (upperCode depth) := rfl

theorem terminal_codes_equal : raisedLowerCode 0 = upperCode 0 := rfl

theorem nonzero_codes_differ (depth : Nat) : raisedLowerCode (depth + 1) ≠ upperCode (depth + 1) := by
  intro equal
  cases equal

theorem nonzero_program_not_neutral (depth : Nat) : (program (depth + 1)).neutral = false := rfl

/-- Replacing the certificate for a genuinely computed argument by a
variable certificate is rejected, even though the eventual value is that
variable. Checking does not silently normalize the supplied derivation. -/
theorem forged_computed_argument_rejected (depth : Nat) : check Tower.rules noConversionCheck context
    (program (depth + 1)) (.head one) (.cumul zero (Code.var : Replay 1)) = false := rfl

private theorem identity_step_trace (level : LevelExpr Nat) (argument : Tower.Tm 1)
    (argumentCode terminal : Replay 1)
    (trace : BetaToVariable argument (.head (.sort level)) argumentCode 0 terminal) :
    BetaToVariable (.app (.lam (.var 0)) argument) (.head (.sort level))
      (.appElim (.head (.sort level)) (.head (.sort level)) (identityCode level) argumentCode) 0 terminal :=
  .beta (Head := Tower.Head) (n := 1) (argument := argument)
    (argumentCode := argumentCode) (argumentTerminal := terminal)
    (A := .head (.sort level)) (B := .head (.sort level)) (body := .var 0)
    (level := .sort (.max (.succ level) (.succ level)))
    (domainLevel := .sort (.succ level)) (bodyLevel := .sort (.succ level))
    (formation := .piForm (.sort (.succ level)) (.sort (.succ level)) .headType .headType)
    (domainCode := .headType) (codomainCode := .headType) (bodyCode := .var) rfl rfl trace trace

theorem lower_trace (depth : Nat) : BetaToVariable (program depth) (.head zero) (lowerCode depth) 0 .var := by
  induction depth with
  | zero => exact .var 0 _ _
  | succ depth ih => exact identity_step_trace Tower.zero _ _ _ ih

theorem raised_lower_trace (depth : Nat) :
    BetaToVariable (program depth) (.head one) (raisedLowerCode depth) 0 (.cumul zero .var) :=
  .cumulative (lower_trace depth)

theorem upper_trace (depth : Nat) :
    BetaToVariable (program depth) (.head one) (upperCode depth) 0 (.cumul zero .var) := by
  induction depth with
  | zero => exact .var 0 _ _
  | succ depth ih => exact identity_step_trace (.succ Tower.zero) _ _ _ ih

theorem terminal_checked_from_trace (depth : Nat) : check Tower.rules noConversionCheck context
    (.var 0) (.head one) (.cumul zero (Code.var : Replay 1)) = true :=
  (raised_lower_trace depth).terminal_checked Tower.rules (raised_lower_checked depth)

theorem program_reduces (depth : Nat) :
    Relation.ReflTransGen (StepCore Tower.rules.computation Tower.rules.headEq) (program depth) (.var 0) :=
  (upper_trace depth).reduces Tower.rules

def forgedStepCode : Replay 1 :=
  .appElim (.head one) (.head one) (identityCode (.succ Tower.zero)) .var

/-- The trace records computation, not typing authority: omitting the
required cumulative argument rule still admits a structural trace, while
both the source and its retained terminal certificate are rejected. -/
theorem trace_does_not_authorize_source :
    BetaToVariable (program 1) (.head one) forgedStepCode 0 .var ∧
      check Tower.rules noConversionCheck context (program 1) (.head one) forgedStepCode = false ∧
      check Tower.rules noConversionCheck context (.var 0) (.head one) (Code.var : Replay 1) = false := by
  exact ⟨identity_step_trace (.succ Tower.zero) _ _ _ (.var 0 _ _), by decide, by decide⟩

theorem producer_positive_controls :
    ((raisedLowerCode 1).betaToVariable? 3 (program 1) (.head one)).isSome = true ∧
      ((raisedLowerCode 3).betaToVariable? 5 (program 3) (.head one)).isSome = true ∧
      ((upperCode 3).betaToVariable? 5 (program 3) (.head one)).isSome = true := by decide

/-- A body returning the older variable is not the identity shortcut. The
general branch still computes its argument and then its distinct reduct. -/
theorem producer_nonidentity_fallback :
    let term : Tower.Tm 1 := .app (.lam (.var 1)) (program 1)
    let code : Replay 1 := .appElim (.head zero) (.head zero) (identityCode Tower.zero) (lowerCode 1)
    check Tower.rules noConversionCheck context term (.head zero) code = true ∧
      (code.betaToVariable? 4 term (.head zero)).isSome = true := by decide

/-- Search failure includes fuel exhaustion and unsupported syntax; neither
case is an alternative rejection rule for the type checker. -/
theorem producer_cutoff_and_unsupported :
    ((raisedLowerCode 3).betaToVariable? 0 (program 3) (.head one)).isNone = true ∧
      ((Code.headType : Replay 1).betaToVariable? 5 (.head zero) (.head one)).isNone = true ∧
      check Tower.rules noConversionCheck context (.head zero) (.head one) (Code.headType : Replay 1) = true := by
  decide

theorem producer_success_is_not_authority :
    (forgedStepCode.betaToVariable? 3 (program 1) (.head one)).isSome = true ∧
      check Tower.rules noConversionCheck context (program 1) (.head one) forgedStepCode = false := by decide

def generatedThree : { result : Fin 1 × Replay 1 //
    BetaToVariable (program 3) (.head one) (raisedLowerCode 3) result.1 result.2 } :=
  ((raisedLowerCode 3).betaToVariable? 5 (program 3) (.head one)).get (by decide)

theorem generated_three_coordinates : generatedThree.val = (0, .cumul zero .var) := rfl

noncomputable def iteratedValue (h : CofinalInaccessibles.{u}) (level : Nat) : Nat → ZFSet.{u} → ZFSet.{u}
  | 0, x => x
  | depth + 1, x => traceApp (traceLam (graph (universeSet h ∅ level) id)) (iteratedValue h level depth x)

noncomputable def programMeaning (h : CofinalInaccessibles.{u}) (level depth : Nat) : Meaning.{u} 1 :=
  .plain (fun env => iteratedValue h level depth (env 0))

theorem lower_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (lowerCode depth) (program depth) (.head zero) = some (programMeaning h 0 depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [lowerCode, program, identityCode, assemble, Option.pure_def, ih]
      rfl

theorem raised_lower_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (raisedLowerCode depth) (program depth) (.head one) = some (programMeaning h 0 depth) :=
  lower_assembles h constants depth

theorem upper_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (upperCode depth) (program depth) (.head one) = some (programMeaning h 1 depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [upperCode, program, identityCode, assemble, Option.pure_def, ih]
      rfl

theorem iterated_value_of_member (h : CofinalInaccessibles.{u}) (level depth : Nat)
    (x : ZFSet.{u}) (inside : x ∈ universeSet h ∅ level) : iteratedValue h level depth x = x := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [iteratedValue, ih]
      exact traceApp_graph_beta _ inside

private theorem heads_monotone (h : CofinalInaccessibles.{u}) : ∀ a b,
    Tower.rules.cumulative a b → interpretHead h ∅ (twoCode h).1 (fun _ => 0) a ⊆
      interpretHead h ∅ (twoCode h).1 (fun _ => 0) b :=
  fun _ _ below => ZFSetReplayUniverseFormation.cumulative_subset h ∅ (twoCode h).1 (fun _ => 0) below

theorem computed_values_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) (env : Environment.{u} 1)
    (admitted : valid h env) : (programMeaning h 0 depth).value env = (programMeaning h 1 depth).value env :=
  BetaToVariable.values_agree (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    Tower.rules (heads_monotone h) (raised_lower_trace depth) (upper_trace depth) contextCode
    context_checked (raised_lower_checked depth) (upper_checked depth) (context_assembles h constants)
    (programMeaning h 0 depth) (programMeaning h 1 depth)
    (raised_lower_assembles h constants depth) (upper_assembles h constants depth) env admitted

/-- Consume the trace returned by the executable producer, not the separately
inductive construction of traces for this family. -/
theorem generated_trace_value (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (env : Environment.{u} 1) (admitted : valid h env) :
    (programMeaning h 0 3).value env = env 0 :=
  BetaToVariable.value (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants Tower.rules
    (heads_monotone h) generatedThree.property contextCode context_checked (raised_lower_checked 3)
    (context_assembles h constants) (programMeaning h 0 3) (raised_lower_assembles h constants 3) env admitted

/-- The validity premise cannot be dropped: feeding a universe to the lower
identity outside its declared domain loses its value, while the upper
identity is defined there. These inputs do not inhabit the source context. -/
theorem invalid_input_values (h : CofinalInaccessibles.{u}) :
    ¬ valid h (fun _ => universeSet h ∅ 0) ∧
      (programMeaning h 0 1).value (fun _ => universeSet h ∅ 0) = ∅ ∧
      (programMeaning h 1 1).value (fun _ => universeSet h ∅ 0) = universeSet h ∅ 0 := by
  refine ⟨fun admitted => universeSet_no_self_membership h ∅ 0 admitted.2, ?_,
    traceApp_graph_beta _ (universeSet_mem_next h ∅ 0)⟩
  apply ZFSet.ext
  intro z
  change z ∈ traceApp (traceLam (graph (universeSet h ∅ 0) id)) (universeSet h ∅ 0) ↔ _
  rw [ZFSetTraceProducts.mem_traceApp, ZFSetTraceProducts.pair_mem_traceLam]
  constructor
  · rintro ⟨value, member, _⟩
    exact (universeSet_no_self_membership h ∅ 0
      (ZFSetDependentProducts.pair_mem_graph.mp member).1).elim
  · exact fun impossible => (ZFSet.notMem_empty z impossible).elim

theorem invalid_input_distinguishes (h : CofinalInaccessibles.{u}) :
    (programMeaning h 0 1).value (fun _ => universeSet h ∅ 0) ≠
      (programMeaning h 1 1).value (fun _ => universeSet h ∅ 0) := by
  obtain ⟨_, lower, upper⟩ := invalid_input_values h
  rw [lower, upper]
  intro equal
  have member := seed_mem_universeSet h (∅ : ZFSet.{u}) (0 : Nat)
  rw [← equal] at member
  exact ZFSet.notMem_empty _ member

namespace DependentFamily

private abbrev level : Tower.Head := .sort (.succ (.succ Tower.zero))

def family : Tower.Tm 2 := .id (.head one) (.var 0) (.var 0)
def familyCode : Replay 2 := .idForm level .headType .var .var

theorem family_checked : check Tower.rules noConversionCheck (.snoc context (.head one))
    family (.head level) familyCode = true := by decide

def sourceFormation (depth : Nat) : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute family (.head level)
    (program depth) familyCode (raisedLowerCode depth)

def terminalFormation : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute family (.head level)
    (.var 0) familyCode (.cumul zero .var)

/-- Both certificates here are actually generated by substitution. Equality
of their semantic fibres does not add a conversion rule to the checker. -/
theorem generated_formations_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    check Tower.rules noConversionCheck context (inst0 (program depth) family) (.head level)
      (sourceFormation depth) = true ∧
    check Tower.rules noConversionCheck context (inst0 (.var 0) family) (.head level)
      terminalFormation = true ∧
    ∃ left right,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (sourceFormation depth) (inst0 (program depth) family) (.head level) = some left ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        terminalFormation (inst0 (.var 0) family) (.head level) = some right ∧
      ∀ env, valid h env → left.value env = right.value env :=
  BetaToVariable.family_values (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    Tower.rules (heads_monotone h) (raised_lower_trace depth) contextCode context_checked
    (raised_lower_checked depth) (context_assembles h constants) family level familyCode family_checked

theorem terminal_reflexivity_checked :
    check Tower.rules noConversionCheck context (.refl (.var 0)) (inst0 (.var 0) family)
      (.reflIntro (.head one) (.cumul zero (Code.var : Replay 1))) = true := by decide

theorem unreduced_family_rejects_terminal_reflexivity (depth : Nat) :
    check Tower.rules noConversionCheck context (.refl (.var 0)) (inst0 (program (depth + 1)) family)
      (.reflIntro (.head one) (.cumul zero (Code.var : Replay 1))) = false := by
  rfl

/-- Unlike a reflexive family, this fibre compares the argument with the
older context variable. Its value therefore depends on the argument. -/
def anchoredFamily : Tower.Tm 2 := .id (.head one) (.var 0) (.var 1)
def anchoredCode : Replay 2 := .idForm level .headType .var (.cumul zero .var)
private abbrev higherLevel : Tower.Head := .sort (.succ (.succ (.succ Tower.zero)))
def raisedAnchoredCode : Replay 2 := .cumul level anchoredCode

theorem anchored_checked : check Tower.rules noConversionCheck (.snoc context (.head one))
    anchoredFamily (.head level) anchoredCode = true := by decide

theorem raised_anchored_checked : check Tower.rules noConversionCheck (.snoc context (.head one))
    anchoredFamily (.head higherLevel) raisedAnchoredCode = true := by decide

def anchoredSource (depth : Nat) : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute anchoredFamily (.head level)
    (program depth) anchoredCode (raisedLowerCode depth)
def anchoredAlternative (depth : Nat) : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute anchoredFamily (.head higherLevel)
    (program depth) raisedAnchoredCode (upperCode depth)
def anchoredTerminal : Replay 1 :=
  Code.instantiate noConversionRename noConversionSubstitute anchoredFamily (.head level)
    (.var 0) anchoredCode (.cumul zero .var)

theorem anchored_original_qualified :
    anchoredCode.neutralEliminations anchoredFamily (.head level) = true := rfl

/-- Substitution destroys the earlier qualification, but not the comparison
which follows the exact instantiated certificates. -/
theorem anchored_instance_not_qualified (depth : Nat) :
    (anchoredSource (depth + 1)).neutralEliminations
      (inst0 (program (depth + 1)) anchoredFamily) (.head level) = false := rfl

theorem independent_anchored_formations (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    check Tower.rules noConversionCheck context (inst0 (program depth) anchoredFamily) (.head level)
      (anchoredSource depth) = true ∧
    check Tower.rules noConversionCheck context (inst0 (program depth) anchoredFamily) (.head higherLevel)
      (anchoredAlternative depth) = true ∧
    ∃ left right,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (anchoredSource depth) (inst0 (program depth) anchoredFamily) (.head level) = some left ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (anchoredAlternative depth) (inst0 (program depth) anchoredFamily) (.head higherLevel) = some right ∧
      ∀ env, valid h env → left.value env = right.value env :=
  BetaToVariable.independent_family_values (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    Tower.rules (heads_monotone h) (raised_lower_trace depth) (upper_trace depth) contextCode
    context_checked (raised_lower_checked depth) (upper_checked depth) (context_assembles h constants)
    anchoredFamily level higherLevel anchoredCode raisedAnchoredCode anchored_checked
    raised_anchored_checked anchored_original_qualified

/-- The checked context can store a witness of the fibre indexed by the
computed expression or by its returned variable. The same environments
inhabit both actual context assemblies. -/
theorem anchored_contexts_agree (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    checkContext Tower.rules noConversionCheck (.snoc context (inst0 (program depth) anchoredFamily))
      (.snoc contextCode level (anchoredSource depth)) = true ∧
    checkContext Tower.rules noConversionCheck (.snoc context (inst0 (.var 0) anchoredFamily))
      (.snoc contextCode level anchoredTerminal) = true ∧
    ∃ left right,
      assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (.snoc contextCode level (anchoredSource depth))
        (.snoc context (inst0 (program depth) anchoredFamily)) = some left ∧
      assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (.snoc contextCode level anchoredTerminal)
        (.snoc context (inst0 (.var 0) anchoredFamily)) = some right ∧
      left = right :=
  BetaToVariable.family_contexts (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    Tower.rules (heads_monotone h) (raised_lower_trace depth) contextCode context_checked
    (raised_lower_checked depth) (context_assembles h constants) anchoredFamily level (by decide)
    anchoredCode anchored_checked

theorem anchored_context_inhabited (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    ∃ environments,
      assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        (.snoc contextCode level (anchoredSource depth))
        (.snoc context (inst0 (program depth) anchoredFamily)) = some environments ∧
      environments (ZFSetTypeExpressionInterpretation.extend (fun _ => (twoCode h).1) ∅) := by
  obtain ⟨_, _, left, right, atLeft, atRight, equal⟩ := anchored_contexts_agree h constants depth
  refine ⟨left, atLeft, ?_⟩
  rw [equal]
  have terminalAssembled : assembleContext (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (.snoc contextCode level anchoredTerminal)
      (.snoc context (inst0 (.var 0) anchoredFamily)) =
      some (fun env : Environment.{u} 2 => valid h (env ∘ wk) ∧
        env 0 ∈ truthCode (env 1 = env 1)) := rfl
  rw [terminalAssembled] at atRight
  cases Option.some.inj atRight
  exact ⟨ZFSetReplayApplicationComparisonControls.nonempty_input_valid h,
    (mem_truthCode _ _).mpr ⟨rfl, rfl⟩⟩

end DependentFamily

namespace Consumer

open ZFSetReplayApplicationComparisonControls (pairType pairFormation body upperFormation upperBodyCode)

private abbrev pairLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))
private abbrev level : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero))))

def term (depth : Nat) : Tower.Tm 1 := .app (.lam body) (program depth)
def code (argument : Replay 1) : Replay 1 :=
  .appElim (.head one) pairType (.lamIntro level upperFormation upperBodyCode) argument

theorem checked (depth : Nat) (argument : Replay 1)
    (accepted : check Tower.rules noConversionCheck context (program depth) (.head one) argument = true) :
    check Tower.rules noConversionCheck context (term depth) pairType (code argument) = true := by
  change ((true && check Tower.rules noConversionCheck context (program depth) (.head one) argument) && true) = true
  simpa only [Bool.true_and, Bool.and_true] using accepted

noncomputable def meaning (h : CofinalInaccessibles.{u}) (argument : Meaning.{u} 1) : Meaning.{u} 1 :=
  .plain (fun env => traceApp (traceLam (graph (universeSet h ∅ 1) (fun x => ZFSet.pair x ∅)))
    (argument.value env))

theorem assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (depth : Nat) (argumentCode : Replay 1) (argument : Meaning.{u} 1)
    (atArgument : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      argumentCode (program depth) (.head one) = some argument) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (code argumentCode) (term depth) pairType = some (meaning h argument) := by
  simp only [code, term, assemble, upperFormation, pairFormation, upperBodyCode, atArgument,
    Option.pure_def]
  rfl

theorem argument_member (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (depth : Nat) (argumentCode terminal : Replay 1) (argument : Meaning.{u} 1)
    (trace : StructuralTypingReplay.BetaToVariable (program depth) (.head one) argumentCode 0 terminal)
    (accepted : check Tower.rules noConversionCheck context (program depth) (.head one) argumentCode = true)
    (atArgument : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      argumentCode (program depth) (.head one) = some argument)
    (env : Environment.{u} 1) (admitted : valid h env) : argument.value env ∈ universeSet h ∅ 1 :=
  BetaToVariable.membership (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants Tower.rules
    (heads_monotone h) trace contextCode .headType (.sort (.succ (.succ Tower.zero)))
    context_checked accepted (by decide) rfl (context_assembles h constants)
    argument (.plain (fun _ => universeSet h ∅ 1)) atArgument rfl env admitted

theorem computes (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (depth : Nat) (argumentCode terminal : Replay 1) (argument : Meaning.{u} 1)
    (trace : StructuralTypingReplay.BetaToVariable (program depth) (.head one) argumentCode 0 terminal)
    (accepted : check Tower.rules noConversionCheck context (program depth) (.head one) argumentCode = true)
    (atArgument : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      argumentCode (program depth) (.head one) = some argument)
    (env : Environment.{u} 1) (admitted : valid h env) :
    (meaning h argument).value env = ZFSet.pair (env 0) ∅ := by
  change traceApp (traceLam (graph (universeSet h ∅ 1) _)) (argument.value env) = _
  rw [traceApp_graph_beta _ (argument_member h constants depth argumentCode terminal argument trace
    accepted atArgument env admitted)]
  rw [BetaToVariable.value (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants Tower.rules
    (heads_monotone h) trace contextCode context_checked accepted (context_assembles h constants)
    argument atArgument env admitted]

theorem values_agree (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (depth : Nat) (env : Environment.{u} 1) (admitted : valid h env) :
    (meaning h (programMeaning h 0 depth)).value env = (meaning h (programMeaning h 1 depth)).value env :=
  (computes h constants depth _ _ _ (raised_lower_trace depth) (raised_lower_checked depth)
    (raised_lower_assembles h constants depth) env admitted).trans
    (computes h constants depth _ _ _ (upper_trace depth) (upper_checked depth)
      (upper_assembles h constants depth) env admitted).symm

theorem nonempty_input_computes (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (depth : Nat) : (meaning h (programMeaning h 0 depth)).value (fun _ => (twoCode h).1) =
      ZFSet.pair (twoCode h).1 ∅ :=
  computes h constants depth _ _ _ (raised_lower_trace depth) (raised_lower_checked depth)
    (raised_lower_assembles h constants depth) _
    (ZFSetReplayApplicationComparisonControls.nonempty_input_valid h)

theorem result_member (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (depth : Nat) (env : Environment.{u} 1) (admitted : valid h env) :
    (meaning h (programMeaning h 0 depth)).value env ∈
      sigmaSet (universeSet h ∅ 1) (fun x => truthCode (x = x)) := by
  rw [computes h constants depth _ _ _ (raised_lower_trace depth) (raised_lower_checked depth)
    (raised_lower_assembles h constants depth) env admitted]
  exact ZFSetDependentProducts.mem_sigmaSet.mpr
    ⟨env 0, universeSet_subset_next h ∅ 0 admitted.2, ∅,
      (mem_truthCode _ _).mpr ⟨rfl, rfl⟩, rfl⟩

def identity (depth : Nat) : Tower.Tm 1 := .id pairType (term depth) (term depth)
def lowerIdentityCode (depth : Nat) : Replay 1 :=
  .idForm pairLevel pairFormation (code (raisedLowerCode depth)) (code (raisedLowerCode depth))
def mixedIdentityCode (depth : Nat) : Replay 1 :=
  .idForm pairLevel pairFormation (code (upperCode depth)) (code (raisedLowerCode depth))
def proofCode (depth : Nat) : Replay 1 := .reflIntro pairType (code (raisedLowerCode depth))

theorem reflexivity_checked (depth : Nat) : check Tower.rules noConversionCheck context
    (.refl (term depth)) (identity depth) (proofCode depth) = true := by
  change (check Tower.rules noConversionCheck context (term depth) pairType
    (code (raisedLowerCode depth)) && decide (identity depth = .id pairType (term depth) (term depth))) = true
  simpa only [identity, decide_true, Bool.and_true] using checked depth _ (raised_lower_checked depth)

theorem reflexivity_assembles (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (depth : Nat) : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (proofCode depth) (.refl (term depth)) (identity depth) = some (.plain (fun _ => ∅)) := rfl

noncomputable def lowerIdentityMeaning (h : CofinalInaccessibles.{u}) (depth : Nat) : Meaning.{u} 1 :=
  .plain (fun env => truthCode ((meaning h (programMeaning h 0 depth)).value env =
    (meaning h (programMeaning h 0 depth)).value env))

theorem lower_identity_assembles (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) :
    assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (lowerIdentityCode depth) (identity depth) (.head pairLevel) = some (lowerIdentityMeaning h depth) := by
  simp only [lowerIdentityCode, identity, assemble,
    assembles h constants depth _ _ (raised_lower_assembles h constants depth), Option.pure_def]
  rfl

theorem identities_checked (depth : Nat) :
    check Tower.rules noConversionCheck context (identity depth) (.head pairLevel) (lowerIdentityCode depth) = true ∧
    check Tower.rules noConversionCheck context (identity depth) (.head pairLevel) (mixedIdentityCode depth) = true := by
  have lower := checked depth _ (raised_lower_checked depth)
  have upper := checked depth _ (upper_checked depth)
  constructor
  · change ((((true && true) && check Tower.rules noConversionCheck context (term depth) pairType
      (code (raisedLowerCode depth))) && check Tower.rules noConversionCheck context (term depth) pairType
        (code (raisedLowerCode depth))) && true) = true
    simp only [lower, Bool.and_self]
  · change ((((true && true) && check Tower.rules noConversionCheck context (term depth) pairType
      (code (upperCode depth))) && check Tower.rules noConversionCheck context (term depth) pairType
        (code (raisedLowerCode depth))) && true) = true
    simp only [lower, upper, Bool.and_self]

theorem identity_fibres_agree (h : CofinalInaccessibles.{u}) (constants : DeclName → ZFSet.{u})
    (depth : Nat) (first second : Meaning.{u} 1)
    (atFirst : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (lowerIdentityCode depth) (identity depth) (.head pairLevel) = some first)
    (atSecond : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (mixedIdentityCode depth) (identity depth) (.head pairLevel) = some second)
    (env : Environment.{u} 1) (admitted : valid h env) : first.value env = second.value env := by
  exact identity_values_eq (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    (lowerIdentityCode depth) (mixedIdentityCode depth) pairType (term depth) (term depth)
    (.head pairLevel) (.head pairLevel) pairLevel pairLevel
    pairFormation (code (raisedLowerCode depth)) (code (raisedLowerCode depth))
    pairFormation (code (upperCode depth)) (code (raisedLowerCode depth)) .hole .hole first second
    (meaning h (programMeaning h 0 depth)) (meaning h (programMeaning h 0 depth))
    (meaning h (programMeaning h 1 depth)) (meaning h (programMeaning h 0 depth))
    rfl rfl atFirst atSecond
    (assembles h constants depth _ _ (raised_lower_assembles h constants depth))
    (assembles h constants depth _ _ (raised_lower_assembles h constants depth))
    (assembles h constants depth _ _ (upper_assembles h constants depth))
    (assembles h constants depth _ _ (raised_lower_assembles h constants depth)) env
    (values_agree h constants depth env admitted) rfl

/-- The independently assembled mixed fibre accepts the value of the
actually checked reflexivity program. The theorem consumes both assembly
receipts, so the proof is used as a member, not merely displayed. -/
theorem reflexivity_member_independent_formation (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) (depth : Nat) (proof formed : Meaning.{u} 1)
    (atProof : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (proofCode depth) (.refl (term depth)) (identity depth) = some proof)
    (atFormation : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      (mixedIdentityCode depth) (identity depth) (.head pairLevel) = some formed)
    (env : Environment.{u} 1) (admitted : valid h env) : proof.value env ∈ formed.value env := by
  rw [reflexivity_assembles h constants depth] at atProof
  cases Option.some.inj atProof
  rw [← identity_fibres_agree h constants depth (lowerIdentityMeaning h depth) formed
    (lower_identity_assembles h constants depth) atFormation env admitted]
  exact (mem_truthCode _ _).mpr ⟨rfl, rfl⟩

end Consumer

#print axioms lower_checked
#print axioms raised_lower_checked
#print axioms upper_checked
#print axioms lower_assembles
#print axioms upper_assembles
#print axioms forged_computed_argument_rejected
#print axioms raised_lower_trace
#print axioms upper_trace
#print axioms terminal_checked_from_trace
#print axioms program_reduces
#print axioms trace_does_not_authorize_source
#print axioms producer_positive_controls
#print axioms producer_nonidentity_fallback
#print axioms producer_cutoff_and_unsupported
#print axioms producer_success_is_not_authority
#print axioms generated_trace_value
#print axioms computed_values_agree
#print axioms invalid_input_values
#print axioms invalid_input_distinguishes
#print axioms DependentFamily.generated_formations_agree
#print axioms DependentFamily.terminal_reflexivity_checked
#print axioms DependentFamily.unreduced_family_rejects_terminal_reflexivity
#print axioms DependentFamily.anchored_instance_not_qualified
#print axioms DependentFamily.independent_anchored_formations
#print axioms DependentFamily.anchored_contexts_agree
#print axioms DependentFamily.anchored_context_inhabited
#print axioms Consumer.computes
#print axioms Consumer.nonempty_input_computes
#print axioms Consumer.result_member
#print axioms Consumer.reflexivity_checked
#print axioms Consumer.identity_fibres_agree
#print axioms Consumer.reflexivity_member_independent_formation

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedArgumentControls
