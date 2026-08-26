import Mettapedia.GSLT.LanguageDef.ExactArithmeticToC0

/-!
# Canonical-profile admission for the exact-arithmetic to C0 bootstrap

The operation lowerer in `ExactArithmeticToC0` is deliberately small.  This
module adds an exact, structural admission guard around that fixed lowerer.
It is not a GSLT-to-GSLT transformer: the admitted presentations are checked
but do not determine the emitted program.

The first supported profile is exact and fail closed: all source and target
types, constructors, equations, and ordered operational rules must agree with
the independently authored exact-arithmetic and C0 presentations.  Language
names are intentionally not inspected.  Consequently a semantic rule change
is rejected before the fixed bootstrap lowerer runs, while a harmless rename
does not affect admission.  Rejection sensitivity must not be confused with
deriving output from the supplied operational rules.
-/

namespace Mettapedia.GSLT.LanguageDef.ExactArithmeticToC0PresentationTransform

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger
open Mettapedia.GSLT.LanguageDef.C0PureNTT
open Mettapedia.GSLT.LanguageDef.ExactArithmeticNTT
open Mettapedia.GSLT.LanguageDef.ExactArithmeticToC0

/-- Decidable, lossless data carried by an authored operational rule.

`RewriteRule` itself intentionally has no global `DecidableEq` instance.  The
compiler admission boundary nevertheless needs a decidable comparison, so it
uses this structurally identical data view.  Injectivity below prevents the
view from quotienting away premises, ordering, or either side of a rule. -/
structure RuleData where
  name : String
  typeContext : List (String × TypeExpr)
  premises : List Premise
  left : Pattern
  right : Pattern
deriving Repr, DecidableEq

namespace RuleData

def ofRule (rule : RewriteRule) : RuleData := {
  name := rule.name
  typeContext := rule.typeContext
  premises := rule.premises
  left := rule.left
  right := rule.right
}

theorem ofRule_injective : Function.Injective ofRule := by
  intro first second equal
  cases first
  cases second
  simp only [ofRule, mk.injEq] at equal
  rcases equal with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

end RuleData

/-- The exact operational profile currently admitted before the handwritten
bootstrap lowerer.  Presentation names are absent because they carry no
operational authority. -/
structure SupportedPresentations
    (source target : LanguageDef) : Type where
  sourceTypes : source.types = exactArithmetic.types
  sourceTerms : source.terms = exactArithmetic.terms
  sourceEquations : source.equations = []
  sourceRules : source.rewrites.map RuleData.ofRule =
    exactArithmetic.rewrites.map RuleData.ofRule
  targetTypes : target.types = c0Pure.types
  targetTerms : target.terms = c0Pure.terms
  targetEquations : target.equations = []
  targetRules : target.rewrites.map RuleData.ofRule =
    c0Pure.rewrites.map RuleData.ofRule

namespace SupportedPresentations

/-- The decidable rule view is lossless, so admission really fixes the source
operational rules rather than merely a coarse signature. -/
theorem sourceRules_eq {source target : LanguageDef}
    (profile : SupportedPresentations source target) :
    source.rewrites = exactArithmetic.rewrites := by
  exact (List.map_injective_iff.mpr RuleData.ofRule_injective)
    profile.sourceRules

/-- Target admission fixes every ordered C0 transition, including premises,
fault branches, outcomes, and receipts. -/
theorem targetRules_eq {source target : LanguageDef}
    (profile : SupportedPresentations source target) :
    target.rewrites = c0Pure.rewrites := by
  exact (List.map_injective_iff.mpr RuleData.ofRule_injective)
    profile.targetRules

end SupportedPresentations

private def equalityProof? {α : Type} [DecidableEq α]
    (first second : α) : Option (PLift (first = second)) :=
  if equal : first = second then some ⟨equal⟩ else none

private def emptyProof? {α : Type}
    (items : List α) : Option (PLift (items = [])) :=
  match items with
  | [] => some ⟨rfl⟩
  | _ :: _ => none

/-- Structurally inspect and admit the exact source/target operational profile.

The result contains proofs about the supplied values themselves.  There is no
path, filename, digest, generated-artifact identity, or external verifier in
this decision. -/
def admitPresentations?
    (source target : LanguageDef) :
    Option (SupportedPresentations source target) := do
  let sourceTypes ← equalityProof? source.types exactArithmetic.types
  let sourceTerms ← equalityProof? source.terms exactArithmetic.terms
  let sourceEquations ← emptyProof? source.equations
  let sourceRules ← equalityProof?
    (source.rewrites.map RuleData.ofRule)
    (exactArithmetic.rewrites.map RuleData.ofRule)
  let targetTypes ← equalityProof? target.types c0Pure.types
  let targetTerms ← equalityProof? target.terms c0Pure.terms
  let targetEquations ← emptyProof? target.equations
  let targetRules ← equalityProof?
    (target.rewrites.map RuleData.ofRule)
    (c0Pure.rewrites.map RuleData.ofRule)
  pure {
    sourceTypes := sourceTypes.down
    sourceTerms := sourceTerms.down
    sourceEquations := sourceEquations.down
    sourceRules := sourceRules.down
    targetTypes := targetTypes.down
    targetTerms := targetTerms.down
    targetEquations := targetEquations.down
    targetRules := targetRules.down
  }

/-- Admit the canonical presentations, then run the fixed seven-operation
bootstrap lowerer.

The profile witness is deliberately discarded.  This definition therefore
does not inhabit the generic presentation-sensitive transformation interface. -/
def admitCanonicalProfileAndCompileOperation?
    (source target : LanguageDef) (sourceTerm : Pattern) : Option Pattern := do
  let _profile ← admitPresentations? source target
  compileSourceOperation? sourceTerm

/-- Successful admitted compilation exposes its presentation evidence and the
exact seven-operation compiler image. -/
theorem admitted_compilation_successful
    {source target : LanguageDef} {sourceTerm targetProgram : Pattern}
    (compiled :
      admitCanonicalProfileAndCompileOperation? source target sourceTerm =
        some targetProgram) :
    Nonempty (SupportedPresentations source target) ∧
      CompilerImage targetProgram := by
  unfold admitCanonicalProfileAndCompileOperation? at compiled
  cases admitted : admitPresentations? source target with
  | none =>
      rw [admitted] at compiled
      contradiction
  | some profile =>
      rw [admitted] at compiled
      refine ⟨⟨profile⟩, ?_⟩
      exact successful_compilation_has_source (by
        simpa using compiled)

/-- On a canonical exact-arithmetic request, admitted bootstrap lowering
returns the same concrete C0 program used by the operational hosting theorem.
This joins admission to the existing fixed-profile theorem; it does not show
that either presentation generated the compiler output. -/
theorem admitted_encoded_result_eq
    {source target : LanguageDef} {operation : CoreOp}
    {targetProgram : Pattern}
    (compiled :
      admitCanonicalProfileAndCompileOperation? source target
        (encodeSourceOperation operation) = some targetProgram) :
    targetProgram = compileCoreOperation operation := by
  unfold admitCanonicalProfileAndCompileOperation? at compiled
  cases admitted : admitPresentations? source target with
  | none =>
      rw [admitted] at compiled
      contradiction
  | some profile =>
      rw [admitted, compile_encoded_source] at compiled
      exact Option.some.inj compiled.symm

/-- A successful admitted bootstrap request carries the request-local
arithmetic-to-C0 theorem for the program it actually returned.

This packages source execution, target execution, and reachable terminal
reflection at both outcome and ordered-receipt observations.  It deliberately
does not claim a global `BehavioralTransformation`: that stronger interface
also requires a term map and simulation for every state of the two authored
operational theories. -/
theorem admitted_encoded_hosts_completion
    {source target : LanguageDef} {operation : CoreOp}
    {first second : Int} {targetProgram : Pattern}
    (compiled :
      admitCanonicalProfileAndCompileOperation? source target
        (encodeSourceOperation operation) = some targetProgram) :
    Nonempty (SupportedPresentations source target) ∧
      targetProgram = compileCoreOperation operation ∧
      langReducesUsing (arithmeticSourceReferenceEnv operation first second)
          exactArithmetic (arithmeticSourceStart operation first second)
          (arithmeticSourceDone operation first second) ∧
      Relation.ReflTransGen
        (langReducesUsing (arithmeticC0ReferenceEnv operation first second)
          c0Pure)
        (compiledC0Start operation first second)
        (compiledC0Done operation first second) ∧
      ∀ outcome receipt,
        Relation.ReflTransGen
          (langReducesUsing (arithmeticC0ReferenceEnv operation first second)
            c0Pure)
          (compiledC0Start operation first second)
          (halted outcome receipt) →
        outcome =
            (match coreSem operation first second with
            | .declined => ExactArithmeticToC0.a "c0:outcome-declined"
            | .val value => ExactArithmeticToC0.a "c0:outcome-value"
                [exactIntegerValue value]) ∧
          receipt = compiledC0Receipt operation first second := by
  have presentations := (admitted_compilation_successful compiled).1
  have programEq := admitted_encoded_result_eq compiled
  subst targetProgram
  have hosted := exactArithmetic_to_C0_hosts_completion
    operation first second
  exact ⟨presentations, rfl, hosted⟩

/-- Any source-rule change visible in `RuleData` makes successful compilation
impossible.  This is rejection sensitivity for the fixed admitted profile,
not a general compiler-sensitivity theorem. -/
theorem source_rule_change_cannot_compile
    {source target : LanguageDef} {sourceTerm targetProgram : Pattern}
    (changed : source.rewrites.map RuleData.ofRule ≠
      exactArithmetic.rewrites.map RuleData.ofRule) :
    admitCanonicalProfileAndCompileOperation? source target sourceTerm ≠
      some targetProgram := by
  intro compiled
  rcases (admitted_compilation_successful compiled).1 with ⟨profile⟩
  exact changed profile.sourceRules

/-- Any target-rule change visible in `RuleData` likewise makes successful
compilation impossible. -/
theorem target_rule_change_cannot_compile
    {source target : LanguageDef} {sourceTerm targetProgram : Pattern}
    (changed : target.rewrites.map RuleData.ofRule ≠
      c0Pure.rewrites.map RuleData.ofRule) :
    admitCanonicalProfileAndCompileOperation? source target sourceTerm ≠
      some targetProgram := by
  intro compiled
  rcases (admitted_compilation_successful compiled).1 with ⟨profile⟩
  exact changed profile.targetRules

/-! ## Positive and negative controls -/

def renamedExactArithmetic : LanguageDef :=
  { exactArithmetic with name := "RenamedExactArithmetic" }

def renamedC0Pure : LanguageDef :=
  { c0Pure with name := "RenamedC0Pure" }

/-- Mere display-name changes do not affect the admitted semantics. -/
theorem renamed_presentations_compile (operation : CoreOp) :
    admitCanonicalProfileAndCompileOperation? renamedExactArithmetic
        renamedC0Pure
        (encodeSourceOperation operation) =
      some (compileCoreOperation operation) := by
  cases operation <;> decide +kernel

def changedAddRule : RewriteRule :=
  { evaluateRule "arith:add" "ExactIntegerAdd" with
    right := ExactArithmeticNTT.a "arith:halted"
      [ExactArithmeticNTT.a "arith:outcome-declined"] }

def sourceWithChangedAddSemantics : LanguageDef :=
  { exactArithmetic with
    rewrites := changedAddRule :: exactArithmetic.rewrites.tail }

/-- Changing the authored result of addition is rejected before lowering. -/
theorem changed_source_semantics_rejected :
    admitCanonicalProfileAndCompileOperation? sourceWithChangedAddSemantics
        c0Pure
        (encodeSourceOperation .add) = none := by
  decide +kernel

def changedReturnValueRule : RewriteRule :=
  { returnValueTransition with
    right := returnDeclinedTransition.right }

def targetWithChangedReturnSemantics : LanguageDef :=
  { c0Pure with
    rewrites := [
      fuelExhaustedRule,
      branchZeroTransition,
      branchNonzeroTransition,
      callValueTransition,
      callLanguageFaultTransition,
      callEngineFaultTransition,
      callResourceFaultTransition,
      changedReturnValueRule,
      returnDeclinedTransition,
      returnLanguageFaultTransition,
      returnEngineFaultTransition,
      returnResourceFaultTransition
    ] }

/-- Changing C0 value return into decline is rejected before lowering. -/
theorem changed_target_semantics_rejected :
    admitCanonicalProfileAndCompileOperation? exactArithmetic
        targetWithChangedReturnSemantics
        (encodeSourceOperation .add) = none := by
  decide +kernel

/-- Unsupported source syntax remains rejected after presentation admission. -/
theorem invented_source_operation_rejected :
    admitCanonicalProfileAndCompileOperation? exactArithmetic c0Pure
        (.apply "arith:invented" []) = none := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.ExactArithmeticToC0PresentationTransform
