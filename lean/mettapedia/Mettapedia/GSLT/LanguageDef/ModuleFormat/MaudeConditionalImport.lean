import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalSourceGuard
import Mettapedia.Languages.Maude.ConditionalMaxBoolConservativity
import Mettapedia.Languages.Maude.SchemaLink

/-! A ground-conservative BOOL import profile for the original conditional
max module. Checking the full retained IR is required; an imported signature
or module name alone never grants executable admission. The imported source
semantics includes BOOL-OPS, polymorphic branches and canonical equality
hooks at Nat and Bool. General imported modules need their own certificates.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalImport

open Mettapedia.Languages
open Maude.ConditionalMax
open MaudeCompilation.ConditionalCompilation

/-- Declaration order produced by the original source's leading import. -/
def retainedTheory : Maude.Theory := {
  Maude.Examples.conditional with signature :=
    ⟨["Bool", "Nat"], [trueOperator, falseOperator, zeroOperator, successorOperator, leOperator, maxOperator]⟩ }

def interfaceName : String := "BOOL:Nat-Bool:ground-conservative"

def signatureInterface : MaudeSourceLowering.ImportSignature :=
  ⟨"BOOL", interfaceName, ⟨["Bool"], [trueOperator, falseOperator]⟩⟩

def settings : MaudeSourceLowering.Settings := {
  names := [(Maude.Examples.conditional.name, {
    operators := Maude.Examples.conditional.signature.operators.map MaudeSourceLowering.OperatorBinding.ofOperator
    equations := Maude.Examples.conditional.equations.map (·.name) })]
  imports := [signatureInterface] }

theorem retainedToLocal : Maude.TheoryEmbedding retainedTheory Maude.Examples.conditional where
  operators declaration member := by
    simp only [retainedTheory, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact true_member
    · exact false_member
    · exact zero_member
    · exact successor_member
    · exact le_member
    · exact max_member
  equations _ member := member
  checked row member _ := by
    simp only [retainedTheory, Maude.Examples.conditional, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide_cbv

theorem localToRetained : Maude.TheoryEmbedding Maude.Examples.conditional retainedTheory where
  operators declaration member := by
    rcases Maude.ConditionalMax.operators member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [retainedTheory, List.mem_cons, true_or, or_true]
  equations _ member := member
  checked row member _ := by
    simp only [Maude.Examples.conditional, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide_cbv

structure Certificate (source : MaudeSourceLowering.SourceModule) where
  schema : Maude.SchemaLink.Witness source.theory retainedTheory
  functional : source.kind = .functional
  imports : source.importInterfaces = [⟨"BOOL", interfaceName, .protecting⟩]

def check (source : MaudeSourceLowering.SourceModule) : Option (Certificate source) := do
  let schema ← Maude.SchemaLink.check source.theory retainedTheory
  if functional : source.kind = .functional then
    if imports : source.importInterfaces = [⟨"BOOL", interfaceName, .protecting⟩] then
      some ⟨schema, functional, imports⟩
    else none
  else none

def certify (source : MaudeSourceLowering.SourceModule) : Except String (Certificate source) :=
  match check source with
  | some evidence => .ok evidence
  | none => .error "conditional BOOL import requires the checked source equations and import interface"

def compile (source : MaudeSourceLowering.SourceModule) : Except String Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef := do
  let _ ← certify source
  MaudeCompilation.ConditionalCompilation.prepare source.theory

theorem Certificate.signature {source : MaudeSourceLowering.SourceModule} (certificate : Certificate source) :
    source.theory.signature = retainedTheory.signature := by
  simpa only [Maude.Theory.named] using congrArg Maude.Theory.signature certificate.schema.same

theorem named_equivalent_iff {actual reference : Maude.Theory}
    (witness : Maude.SchemaLink.Witness actual reference)
    {context : Maude.VariableContext} {sort : String} {source target : Maude.Term} :
    Maude.Equivalent actual context sort source target ↔ Maude.Equivalent reference context sort source target := by
  constructor
  · intro equivalent
    simpa only [witness.same] using equivalent.withName reference.name
  · intro equivalent
    rw [← witness.same] at equivalent
    simpa only [Maude.Theory.named] using equivalent.withName actual.name

theorem Certificate.ground_equivalent_iff {source : MaudeSourceLowering.SourceModule}
    (certificate : Certificate source) {first second : Maude.Term} {sort : String}
    (firstTyped : Maude.HasSort source.theory.signature [] first sort)
    (secondTyped : Maude.HasSort source.theory.signature [] second sort) :
    Maude.HookedEquivalent BoolPrelude.theory BoolPrelude.EqualityHook [] sort first second ↔
      Maude.Equivalent source.theory [] sort first second := by
  rw [certificate.signature] at firstTyped secondTyped
  have firstLocal := firstTyped.of_operator_subset retainedToLocal.operators
  have secondLocal := secondTyped.of_operator_subset retainedToLocal.operators
  rw [BoolPrelude.ground_equivalent_iff firstLocal secondLocal, named_equivalent_iff certificate.schema]
  exact ⟨localToRetained.ordinary, retainedToLocal.ordinary⟩

theorem imported_guard_exact (bound first second : Nat)
    (firstBound : first ≤ bound) (secondBound : second ≤ bound) :
    trueRow first second ∈ (provider bound).rows ↔
      Maude.HookedEquivalent BoolPrelude.theory BoolPrelude.EqualityHook [] "Bool"
        (le (numeral first) (numeral second)) truth := by
  rw [bounded_source_guard_iff bound first second firstBound secondBound,
    BoolPrelude.ground_equivalent_iff
      (le_sorted (numeral_sorted [] first) (numeral_sorted [] second)) (truth_sorted [])]

theorem compiled_ground_equivalent_iff {source : MaudeSourceLowering.SourceModule}
    {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (accepted : compile source = .ok language) {first second : Maude.Term} {sort : String}
    (firstTyped : Maude.HasSort source.theory.signature [] first sort)
    (secondTyped : Maude.HasSort source.theory.signature [] second sort) :
    Maude.HookedEquivalent BoolPrelude.theory BoolPrelude.EqualityHook [] sort first second ↔
      Maude.Equivalent source.theory [] sort first second := by
  cases evidence : certify source with
  | error reason =>
    unfold compile at accepted
    rw [evidence] at accepted
    change (Except.error reason : Except String Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef) = .ok language at accepted
    cases accepted
  | ok certificate => exact certificate.ground_equivalent_iff firstTyped secondTyped

#print axioms Certificate.ground_equivalent_iff
#print axioms imported_guard_exact
#print axioms compiled_ground_equivalent_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalImport
