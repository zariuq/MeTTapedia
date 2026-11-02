import Mettapedia.Logic.TierZero.Adequacy.HOLLightSelectedAdmission
import Mettapedia.Languages.HOLLight.ProofDataEncoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.WireDataABT
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSchemaKernel

/-!
# Original registered HOL commands activated at exact immutable context IDs

A stored entry fixes the original source command, including its origin and
ordered parent addresses. Public cache input supplies data, not authority.
Activation reads only the selected parent values in protected judgment space.
The original local admission/formation operation computes the output; no
proof history or independent derivability decision is run during activation.

Context identifiers have an explicit interpretation as actual TheoryContext
values. Routing follows the command's computed context, never printed names
or an assumed injectivity property of a digest.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightContextActivation

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Logic
open InferenceSchemaActivation (Tm action)
open InferenceSchemaKernel (Space Value)

/-- The declaration context is computed independently of proof-cache validity. -/
def targetContext (context : TheoryContext) : Command → Option TheoryContext
  | .proof _ _ => some context
  | .constant _ name body witnesses => (admitConstantInTheory context witnesses name body).map (·.context)
  | .typeDefinition _ request _ witnesses => (admitSourceTypeInTheory context witnesses request).map (·.context)

theorem checked_target_context (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (cache : Array Theorem) (command : Command)
    {result : Output} (accepted : command.check policy context cache = some result) :
    targetContext context command = some result.context := by
  cases command with
  | proof node witnesses =>
      simp only [Command.check] at accepted
      cases replayed : node.replay (ruleWitness policy) cache with
      | none => simp [replayed] at accepted
      | some next =>
          rw [replayed] at accepted
          split at accepted
          · cases Option.some.inj accepted; rfl
          · contradiction
  | constant origin name body witnesses =>
      simp only [Command.check] at accepted
      cases admitted : admitConstantInTheory context witnesses name body with
      | none => simp [admitted] at accepted
      | some defined =>
          rw [admitted] at accepted
          dsimp only [Bind.bind, Option.bind] at accepted
          split at accepted
          · cases Option.some.inj accepted
            simp [targetContext, admitted]
          · contradiction
  | typeDefinition origin request index witnesses =>
      simp only [Command.check] at accepted
      cases found : cache[index]? with
      | none => simp [found] at accepted
      | some existence =>
          rw [found] at accepted
          dsimp only [Bind.bind, Option.bind] at accepted
          split at accepted
          · cases admitted : admitSourceTypeInTheory context witnesses request with
            | none => simp [admitted] at accepted
            | some defined =>
                rw [admitted] at accepted
                dsimp only [Bind.bind, Option.bind] at accepted
                split at accepted
                · cases Option.some.inj accepted
                  simp [targetContext, admitted]
                · contradiction
          · contradiction

/-- Only context routing is a stored proof obligation. Logical soundness is
earned from the original independent command semantics and selected premises. -/
structure Entry (contexts : Nat → TheoryContext) where
  before : Nat
  after : Nat
  command : Command
  routed : targetContext (contexts before) command = some (contexts after)

def theoremPayload (context : Nat) (fact : Theorem) : Tm :=
  .node (.inr "registered.judgment") (.cons 0
    (WireDataABT.encode (.pair (.atom context) (theoremCodec.put fact))) .nil)

theorem theoremPayload_injective {firstContext secondContext : Nat} {first second : Theorem}
    (same : theoremPayload firstContext first = theoremPayload secondContext second) :
    firstContext = secondContext ∧ first = second := by
  have inner : WireDataABT.encode (.pair (.atom firstContext) (theoremCodec.put first)) =
      WireDataABT.encode (.pair (.atom secondContext) (theoremCodec.put second)) := by
    simpa [theoremPayload] using same
  have both := WireDataABT.encode_injective inner
  simp only [Data.pair.injEq, Data.atom.injEq] at both
  exact ⟨both.1, theoremCodec.put_injective both.2⟩

theorem theoremPayload_fixed (context : Nat) (fact : Theorem)
    (assignment : ABTProtectedParameters.Assignment InferenceSchemaActivation.Head 0) :
    action.apply assignment (theoremPayload context fact) = theoremPayload context fact := by
  apply ABTProtectedParameters.supported_term_fixed
  simpa [theoremPayload, Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.supportedAt,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.Fields.supportedAt] using
    WireDataABT.encode_supported (.pair (.atom context) (theoremCodec.put fact))

def requestPayload {contexts : Nat → TheoryContext} (source : Nat) (entry : Entry contexts)
    (cache : Array Theorem) : Tm :=
  .node (.inr "registered.request") (.cons 0
    (WireDataABT.encode (.pair (.atom source) (.pair (.atom entry.before) (.pair (.atom entry.after)
      (.pair (ProofDataEncoding.originCodec.put entry.command.origin)
        ((Codec.list theoremCodec).put cache.toList)))))) .nil)

def fromResult {contexts : Nat → TheoryContext} (source : Nat) (entry : Entry contexts)
    (cache : Array Theorem) (parents : List Theorem) (output : Output) : RuleInstance Value :=
  ⟨[(.requests, requestPayload source entry cache)],
    parents.map (fun fact => (.judgments, theoremPayload entry.before fact)), [], [],
    output.theorems.map (fun fact => (.judgments, theoremPayload entry.after fact))⟩

def activate (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (source : Nat) (cache : Array Theorem) : Option (RuleInstance Value) := do
  let entry ← entries source
  let output ← entry.command.check policy (contexts entry.before) cache
  let parents ← DerivationGraph.lookupPremises cache entry.command.parents
  pure (fromResult source entry cache parents output)

theorem origin (policy : AxiomPolicy) [DecidablePred policy] (contexts : Nat → TheoryContext)
    (entries : Nat → Option (Entry contexts)) (source : Nat) (cache : Array Theorem)
    {raw : RuleInstance Value} (computed : activate policy contexts entries source cache = some raw) :
    ∃ entry output parents, entries source = some entry ∧
      entry.command.check policy (contexts entry.before) cache = some output ∧
      DerivationGraph.lookupPremises cache entry.command.parents = some parents ∧
      output.context = contexts entry.after ∧ raw = fromResult source entry cache parents output := by
  cases found : entries source with
  | none => simp [activate, found] at computed
  | some entry =>
      cases checked : entry.command.check policy (contexts entry.before) cache with
      | none => simp [activate, found, checked] at computed
      | some output =>
          cases selected : DerivationGraph.lookupPremises cache entry.command.parents with
          | none => simp [activate, found, checked, selected] at computed
          | some parents =>
              have same : fromResult source entry cache parents output = raw := by
                simpa [activate, found, checked, selected] using computed
              refine ⟨entry, output, parents, rfl, checked, selected, ?_, same.symm⟩
              exact Option.some.inj ((checked_target_context policy _ _ _ checked).symm.trans entry.routed)

end Mettapedia.Logic.TierZero.Adequacy.HOLLightContextActivation
