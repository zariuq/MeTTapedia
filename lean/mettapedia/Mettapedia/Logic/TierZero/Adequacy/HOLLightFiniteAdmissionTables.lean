import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextSource
import Mettapedia.Logic.TierZero.Adequacy.HOLLightContextActivation
import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionTables

/-!
# Original local admission constructs the successor finite declaration table

The data-bearing table is updated using the original finite declaration
owners. Its context index is the actual original local-check output. This
is local source admission and table construction, never old proof/history
replay. Logical source licensing remains a separate protected-premise law.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteAdmissionTables

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open Mettapedia.Languages.HOLLight.MeTTa

def constantTable {context : TheoryContext} (before : DeclarationTable.Table context)
    (certificates : InstanceWitnesses) (name : Name) (body : SourceTerm)
    (result : ContextConstantDefinitionResult)
    (accepted : admitConstantInTheory context certificates name body = some result) : DeclarationTable.Table result.context := by
  unfold admitConstantInTheory at accepted
  split at accepted
  · cases accepted
  · rename_i definition sourceChecked
    split at accepted
    · rename_i formed
      split at accepted
      · rename_i fresh
        split at accepted
        · cases accepted
        · cases Option.some.inj accepted
          exact DeclarationTable.addConstant before (.mk name (.defined body)) definition.ty
            ((typeFormedB_eq_true_iff _ _).mp formed) fresh
      · cases accepted
    · cases accepted

def sourceTypeTable {context : TheoryContext} (before : DeclarationTable.Table context)
    (certificates : InstanceWitnesses) (request : TypeOperatorDefinitionRequest)
    (result : SourceTypeDefinitionResult)
    (accepted : admitSourceTypeInTheory context certificates request = some result) : DeclarationTable.Table result.context := by
  unfold admitSourceTypeInTheory at accepted
  split at accepted
  · cases accepted
  · rename_i view viewed
    split at accepted
    · cases accepted
    · rename_i core admitted
      split at accepted
      · cases Option.some.inj accepted
        change DeclarationTable.Table core.context
        unfold admitTypeInTheoryFromApplication at admitted
        split at admitted
        · split at admitted
          · rename_i representedFormed
            split at admitted
            · rename_i functionArity
              split at admitted
              · rename_i fresh
                split at admitted
                · cases admitted
                · cases Option.some.inj admitted
                  exact TypeDefinitionTables.extension context before request view.argument.ty functionArity
                    ((typeFormedB_eq_true_iff _ _).mp representedFormed) fresh
              · cases admitted
            · cases admitted
          · cases admitted
        · cases admitted
      · cases accepted

def outputTable (policy : AxiomPolicy) [DecidablePred policy] {context : TheoryContext}
    (before : DeclarationTable.Table context) (cache : Array Theorem) (command : Command)
    (output : Output) (accepted : command.check policy context cache = some output) : DeclarationTable.Table output.context := by
  cases command with
  | proof node certificates =>
      have same : context = output.context := Option.some.inj (HOLLightContextActivation.checked_target_context policy context cache _ accepted)
      exact same ▸ before
  | constant origin name body certificates =>
      cases admitted : admitConstantInTheory context certificates name body with
      | none => simp [Command.check, admitted] at accepted
      | some result =>
          simp only [Command.check, admitted, Bind.bind, Option.bind] at accepted
          split at accepted
          · cases Option.some.inj accepted
            exact constantTable before certificates name body result admitted
          · contradiction
  | typeDefinition origin request index certificates =>
      cases found : cache[index]? with
      | none => simp [Command.check, found] at accepted
      | some existence =>
          simp only [Command.check, found, Bind.bind, Option.bind] at accepted
          split at accepted
          · cases admitted : admitSourceTypeInTheory context certificates request with
            | none => simp [admitted] at accepted
            | some result =>
                simp only [admitted] at accepted
                split at accepted
                · cases Option.some.inj accepted
                  exact sourceTypeTable before certificates request result admitted
                · contradiction
          · contradiction

def admitWithTable (policy : AxiomPolicy) [DecidablePred policy] {context : TheoryContext}
    (before : DeclarationTable.Table context) (cache : Array Theorem) (command : Command) :
    Option (Σ output : Output, DeclarationTable.Table output.context) :=
  match accepted : command.check policy context cache with
  | none => none
  | some output => some ⟨output, outputTable policy before cache command output accepted⟩

theorem admitWithTable_output_exact (policy : AxiomPolicy) [DecidablePred policy] {context : TheoryContext}
    (before : DeclarationTable.Table context) (cache : Array Theorem) (command : Command) :
    (admitWithTable policy before cache command).map Sigma.fst = command.check policy context cache := by
  unfold admitWithTable
  split
  · rename_i missing
    exact missing.symm
  · rename_i output accepted
    exact accepted.symm

theorem admitted_context_wire_exact (policy : AxiomPolicy) [DecidablePred policy] {context : TheoryContext}
    (before : DeclarationTable.Table context) (cache : Array Theorem) (command : Command) {output : Output}
    (accepted : command.check policy context cache = some output) :
    (HOLLightFiniteContextData.codec.get
      (HOLLightFiniteContextData.codec.put (HOLLightFiniteContextSource.ofTable (outputTable policy before cache command output accepted)))).bind
      HOLLightFiniteContextData.decode = some output.context :=
  HOLLightFiniteContextSource.wire_decode_ofTable (outputTable policy before cache command output accepted)

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteAdmissionTables
