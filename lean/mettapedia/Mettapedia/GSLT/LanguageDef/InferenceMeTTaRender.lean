import Mettapedia.GSLT.LanguageDef.CheckedSource
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat

namespace Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource

def quote (value : String) : String := reprStr value

def renderList (render : α → String) : List α → String
  | [] => "LNil"
  | value :: values =>
      s!"(LCons {render value} {renderList render values})"

mutual

def renderPattern (pattern : Pattern) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodePattern pattern)

def renderPatterns (patterns : List Pattern) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodePatterns patterns)

end

def renderFormal (formal : String × Nat) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeFormal formal)

def renderSideCondition (condition : RuleSideCondition) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeSideCondition condition)

def renderRule (rule : RuleSchema) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeRule rule)

def renderConstructor (declaration : GrammarRule) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeConstructor
      { head := declaration.label, arity := declaration.params.length })

def renderJudgment (judgment : JudgmentDecl) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeJudgment judgment)

def renderConversion (conversion : Option ConversionDecl) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeConversion conversion)

def renderDefinition (definition : CalculusLanguageDef) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeDefinition definition)

def renderSourceIdentity (identity : SourceIdentity) : String :=
  s!"(SourceIdentityV1 {quote identity.systemId} {quote identity.revision} " ++
    s!"{quote identity.artifactDigest})"

def renderSourceAssumption (assumption : SourceAssumption) : String :=
  s!"(SourceAssumptionV1 {quote assumption.id} " ++
    s!"{renderPattern assumption.statement})"

def renderAssumptionLedger (ledger : AssumptionLedger) : String :=
  s!"(AssumptionLedgerV1 {renderList renderSourceAssumption ledger.entries})"

def renderSourceProfile (profile : SourceProfile) : String :=
  s!"(SourceProfileV1 {quote profile.name} {quote profile.version} " ++
    s!"{renderPattern profile.payload})"

def renderProfileLedger (ledger : ProfileLedger) : String :=
  s!"(ProfileLedgerV1 {renderList renderSourceProfile ledger.entries})"

/-- Serialize the exact checked-source package consumed by the operational
source-indexed checker. -/
def renderGSLTSource (source : GSLTSource) : String :=
  s!"(GSLTSourceV1 {renderSourceIdentity source.identity} " ++
    s!"{renderAssumptionLedger source.assumptions} " ++
    s!"{renderProfileLedger source.profiles} " ++
    s!"{renderDefinition source.definition})"

def renderRuleInstance (ruleInstance : RuleInstance) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeRuleInstance ruleInstance)

mutual

def renderRawProof (proof : RawProof) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeRawProof proof)

def renderProofs (proofs : List RawProof) : String :=
  InferenceCettaWire.CettaTerm.render
    (InferenceCettaWire.encodeProofs proofs)

end


end Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
