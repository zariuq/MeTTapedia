import Mettapedia.GSLT.LanguageDef.CheckedSource

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

def renderPattern : Pattern → String
  | .bvar index => s!"(Var {index})"
  | .fvar name => s!"(FVar {quote name})"
  | .apply head arguments =>
      s!"(PApp {quote head} {renderPatterns arguments})"
  | .lambda binder body =>
      let renderedBinder := match binder with
        | none => "BNone"
        | some name => s!"(BSome {quote name})"
      s!"(PLam {renderedBinder} {renderPattern body})"
  | .multiLambda arity binders body =>
      s!"(PMultiLam {arity} {renderList quote binders} {renderPattern body})"
  | .subst body replacement =>
      s!"(PSubst {renderPattern body} {renderPattern replacement})"
  | .collection collectionType elements rest =>
      let renderedRest := match rest with
        | none => "RNone"
        | some name => s!"(RSome {quote name})"
      s!"(PCollection {quote (reprStr collectionType)} " ++
        s!"{renderPatterns elements} {renderedRest})"
termination_by pattern => 2 * sizeOf pattern

def renderPatterns : List Pattern → String
  | [] => "LNil"
  | pattern :: patterns =>
      s!"(LCons {renderPattern pattern} {renderPatterns patterns})"
termination_by patterns => 2 * sizeOf patterns + 1

end

def renderFormal (formal : String × Nat) : String :=
  s!"(Formal {quote formal.1} {formal.2})"

def renderRule (rule : RuleSchema) : String :=
  s!"(GRule {quote rule.id.value} {renderList renderFormal rule.metavariables} " ++
    s!"{renderPatterns rule.premises} {renderPattern rule.conclusion})"

def renderConstructor (declaration : GrammarRule) : String :=
  s!"(CDecl {quote declaration.label} {declaration.params.length})"

def renderJudgment (judgment : JudgmentDecl) : String :=
  s!"(JDecl {quote judgment.head} {judgment.arity})"

def renderPresentation (presentation : Presentation) : String :=
  s!"(GPresentation " ++
    s!"{renderList renderConstructor presentation.language.terms} " ++
    s!"{renderList renderJudgment presentation.judgments} " ++
    s!"{renderList renderRule presentation.rules})"

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
    s!"{renderPresentation source.presentation})"

def renderRuleInstance (ruleInstance : RuleInstance) : String :=
  s!"(GRuleInst {quote ruleInstance.ruleId.value} " ++
    s!"{renderPatterns ruleInstance.arguments})"

mutual

def renderRawProof : RawProof → String
  | .node ruleInstance children =>
      s!"(GProof {renderRuleInstance ruleInstance} {renderProofs children})"
termination_by proof => 2 * sizeOf proof
decreasing_by all_goals simp_wf; omega

def renderProofs : List RawProof → String
  | [] => "PrNil"
  | proof :: proofs =>
      s!"(PrCons {renderRawProof proof} {renderProofs proofs})"
termination_by proofs => 2 * sizeOf proofs + 1

end


end Mettapedia.GSLT.LanguageDef.InferenceMeTTaRender
