import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRRequestReading
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseTyping
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderRootComparison

/-! A firing of an actual compiled clause has a source-authorized head.
The premise semantics supplies the final typed assignment and preserves the
pool captures from the request. Guard and body authorization are joined
separately to this conclusion theorem. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.FiringReading

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch Match
open GeneralFirstOrderProjection

def sourceAssignment (pools : Join.Pools) (completed : ScopedRuleMatching.Assignment) :
    Mettapedia.Languages.Datalog.Assignment :=
  ClauseReading.assignment (ClauseDictionary.expand pools (ordinary completed))

theorem assignment_extends (pools : Join.Pools) {before after : ScopedRuleMatching.Assignment}
    (preserved : GeneralScopedMatch.Extends before after) (name : String) (value : Value)
    (defined : sourceAssignment pools before name = some value) :
    sourceAssignment pools after name = some value := by
  simp only [sourceAssignment,ClauseReading.assignment,ClauseDictionary.expand_lookup,ordinary_lookup] at defined ⊢
  cases selected : ScopedRuleMatching.lookup before (Join.logicalVariable name) with
  | none => simp [selected] at defined
  | some capture =>
    have retained := preserved _ _ selected
    simp only [selected,Option.map_some,Option.bind_some] at defined
    simpa only [retained,Option.map_some,Option.bind_some] using defined

theorem source_match_extends (pools : Join.Pools) {before after : ScopedRuleMatching.Assignment}
    (preserved : GeneralScopedMatch.Extends before after) (source : Mettapedia.Languages.Datalog.Atom) (fact : GroundFact)
    (matched : source.Matches (sourceAssignment pools before) fact) :
    source.Matches (sourceAssignment pools after) fact := by
  refine ⟨matched.1,?_⟩
  apply List.Forall₂.imp _ matched.2
  intro argument value first
  cases argument with
  | literal expected => exact first
  | var name => exact assignment_extends pools preserved name value first
  | anonymous => trivial

theorem compiled_fields (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule) :
    rule.left = .apply "InferSnapshot" [Join.poolPattern (Join.relationSlots pools),Join.poolPattern (Join.literalSlots pools)] ∧
      Join.atom? pools clause.body.length clause.head = some rule.right := by
  obtain ⟨original,originalCompiled,rfl⟩ := Option.map_eq_some_iff.mp compiled
  constructor
  · rfl
  · cases safe : clause.checkRangeRestriction with
    | false => simp [Join.compileClause?,safe] at originalCompiled
    | true =>
      simp only [Join.compileClause?,safe,Bool.not_true,Bool.false_eq_true,if_false] at originalCompiled
      change ((Join.atom? pools clause.body.length clause.head).bind fun right =>
        ((Join.orderedBody clause).zipIdx.mapM fun entry => Join.bodyPremise? pools entry.2 entry.1).bind fun premises =>
          some ({
            name := "datalog-clause:" ++ toString ordinal
            typeContext := Join.variableContext pools clause
            premises := premises
            left := .apply "Infer" [Join.poolPattern (Join.relationSlots pools),
              Join.poolPattern (Join.literalSlots pools),.fvar "facts"]
            right := right } : RewriteRule)) = some original at originalCompiled
      simp only [Option.bind_eq_some_iff,Option.some.injEq] at originalCompiled
      obtain ⟨right,rightRead,premises,_,rfl⟩ := originalCompiled
      exact rightRead

theorem root_target_readout (rule : RewriteRule) (spec : RuleBindingSpec)
    (shape : binderFree rule.right = true) (zero : GeneralPremise.checkZeroDependencies spec = true)
    {environment : GeneralPremise.Environment} {index : Nat} {source : Pattern}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (firing : GeneralPremise.RootFiring environment [] (.base "DlStatement") source index trace captured completed history target) :
    applyBindings (ordinary completed) rule.right = target := by
  cases firing with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ actualDeclared actualSpecified _ _ _ capturedTyped premises reduced _ =>
    have sameRule : actualRule = rule := Option.some.inj (actualDeclared.symm.trans declared)
    subst actualRule
    have sameSpec : actualSpec = spec := Option.some.inj (actualSpecified.symm.trans specified)
    subst actualSpec
    exact binderFree_instantiation_readout shape ((premises.typed capturedTyped).rootValues zero) reduced

theorem root_conclusion_readout (pools : Join.Pools) (clause : Clause) (rule : RewriteRule) (spec : RuleBindingSpec)
    (left : rule.left = .apply "InferSnapshot" [Join.poolPattern (Join.relationSlots pools),Join.poolPattern (Join.literalSlots pools)])
    (right : Join.atom? pools clause.body.length clause.head = some rule.right)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    {environment : GeneralPremise.Environment} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (firing : GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request pools)
      index trace captured completed history target)
    (fact : GroundFact) (decoded : IRCodec.groundFact? (applyBindings (Executable.dictionary pools) target) = some fact) :
    clause.head.Matches (sourceAssignment pools completed) fact := by
  cases firing with
  | @fire _ _ _ _ _ actualRule actualSpec _ _ _ _ actualDeclared actualSpecified _ _ matching capturedTyped premises reduced _ =>
    have same : actualRule = rule := Option.some.inj (actualDeclared.symm.trans declared)
    subst actualRule
    have sameSpec : actualSpec = spec := Option.some.inj (actualSpecified.symm.trans specified)
    subst actualSpec
    have roots := (premises.typed capturedTyped).rootValues zero
    have requestMatch : Matches rule spec 0 .left [] 0 []
        (.apply "InferSnapshot" [Join.poolPattern (Join.relationSlots pools),Join.poolPattern (Join.literalSlots pools)])
        (Executable.request pools) captured := by
      simpa only [left,List.length_nil] using matching.matching
    have poolsRead := RequestReading.request_pools pools requestMatch premises.extension roots
    have shape := ClauseDictionary.atom_binderFree pools clause.body.length clause.head rule.right right
    have reconstructed : applyBindings (ordinary completed) rule.right = target :=
      binderFree_instantiation_readout shape roots reduced
    rw [← reconstructed,← ClauseDictionary.atom_expands pools (ordinary completed) clause.body.length clause.head rule.right right] at decoded
    exact ClauseReading.atom_decoding_sound pools _ poolsRead clause.body.length clause.head rule.right right fact decoded

theorem root_conclusion_sound (pools : Join.Pools) (ordinal : Nat) (clause : Clause) (rule : RewriteRule)
    (compiled : Query.compileClause? pools ordinal clause = some rule)
    {environment : GeneralPremise.Environment} {index : Nat}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event} {target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some (GeneralRuleBindingInference.inferredSpec rule))
    (firing : GeneralPremise.RootFiring environment [] (.base "DlStatement") (Executable.request pools)
      index trace captured completed history target)
    (fact : GroundFact) (decoded : IRCodec.groundFact? (applyBindings (Executable.dictionary pools) target) = some fact) :
    clause.head.Matches (sourceAssignment pools completed) fact := by
  obtain ⟨left,right⟩ := compiled_fields pools ordinal clause rule compiled
  exact root_conclusion_readout pools clause rule (GeneralRuleBindingInference.inferredSpec rule) left right
    (inferred_zero rule) declared specified firing fact decoded

#print axioms assignment_extends
#print axioms source_match_extends
#print axioms compiled_fields
#print axioms root_target_readout
#print axioms root_conclusion_readout
#print axioms root_conclusion_sound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.FiringReading
