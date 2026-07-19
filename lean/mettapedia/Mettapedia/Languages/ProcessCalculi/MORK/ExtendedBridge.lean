import Mettapedia.Languages.ProcessCalculi.MORK.AuthoredContextBridge

/-!
# MORK bridge for fully applied authored rules

Rules whose source syntax contains substitution nodes or collection rest
variables need no extra reduction law.  Once the ordinary MeTTaIL rule
matcher, premise relation, and reflective substitution have produced a
bounded authored step, the generic contextual compiler emits the MORK rule.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.ExtendedBridge

open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- A fully evidenced authored rule application compiles to a MORK rule and
fires on the singleton translation of its source.  This includes rules whose
surface right-hand sides normalize substitution or rest-variable syntax. -/
theorem authoredRule_mork_fire
    {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat}
    {source target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {rule : RewriteRule}
    {initial final : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
    (ruleMember : rule ∈ lang.rewrites)
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        lang rule source)
    (premises : PremisesAt base lang fuel initial rule.premises final)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        lang rule final = target)
    (sourceGround : isGroundAtom (morkPatternToAtom source) = true)
    (targetGround : isGroundAtom (morkPatternToAtom target) = true) :
    ∃ compiledRule ∈ compiledContextRules base lang (fuel + 1) source,
      patternToSpace target ∈ fireRule (patternToSpace source) compiledRule := by
  exact stepAt_compiles_to_mork_fire
    (.rule ruleMember matched premises targetEq) sourceGround targetGround

/-- Source-aware form of `authoredRule_mork_fire`, valid in any workspace
containing the translated source. -/
theorem authoredRule_mork_sourceRuleFire
    {base : BasePremiseEvaluator} {lang : LanguageDef} {fuel : Nat}
    {source target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {rule : RewriteRule}
    {initial final : Mettapedia.OSLF.MeTTaIL.Match.Bindings}
    (ruleMember : rule ∈ lang.rewrites)
    (matched : initial ∈
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        lang rule source)
    (premises : PremisesAt base lang fuel initial rule.premises final)
    (targetEq :
      Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule
        lang rule final = target)
    (workspace : Space)
    (sourceMember : morkPatternToAtom source ∈ workspace)
    (sourceGround : isGroundAtom (morkPatternToAtom source) = true)
    (targetGround : isGroundAtom (morkPatternToAtom target) = true) :
    ∃ compiledRule ∈ compiledContextSourceRules base lang (fuel + 1) source,
      workspace.erase (morkPatternToAtom source) ∪ {morkPatternToAtom target} ∈
        fireSourceRule workspace compiledRule := by
  exact stepAt_compiles_to_mork_sourceRule
    (.rule ruleMember matched premises targetEq) workspace sourceMember
      sourceGround targetGround

section Canaries
#check @authoredRule_mork_fire
#check @authoredRule_mork_sourceRuleFire
end Canaries

section AxiomAudit
#print axioms authoredRule_mork_fire
#print axioms authoredRule_mork_sourceRuleFire
end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK.ExtendedBridge
