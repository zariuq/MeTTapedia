import Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef

/-!
# Operational canaries for named-to-resolved FOF

These exact-list checks exercise the authored binder-resolution rules with
the explicit pattern-equality relation service. They distinguish nearest
binder lookup, outer-binder lookup, nested shadowing, and fail-closed free
variables.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

def relations : RelationEnv :=
  PatternEqualityDecision.relationEnv

namespace Canary

def nameX : Pattern := a "X"
def nameY : Pattern := a "Y"

def shadowingSource : Pattern :=
  sourceFormula "all" [sourceName nameX,
    sourceFormula "and" [
      sourceFormula "equal" [sourceVariable nameX, sourceVariable nameX],
      sourceFormula "ex" [sourceName nameX,
        sourceFormula "equal"
          [sourceVariable nameX, sourceVariable nameX]]]]

def shadowingTarget : Pattern :=
  targetFormula "all" [
    targetFormula "and" [
      targetFormula "equal"
        [targetVariable targetIndexZero, targetVariable targetIndexZero],
      targetFormula "ex" [
        targetFormula "equal"
          [targetVariable targetIndexZero, targetVariable targetIndexZero]]]]

def freeVariableSource : Pattern :=
  sourceFormula "equal" [sourceVariable nameX, sourceVariable nameX]

theorem head_lookup_is_zero :
    rewriteAt (engineBasePremises relations) language 12
        (lookup nameX (environmentCons nameX environmentNil)) =
      [targetIndexZero] := by
  decide +kernel

theorem outer_lookup_is_successor :
    rewriteAt (engineBasePremises relations) language 12
        (lookup nameX
          (environmentCons nameY (environmentCons nameX environmentNil))) =
      [targetIndexSucc targetIndexZero] := by
  decide +kernel

theorem shadowing_resolves_to_nearest_binder :
    rewriteAt (engineBasePremises relations) language 12
        (resolveClosed shadowingSource) = [shadowingTarget] := by
  decide +kernel

theorem free_variable_is_rejected :
    rewriteAt (engineBasePremises relations) language 12
        (resolveClosed freeVariableSource) = [] := by
  decide +kernel

end Canary

#print axioms Canary.head_lookup_is_zero
#print axioms Canary.outer_lookup_is_successor
#print axioms Canary.shadowing_resolves_to_nearest_binder
#print axioms Canary.free_variable_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpNamedFofToResolvedLanguageDef
