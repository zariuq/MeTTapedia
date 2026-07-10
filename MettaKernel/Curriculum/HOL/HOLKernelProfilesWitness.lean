import Mettapedia.GSLT.LanguageDef.HOLKernelProfiles

/-!
# HOL Kernel Profile Witnesses

These checks exercise the new HOL kernel profiles through the OSLF
LanguageDef reducer.  They are deliberately narrow: the current pipeline
consumes rewrite rules plus relation tuples induced from finite Datalog closure
over `LanguageDef.logic`.  Proof-checker adequacy remains an open obligation
recorded in the NTT claim tracker.
-/

namespace Mettapedia.MettaKernel.Curriculum.HOLKernelProfilesWitness

open Mettapedia.GSLT.LanguageDef.HOLKernelProfiles
open Mettapedia.OSLF.MeTTaIL.Engine

#guard
    hol4LogicRelationEnv.tuples "isBool" [A] == [[A], [B], [AndAA]]

#guard
    hol4NoLogicRelationEnv.tuples "isBool" [A] == []

#guard
    rewriteWithContextWithPremisesUsing hol4LogicRelationEnv hol4LcfKernel hol4DischWitness ==
      [hol4DischResult]

#guard
    rewriteWithContextWithPremisesUsing hol4NoLogicRelationEnv hol4NoLogic hol4DischWitness ==
      []

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel hol4DischWitness ==
      []

#guard
    rewriteWithContextWithPremisesUsing hol4LogicRelationEnv hol4LcfKernel hol4MPWitness ==
      [hol4MPResult]

#guard
    rewriteWithContextWithPremisesUsing hol4LogicRelationEnv hol4LcfKernel hol4BadMPWitness ==
      []

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel hol4MPWitness ==
      []

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel holLightReflWitness ==
      [holLightReflResult]

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel holLightBadEqMPWitness ==
      []

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel holLightAssumeAWitness ==
      [holLightAssumeAResult]

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel holLightConjAAWitness ==
      [holLightConjAAResult]

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel holLightConjunct1AAWitness ==
      [holLightConjunct1AAResult]

#guard
    (rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel
      holLightDischAACoreWitness).contains holLightDischAACoreResult

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel holLightImpDefAAWitness ==
      [holLightImpDefAAResult]

#guard
    (rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel
      holLightSelfImpWitness).contains holLightSelfImpResult

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel
      holLightPrimitiveDischShortcutWitness == []

#guard
    rewriteWithContextWithPremisesUsing holLightLogicRelationEnv holLightEqKernel
      holLightBadSelfImpWitness == []

#guard
    checkProofArticleWithEnv hol4LogicRelationEnv hol4LcfKernel 4 hol4SelfMPArticle

#guard
    checkProofArticleWithEnv holLightLogicRelationEnv holLightEqKernel 4 hol4SelfMPArticle == false

#guard
    checkProofArticleWithEnv hol4LogicRelationEnv hol4LcfKernel 2 hol4BadMPArticle == false

#guard
    checkProofArticleWithEnv holLightLogicRelationEnv holLightEqKernel 6 holLightSelfImpArticle

#guard
    checkProofArticleWithEnv hol4LogicRelationEnv hol4LcfKernel 6 holLightSelfImpArticle == false

#guard
    checkProofArticleWithEnv holLightLogicRelationEnv holLightEqKernel 3
      holLightPrimitiveDischShortcutArticle == false

#guard
    checkProofArticleWithEnv holLightLogicRelationEnv holLightEqKernel 6
      holLightBadSelfImpArticle == false

#guard Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.validate holLightEqKernel == []
#guard Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef.validate hol4LcfKernel == []

end Mettapedia.MettaKernel.Curriculum.HOLKernelProfilesWitness
