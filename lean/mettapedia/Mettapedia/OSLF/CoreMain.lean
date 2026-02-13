import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Semantics
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReduces
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.OSLF.MeTTaIL.MatchSpec
import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.RhoCalculus.Soundness
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.RhoCalculus.Engine
import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.RhoInstance
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.FULLStatus
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.GeneratedTyping
import Mettapedia.OSLF.Framework.SynthesisBridge
import Mettapedia.OSLF.Framework.ToposReduction
import Mettapedia.OSLF.Framework.LambdaInstance
import Mettapedia.OSLF.Framework.PetriNetInstance
import Mettapedia.OSLF.Framework.TinyMLInstance
import Mettapedia.OSLF.Framework.MeTTaMinimalInstance
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.ConstructorFibration
import Mettapedia.OSLF.Framework.ModalEquivalence
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Framework.PLNSelectorGSLT
import Mettapedia.OSLF.Framework.BeckChevalleyOSLF
import Mettapedia.OSLF.MeTTaCore.Premises
import Mettapedia.OSLF.MeTTaCore.FullLanguageDef
import Mettapedia.OSLF.Framework.MeTTaFullInstance
import Mettapedia.OSLF.Formula

/-!
# OSLF Core Entry Point

Sorry-free core entry point for OSLF + GSLT + premise-aware rewriting pipeline.

This file intentionally excludes `Mettapedia.OSLF.PiCalculus.Main`, so reviewers
can import one entrypoint for the full core stack without pulling in current
π-calculus WIP.
-/

namespace Mettapedia.OSLF

export Mettapedia.OSLF.MeTTaCore.Premises (
  space0Atomspace
  space0Entries
  spaceEntriesOfPattern?
  atomspaceOfPattern?
  eqnLookupTuples
  noEqnLookupTuples
  neqTuples
  typeOfTuples
  notTypeOfTuples
  castTuples
  notCastTuples
  groundedCallTuples
  noGroundedCallTuples
)

export Mettapedia.OSLF.MeTTaCore.FullLanguageDef (
  mettaFull
  mettaFullOSLF
  mettaFullGalois
  mettaFullRelEnv
)

export Mettapedia.OSLF.Framework.MeTTaFullInstance (
  mettaFull_pathOrder
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph
  mettaFull_checker_sat_to_pathSemClosed_commDi_bc_graph_auto
  mettaFullSpecAtomCheck
  mettaFullSpecAtomSem
  mettaFull_checkLangUsing_sat_sound_specAtoms
  mettaFull_checkLang_sat_sound_specAtoms
)

#check Mettapedia.OSLF.Framework.FULLStatus.remaining_eq_nil
#check Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFull
#check Mettapedia.OSLF.MeTTaCore.FullLanguageDef.mettaFullOSLF

end Mettapedia.OSLF
