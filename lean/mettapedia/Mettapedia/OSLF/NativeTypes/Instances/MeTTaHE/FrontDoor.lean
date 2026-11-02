import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EngineAgreement
import Mettapedia.Languages.MeTTa.HE.CoreFragment

/-!
# HE MeTTa at the front door

HE MeTTa's machine is authored as a language (`mettaHE`, fifty-eight rules) whose premises query relations a runtime
supplies (`isEmpty`, `typeOf`, `eqQueryResult`, …), in any relation environment. The language is aligned and
equation-free (`profile`, `equationFree`), so in every relation environment its native types are read through the
engine's steps (`EngineAgreement`):

- **some step to a term** (`sat_step_iff`): `◇(is t)` at a state holds exactly when the engine steps there;
- **no step** (`sat_stuck_iff`): `□⊥` holds exactly when the engine has no step to a state;
- **HE's runtime core fragment answers at the front door** (`sat_of_core_step`): a step of the premise-bearing core
  fragment of the HE runtime (`HEPremiseCoreStep`) is a front-door step, through the established embedding into the
  language's least contextual relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.MeTTaHE

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.Languages.MeTTa.HE.LanguageDef (mettaHE)

/-- **The language is aligned**: its reference steps are its engine steps. -/
theorem profile : ReferenceProfile mettaHE := by
  have checked : mettaHE.rewrites.all Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned = true := by decide +kernel
  exact fun rule member => List.all_eq_true.mp checked rule member

theorem equationFree : mettaHE.isEquationFree = true := by decide +kernel

/-- The front door's reading of HE MeTTa in a relation environment. -/
noncomputable abbrev Machine (relEnv : RelationEnv) : NativeStructure Pattern := referenceStructure relEnv mettaHE

/-- **Some step to a term is the engine's step.** -/
theorem sat_step_iff (relEnv : RelationEnv) {source target : Pattern} (sourceState : IsState source)
    (targetState : IsState target) :
    (Machine relEnv).sat Env.closed (.possibly .any (.is target)) source ↔
      Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv mettaHE source target :=
  sat_possibly_is_iff profile equationFree sourceState targetState

/-- **No step is the engine's having none.** -/
theorem sat_stuck_iff (relEnv : RelationEnv) {source : Pattern} (sourceState : IsState source) :
    (Machine relEnv).sat Env.closed (.necessarily .any .bot) source ↔
      ∀ target, IsState target → ¬ Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv mettaHE source target :=
  Mettapedia.OSLF.NativeTypes.GeneratedLogic.sat_stuck_iff profile equationFree sourceState

/-- **HE's runtime core fragment answers at the front door**: a premise-bearing core step of the HE runtime is a step
of the front door. -/
theorem sat_of_core_step {relEnv : RelationEnv} {source target : Pattern}
    (core : Mettapedia.Languages.MeTTa.HE.CoreFragment.HEPremiseCoreStep relEnv source target)
    (sourceState : IsState source) (targetState : IsState target) :
    (Machine relEnv).sat Env.closed (.possibly .any (.is target)) source :=
  (sat_step_iff relEnv sourceState targetState).mpr
    (Mettapedia.Languages.MeTTa.HE.CoreFragment.premiseCoreToLanguageStep core)

end Mettapedia.OSLF.NativeTypes.Instances.MeTTaHE
