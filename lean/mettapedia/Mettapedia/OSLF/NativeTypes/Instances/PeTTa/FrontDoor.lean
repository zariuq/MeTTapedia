import Mettapedia.OSLF.NativeTypes.GeneratedLogic.EngineAgreement
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef

/-!
# PeTTa at the front door

PeTTa's machine is authored as a language over its configurations (`ConfigurationLanguageDef.language`), whose
computational premises a program supplies (`relationEnv`). The language is aligned and equation-free (`profile`,
`ConfigurationLanguageDef.equation_free`), so its native types are read through the engine's steps
(`EngineAgreement`), and the engine's steps are PeTTa's own transitions:

- **a configuration's transitions are its native type** (`sat_step_iff`): some step from the encoded configuration to
  a term holds exactly when PeTTa's transition relation takes the configuration to a configuration that term encodes;
- **and its executable evaluator's** (`sat_step_iff_eval`): exactly when `Eval.step` computes that configuration;
- **a configuration has no step exactly when PeTTa has no transition from it** (`sat_stuck_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef (language relationEnv equation_free generated_step_iff)
open Mettapedia.Languages.MeTTa.PeTTa.ConfigurationEncoding (encode cellSupportAfter)

/-- **The language is aligned**: its reference steps are its engine steps. -/
theorem profile : ReferenceProfile language := by
  have checked : language.rewrites.all Mettapedia.OSLF.MeTTaIL.ReferenceStep.ruleAligned = true := by decide +kernel
  exact fun rule member => List.all_eq_true.mp checked rule member

/-- The front door's reading of PeTTa's configurations under a program. -/
noncomputable abbrev Machine (program : SpaceSemantics.Program) : NativeStructure Pattern :=
  referenceStructure (relationEnv program) language

/-- The engine's step is the generated language's step, the language having no equations. -/
theorem langReduces_iff_generated (program : SpaceSemantics.Program) (source target : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing (relationEnv program) language source target ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing (relationEnv program) language).Step source target :=
  (Mettapedia.GSLT.LanguageDef.EquationSemantics.stepModuloEquations_iff_step_of_no_generators equation_free source
    target).symm

/-- **A configuration's transitions are its native type**: some step from the encoded configuration reaches a term
exactly when PeTTa's transition relation takes the configuration to the configuration that term encodes. -/
theorem sat_step_iff (program : SpaceSemantics.Program) (source : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none) {target : Pattern}
    (sourceState : IsState (encode source names)) (targetState : IsState target) :
    (Machine program).sat Env.closed (.possibly .any (.is target)) (encode source names) ↔
      ∃ after, DeclarativeSpec.Transition program source after ∧ target = encode after (cellSupportAfter source names) := by
  rw [sat_possibly_is_iff profile equation_free sourceState targetState, langReduces_iff_generated,
    generated_step_iff program source names vacant covers]

/-- **And its executable evaluator's**: the step reaches exactly the encoding of what `Eval.step` computes. -/
theorem sat_step_iff_eval (program : SpaceSemantics.Program) (source : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none) {target : Pattern}
    (sourceState : IsState (encode source names)) (targetState : IsState target) :
    (Machine program).sat Env.closed (.possibly .any (.is target)) (encode source names) ↔
      ∃ after, Eval.step program source = some after ∧ target = encode after (cellSupportAfter source names) := by
  rw [sat_step_iff program source names vacant covers sourceState targetState]
  simp only [Eval.step_iff_transition]

/-- **A configuration has no step exactly when PeTTa has no transition from it.** -/
theorem sat_stuck_iff (program : SpaceSemantics.Program) (source : Eval.Configuration) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail source.state [])
    (covers : ∀ name, name ∉ names → source.state.cells name = none)
    (sourceState : IsState (encode source names))
    (targetsState : ∀ after, IsState (encode after (cellSupportAfter source names))) :
    (Machine program).sat Env.closed (.necessarily .any .bot) (encode source names) ↔
      ∀ after, ¬ DeclarativeSpec.Transition program source after := by
  rw [Mettapedia.OSLF.NativeTypes.GeneratedLogic.sat_stuck_iff profile equation_free sourceState]
  constructor
  · intro none after transition
    exact none _ (targetsState after) ((langReduces_iff_generated program _ _).mpr
      ((generated_step_iff program source names vacant covers _).mpr ⟨after, transition, rfl⟩))
  · intro none target _ step
    obtain ⟨after, transition, -⟩ := (generated_step_iff program source names vacant covers target).mp
      ((langReduces_iff_generated program _ _).mp step)
    exact none after transition

end Mettapedia.OSLF.NativeTypes.Instances.PeTTa
