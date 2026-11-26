import Mettapedia.Languages.MeTTa.SpaceTheory.HEObservationReplacement
import Mettapedia.Languages.MeTTa.SpaceTheory.PeTTaExecution

/-!
# The common part of each dialect's snapshot theories

The base keeps the steps that do not require a particular declaration
view. Grounded services and actual space data are still arguments
of the dialect, not replaced by the empty store. A snapshot supplies
what its declarations can justify beyond this common part. In
particular, having no declaration in one snapshot does not authorize
the unknown-head behavior in every extension.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.DialectBase

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational (OperationalTranslation)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (WorldEnvironment Policy Result)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (WorldConfiguration)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.ProgramReplay
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

variable {Context World : Type}

/-- Only the declaration view varies. The world and its services keep
their dialect meanings. -/
def he (env : WorldEnvironment Context World) (policy : Policy) : GSLT :=
  equalityGSLT (WorldConfiguration Context World) fun first second =>
    ∀ view, (HEControlOnTransform.source {env with view} policy).Step first second

def heInclude (env : WorldEnvironment Context World) (policy : Policy) (view : World → Context → Space) :
    OperationalTranslation (he env policy) (HEControlOnTransform.source {env with view} policy) where
  mapTerm := id
  mapEquiv := id
  mapStep := fun stable => stable view

/-- Native calls, entering contexts, and the independent application,
binding and return phases are inherited from HE. Their independence
was established from the source transition rules. -/
theorem he_independent_iff (env : WorldEnvironment Context World) (policy : Policy)
    {first : HEFocused.Focus Context World} {second : WorldConfiguration Context World}
    (independent : HEObservationReplacement.Independent first) :
    (he env policy).Step (HEFocused.restore first) second ↔
      (HEControlOnTransform.source env policy).Step (HEFocused.restore first) second := by
  constructor
  · intro stable
    exact stable env.view
  · intro current view
    exact (HEObservationReplacement.protected_step env view policy (.independent independent)).mp current

theorem he_publication (env : WorldEnvironment Context World) (policy : Policy) (world : World)
    (scope : Context) (answer : Result) (pending already : List Result) :
    (he env policy).Step ⟨world, scope, .returning (answer :: pending), [], already⟩
      ⟨world, scope, .returning pending, [], already ++ [answer]⟩ := by
  intro view
  exact (HEControlOnTransform.source_step_iff {env with view} policy _ _).mpr .publish

/-- The PeTTa base varies the declared program, not the state carried
by the evaluator. Consequently inherited matching, IO and grounded
operations still act on the actual named spaces. -/
def petta : GSLT :=
  equalityGSLT Eval.Configuration fun first second =>
    ∀ atoms, (PeTTaExecution.theoryAt atoms).Step first second

def pettaInclude (atoms : List Atom) :
    OperationalTranslation petta (PeTTaExecution.theoryAt atoms) where
  mapTerm := id
  mapEquiv := id
  mapStep := fun stable => stable atoms

def pettaLiveInclude : OperationalTranslation petta LiveRegistry.theory where
  mapTerm := id
  mapEquiv := id
  mapStep := fun {first second} stable =>
    (PeTTaExecution.live_rewrite_iff first second).mpr (stable first.state.core)

theorem petta_grounded {first : Eval.Configuration} {bindings : Subst} {head : String}
    {position : Nat} {values answers : List Atom} {after : Effects.State}
    (ready : first.control = .arguments bindings (.function head) [] values position)
    (ordinary : Eval.ioHead head = false) (native : StdLib.known head = true)
    (runs : StdLib.apply first.state head values = .ok (after, answers)) :
    petta.Step first {first with state := after, control := .returned answers} := by
  intro atoms
  exact DeclarativeSpec.Transition.primitive ready ordinary native runs

theorem petta_push_let {first : Eval.Configuration} {bindings : Subst} {pattern value body : Atom}
    (ready : first.control = .evaluate bindings (.expression [.symbol "let", pattern, value, body])) :
    petta.Step first
      {first with
        control := .evaluate bindings value
        frames := .bind bindings pattern body :: first.frames} := by
  intro atoms
  exact DeclarativeSpec.Transition.let_enter ready

theorem petta_without_program_is_not_the_base :
    let before := Eval.start Effects.empty (.expression [.symbol "temperature"])
    let readAsData : Eval.Configuration :=
      {before with control := .arguments [] .data [.symbol "temperature"] [] 0}
    let define := Atom.expression [.symbol "=", .expression [.symbol "temperature"], .symbol "warm"]
    (PeTTaExecution.theoryAt []).Step before readAsData ∧
      ¬ (PeTTaExecution.theoryAt [define]).Step before readAsData ∧
      ¬ petta.Step before readAsData := by
  dsimp only
  have emptySnapshot : (PeTTaExecution.theoryAt []).Step (Eval.start Effects.empty (.expression [.symbol "temperature"]))
      {Eval.start Effects.empty (.expression [.symbol "temperature"]) with
        control := .arguments [] .data [.symbol "temperature"] [] 0} := by
    rw [PeTTaExecution.snapshot_rewrite_iff]
    rfl
  refine ⟨emptySnapshot, ?_, ?_⟩
  · intro supposed
    have computed := (PeTTaExecution.snapshot_rewrite_iff _ _ _).mp supposed
    have incompatible := congrArg Eval.Configuration.control (Option.some.inj computed)
    cases incompatible
  · intro stable
    have incompatible := (PeTTaExecution.snapshot_rewrite_iff _ _ _).mp
      (stable [.expression [.symbol "=", .expression [.symbol "temperature"], .symbol "warm"]])
    cases congrArg Eval.Configuration.control (Option.some.inj incompatible)

end Mettapedia.Languages.MeTTa.SpaceTheory.DialectBase
