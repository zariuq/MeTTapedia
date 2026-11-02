import Mettapedia.Languages.Maude.SchemaLink
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoEmissionAgreement

/-! The certified Peano realizer interprets the actual linked IR theory.
Linking checks complete structure and supplies an equality witness. Display
names may differ; equation paths transport through the proved name change.
The source-to-IR frontend remains a separate correctness boundary.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.LinkedPeano

open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Eval (PureReturns)
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Program)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open WireKit

theorem emitted_source_run {actual : Maude.Theory}
    (link : Maude.SchemaLink.Witness actual Maude.Examples.peano)
    {context : Maude.VariableContext} {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? (PeanoEmission.spec context) name .classes = .ok emitted)
    (state : State) (source : Maude.Term)
    (typed : Maude.HasSort actual.signature context source "Nat") (ticks quantum : Nat) :
    PureReturns (CompleteEmission.runtime.append emitted) [] state
      (.expression (.symbol (CompleteEmission.runHead name) ::
        [CompleteExecution.patternValue (encode source), number ticks, number quantum])) state
      (encoded (CompleteExecution.classTraceTerm (PeanoProducer.compiledPlan context)
        (PeanoRunner.run context source ticks quantum))) ∧
    (∃ result, (PeanoRunner.run context source ticks quantum).state = encode result ∧
      Maude.EquationPath actual context "Nat" source result) ∧
    ((PeanoRunner.run context source ticks quantum).phase = .done →
      (PeanoRunner.run context source ticks quantum).state = encode (Maude.PeanoNormalization.reduce source)) := by
  have accepted : (Maude.SchemaLink.check actual Maude.Examples.peano).isSome = true :=
    (Maude.SchemaLink.check_reflects actual Maude.Examples.peano).mpr link.same
  have typedReference : Maude.HasSort Maude.Examples.peano.signature context source "Nat" := by
    rw [← Maude.SchemaLink.signature_eq accepted]
    exact typed
  obtain ⟨runs, path, done⟩ := PeanoEmission.emitted_source_run ok state source typedReference ticks quantum
  obtain ⟨result, endpoint, path⟩ := path
  exact ⟨runs, ⟨result, endpoint, (Maude.SchemaLink.equationPath_iff accepted).mpr path⟩, done⟩

theorem emitted_source_explore {actual : Maude.Theory}
    (link : Maude.SchemaLink.Witness actual Maude.Examples.peano)
    {context : Maude.VariableContext} {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? (PeanoEmission.spec context) name .classes = .ok emitted)
    (state : State) {source target : Maude.Term}
    (typed : Maude.HasSort actual.signature context source "Nat")
    (path : Maude.EquationPath actual context "Nat" source target) :
    ∃ work, encode target ∈ (CompleteEmission.explored (PeanoEmission.spec context) (encode source) work).nodes.map (·.state) ∧
      PureReturns (CompleteEmission.runtime.append emitted) [] state
        (.expression (.symbol (CompleteEmission.exploreHead name) :: [CompleteExecution.patternValue (encode source), number work]))
        state (CompleteExecution.patternsValue
          ((CompleteEmission.explored (PeanoEmission.spec context) (encode source) work).nodes.map (·.state))) := by
  have accepted : (Maude.SchemaLink.check actual Maude.Examples.peano).isSome = true :=
    (Maude.SchemaLink.check_reflects actual Maude.Examples.peano).mpr link.same
  have typedReference : Maude.HasSort Maude.Examples.peano.signature context source "Nat" := by
    rw [← Maude.SchemaLink.signature_eq accepted]
    exact typed
  exact PeanoEmission.emitted_source_explore ok state typedReference
    ((Maude.SchemaLink.equationPath_iff accepted).mp path)

theorem emitted_explore_source_sound {actual : Maude.Theory}
    (link : Maude.SchemaLink.Witness actual Maude.Examples.peano)
    {context : Maude.VariableContext} {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? (PeanoEmission.spec context) name .classes = .ok emitted)
    (state : State) (source : Maude.Term)
    (typed : Maude.HasSort actual.signature context source "Nat") (work : Nat) :
    PureReturns (CompleteEmission.runtime.append emitted) [] state
      (.expression (.symbol (CompleteEmission.exploreHead name) :: [CompleteExecution.patternValue (encode source), number work]))
      state (CompleteExecution.patternsValue
        ((CompleteEmission.explored (PeanoEmission.spec context) (encode source) work).nodes.map (·.state))) ∧
    ∀ target ∈ (CompleteEmission.explored (PeanoEmission.spec context) (encode source) work).nodes.map (·.state),
      ∃ result, target = encode result ∧ Maude.EquationPath actual context "Nat" source result := by
  have accepted : (Maude.SchemaLink.check actual Maude.Examples.peano).isSome = true :=
    (Maude.SchemaLink.check_reflects actual Maude.Examples.peano).mpr link.same
  have typedReference : Maude.HasSort Maude.Examples.peano.signature context source "Nat" := by
    rw [← Maude.SchemaLink.signature_eq accepted]
    exact typed
  obtain ⟨runs, sound⟩ := PeanoEmission.emitted_explore_source_sound ok state source typedReference work
  refine ⟨runs, ?_⟩
  intro target member
  obtain ⟨result, endpoint, path⟩ := sound target member
  exact ⟨result, endpoint, (Maude.SchemaLink.equationPath_iff accepted).mpr path⟩

#print axioms emitted_source_run
#print axioms emitted_source_explore
#print axioms emitted_explore_source_sound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.LinkedPeano
