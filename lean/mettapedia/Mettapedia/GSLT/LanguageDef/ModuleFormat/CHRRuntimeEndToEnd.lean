import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimePreparation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineObservation

/-! Ground CHR (C0) through the lang library's package port, end to end in
the PeTTa evaluator model. A ready preparation emits text that loads as the
port runtime of the admitted program and its seeds; in that runtime `begin`,
`advance` and `outcome` run the refined CHR machine
(`CHRMachineExecution.port_runs`); and a completed run, printed and observed,
publishes the constraints of a completed refined CHR run from the same seeds,
as a multiset. CeTTa's C evaluator, reader and printer correspond to the model
by tests; the provider's own wire and dictionary strings are decoded as
premises. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler

open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRMachineExecution
  (completeResult orderedContents observed_refines portRuntime)

theorem declared_prop (program : CHR.Program) (name : String) (arity : Nat)
    (holds : declared program name arity = true) : CHR.Declared program name arity := by
  simp only [declared, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at holds
  exact holds

/-- **C0 in the model, from preparation to observation.** -/
theorem prepared_end_to_end (wire rows separator : String) (lowered : CHRPrologLowering.Program)
    (captured : List (Nat × CHR.Constraint)) (definitions : String)
    (ready : prepareRun wire rows "lang:compiled" = .ok (.ready lowered captured definitions)) :
    (SpaceSemantics.readProgram definitions).map (CHRMachineSource.library.base.append ·) =
        .ok (portRuntime (CHR.Machine.table lowered.program)
          ((seedsOf lowered captured).map CHR.Constraint.asHead) ticksPerUnit) ∧
      ∀ (dictionaryText data : String) (dictionary : Dictionary) (budget : Nat) (final : CHR.Machine.State),
        dictionary? dictionaryText = .ok dictionary →
        (seedsOf lowered captured).length = dictionary.captured.length + dictionary.queries →
        CHR.Machine.advance (CHR.Machine.table lowered.program) budget
          (CHR.Machine.start ((seedsOf lowered captured).map CHR.Constraint.asHead)) = final →
        final.status = .running → final.tasks = [] →
        ReadAfterRender.render? (completeResult final) = some data →
        observe wire dictionaryText data separator =
            .ok (completeJson dictionary final.seeds.reverse (orderedContents final.store)) ∧
          ∃ abstract store, Relation.ReflTransGen (CHR.Step lowered.program)
              (CHR.initial (seedsOf lowered captured)) abstract ∧
            CHR.observe abstract = .completed store ∧
            ((orderedContents final.store).map Prod.snd).Perm store := by
  obtain ⟨read, admitted, seeded, rendered, _⟩ :=
    prepareRun_ready wire rows "lang:compiled" lowered captured definitions ready
  refine ⟨definitions_runtime lowered.program (seedsOf lowered captured) definitions rendered, ?_⟩
  intro dictionaryText data dictionary budget final dictionaryRead counted reached running finished printed
  exact observed_refines wire dictionaryText data separator lowered dictionary (seedsOf lowered captured) budget
    final read dictionaryRead admitted (fun constraint member => declared_prop _ _ _ (seeded constraint member))
    counted reached running finished printed

#print axioms prepared_end_to_end

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
