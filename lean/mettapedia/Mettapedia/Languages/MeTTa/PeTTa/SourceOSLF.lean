import Mettapedia.Languages.MeTTa.PeTTa.SourceExecution
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Behavioral predicates of source execution

The source machine uses the existing equation-aware GSLT-to-OSLF construction.
Its reduction span contains actual control transitions, including effects and
I/O. The observation laws below concern those transitions: printed output is
append-only, and parsed input is consumed in order.

The forward box expresses preservation of an observation through every next
step. It is distinct from the predecessor box in OSLF's diamond/box adjunction.
Guest checking and cache invariants require further program-specific proofs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SourceOSLF

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SourceProgram (Program)
open SourceEvaluation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities

def system (program : Program) := gsltOSLF (theory program)

theorem next_configuration_type (program : Program) (source target : Configuration) :
    (system program).satisfies (S := ()) source
      (exactTargetNativeType (theory program) target).pred ↔
        step program source = some target :=
  satisfies_exactTargetNativeType_iff_step (theory program) source target

theorem output_extends (program : Program) (source target : Configuration)
    (transition : step program source = some target) :
    ∃ added, target.output = source.output ++ added := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals simp only [step] at transition
      all_goals
        repeat' first
          | contradiction
          | split at transition
          | solve
              | cases transition
                simp_all

theorem input_is_consumed_in_order (program : Program) (source target : Configuration)
    (transition : step program source = some target) :
    ∃ consumed, source.input = consumed ++ target.input := by
  cases source with
  | mk state control frames input output =>
      cases control <;> cases frames
      all_goals simp only [step] at transition
      all_goals
        repeat' first
          | contradiction
          | split at transition
          | solve
              | cases transition
                simp_all
                all_goals first | exact ⟨[], rfl⟩ | exact ⟨[_], rfl⟩

def Printed (history : List Atom) (configuration : Configuration) : Prop :=
  ∃ suffix, configuration.output = history ++ suffix

theorem printed_preserved (program : Program) (history : List Atom) :
    Printed history ≤ derivedForwardBox (gsltSpan (theory program)) (Printed history) := by
  intro source observed edge atSource
  obtain ⟨suffix, before⟩ := observed
  obtain ⟨added, after⟩ := output_extends program edge.source edge.target edge.step
  change edge.source = source at atSource
  subst source
  refine ⟨suffix ++ added, ?_⟩
  change edge.target.output = history ++ (suffix ++ added)
  rw [after, before, List.append_assoc]

theorem printed_step_image (program : Program) (history : List Atom) :
    derivedImage (gsltSpan (theory program)) (Printed history) ≤ Printed history :=
  (preserved_iff_derivedImage_le (gsltSpan (theory program)) (Printed history)).mp
    (printed_preserved program history)

end Mettapedia.Languages.MeTTa.PeTTa.SourceOSLF
