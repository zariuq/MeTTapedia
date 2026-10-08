import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# PeTTa execution as an OSLF-generating GSLT

The operational rules in `DeclarativeSpec`, including effects and I/O, form
the GSLT in `Eval`, and OSLF modalities are generated from that graph. The
type of configurations reachable in one step is exactly the transition
judgment and, by adequacy, the executable step function.
Printed output only grows and input is consumed in order along every
transition. The selected-rewrite view, a GSLT built from the `CoreDecl` relation over
`Pattern`, is in `PatternRewrite.OperationalGSLT`; relating the two needs a
fragment simulation, not a renaming.
-/


namespace Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Eval
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities

def system (program : Program) := gsltOSLF (theory program)

/-- The generated modality directly classifies the declarative transitions. -/
theorem next_configuration_type_iff_transition
    (program : Program) (source target : Configuration) :
    (system program).satisfies (S := ()) source
      (exactTargetNativeType (theory program) target).pred ↔
        DeclarativeSpec.Transition program source target :=
  satisfies_exactTargetNativeType_iff_step (theory program) source target

theorem next_configuration_type (program : Program) (source target : Configuration) :
    (system program).satisfies (S := ()) source
      (exactTargetNativeType (theory program) target).pred ↔
        step program source = some target :=
  (next_configuration_type_iff_transition program source target).trans
    (step_iff_transition program source target).symm

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
  obtain ⟨added, after⟩ := output_extends program edge.source edge.target
    (transition_step edge.step)
  change edge.source = source at atSource
  subst source
  refine ⟨suffix ++ added, ?_⟩
  change edge.target.output = history ++ (suffix ++ added)
  rw [after, before, List.append_assoc]

theorem printed_step_image (program : Program) (history : List Atom) :
    derivedImage (gsltSpan (theory program)) (Printed history) ≤ Printed history :=
  (preserved_iff_derivedImage_le (gsltSpan (theory program)) (Printed history)).mp
    (printed_preserved program history)

/-- Finiteness is preserved by the actual judgment-generated GSLT. -/
theorem finite_cells_preserved (program : SpaceSemantics.Program) :
    (fun configuration : Configuration => NamedSpaces.Store.FiniteCells configuration.state) ≤
      derivedForwardBox (gsltSpan (theory program))
        (fun configuration => NamedSpaces.Store.FiniteCells configuration.state) := by
  intro source finite edge atSource
  change edge.source = source at atSource
  subst source
  exact DeclarativeSpec.transition_finite_cells finite edge.step

theorem empty_tail_preserved (program : SpaceSemantics.Program) :
    (fun configuration : Configuration => NamedSpaces.Store.EmptyTail configuration.state []) ≤
      derivedForwardBox (gsltSpan (theory program))
        (fun configuration => NamedSpaces.Store.EmptyTail configuration.state []) := by
  intro source vacant edge atSource
  change edge.source = source at atSource
  subst source
  exact DeclarativeSpec.transition_empty_tail vacant edge.step

end Mettapedia.Languages.MeTTa.PeTTa.OperationalGSLT
