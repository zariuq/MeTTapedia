import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSpecialization
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveControls

/-! # Specialization controls using the authored type rows -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSpecialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlySpecialization
open NativeTypeCallGraph NativeTypeRecursiveDriver NativeTypeRecursiveControls

private def pending : PrimitiveStore
  | .closure _ => none
  | question => primitiveStore question

private def call : Call := .infer true (sym "a")
private def saved := prepare ops pending 2 1 call

private theorem saved_reads :
    saved.reads = [(.annotations (sym "a"), some (.types [sym "A"]))] := by
  have trace : (run pending (expand ops 1 call)).reads =
      [(.annotations (sym "a"), some (.types [sym "A"])), (.closure [sym "A"], none)] := by
    rw [expanded_reads ops pending 0 call]
    cbv
  change (drive (staticAnnotation pending) pending 2 (expand ops 1 call)).reads = _
  rw [drive_reads_from_source, trace]
  rfl

/-- A pending closure can finish later without discarding the discharged
annotation read. The source port supplies the authored subtype edge. -/
theorem closure_stays_live :
    saved.reads = [(.annotations (sym "a"), some (.types [sym "A"]))] ∧
      (saved.tryRun pending).map Observation.answer = some none ∧
      (saved.tryRun primitiveStore).map (fun result => publishTypes result.answer) =
        some (some [sym "A", sym "B"]) := by
  refine ⟨saved_reads, ?_, ?_⟩
  · have valid : Agrees pending saved.reads := drive_agrees _ _ _ _
    simp only [Residual.tryRun, (checkReads_iff _ _).mpr valid, if_true, Option.map_some,
      saved.exactOn pending valid, expanded_answer]
    cbv
  · have actual : primitiveStore (.annotations (sym "a")) = some (.types [sym "A"]) := rfl
    have valid : Agrees primitiveStore saved.reads := by
      simp [Agrees, saved_reads, actual]
    simp only [Residual.tryRun, (checkReads_iff _ _).mpr valid, if_true, Option.map_some,
      saved.exactOn primitiveStore valid, expanded_answer]
    exact congrArg some inferred_and_tuple_questions_differ.1

private def withoutAnnotation : PrimitiveStore
  | .annotations (.symbol "a") => some (.types [])
  | question => primitiveStore question

/-- Completed empty annotations and an unfinished closure take different
source branches. An earlier annotation cannot authorize the changed branch. -/
theorem changed_annotation_declines :
    saved.tryRun withoutAnnotation = none ∧
      publishTypes (evaluate ops withoutAnnotation 1 call) = some [Atom.undefinedType] := by
  constructor
  · simp [Residual.tryRun, checkReads, saved_reads, withoutAnnotation, sym]
  · cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSpecialization
