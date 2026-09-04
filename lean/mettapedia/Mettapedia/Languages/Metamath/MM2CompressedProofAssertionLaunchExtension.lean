import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSquare

/-!
# Scheduler-inert extension of the compressed assertion launch

Source-derived heap, node, stack, save, and scanner rows may surround the
canonical launch slice.  Positive matching is monotone, while rows with no
supported executable shell leave the scheduler inventory unchanged.  This
module lifts the launch square across exactly that frame boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchExtension

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrameMatch
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchScheduledStep
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchSelect
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private theorem canonical_direct_assertion_shell
    (context : DirectAssertionContext) :
    speculativeDirectAssertionDirective.atom ∈
      canonicalDirectAssertionSpace context := by
  unfold canonicalDirectAssertionSpace directAssertionMatchSlice
  simp

private theorem matcherRow_append
    (space extra : List Atom)
    (shell : speculativeDirectAssertionDirective.atom ∈ space)
    {substitution : Subst}
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          space.erase speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input).map Prod.fst) :
    substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          (space ++ extra).erase speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input).map Prod.fst := by
  have liveExact :
      (space ++ extra).erase speculativeDirectAssertionDirective.atom =
        space.erase speculativeDirectAssertionDirective.atom ++ extra :=
    List.erase_append_left extra shell
  rw [List.mem_map] at rowMember ⊢
  obtain ⟨⟨matchedSubstitution, consumed⟩, matched, rfl⟩ := rowMember
  refine ⟨(matchedSubstitution, consumed), ?_, rfl⟩
  rw [speculative_direct_assertion_input_exact] at matched ⊢
  rw [liveExact]
  exact cmatchPattern_mono []
    (speculativeDirectAssertionDirective.atom ::
      space.erase speculativeDirectAssertionDirective.atom)
    (speculativeDirectAssertionDirective.atom ::
      (space.erase speculativeDirectAssertionDirective.atom ++ extra))
    (mkPattern directAssertionPatterns)
    (fun atom member => by
      simp only [List.mem_cons] at member ⊢
      rcases member with rfl | member
      · exact Or.inl rfl
      · exact Or.inr (List.mem_append_left _ member))
    matchedSubstitution consumed matched

theorem ExactDirectAssertionLaunch.append
    (context : DirectAssertionContext) {space : List Atom}
    (launch : ExactDirectAssertionLaunch context space)
    (shell : speculativeDirectAssertionDirective.atom ∈ space)
    (extra : List Atom) :
    ExactDirectAssertionLaunch context (space ++ extra) := by
  rcases launch with ⟨substitution, rowMember, outputs⟩
  exact ⟨substitution,
    matcherRow_append space extra shell rowMember, outputs⟩

theorem canonical_exact_direct_assertion_launch_append
    (context : DirectAssertionContext) (extra : List Atom) :
    ExactDirectAssertionLaunch context
      (canonicalDirectAssertionSpace context ++ extra) :=
  ExactDirectAssertionLaunch.append context
    (canonical_exact_direct_assertion_launch context)
    (canonical_direct_assertion_shell context) extra

theorem canonicalDirectAssertionSpace_append_supported
    (context : DirectAssertionContext) (extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    cSupportedSourceExecFacts
        (canonicalDirectAssertionSpace context ++ extra) =
      directAssertionSupportInterface.rows := by
  unfold cSupportedSourceExecFacts
  rw [List.filterMap_append]
  change cSupportedSourceExecFacts (canonicalDirectAssertionSpace context) ++
      cSupportedSourceExecFacts extra = _
  rw [canonicalDirectAssertionSpace_supported, inert, List.append_nil]

private theorem selectNextScheduled_of_eq {α : Type}
    [SchedulerKey α] {left right : List α} {selected : α}
    (equal : left = right)
    (rightSelected : selectNextScheduled right = some selected) :
    selectNextScheduled left = some selected :=
  (congrArg selectNextScheduled equal).trans rightSelected

theorem canonicalDirectAssertionSpace_append_selects
    (context : DirectAssertionContext) (extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    selectNextScheduled
        (cSupportedSourceExecFacts
          (canonicalDirectAssertionSpace context ++ extra)) =
      some speculativeDirectAssertionDirective :=
  selectNextScheduled_of_eq
    (canonicalDirectAssertionSpace_append_supported context extra inert)
    directAssertionSupportInterface.selected

private theorem reflectiveStep_of_selected {space : List Atom}
    {directive : SourceExecFact}
    (selected :
      selectNextScheduled (cSupportedSourceExecFacts space) = some directive) :
    cReflectiveSourceWorkQueueStep .leaveInert space =
      some (cFireReflectiveSourceExecFact space directive) := by
  simp only [cReflectiveSourceWorkQueueStep, selected]

theorem canonicalDirectAssertionSpace_append_steps
    (context : DirectAssertionContext) (extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (canonicalDirectAssertionSpace context ++ extra) =
      some (cFireReflectiveSourceExecFact
        (canonicalDirectAssertionSpace context ++ extra)
        speculativeDirectAssertionDirective) :=
  reflectiveStep_of_selected
    (canonicalDirectAssertionSpace_append_selects context extra inert)

theorem canonicalDirectAssertionSpace_append_publishes
    (context : DirectAssertionContext) (extra : List Atom) :
    ∀ row ∈ context.launchRows,
      row ∈ cFireReflectiveSourceExecFact
        (canonicalDirectAssertionSpace context ++ extra)
        speculativeDirectAssertionDirective := by
  exact direct_assertion_fire_adds_launch_rows context
    (canonicalDirectAssertionSpace context ++ extra)
    (canonical_exact_direct_assertion_launch_append context extra)

theorem canonicalDirectAssertionSpace_append_inhabits_exact_native_target
    (context : DirectAssertionContext) (extra : List Atom)
    (inert : cSupportedSourceExecFacts extra = []) :
    (gsltOSLF (reflectiveNativeListExecGSLT .leaveInert)).satisfies
      (canonicalDirectAssertionSpace context ++ extra)
      (reflectiveNativeListExactTargetNativeType .leaveInert
        (cFireReflectiveSourceExecFact
          (canonicalDirectAssertionSpace context ++ extra)
          speculativeDirectAssertionDirective)).pred := by
  apply (satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    .leaveInert _ _).2
  exact canonicalDirectAssertionSpace_append_steps context extra inert

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchExtension
