import Mettapedia.OSLF.Framework.SortedTypedInstrumentRPOComparison
import Mettapedia.OSLF.Framework.SortedTypedInstrumentSourceControls
import Mathlib.Tactic.NormNum

/-!+# Genuine sorted source bounds, complete RPO recovery and nonfullness

A channel-to-process source frame produces an actual IPO at the complete
send value. Every native competing candidate under this source bound has a
complete source reconstruction. In contrast, the actual administrative
ask/get context reaches a source-empty sort and has no source preimage.
Its positive hereditary count separates it from source bounds. Thus the
universal comparison does not rely on an ambient fullness claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstrumentRPOControls

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative
open Mettapedia.GSLT.RelativePushout
open SortedTypedInstruments SortedTypedInstrumentControls SortedTypedInstrumentSourceControls
open scoped BigOperators

def sourceAgent (index : Nat) :
    (.origin : SourceCategory sourceSignature sourceParallel) ⟶ .interface .channel :=
  RawArrow.value (classOf (sourceName index))

def sourceRedex (index : Nat) :
    (.origin : SourceCategory sourceSignature sourceParallel) ⟶ .interface .process :=
  RawArrow.value (classOf (sourcePayload index))

def sourceLabel :
    (.interface .channel : SourceCategory sourceSignature sourceParallel) ⟶ .interface .process :=
  RawArrow.context (contextClassOf (sendContext (.zero rfl)))

theorem source_square (index : Nat) : sourceAgent index ≫ sourceLabel = sourceRedex index := by
  apply congrArg RawArrow.value
  exact congrArg classOf (complete_source_filling index (.zero rfl))

theorem genuine_heterogeneous_source_ipo (index : Nat) :
    IsIdemPushout (sourceAgent index) (sourceRedex index) sourceLabel (𝟙 _)
      ((source_square index).trans (Category.comp_id _).symm) :=
  raw_right_identity_isIPO sourceLabel (source_square index)

theorem genuine_heterogeneous_native_ipo (index : Nat) :
    IsIdemPushout
      ((inclusion sourceSignature sourceParallel).map (sourceAgent index))
      ((inclusion sourceSignature sourceParallel).map (sourceRedex index))
      ((inclusion sourceSignature sourceParallel).map sourceLabel)
      ((inclusion sourceSignature sourceParallel).map (𝟙 _))
      (by rw [← Functor.map_comp, ← Functor.map_comp, source_square, Category.comp_id]) :=
  (RPO.idemPushout_iff_mapped ((source_square index).trans (Category.comp_id _).symm)).mp
    (genuine_heterogeneous_source_ipo index)

theorem arbitrary_competing_sorted_candidate_is_fully_recovered (index : Nat)
    (candidate : Candidate
      ((inclusion sourceSignature sourceParallel).map (sourceAgent index))
      ((inclusion sourceSignature sourceParallel).map (sourceRedex index))
      ((inclusion sourceSignature sourceParallel).map sourceLabel)
      ((inclusion sourceSignature sourceParallel).map (𝟙 _))) :
    ∃ original : Candidate (sourceAgent index) (sourceRedex index) sourceLabel (𝟙 _),
      mapCandidate (inclusion sourceSignature sourceParallel) original = candidate :=
  RPO.mapped_candidate_reconstruction candidate

def observerEscape : RawContext (signature sourceSignature sourceParallel) NativeParallel
    (.original .process) (.original .absent) :=
  (probeContext (source := sourceSignature) (Parallel := sourceParallel) (.ask (.ordinary Symbol.blocked))).comp
    (probeContext (source := sourceSignature) (Parallel := sourceParallel) (.get (.ordinary Symbol.blocked) 0))

def observerEscapeArrow :
    ((inclusion sourceSignature sourceParallel).obj (.interface .process)) ⟶
      ((inclusion sourceSignature sourceParallel).obj (.interface .absent)) :=
  RawArrow.context (contextClassOf observerEscape)

theorem observer_escape_has_no_original_reading :
    readContext observerEscape =
      (none : Option (MixedContext sourceSignature sourceParallel .process .absent)) := rfl

theorem source_inclusion_is_genuinely_not_full : ¬(inclusion sourceSignature sourceParallel).Full := by
  intro full
  obtain ⟨original, read⟩ := full.map_surjective observerEscapeArrow
  cases original with
  | context original =>
    have comparison := congrArg classContextReading (RawArrow.context.inj read)
    rw [classContextReading_embedding] at comparison
    change some (normalizeContext original) = none at comparison
    cases comparison

private theorem probe_count (instrument : Probe sourceSignature sourceParallel) :
    observerCount (probe instrument) = 1 := by
  change 1 + (∑ position : Fin 0, observerCount (Fin.elim0 position)) = 1
  simp only [Fin.sum_univ_zero, Nat.add_zero]

private theorem probe_context_count (instrument : Probe sourceSignature sourceParallel) :
    contextObserverCount (probeContext instrument) = 2 := by
  unfold probeContext
  change 1 + siblingCount (.cut instrument) 1 _ + 0 = 2
  unfold siblingCount
  change 1 + (∑ other : Fin 2, _) + 0 = 2
  rw [Fin.sum_univ_two]
  norm_num [Fin.cases]
  change 1 + observerCount (probe instrument) = 2
  rw [probe_count]

theorem observer_escape_has_positive_context_support : contextObserverCount observerEscape = 4 := by
  rw [observerEscape, contextObserverCount_comp, probe_context_count, probe_context_count]

theorem complete_original_frame_is_pure_but_escape_is_not :
    arrowObserverCount ((inclusion sourceSignature sourceParallel).map sourceLabel) = 0 ∧
      arrowObserverCount observerEscapeArrow = 4 :=
  ⟨arrowObserverCount_embedding sourceLabel, observer_escape_has_positive_context_support⟩

end Mettapedia.OSLF.Framework.SortedTypedInstrumentRPOControls
