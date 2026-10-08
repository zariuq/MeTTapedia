import Mettapedia.OSLF.Framework.SortedTypedInstrumentContextSupport

/-!+# Exact source-arrow and source-apex reconstruction from zero support

Every source arrow has zero hereditary observer support. Conversely, a
zero-support native arrow between original objects has a unique complete
source preimage. Its target is an original object even when that target was
not initially supplied as a source image. Additivity also detects each factor
of a zero-support composite. No ambient fullness is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedTypedInstruments

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative

universe u v

variable {source : Mettapedia.OSLF.SortedConstructors.Signature.{u,v}}
  {Parallel : source.Srt → Prop}

theorem classObserverCount_zero_sort {sort : Srt source Parallel}
    (supplied : ValueClass (source := source) (Parallel := Parallel) sort)
    (pure : classObserverCount supplied = 0) : ∃ original : source.Srt, sort = .original original := by
  revert pure
  refine Quotient.inductionOn supplied ?_
  intro raw pure
  obtain ⟨original, term, sortRead, _⟩ := observerCount_zero_reconstruction raw pure
  exact ⟨original, sortRead⟩

theorem classContextObserverCount_zero_sort {first : source.Srt} {second : Srt source Parallel}
    (supplied : ContextClass (signature source Parallel) NativeParallel (.original first) second)
    (pure : classContextObserverCount supplied = 0) : ∃ original : source.Srt, second = .original original := by
  revert pure
  refine Quotient.inductionOn supplied ?_
  intro raw pure
  obtain ⟨original, context, sortRead, _⟩ := contextObserverCount_zero_reconstruction raw pure
  exact ⟨original, sortRead⟩

theorem arrowObserverCount_embedding {first second : SourceCategory source Parallel}
    (supplied : first ⟶ second) : arrowObserverCount ((inclusion source Parallel).map supplied) = 0 := by
  cases supplied with
  | identity => rfl
  | value supplied => exact classObserverCount_embedding supplied
  | context supplied => exact Quotient.inductionOn supplied contextObserverCount_embed

theorem arrowObserverCount_zero_preimage {first second : SourceCategory source Parallel}
    (supplied : (inclusion source Parallel).obj first ⟶ (inclusion source Parallel).obj second)
    (pure : arrowObserverCount supplied = 0) :
    ∃ before : first ⟶ second, (inclusion source Parallel).map before = supplied := by
  cases first with
  | origin =>
    cases second with
    | origin => cases supplied; exact ⟨.identity, rfl⟩
    | interface sort =>
      cases supplied with
      | value supplied =>
        obtain ⟨before, read⟩ := classObserverCount_zero_original supplied pure
        exact ⟨.value before, congrArg RawArrow.value read⟩
  | interface first =>
    cases second with
    | origin => cases supplied
    | interface second =>
      cases supplied with
      | context supplied =>
        obtain ⟨before, read⟩ := (classContextObserverCount_original_iff_source_image supplied).mp pure
        exact ⟨.context before, congrArg RawArrow.context read⟩

theorem arrowObserverCount_zero_iff_image {first second : SourceCategory source Parallel}
    (supplied : (inclusion source Parallel).obj first ⟶ (inclusion source Parallel).obj second) :
    arrowObserverCount supplied = 0 ↔
      ∃ before : first ⟶ second, (inclusion source Parallel).map before = supplied := by
  refine ⟨arrowObserverCount_zero_preimage supplied, ?_⟩
  rintro ⟨before, rfl⟩
  exact arrowObserverCount_embedding before

theorem arrowObserverCount_zero_unique_preimage {first second : SourceCategory source Parallel}
    (supplied : (inclusion source Parallel).obj first ⟶ (inclusion source Parallel).obj second)
    (pure : arrowObserverCount supplied = 0) :
    ∃! before : first ⟶ second, (inclusion source Parallel).map before = supplied := by
  obtain ⟨before, read⟩ := arrowObserverCount_zero_preimage supplied pure
  exact ⟨before, read, fun after afterRead => (inclusion source Parallel).map_injective (afterRead.trans read.symm)⟩

theorem arrowObserverCount_zero_target {first : SourceCategory source Parallel}
    {second : ContextCategory source Parallel}
    (supplied : (inclusion source Parallel).obj first ⟶ second)
    (pure : arrowObserverCount supplied = 0) :
    ∃ original : SourceCategory source Parallel, (inclusion source Parallel).obj original = second := by
  cases first with
  | origin =>
    cases supplied with
    | identity => exact ⟨.origin, rfl⟩
    | @value sort supplied =>
      obtain ⟨original, sortRead⟩ := classObserverCount_zero_sort supplied pure
      subst sort
      exact ⟨.interface original, rfl⟩
  | interface first =>
    cases supplied with
    | @context _ second supplied =>
      obtain ⟨original, sortRead⟩ := classContextObserverCount_zero_sort supplied pure
      subst second
      exact ⟨.interface original, rfl⟩

end Mettapedia.OSLF.Framework.SortedTypedInstruments
