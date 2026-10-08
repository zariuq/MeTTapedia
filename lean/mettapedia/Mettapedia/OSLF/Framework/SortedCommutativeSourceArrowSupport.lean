import Mettapedia.OSLF.Syntax.SortedCommutativeSourceSupport

/-!
# Pure arrow and apex reconstruction for the source inclusion

Every source arrow has hereditary support zero. Conversely, a zero-support
arrow between source images has an actual source preimage, unique by the
independently earned faithfulness. A zero-support arrow out of a source
object also forces its target to be a source object. These are local image
theorems, rather than a false fullness claim about the observer extension.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedCommutative

universe u

variable {Symbols : Type u} {arity : Symbols → Nat}

theorem arrowObserverCount_embedding {source target : Source.SourceCategory (arity := arity)}
    (supplied : source ⟶ target) : arrowObserverCount (Source.inclusion.map supplied) = 0 := by
  cases supplied with
  | identity => rfl
  | value supplied =>
    exact Quotient.inductionOn supplied observerCount_embed
  | context supplied =>
    exact Quotient.inductionOn supplied contextObserverCount_embed

theorem arrowObserverCount_zero_preimage {source target : Source.SourceCategory (arity := arity)}
    (supplied : Source.inclusion.obj source ⟶ Source.inclusion.obj target)
    (pure : arrowObserverCount supplied = 0) :
    ∃ before : source ⟶ target, Source.inclusion.map before = supplied := by
  cases source with
  | origin =>
    cases target with
    | origin =>
      cases supplied
      exact ⟨.identity, rfl⟩
    | interface sort =>
      cases sort with
      | up sort =>
        cases sort
        cases supplied with
        | value supplied =>
          exact ⟨.value (Source.classRetraction supplied),
            congrArg RawArrow.value (classObserverCount_zero_readback supplied pure)⟩
  | interface source =>
    cases target with
    | origin => cases supplied
    | interface target =>
      cases source with
      | up source =>
        cases source
        cases target with
        | up target =>
          cases target
          cases supplied with
          | context supplied =>
            exact ⟨.context (Source.contextRetraction supplied),
              congrArg RawArrow.context (classContextObserverCount_zero_readback supplied pure)⟩

theorem arrowObserverCount_zero_iff_image {source target : Source.SourceCategory (arity := arity)}
    (supplied : Source.inclusion.obj source ⟶ Source.inclusion.obj target) :
    arrowObserverCount supplied = 0 ↔
      ∃ before : source ⟶ target, Source.inclusion.map before = supplied := by
  refine ⟨arrowObserverCount_zero_preimage supplied, ?_⟩
  rintro ⟨before, rfl⟩
  exact arrowObserverCount_embedding before

theorem arrowObserverCount_zero_unique_preimage {source target : Source.SourceCategory (arity := arity)}
    (supplied : Source.inclusion.obj source ⟶ Source.inclusion.obj target)
    (pure : arrowObserverCount supplied = 0) :
    ∃! before : source ⟶ target, Source.inclusion.map before = supplied := by
  obtain ⟨before, same⟩ := arrowObserverCount_zero_preimage supplied pure
  exact ⟨before, same, fun after reading => Source.inclusion.map_injective (reading.trans same.symm)⟩

theorem arrowObserverCount_zero_target {source : Source.SourceCategory (arity := arity)}
    {target : ContextCategory arity} (supplied : Source.inclusion.obj source ⟶ target)
    (pure : arrowObserverCount supplied = 0) :
    ∃ before : Source.SourceCategory (arity := arity), Source.inclusion.obj before = target := by
  cases source with
  | origin =>
    cases supplied with
    | identity => exact ⟨.origin, rfl⟩
    | @value sort supplied =>
      have sortRead : sort = .base := classObserverCount_zero_sort supplied pure
      subst sort
      exact ⟨.interface (ULift.up ()), rfl⟩
  | interface sort =>
    cases sort with
    | up sort =>
      cases sort
      cases supplied with
      | @context _ target supplied =>
        have sortRead : target = .base := classContextObserverCount_zero_sort supplied pure
        subst target
        exact ⟨.interface (ULift.up ()), rfl⟩

theorem composite_zero_support {source middle target : ContextCategory arity}
    (before : source ⟶ middle) (after : middle ⟶ target)
    (pure : arrowObserverCount (before ≫ after) = 0) :
    arrowObserverCount before = 0 ∧ arrowObserverCount after = 0 := by
  rw [arrowCount_comp] at pure
  exact Nat.add_eq_zero_iff.mp pure

end Mettapedia.OSLF.Framework.SortedCommutativeInstruments.Support
