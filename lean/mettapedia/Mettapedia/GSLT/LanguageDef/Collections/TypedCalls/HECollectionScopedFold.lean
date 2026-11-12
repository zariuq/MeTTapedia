import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionFoldWorldServices
import Mettapedia.Languages.MeTTa.HE.EquationProtectedNames

/-!
# The collection fold retains unrelated live caller variables

The capture operation restores its caller frame while saving child frames in
the snapshot world. The fold's only new binding support therefore comes from
its actual selected source equation. Freshening and matcher support derive
the preservation law; it is not a premise about a completed fold.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionScopedFold

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment snapshots)

def PreservesUnrelated (live : List Atom) (before after : Frame) (left right : String) : Prop :=
  ∀ name, (∃ atom ∈ live, Spec.Match.Merge.AtomOccurs atom name) → name ∉ specBindingVars before.bindings →
    name ≠ left → name ≠ right → name ∉ specBindingVars after.bindings

theorem source (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (caller : Option Atom)
    (left right : String) (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (rows : List Result) (pairs : List Entry.Value)
    (stored : List.Forall₂ (StoredPairRel snapshots HECollectionSpaceExtension.space world) rows pairs)
    (closed : ∀ row ∈ rows, TypeSubst.typeVars row.1.erase = []) :
    let current := environment minimal nativePolicy external active primitive subtypes
    ∃ after mark,
      Stateful.MinimalRel current HECollectionSpaceExtension.space world live scope caller
        (.expression .active [.symbol "eval", HEFoldParameterCapture.query pairs (.expression .active []) left right]) before
        [(.expression mark (rows.map Prod.fst), after)] world (policy := policy) ∧
      PreservesUnrelated live before after left right := by
  let current := environment minimal nativePolicy external active primitive subtypes
  have pairsClosed := HECollectionFoldSourceLoop.pairs_closed stored closed
  have initClosed : TypeSubst.typeVars (.expression .active [] : Entry.Value).erase = [] := by
    simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]
  obtain ⟨work, after, a, b, spaceName, frontier, bindings, unified, bodyRead, differentAB, differentAS, differentBS, aFixed, bFixed⟩ :=
    HEFoldSourceFrontier.complete_frame policy live before pairs (.expression .active []) left right different
      leftFresh rightFresh pairsClosed initClosed
  obtain ⟨mark, executed⟩ := HECollectionFoldFunction.source
    (HECollectionFoldWorldServices.emitter minimal nativePolicy external active primitive subtypes world) policy after
    (HECollectionAppendSource.append_calls
      (HECollectionFoldWorldServices.append_interface minimal nativePolicy external active primitive subtypes world policy) after)
    a b spaceName .active differentAB (Or.inr rfl) differentAS differentBS aFixed bFixed rows pairs stored closed live scope
    (some (HEFoldParameterCapture.query pairs (.expression .active []) left right).erase) .active [] rfl
  have invocation : Stateful.InvocationRel current HECollectionSpaceExtension.space world live scope caller
      (HEFoldParameterCapture.query pairs (.expression .active []) left right) before
      [(.expression mark (rows.map Prod.fst), after)] world (policy := policy) := by
    refine Stateful.InvocationRel.equations (works := [work]) ?_ frontier (by simp) ?_
    · simpa only [HEFoldParameterCapture.query, Entry.Value.erase, List.map_cons, List.map_nil] using
        HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes "foldl-atom"
          [(.expression .active pairs : Entry.Value).erase, (.expression .active [] : Entry.Value).erase,
            .var left, .var right, (HECollectionFoldSourceLoop.operation .active left right).erase] (by simp)
    · simpa only [List.nil_append, List.append_nil] using
        (Stateful.InvocationEquationsRel.cons bindings unified
          (by
            rw [bodyRead]
            exact Stateful.BoundaryRel.producerFunction (by
              refine ⟨?_, Or.inr rfl⟩
              simp [HECollectionFoldFunction.function, Entry.Value.erase, Minimal.IsFunction]) executed) .nil)
  refine ⟨after, mark, ?_, ?_⟩
  · apply Stateful.MinimalRel.eval
    rw [HEFoldSourceInvocation.query_read policy before pairs (.expression .active []) left right leftFresh rightFresh pairsClosed initClosed]
    exact invocation
  · intro name visible unbound notLeft notRight
    rw [bindings]
    apply EquationProtectedNames.selected frontier (by simp) name (Or.inr (Or.inl visible)) unbound
    intro member
    simp [HEFoldParameterCapture.query, HECollectionFoldSourceLoop.operation, Entry.Value.erase,
      TypeSubst.typeVars, TypeSubst.typeVarsList, pairsClosed, notLeft, notRight] at member

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionScopedFold
