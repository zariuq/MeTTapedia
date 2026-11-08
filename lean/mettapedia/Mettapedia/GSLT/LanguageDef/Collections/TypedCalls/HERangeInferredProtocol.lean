import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProtocol
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredSuperpose

/-! The range protocol's inferred-reader instance is assembled entirely from
the earned literal, primitive, fresh activation and per-item return laws. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredProtocol

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RetainedTypePayloads (ExternalView)

theorem undefined_head (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (names : List String) (before : Frame) (name : String)
    (member : name = "range" ∨ name = "empty") :
    HERangeArgumentQueryTransport.inferredRead
      (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world names
      before.bindings (.symbol name) Atom.undefinedType [Atom.undefinedType] := by
  let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
  let supply : TypeReadSupply.Supply :=
    ⟨invocationTypeScope names [] (.symbol name) Atom.undefinedType before.bindings, 0⟩
  refine ⟨supply, 1, fun _ present => present, ?_⟩
  rcases member with rfl | rfl
  · exact congrArg Prod.fst (HERangeTypeReadApplications.undeclared_range currentOps world 0 supply)
  · exact congrArg Prod.fst (HERangeTypeReadApplications.undeclared_empty currentOps world 0 supply)

def ports (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom) :
    HERangeSourceProtocol.Ports where
  environment := HERangeAdmissionBoundary.environment minimal
    (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world
  view := rfl
  dispatch := rfl
  undefinedHead := undefined_head world active primitive unobservedClosure
  number := HERangeInferredSuperpose.number_undefined minimal
    (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world
  addition := HERangeInferredArithmetic.addition_source minimal
    (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world
  conditional := HERangeInferredIfSource.source_activation minimal world active primitive unobservedClosure
  superpose := HERangeInferredSuperpose.source minimal
    (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredProtocol
