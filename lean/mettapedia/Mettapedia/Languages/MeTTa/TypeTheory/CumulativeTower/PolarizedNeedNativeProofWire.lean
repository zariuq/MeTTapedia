import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeWireData
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawInferenceService
import Mettapedia.Languages.Megalodon.NIKNativeProof

/-!
# Raw native proof requests in the existing wire carrier

These codecs retain every constructor of the actual Mathdata types, terms
and proof objects, including constructors outside the Henkin soundness
fragment. Decoding is not formation or proof admission. The environment is
selected by the service, never supplied as an untrusted axiom table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace PolarizedNeedNativeProofWire

open Mettapedia.Languages.Megalodon MathdataKernel

abbrev Wire := NativeWireData.Wire
abbrev Scope := RawInferenceService.Scope

def encodeTp : Tp → Wire
  | .var i => .application "Tp.var" [.natural i]
  | .prop => .application "Tp.prop" []
  | .base i => .application "Tp.base" [.natural i]
  | .arr a b => .application "Tp.arr" [encodeTp a, encodeTp b]
  | .all a => .application "Tp.all" [encodeTp a]

def decodeTp : Wire → Option Tp
  | .application "Tp.var" [.natural i] => some (.var i)
  | .application "Tp.prop" [] => some .prop
  | .application "Tp.base" [.natural i] => some (.base i)
  | .application "Tp.arr" [a, b] => return .arr (← decodeTp a) (← decodeTp b)
  | .application "Tp.all" [a] => return .all (← decodeTp a)
  | _ => none

@[simp] theorem decodeTp_encode (type : Tp) : decodeTp (encodeTp type) = some type := by
  induction type <;> simp_all [encodeTp, decodeTp]

def encodeTm : Tm → Wire
  | .db i => .application "Tm.db" [.natural i]
  | .named name => .application "Tm.named" [.string name]
  | .prim i => .application "Tm.prim" [.natural i]
  | .app f a => .application "Tm.app" [encodeTm f, encodeTm a]
  | .lam a body => .application "Tm.lam" [encodeTp a, encodeTm body]
  | .imp a b => .application "Tm.imp" [encodeTm a, encodeTm b]
  | .all a body => .application "Tm.all" [encodeTp a, encodeTm body]
  | .typeApp f a => .application "Tm.typeApp" [encodeTm f, encodeTp a]
  | .typeLam body => .application "Tm.typeLam" [encodeTm body]
  | .typeAll body => .application "Tm.typeAll" [encodeTm body]

def decodeTm : Wire → Option Tm
  | .application "Tm.db" [.natural i] => some (.db i)
  | .application "Tm.named" [.string name] => some (.named name)
  | .application "Tm.prim" [.natural i] => some (.prim i)
  | .application "Tm.app" [f, a] => return .app (← decodeTm f) (← decodeTm a)
  | .application "Tm.lam" [a, body] => return .lam (← decodeTp a) (← decodeTm body)
  | .application "Tm.imp" [a, b] => return .imp (← decodeTm a) (← decodeTm b)
  | .application "Tm.all" [a, body] => return .all (← decodeTp a) (← decodeTm body)
  | .application "Tm.typeApp" [f, a] => return .typeApp (← decodeTm f) (← decodeTp a)
  | .application "Tm.typeLam" [body] => return .typeLam (← decodeTm body)
  | .application "Tm.typeAll" [body] => return .typeAll (← decodeTm body)
  | _ => none

@[simp] theorem decodeTm_encode (term : Tm) : decodeTm (encodeTm term) = some term := by
  induction term <;> simp_all [encodeTm, decodeTm]

def encodePf : Pf → Wire
  | .gpa name => .application "Pf.gpa" [.string name]
  | .hyp i => .application "Pf.hyp" [.natural i]
  | .known name => .application "Pf.known" [.string name]
  | .termApp f a => .application "Pf.termApp" [encodePf f, encodeTm a]
  | .proofApp f a => .application "Pf.proofApp" [encodePf f, encodePf a]
  | .proofLam p body => .application "Pf.proofLam" [encodeTm p, encodePf body]
  | .termLam a body => .application "Pf.termLam" [encodeTp a, encodePf body]
  | .typeApp f a => .application "Pf.typeApp" [encodePf f, encodeTp a]
  | .typeLam body => .application "Pf.typeLam" [encodePf body]

def decodePf : Wire → Option Pf
  | .application "Pf.gpa" [.string name] => some (.gpa name)
  | .application "Pf.hyp" [.natural i] => some (.hyp i)
  | .application "Pf.known" [.string name] => some (.known name)
  | .application "Pf.termApp" [f, a] => return .termApp (← decodePf f) (← decodeTm a)
  | .application "Pf.proofApp" [f, a] => return .proofApp (← decodePf f) (← decodePf a)
  | .application "Pf.proofLam" [p, body] => return .proofLam (← decodeTm p) (← decodePf body)
  | .application "Pf.termLam" [a, body] => return .termLam (← decodeTp a) (← decodePf body)
  | .application "Pf.typeApp" [f, a] => return .typeApp (← decodePf f) (← decodeTp a)
  | .application "Pf.typeLam" [body] => return .typeLam (← decodePf body)
  | _ => none

@[simp] theorem decodePf_encode (proof : Pf) : decodePf (encodePf proof) = some proof := by
  induction proof <;> simp_all [encodePf, decodePf]

theorem encodePf_injective : Function.Injective encodePf := by
  intro first second same
  simpa only [decodePf_encode, Option.some.injEq] using congrArg decodePf same

def decodeList {α : Type} (decode : Wire → Option α) : List Wire → Option (List α)
  | [] => some []
  | first :: rest => return (← decode first) :: (← decodeList decode rest)

theorem decodeList_map {α : Type} (encode : α → Wire) (decode : Wire → Option α)
    (roundTrip : ∀ value, decode (encode value) = some value) (values : List α) :
    decodeList decode (values.map encode) = some values := by
  induction values <;> simp_all [decodeList]

/-- Every native judgment coordinate except the service's fixed environment. -/
structure Request where
  scope : Scope
  fuel : Nat
  typeDepth : Nat
  termContext : List Tp
  proofContext : List Tm
  proposition : Tm
  deriving DecidableEq, Repr

def Request.claim (request : Request) (environment : Environment) : NIKNativeProof.Claim :=
  ⟨environment, request.fuel, request.typeDepth, request.termContext,
    request.proofContext, request.proposition⟩

def encodeRequest (request : Request) : Wire :=
  .application "NativeProof.request" [.natural request.scope.authority, .natural request.scope.revision,
    .natural request.fuel, .natural request.typeDepth,
    .application "types" (request.termContext.map encodeTp),
    .application "hypotheses" (request.proofContext.map encodeTm), encodeTm request.proposition]

def decodeRequest : Wire → Option Request
  | .application "NativeProof.request" [.natural authority, .natural revision,
      .natural fuel, .natural depth, .application "types" types,
      .application "hypotheses" hypotheses, proposition] => do
      return ⟨⟨authority, revision⟩, fuel, depth, ← decodeList decodeTp types,
        ← decodeList decodeTm hypotheses, ← decodeTm proposition⟩
  | _ => none

@[simp] theorem decodeRequest_encode (request : Request) :
    decodeRequest (encodeRequest request) = some request := by
  cases request
  simp only [encodeRequest, decodeRequest, decodeList_map encodeTp decodeTp decodeTp_encode,
    decodeList_map encodeTm decodeTm decodeTm_encode, decodeTm_encode]
  rfl

structure Packet where
  request : Request
  proof : Pf
  deriving DecidableEq, Repr

def encodePacket (packet : Packet) : Wire :=
  .application "NativeProof.packet" [encodeRequest packet.request, encodePf packet.proof]

def decodePacket : Wire → Option Packet
  | .application "NativeProof.packet" [request, proof] =>
      return ⟨← decodeRequest request, ← decodePf proof⟩
  | _ => none

@[simp] theorem decodePacket_encode (packet : Packet) :
    decodePacket (encodePacket packet) = some packet := by
  cases packet
  simp [decodePacket, encodePacket]

theorem encodePacket_injective : Function.Injective encodePacket := by
  intro first second same
  simpa only [decodePacket_encode, Option.some.injEq] using congrArg decodePacket same

theorem malformed_proof_rejected : decodePf (.application "Pf.proofApp" [.natural 0]) = none := rfl

/-- Successful serialization includes raw constructors not admitted by the
ordinary native checker. Codec coverage cannot serve as proof soundness. -/
theorem raw_gpa_retained (name : String) : decodePf (encodePf (.gpa name)) = some (.gpa name) :=
  decodePf_encode _

#print axioms decodeTp_encode
#print axioms decodeTm_encode
#print axioms decodePf_encode
#print axioms encodePf_injective
#print axioms decodeRequest_encode
#print axioms decodePacket_encode
#print axioms encodePacket_injective
#print axioms malformed_proof_rejected
#print axioms raw_gpa_retained

end PolarizedNeedNativeProofWire
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
