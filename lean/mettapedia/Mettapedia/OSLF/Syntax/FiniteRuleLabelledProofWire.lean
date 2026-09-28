import Mettapedia.OSLF.Syntax.FiniteRulePremiseEvidence
import Mathlib.Data.List.OfFn

/-!
# Exact finite-rule derivation serialization

The decoder is shared by every finite-premise presentation. Executable use
requires a computable codec for its rule-instance shapes, computable judgment
equality, and computable ordered-premise data. It checks
the supplied ordered tree and constructs the indexed derivation itself.
Its two round trips retain whole proof histories, including distinct rules
and repeated premise positions. Rejecting a tree does not refute its goal.

This module does not supply a codec for every possible shape type, a proof
search algorithm, an Agda rule-instance codec, or a native runtime adapter.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

universe u v w
variable {J : Type u} (F : FinitePresentation.{0,u,v} Unit (fun _ => J))

abbrev PackedShape := Σ j : J, F.Shape () j
abbrev Packed := Σ j : J, F.Derivation () j

/-- A partial bijection between concrete rule-instance shapes and structured
labels. Its existence and executable realization are presentation obligations. -/
structure ShapeCodec (Label : Type w) where
  encode : PackedShape F → Label
  decode : Label → Option (PackedShape F)
  roundtrip : ∀ shape, decode (encode shape) = some shape
  canonical : ∀ label shape, decode label = some shape → encode shape = label

/-- Rule-instance labels and ordered recursive children. No typing verdict is
trusted from the input tree. -/
inductive Wire (Label : Type w) where
  | node (label : Label) (children : List (Wire Label))
  deriving Repr

variable {Label : Type w} (codec : ShapeCodec F Label)

def encode {j : J} (tree : F.Derivation () j) : Wire Label :=
  match tree with
  | .roll shape children => .node (codec.encode ⟨j,shape⟩)
      (List.ofFn (fun p => encode (children p)))
termination_by structural tree

variable [DecidableEq J]

def atIndex (j : J) : Packed F → Option (F.Derivation () j)
  | ⟨k,tree⟩ => if h : k = j then some (h ▸ tree) else none

def assemble : (indices : List J) → List (Option (Packed F)) →
    Option (Evidence (F.Derivation ()) indices)
  | [], [] => some (noEvidence _)
  | j :: js, child :: children => do
      let packet ← child
      let tree ← atIndex F j packet
      let rest ← assemble js children
      return consEvidence _ tree rest
  | _, _ => none

/-- Deterministic decoding inspects the exact declared child judgments and
rejects missing, extra or mismatched children. Recursion follows the input tree. -/
def decode : Wire Label → Option (Packed F)
  | .node label children => do
      let ⟨j,shape⟩ ← codec.decode label
      let checked ← assemble F (F.premises () j shape) (children.attach.map (fun child => decode child.val))
      return ⟨j, .roll shape checked⟩
termination_by wire => sizeOf wire
decreasing_by
  have smaller := List.sizeOf_lt_of_mem child.property
  simp only [Wire.node.sizeOf_spec]
  exact Nat.lt_trans smaller (Nat.lt_add_of_pos_left
    (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_add_right 1 (sizeOf label))))

@[simp] theorem atIndex_self {j : J} (tree : F.Derivation () j) :
    atIndex F j ⟨j, tree⟩ = some tree := by
  simp only [atIndex, dite_true]

theorem assemble_ofFn (indices : List J)
    (children : Evidence (F.Derivation ()) indices) :
    assemble F indices
      (List.ofFn fun p => some ⟨indices.get p, children p⟩) = some children := by
  induction indices with
  | nil =>
      have empty : noEvidence (F.Derivation ()) = children := by
        funext p
        exact Fin.elim0 p
      simpa only [List.ofFn_zero, assemble] using congrArg some empty
  | cons j js ih =>
      rw [List.ofFn_succ]
      change assemble F (j :: js)
        (some ⟨j, children 0⟩ :: List.ofFn fun p => some ⟨js.get p, children p.succ⟩) = some children
      simp only [assemble, bind, Option.bind_some, atIndex, dite_true]
      change (assemble F js (List.ofFn fun p => some ⟨js.get p, children p.succ⟩) >>=
        fun rest => some (consEvidence (F.Derivation ()) (children 0) rest)) = some children
      rw [ih]
      exact congrArg some (consEvidence_eta (F.Derivation ()) children)

/-- Every native proof has a serialization that recovers that same proof. -/
theorem decode_encode {j : J} (tree : F.Derivation () j) :
    decode F codec (encode F codec tree) = some ⟨j, tree⟩ := by
  refine IndexedPolynomial.Fix.rec
    (motive := fun j tree => decode F codec (encode F codec tree) = some ⟨j, tree⟩)
    ?_ tree
  intro j shape children ih
  change F.Shape () j at shape
  change Evidence (F.Derivation ()) (F.premises () j shape) at children
  change ∀ p, decode F codec (encode F codec (children p)) =
    some ⟨(F.premises () j shape).get p, children p⟩ at ih
  have children_eq :
      (List.ofFn fun p => encode F codec (children p)).attach.map
          (fun child => decode F codec child.val) =
        List.ofFn (fun p => some ⟨(F.premises () j shape).get p, children p⟩) := by
    rw [List.attach_map_val, List.map_ofFn]
    congr 1
    funext p
    exact ih p
  change decode F codec (.node (codec.encode ⟨j,shape⟩)
      (List.ofFn fun p => encode F codec (children p))) =
    some ⟨j, IndexedPolynomial.Fix.roll shape children⟩
  rw [decode, codec.roundtrip]
  change (assemble F (F.premises () j shape)
      ((List.ofFn fun p => encode F codec (children p)).attach.map
        (fun child => decode F codec child.val))).bind
      (fun checked => some (⟨j, .roll shape checked⟩ : Packed F)) =
      some (⟨j, .roll shape children⟩ : Packed F)
  rw [children_eq, assemble_ofFn]
  rfl

def encodePacked (tree : Packed F) : Wire Label := encode F codec tree.2

@[simp] theorem decode_encodePacked (tree : Packed F) :
    decode F codec (encodePacked F codec tree) = some tree := by
  cases tree with
  | mk j tree => exact decode_encode F codec tree

theorem encodePacked_injective : Function.Injective (encodePacked F codec) := by
  intro first second equal
  have decoded := congrArg (decode F codec) equal
  rw [decode_encodePacked, decode_encodePacked] at decoded
  exact Option.some.inj decoded

theorem atIndex_eq_some {j : J} {packet : Packed F} {tree : F.Derivation () j}
    (accepted : atIndex F j packet = some tree) : packet = ⟨j, tree⟩ := by
  rcases packet with ⟨k, prior⟩
  by_cases equal : k = j
  · subst k
    simp only [atIndex_self, Option.some.injEq] at accepted
    cases accepted
    rfl
  · simp only [atIndex, dif_neg equal] at accepted
    cases accepted

theorem assemble_eq_some (indices : List J) (packets : List (Option (Packed F)))
    (children : Evidence (F.Derivation ()) indices)
    (accepted : assemble F indices packets = some children) :
    packets = List.ofFn fun p => some ⟨indices.get p, children p⟩ := by
  induction indices generalizing packets with
  | nil =>
      cases packets with
      | nil => rfl
      | cons head tail => cases accepted
  | cons j js ih =>
      cases packets with
      | nil => cases accepted
      | cons head tail =>
          cases head with
          | none => cases accepted
          | some packet =>
              cases first : atIndex F j packet with
              | none => simp only [assemble, bind, Option.bind_some, first, Option.bind_none] at accepted; cases accepted
              | some firstTree =>
                  cases rest : assemble F js tail with
                  | none => simp only [assemble, bind, Option.bind_some, first, rest, Option.bind_none] at accepted; cases accepted
                  | some restTrees =>
                      have packed := atIndex_eq_some F first
                      have tail_eq := ih tail restTrees rest
                      have all_eq : consEvidence (F.Derivation ()) firstTree restTrees = children := by
                        simpa only [assemble, bind, Option.bind_some, first, rest, pure, Option.some.injEq] using accepted
                      cases packed
                      cases all_eq
                      rw [List.ofFn_succ, tail_eq]
                      rfl

theorem list_decode_inverse (wires : List (Wire Label)) (packets : List (Packed F))
    (matched : wires.map (decode F codec) = packets.map some)
    (inverse : ∀ wire ∈ wires, ∀ packet, decode F codec wire = some packet →
      encodePacked F codec packet = wire) :
    packets.map (encodePacked F codec) = wires := by
  induction wires generalizing packets with
  | nil =>
      cases packets with
      | nil => rfl
      | cons head tail => cases matched
  | cons wire wires ih =>
      cases packets with
      | nil => cases matched
      | cons packet packets =>
          have parts := List.cons.inj matched
          change encodePacked F codec packet :: packets.map (encodePacked F codec) = wire :: wires
          rw [inverse wire (List.mem_cons_self ..) packet parts.1]
          congr 1
          exact ih packets parts.2 (fun child member => inverse child (List.mem_cons_of_mem wire member))

/-- Every accepted tree is the exact serialization of the proof constructed
by the decoder. No unobserved children or alternative shape codes survive. -/
theorem encode_decode (wire : Wire Label) (packet : Packed F)
    (accepted : decode F codec wire = some packet) :
    encodePacked F codec packet = wire := by
  cases wire with
  | node label wires =>
      cases label_eq : codec.decode label with
      | none =>
          simp only [decode, label_eq, bind, Option.bind_none] at accepted
          cases accepted
      | some shapePacket =>
          rcases shapePacket with ⟨j, shape⟩
          cases children_eq : assemble F (F.premises () j shape)
              (wires.attach.map fun child => decode F codec child.val) with
          | none =>
              simp only [decode, label_eq, bind, Option.bind_some, children_eq, Option.bind_none] at accepted
              cases accepted
          | some children =>
              have packet_eq : (⟨j, .roll shape children⟩ : Packed F) = packet := by
                simpa only [decode, label_eq, bind, Option.bind_some, children_eq, pure, Option.some.injEq] using accepted
              cases packet_eq
              have packed_eq := assemble_eq_some F _ _ children children_eq
              rw [List.attach_map_val] at packed_eq
              have mapped : (List.ofFn (fun p =>
                  (⟨(F.premises () j shape).get p, children p⟩ : Packed F))).map
                  (encodePacked F codec) = wires := by
                apply list_decode_inverse F codec
                · simpa only [List.map_ofFn, Function.comp_def] using packed_eq
                · intro child member result result_eq
                  exact encode_decode child result result_eq
              change Wire.node (codec.encode ⟨j,shape⟩)
                (List.ofFn fun p => encode F codec (children p)) = Wire.node label wires
              rw [codec.canonical label ⟨j,shape⟩ label_eq]
              congr 1
              simpa only [List.map_ofFn, Function.comp_def, encodePacked] using mapped
termination_by sizeOf wire
decreasing_by
  subst wire
  have smaller := List.sizeOf_lt_of_mem member
  simp only [Wire.node.sizeOf_spec]
  exact Nat.lt_trans smaller (Nat.lt_add_of_pos_left
    (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_add_right 1 (sizeOf label))))

def decodeAt (j : J) (wire : Wire Label) : Option (F.Derivation () j) :=
  (decode F codec wire).bind (atIndex F j)

theorem decodeAt_encode {j : J} (tree : F.Derivation () j) :
    decodeAt F codec j (encode F codec tree) = some tree := by
  rw [decodeAt, decode_encode]
  exact atIndex_self F tree

theorem decodeAt_exact {j : J} {wire : Wire Label} {tree : F.Derivation () j}
    (accepted : decodeAt F codec j wire = some tree) :
    encode F codec tree = wire := by
  cases decoded : decode F codec wire with
  | none => simp only [decodeAt, decoded, Option.bind_none] at accepted; cases accepted
  | some packet =>
      have index_eq : atIndex F j packet = some tree := by
        simpa only [decodeAt, decoded, Option.bind_some] using accepted
      have packet_eq := atIndex_eq_some F index_eq
      cases packet_eq
      exact encode_decode F codec wire ⟨j,tree⟩ decoded

theorem decodeAt_iff {j : J} {wire : Wire Label} {tree : F.Derivation () j} :
    decodeAt F codec j wire = some tree ↔ encode F codec tree = wire := by
  constructor
  · exact decodeAt_exact F codec
  · intro encoded
    rw [← encoded]
    exact decodeAt_encode F codec tree

/-- Finite proof-object checking; this does not decide theoremhood. -/
def check (j : J) (wire : Wire Label) : Bool := (decodeAt F codec j wire).isSome

theorem check_iff (j : J) (wire : Wire Label) :
    check F codec j wire = true ↔
      ∃ tree : F.Derivation () j, encode F codec tree = wire := by
  simp only [check, Option.isSome_iff_exists, decodeAt_iff]

def acceptedEquiv : Packed F ≃ { wire : Wire Label // (decode F codec wire).isSome } where
  toFun packet := ⟨encodePacked F codec packet, by rw [decode_encodePacked]; rfl⟩
  invFun wire := (decode F codec wire.val).get wire.property
  left_inv packet := by simp only [decode_encodePacked, Option.get_some]
  right_inv wire := by
    apply Subtype.ext
    exact encode_decode F codec wire.val _ (Option.some_get wire.property).symm


end Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire
