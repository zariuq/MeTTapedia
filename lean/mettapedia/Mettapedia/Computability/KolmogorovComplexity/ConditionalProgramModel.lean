import Mathlib.Computability.PartrecCode
import Mathlib.Data.List.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.OrderIsoNat

/-!
# Conditional programs and exact natural-word interpreter adapters

The source-program interface depends only on Mathlib. An exact word codec and
a computable program decoder induce a genuine partial interpreter. Its output
relation and compiler-prefix universality are proved from natural-code
execution. Different program formats need not have identical decoders.
-/

set_option autoImplicit false

namespace KolmogorovComplexity

open scoped Classical

/-- A partial algorithm with a program and an auxiliary condition. -/
abbrev ConditionalAlgorithm := List Bool → List Bool →. List Bool

/-- The compiler prefix depends on the simulated partial-recursive algorithm,
not on its program, condition or output. -/
def IsUniversalConditional (U : ConditionalAlgorithm) : Prop :=
  ∀ V : ConditionalAlgorithm, Partrec₂ V →
    ∃ compilerPrefix : List Bool, ∀ p condition x,
      x ∈ V p condition → x ∈ U (compilerPrefix ++ p) condition

/-- Program lengths producing an output under an auxiliary condition. -/
def conditionalPlainLengthsFor (U : ConditionalAlgorithm) (condition x : List Bool) : Set Nat :=
  {n | ∃ p : List Bool, x ∈ U p condition ∧ p.length = n}

/-- The empty represented-output set has infimum zero. Shortest-program
results must retain their separate representability premise. -/
noncomputable def plainConditionalComplexity (U : ConditionalAlgorithm) (x condition : List Bool) : Nat :=
  sInf (conditionalPlainLengthsFor U condition x)

/-- All naturals decode and every word, including its leading zero bits,
round-trips. The two directions are separately required. -/
structure NaturalWordCodec where
  encode : List Bool → Nat
  decode : Nat → List Bool
  decode_encode : ∀ word, decode (encode word) = word
  encode_decode : ∀ value, encode (decode value) = value
  encode_computable : Computable encode
  decode_computable : Computable decode

namespace NaturalWordCodec

def packCondition (codec : NaturalWordCodec) (condition payload : List Bool) : List Bool :=
  codec.decode (Nat.pair (codec.encode condition) (codec.encode payload))

def unpackCondition (codec : NaturalWordCodec) (word : List Bool) : List Bool × List Bool :=
  (codec.decode (codec.encode word).unpair.1, codec.decode (codec.encode word).unpair.2)

theorem unpack_packCondition (codec : NaturalWordCodec) (condition payload : List Bool) :
    codec.unpackCondition (codec.packCondition condition payload) = (condition, payload) := by
  simp only [unpackCondition, packCondition, codec.encode_decode, Nat.unpair_pair, codec.decode_encode]

theorem pack_unpackCondition (codec : NaturalWordCodec) (word : List Bool) :
    codec.packCondition (codec.unpackCondition word).1 (codec.unpackCondition word).2 = word := by
  simp only [packCondition, unpackCondition, codec.encode_decode, Nat.pair_unpair, codec.decode_encode]

theorem packCondition_computable (codec : NaturalWordCodec) : Computable₂ codec.packCondition :=
  codec.decode_computable.comp
    (Primrec₂.natPair.to_comp.comp (codec.encode_computable.comp Computable.fst)
      (codec.encode_computable.comp Computable.snd))

theorem unpackCondition_computable (codec : NaturalWordCodec) : Computable codec.unpackCondition :=
  (codec.decode_computable.comp (Computable.fst.comp (Computable.unpair.comp codec.encode_computable))).pair
    (codec.decode_computable.comp (Computable.snd.comp (Computable.unpair.comp codec.encode_computable)))

theorem encode_injective (codec : NaturalWordCodec) : Function.Injective codec.encode := by
  intro first second same
  simpa only [codec.decode_encode] using congrArg codec.decode same

theorem decode_injective (codec : NaturalWordCodec) : Function.Injective codec.decode := by
  intro first second same
  simpa only [codec.encode_decode] using congrArg codec.encode same

def interpreter (codec : NaturalWordCodec) (decodeProgram : List Bool → Nat.Partrec.Code) : ConditionalAlgorithm :=
  fun program condition => (Nat.Partrec.Code.eval (decodeProgram program) (codec.encode condition)).map codec.decode

/-- The independently specified natural execution relation and the shared
partial interpreter agree on every program, input and output word. -/
theorem interpreter_output_iff (codec : NaturalWordCodec) (decodeProgram : List Bool → Nat.Partrec.Code)
    (program condition output : List Bool) :
    output ∈ codec.interpreter decodeProgram program condition ↔
      Nat.Partrec.Code.eval (decodeProgram program) (codec.encode condition) = Part.some (codec.encode output) := by
  constructor
  · intro observed
    change output ∈ (Nat.Partrec.Code.eval (decodeProgram program) (codec.encode condition)).map codec.decode at observed
    obtain ⟨value, computes, same⟩ := (Part.mem_map_iff codec.decode).mp observed
    have encoded : value = codec.encode output := by
      rw [← same, codec.encode_decode]
    exact Part.eq_some_iff.mpr (encoded ▸ computes)
  · intro computes
    have observed : codec.encode output ∈
        Nat.Partrec.Code.eval (decodeProgram program) (codec.encode condition) :=
      Part.eq_some_iff.mp computes
    simpa only [interpreter, codec.decode_encode] using Part.mem_map codec.decode observed

theorem interpreter_partrec (codec : NaturalWordCodec) {decodeProgram : List Bool → Nat.Partrec.Code}
    (effective : Computable decodeProgram) : Partrec₂ (codec.interpreter decodeProgram) := by
  have evaluation : Partrec fun input : List Bool × List Bool =>
      Nat.Partrec.Code.eval (decodeProgram input.1) (codec.encode input.2) :=
    Nat.Partrec.Code.eval_part.comp (effective.comp Computable.fst)
      (codec.encode_computable.comp Computable.snd)
  exact (evaluation.map (codec.decode_computable.comp Computable.snd).to₂).to₂

def naturalRunner (codec : NaturalWordCodec) (V : ConditionalAlgorithm) : Nat →. Nat :=
  fun input => (V (codec.decode input.unpair.2) (codec.decode input.unpair.1)).map codec.encode

theorem naturalRunner_partrec (codec : NaturalWordCodec) {V : ConditionalAlgorithm}
    (effective : Partrec₂ V) : Partrec (codec.naturalRunner V) := by
  have runner := effective.comp
    (codec.decode_computable.comp (Computable.snd.comp Computable.unpair))
    (codec.decode_computable.comp (Computable.fst.comp Computable.unpair))
  exact runner.map (codec.encode_computable.comp Computable.snd).to₂

/-- A real layout equation for compiler-generated programs suffices to
derive universality. The layout is an actual word prefix, so its complete
length is the uniform overhead. No correspondence is assumed for other
programs or for a different interpreter's minimum descriptions. -/
theorem interpreter_isUniversal (codec : NaturalWordCodec) (decodeProgram : List Bool → Nat.Partrec.Code)
    (compilerLayout : Nat.Partrec.Code → List Bool)
    (layout : ∀ code payload condition,
      Nat.Partrec.Code.eval (decodeProgram (compilerLayout code ++ payload)) (codec.encode condition) =
        Nat.Partrec.Code.eval code (Nat.pair (codec.encode condition) (codec.encode payload))) :
    IsUniversalConditional (codec.interpreter decodeProgram) := by
  intro V effective
  obtain ⟨code, represents⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.mp (codec.naturalRunner_partrec effective))
  refine ⟨compilerLayout code, fun payload condition output observed => ?_⟩
  have encoded : codec.encode output ∈ codec.naturalRunner V
      (Nat.pair (codec.encode condition) (codec.encode payload)) := by
    simpa only [naturalRunner, Nat.unpair_pair, codec.decode_encode] using
      Part.mem_map codec.encode observed
  have computes : codec.encode output ∈
      Nat.Partrec.Code.eval (decodeProgram (compilerLayout code ++ payload)) (codec.encode condition) := by
    rw [layout, represents]
    exact encoded
  simpa only [interpreter, codec.decode_encode] using Part.mem_map codec.decode computes

#print axioms interpreter_output_iff
#print axioms interpreter_partrec
#print axioms naturalRunner_partrec
#print axioms interpreter_isUniversal

end NaturalWordCodec

end KolmogorovComplexity
