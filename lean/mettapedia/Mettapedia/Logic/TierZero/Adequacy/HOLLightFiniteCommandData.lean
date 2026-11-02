import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandWitnesses

/-!
# Finite data envelopes for the existing registered commands

The tagged fields are exactly the original command constructor arguments;
decoding constructs that original Command directly. The finite certificate
graph replaces only its function-valued provider. The original checker is
the sole local admission operation, not a new proof interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandData

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.ProofExecution
open Mettapedia.Languages.HOLLight.ProofExecution.Registered
open HOLLightFiniteWitnesses HOLLightFiniteCommandWitnesses

def typeRequestCodec : Codec TypeOperatorDefinitionRequest :=
  (Codec.prod nameCodec (Codec.prod nameCodec (Codec.prod nameCodec
    (Codec.prod (Codec.list nameCodec) (Codec.prod sourceTermCodec theoremCodec))))).mapped
    (fun request => (request.typeName, request.abstractionName, request.representationName,
      request.typeVariables, request.predicateSource, request.existence))
    (fun fields => some ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
      fields.2.2.2.2.1, fields.2.2.2.2.2⟩) (fun _ => rfl)

def shape : Command → Data
  | .proof node _ => .pair (.atom 0) (ProofDataEncoding.receiptCodec.put node)
  | .constant origin name body _ => .pair (.atom 1)
      (.pair (ProofDataEncoding.originCodec.put origin) (.pair (nameCodec.put name) (sourceTermCodec.put body)))
  | .typeDefinition origin request index _ => .pair (.atom 2)
      (.pair (ProofDataEncoding.originCodec.put origin) (.pair (typeRequestCodec.put request) (.atom index)))

def decodeShape (certificates : SignatureFormation.InstanceWitnesses) : Data → Option Command
  | .pair (.atom 0) node => do return .proof (← ProofDataEncoding.receiptCodec.get node) certificates
  | .pair (.atom 1) (.pair origin (.pair name body)) => do
      return .constant (← ProofDataEncoding.originCodec.get origin) (← nameCodec.get name)
        (← sourceTermCodec.get body) certificates
  | .pair (.atom 2) (.pair origin (.pair request (.atom index))) => do
      return .typeDefinition (← ProofDataEncoding.originCodec.get origin) (← typeRequestCodec.get request) index certificates
  | _ => none

theorem decodeShape_shape (command : Command) (certificates : SignatureFormation.InstanceWitnesses) :
    decodeShape certificates (shape command) = some (withWitnesses command certificates) := by
  cases command <;> simp [shape, decodeShape, withWitnesses, ProofDataEncoding.receiptCodec.get_put,
    ProofDataEncoding.originCodec.get_put, nameCodec.get_put, sourceTermCodec.get_put, typeRequestCodec.get_put]

def encode (command : Command) (graph : Graph) : Data := .pair (shape command) (graphCodec.put graph)

def decode : Data → Option Command
  | .pair source graph => do
      let certificates ← graphCodec.get graph
      decodeShape (witnesses certificates) source
  | _ => none

theorem decode_encode (command : Command) (graph : Graph) :
    decode (encode command graph) = some (withWitnesses command (witnesses graph)) := by
  simp [decode, encode, graphCodec.get_put, decodeShape_shape]

theorem decoded_origin (command : Command) (graph : Graph) :
    (decode (encode command graph)).map Command.origin = some command.origin := by
  rw [decode_encode]
  exact congrArg some (origin_preserved command _)

theorem decoded_parents (command : Command) (graph : Graph) :
    (decode (encode command graph)).map Command.parents = some command.parents := by
  rw [decode_encode]
  exact congrArg some (parents_preserved command _)

/-- Every accepted original finite source command is representable by one
finite data envelope with exactly the same local admission output. -/
theorem every_accepted_command_representable (policy : AxiomPolicy) [DecidablePred policy]
    (context : TheoryContext) (cache : Array Theorem) (command : Command) {output : Output}
    (accepted : command.check policy context cache = some output) :
    (decode (encode command (sampleCommand command output))).bind
      (fun decoded => decoded.check policy context cache) = some output := by
  rw [decode_encode]
  exact accepted_finite_observation policy context cache command accepted

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteCommandData
