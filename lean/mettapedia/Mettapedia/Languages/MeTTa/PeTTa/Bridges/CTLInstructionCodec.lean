import Mettapedia.Logic.BDD.CTLProgram
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# Codec for the CTL workload's topological instruction atoms

The codec uses the existing PeTTa Atom carrier and the `do-ap`, `do-tt`,
`do-not`, `do-and`, `do-or`, `do-ex`, `do-eu` and `do-eg` call shapes found in
the generated workload. Successful decoding is exact syntax, and decoded
programs feed the separately certified shared symbolic evaluator.

This is deliberately not an operational PeTTa admission theorem: the names
are authored functions whose actual bodies, mutations, return counts and
round counts must also be qualified before replacing their execution.
Unknown forms are refused, never skipped or interpreted as false.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLInstructionCodec

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.BDDCore CTLProgram StatePredicates StateTransducer
open Mettapedia.Logic.CTLFormula

def encode (instruction : Instruction String) : Atom :=
  let destination := Atom.symbol instruction.destination
  match instruction.node with
  | .atom label => .expression [.symbol "do-ap", destination, .symbol label]
  | .truth => .expression [.symbol "do-tt", destination]
  | .neg body => .expression [.symbol "do-not", destination, .symbol body]
  | .conj left right => .expression [.symbol "do-and", destination, .symbol left, .symbol right]
  | .disj left right => .expression [.symbol "do-or", destination, .symbol left, .symbol right]
  | .ex body => .expression [.symbol "do-ex", destination, .symbol body]
  | .eu holds goal => .expression [.symbol "do-eu", destination, .symbol holds, .symbol goal]
  | .eg body => .expression [.symbol "do-eg", destination, .symbol body]

def decode : Atom → Option (Instruction String)
  | .expression [.symbol "do-ap", .symbol destination, .symbol label] => some ⟨destination, .atom label⟩
  | .expression [.symbol "do-tt", .symbol destination] => some ⟨destination, .truth⟩
  | .expression [.symbol "do-not", .symbol destination, .symbol body] => some ⟨destination, .neg body⟩
  | .expression [.symbol "do-and", .symbol destination, .symbol left, .symbol right] => some ⟨destination, .conj left right⟩
  | .expression [.symbol "do-or", .symbol destination, .symbol left, .symbol right] => some ⟨destination, .disj left right⟩
  | .expression [.symbol "do-ex", .symbol destination, .symbol body] => some ⟨destination, .ex body⟩
  | .expression [.symbol "do-eu", .symbol destination, .symbol holds, .symbol goal] => some ⟨destination, .eu holds goal⟩
  | .expression [.symbol "do-eg", .symbol destination, .symbol body] => some ⟨destination, .eg body⟩
  | _ => none

theorem decode_encode (instruction : Instruction String) : decode (encode instruction) = some instruction := by
  rcases instruction with ⟨destination, node⟩
  cases node <;> rfl

theorem decode_exact (source : Atom) (instruction : Instruction String) (decoded : decode source = some instruction) :
    encode instruction = source := by
  unfold decode at decoded
  split at decoded <;> cases decoded <;> rfl

def decodeProgram (source : List Atom) : Option (List (Instruction String)) := source.mapM decode

theorem decodeProgram_encode (instructions : List (Instruction String)) :
    decodeProgram (instructions.map encode) = some instructions := by
  induction instructions with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [decodeProgram, List.map_cons, List.mapM_cons, decode_encode]
      change (decodeProgram (rest.map encode)).bind (fun later => some (instruction :: later)) = _
      rw [ih]
      rfl

theorem decodeProgram_exact (source : List Atom) (instructions : List (Instruction String))
    (decoded : decodeProgram source = some instructions) : instructions.map encode = source := by
  induction source generalizing instructions with
  | nil => cases decoded; rfl
  | cons first rest ih =>
      simp only [decodeProgram, List.mapM_cons, Option.bind_eq_bind] at decoded
      obtain ⟨instruction, firstDecoded, remaining⟩ := Option.bind_eq_some_iff.mp decoded
      obtain ⟨later, restDecoded, same⟩ := Option.bind_eq_some_iff.mp remaining
      cases Option.some.inj same
      simp only [List.map_cons, decode_exact first instruction firstDecoded, ih later restDecoded]

def symbolic {n : Nat} {domain : Diagram n} (program : Certified n domain) (atoms : String → Diagram n)
    (source : List Atom) (name : String) : Option (Diagram n) :=
  (decodeProgram source).bind fun instructions => root program atoms instructions name

/-- The source atoms first decode to the instruction/data profile. This
theorem does not certify the authored MeTTa functions with those spellings. -/
theorem symbolic_path_exact {n : Nat} {domain : Diagram n} (program : Certified n domain)
    (atoms : String → Diagram n) (source : List Atom) (instructions : List (Instruction String))
    (decoded : decodeProgram source = some instructions) (name : String) (formula : Formula String)
    (expanded : (decodeFrom instructions []).bind (lookup name) = some formula) :
    (symbolic program atoms source name).map denote =
      some (meaning (denote domain) (Relation domain program.rules) (fun label => denote (atoms label)) formula) := by
  simpa [symbolic, decoded] using root_path_exact program atoms instructions name formula expanded

namespace Controls

def core : List (Instruction String) :=
  [⟨"f001", .truth⟩, ⟨"f002", .atom "dead"⟩, ⟨"f003", .eu "f001" "f002"⟩,
   ⟨"f004", .neg "f003"⟩, ⟨"f005", .eg "f004"⟩]

theorem actual_opcode_shapes_roundtrip : decodeProgram (core.map encode) = some core := decodeProgram_encode core

theorem nested_operand_expansion :
    (decodeFrom core []).bind (lookup "f005") = some (.eg (.neg (.eu .truth (.atom "dead")))) := by decide +kernel

theorem unknown_operation_is_not_ignored :
    decodeProgram [.expression [.symbol "do-unknown", .symbol "f000"]] = none := by decide

theorem variable_name_is_not_a_fixed_reference :
    decode (.expression [.symbol "do-ex", .symbol "f000", .var "earlier"]) = none := by decide

theorem wrong_arity_is_not_a_formula :
    decode (.expression [.symbol "do-eu", .symbol "f000", .symbol "f001"]) = none := by decide

theorem reordered_dependencies_decline :
    decodeFrom (core.reverse) [] = none := by decide +kernel

theorem duplicate_definition_does_not_choose_an_overwrite :
    decodeFrom ([⟨"f", .truth⟩, ⟨"f", .neg "f"⟩] : List (Instruction String)) [] = none := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLInstructionCodec
