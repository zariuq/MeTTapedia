import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofProgram

/-! Total decoding of supplied proof data. Original proof constructors and v2
wrappers retain their ordered children, literal operands, replacements and
occurrence hints. The round trips prove injectivity of canonical encodings;
they do not identify different external numeral spellings or certify a text
reader. Unknown shapes and variable-valued payloads are refused. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.ProofWitnessCodec

open ComputationalData ComputationalShift ComputationalProofs ComputationalLiterals ComputationalSimultaneous
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def naturals : List Term → Option (List Nat)
  | [] => some []
  | first :: rest => return (← natural? first) :: (← naturals rest)

@[simp] theorem naturals_encoded (values : List Nat) : naturals (values.map natural) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [naturals, ih]

def literalRequest : Term → Option LiteralRequest
  | .list [.sym "Literal:IsNat", value] => return .isNat (← natural? value)
  | .list [.sym "Literal:Lt", left, right] => return .lessThan (← natural? left) (← natural? right)
  | .list [.sym "Literal:Add", left, right] => return .addition (← natural? left) (← natural? right)
  | .list [.sym "Literal:Mul", left, right] => return .multiplication (← natural? left) (← natural? right)
  | .list [.sym "Literal:Div", left, right] => return .division (← natural? left) (← natural? right)
  | .list [.sym "Literal:Length", value] => return .length (← decode value)
  | .list [.sym "Literal:Get", value, index] => return .get (← decode value) (← natural? index)
  | _ => none

@[simp] theorem literalRequest_encoded (request : LiteralRequest) :
    literalRequest (encodeRequest request) = some request := by
  cases request <;> simp [literalRequest, encodeRequest]

def original : Term → Option ProofWitness
  | .list [.sym "Proof:Axiom", index] => return .axiom (← natural? index)
  | .list [.sym "Proof:Definition", index, .list hints] =>
      return .definition (← natural? index) (← naturals hints)
  | .list [.sym "Proof:MP", implication, premise] => return .modusPonens (← original implication) (← original premise)
  | .list [.sym "Proof:Instantiate", symbol, value, child] =>
      return .instantiate (← decodeSymbol symbol) (← decode value) (← original child)
  | .list [.sym "Proof:Literal", request] => return .literal (← literalRequest request)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem original_encoded (witness : ProofWitness) :
    original (ComputationalProofs.encodeWitness witness) = some witness := by
  induction witness <;> simp_all [original, ComputationalProofs.encodeWitness, encodeBinders]

def replacement : Term → Option (Spec.SymId × Spec.Term)
  | .list [symbol, value] => return (← decodeSymbol symbol, ← decode value)
  | _ => none

def replacementList : List Term → Option (List (Spec.SymId × Spec.Term))
  | [] => some []
  | first :: rest => return (← replacement first) :: (← replacementList rest)

@[simp] theorem replacementList_encoded (values : List (Spec.SymId × Spec.Term)) :
    replacementList (values.map encodeReplacement) = some values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [replacementList, replacement, encodeReplacement, ih]

def simultaneous : Term → Option SimultaneousProofs.Witness
  | .list [.sym "Proof2:Base", witness] => return .base (← original witness)
  | .list [.sym "Proof2:MP", implication, premise] =>
      return .modusPonens (← simultaneous implication) (← simultaneous premise)
  | .list [.sym "Proof2:Many", .list replacements, child] =>
      return .instantiateMany (← replacementList replacements) (← simultaneous child)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem simultaneous_encoded (witness : SimultaneousProofs.Witness) :
    simultaneous (ComputationalProofsV2.encodeWitness witness) = some witness := by
  induction witness <;> simp_all [simultaneous, ComputationalProofsV2.encodeWitness, encodeReplacements]

theorem original_encoding_injective : Function.Injective ComputationalProofs.encodeWitness := by
  intro first second same
  exact Option.some.inj (by simpa only [original_encoded] using congrArg original same)

theorem simultaneous_encoding_injective : Function.Injective ComputationalProofsV2.encodeWitness := by
  intro first second same
  exact Option.some.inj (by simpa only [simultaneous_encoded] using congrArg simultaneous same)

theorem malformed_wrapper_refused : simultaneous (.list [.sym "Proof2:MP", .list []]) = none := by
  simp [simultaneous]
theorem variable_child_refused : simultaneous (.list [.sym "Proof2:Base", .var "forged"]) = none := by
  simp [simultaneous, original]

#print axioms original_encoded
#print axioms simultaneous_encoded

end Mettapedia.Languages.VibeITP.Presentation.ProofWitnessCodec
