import Mettapedia.GSLT.LanguageDef.CettaWireTerm
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationSignature
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRegularity

/-!
# CeTTa wire data in the native scoped term carrier

The existing physical wire carrier is represented with ordinary native
constants and application. Tagged names contain literal strings and natural
numbers; their typing recognizes those tags directly, without a registry or
proof-valued payload. Two fixed binary constructors represent applications
and ordered argument lists. All declarations are opaque.

Formation of this data type does not validate a represented proof, request,
or theory. The decoder is independent of typing and rejects other native
terms. Mathematical admission remains the responsibility of the selected
checker and its independently justified meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeWireData

open Presentation Presentation.Declaration
open Mettapedia.GSLT.LanguageDef

abbrev Wire := CettaWire.Term

def dataName : Lean.Name := .str .anonymous "NativeWire.Data"
def applicationName : Lean.Name := .str .anonymous "NativeWire.application"
def consName : Lean.Name := .str .anonymous "NativeWire.cons"
def nilName : Lean.Name := .str .anonymous "NativeWire.nil"
def symbolPrefix : Lean.Name := .str .anonymous "NativeWire.symbol"
def stringPrefix : Lean.Name := .str .anonymous "NativeWire.string"
def naturalPrefix : Lean.Name := .str .anonymous "NativeWire.natural"

def dataType {n : Nat} : Tower.Tm n := .const dataName

def binaryType {n : Nat} : Tower.Tm n := .pi dataType (.pi dataType dataType)

/-- A fixed constructor signature with directly tagged literal declarations.
Literal contents are data, not names resolved in an external proof store. -/
def signature : Signature Tower.Head where
  entries name :=
    if name = dataName then some ⟨sortTm Tower.zero, none⟩
    else if name = applicationName ∨ name = consName then some ⟨binaryType, none⟩
    else if name = nilName then some ⟨dataType, none⟩
    else match name with
      | .str tag _ =>
          if tag = symbolPrefix ∨ tag = stringPrefix then some ⟨dataType, none⟩ else none
      | .num tag _ =>
          if tag = naturalPrefix then some ⟨dataType, none⟩ else none
      | .anonymous => none

def rules : Rules Tower.Head := extendRules Tower.rules signature

mutual

def encode {n : Nat} : Wire → Tower.Tm n
  | .symbol name => .const (.str symbolPrefix name)
  | .string value => .const (.str stringPrefix value)
  | .natural value => .const (.num naturalPrefix value)
  | .application head arguments =>
      .app (.app (.const applicationName) (.const (.str symbolPrefix head))) (encodeList arguments)
termination_by wire => sizeOf wire

def encodeList {n : Nat} : List Wire → Tower.Tm n
  | [] => .const nilName
  | value :: values => .app (.app (.const consName) (encode value)) (encodeList values)
termination_by wires => sizeOf wires

end

mutual

def decode {n : Nat} : Tower.Tm n → Option Wire
  | .const (.str tag name) =>
      if tag = symbolPrefix then some (.symbol name)
      else if tag = stringPrefix then some (.string name) else none
  | .const (.num tag value) =>
      if tag = naturalPrefix then some (.natural value) else none
  | .app (.app (.const constructor) (.const (.str tag head))) arguments =>
      if constructor = applicationName ∧ tag = symbolPrefix then
        (decodeList arguments).map (.application head)
      else none
  | _ => none
termination_by term => sizeOf term

def decodeList {n : Nat} : Tower.Tm n → Option (List Wire)
  | .const name => if name = nilName then some [] else none
  | .app (.app (.const constructor) value) values =>
      if constructor = consName then do
        let decodedValue ← decode value
        let decodedValues ← decodeList values
        pure (decodedValue :: decodedValues)
      else none
  | _ => none
termination_by term => sizeOf term

end

mutual

@[simp] theorem decode_encode {n : Nat} (wire : Wire) :
    decode (encode (n := n) wire) = some wire := by
  cases wire with
  | symbol name => simp [encode, decode]
  | string value => simp [encode, decode, stringPrefix, symbolPrefix]
  | natural value => simp [encode, decode]
  | application head arguments =>
      simp only [encode, decode, and_self, ite_true, decodeList_encodeList arguments, Option.map_some]
termination_by sizeOf wire

@[simp] theorem decodeList_encodeList {n : Nat} (wires : List Wire) :
    decodeList (encodeList (n := n) wires) = some wires := by
  cases wires with
  | nil => simp [encodeList, decodeList]
  | cons wire wires =>
      simp [encodeList, decodeList, decode_encode wire, decodeList_encodeList wires]
termination_by sizeOf wires

end

theorem encode_injective {n : Nat} : Function.Injective (encode (n := n)) := by
  intro left right equal
  have decoded := congrArg decode equal
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem encodeList_injective {n : Nat} : Function.Injective (encodeList (n := n)) := by
  intro left right equal
  have decoded := congrArg decodeList equal
  simpa only [decodeList_encodeList, Option.some.injEq] using decoded

mutual

@[simp] theorem subst_encode {n m : Nat} (substitution : Sub Tower.Head n m) (wire : Wire) :
    subst substitution (encode wire) = encode wire := by
  cases wire with
  | symbol _ | string _ | natural _ => simp only [encode, subst]
  | application head arguments =>
      simp only [encode, subst, subst_encodeList substitution arguments]
termination_by sizeOf wire

@[simp] theorem subst_encodeList {n m : Nat} (substitution : Sub Tower.Head n m)
    (wires : List Wire) : subst substitution (encodeList wires) = encodeList wires := by
  cases wires with
  | nil => simp only [encodeList, subst]
  | cons wire wires =>
      simp only [encodeList, subst, subst_encode substitution wire, subst_encodeList substitution wires]
termination_by sizeOf wires

end

@[simp] theorem rename_encode {n m : Nat} (rho : Ren n m) (wire : Wire) :
    rename rho (encode wire) = encode wire := by
  rw [← subst_renSub, subst_encode]

@[simp] theorem rename_encodeList {n m : Nat} (rho : Ren n m) (wires : List Wire) :
    rename rho (encodeList wires) = encodeList wires := by
  rw [← subst_renSub, subst_encodeList]

private theorem data_lookup : rules.constantType dataName = some (sortTm Tower.zero) := by decide
private theorem application_lookup : rules.constantType applicationName = some binaryType := by decide
private theorem cons_lookup : rules.constantType consName = some binaryType := by decide
private theorem nil_lookup : rules.constantType nilName = some dataType := by decide

private theorem symbol_lookup (value : String) :
    rules.constantType (.str symbolPrefix value) = some dataType := by
  simp [rules, extendRules, combinedType, Tower.rules, Signature.typeOf?, signature,
    dataName, applicationName, consName, nilName, symbolPrefix, stringPrefix]

private theorem string_lookup (value : String) :
    rules.constantType (.str stringPrefix value) = some dataType := by
  simp [rules, extendRules, combinedType, Tower.rules, Signature.typeOf?, signature,
    dataName, applicationName, consName, nilName, symbolPrefix, stringPrefix]

private theorem natural_lookup (value : Nat) :
    rules.constantType (.num naturalPrefix value) = some dataType := by
  simp [rules, extendRules, combinedType, Tower.rules, Signature.typeOf?, signature,
    dataName, applicationName, consName, nilName, naturalPrefix]

theorem dataType_formed {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing rules context dataType (sortTm Tower.zero) :=
  .const data_lookup (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

private theorem binaryType_formed : FormationSensitive.Typing rules .nil binaryType
    (sortTm (.max Tower.zero (.max Tower.zero Tower.zero))) :=
  .piForm (dataType_formed _) (.sort _)
    (.piForm (dataType_formed _) (.sort _) (dataType_formed _) (.sort _) (.sorts _ _))
    (.sort _) (.sorts _ _)

private theorem literal_typed {n : Nat} (context : Tower.Ctx n) {name : Lean.Name}
    (declared : rules.constantType name = some dataType) :
    FormationSensitive.Typing rules context (.const name) dataType :=
  .const declared (dataType_formed _) (.sort Tower.zero)

private theorem binary_typed {n : Nat} {context : Tower.Ctx n} {name : Lean.Name}
    (declared : rules.constantType name = some binaryType) {left right : Tower.Tm n}
    (leftTyped : FormationSensitive.Typing rules context left dataType)
    (rightTyped : FormationSensitive.Typing rules context right dataType) :
    FormationSensitive.Typing rules context (.app (.app (.const name) left) right) dataType := by
  have headTyped : FormationSensitive.Typing rules context (.const name) binaryType :=
    .const declared binaryType_formed (.sort _)
  have first := FormationSensitive.Typing.appElim headTyped leftTyped
  have firstTyped : FormationSensitive.Typing rules context (.app (.const name) left)
      (.pi dataType dataType) := by
    simpa only [binaryType, dataType, inst0, subst] using first
  simpa only [dataType, inst0, subst] using FormationSensitive.Typing.appElim firstTyped rightTyped

theorem nil_typing {n : Nat} (context : Tower.Ctx n) :
    FormationSensitive.Typing rules context (.const nilName) dataType :=
  literal_typed context nil_lookup

theorem application_typing {n : Nat} {context : Tower.Ctx n}
    {head arguments : Tower.Tm n}
    (headTyped : FormationSensitive.Typing rules context head dataType)
    (argumentsTyped : FormationSensitive.Typing rules context arguments dataType) :
    FormationSensitive.Typing rules context
      (.app (.app (.const applicationName) head) arguments) dataType :=
  binary_typed application_lookup headTyped argumentsTyped

theorem cons_typing {n : Nat} {context : Tower.Ctx n} {head tail : Tower.Tm n}
    (headTyped : FormationSensitive.Typing rules context head dataType)
    (tailTyped : FormationSensitive.Typing rules context tail dataType) :
    FormationSensitive.Typing rules context
      (.app (.app (.const consName) head) tail) dataType :=
  binary_typed cons_lookup headTyped tailTyped

mutual

theorem encode_typing {n : Nat} (context : Tower.Ctx n) (wire : Wire) :
    FormationSensitive.Typing rules context (encode wire) dataType := by
  cases wire with
  | symbol name => simpa only [encode] using literal_typed context (symbol_lookup name)
  | string value => simpa only [encode] using literal_typed context (string_lookup value)
  | natural value => simpa only [encode] using literal_typed context (natural_lookup value)
  | application head arguments =>
      simpa only [encode] using binary_typed application_lookup (literal_typed context (symbol_lookup head))
        (encodeList_typing context arguments)
termination_by sizeOf wire

theorem encodeList_typing {n : Nat} (context : Tower.Ctx n) (wires : List Wire) :
    FormationSensitive.Typing rules context (encodeList wires) dataType := by
  cases wires with
  | nil => simpa only [encodeList] using literal_typed context nil_lookup
  | cons wire wires =>
      simpa only [encodeList] using binary_typed cons_lookup (encode_typing context wire) (encodeList_typing context wires)
termination_by sizeOf wires

end

theorem encode_judgment {n : Nat} {context : Tower.Ctx n}
    (formed : FormationSensitive.ContextFormation rules context) (wire : Wire) :
    FormationSensitive.Judgment rules context (encode wire) dataType :=
  ⟨formed, encode_typing context wire⟩

theorem symbol_string_distinct {n : Nat} (value : String) :
    encode (n := n) (.symbol value) ≠ encode (.string value) := by
  intro equal
  have impossible := encode_injective equal
  cases impossible

theorem application_retains_argument_order {n : Nat} (head : String) :
    encode (n := n) (.application head [.natural 0, .natural 1]) ≠
      encode (.application head [.natural 1, .natural 0]) := by
  intro equal
  have impossible := encode_injective equal
  cases impossible

theorem native_variable_rejected {n : Nat} (index : Fin n) :
    decode (.var index) = none := by simp [decode]

theorem malformed_application_rejected {n : Nat} :
    decode (n := n) (.app (.app (.const applicationName) (encode (.natural 0))) (encodeList [])) = none := by
  simp [encode, decode]

/-- Native data formation does not replace the structural wire decoder. -/
theorem formed_data_need_not_decode :
    ∃ term : Tower.Tm 0,
      FormationSensitive.Judgment rules .nil term dataType ∧ decode term = none := by
  refine ⟨.app (.app (.const applicationName) (encode (.natural 0))) (encodeList []),
    ⟨.nil, ?_⟩, malformed_application_rejected⟩
  exact application_typing (encode_typing .nil (.natural 0)) (encodeList_typing .nil [])

theorem represented_data_is_not_its_claim {n : Nat} :
    encode (n := n) (.symbol "proof-accepted") ≠ (.refl dataType : Tower.Tm n) := by
  intro equal
  simp only [encode] at equal
  cases equal

#print axioms decode_encode
#print axioms decodeList_encodeList
#print axioms encode_injective
#print axioms subst_encode
#print axioms rename_encode
#print axioms dataType_formed
#print axioms nil_typing
#print axioms application_typing
#print axioms cons_typing
#print axioms encode_typing
#print axioms encode_judgment
#print axioms symbol_string_distinct
#print axioms application_retains_argument_order
#print axioms native_variable_rejected
#print axioms malformed_application_rejected
#print axioms formed_data_need_not_decode

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeWireData
