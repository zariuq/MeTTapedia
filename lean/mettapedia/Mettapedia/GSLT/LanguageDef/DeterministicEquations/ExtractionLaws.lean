import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ComputationLists
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalProductDivision

/-!
# Proof constructors for extraction of typed computations

The constructors compose runs of the existing equation evaluator. Source
values, including optional refusals, are data; resource exhaustion is not a
source value. These laws do not assert correspondence for an extracted
function. The extracting elaborator must build that proof from its actual
defining equations and recursion principle.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction

def encodeOption {α : Type} (encode : α → Term) : Option α → Term
  | none => .sym "None"
  | some value => .expr [.sym "Some", encode value]

def encodeList {α : Type} (encode : α → Term) (values : List α) : Term :=
  .list (values.map encode)

def encodeByte (value : UInt8) : Term := natural value.toNat

def named (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)

theorem named_not_special {head : String} {arguments : List Term}
    (notLet : head ≠ "let") (notNullary : head ≠ "metta-nullary") :
    ¬ Special head arguments := by
  simp [Special, notLet, notNullary]

theorem evaluate_call {P : Program} {H : Host} {environment : Env}
    {head : String} {sources values : List Term} {result : Term}
    (notLet : head ≠ "let") (notNullary : head ≠ "metta-nullary")
    (children : List.Forall₂ (Evaluates P H environment) sources values)
    (operation : Applies P H head values result) :
    Evaluates P H environment (named head sources) result :=
  Evaluates.call (named_not_special notLet notNullary) children operation

theorem evaluate_constructor {P : Program} {H : Host} {environment : Env}
    {head : String} {sources values : List Term}
    (notLet : head ≠ "let") (notNullary : head ≠ "metta-nullary")
    (undefined : P.defines head = false) (unhandled : H.primitive head values = .unhandled)
    (children : List.Forall₂ (Evaluates P H environment) sources values) :
    Evaluates P H environment (named head sources) (named head values) :=
  evaluate_call notLet notNullary children (Applies.constructor undefined unhandled)

theorem evaluate_primitive {P : Program} {H : Host} {environment : Env}
    {head : String} {sources values : List Term} {result : Term}
    (notLet : head ≠ "let") (notNullary : head ≠ "metta-nullary")
    (undefined : P.defines head = false) (computed : H.primitive head values = .value result)
    (children : List.Forall₂ (Evaluates P H environment) sources values) :
    Evaluates P H environment (named head sources) result :=
  evaluate_call notLet notNullary children (Applies.primitive undefined computed)

theorem evaluate_list_nil (P : Program) (H : Host) (environment : Env) :
    Evaluates P H environment (.list []) (.list []) := Evaluates.list .nil

theorem evaluate_list_cons {P : Program} {environment : Env}
    {first rest : Term} {value : Term} {values : List Term}
    (undefined : P.defines "nik:list-cons" = false)
    (head : Evaluates P productDivisionHost environment first value)
    (tail : Evaluates P productDivisionHost environment rest (.list values)) :
    Evaluates P productDivisionHost environment (named "nik:list-cons" [first, rest])
      (.list (value :: values)) := by
  apply evaluate_primitive (values := [value, .list values]) (by decide) (by decide) undefined
  · rfl
  · exact .cons head (.cons tail .nil)

theorem evaluate_remainder {P : Program} {environment : Env} {source : Term} (value modulus : Nat)
    (undefined : P.defines "nik:nat-mod" = false) (positive : modulus ≠ 0)
    (operand : Evaluates P productDivisionHost environment source (natural value)) :
    Evaluates P productDivisionHost environment (named "nik:nat-mod" [source, natural modulus])
      (natural (value % modulus)) := by
  apply evaluate_primitive (by decide) (by decide) undefined
    (productDivisionHost_mod value modulus positive)
  exact .cons operand (.cons (Evaluates.literal P productDivisionHost environment _) .nil)

theorem evaluate_quotient {P : Program} {environment : Env} {source : Term} (value divisor : Nat)
    (undefined : P.defines "nik:nat-div" = false) (positive : divisor ≠ 0)
    (operand : Evaluates P productDivisionHost environment source (natural value)) :
    Evaluates P productDivisionHost environment (named "nik:nat-div" [source, natural divisor])
      (natural (value / divisor)) := by
  apply evaluate_primitive (by decide) (by decide) undefined
    (productDivisionHost_div value divisor positive)
  exact .cons operand (.cons (Evaluates.literal P productDivisionHost environment _) .nil)

theorem evaluate_byte {P : Program} {environment : Env} {source : Term} (value : Nat)
    (undefined : P.defines "nik:nat-mod" = false)
    (operand : Evaluates P productDivisionHost environment source (natural value)) :
    Evaluates P productDivisionHost environment (named "nik:nat-mod" [source, natural 256])
      (encodeByte (UInt8.ofNat value)) := by
  simpa [encodeByte, UInt8.toNat_ofNat'] using
    evaluate_remainder value 256 undefined (by decide) operand

theorem applies_option_cases {α β : Type} {P : Program} {H : Host}
    (encode : α → Term) (encodeResult : β → Term) (head : String) (captures : List Term)
    (value : Option α) (continuation : α → Option β)
    (noneCase : Applies P H head (.sym "None" :: captures) (.sym "None"))
    (someCase : ∀ a, Applies P H head (named "Some" [encode a] :: captures)
      (encodeOption encodeResult (continuation a))) :
    Applies P H head (encodeOption encode value :: captures)
      (encodeOption encodeResult (value.bind continuation)) := by
  cases value with
  | none => exact noneCase
  | some a => exact someCase a

theorem completed_exact {P : Program} {H : Host} {head : String} {arguments : List Term}
    {result : Term} (computed : Applies P H head arguments result) (fuel : Nat)
    (completed : apply P H fuel head arguments ≠ .exhausted) :
    apply P H fuel head arguments = .value result := computed.completed fuel completed

theorem result_exact {P : Program} {H : Host} {head : String} {arguments : List Term}
    {result other : Term} (computed : Applies P H head arguments result) :
    Applies P H head arguments other ↔ other = result := by
  constructor
  · exact fun observation => observation.deterministic computed
  · rintro rfl
    exact computed

theorem incorrect_result_refused {P : Program} {H : Host} {head : String} {arguments : List Term}
    {result other : Term} (computed : Applies P H head arguments result) (different : other ≠ result) :
    ¬ Applies P H head arguments other := fun observation => different (observation.deterministic computed)

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction
