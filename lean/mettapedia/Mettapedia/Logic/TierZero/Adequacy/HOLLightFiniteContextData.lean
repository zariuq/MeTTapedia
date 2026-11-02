import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteSignatureLookup

/-!
# Validated finite data for the original registered HOL declaration context

The data stores full structural symbol/provenance keys, schemas and occupied
names. Its finite validator reconstructs the original TheoryContext fields.
Decoding is local formation checking, not declaration/proof-history replay.
The decoder establishes structural registration laws; logical availability
still follows original source admission and protected rooted authority.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextData

open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open HOLLightFiniteSignatureLookup

local instance : DecidableEq TypeOp := typeOpCodec.decEq
local instance : DecidableEq Const := constantCodec.decEq
local instance : DecidableEq Ty := tyCodec.decEq

def definedNameCodec : Codec DefinedSymbolName :=
  (Codec.prod Codec.nat nameCodec).mapped
    (fun name => match name with | .typeOperator name => (0, name) | .constant name => (1, name))
    (fun value => match value with | (0, name) => some (.typeOperator name) | (1, name) => some (.constant name) | _ => none)
    (by intro name; cases name <;> rfl)

structure ContextData where
  names : NameContext
  operators : List (TypeOp × Nat)
  constants : List (Const × Ty)

def codec : Codec ContextData :=
  (Codec.prod (finsetCodec definedNameCodec)
    (Codec.prod (Codec.list (Codec.prod typeOpCodec Codec.nat)) (Codec.list (Codec.prod constantCodec tyCodec)))).mapped
    (fun value => (value.names, value.operators, value.constants))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩) (fun _ => rfl)

def signature (data : ContextData) : Signature :=
  ⟨fun key => rowLookup key data.operators, fun key => rowLookup key data.constants⟩

def WellFormed (data : ContextData) : Prop :=
  (∀ entry ∈ data.operators, .typeOperator (operatorName entry.1) ∈ data.names) ∧
  (∀ entry ∈ data.constants, .constant (constantName entry.1) ∈ data.names) ∧
  (∀ first ∈ data.operators, ∀ second ∈ data.operators,
    operatorName first.1 = operatorName second.1 → first = second) ∧
  (∀ first ∈ data.constants, ∀ second ∈ data.constants,
    constantName first.1 = constantName second.1 → first = second) ∧
  (∀ entry ∈ data.constants, TypeFormed (signature data) entry.2)

def valid (data : ContextData) : Bool :=
  data.operators.all (fun entry => decide (.typeOperator (operatorName entry.1) ∈ data.names)) &&
  (data.constants.all (fun entry => decide (.constant (constantName entry.1) ∈ data.names)) &&
  (data.operators.all (fun first => data.operators.all (fun second =>
    decide (operatorName first.1 = operatorName second.1 → first = second))) &&
  (data.constants.all (fun first => data.constants.all (fun second =>
    decide (constantName first.1 = constantName second.1 → first = second))) &&
  data.constants.all (fun entry => typeFormedB (signature data) entry.2))))

theorem valid_iff (data : ContextData) : valid data = true ↔ WellFormed data := by
  simp only [valid, WellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, typeFormedB_eq_true_iff]

def toContext (data : ContextData) (formed : WellFormed data) : TheoryContext where
  names := data.names
  signature := signature data
  typeNames := by
    intro operator arity found
    exact formed.1 (operator, arity) (rowLookup_member found)
  constantNames := by
    intro constant schema found
    exact formed.2.1 (constant, schema) (rowLookup_member found)
  uniqueTypeNames := by
    intro first second firstArity secondArity firstKnown secondKnown sameName
    have same := formed.2.2.1 (first, firstArity) (rowLookup_member firstKnown)
      (second, secondArity) (rowLookup_member secondKnown) sameName
    exact congrArg Prod.fst same
  uniqueConstantNames := by
    intro first second firstSchema secondSchema firstKnown secondKnown sameName
    have same := formed.2.2.2.1 (first, firstSchema) (rowLookup_member firstKnown)
      (second, secondSchema) (rowLookup_member secondKnown) sameName
    exact congrArg Prod.fst same
  constantTypes := by
    intro constant schema found
    exact formed.2.2.2.2 (constant, schema) (rowLookup_member found)

def toTable (data : ContextData) (formed : WellFormed data) :
    Mettapedia.Languages.HOLLight.MeTTa.DeclarationTable.Table (toContext data formed) where
  operators :=
    { entries := data.operators
      registered := by
        intro entry member
        apply rowLookup_of_consistent_member _ member
        intro first firstMember second secondMember same
        exact congrArg Prod.snd (formed.2.2.1 first firstMember second secondMember (congrArg operatorName same))
      complete := fun _ _ found => rowLookup_member found }
  constants := data.constants
  registered := by
    intro entry member
    apply rowLookup_of_consistent_member _ member
    intro first firstMember second secondMember same
    exact congrArg Prod.snd (formed.2.2.2.1 first firstMember second secondMember (congrArg constantName same))
  complete := fun _ _ found => rowLookup_member found

theorem toTable_operator_rows (data : ContextData) (formed : WellFormed data) :
    (toTable data formed).operators.entries = data.operators := rfl

theorem toTable_constant_rows (data : ContextData) (formed : WellFormed data) :
    (toTable data formed).constants = data.constants := rfl

def decode (data : ContextData) : Option TheoryContext :=
  if checked : valid data = true then some (toContext data ((valid_iff data).mp checked)) else none

theorem decode_fields (data : ContextData) {context : TheoryContext} (decoded : decode data = some context) :
    context.names = data.names ∧ context.signature = signature data := by
  unfold decode at decoded
  split at decoded
  · cases Option.some.inj decoded
    exact ⟨rfl, rfl⟩
  · cases decoded

theorem decode_isSome_iff (data : ContextData) : (decode data).isSome = true ↔ WellFormed data := by
  simp only [decode]
  split
  · rename_i checked
    exact ⟨fun _ => (valid_iff data).mp checked, fun _ => rfl⟩
  · rename_i invalid
    constructor
    · intro impossible
      cases impossible
    · intro formed
      exact False.elim (invalid ((valid_iff data).mpr formed))

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextData
