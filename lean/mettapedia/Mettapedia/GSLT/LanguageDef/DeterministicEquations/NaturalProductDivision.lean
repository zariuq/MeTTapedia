import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ListData
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.HostExtension

/-!
# Decoded natural product, quotient and remainder primitives

The additional operations act on arbitrary natural data. Quotient/remainder
refuse a zero divisor before producing a value; malformed scalar inputs also
fault. The previous host, including its constructor behavior, is preserved
outside these three names. Word bounds, wrapping and guest theorem authority
are not primitive operations here. Executable BigInt/runtime binding remains
a separate realization obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

inductive NaturalProduct where
  | multiply | quotient | remainder
  deriving DecidableEq, Repr

def naturalProduct? : String → Option NaturalProduct
  | "nik:nat-mul" => some .multiply
  | "nik:nat-div" => some .quotient
  | "nik:nat-mod" => some .remainder
  | _ => none

def NaturalProduct.result (operation : NaturalProduct) (left right : Nat) : PrimitiveResult :=
  match operation with
  | .multiply => .value (natural (left * right))
  | .quotient => if right = 0 then .fault else .value (natural (left / right))
  | .remainder => if right = 0 then .fault else .value (natural (left % right))

def productDivisionHost : Host where
  primitive head arguments :=
    match naturalProduct? head with
    | some operation =>
        match arguments with
        | [left, right] =>
            match natural? left, natural? right with
            | some left, some right => operation.result left right
            | _, _ => .fault
        | _ => .fault
    | none => computationalHost.primitive head arguments

theorem productDivisionHost_binary {head : String} {operation : NaturalProduct}
    (selected : naturalProduct? head = some operation) (left right : Nat) :
    productDivisionHost.primitive head [natural left, natural right] = operation.result left right := by
  simp [productDivisionHost, selected]

theorem productDivisionHost_mul (left right : Nat) :
    productDivisionHost.primitive "nik:nat-mul" [natural left, natural right] =
      .value (natural (left * right)) :=
  productDivisionHost_binary (head := "nik:nat-mul") (operation := .multiply) rfl left right

theorem productDivisionHost_div (left right : Nat) (nonzero : right ≠ 0) :
    productDivisionHost.primitive "nik:nat-div" [natural left, natural right] =
      .value (natural (left / right)) := by
  rw [productDivisionHost_binary (head := "nik:nat-div") (operation := .quotient) rfl]
  simp [NaturalProduct.result, nonzero]

theorem productDivisionHost_mod (left right : Nat) (nonzero : right ≠ 0) :
    productDivisionHost.primitive "nik:nat-mod" [natural left, natural right] =
      .value (natural (left % right)) := by
  rw [productDivisionHost_binary (head := "nik:nat-mod") (operation := .remainder) rfl]
  simp [NaturalProduct.result, nonzero]

theorem productDivisionHost_div_zero (left : Nat) :
    productDivisionHost.primitive "nik:nat-div" [natural left, natural 0] = .fault := by
  rw [productDivisionHost_binary (head := "nik:nat-div") (operation := .quotient) rfl]
  rfl

theorem productDivisionHost_mod_zero (left : Nat) :
    productDivisionHost.primitive "nik:nat-mod" [natural left, natural 0] = .fault := by
  rw [productDivisionHost_binary (head := "nik:nat-mod") (operation := .remainder) rfl]
  rfl

theorem productDivisionHost_prior (head : String) (arguments : List Term)
    (notNew : naturalProduct? head = none) :
    productDivisionHost.primitive head arguments = computationalHost.primitive head arguments := by
  simp [productDivisionHost, notNew]

theorem productDivisionHost_agrees (heads : List String)
    (notNew : ∀ head ∈ heads, naturalProduct? head = none) :
    computationalHost.AgreesOn productDivisionHost heads := by
  intro head member arguments
  exact (productDivisionHost_prior head arguments (notNew head member)).symm

theorem productDivisionHost_wrong_arity {head : String} {operation : NaturalProduct}
    (selected : naturalProduct? head = some operation) (arguments : List Term)
    (wrong : arguments.length ≠ 2) :
    productDivisionHost.primitive head arguments = .fault := by
  cases arguments with
  | nil => simp [productDivisionHost, selected]
  | cons first rest =>
      cases rest with
      | nil => simp [productDivisionHost, selected]
      | cons second rest =>
          cases rest with
          | nil => simp at wrong
          | cons third rest => simp [productDivisionHost, selected]

theorem productDivisionHost_non_natural {head : String} {operation : NaturalProduct}
    (selected : naturalProduct? head = some operation) (left right : Term)
    (malformed : natural? left = none ∨ natural? right = none) :
    productDivisionHost.primitive head [left, right] = .fault := by
  rcases malformed with leftBad | rightBad
  · simp [productDivisionHost, selected, leftBad]
  · cases first : natural? left <;> simp [productDivisionHost, selected, first, rightBad]

namespace NaturalProductDivisionControls

theorem unbounded_product_does_not_wrap :
    productDivisionHost.primitive "nik:nat-mul"
      [natural 18446744073709551616, natural 18446744073709551616] =
      .value (natural 340282366920938463463374607431768211456) := productDivisionHost_mul _ _

theorem quotient_uses_floor_division :
    productDivisionHost.primitive "nik:nat-div" [natural 17, natural 5] = .value (natural 3) :=
  productDivisionHost_div 17 5 (by decide)

theorem remainder_uses_same_divisor :
    productDivisionHost.primitive "nik:nat-mod" [natural 17, natural 5] = .value (natural 2) :=
  productDivisionHost_mod 17 5 (by decide)

theorem zero_divisors_fault_before_value (value : Nat) :
    productDivisionHost.primitive "nik:nat-div" [natural value, natural 0] = .fault ∧
    productDivisionHost.primitive "nik:nat-mod" [natural value, natural 0] = .fault :=
  ⟨productDivisionHost_div_zero value, productDivisionHost_mod_zero value⟩

theorem malformed_scalar_faults :
    productDivisionHost.primitive "nik:nat-mul" [.sym "not-a-number", natural 3] = .fault := by
  apply productDivisionHost_non_natural (operation := .multiply) rfl
  left
  rfl

theorem guest_name_is_not_a_primitive :
    productDivisionHost.primitive "vibe:literal-query" [] = .unhandled := rfl

end NaturalProductDivisionControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
