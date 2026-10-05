import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalProductDivision

/-!
# Structural comparison of evaluated data

This primitive compares constructor data, including constructor tags and the
order and multiplicity of children. It performs no evaluation, unification or
guest conversion. Its realization must preserve this exact data equality.
All previously available primitives remain unchanged outside its own name.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations

mutual

def dataEqual : Term → Term → Bool
  | .sym left, .sym right => left == right
  | .lit left, .lit right => left == right
  | .var left, .var right => left == right
  | .expr left, .expr right => dataListEqual left right
  | .list left, .list right => dataListEqual left right
  | _, _ => false
termination_by left _ => sizeOf left

def dataListEqual : List Term → List Term → Bool
  | [], [] => true
  | left :: lefts, right :: rights => dataEqual left right && dataListEqual lefts rights
  | _, _ => false
termination_by left _ => sizeOf left

end

mutual

theorem dataEqual_eq_true (left right : Term) : dataEqual left right = true ↔ left = right := by
  cases left with
  | sym name => cases right <;> simp [dataEqual]
  | lit name => cases right <;> simp [dataEqual]
  | var name => cases right <;> simp [dataEqual]
  | expr items =>
      cases right <;> simp only [dataEqual, reduceCtorEq, Bool.false_eq_true, iff_self, Term.expr.injEq]
      exact dataListEqual_eq_true items _
  | list items =>
      cases right <;> simp only [dataEqual, reduceCtorEq, Bool.false_eq_true, iff_self, Term.list.injEq]
      exact dataListEqual_eq_true items _
termination_by sizeOf left

theorem dataListEqual_eq_true (left right : List Term) : dataListEqual left right = true ↔ left = right := by
  cases left with
  | nil => cases right <;> simp [dataListEqual]
  | cons first rest =>
      cases right with
      | nil => simp [dataListEqual]
      | cons other others =>
          simp only [dataListEqual, Bool.and_eq_true, dataEqual_eq_true first other,
            dataListEqual_eq_true rest others, List.cons.injEq]
termination_by sizeOf left

end

instance : DecidableEq Term := fun left right =>
  if equal : dataEqual left right = true then isTrue ((dataEqual_eq_true left right).mp equal)
  else isFalse (fun same => equal ((dataEqual_eq_true left right).mpr same))

def dataEqualityHost : Host where
  primitive head arguments :=
    if head = "nik:data-eq" then
      match arguments with
      | [left, right] => .value (boolean (decide (left = right)))
      | _ => .fault
    else productDivisionHost.primitive head arguments

theorem dataEqualityHost_compare (left right : Term) :
    dataEqualityHost.primitive "nik:data-eq" [left, right] =
      .value (boolean (decide (left = right))) := by
  simp [dataEqualityHost]

theorem dataEqualityHost_encoded {α : Type} [DecidableEq α]
    (encode : α → Term) (injective : Function.Injective encode) (left right : α) :
    dataEqualityHost.primitive "nik:data-eq" [encode left, encode right] =
      .value (boolean (decide (left = right))) := by
  simp [dataEqualityHost, injective.eq_iff]

theorem dataEqualityHost_prior (head : String) (arguments : List Term)
    (different : head ≠ "nik:data-eq") :
    dataEqualityHost.primitive head arguments = productDivisionHost.primitive head arguments := by
  simp [dataEqualityHost, different]

theorem dataEqualityHost_agrees (heads : List String)
    (absent : "nik:data-eq" ∉ heads) :
    productDivisionHost.AgreesOn dataEqualityHost heads := by
  intro head member arguments
  exact (dataEqualityHost_prior head arguments (fun same => absent (same ▸ member))).symm

theorem dataEqualityHost_computational_agrees (heads : List String)
    (absent : "nik:data-eq" ∉ heads)
    (noProduct : ∀ head ∈ heads, naturalProduct? head = none) :
    computationalHost.AgreesOn dataEqualityHost heads := by
  intro head member arguments
  exact (productDivisionHost_agrees heads noProduct head member arguments).trans
    (dataEqualityHost_agrees heads absent head member arguments)

theorem dataEqualityHost_wrong_arity (arguments : List Term) (wrong : arguments.length ≠ 2) :
    dataEqualityHost.primitive "nik:data-eq" arguments = .fault := by
  cases arguments with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => simp at wrong
          | cons third rest => rfl

theorem data_equality_computes (program : Program) (left right : Term)
    (undefined : program.defines "nik:data-eq" = false) :
    Applies program dataEqualityHost "nik:data-eq" [left, right]
      (boolean (decide (left = right))) :=
  Applies.primitive undefined (dataEqualityHost_compare left right)

namespace DataEqualityControls

theorem reflexive (value : Term) :
    dataEqualityHost.primitive "nik:data-eq" [value, value] = .value (.sym "True") := by
  simp [dataEqualityHost, boolean]

theorem constructor_names_are_significant :
    dataEqualityHost.primitive "nik:data-eq"
      [.expr [.sym "Variable", natural 0], .expr [.sym "Constant", natural 0]] =
      .value (.sym "False") := by simp [dataEqualityHost, boolean]

theorem child_order_is_significant :
    dataEqualityHost.primitive "nik:data-eq"
      [.list [.sym "a", .sym "b"], .list [.sym "b", .sym "a"]] = .value (.sym "False") := by simp [dataEqualityHost, boolean]

theorem multiplicity_is_significant :
    dataEqualityHost.primitive "nik:data-eq"
      [.list [.sym "a", .sym "a"], .list [.sym "a"]] = .value (.sym "False") := by simp [dataEqualityHost, boolean]

theorem lists_and_expressions_are_distinct :
    dataEqualityHost.primitive "nik:data-eq" [.list [.sym "a"], .expr [.sym "a"]] =
      .value (.sym "False") := by simp [dataEqualityHost, boolean]

theorem syntactic_comparison_does_not_evaluate :
    dataEqualityHost.primitive "nik:data-eq"
      [.expr [.sym "nik:nat-mul", natural 2, natural 3], natural 6] = .value (.sym "False") := by simp [dataEqualityHost, boolean, natural]

theorem guest_checking_is_not_a_primitive :
    dataEqualityHost.primitive "mm0:conversion" [] = .unhandled := rfl

theorem incomplete_comparison_faults :
    dataEqualityHost.primitive "nik:data-eq" [.sym "a"] = .fault := rfl

end DataEqualityControls

end Mettapedia.GSLT.LanguageDef.DeterministicEquations
