import Mettapedia.GSLT.Topos.ConstructivePresheafFunctionPredicates
import Mettapedia.GSLT.Topos.PresheafEventModalControls

/-!
# Function-object and future-argument controls

Boolean exclusive-or yields different curried functions at its two parameter
values. A predicate with no arguments at stage zero gains an argument later;
checking a function only against its current arguments therefore misses a
violation. The internal function predicate detects that later argument.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf.FunctionControls

open CategoryTheory
open scoped ConstructivePresheaf
open PresheafEventModalities.Controls (vertices)

def xorOperation : NatTrans (FunctorToTypes.prod vertices vertices) vertices where
  app _ := TypeCat.ofHom (fun pair => Bool.xor pair.1 pair.2)
  naturality _ _ _ := rfl

def trueOnly : Subfunctor vertices where
  obj _ := {b | b = true}
  map _ _ held := held

def falseOnly : Subfunctor vertices where
  obj _ := {b | b = false}
  map _ _ held := held

theorem xor_curried_false :
    ((curryFunction xorOperation).app 0 false).app 0 (𝟙 0) false = false := rfl

theorem xor_curried_true :
    ((curryFunction xorOperation).app 0 true).app 0 (𝟙 0) false = true := rfl

theorem curried_parameters_remain_distinct :
    (curryFunction xorOperation).app 0 false ≠ (curryFunction xorOperation).app 0 true := by
  intro same
  have impossible := congrArg (fun value => value.app 0 (𝟙 0) false) same
  cases impossible

theorem xor_respects_predicate :
    trueOnly ≤ preimage (curryFunction xorOperation) (functionPredicate falseOnly trueOnly) := by
  apply (curry_preserves_predicates_iff xorOperation falseOnly trueOnly trueOnly).2
  intro X pair member
  change pair.1 = false ∧ pair.2 = true at member
  change Bool.xor pair.1 pair.2 = true
  rw [member.1, member.2]
  rfl

theorem identity_parameter_rejected :
    (curryFunction xorOperation).app 0 false ∉ (functionPredicate falseOnly trueOnly).obj 0 := by
  intro held
  have impossible : false = true := held 0 (𝟙 0) false rfl
  cases impossible

def futureArguments : Subfunctor vertices where
  obj stage := {b | 0 < stage ∧ b = false}
  map step _ held := ⟨Nat.lt_of_lt_of_le held.1 (leOfHom step), held.2⟩

def identityAt (stage : Nat) : FunctionSection vertices vertices stage where
  app _ _ := TypeCat.ofHom id
  naturality _ _ := rfl

theorem pointwise_function_test_vacuous :
    ∀ b : vertices.obj 0, b ∈ futureArguments.obj 0 →
      (identityAt 0).app 0 (𝟙 0) b ∈ (⊥ : Subfunctor vertices).obj 0 := by
  intro b member
  exact (Nat.not_lt_zero 0 member.1).elim

theorem internal_function_test_rejects :
    identityAt 0 ∉ (functionPredicate futureArguments (⊥ : Subfunctor vertices)).obj 0 := by
  intro held
  exact held 1 (homOfLE (Nat.zero_le 1)) false ⟨by decide, rfl⟩

theorem changing_function_without_naturality_impossible (value : FunctionSection vertices vertices 0) :
    ¬ (value.app 0 (𝟙 0) false = false ∧
      value.app 1 (homOfLE (Nat.zero_le 1)) false = true) := by
  rintro ⟨atZero, atOne⟩
  have naturally := congrArg (fun h : vertices.obj 0 ⟶ vertices.obj 1 => h false)
    (value.naturality (homOfLE (Nat.zero_le 1)) (𝟙 0))
  change value.app 1 (𝟙 0 ≫ homOfLE (Nat.zero_le 1)) false = value.app 0 (𝟙 0) false at naturally
  rw [Category.id_comp, atOne, atZero] at naturally
  cases naturally

end Mettapedia.GSLT.Topos.ConstructivePresheaf.FunctionControls
