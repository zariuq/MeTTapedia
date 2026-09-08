import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveHOLInterface
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant

/-!
# The call-guard HOL invariant represented by a declared logical signature

The source formulas and proof are the existing intrinsic HOL invariant for
the specified compiler. An explicit declaration signature represents its
proposition carrier, implication, universal quantification and three operational
symbols. Quantification uses an opaque type-indexed operator applied to a
lambda; it is not identified with dependent-product formation.

The representation has a formation-sensitive derivation. Its logical validity
is a separate fact in the independently supplied call-guard Henkin model.
Changing that model's predicate preserves all formation and the same HOL
derivation but refutes validity. No HOL proof-as-inhabitant translation, native
Prime logic selection, or complete CeTTa correctness theorem is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveHOLInvariant

open Presentation Presentation.Declaration Presentation.FormationSensitive
open FormationSensitiveHOLInterface Mettapedia.Logic
open Mettapedia.Languages.MeTTa.PeTTa
open MainlineCallGuardHOLInvariant

def types : TypeInterpretation Unit where
  proposition := .const `HOLInterface.prop
  base := fun _ => .head .legacyGround

/-- The displayed declaration type takes a type and then a predicate on it. -/
def universalType : Tower.Tm 0 :=
  .pi (sortTm Tower.zero)
    (.pi (.pi (.var 0) (.const `HOLInterface.prop)) (.const `HOLInterface.prop))

def symbolName : {type : HOL.Ty Unit} → Constant type → DeclName
  | _, .step => `HOLInterface.step
  | _, .sameResult => `HOLInterface.sameResult
  | _, .property => `HOLInterface.property

/-- The interface is an ordinary existing declaration signature. All entries
are opaque; no equations equate logical truth with target inhabitation. -/
def declarations : Signature Tower.Head := Signature.ofList
  [(`HOLInterface.prop, ⟨sortTm Tower.zero, none⟩),
   (`HOLInterface.implication, ⟨typeAt types 0 (.arr .prop (.arr .prop .prop)), none⟩),
   (`HOLInterface.universal, ⟨universalType, none⟩),
   (`HOLInterface.step, ⟨typeAt types 0 (.arr stateType (.arr stateType .prop)), none⟩),
   (`HOLInterface.sameResult, ⟨typeAt types 0 (.arr stateType (.arr stateType .prop)), none⟩),
   (`HOLInterface.property, ⟨typeAt types 0 (.arr stateType .prop), none⟩)]

def rules : Rules Tower.Head := extendRules Tower.rules declarations

private theorem proposition_lookup :
    rules.constantType `HOLInterface.prop = some (sortTm Tower.zero) := by decide

private theorem implication_lookup : rules.constantType `HOLInterface.implication =
    some (typeAt types 0 (.arr .prop (.arr .prop .prop))) := by decide

private theorem universal_lookup :
    rules.constantType `HOLInterface.universal = some universalType := by decide

private theorem symbol_lookup {type : HOL.Ty Unit} (symbol : Constant type) :
    rules.constantType (symbolName symbol) = some (typeAt types 0 type) := by
  cases symbol <;> decide

theorem proposition_formed {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (.const `HOLInterface.prop) (sortTm Tower.zero) :=
  .const proposition_lookup (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

theorem simple_type_formed (type : HOL.Ty Unit) {n : Nat} (gamma : Tower.Ctx n) :
    Typing rules gamma (typeAt types n type) (sortTm Tower.zero) :=
  typeAt_formed_of_atoms declarations types (proposition_formed .nil)
    (fun _ => .headType .legacyGround) type gamma

private theorem pi_zero {n : Nat} {gamma : Tower.Ctx n}
    {a : Tower.Tm n} {b : Tower.Tm (n + 1)}
    (ha : Typing rules gamma a (sortTm Tower.zero))
    (hb : Typing rules (.snoc gamma a) b (sortTm Tower.zero)) :
    Typing rules gamma (.pi a b) (sortTm Tower.zero) := by
  apply Typing.cumul (.piForm ha (.sort Tower.zero) hb (.sort Tower.zero)
    (.sorts Tower.zero Tower.zero))
  intro valuation
  simp [LevelExpr.eval, Tower.zero]

/-- The type-indexed operator's own dependent declaration is independently formed. -/
theorem universal_type_formed : Typing rules .nil universalType
    (sortTm (.max (.succ Tower.zero) Tower.zero)) := by
  refine Typing.piForm (R := rules) (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))
    ?_ (.sort Tower.zero) (.sorts (.succ Tower.zero) Tower.zero)
  apply pi_zero
  · exact pi_zero (.var 0) (proposition_formed _)
  · exact proposition_formed _

def universal (type : HOL.Ty Unit) : Tower.Tm 0 :=
  .app (.const `HOLInterface.universal) (typeAt types 0 type)

theorem universal_typed (type : HOL.Ty Unit) :
    Typing rules .nil (universal type) (typeAt types 0 (.arr (.arr type .prop) .prop)) := by
  have symbol : Typing rules .nil (.const `HOLInterface.universal) universalType :=
    .const universal_lookup universal_type_formed (.sort (.max (.succ Tower.zero) Tower.zero))
  have applied := Typing.appElim symbol (simple_type_formed type .nil)
  simpa only [universal, universalType, typeAt, types, liftClosed, Presentation.rename,
    inst0, Presentation.subst, subst0, consSub, liftSub, Fin.cases_zero] using applied

def signature : LogicalSignature Unit Constant where
  declarations := declarations
  types := types
  proposition_formed := proposition_formed .nil
  base_formed := fun _ => .headType .legacyGround
  constant := fun symbol => .const (symbolName symbol)
  constant_typed := by
    intro type symbol
    simpa only [rules, liftClosed, typeAt_rename] using
      Typing.const (Γ := .nil) (symbol_lookup symbol)
        (simple_type_formed type .nil) (.sort Tower.zero)
  implication := .const `HOLInterface.implication
  implication_typed := .const implication_lookup
    (simple_type_formed (.arr .prop (.arr .prop .prop)) .nil) (.sort Tower.zero)
  universal := universal
  universal_typed := universal_typed

/-- An independently displayed target formula, including both binder indices. -/
def rawConclusion : Tower.Tm 0 :=
  .app (.app (.const `HOLInterface.universal) (.head .legacyGround))
    (.lam (.app (.app (.const `HOLInterface.universal) (.head .legacyGround))
      (.lam (.app (.app (.const `HOLInterface.implication)
        (.app (.app (.const `HOLInterface.step) (.var 1)) (.var 0)))
        (.app (.app (.const `HOLInterface.implication)
          (.app (.const `HOLInterface.property) (.var 1)))
          (.app (.const `HOLInterface.property) (.var 0)))))))

/-- Exact source-to-target syntax comparison, not an alias of the source formula. -/
theorem conclusion_represented : represent signature conclusion = some rawConclusion := rfl

theorem conclusion_formed : Typing rules .nil rawConclusion (.const `HOLInterface.prop) :=
  represent_typed signature conclusion conclusion_represented

/-- The same represented formula is independently valid for every predicate
on reference compilation results, using the existing actual HOL derivation. -/
theorem result_predicate_valid
    (observe : MainlineCallGuardPlan.CompilationResult → Prop) :
    HOL.HenkinModel.models (model (fun state => observe state.denote)) conclusion :=
  HOL.Soundness.derivation_sound preservation_derived
    (M := model (fun state => observe state.denote)) (ρ := emptyValuation _)
    (emptyValuation_admissible _)
    (resultPredicate_satisfies_assumptions observe)

/-- Formation of the represented proposition is not a proof of its meaning.
The existing compiler step refutes the same formula under a changed predicate. -/
theorem formation_not_validity :
    Typing rules .nil rawConclusion (.const `HOLInterface.prop) ∧
      ¬ HOL.HenkinModel.models (model runningPredicate) conclusion :=
  ⟨conclusion_formed, altered_interpretation_not_valid⟩

/-- Equality is deliberately outside the current logical interface. -/
theorem equality_not_represented :
    represent signature (HOL.Term.eq (HOL.Term.const Constant.property)
      (HOL.Term.const Constant.property) : HOL.ClosedFormula Constant) = none := rfl

/-! ## Higher-order specialization through both binding routes -/

def predicateType : HOL.Ty Unit := .arr stateType .prop

def functionArgument : HOL.Term Constant [] predicateType :=
  .lam (.app (.const .property) (.var .vz))

/-- This formula is open in a function-valued variable, then binds a state. -/
def predicateBody : HOL.Formula Constant [predicateType] :=
  .all (.imp (.app (.var (.vs .vz)) (.var .vz))
    (.app (.var (.vs .vz)) (.var .vz)))

def rawFunctionArgument : Tower.Tm 0 :=
  .lam (.app (.const `HOLInterface.property) (.var 0))

def rawPredicateBody : Tower.Tm 1 :=
  .app (.app (.const `HOLInterface.universal) (.head .legacyGround))
    (.lam (.app (.app (.const `HOLInterface.implication) (.app (.var 1) (.var 0)))
      (.app (.var 1) (.var 0))))

theorem function_argument_represented :
    represent signature functionArgument = some rawFunctionArgument := rfl

theorem predicate_body_represented :
    represent signature predicateBody = some rawPredicateBody := rfl

private theorem specialization_components {type : HOL.Ty Unit}
    (index : HOL.Var [predicateType] type) :
    represent signature (HOL.Subst.single functionArgument index) =
      some (subst0 rawFunctionArgument (variableIndex index)) := by
  cases index with
  | vz => exact function_argument_represented
  | vs prior => nomatch prior

/-- A function-valued argument is substituted beneath the state quantifier.
The native substitution and intrinsic substitution routes have the same
representation and the source Henkin denotation satisfies substitution. -/
theorem higher_order_specialization
    (henkin : HOL.HenkinModel.{0, 0, 0} Unit Constant)
    (valuation : HOL.HenkinModel.Valuation henkin []) :
    represent signature (HOL.instantiate functionArgument predicateBody) =
      some (inst0 rawFunctionArgument rawPredicateBody) ∧
      Typing rules .nil (inst0 rawFunctionArgument rawPredicateBody)
        (.const `HOLInterface.prop) ∧
      henkin.denote (HOL.instantiate functionArgument predicateBody) valuation =
        henkin.denote predicateBody
          (HOL.Soundness.substVal henkin (HOL.Subst.single functionArgument) valuation) :=
  substitution_interface signature (HOL.Subst.single functionArgument)
    (subst0 rawFunctionArgument) specialization_components predicateBody
    predicate_body_represented henkin valuation

/-- The same interface supports quantification over predicates, not merely
first-order state quantification. The type argument is itself an arrow type. -/
def rawHigherOrderQuantification : Tower.Tm 0 :=
  .app (.app (.const `HOLInterface.universal)
    (.pi (.head .legacyGround) (.const `HOLInterface.prop)))
    (.lam rawPredicateBody)

theorem higher_order_quantifier_represented :
    represent signature (HOL.Term.all predicateBody) = some rawHigherOrderQuantification := rfl

theorem higher_order_quantifier_formed :
    Typing rules .nil rawHigherOrderQuantification (.const `HOLInterface.prop) :=
  represent_typed signature _ higher_order_quantifier_represented

/-- The concrete signature does not identify propositions with the state type. -/
theorem proposition_state_distinct :
    typeAt types 0 (.prop : HOL.Ty Unit) ≠ typeAt types 0 stateType := by decide

#print axioms universal_type_formed
#print axioms universal_typed
#print axioms conclusion_formed
#print axioms result_predicate_valid
#print axioms formation_not_validity
#print axioms higher_order_specialization
#print axioms higher_order_quantifier_formed

end FormationSensitiveHOLInvariant
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
