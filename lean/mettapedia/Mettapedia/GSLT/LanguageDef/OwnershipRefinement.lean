import Mettapedia.GSLT.LanguageDef.OwnershipAdmission

/-!
# Nullable result refinement at ownership interfaces

This first refinement preserves argument requirements, effects, families,
reference origins and record postconditions. A nonnull result may implement a
nullable result contract. The existing call transition and return predicate
give its operational meaning; general C execution is outside this model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Ownership.Refinement

open Mettapedia.Machines.CMemory.Borrowing

def nullabilityLe (provided expected : Bool) : Bool := !provided || expected

theorem nullabilityLe_refl (value : Bool) : nullabilityLe value value = true := by
  cases value <;> rfl

theorem nullabilityLe_sound {provided expected : Bool}
    (accepted : nullabilityLe provided expected = true) :
    provided = true → expected = true := by
  cases provided <;> cases expected <;> simp_all [nullabilityLe]

theorem nullabilityLe_trans {a b c : Bool}
    (ab : nullabilityLe a b = true) (bc : nullabilityLe b c = true) :
    nullabilityLe a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [nullabilityLe]

def shapeCore : ReturnShape → ReturnShape
  | .static _ => .static false
  | .borrowed input offset count writing _ => .borrowed input offset count writing false
  | .owned family _ => .owned family false
  | shape => shape

def shapeNullable : ReturnShape → Bool
  | .static nullable | .borrowed _ _ _ _ nullable | .owned _ nullable => nullable
  | _ => false

def shapeRefines (provided expected : ReturnShape) : Bool :=
  decide (shapeCore provided = shapeCore expected) &&
    nullabilityLe (shapeNullable provided) (shapeNullable expected)

theorem shapeRefines_refl (shape : ReturnShape) : shapeRefines shape shape = true := by
  simp [shapeRefines, nullabilityLe_refl]

theorem shapeRefines_trans {a b c : ReturnShape}
    (ab : shapeRefines a b = true) (bc : shapeRefines b c = true) :
    shapeRefines a c = true := by
  simp only [shapeRefines, Bool.and_eq_true, decide_eq_true_eq] at ab bc ⊢
  exact ⟨ab.1.trans bc.1, nullabilityLe_trans ab.2 bc.2⟩

def resultCore : ResultSpec → ResultSpec
  | .static _ => .static false
  | .borrowed region writing _ => .borrowed region writing false
  | .owned family _ => .owned family false
  | result => result

def resultNullable : ResultSpec → Bool
  | .static nullable | .borrowed _ _ nullable | .owned _ nullable => nullable
  | _ => false

def resultRefines (provided expected : ResultSpec) : Bool :=
  decide (resultCore provided = resultCore expected) &&
    nullabilityLe (resultNullable provided) (resultNullable expected)

theorem resultRefines_refl (result : ResultSpec) : resultRefines result result = true := by
  simp [resultRefines, nullabilityLe_refl]

theorem resultRefines_trans {a b c : ResultSpec}
    (ab : resultRefines a b = true) (bc : resultRefines b c = true) :
    resultRefines a c = true := by
  simp only [resultRefines, Bool.and_eq_true, decide_eq_true_eq] at ab bc ⊢
  exact ⟨ab.1.trans bc.1, nullabilityLe_trans ab.2 bc.2⟩

theorem returnAllowed_decompose (result : ResultSpec) (state : State) :
    returnAllowed result state =
      (returnAllowed (resultCore result) state ||
        (resultNullable result && clean state && nullOnly state)) := by
  cases result with
  | value => simp [resultCore, resultNullable]
  | viewed region writing => simp [resultCore, resultNullable]
  | static nullable =>
      cases nullable <;> cases same : clean state <;>
        simp [resultCore, resultNullable, returnAllowed, same, Bool.or_comm]
  | borrowed region writing nullable =>
      cases nullable <;> cases same : clean state <;>
        simp [resultCore, resultNullable, returnAllowed, same, Bool.or_comm]
  | owned family nullable =>
      cases nullable <;> cases same : clean state <;>
        simp [resultCore, resultNullable, returnAllowed, same, Bool.or_comm]

theorem resultRefines_preserves_return {provided expected : ResultSpec}
    (accepted : resultRefines provided expected = true) (state : State)
    (returned : returnAllowed provided state = true) :
    returnAllowed expected state = true := by
  simp only [resultRefines, Bool.and_eq_true, decide_eq_true_eq] at accepted
  rw [returnAllowed_decompose] at returned ⊢
  rcases Bool.or_eq_true_iff.mp returned with core | nullable
  · exact Bool.or_eq_true_iff.mpr (Or.inl (accepted.1 ▸ core))
  · have parts := Bool.and_eq_true_iff.mp nullable
    have flags := Bool.and_eq_true_iff.mp parts.1
    exact Bool.or_eq_true_iff.mpr (Or.inr (Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨nullabilityLe_sound accepted.2 flags.1, flags.2⟩, parts.2⟩))

theorem instantiate_core (inputs : List Nat) (shape : ReturnShape) :
    (instantiateResult inputs shape).map resultCore = instantiateResult inputs (shapeCore shape) := by
  cases shape with
  | value => rfl
  | static nullable => rfl
  | owned family nullable => rfl
  | borrowed input offset count writing nullable =>
      cases found : inputs[input]? <;> simp [instantiateResult, shapeCore, resultCore, found]
  | viewed input offset count writing =>
      cases found : inputs[input]? <;> simp [instantiateResult, shapeCore, resultCore, found]
  | wholeViewed input writing =>
      cases found : inputs[input]? <;> simp [instantiateResult, shapeCore, resultCore, found]

theorem instantiate_nullable {inputs : List Nat} {shape : ReturnShape} {result : ResultSpec}
    (instantiated : instantiateResult inputs shape = some result) :
    resultNullable result = shapeNullable shape := by
  cases shape with
  | value => cases Option.some.inj instantiated; rfl
  | static nullable => cases Option.some.inj instantiated; rfl
  | owned family nullable => cases Option.some.inj instantiated; rfl
  | borrowed input offset count writing nullable =>
      obtain ⟨root, _, same⟩ := Option.bind_eq_some_iff.mp instantiated
      cases Option.some.inj same
      rfl
  | viewed input offset count writing =>
      obtain ⟨root, _, same⟩ := Option.bind_eq_some_iff.mp instantiated
      cases Option.some.inj same
      rfl
  | wholeViewed input writing =>
      obtain ⟨root, _, same⟩ := Option.bind_eq_some_iff.mp instantiated
      cases Option.some.inj same
      rfl

theorem instantiate_refinement {inputs : List Nat} {provided expected : ReturnShape}
    {result : ResultSpec} (accepted : shapeRefines provided expected = true)
    (instantiated : instantiateResult inputs provided = some result) :
    ∃ other, instantiateResult inputs expected = some other ∧ resultRefines result other = true := by
  simp only [shapeRefines, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have same := (instantiate_core inputs provided).trans
    ((congrArg (instantiateResult inputs) accepted.1).trans (instantiate_core inputs expected).symm)
  rw [instantiated] at same
  cases other : instantiateResult inputs expected with
  | none => simp [other] at same
  | some target =>
      refine ⟨target, rfl, ?_⟩
      simp only [other, Option.map_some, Option.some.injEq] at same
      simp only [resultRefines, same, decide_true, Bool.true_and]
      rw [instantiate_nullable instantiated, instantiate_nullable other]
      exact accepted.2

def signatureRefines (provided expected : Signature) : Bool :=
  decide (provided.parameters = expected.parameters) &&
    decide (provided.variadicRead = expected.variadicRead) &&
    decide (provided.fields = expected.fields) && decide (provided.records = expected.records) &&
    shapeRefines provided.result expected.result

theorem signatureRefines_refl (signature : Signature) : signatureRefines signature signature = true := by
  simp [signatureRefines, shapeRefines_refl]

theorem signatureRefines_parameters {provided expected : Signature}
    (accepted : signatureRefines provided expected = true) :
    provided.parameters = expected.parameters ∧ provided.variadicRead = expected.variadicRead := by
  simp only [signatureRefines, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1.1.1.1, accepted.1.1.1.2⟩

theorem signatureRefines_result {provided expected : Signature}
    (accepted : signatureRefines provided expected = true) :
    shapeRefines provided.result expected.result = true := by
  simp only [signatureRefines, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact accepted.2

theorem signatureRefines_trans {a b c : Signature}
    (ab : signatureRefines a b = true) (bc : signatureRefines b c = true) :
    signatureRefines a c = true := by
  simp only [signatureRefines, Bool.and_eq_true, decide_eq_true_eq] at ab bc ⊢
  rcases ab with ⟨⟨⟨⟨parametersAB, variadicAB⟩, fieldsAB⟩, recordsAB⟩, resultAB⟩
  rcases bc with ⟨⟨⟨⟨parametersBC, variadicBC⟩, fieldsBC⟩, recordsBC⟩, resultBC⟩
  exact ⟨⟨⟨⟨parametersAB.trans parametersBC, variadicAB.trans variadicBC⟩,
    fieldsAB.trans fieldsBC⟩, recordsAB.trans recordsBC⟩, shapeRefines_trans resultAB resultBC⟩

theorem signatureRefines_invocation {provided expected : Signature}
    (accepted : signatureRefines provided expected = true) (state : State) (arguments : List Argument) :
    invoke provided state arguments = invoke expected state arguments := by
  obtain ⟨parameters, variadic⟩ := signatureRefines_parameters accepted
  simp only [invoke, parameters, variadic]

namespace Controls

private def required : Signature := ⟨[.borrowed 8 false], false, .borrowed 0 0 8 false false, [], []⟩
private def optional : Signature := { required with result := .borrowed 0 0 8 false true }

theorem nonnull_implements_nullable : signatureRefines required optional = true := by decide
theorem nullable_does_not_implement_nonnull : signatureRefines optional required = false := by decide
theorem different_origin_refused :
    signatureRefines { required with result := .static false } optional = false := by decide
theorem different_extent_refused :
    signatureRefines { required with result := .borrowed 0 0 4 false false } optional = false := by decide
theorem stronger_write_requirement_refused :
    signatureRefines { required with parameters := [.borrowed 8 true] } optional = false := by decide
theorem different_family_refused :
    shapeRefines (.owned 1 false) (.owned 2 true) = false := by decide

end Controls

#print axioms resultRefines_preserves_return
#print axioms instantiate_refinement
#print axioms signatureRefines_invocation

end Mettapedia.GSLT.LanguageDef.Ownership.Refinement
