import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift

/-!
# Set codes for the existing higher-order set model

The set carrier is the previously constructed universe-shifted carrier code.
Propositions are coded by two distinct sets, and arrows by total functional
graphs. Decoding yields the actual carriers of `ZFSetHenkinInterpretation`,
including its full higher-order function domains, rather than a second model.

The proposition comparison uses classical truth values in this extensional
semantic model. It makes no claim that native identity proofs, source proof
trees, or retained presentations should be identified or erased.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLTypeInterpretation

open ZFSetDependentProducts ZFSetUniverseClosure ZFSetUniverseLift

universe u

/-! ## Actual truth-value codes -/

def falseSet : ZFSet.{u} := ∅
def trueSet : ZFSet.{u} := {∅}
def truthCode : ZFSet.{u} := {falseSet, trueSet}

theorem falseSet_ne_trueSet : falseSet.{u} ≠ trueSet := by
  intro equal
  have member : (∅ : ZFSet.{u}) ∈ trueSet := ZFSet.mem_singleton.mpr rfl
  rw [← equal] at member
  exact ZFSet.mem_irrefl _ member

def falseValue : Elements truthCode.{u} :=
  ⟨falseSet, ZFSet.mem_pair.mpr (Or.inl rfl)⟩

def trueValue : Elements truthCode.{u} :=
  ⟨trueSet, ZFSet.mem_pair.mpr (Or.inr rfl)⟩

def holds (value : Elements truthCode.{u}) : Prop := value.1 = trueSet

noncomputable def truth (p : Prop) : Elements truthCode.{u} := by
  classical
  exact if p then trueValue else falseValue

@[simp] theorem holds_truth (p : Prop) : holds (truth.{u} p) ↔ p := by
  classical
  by_cases hp : p <;> simp [truth, hp, holds, trueValue, falseValue, falseSet_ne_trueSet]

theorem truth_holds (value : Elements truthCode.{u}) : truth (holds value) = value := by
  classical
  apply Subtype.ext
  obtain hfalse | htrue := ZFSet.mem_pair.mp value.2
  · simp [truth, holds, hfalse, falseSet_ne_trueSet, falseValue]
  · simp [truth, holds, htrue, trueValue]

noncomputable def truthEquiv : Elements truthCode.{u + 1} ≃ ULift.{u + 1} Prop where
  toFun := fun value => .up (holds value)
  invFun := fun value => truth value.down
  left_inv := truth_holds
  right_inv := by
    intro value
    apply ULift.ext
    exact propext (holds_truth value.down)

@[simp] theorem truthEquiv_truth (p : Prop) :
    truthEquiv.{u} (truth p) = ULift.up p := by
  apply ULift.ext
  exact propext (holds_truth p)

theorem truthCode_mem {U a : ZFSet.{u}} (closed : Closed U) (ha : a ∈ U) :
    truthCode ∈ U :=
  closed.unorderedPair_mem (closed.empty_mem ha)
    (closed.singleton_mem (closed.empty_mem ha))

/-! ## Recursive type codes and decoding -/

@[reducible] noncomputable def typeCode : Ty Unit → ZFSet.{u + 1}
  | .prop => truthCode
  | .base _ => carrierCode.{u}
  | .arr A B => piSet (typeCode A) (fun _ => typeCode B)

abbrev Value (A : Ty Unit) := Elements (typeCode.{u} A)

/-- Conjugating a function by the domain and codomain equivalences. -/
def functionEquiv {A : Type*} {B : Type*} {C : Type*} {D : Type*}
    (domain : A ≃ B) (codomain : C ≃ D) : (A → C) ≃ (B → D) where
  toFun := fun f x => codomain (f (domain.symm x))
  invFun := fun f x => codomain.symm (f (domain x))
  left_inv := by intro f; funext x; simp
  right_inv := by intro f; funext x; simp

noncomputable def decode : (A : Ty Unit) →
    Value.{u} A ≃ Ty.denote.{0, u + 1} ZFSetHenkinInterpretation.carrier.{u} A
  | .prop => truthEquiv
  | .base _ => carrierEquiv
  | .arr A B => (piEquiv (typeCode A) (fun _ => typeCode B)).trans
      (functionEquiv (decode A) (decode B))

theorem typeCode_mem {U : ZFSet.{u + 1}} (closed : Closed U)
    (carrier_mem : carrierCode.{u} ∈ U) (A : Ty Unit) : typeCode A ∈ U := by
  induction A with
  | prop => exact truthCode_mem closed carrier_mem
  | base => exact carrier_mem
  | arr A B ihA ihB => exact closed.piSet_mem ihA _ (fun _ _ => ihB)

/-! ## Graph lambda and application, independently of HOL denotation -/

noncomputable def lam {A B : Ty Unit} (body : Value.{u} A → Value B) : Value (A ⇒ B) :=
  encodeFunction (a := typeCode A) (b := fun _ => typeCode B) body

noncomputable def app {A B : Ty Unit} (function : Value.{u} (A ⇒ B))
    (argument : Value A) : Value B :=
  graphValue (a := typeCode A) (b := fun _ => typeCode B) function argument

@[simp] theorem app_lam {A B : Ty Unit} (body : Value.{u} A → Value B)
    (argument : Value A) : app (lam body) argument = body argument :=
  congrFun (decode_encode_function (a := typeCode A) (b := fun _ => typeCode B) body) argument

theorem lam_eta {A B : Ty Unit} (function : Value.{u} (A ⇒ B)) :
    lam (fun argument => app function argument) = function :=
  encode_decode_function (a := typeCode A) (b := fun _ => typeCode B) function

theorem decode_app {A B : Ty Unit} (function : Value.{u} (A ⇒ B))
    (argument : Value A) :
    decode B (app function argument) = decode (A ⇒ B) function (decode A argument) := by
  change decode B (graphValue function argument) =
    decode B (graphValue function ((decode A).symm (decode A argument)))
  rw [Equiv.symm_apply_apply]

theorem decode_lam {A B : Ty Unit} (body : Value.{u} A → Value B) :
    decode (A ⇒ B) (lam body) =
      fun x => decode B (body ((decode A).symm x)) := by
  funext x
  change decode B (app (lam body) ((decode A).symm x)) = _
  rw [app_lam]

theorem decode_truth (p : Prop) : decode .prop (truth.{u + 1} p) = ULift.up p :=
  truthEquiv_truth p

/-- Equality of graph codes is exactly the already extensional equality
of values in the full-domain set/HOL model. -/
theorem equality_decode {A : Ty Unit} (left right : Value.{u} A) :
    left = right ↔ ZFSetHenkinInterpretation.model.Eqv A
      (decode A left) (decode A right) := by
  constructor
  · rintro rfl
    exact ZFSetHenkinInterpretation.model.eqv_refl
      (ZFSetHenkinInterpretation.fullDomains A _)
  · intro equal
    apply (decode A).injective
    exact ZFSetHenkinInterpretation.model.eq_of_eqv_of_fullDomains
      ZFSetHenkinInterpretation.fullDomains equal

/-! ## Nontrivial controls -/

theorem truth_false_ne_truth_true : truth.{u} False ≠ truth True := by
  intro equal
  have contradiction := (holds_truth False).mp
    (equal ▸ (holds_truth True).mpr trivial)
  exact contradiction

noncomputable def negation : Value.{u} (.prop ⇒ .prop) := lam (fun p => truth (¬ holds p))

theorem negation_true : app negation.{u} (truth True) = truth False := by
  rw [negation, app_lam]
  congr 1
  exact propext (by simp)

theorem negation_false : app negation.{u} (truth False) = truth True := by
  rw [negation, app_lam]
  congr 1
  exact propext (by simp)

theorem negation_not_identity : negation.{u} ≠ lam (fun p : Value .prop => p) := by
  intro equal
  have valueEqual := congrArg (fun f => app (A := .prop) (B := .prop) f (truth True)) equal
  rw [negation_true, app_lam] at valueEqual
  exact truth_false_ne_truth_true valueEqual

#print axioms truthEquiv
#print axioms typeCode_mem
#print axioms decode
#print axioms app_lam
#print axioms lam_eta
#print axioms decode_app
#print axioms decode_lam
#print axioms equality_decode
#print axioms truth_false_ne_truth_true
#print axioms negation_not_identity

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLTypeInterpretation
