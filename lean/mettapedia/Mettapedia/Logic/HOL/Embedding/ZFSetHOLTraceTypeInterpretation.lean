import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTypeInterpretation

/-!
# Uniform trace codes for the existing HOL simple types

The base set carrier and truth-value code are unchanged. Every arrow uses
the actual Aczel trace product, recursively even when its domain or codomain
is itself a function type. Decoding lands in the same existing Henkin model.
The earlier graph codes remain separate and are compared by equivalences,
not identified as sets. This extensional model does not erase native proof
identity or constitute an interpretation of every native dependent rule.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTypeInterpretation

open ZFSetDependentProducts ZFSetTraceProducts ZFSetUniverseClosure ZFSetUniverseLift
open ZFSetHOLTypeInterpretation (truthCode truth holds truthEquiv functionEquiv
  truthCode_mem truthEquiv_truth holds_truth truth_false_ne_truth_true)

universe u

@[reducible] noncomputable def typeCode : Ty Unit → ZFSet.{u + 1}
  | .prop => truthCode
  | .base _ => carrierCode.{u}
  | .arr A B => tracePiSet (typeCode A) (fun _ => typeCode B)

abbrev Value (A : Ty Unit) := Elements (typeCode.{u} A)

noncomputable def decode : (A : Ty Unit) →
    Value.{u} A ≃ Ty.denote.{0, u + 1} ZFSetHenkinInterpretation.carrier.{u} A
  | .prop => truthEquiv
  | .base _ => carrierEquiv
  | .arr A B => (tracePiEquiv (typeCode A) (fun _ => typeCode B)).trans
      (functionEquiv (decode A) (decode B))

theorem typeCode_mem {U : ZFSet.{u + 1}} (closed : Closed U)
    (carrier_mem : carrierCode.{u} ∈ U) (A : Ty Unit) : typeCode A ∈ U := by
  induction A with
  | prop => exact truthCode_mem closed carrier_mem
  | base => exact carrier_mem
  | arr A B ihA ihB => exact closed.tracePiSet_mem ihA _ (fun _ _ => ihB)

/-! ## Actual trace lambda/application and their typed computations -/

noncomputable def lam {A B : Ty Unit} (body : Value.{u} A → Value B) : Value (A ⇒ B) :=
  traceEncode (a := typeCode A) (b := fun _ => typeCode B) body

noncomputable def app {A B : Ty Unit} (function : Value.{u} (A ⇒ B))
    (argument : Value A) : Value B :=
  traceValue (a := typeCode A) (b := fun _ => typeCode B) function argument

@[simp] theorem app_lam {A B : Ty Unit} (body : Value.{u} A → Value B)
    (argument : Value A) : app (lam body) argument = body argument :=
  congrFun (trace_beta (a := typeCode A) (b := fun _ => typeCode B) body) argument

theorem lam_eta {A B : Ty Unit} (function : Value.{u} (A ⇒ B)) :
    lam (fun argument => app function argument) = function :=
  trace_eta (a := typeCode A) (b := fun _ => typeCode B) function

theorem decode_app {A B : Ty Unit} (function : Value.{u} (A ⇒ B))
    (argument : Value A) :
    decode B (app function argument) = decode (A ⇒ B) function (decode A argument) := by
  change decode B (traceValue function argument) =
    decode B (traceValue function ((decode A).symm (decode A argument)))
  rw [Equiv.symm_apply_apply]

theorem decode_lam {A B : Ty Unit} (body : Value.{u} A → Value B) :
    decode (A ⇒ B) (lam body) =
      fun x => decode B (body ((decode A).symm x)) := by
  funext x
  change decode B (app (lam body) ((decode A).symm x)) = _
  rw [app_lam]

theorem decode_truth (p : Prop) : decode .prop (truth.{u + 1} p) = ULift.up p :=
  truthEquiv_truth p

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

/-! ## Comparison with the distinct existing graph representation -/

noncomputable def graphEquiv (A : Ty Unit) : Value.{u} A ≃ ZFSetHOLTypeInterpretation.Value.{u} A :=
  (decode A).trans (ZFSetHOLTypeInterpretation.decode A).symm

theorem graphEquiv_decode (A : Ty Unit) (value : Value.{u} A) :
    ZFSetHOLTypeInterpretation.decode A (graphEquiv A value) = decode A value :=
  Equiv.apply_symm_apply (ZFSetHOLTypeInterpretation.decode A) (decode A value)

theorem graphEquiv_prop (p : Value.{u} .prop) : graphEquiv .prop p = p :=
  Equiv.symm_apply_apply truthEquiv p

theorem graphEquiv_base (x : Value.{u} (.base ())) : graphEquiv (.base ()) x = x :=
  Equiv.symm_apply_apply carrierEquiv x

theorem graphEquiv_app {A B : Ty Unit} (function : Value.{u} (A ⇒ B))
    (argument : Value A) : graphEquiv B (app function argument) =
      ZFSetHOLTypeInterpretation.app (graphEquiv (A ⇒ B) function) (graphEquiv A argument) := by
  apply (ZFSetHOLTypeInterpretation.decode B).injective
  rw [graphEquiv_decode, decode_app, ZFSetHOLTypeInterpretation.decode_app,
    graphEquiv_decode, graphEquiv_decode]

theorem graphEquiv_lam {A B : Ty Unit} (body : Value.{u} A → Value B) :
    graphEquiv (A ⇒ B) (lam body) =
      ZFSetHOLTypeInterpretation.lam (fun x => graphEquiv B (body ((graphEquiv A).symm x))) := by
  apply (ZFSetHOLTypeInterpretation.decode (A ⇒ B)).injective
  rw [graphEquiv_decode, decode_lam, ZFSetHOLTypeInterpretation.decode_lam]
  funext x
  rw [graphEquiv_decode]
  congr 2
  change (decode A).symm x =
    (decode A).symm (ZFSetHOLTypeInterpretation.decode A
      ((ZFSetHOLTypeInterpretation.decode A).symm x))
  rw [Equiv.apply_symm_apply]

/-! ## Higher-order controls and a literal code inequality -/

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

noncomputable def twice : Value.{u} ((.prop ⇒ .prop) ⇒ (.prop ⇒ .prop)) :=
  lam (fun f => lam (fun p => app f (app f p)))

theorem twice_negation_true : app (app twice.{u} negation) (truth True) = truth True := by
  rw [twice, app_lam, app_lam, negation_true, negation_false]

theorem empty_mem_trace_arrow : (∅ : ZFSet.{u + 1}) ∈ typeCode (.prop ⇒ .prop) :=
  mem_tracePiSet.mpr ⟨graph truthCode (fun _ => ∅),
    graph_mem_piSet (fun _ _ => ZFSet.mem_pair.mpr (Or.inl rfl)),
    traceLam_graph_empty truthCode⟩

theorem empty_not_mem_graph_arrow :
    (∅ : ZFSet.{u + 1}) ∉ ZFSetHOLTypeInterpretation.typeCode (.prop ⇒ .prop) := by
  intro member
  obtain ⟨value, impossible, _⟩ :=
    (mem_piSet.mp member).1.2 ∅ (ZFSet.mem_pair.mpr (Or.inl rfl))
  exact ZFSet.notMem_empty _ impossible

/-- Equivalent full function carriers have different actual set codes. -/
theorem trace_arrow_code_ne_graph_arrow_code :
    typeCode.{u} (.prop ⇒ .prop) ≠ ZFSetHOLTypeInterpretation.typeCode.{u} (.prop ⇒ .prop) := by
  intro equal
  exact empty_not_mem_graph_arrow (equal ▸ empty_mem_trace_arrow)

#print axioms decode
#print axioms typeCode_mem
#print axioms app_lam
#print axioms lam_eta
#print axioms decode_app
#print axioms decode_lam
#print axioms equality_decode
#print axioms graphEquiv
#print axioms graphEquiv_app
#print axioms graphEquiv_lam
#print axioms negation_not_identity
#print axioms twice_negation_true
#print axioms trace_arrow_code_ne_graph_arrow_code

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTypeInterpretation
