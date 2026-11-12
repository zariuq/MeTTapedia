import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RhoPast
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Narrowings
import Mettapedia.OSLF.Syntax.RhoCommunicationEncoding

/-!
# The step's OSLF types against rho's native types

Rho is presented by a binding signature in which the input former binds the name it receives
(`RhoSchema`), with its communication schema; the step hosts it as the channel-communication
fragment, and reading a heated store as one process (`FragmentsOfTheStep.NarrowingToRho.narrow`) is
an onto functional bisimulation.

**The generated logic** (`Formula`): atoms, Boolean connectives, OSLF's possibility, successor
necessity and predecessor necessity, interpreted on any reduction system through OSLF's derived
modalities on its span (`interp`).

* **Every formula pulls back, with the past read over fibres** (`pb_interp`): along any onto
  functional bisimulation `h`, the pullback of a formula's meaning is its meaning on the source with
  atoms pulled back and predecessor necessity taken over the fibres of `h` (`interpFibre`). For
  formulas without the past the fibres play no role (`pb_interp_of_pastFree`).
* **Rho** (`rho_native_types`, `rho_native_types_pastFree`): every native type of rho built in the
  generated logic, over arbitrary predicates on processes, binder-sensitive ones included, is the
  pullback of the step's type of the same formula; the past is taken over the heating class.

**Where they diverge.**

* **The past** (`past_diverges`): read at the state alone, predecessor necessity on the step is not
  the pullback of rho's; "no predecessor" holds of a heated store with no knowledge and fails of its
  process (`LogicOverTheStep.RhoPast.rho_predecessorBox_fails`).
* **History** (`knowledge_not_native`): a predicate on heated stores is the pullback of a predicate on
  processes exactly when it is constant on the fibres of the narrowing (`eq_pb_iff_fibreInvariant`).
  "The knowledge is empty" is not: two heated stores with one process, one with and one without
  knowledge. The step's types see history; rho's native types cannot.
* **The authored presentation** (`authored_intrinsic_divergence`): the narrowing reaches the intrinsic
  binding-signature presentation. The authored MeTTa-IL rho (`rhoCalc`) contracts the round trip
  `*@q` while substituting the received name, so on a closed communication the two reducts are not
  structurally congruent and a structural observation tells them apart, while every observation
  respecting residual equivalence agrees on them
  (`Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding`). The divergence is in the semantics of
  substituting for the bound name, not in the modal logic.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.RhoNativeTypes

open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open LogicOverTheStep.ModalComparison LogicOverTheStep.RhoPast

universe u v w

/-! ## The generated logic -/

/-- **The formulas of the generated logic.** -/
inductive Formula (Atom : Type u) : Type u
  | atom (a : Atom)
  | neg (φ : Formula Atom)
  | and (φ ψ : Formula Atom)
  | or (φ ψ : Formula Atom)
  | diamond (φ : Formula Atom)
  | forwardBox (φ : Formula Atom)
  | past (φ : Formula Atom)

namespace Formula

variable {Atom : Type u}

/-- The formulas without predecessor necessity. -/
inductive PastFree : Formula Atom → Prop
  | atom (a : Atom) : PastFree (atom a)
  | neg {φ : Formula Atom} : PastFree φ → PastFree (neg φ)
  | and {φ ψ : Formula Atom} : PastFree φ → PastFree ψ → PastFree (and φ ψ)
  | or {φ ψ : Formula Atom} : PastFree φ → PastFree ψ → PastFree (or φ ψ)
  | diamond {φ : Formula Atom} : PastFree φ → PastFree (diamond φ)
  | forwardBox {φ : Formula Atom} : PastFree φ → PastFree (forwardBox φ)

variable {X : Type v} {Y : Type w}

/-- **Meaning on a reduction system**: OSLF's derived modalities on its span. -/
def interp (step : X → X → Prop) (val : Atom → X → Prop) : Formula Atom → X → Prop
  | atom a => val a
  | neg φ => (interp step val φ)ᶜ
  | and φ ψ => fun x => interp step val φ x ∧ interp step val ψ x
  | or φ ψ => fun x => interp step val φ x ∨ interp step val ψ x
  | diamond φ => derivedDiamond (span step) (interp step val φ)
  | forwardBox φ => derivedForwardBox (span step) (interp step val φ)
  | past φ => derivedBox (span step) (interp step val φ)

/-- **Meaning on a system observed through a map**, with predecessor necessity over the map's fibres. -/
def interpFibre (step : X → X → Prop) (h : X → Y) (val : Atom → X → Prop) : Formula Atom → X → Prop
  | atom a => val a
  | neg φ => (interpFibre step h val φ)ᶜ
  | and φ ψ => fun x => interpFibre step h val φ x ∧ interpFibre step h val ψ x
  | or φ ψ => fun x => interpFibre step h val φ x ∨ interpFibre step h val ψ x
  | diamond φ => derivedDiamond (span step) (interpFibre step h val φ)
  | forwardBox φ => derivedForwardBox (span step) (interpFibre step h val φ)
  | past φ => fibrePredecessorBox step h (interpFibre step h val φ)

/-- **Every formula pulls back along an onto functional bisimulation**, with the past over fibres. -/
theorem pb_interp {stepX : X → X → Prop} {stepY : Y → Y → Prop} {h : X → Y}
    (bisimulation : FunctionalBisimulation stepX stepY h) (onto : Function.Surjective h)
    (val : Atom → Y → Prop) (φ : Formula Atom) :
    pb h (interp stepY val φ) = interpFibre stepX h (fun a => pb h (val a)) φ := by
  induction φ with
  | atom a => rfl
  | neg φ ih =>
      show pb h (interp stepY val φ)ᶜ = (interpFibre stepX h _ φ)ᶜ
      rw [(pb_modal_hom bisimulation).2.2.1, ih]
  | and φ ψ ihφ ihψ =>
      show pb h (fun y => interp stepY val φ y ∧ interp stepY val ψ y) =
        fun x => interpFibre stepX h _ φ x ∧ interpFibre stepX h _ ψ x
      rw [(pb_modal_hom bisimulation).2.2.2.1, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      show pb h (fun y => interp stepY val φ y ∨ interp stepY val ψ y) =
        fun x => interpFibre stepX h _ φ x ∨ interpFibre stepX h _ ψ x
      rw [(pb_modal_hom bisimulation).2.2.2.2, ihφ, ihψ]
  | diamond φ ih =>
      show pb h (derivedDiamond (span stepY) (interp stepY val φ)) =
        derivedDiamond (span stepX) (interpFibre stepX h _ φ)
      rw [(pb_modal_hom bisimulation).1, ih]
  | forwardBox φ ih =>
      show pb h (derivedForwardBox (span stepY) (interp stepY val φ)) =
        derivedForwardBox (span stepX) (interpFibre stepX h _ φ)
      rw [(pb_modal_hom bisimulation).2.1, ih]
  | past φ ih =>
      show pb h (derivedBox (span stepY) (interp stepY val φ)) =
        fibrePredecessorBox stepX h (interpFibre stepX h _ φ)
      rw [pb_predecessorBox_eq_fibre bisimulation onto, ih]

/-- Without the past, the fibres play no role. -/
theorem interpFibre_eq_interp {step : X → X → Prop} {h : X → Y} {val : Atom → X → Prop}
    {φ : Formula Atom} (free : PastFree φ) : interpFibre step h val φ = interp step val φ := by
  induction free with
  | atom a => rfl
  | neg _ ih =>
      show (interpFibre step h val _)ᶜ = (interp step val _)ᶜ
      rw [ih]
  | and _ _ ihφ ihψ =>
      show (fun x => interpFibre step h val _ x ∧ interpFibre step h val _ x) =
        fun x => interp step val _ x ∧ interp step val _ x
      rw [ihφ, ihψ]
  | or _ _ ihφ ihψ =>
      show (fun x => interpFibre step h val _ x ∨ interpFibre step h val _ x) =
        fun x => interp step val _ x ∨ interp step val _ x
      rw [ihφ, ihψ]
  | diamond _ ih =>
      show derivedDiamond (span step) (interpFibre step h val _) = derivedDiamond (span step) (interp step val _)
      rw [ih]
  | forwardBox _ ih =>
      show derivedForwardBox (span step) (interpFibre step h val _) =
        derivedForwardBox (span step) (interp step val _)
      rw [ih]

/-- **Past-free formulas pull back to the same formula.** -/
theorem pb_interp_of_pastFree {stepX : X → X → Prop} {stepY : Y → Y → Prop} {h : X → Y}
    (bisimulation : FunctionalBisimulation stepX stepY h) (onto : Function.Surjective h)
    (val : Atom → Y → Prop) {φ : Formula Atom} (free : PastFree φ) :
    pb h (interp stepY val φ) = interp stepX (fun a => pb h (val a)) φ := by
  rw [pb_interp bisimulation onto, interpFibre_eq_interp free]

end Formula

/-- **A predicate is a pullback exactly when it is constant on fibres.** -/
theorem eq_pb_iff_fibreInvariant {X : Type v} {Y : Type w} {h : X → Y} (ψ : X → Prop) :
    (∃ φ : Y → Prop, ψ = pb h φ) ↔ ∀ x x', h x = h x' → (ψ x ↔ ψ x') := by
  constructor
  · rintro ⟨φ, rfl⟩ x x' same
    show φ (h x) ↔ φ (h x')
    rw [same]
  · intro invariant
    refine ⟨fun y => ∃ x, h x = y ∧ ψ x, ?_⟩
    funext x
    apply propext
    constructor
    · exact fun holds => ⟨x, rfl, holds⟩
    · rintro ⟨x', same, holds⟩
      exact (invariant x' x same).mp holds

/-! ## Rho -/

section Rho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open FragmentsOfTheStep.NarrowingToRho FragmentsOfTheStep.RhoChannelFragment
open Formula

variable {context : Ctx sig} {Atom : Type u}

/-- **Rho's native types are the step's types along the narrowing**: every formula of the generated
logic, over any predicates on processes, with predecessor necessity over the heating class. -/
theorem rho_native_types (val : Atom → Process context → Prop) (φ : Formula Atom) :
    pb narrow (interp RhoStep val φ) =
      interpFibre (heatedStep (context := context)) narrow (fun a => pb narrow (val a)) φ :=
  pb_interp narrowing_functionalBisimulation narrowing_onto val φ

/-- **Without the past, the same formula.** -/
theorem rho_native_types_pastFree (val : Atom → Process context → Prop) {φ : Formula Atom}
    (free : PastFree φ) :
    pb narrow (interp RhoStep val φ) = interp (heatedStep (context := context)) (fun a => pb narrow (val a)) φ :=
  pb_interp_of_pastFree narrowing_functionalBisimulation narrowing_onto val free

/-- **The past diverges at the state**: "no predecessor", read on the step at a heated store, holds
where rho's, pulled back, fails. -/
theorem past_diverges :
    ∃ C₀ : HeatedStore [],
      interp (heatedStep (context := [])) (fun _ : Unit => pb narrow (fun _ => False)) (past (atom ())) C₀ ∧
        ¬ pb narrow (interp (RhoStep (context := [])) (fun _ : Unit => fun _ => False) (past (atom ()))) C₀ :=
  rho_predecessorBox_fails

/-- Two heated stores with one process, one with no knowledge and one with knowledge. -/
theorem same_process_different_knowledge :
    ∃ C₀ C₁ : HeatedStore [], narrow C₀ = narrow C₁ ∧ C₀.1.equations = [] ∧ C₁.1.equations ≠ [] := by
  obtain ⟨C₀, P, empty, step⟩ := forgetful_store
  obtain ⟨C, rfl⟩ := narrowing_onto P
  obtain ⟨C₁, moved, image⟩ := narrowing_functionalBisimulation.zag step
  exact ⟨C₀, C₁, image.symm, empty, channelStep_learns moved⟩

/-- **History is not a native type of rho**: "the knowledge is empty" is a predicate of the step that
is the pullback of no predicate on processes. -/
theorem knowledge_not_native :
    ¬ ∃ φ : Process [] → Prop, (fun C : HeatedStore [] => C.1.equations = []) = pb narrow φ := by
  intro native
  obtain ⟨C₀, C₁, same, empty, nonempty⟩ := same_process_different_knowledge
  exact nonempty (((eq_pb_iff_fibreInvariant (h := narrow)
    (fun C : HeatedStore [] => C.1.equations = [])).mp native C₀ C₁ same).mp empty)

end Rho

/-! ## The intrinsic and the authored presentation -/

section Authored

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.OSLF.Binding.RhoSchema Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding

/-- **Where the authored MeTTa-IL rho and the intrinsic presentation diverge**: on a closed
communication their reducts are not structurally congruent and a structural observation tells them
apart, while every observation respecting residual equivalence agrees on them. -/
theorem authored_intrinsic_divergence :
    ¬ StructuralCongruence (encodeTerm commTarget) authoredCommReduct ∧
      (Canonical.canonicalize authoredCommReduct = zeroPattern ∧
        Canonical.canonicalize (encodeTerm commTarget) ≠ zeroPattern) ∧
      ∀ φ : ProcPred, ProcPredRespectsResidualEquiv φ →
        (φ authoredCommReduct ↔ φ (encodeTerm commTarget)) :=
  ⟨notStructurallyCongruent, structuralObservation_distinguishes, residualObservation_agrees⟩

end Authored

end NativeTypesOnTheStep.RhoNativeTypes

#print axioms NativeTypesOnTheStep.RhoNativeTypes.Formula.pb_interp
#print axioms NativeTypesOnTheStep.RhoNativeTypes.Formula.interpFibre_eq_interp
#print axioms NativeTypesOnTheStep.RhoNativeTypes.Formula.pb_interp_of_pastFree
#print axioms NativeTypesOnTheStep.RhoNativeTypes.eq_pb_iff_fibreInvariant
#print axioms NativeTypesOnTheStep.RhoNativeTypes.rho_native_types
#print axioms NativeTypesOnTheStep.RhoNativeTypes.rho_native_types_pastFree
#print axioms NativeTypesOnTheStep.RhoNativeTypes.past_diverges
#print axioms NativeTypesOnTheStep.RhoNativeTypes.same_process_different_knowledge
#print axioms NativeTypesOnTheStep.RhoNativeTypes.knowledge_not_native
#print axioms NativeTypesOnTheStep.RhoNativeTypes.authored_intrinsic_divergence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
