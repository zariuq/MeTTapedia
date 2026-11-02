import Mettapedia.GSLT.LanguageDef.AdmittedChildPremiseControls
import Mettapedia.GSLT.LanguageDef.AdmittedContainerChildConditions
import Mettapedia.Logic.HOL.IndexedPredicateInterpretation

/-!
# A genuine child-array model for original Cons premises

The source coding extends the generated Nil value at its active child and
uses bottom at every inactive slot. The strengthened child predicate keeps
both generated membership and the non-bottom motive.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedChildPremiseModelControls

open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open AdmittedContainerHOL AdmittedContainerGeneratedControls
open AdmittedContainerInductionControls (initial num ctor bottom motive num_meaning)
open IndexedInductiveNatVec

noncomputable section

def point := constructorPoint block registered (reading := reading) environment
  ⟨Natural.succ Natural.zero, consShape Natural.zero true⟩

theorem point_source : sourcePoint block registered environment point =
    ⟨Natural.succ Natural.zero, consShape Natural.zero true⟩ :=
  sourcePoint_constructorPoint block registered environment _

def coding :=
  (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
    (consShape Natural.zero true)

def goodChildren : Nat → Ty.denote.{0,0} model.Carrier space :=
  coding.extend (model.denote bottomCode empty) (fun _ => nilValue)

def world : model.Valuation AdmittedChildPremiseControls.context :=
  model.extend (σ := number ⇒ space) empty (fun slot : ULift.{1} Nat => goodChildren slot.down)

theorem represented : interpreted.Represents environment initial world := by
  intro _ impossible
  nomatch impossible

theorem payload_exact :
    model.denote (FiniteConstructorEncoding.encode AdmittedChildPremiseControls.constructors.fields
      consOccurrence AdmittedChildPremiseControls.arguments) world =
      nativePayload block registered sourceOrder interpreted environment (sourcePoint block registered environment point) := by
  rw [point_source]
  rfl

theorem nil_not_bottom : nilValue ≠ model.denote bottomCode empty := by
  intro equal
  exact bottom_not_generated ⟨Natural.zero, equal ▸ nil_generated⟩

theorem leastNil :
    (model.denote AdmittedChildPremiseControls.signature.least world nilValue).down := by
  apply (least_iff (block := block) (registered := registered) (sourceOrder := sourceOrder)
    (realization := interpreted) (images := images) (rho := initial) (numeral := num)
    (values := world) (environment := environment) (represented := represented)
    (zero := AdmittedChildPremiseControls.zero) (successor := AdmittedChildPremiseControls.successor)
    (full := full) (arithmeticValues := empty) (zero_meaning := rfl) (successor_meaning := fun _ => rfl)
    (bottomCode := bottom) (constructorCode := ctor) (injections := injections)
    (constructor_fields := constructor_fields) index_injective (num_meaning world) nilValue).mpr
  exact ⟨Natural.zero, nil_generated⟩

def predicate : Term Symbol AdmittedChildPremiseControls.context (space ⇒ .prop) :=
  PredicateFixedPoint.intersection AdmittedChildPremiseControls.signature.least
    (IndexedPredicateInduction.lift (AdmittedChildPremiseControls.constructors.rootProgram ctor) motive)

theorem predicateNil : (model.denote predicate world nilValue).down := by
  rw [predicate, PredicateFixedPoint.intersection_denote]
  refine ⟨leastNil, ?_⟩
  rw [IndexedPredicateInduction.lift_denote]
  intro _ _ _
  change ¬ (nilValue = model.denote bottomCode empty)
  exact nil_not_bottom

theorem source_child_facts : ∀ slot position,
    ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      (sourcePoint block registered environment point).2).decode slot = some position →
    IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
      (nativePayload block registered sourceOrder interpreted)
      (fun _ => nativeConstructor block registered sourceOrder interpreted (ctor (Γ := AdmittedChildPremiseControls.context)) world)
      environment
      ((IndexedPositiveContainer.Unindexed.blockPolynomial block registered).next
        (sourcePoint block registered environment point).2 position) (goodChildren slot) ∧
      (model.denote predicate world (goodChildren slot)).down := by
  rw [point_source]
  intro slot position decoded
  have atChild : goodChildren slot = nilValue := by
    unfold goodChildren
    change coding.decode slot = some position at decoded
    simp only [IndexedPolynomial.SlotEncoding.extend, decoded]
  rw [atChild]
  constructor
  · cases position with
    | none => exact compiled_nil_root
    | some impossible => nomatch impossible
  · exact predicateNil

theorem canonical :
    ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      (sourcePoint block registered environment point).2).Canonical
        (model.denote (bottom (Γ := AdmittedChildPremiseControls.context)) world) goodChildren := by
  rw [point_source]
  exact coding.extend_canonical (model.denote bottomCode empty) (fun _ => nilValue)

theorem conditions_valid : (model.denote AdmittedChildPremiseControls.conditions world).down := by
  apply childConditions_of_source (block := block) (registered := registered) (sourceOrder := sourceOrder)
    (realization := interpreted) (images := images) (rho := initial) (numeral := num)
    (values := world) (environment := environment) (represented := represented)
    (zero := AdmittedChildPremiseControls.zero) (successor := AdmittedChildPremiseControls.successor)
    (full := full) (arithmeticValues := empty) (zero_meaning := rfl) (successor_meaning := fun _ => rfl)
    (index_injective := index_injective) (numeral_meaning := num_meaning world)
    (bottomCode := bottom) (constructorCode := ctor) predicate
    (FiniteConstructorEncoding.encode AdmittedChildPremiseControls.constructors.fields
      consOccurrence AdmittedChildPremiseControls.arguments)
    AdmittedChildPremiseControls.children point goodChildren payload_exact
    (fun _ => rfl) source_child_facts canonical

theorem separation_valid (values : model.Valuation AdmittedChildPremiseControls.context) :
    (model.denote (NaturalNumeralProofs.separation
      (weakenCtx AdmittedChildPremiseControls.context AdmittedChildPremiseControls.zero)
      (weakenCtx AdmittedChildPremiseControls.context AdmittedChildPremiseControls.successor)) values).down := by
  change ∀ value : ULift.{1} Nat, True → ¬ ((ULift.up (value.down + 1) : ULift.{1} Nat) = ULift.up 0)
  intro value _ equal
  exact Nat.succ_ne_zero value.down (congrArg ULift.down equal)

theorem injectivity_valid (values : model.Valuation AdmittedChildPremiseControls.context) :
    (model.denote (NaturalNumeralProofs.injectivity
      (weakenCtx AdmittedChildPremiseControls.context AdmittedChildPremiseControls.successor)) values).down := by
  change ∀ left : ULift.{1} Nat, True → ∀ right : ULift.{1} Nat, True →
    (((ULift.up (left.down + 1) : ULift.{1} Nat) = ULift.up (right.down + 1)) ↔ left = right)
  intro left _ right _
  constructor
  · intro equal
    apply ULift.ext
    exact Nat.succ.inj (congrArg ULift.down equal)
  · intro equal
    cases equal
    rfl

theorem induction_valid (values : model.Valuation AdmittedChildPremiseControls.context) :
    (model.denote (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx AdmittedChildPremiseControls.context AdmittedChildPremiseControls.zero)
      (weakenCtx AdmittedChildPremiseControls.context AdmittedChildPremiseControls.successor)) values).down := by
  change ∀ predicate : Ty.denote model.Carrier (number ⇒ .prop), True →
    ((predicate (ULift.up 0)).down ∧
      (∀ value : ULift.{1} Nat, True → (predicate value).down → (predicate (ULift.up (value.down + 1))).down)) →
      ∀ value : ULift.{1} Nat, True → (predicate value).down
  intro predicate _ premises value _
  rcases value with ⟨n⟩
  induction n with
  | zero => exact premises.1
  | succ n previous => exact premises.2 (ULift.up n) trivial previous

theorem assumptions_valid (values : model.Valuation AdmittedChildPremiseControls.context)
    (condition : (model.denote AdmittedChildPremiseControls.conditions values).down) :
    ∀ formula ∈ AdmittedChildPremiseControls.assumptions, (model.denote formula values).down := by
  intro formula member
  rcases List.mem_cons.mp member with equal | member
  · subst formula
    exact condition
  · rcases List.mem_cons.mp member with equal | member
    · subst formula
      exact separation_valid values
    · rcases List.mem_cons.mp member with equal | member
      · subst formula
        exact injectivity_valid values
      · rcases List.mem_cons.mp member with equal | member
        · subst formula
          exact induction_valid values
        · exact False.elim (List.not_mem_nil member)

theorem assumptions_realizable :
    ∀ formula ∈ AdmittedChildPremiseControls.assumptions, (model.denote formula world).down :=
  assumptions_valid world conditions_valid

theorem selectedChildExists_realized :
    (model.denote (IndexedConstructorGuards.PositionPrograms.originalChildExists
      AdmittedChildPremiseControls.constructors AdmittedChildPremiseControls.zero
      AdmittedChildPremiseControls.successor AdmittedChildPremiseControls.plans bottom ctor motive
      consOccurrence AdmittedChildPremiseControls.arguments AdmittedChildPremiseControls.children
      AdmittedChildPremiseControls.target) world).down :=
  Soundness.extDerivation_sound AdmittedChildPremiseControls.selectedChildExists.erase (M := model) (ρ := world)
    (model.functionsRespectEqv_of_fullDomains full) (by intro type entry; exact full type (world entry)) assumptions_realizable

def badWorld : model.Valuation AdmittedChildPremiseControls.context :=
  model.extend (σ := number ⇒ space) empty (fun _ : ULift.{1} Nat => model.denote bottomCode empty)

theorem bad_children_refused : ¬ (model.denote AdmittedChildPremiseControls.conditions badWorld).down := by
  intro condition
  have impossible := Soundness.extDerivation_sound AdmittedChildPremiseControls.selectedNonbottom.erase
    (M := model) (ρ := badWorld) (model.functionsRespectEqv_of_fullDomains full)
    (by intro type entry; exact full type (badWorld entry)) (assumptions_valid badWorld condition)
  change ¬ (model.denote bottomCode empty = model.denote bottomCode empty) at impossible
  exact impossible rfl

#print axioms conditions_valid
#print axioms assumptions_realizable
#print axioms selectedChildExists_realized
#print axioms bad_children_refused

end
end Mettapedia.GSLT.LanguageDef.AdmittedChildPremiseModelControls
