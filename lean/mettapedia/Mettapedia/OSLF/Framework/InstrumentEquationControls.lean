import Mettapedia.OSLF.Framework.InstrumentEquationReconstruction

/-!
# Unit, commutativity, least-count descent and retained decomposition controls

The authored binary cut has associativity, commutativity and a unit. Its
independent multiset invariant separates genuine equation classes and earns
the least count of a nontrivial two-particle compound. Openings retain raw
decomposition witnesses even when padding has the same entire quotient
target. A separately authored all-pairs equation theory honestly collapses
the quotient; no nondegeneracy assumption is hidden in reconstruction.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.InstrumentEquationControls

open InstrumentObservations InstrumentEquations

inductive Symbol where
  | unit | a | b | cut
  deriving DecidableEq

abbrev arity : Symbol → Nat
  | .cut => 2
  | _ => 0

abbrev Term := Tree Symbol arity

def unit : Term := .node .unit Fin.elim0
def a : Term := .node .a Fin.elim0
def b : Term := .node .b Fin.elim0
def cut (first second : Term) : Term := .node .cut ![first, second]

inductive Generators : Term → Term → Prop where
  | unit (term : Term) : Generators (cut term unit) term
  | comm (first second : Term) : Generators (cut first second) (cut second first)
  | assoc (first second third : Term) :
      Generators (cut (cut first second) third) (cut first (cut second third))

def inventory : Term → Multiset Bool
  | .node .unit _ => 0
  | .node .a _ => {false}
  | .node .b _ => {true}
  | .node .cut arguments => inventory (arguments 0) + inventory (arguments 1)

theorem inventory_generator {first second : Term} (equation : Generators first second) :
    inventory first = inventory second := by
  cases equation <;> simp [inventory, cut, unit, add_comm, add_assoc]

theorem inventory_equation {first second : Term} (equation : Equation Generators first second) :
    inventory first = inventory second := by
  induction equation with
  | refl => rfl
  | generator supplied => exact inventory_generator supplied
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH
  | congruence constructor first second _ inductionHypothesis =>
    cases constructor with
    | unit => rfl
    | a => rfl
    | b => rfl
    | cut => exact congrArg₂ (· + ·) (inductionHypothesis 0) (inductionHypothesis 1)

def inventoryClass : TermClass Generators → Multiset Bool :=
  Quotient.lift inventory (fun _ _ equation => inventory_equation equation)

theorem a_class_ne_unit : classOf Generators a ≠ classOf Generators unit := by
  intro same
  have counted := congrArg (fun value => (inventoryClass value).card) same
  change 1 = 0 at counted
  exact Nat.one_ne_zero counted

theorem a_class_ne_b : classOf Generators a ≠ classOf Generators b := by
  intro same
  have counted := congrArg (fun value => (inventoryClass value).count false) same
  change 1 = 0 at counted
  exact Nat.one_ne_zero counted

theorem constructorCount_cut (first second : Term) :
    constructorCount (cut first second) = 1 + constructorCount first + constructorCount second := by
  simp [constructorCount, cut, arity, Fin.sum_univ_two, Nat.add_assoc]

theorem constructorCount_a : constructorCount a = 1 := by simp [constructorCount, a, arity]
theorem constructorCount_b : constructorCount b = 1 := by simp [constructorCount, b, arity]
theorem constructorCount_unit : constructorCount unit = 1 := by simp [constructorCount, unit, arity]

theorem count_bounds_inventory (term : Term) :
    2 * (inventory term).card ≤ constructorCount term + 1 := by
  induction term with
  | node constructor arguments inductionHypothesis =>
    cases constructor with
    | unit => simp [inventory, constructorCount, arity]
    | a => simp [inventory, constructorCount, arity]
    | b => simp [inventory, constructorCount, arity]
    | cut =>
      have first := inductionHypothesis 0
      have second := inductionHypothesis 1
      simp only [inventory, Multiset.card_add, constructorCount, arity, Fin.sum_univ_two]
      omega

theorem a_measure : measure Generators (classOf Generators a) = 1 := by
  have lower := measure_positive Generators (classOf Generators a)
  have upper := measure_le_count Generators (classOf Generators a) a rfl
  rw [constructorCount_a] at upper
  omega

theorem unit_padding_changes_raw_count : constructorCount (cut a unit) = 3 := by
  rw [constructorCount_cut, constructorCount_a, constructorCount_unit]

theorem unit_padding_same_class : classOf Generators (cut a unit) = classOf Generators a :=
  Quotient.sound (Equation.generator (Generators.unit a))

theorem unit_padding_not_lean : ¬ IsLean Generators (cut a unit) := by
  intro lean
  change constructorCount (cut a unit) = measure Generators (classOf Generators (cut a unit)) at lean
  rw [unit_padding_same_class, a_measure, unit_padding_changes_raw_count] at lean
  omega

theorem cut_a_b_measure : measure Generators (classOf Generators (cut a b)) = 3 := by
  have upper := measure_le_count Generators (classOf Generators (cut a b)) (cut a b) rfl
  rw [constructorCount_cut, constructorCount_a, constructorCount_b] at upper
  obtain ⟨term, represents, counted⟩ := measure_attained Generators (classOf Generators (cut a b))
  have inventorySame := inventory_equation (Quotient.exact represents)
  have cards := congrArg Multiset.card inventorySame
  have bounded := count_bounds_inventory term
  have two : (inventory (cut a b)).card = 2 := by simp [inventory, cut, a, b]
  rw [two] at cards
  rw [cards, counted] at bounded
  omega

theorem compound_is_actually_lean : IsLean Generators (cut a b) := by
  change constructorCount (cut a b) = measure Generators (classOf Generators (cut a b))
  rw [constructorCount_cut, constructorCount_a, constructorCount_b, cut_a_b_measure]

theorem actual_compound_child_descent :
    IsLean Generators a ∧ measure Generators (classOf Generators a) <
      measure Generators (classOf Generators (cut a b)) :=
  lean_child_descent Generators .cut ![a, b] compound_is_actually_lean 0

def full : Policy Symbol := fun _ => True

theorem cross_root_equation_calibrates :
    ClassBisimilar Generators full (.term (classOf Generators (cut a unit)))
      (.term (classOf Generators a)) :=
  class_equation_calibration Generators full (.generator (Generators.unit a))

theorem raw_view_admission_rejects_unit : ¬ LocalEquationAdmission full Generators := by
  intro admission
  have same := admission (cut a unit) a (Generators.unit a)
  have raw := complete_view_injective full (fun _ => trivial) same
  cases raw

theorem actual_full_reconstruction (first second : Term) :
    ClassBisimilar Generators full (.term (classOf Generators first))
      (.term (classOf Generators second)) ↔ Equation Generators first second :=
  complete_raw_equation_reconstruction Generators full (fun _ => trivial) first second

def directOpening (origin : Nat) : RetainedOpening Generators Nat (classOf Generators a) .cut where
  origin := origin
  arguments := ![a, unit]
  decomposes := unit_padding_same_class

def paddedOpening (origin : Nat) : RetainedOpening Generators Nat (classOf Generators a) .cut where
  origin := origin
  arguments := ![cut a unit, unit]
  decomposes := Quotient.sound
    (Equation.trans (.generator (Generators.unit (cut a unit))) (.generator (Generators.unit a)))

theorem padding_same_complete_target (firstOrigin secondOrigin : Nat) :
    (directOpening firstOrigin).target = (paddedOpening secondOrigin).target := by
  change ClassState.bundle (generators := Generators) Symbol.cut
      (fun position => classOf Generators (![a, unit] position)) =
    ClassState.bundle (generators := Generators) Symbol.cut
      (fun position => classOf Generators (![cut a unit, unit] position))
  apply congrArg (ClassState.bundle (generators := Generators) Symbol.cut)
  funext position
  fin_cases position
  · exact unit_padding_same_class.symm
  · rfl

theorem retained_raw_decompositions_differ (firstOrigin secondOrigin : Nat) :
    constructorCount (arity := arity) (.node Symbol.cut (directOpening firstOrigin).arguments) = 3 ∧
      constructorCount (arity := arity) (.node Symbol.cut (paddedOpening secondOrigin).arguments) = 5 := by
  constructor <;> simp [directOpening, paddedOpening, constructorCount, arity,
    Fin.sum_univ_two, cut, a, unit]

theorem actual_receipt_origins_retained :
    ((directOpening 7).receipt full (by trivial)).origin = 7 ∧
      ((paddedOpening 8).receipt full (by trivial)).origin = 8 := ⟨rfl, rfl⟩

theorem no_receipt_with_empty_origins {source : ClassState Generators}
    {label : Label Symbol arity} {target : ClassState Generators} :
    ¬ Nonempty (ClassReceipt Generators Empty full source label target) := by
  rintro ⟨receipt⟩
  exact receipt.origin.elim

theorem unit_two_actual_openings :
    ClassResponse Generators full (.term (classOf Generators a)) (.ask .cut)
      (.bundle .cut (fun position => classOf Generators (![a, unit] position))) ∧
    ClassResponse Generators full (.term (classOf Generators a)) (.ask .cut)
      (.bundle .cut (fun position => classOf Generators (![unit, a] position))) := by
  constructor
  · exact ⟨(directOpening 7).event full (by trivial)⟩
  · refine ⟨ClassEvent.ask (generators := Generators) Symbol.cut ![unit, a]
      (by trivial) (classOf Generators a) ?_⟩
    exact Quotient.sound
      (Equation.trans (.generator (Generators.comm unit a)) (.generator (Generators.unit a)))

theorem opening_targets_are_distinct :
    (ClassState.bundle (generators := Generators) Symbol.cut
      (fun position => classOf Generators (![a, unit] position))) ≠
      (.bundle Symbol.cut (fun position => classOf Generators (![unit, a] position))) := by
  intro same
  have components := eq_of_heq (ClassState.bundle.inj same).2
  exact a_class_ne_unit (congrFun components 0)

inductive CollapseGenerators : Term → Term → Prop where
  | identify (first second : Term) : CollapseGenerators first second

theorem collapsed_classes_equal (first second : Term) :
    classOf CollapseGenerators first = classOf CollapseGenerators second :=
  Quotient.sound (Equation.generator (CollapseGenerators.identify first second))

theorem collapsed_measure_is_one (term : Term) :
    measure CollapseGenerators (classOf CollapseGenerators term) = 1 := by
  have lower := measure_positive CollapseGenerators (classOf CollapseGenerators term)
  have upper := measure_le_count CollapseGenerators (classOf CollapseGenerators term) a
    (collapsed_classes_equal a term)
  rw [constructorCount_a] at upper
  omega

theorem collapsed_equations_need_not_preserve_raw_trees :
    a ≠ b ∧ ClassBisimilar CollapseGenerators full (.term (classOf CollapseGenerators a))
      (.term (classOf CollapseGenerators b)) := by
  constructor
  · intro same
    have counted := congrArg (fun value => (inventory value).count false) same
    change 1 = 0 at counted
    exact Nat.one_ne_zero counted
  · exact class_equation_calibration CollapseGenerators full
      (.generator (CollapseGenerators.identify a b))

end Mettapedia.OSLF.Framework.InstrumentEquationControls
