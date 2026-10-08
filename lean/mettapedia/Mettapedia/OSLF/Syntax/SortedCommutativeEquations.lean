import Mettapedia.OSLF.Syntax.SortedConstructorContexts
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Sorted free constructors with designated associative-commutative Cut

Only a declared parallel sort has a unit and binary Cut. Ordinary constructors
retain their independently declared heterogeneous profiles. The equation
relation is generated before its quotient is formed. A complete head record
retains the constructor and every actual child equation class; parallel
inventories flatten Cut only, never a free constructor or a fresh sort.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open Mettapedia.OSLF.SortedConstructors

universe u v

variable (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop)

inductive Term : signature.Srt → Type (max u v) where
  | zero {sort} (parallel : Parallel sort) : Term sort
  | cut {sort} (parallel : Parallel sort) (first second : Term sort) : Term sort
  | node (constructor : signature.Constructor)
      (arguments : (position : Fin (signature.arity constructor)) →
        Term (signature.input constructor position)) : Term (signature.output constructor)

variable {signature Parallel}

inductive Equation : {sort : signature.Srt} →
    Term signature Parallel sort → Term signature Parallel sort → Prop where
  | refl {sort} (term : Term signature Parallel sort) : Equation term term
  | symm {sort} {first second : Term signature Parallel sort} :
      Equation first second → Equation second first
  | trans {sort} {first second third : Term signature Parallel sort} :
      Equation first second → Equation second third → Equation first third
  | node {constructor : signature.Constructor}
      {first second : (position : Fin (signature.arity constructor)) →
        Term signature Parallel (signature.input constructor position)} :
      (∀ position, Equation (first position) (second position)) →
      Equation (.node constructor first) (.node constructor second)
  | cut {sort} (parallel : Parallel sort) {first first' second second' : Term signature Parallel sort} :
      Equation first first' → Equation second second' →
      Equation (.cut parallel first second) (.cut parallel first' second')
  | assoc {sort} (parallel : Parallel sort) (first second third : Term signature Parallel sort) :
      Equation (.cut parallel (.cut parallel first second) third)
        (.cut parallel first (.cut parallel second third))
  | comm {sort} (parallel : Parallel sort) (first second : Term signature Parallel sort) :
      Equation (.cut parallel first second) (.cut parallel second first)
  | unit {sort} (parallel : Parallel sort) (term : Term signature Parallel sort) :
      Equation (.cut parallel term (.zero parallel)) term

def equationSetoid (sort : signature.Srt) : Setoid (Term signature Parallel sort) where
  r := Equation
  iseqv := ⟨Equation.refl, Equation.symm, Equation.trans⟩

abbrev Class (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop) (sort : signature.Srt) :=
  Quotient (equationSetoid (signature := signature) (Parallel := Parallel) sort)

def classOf {sort : signature.Srt} (term : Term signature Parallel sort) : Class signature Parallel sort :=
  Quotient.mk _ term

inductive Head : signature.Srt → Type (max u v) where
  | node (constructor : signature.Constructor)
      (arguments : (position : Fin (signature.arity constructor)) →
        Class signature Parallel (signature.input constructor position)) : Head (signature.output constructor)

def inventory {sort : signature.Srt} : Term signature Parallel sort → Multiset (Head (signature := signature) (Parallel := Parallel) sort)
  | .zero _ => 0
  | .cut _ first second => inventory first + inventory second
  | .node constructor arguments => {Head.node constructor (fun position => classOf (arguments position))}

theorem Equation.inventory {sort : signature.Srt} {first second : Term signature Parallel sort}
    (equation : Equation first second) : inventory first = inventory second := by
  induction equation with
  | refl => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ first second => exact first.trans second
  | node equations _ =>
    apply congrArg (fun head => ({head} : Multiset _))
    apply congrArg (Head.node _)
    funext position
    exact Quotient.sound (equations position)
  | cut _ _ _ first second => exact congrArg₂ (· + ·) first second
  | assoc => exact add_assoc _ _ _
  | comm => exact add_comm _ _
  | unit => exact add_zero _

def inventoryQ {sort : signature.Srt} :
    Class signature Parallel sort → Multiset (Head (signature := signature) (Parallel := Parallel) sort) :=
  Quotient.lift inventory (fun _ _ equation => equation.inventory)

def Head.representative {sort : signature.Srt} :
    Head (signature := signature) (Parallel := Parallel) sort → Term signature Parallel sort
  | .node constructor arguments => .node constructor (fun position => (arguments position).out)

def Head.class {sort : signature.Srt}
    (head : Head (signature := signature) (Parallel := Parallel) sort) : Class signature Parallel sort :=
  classOf head.representative

theorem Head.class_node (constructor : signature.Constructor)
    (arguments : (position : Fin (signature.arity constructor)) →
      Term signature Parallel (signature.input constructor position)) :
    (Head.node constructor (fun position => classOf (arguments position))).class =
      classOf (.node constructor arguments) := by
  apply Quotient.sound
  apply Equation.node
  intro position
  exact Quotient.exact (Quotient.out_eq (classOf (arguments position)))

def classCut {sort : signature.Srt} (parallel : Parallel sort)
    (first second : Class signature Parallel sort) : Class signature Parallel sort :=
  Quotient.map₂ (Term.cut parallel)
    (fun _ _ first _ _ second => Equation.cut parallel first second) first second

instance classZero {sort : signature.Srt} [parallel : Fact (Parallel sort)] :
    Zero (Class signature Parallel sort) := ⟨classOf (.zero parallel.out)⟩

instance classAdd {sort : signature.Srt} [parallel : Fact (Parallel sort)] :
    Add (Class signature Parallel sort) := ⟨classCut parallel.out⟩

instance classAddCommMonoid {sort : signature.Srt} [parallel : Fact (Parallel sort)] :
    AddCommMonoid (Class signature Parallel sort) where
  add_assoc a b c := Quotient.inductionOn₃ a b c
    (fun a b c => Quotient.sound (Equation.assoc parallel.out a b c))
  zero_add a := Quotient.inductionOn a (fun a =>
    Quotient.sound ((Equation.comm parallel.out (.zero parallel.out) a).trans (Equation.unit parallel.out a)))
  add_zero a := Quotient.inductionOn a (fun a => Quotient.sound (Equation.unit parallel.out a))
  add_comm a b := Quotient.inductionOn₂ a b (fun a b => Quotient.sound (Equation.comm parallel.out a b))
  nsmul := nsmulRec

section Parallel

variable {sort : signature.Srt} (parallel : Parallel sort)

def assemble (parallel : Parallel sort)
    (supplied : Multiset (Head (signature := signature) (Parallel := Parallel) sort)) :
    Class signature Parallel sort := by
  let : Fact (Parallel sort) := ⟨parallel⟩
  exact (supplied.map Head.class).sum

theorem assemble_add (first second : Multiset (Head (signature := signature) (Parallel := Parallel) sort)) :
    assemble parallel (first + second) = classCut parallel (assemble parallel first) (assemble parallel second) := by
  let : Fact (Parallel sort) := ⟨parallel⟩
  change assemble parallel (first + second) = assemble parallel first + assemble parallel second
  simp only [assemble, Multiset.map_add, Multiset.sum_add]

theorem assemble_inventory (parallel : Parallel sort) (term : Term signature Parallel sort) :
    assemble parallel (inventory term) = classOf term := by
  let : Fact (Parallel sort) := ⟨parallel⟩
  cases term with
  | zero => rfl
  | cut _ first second =>
    rw [inventory, assemble_add, assemble_inventory parallel first, assemble_inventory parallel second]
    rfl
  | node constructor arguments =>
    simpa only [inventory, assemble, Multiset.map_singleton, Multiset.sum_singleton] using
      Head.class_node constructor arguments
termination_by sizeOf term
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals omega

end Parallel

theorem nonparallel_head {sort : signature.Srt} (nonparallel : ¬Parallel sort)
    (term : Term signature Parallel sort) :
    ∃ head : Head (signature := signature) (Parallel := Parallel) sort,
      inventory term = {head} ∧ head.class = classOf term := by
  cases term with
  | zero admitted => exact (nonparallel admitted).elim
  | cut admitted => exact (nonparallel admitted).elim
  | node constructor arguments =>
    exact ⟨.node constructor (fun position => classOf (arguments position)), rfl,
      Head.class_node constructor arguments⟩

/-- Equality of inventories reconstructs the original generated equations,
including child equations below every genuine free constructor. -/
theorem inventoryQ_injective {sort : signature.Srt} :
    Function.Injective (inventoryQ (signature := signature) (Parallel := Parallel) (sort := sort)) := by
  intro first second same
  by_cases parallel : Parallel sort
  · have firstRead : assemble parallel (inventoryQ first) = first :=
      Quotient.inductionOn first (assemble_inventory parallel)
    have secondRead : assemble parallel (inventoryQ second) = second :=
      Quotient.inductionOn second (assemble_inventory parallel)
    exact firstRead.symm.trans ((congrArg (assemble parallel) same).trans secondRead)
  · induction first using Quotient.inductionOn with
    | _ first =>
      induction second using Quotient.inductionOn with
      | _ second =>
        obtain ⟨firstHead, firstInventory, firstClass⟩ := nonparallel_head parallel first
        obtain ⟨secondHead, secondInventory, secondClass⟩ := nonparallel_head parallel second
        change inventory first = inventory second at same
        rw [firstInventory, secondInventory] at same
        exact firstClass.symm.trans ((congrArg Head.class (Multiset.singleton_inj.mp same)).trans secondClass)

theorem equation_iff_inventory {sort : signature.Srt} (first second : Term signature Parallel sort) :
    Equation first second ↔ inventory first = inventory second := by
  refine ⟨Equation.inventory, fun same => ?_⟩
  exact Quotient.exact (inventoryQ_injective same)

end Mettapedia.OSLF.SortedCommutative
