import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Step
import Mathlib.Data.List.Forall2

/-!
# Schematic row closures and their shared interface

A row schema is a premiseless rule producing one term. Its local knowledge and
parameters use its own frame. A closure supplies arguments at the ambient frame;
parameters are identified with those arguments only when the row is used.
Consequently separate uses may instantiate local unknowns independently, while
captured arguments remain shared. Neither reading selects a store default.

The representation uses the existing held-rule specifications. No second
opening, freshness predicate or solver is defined here. The reading predicate
states the denotation of a closure; its connection to actual fresh firings is
a separate operational theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)

universe uO uT uH uC uZ
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

structure Schema (Tm : Obj → Type uT) where
  locals : Obj
  knowledge : EquationStore (Tm locals)
  params : List (Tm locals)
  value : Tm locals

/-- A schema with captured arguments, not copied ambient unknowns. -/
structure Closure (Tm : Obj → Type uT) (a : Obj) where
  schema : Schema Tm
  args : List (Tm a)

namespace Schema

def toRule (row : Schema Tm) : Rule Tm :=
  RuleOccurrences.Spec.closedRow row.locals row.knowledge row.value

def toSpec {C : Type uC} {Z : Type uZ} (row : Schema Tm) : RuleOccurrences.Spec Tm C Z :=
  ⟨row.locals, row.toRule.body, [], row.params, [], [], [], [], []⟩

@[simp] theorem spec_toRule {C : Type uC} {Z : Type uZ} (row : Schema Tm) :
    (row.toSpec : RuleOccurrences.Spec Tm C Z).toRule = row.toRule := rfl

def instantiate (X : Frames Tm Hom) (row : Schema Tm) {b : Obj} (j : Hom row.locals b) : Schema Tm :=
  ⟨b, X.applyStore j row.knowledge, row.params.map (X.act j), X.act j row.value⟩

end Schema

namespace Closure

def WellFormed {a : Obj} (row : Closure Tm a) : Prop := row.schema.params.length = row.args.length

/-- Read a value by instantiating only the row's local frame, at fixed ambient data. -/
def ReadsAt (X : Frames Tm Hom) {a b : Obj} (row : Closure Tm a) (σ : Hom a b)
    (value : Tm b) : Prop :=
  ∃ h : Hom row.schema.locals b,
    X.Models h row.schema.knowledge ∧
    List.Forall₂ (fun parameter argument => X.E (X.act h parameter) (X.act σ argument))
      row.schema.params row.args ∧
    X.E (X.act h row.schema.value) value

theorem wellFormed_of_readsAt (X : Frames Tm Hom) {a b : Obj} (row : Closure Tm a)
    (σ : Hom a b) {value : Tm b} (reads : row.ReadsAt X σ value) : row.WellFormed := by
  obtain ⟨_, _, interface, _⟩ := reads
  exact interface.length_eq

/-- Carry a closure across a frame extension without opening its local binder. -/
def act (X : Frames Tm Hom) {a b : Obj} (j : Hom a b) (row : Closure Tm a) : Closure Tm b :=
  ⟨row.schema, row.args.map (X.act j)⟩

theorem readsAt_act_iff (X : Frames Tm Hom) {a b c : Obj} (j : Hom a b)
    (row : Closure Tm a) (σ : Hom b c) (value : Tm c) :
    (row.act X j).ReadsAt X σ value ↔ row.ReadsAt X (X.comp σ j) value := by
  simp only [ReadsAt, act, List.forall₂_map_right_iff, X.act_comp]

def held {a : Obj} {C : Type uC} {Z : Type uZ} (code : Schema Tm → C) (zone : Z)
    (row : Closure Tm a) : RuleOccurrences.Held Tm C Z a :=
  ⟨code row.schema, row.args, .persistent, zone⟩

theorem held_act (X : Frames Tm Hom) {a b : Obj} {C : Type uC} {Z : Type uZ}
    (code : Schema Tm → C) (zone : Z) (j : Hom a b) (row : Closure Tm a) :
    (row.act X j).held code zone = (row.held code zone).act X j := rfl

/-- Retain the result and both sides of each equation as capture ports. -/
def capturedStore {a : Obj} (store : EquationStore (Tm a)) (term : Tm a) : Closure Tm a :=
  let ports := term :: store.flatMap (fun e => [e.1, e.2])
  ⟨⟨a, store, ports, term⟩, ports⟩

theorem readsAt_capturedStore_iff (X : Frames Tm Hom) {a b : Obj}
    (store : EquationStore (Tm a)) (term : Tm a)
    (σ : Hom a b) (value : Tm b) :
    (capturedStore store term).ReadsAt X σ value ↔
      X.Models σ store ∧ X.E (X.act σ term) value := by
  let ports := term :: store.flatMap (fun e => [e.1, e.2])
  change (∃ h, X.Models h store ∧
    List.Forall₂ (fun l r => X.E (X.act h l) (X.act σ r)) ports ports ∧
    X.E (X.act h term) value) ↔ _
  simp only [List.forall₂_same]
  constructor
  · rintro ⟨h, solved, port, output⟩
    refine ⟨?_, (X.equivalence b).trans ((X.equivalence b).symm (port term List.mem_cons_self)) output⟩
    intro e member
    have lhs := port e.1 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨e, member, by simp⟩))
    have rhs := port e.2 (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨e, member, by simp⟩))
    exact (X.equivalence b).trans ((X.equivalence b).symm lhs) ((X.equivalence b).trans (solved e member) rhs)
  · intro ⟨known, output⟩
    exact ⟨σ, known, fun _ _ => (X.equivalence b).refl _, output⟩

/-- A wholly captured row has no independently instantiable output. -/
def captured {a : Obj} (term : Tm a) : Closure Tm a := capturedStore [] term

theorem readsAt_captured_iff (X : Frames Tm Hom) {a b : Obj} (term : Tm a)
    (σ : Hom a b) (value : Tm b) :
    (captured term).ReadsAt X σ value ↔ X.E (X.act σ term) value := by
  simp only [captured, readsAt_capturedStore_iff, Frames.models_nil, true_and]

def instantiate (X : Frames Tm Hom) {a b : Obj} (row : Closure Tm a)
    (j : Hom row.schema.locals b) : Closure Tm a :=
  ⟨row.schema.instantiate X j, row.args⟩

/-- A directed instance cannot introduce a value absent from the general schema. -/
theorem readsAt_of_instance (X : Frames Tm Hom) {a b c : Obj} (row : Closure Tm a)
    (j : Hom row.schema.locals b) (σ : Hom a c) (value : Tm c)
    (reads : (row.instantiate X j).ReadsAt X σ value) : row.ReadsAt X σ value := by
  dsimp only [ReadsAt, instantiate, Schema.instantiate] at reads
  obtain ⟨h, solved, interface, output⟩ := reads
  refine ⟨X.comp h j, (Frames.models_applyStore j h row.schema.knowledge).mp solved, ?_, ?_⟩
  · simp only [X.act_comp]
    exact List.forall₂_map_left_iff.mp interface
  · rw [X.act_comp]
    exact output

end Closure

/-- The binder is a property of each datum; a plain row has no local activation. -/
inductive Row (Tm : Obj → Type uT) (a : Obj) where
  | shared (value : Tm a)
  | schematic (closure : Closure Tm a)

namespace Row

def ReadsAt (X : Frames Tm Hom) {a b : Obj} (σ : Hom a b) (value : Tm b) : Row Tm a → Prop
  | .shared term => X.E (X.act σ term) value
  | .schematic row => row.ReadsAt X σ value

@[simp] theorem readsAt_shared (X : Frames Tm Hom) {a b : Obj} (σ : Hom a b)
    (term : Tm a) (value : Tm b) :
    ReadsAt X σ value (.shared term) ↔ X.E (X.act σ term) value := Iff.rfl

theorem captured_is_shared (X : Frames Tm Hom) {a b : Obj} (σ : Hom a b)
    (term : Tm a) (value : Tm b) :
    ReadsAt X σ value (.schematic (Closure.captured term)) ↔ ReadsAt X σ value (.shared term) :=
  Closure.readsAt_captured_iff X term σ value

end Row

#print axioms Closure.wellFormed_of_readsAt
#print axioms Closure.readsAt_act_iff
#print axioms Closure.readsAt_captured_iff
#print axioms Closure.readsAt_of_instance
#print axioms Row.captured_is_shared

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
