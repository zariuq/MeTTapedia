import Mettapedia.OSLF.Syntax.DeterministicGSOSFinitePresentation

/-!
# Active and passive positive premises

A premise pattern selects at most one labelled transition at each argument.
Every argument retains its original value; active arguments additionally
retain the selected derivative. The conclusion language is independently
the free constructor syntax over these names. Natural conclusion operations
are classified by exactly one such syntax tree, including under maps that
identify variables. This statement concerns individual positive clauses;
overlapping clauses still need the deterministic consistency condition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.DeterministicGSOS.PositivePremises

open CategoryTheory Mettapedia.TypeTheory

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

/-- One selected action per active argument, with genuinely passive arguments. -/
structure Pattern {sort : S.Srt} (operator : S.Operator sort) where
  active : S.Position operator → Bool
  label : (position : S.Position operator) → active position = true →
    Actions (S.argument operator position)

/-- The original arguments and the independently named selected derivatives. -/
inductive Variable {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) : S.Srt → Type u where
  | original (position : S.Position operator) :
      Variable pattern (S.argument operator position)
  | derivative (position : S.Position operator) (active : pattern.active position = true) :
      Variable pattern (S.argument operator position)

/-- Variables of the positive target syntax, at their declared sorts. -/
abbrev variableFamily {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) : S.Families :=
  fun _ index => Variable pattern index

/-- A selected premise input contains no requirement on passive transitions. -/
structure Input {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) (X : S.Families) where
  originals : S.Arguments X operator
  derivatives : (position : S.Position operator) → pattern.active position = true →
    X PUnit.unit (S.argument operator position)

namespace Input

variable {sort : S.Srt} {operator : S.Operator sort}
    {pattern : Pattern (Actions := Actions) operator}

/-- Relabel both sources and the selected derivatives. -/
def map {X Y : S.Families} (mapping : X ⟶ Y) (input : Input pattern X) : Input pattern Y where
  originals position := mapping PUnit.unit _ (input.originals position)
  derivatives position active := mapping PUnit.unit _ (input.derivatives position active)

/-- Distinct names supply the generic selected premise input. -/
def generic (pattern : Pattern (Actions := Actions) operator) : Input pattern (variableFamily pattern) where
  originals position := .original position
  derivatives position active := .derivative position active

/-- Interpret each target name using the actual supplied premise input. -/
def assignment {X : S.Families} (input : Input pattern X) : variableFamily pattern ⟶ X :=
  fun base index => ↾(fun name =>
    match base, name with
    | .unit, .original position => input.originals position
    | .unit, .derivative position active => input.derivatives position active)

theorem assignment_generic (pattern : Pattern (Actions := Actions) operator) :
    assignment (generic pattern) = 𝟙 (variableFamily pattern) := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name <;> rfl

theorem assignment_map {X Y : S.Families} (mapping : X ⟶ Y) (input : Input pattern X) :
    assignment (map mapping input) = assignment input ≫ mapping := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name <;> rfl

theorem generic_assignment {X : S.Families} (input : Input pattern X) :
    map (assignment input) (generic pattern) = input := by
  cases input
  rfl

end Input

/-- A positive conclusion operation with its actual substitution law. -/
structure NaturalConclusion {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) where
  operation : (X : S.Families) → Input pattern X → S.Term X sort
  naturality : ∀ {X Y : S.Families} (mapping : X ⟶ Y) (input : Input pattern X),
    operation Y (input.map mapping) = S.rename mapping (operation X input)

namespace NaturalConclusion

variable {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator)

/-- Interpret an independently authored free target tree. -/
noncomputable def ofTarget (target : S.Term (variableFamily pattern) sort) : NaturalConclusion pattern where
  operation _ input := S.rename input.assignment target
  naturality mapping input := by
    rw [Input.assignment_map]
    exact (IndexedPolynomial.Free.map_comp S.polynomial
      (fun base index => input.assignment base index)
      (fun base index => mapping base index) target).symm

/-- Read a natural operation on distinct generic sources and derivatives. -/
def target (operation : NaturalConclusion pattern) : S.Term (variableFamily pattern) sort :=
  operation.operation (variableFamily pattern) (Input.generic pattern)

theorem target_ofTarget (body : S.Term (variableFamily pattern) sort) :
    target pattern (ofTarget pattern body) = body := by
  change S.rename (Input.generic pattern).assignment body = body
  rw [Input.assignment_generic]
  exact IndexedPolynomial.Free.map_id S.polynomial body

/-- Naturality at the generic assignment proves the substantive converse. -/
theorem operation_recovered (operation : NaturalConclusion pattern)
    (X : S.Families) (input : Input pattern X) :
    S.rename input.assignment (target pattern operation) = operation.operation X input := by
  have natural := operation.naturality input.assignment (Input.generic pattern)
  rw [Input.generic_assignment] at natural
  exact natural.symm

theorem ofTarget_target (operation : NaturalConclusion pattern) :
    ofTarget pattern (target pattern operation) = operation := by
  cases operation with
  | mk operation naturality =>
      unfold ofTarget
      congr 1
      funext X input
      exact operation_recovered pattern ⟨operation, naturality⟩ X input

/-- Typed target syntax classifies the natural active/passive positive clauses. -/
noncomputable def targetEquiv : S.Term (variableFamily pattern) sort ≃ NaturalConclusion pattern where
  toFun := ofTarget pattern
  invFun := target pattern
  left_inv := target_ofTarget pattern
  right_inv := ofTarget_target pattern

end NaturalConclusion

namespace Pattern

variable {sort : S.Srt} {operator : S.Operator sort}

/-- The literal all-active format: one required selected edge at every argument. -/
def allActive (labels : (position : S.Position operator) → Actions (S.argument operator position)) :
    Pattern (Actions := Actions) operator where
  active _ := true
  label position _ := labels position

/-- A premise-free positive clause keeps all sources and requires no child edge. -/
def allPassive : Pattern (Actions := Actions) operator where
  active _ := false
  label _ impossible := Bool.false_ne_true impossible |>.elim

/-- Selecting premise edges requires precisely the labelled active transitions. -/
def Realizes (pattern : Pattern (Actions := Actions) operator) {X : S.Families}
    (arguments : BehaviourArguments S Actions X operator) (input : Input pattern X) : Prop :=
  (∀ position, input.originals position = (arguments position).1) ∧
    ∀ position (active : pattern.active position = true),
      (arguments position).2 (pattern.label position active) = some (input.derivatives position active)

/-- Passive inputs are available even when all child behavior is empty. -/
theorem passive_realizes (X : S.Families) (children : S.Arguments X operator) :
    Realizes (allPassive (Actions := Actions) (operator := operator))
      (fun position => (children position, fun _ => none))
      ⟨children, fun _ impossible => (Bool.false_ne_true impossible).elim⟩ := by
  constructor
  · intro position
    rfl
  · intro position impossible
    exact (Bool.false_ne_true impossible).elim

/-- An active input cannot be supplied by a child with no transitions. -/
theorem active_not_realized_by_empty (pattern : Pattern (Actions := Actions) operator)
    (position : S.Position operator) (active : pattern.active position = true)
    (X : S.Families) (children : S.Arguments X operator) (input : Input pattern X) :
    ¬ Realizes pattern (fun position => (children position, fun _ => none)) input := by
  intro firing
  have impossible := firing.2 position active
  cases impossible

end Pattern

end Mettapedia.OSLF.DeterministicGSOS.PositivePremises
