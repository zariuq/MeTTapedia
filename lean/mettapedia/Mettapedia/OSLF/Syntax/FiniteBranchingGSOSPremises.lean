import Mettapedia.OSLF.Syntax.FiniteBranchingBehaviour
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi

/-!
# Individually addressed finite GSOS premises

Positive occurrences have an independently supplied finite carrier of addresses.
The same address may occur more than once. Each occurrence introduces its
own typed target name; the original argument names remain available even
at passive positions. Negative premises are independently authored finite
sets of action addresses. Matching positive occurrences does not require
distinct successor values.

The target is ordinary free constructor syntax over precisely those names.
Its natural-operation comparison is proved on independently named inputs,
including variable maps that identify different premise occurrences.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.Premises

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)

universe u

variable {S : Signature.{u}} {Actions : S.Srt → Type u}

/-- A labelled transition requested at a particular argument position. -/
abbrev Address {sort : S.Srt} (operator : S.Operator sort) :=
  Σ position : S.Position operator, Actions (S.argument operator position)

/-- The independently authored positive occurrences and negative tests. -/
structure Pattern {sort : S.Srt} (operator : S.Operator sort) where
  Occurrence : Type u
  finite : Finite Occurrence
  address : Occurrence → Address (Actions := Actions) operator
  negative : Finset (Address (Actions := Actions) operator)

namespace Pattern

variable {sort : S.Srt} {operator : S.Operator sort}

attribute [instance] Pattern.finite

noncomputable instance (pattern : Pattern (Actions := Actions) operator) : Fintype pattern.Occurrence :=
  Fintype.ofFinite _

def resultSort (pattern : Pattern (Actions := Actions) operator)
    (occurrence : pattern.Occurrence) : S.Srt :=
  S.argument operator (pattern.address occurrence).1

/-- A passive pattern imposes no transition requirement at any argument. -/
def passive : Pattern (Actions := Actions) operator :=
  ⟨PEmpty.{u + 1}, inferInstance, PEmpty.elim, ∅⟩

end Pattern

/-- Original sources and individual derivative occurrences have separate names. -/
inductive Variable {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) : S.Srt → Type u where
  | original (position : S.Position operator) : Variable pattern (S.argument operator position)
  | derivative (occurrence : pattern.Occurrence) : Variable pattern (pattern.resultSort occurrence)

abbrev variableFamily {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) : S.Families :=
  fun _ index => Variable pattern index

/-- Selected derivatives, independently of whether the supplied behavior admits them. -/
structure Input {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) (X : S.Families) where
  originals : S.Arguments X operator
  derivatives : ∀ occurrence, X PUnit.unit (pattern.resultSort occurrence)

namespace Input

variable {sort : S.Srt} {operator : S.Operator sort}
    {pattern : Pattern (Actions := Actions) operator}

def map {X Y : S.Families} (mapping : X ⟶ Y) (input : Input pattern X) : Input pattern Y where
  originals position := mapping PUnit.unit _ (input.originals position)
  derivatives occurrence := mapping PUnit.unit _ (input.derivatives occurrence)

def generic (pattern : Pattern (Actions := Actions) operator) : Input pattern (variableFamily pattern) where
  originals position := .original position
  derivatives occurrence := .derivative occurrence

def assignment {X : S.Families} (input : Input pattern X) : variableFamily pattern ⟶ X :=
  fun base index => ↾(fun name =>
    match base, name with
    | .unit, .original position => input.originals position
    | .unit, .derivative occurrence => input.derivatives occurrence)

theorem assignment_generic (pattern : Pattern (Actions := Actions) operator) :
    (generic pattern).assignment = 𝟙 (variableFamily pattern) := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name <;> rfl

theorem assignment_map {X Y : S.Families} (mapping : X ⟶ Y) (input : Input pattern X) :
    (input.map mapping).assignment = input.assignment ≫ mapping := by
  funext base index
  apply ConcreteCategory.hom_ext
  intro name
  cases base
  cases name <;> rfl

theorem generic_assignment {X : S.Families} (input : Input pattern X) :
    (generic pattern).map input.assignment = input := by
  cases input
  rfl

end Input

/-- Independently supplied positive choices and empty negative addresses. -/
def Matches {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) {X : S.Families}
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (input : Input pattern X) : Prop :=
  (∀ position, input.originals position = (arguments position).1) ∧
    (∀ occurrence, input.derivatives occurrence ∈
      (arguments (pattern.address occurrence).1).2 (pattern.address occurrence).2) ∧
    ∀ address ∈ pattern.negative, (arguments address.1).2 address.2 = ∅

abbrev mapArguments {X Y : S.Families} (mapping : X ⟶ Y)
    {sort : S.Srt} {operator : S.Operator sort}
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator) :
    S.Arguments ((sourceBehaviourFunctor S Actions).obj Y) operator :=
  fun position => (mapping PUnit.unit _ (arguments position).1,
    behaviourMap S Actions mapping PUnit.unit _ (arguments position).2)

theorem matches_map {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) {X Y : S.Families}
    (mapping : X ⟶ Y)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (input : Input pattern X) (matching : Matches pattern arguments input) :
    Matches pattern (mapArguments mapping arguments) (input.map mapping) := by
  refine ⟨?_, ?_, ?_⟩
  · intro position
    exact congrArg (mapping PUnit.unit _) (matching.1 position)
  · intro occurrence
    exact (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mpr
      ⟨input.derivatives occurrence, matching.2.1 occurrence, rfl⟩
  · intro address member
    exact (availability_preserved S Actions mapping PUnit.unit _
      (arguments address.1).2 address.2).mpr (matching.2.2 address member)

/-- Each independently named occurrence chooses its own inverse image.
No injectivity of the variable map or distinctness of choices is needed. -/
theorem matches_lift {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) {X Y : S.Families}
    (mapping : X ⟶ Y)
    (arguments : S.Arguments ((sourceBehaviourFunctor S Actions).obj X) operator)
    (input : Input pattern Y) (matching : Matches pattern (mapArguments mapping arguments) input) :
    ∃ earlier : Input pattern X, Matches pattern arguments earlier ∧ earlier.map mapping = input := by
  classical
  have liftable : ∀ occurrence, ∃ value ∈
      (arguments (pattern.address occurrence).1).2 (pattern.address occurrence).2,
      mapping PUnit.unit _ value = input.derivatives occurrence :=
    fun occurrence => (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mp
      (matching.2.1 occurrence)
  let earlier : Input pattern X := ⟨fun position => (arguments position).1,
    fun occurrence => (liftable occurrence).choose⟩
  refine ⟨earlier, ⟨fun _ => rfl, ?_, ?_⟩, ?_⟩
  · intro occurrence
    exact (liftable occurrence).choose_spec.1
  · intro address member
    exact (availability_preserved S Actions mapping PUnit.unit _
      (arguments address.1).2 address.2).mp (matching.2.2 address member)
  · cases input with
    | mk originals derivatives =>
        apply congrArg₂ Input.mk
        · funext position
          exact (matching.1 position).symm
        · funext occurrence
          exact (liftable occurrence).choose_spec.2

/-- An operation on selected premise inputs, with the actual variable-map law. -/
structure NaturalConclusion {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) where
  operation : (X : S.Families) → Input pattern X → S.Term X sort
  naturality : ∀ {X Y : S.Families} (mapping : X ⟶ Y) (input : Input pattern X),
    operation Y (input.map mapping) = S.rename mapping (operation X input)

namespace NaturalConclusion

variable {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator)

def ofTarget (target : S.Term (variableFamily pattern) sort) : NaturalConclusion pattern where
  operation _ input := S.rename input.assignment target
  naturality mapping input := by
    rw [Input.assignment_map]
    exact (IndexedPolynomial.Free.map_comp S.polynomial
      (fun base index => input.assignment base index)
      (fun base index => mapping base index) target).symm

def target (operation : NaturalConclusion pattern) : S.Term (variableFamily pattern) sort :=
  operation.operation (variableFamily pattern) (Input.generic pattern)

theorem target_ofTarget (body : S.Term (variableFamily pattern) sort) :
    target pattern (ofTarget pattern body) = body := by
  change S.rename (Input.generic pattern).assignment body = body
  rw [Input.assignment_generic]
  exact IndexedPolynomial.Free.map_id S.polynomial body

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

/-- Arbitrarily many finite positive occurrences and passive originals have
exactly the independently authored typed free terms as natural conclusions. -/
def targetEquiv : S.Term (variableFamily pattern) sort ≃ NaturalConclusion pattern where
  toFun := ofTarget pattern
  invFun := target pattern
  left_inv := target_ofTarget pattern
  right_inv := ofTarget_target pattern

end NaturalConclusion

end Mettapedia.OSLF.FiniteBranching.Premises
