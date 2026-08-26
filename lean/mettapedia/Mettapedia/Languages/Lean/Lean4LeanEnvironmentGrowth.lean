import Mathlib.CategoryTheory.Functor.OfSequence
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Lemmas
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# Lean4Lean core environment growth as indexed GSLTs

This module connects the axiom-clean declarative core of Lean4Lean to the
existing indexed GSLT and OSLF constructions.  It deliberately imports
neither Lean4Lean's unfinished inductive-declaration semantics nor its
executable verifier.

For a fixed environment, universe-parameter count, context, and expected
type, Lean4Lean's four-place `IsDefEq` judgment is presented as a binary
declarative-relation GSLT on expressions.  Environment extension transports
that relation forward by Lean4Lean's proved monotonicity theorem.  An ordered
sequence of core declarations therefore yields a diagram in the existing
forward operational category, and OSLF records the corresponding relational
modalities in every fibre.

This is a declarative-calculus integration, not an operational reduction or
a Lean kernel realization.  Directed reduction is supplied separately.
Inductives, recursors, quotient installation, executable checking,
proof-relevant derivation occurrences, and NIK admission remain separate
obligations.
-/

namespace Mettapedia.Languages.Lean.Lean4LeanEnvironmentGrowth

open CategoryTheory
open Lean4Lean
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## The axiom-clean core declaration fragment -/

/-- Well-formedness of a definition value, stated without importing the
unfinished full declaration layer. -/
def DefValueWF (environment : VEnv) (value : VDefVal) : Prop :=
  environment.HasType value.uvars [] value.value value.type

/-- The declaration steps whose semantics is already determined by the
axiom-clean Lean4Lean core.  Quotients and inductives are intentionally absent
from this first fragment. -/
inductive CoreDeclStep : VEnv → VDecl → VEnv → Prop where
  | addAxiom
      (wellTyped : constant.toVConstant.WF environment)
      (added : environment.addConst constant.name constant.toVConstant =
        some extended) :
      CoreDeclStep environment (.axiom constant) extended
  | addDefinition
      (wellTyped : DefValueWF environment value)
      (added : environment.addConst value.name value.toVConstant =
        some withConstant) :
      CoreDeclStep environment (.def value)
        (withConstant.addDefEq value.toDefEq)
  | addOpaque
      (wellTyped : DefValueWF environment value)
      (added : environment.addConst value.name value.toVConstant =
        some extended) :
      CoreDeclStep environment (.opaque value) extended
  | checkExample
      (wellTyped : DefValueWF environment value) :
      CoreDeclStep environment (.example value) environment

/-- Every admitted core declaration extends the environment preorder. -/
theorem CoreDeclStep.environment_le
    {environment extended : VEnv} {declaration : VDecl}
    (step : CoreDeclStep environment declaration extended) :
    environment ≤ extended := by
  cases step with
  | addAxiom _ added => exact VEnv.addConst_le added
  | addDefinition _ added =>
      exact VEnv.LE.trans (VEnv.addConst_le added) VEnv.addDefEq_le
  | addOpaque _ added => exact VEnv.addConst_le added
  | checkExample _ => exact VEnv.LE.rfl

/-- A type-valued stage transition retains the selected declaration
occurrence.  `stutter` extends a finite declaration sequence to a `Nat`-indexed
diagram without inventing a declaration. -/
inductive GrowthTransition : VEnv → VEnv → Type where
  | declaration (decl : VDecl)
      (valid : CoreDeclStep before decl after) :
      GrowthTransition before after
  | stutter (environment : VEnv) : GrowthTransition environment environment

/-- Every growth transition is monotone on Lean4Lean environments. -/
def GrowthTransition.environmentLE
    {before after : VEnv} (transition : GrowthTransition before after) :
    before ≤ after :=
  match transition with
  | .declaration _ valid => valid.environment_le
  | .stutter _ => VEnv.LE.rfl

/-- An ordered, occurrence-carrying environment history.  Finite histories
are represented by a stationary tail rather than by forgetting their order. -/
structure CoreEnvironmentGrowth where
  stage : Nat → VEnv
  transition : (index : Nat) →
    GrowthTransition (stage index) (stage (index + 1))

namespace CoreEnvironmentGrowth

/-- Later stages contain every constant and definitional equation available
at earlier stages. -/
theorem stage_mono (growth : CoreEnvironmentGrowth)
    {earlier later : Nat} (order : earlier ≤ later) :
    growth.stage earlier ≤ growth.stage later := by
  induction order with
  | refl => exact VEnv.LE.rfl
  | @step later _ inductionHypothesis =>
      exact VEnv.LE.trans inductionHypothesis
        (growth.transition later).environmentLE

end CoreEnvironmentGrowth

/-! ## Fixed-environment declarative GSLTs -/

/-- Lean4Lean definitional equality at a fixed environment, parameter count,
context, and expected type, presented as a binary GSLT relation.

This is the declarative relation itself.  It is not an evaluator step and is
not claimed to decide the relation. -/
def defEqRelationGSLT (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType : VExpr) : GSLT where
  Term := VExpr
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun left right =>
    environment.IsDefEq universeParameters context left right expectedType
  rewrites_resp_left := by
    intro left left' right equal judgment
    subst left'
    exact ⟨right, judgment, rfl⟩
  rewrites_resp_right := by
    intro left right right' judgment equal
    subst right'
    exact judgment

@[simp] theorem defEqRelationGSLT_step_iff
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType left right : VExpr) :
    (defEqRelationGSLT environment universeParameters context expectedType).Step
        left right ↔
      environment.IsDefEq universeParameters context left right expectedType :=
  Iff.rfl

/-- Environment extension gives a genuine forward operational translation of
the declarative relation.  Reflection is intentionally not claimed: a later
environment may add constants and definitional equations. -/
def defEqRelationEnvironmentTranslation
    {environment extended : VEnv} (extension : environment ≤ extended)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) :
    OperationalTranslation
      (defEqRelationGSLT environment universeParameters context expectedType)
      (defEqRelationGSLT extended universeParameters context expectedType) where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapStep := fun judgment => judgment.mono extension

@[simp] theorem defEqRelationEnvironmentTranslation_id
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType : VExpr) :
    defEqRelationEnvironmentTranslation VEnv.LE.rfl universeParameters context expectedType =
      OperationalTranslation.id
        (defEqRelationGSLT environment universeParameters context expectedType) := by
  apply OperationalTranslation.ext
  rfl

@[simp] theorem defEqRelationEnvironmentTranslation_comp
    {first second third : VEnv}
    (firstToSecond : first ≤ second) (secondToThird : second ≤ third)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) :
    defEqRelationEnvironmentTranslation (VEnv.LE.trans firstToSecond secondToThird)
        universeParameters context expectedType =
      (defEqRelationEnvironmentTranslation firstToSecond universeParameters context
        expectedType).comp
      (defEqRelationEnvironmentTranslation secondToThird universeParameters context
        expectedType) := by
  apply OperationalTranslation.ext
  rfl

/-! ## The ordered environment diagram -/

/-- The declarative GSLT at one stage of an ordered Lean environment growth. -/
def defEqRelationStageTheory (growth : CoreEnvironmentGrowth)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) (stage : Nat) : OperationalTheory :=
  ⟨defEqRelationGSLT (growth.stage stage) universeParameters context expectedType⟩

/-- The adjacent environment map in the operational category. -/
def defEqRelationStageArrow (growth : CoreEnvironmentGrowth)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) (stage : Nat) :
    defEqRelationStageTheory growth universeParameters context expectedType stage ⟶
      defEqRelationStageTheory growth universeParameters context expectedType (stage + 1) :=
  defEqRelationEnvironmentTranslation (growth.transition stage).environmentLE
    universeParameters context expectedType

/-- The Lean4Lean core environment history as a `Nat`-indexed operational
GSLT diagram.  Establishing a supplied colimit and finite presentability is a
later obligation before this may be promoted to `FilteredGrowth`. -/
def defEqRelationEnvironmentDiagram (growth : CoreEnvironmentGrowth)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType : VExpr) : Diagram Nat :=
  CategoryTheory.Functor.ofSequence
    (defEqRelationStageArrow growth universeParameters context expectedType)

/-! ## OSLF-generated native predicates -/

/-- OSLF's native predicate carrier generated from one Lean4Lean declarative
fibre. -/
abbrev DefEqRelationNativeType (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType : VExpr) : Type :=
  GSLTNativeType
    (defEqRelationGSLT environment universeParameters context expectedType)

/-- The exact-target predicate generated for one proposed right-hand side. -/
abbrev exactDefEqRelationTargetType
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType target : VExpr) :
    DefEqRelationNativeType environment universeParameters context expectedType :=
  exactTargetNativeType
    (defEqRelationGSLT environment universeParameters context expectedType) target

/-- Generated exact-target inhabitation has exactly the authored Lean4Lean
declarative meaning at this fibre. -/
theorem satisfies_exactDefEqRelationTargetType_iff
    (environment : VEnv) (universeParameters : Nat)
    (context : List VExpr) (expectedType left right : VExpr) :
    (gsltOSLF
      (defEqRelationGSLT environment universeParameters context expectedType)).satisfies
        left
        (exactDefEqRelationTargetType environment universeParameters context
          expectedType right).pred ↔
      environment.IsDefEq universeParameters context left right expectedType := by
  rw [satisfies_exactTargetNativeType_iff_step]
  rfl

/-- Environment growth transports an authored judgment into the exact OSLF
native predicate generated at the later stage.  Thus OSLF/NTT is used by the
integration theorem rather than merely inventoried beside it. -/
theorem environment_growth_preserves_defEq_relation_type
    {environment extended : VEnv} (extension : environment ≤ extended)
    (universeParameters : Nat) (context : List VExpr)
    (expectedType left right : VExpr)
    (judgment :
      environment.IsDefEq universeParameters context left right expectedType) :
    (gsltOSLF
      (defEqRelationGSLT extended universeParameters context expectedType)).satisfies
        left
        (exactDefEqRelationTargetType extended universeParameters context
          expectedType right).pred := by
  apply (satisfies_exactDefEqRelationTargetType_iff extended universeParameters
    context expectedType left right).2
  exact judgment.mono extension

/-! ## Directionality canary -/

/-- Successfully adding a fresh constant is a strict environment extension:
the resulting environment cannot map back to the source environment. -/
theorem addConst_not_reverse
    {environment extended : VEnv} {name : Name} {constant : VConstant}
    (added : environment.addConst name constant = some extended) :
    ¬ extended ≤ environment := by
  have absent : environment.constants name = none := by
    cases old : environment.constants name with
    | none => rfl
    | some previous =>
        simp [VEnv.addConst, old] at added
  intro reverse
  have inherited : environment.constants name = some constant :=
    reverse.constants (VEnv.addConst_self added)
  rw [absent] at inherited
  cases inherited

/-! ## Concrete positive fixture -/

namespace Canary

def typeName : Name := .str .anonymous "Lean4LeanEnvironmentGrowth.Type"

def typeConstant : VConstVal where
  name := typeName
  uvars := 0
  type := .sort .zero

def afterTypeAxiom : VEnv where
  constants := fun candidate =>
    if typeName = candidate then some typeConstant.toVConstant else none
  defeqs := fun _ => False

theorem typeConstant_wellTyped :
    typeConstant.toVConstant.WF VEnv.empty := by
  refine ⟨.succ .zero, ?_⟩
  exact VEnv.HasType.sort (by trivial)

theorem typeConstant_adds :
    VEnv.empty.addConst typeName typeConstant.toVConstant =
      some afterTypeAxiom := by
  rfl

def typeAxiomStep :
    CoreDeclStep VEnv.empty (.axiom typeConstant) afterTypeAxiom :=
  .addAxiom typeConstant_wellTyped typeConstant_adds

/-- A genuine one-declaration history followed by a stationary tail. -/
def singleAxiomGrowth : CoreEnvironmentGrowth where
  stage
    | 0 => VEnv.empty
    | _ + 1 => afterTypeAxiom
  transition
    | 0 => .declaration (.axiom typeConstant) typeAxiomStep
    | _ + 1 => .stutter afterTypeAxiom

def firstGrowth : (0 : Nat) ⟶ 1 :=
  CategoryTheory.homOfLE (by omega)

/-- The first arrow of the concrete diagram is exactly the operational
translation induced by the authored axiom transition. -/
theorem singleAxiomDiagram_first_map :
    (defEqRelationEnvironmentDiagram singleAxiomGrowth 0 [] (.sort (.succ .zero))).map
        firstGrowth =
      defEqRelationEnvironmentTranslation typeAxiomStep.environment_le 0 []
        (.sort (.succ .zero)) := by
  exact CategoryTheory.Functor.ofSequence_map_homOfLE_succ
    (defEqRelationStageArrow singleAxiomGrowth 0 [] (.sort (.succ .zero))) 0

theorem sortZero_available_before_growth :
    VEnv.empty.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  VEnv.HasType.sort (by trivial)

/-- A judgment already available at the empty stage is transported through
the real declaration edge into the exact native type generated at stage one. -/
theorem sortZero_survives_growth_in_generated_type :
    (gsltOSLF
      (defEqRelationGSLT afterTypeAxiom 0 [] (.sort (.succ .zero)))).satisfies
        (.sort .zero)
        (exactDefEqRelationTargetType afterTypeAxiom 0 [] (.sort (.succ .zero))
          (.sort .zero)).pred :=
  environment_growth_preserves_defEq_relation_type
    typeAxiomStep.environment_le 0 [] (.sort (.succ .zero))
    (.sort .zero) (.sort .zero) sortZero_available_before_growth

theorem typeConstant_available :
    afterTypeAxiom.HasType 0 [] (.const typeName []) (.sort .zero) := by
  have present :
      afterTypeAxiom.constants typeName = some typeConstant.toVConstant := by
    simp [afterTypeAxiom, typeName, typeConstant]
  have typed := VEnv.HasType.const
    (env := afterTypeAxiom) (U := 0) (Γ := [])
    (ci := typeConstant.toVConstant) (ls := []) present
    (by simp) (by rfl)
  simpa [typeConstant, VExpr.instL, VLevel.inst] using typed

/-- Positive: the declaration introduced at stage one inhabits the exact
OSLF target type generated from that stage's declarative GSLT. -/
theorem typeConstant_inhabits_generated_type :
    (gsltOSLF (defEqRelationGSLT afterTypeAxiom 0 [] (.sort .zero))).satisfies
      (.const typeName [])
      (exactDefEqRelationTargetType afterTypeAxiom 0 [] (.sort .zero)
        (.const typeName [])).pred :=
  (satisfies_exactDefEqRelationTargetType_iff afterTypeAxiom 0 [] (.sort .zero)
    (.const typeName []) (.const typeName [])).2 typeConstant_available

/-- Negative: the declaration transition is not a reversible environment
map. -/
theorem typeAxiom_is_strict : ¬ afterTypeAxiom ≤ VEnv.empty :=
  addConst_not_reverse typeConstant_adds

end Canary

section AxiomAudit

#print axioms CoreDeclStep.environment_le
#print axioms CoreEnvironmentGrowth.stage_mono
#print axioms defEqRelationEnvironmentTranslation
#print axioms environment_growth_preserves_defEq_relation_type
#print axioms addConst_not_reverse
#print axioms Canary.typeConstant_inhabits_generated_type
#print axioms Canary.typeAxiom_is_strict
#print axioms Canary.singleAxiomDiagram_first_map
#print axioms Canary.sortZero_survives_growth_in_generated_type

end AxiomAudit

end Mettapedia.Languages.Lean.Lean4LeanEnvironmentGrowth
