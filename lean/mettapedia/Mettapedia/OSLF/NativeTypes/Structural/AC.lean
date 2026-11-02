import Mettapedia.OSLF.NativeTypes.Structural.Semantics
import Mettapedia.GSLT.LanguageDef.EquationSemantics

open Mettapedia.OSLF.Framework

/-!
# Separating laws detected from authored equations

The detector reads the actual unconditional binary commutativity and
associativity schemas. Its successful results earn those laws in the existing
authored contextual equation semantics, so the generated split has its
separating laws without a supplied semantic admissibility predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics

def commLeft (label : String) : Pattern := .apply label [.fvar "P", .fvar "Q"]
def commRight (label : String) : Pattern := .apply label [.fvar "Q", .fvar "P"]
def assocLeft (label : String) : Pattern :=
  .apply label [.fvar "P", .apply label [.fvar "Q", .fvar "R"]]
def assocRight (label : String) : Pattern :=
  .apply label [.apply label [.fvar "P", .fvar "Q"], .fvar "R"]

def commSchema? (label : String) (equation : Equation) : Bool :=
  equation.left == commLeft label && equation.right == commRight label && equation.premises.isEmpty

def assocSchema? (label : String) (equation : Equation) : Bool :=
  equation.left == assocLeft label && equation.right == assocRight label && equation.premises.isEmpty

def findCommutativity (language : LanguageDef) (label : String) : Option Equation :=
  language.equations.find? (commSchema? label)

def findAssociativity (language : LanguageDef) (label : String) : Option Equation :=
  language.equations.find? (assocSchema? label)

theorem commSchema?_spec (label : String) (equation : Equation) :
    commSchema? label equation = true ↔
      equation.left = commLeft label ∧ equation.right = commRight label ∧ equation.premises = [] := by
  simp [commSchema?, and_assoc]

theorem assocSchema?_spec (label : String) (equation : Equation) :
    assocSchema? label equation = true ↔
      equation.left = assocLeft label ∧ equation.right = assocRight label ∧ equation.premises = [] := by
  simp [assocSchema?, and_assoc]

theorem findCommutativity_spec {language : LanguageDef} {label : String} {equation : Equation}
    (found : findCommutativity language label = some equation) :
    equation ∈ language.equations ∧ equation.left = commLeft label ∧
      equation.right = commRight label ∧ equation.premises = [] := by
  have found' := List.find?_some found
  exact ⟨List.mem_of_find?_eq_some found,
    (commSchema?_spec label equation).mp found'⟩

theorem findAssociativity_spec {language : LanguageDef} {label : String} {equation : Equation}
    (found : findAssociativity language label = some equation) :
    equation ∈ language.equations ∧ equation.left = assocLeft label ∧
      equation.right = assocRight label ∧ equation.premises = [] := by
  have found' := List.find?_some found
  exact ⟨List.mem_of_find?_eq_some found,
    (assocSchema?_spec label equation).mp found'⟩

theorem detected_commutative {language : LanguageDef} {label : String} {equation : Equation}
    (base : BasePremiseEvaluator)
    (found : findCommutativity language label = some equation) (left right : Pattern) :
    EquationEquiv base language (.apply label [left, right]) (.apply label [right, left]) := by
  obtain ⟨member, leftShape, rightShape, premises⟩ := findCommutativity_spec found
  apply Relation.EqvGen.rel
  apply EquationContextStep.inContext .hole
  apply Or.inl
  refine ⟨0, EquationInstanceAt.forward (equation := equation)
    (initialBindings := [("Q", right), ("P", left)])
    (finalBindings := [("Q", right), ("P", left)]) member ?_ ?_ ?_ ?_⟩
  · simp [readsRaw, leftShape, rightShape, commLeft, commRight, binderFree, binderFreeList]
  · rw [leftShape]
    simp [commLeft, matchPattern, matchArgs, mergeBindings]
  · rw [premises]
    exact .nil _
  · rw [rightShape]
    simp [commRight, applyBindings]

theorem detected_associative {language : LanguageDef} {label : String} {equation : Equation}
    (base : BasePremiseEvaluator)
    (found : findAssociativity language label = some equation) (first second third : Pattern) :
    EquationEquiv base language (.apply label [first, .apply label [second, third]])
      (.apply label [.apply label [first, second], third]) := by
  obtain ⟨member, leftShape, rightShape, premises⟩ := findAssociativity_spec found
  apply Relation.EqvGen.rel
  apply EquationContextStep.inContext .hole
  apply Or.inl
  refine ⟨0, EquationInstanceAt.forward (equation := equation)
    (initialBindings := [("Q", second), ("R", third), ("P", first)])
    (finalBindings := [("Q", second), ("R", third), ("P", first)]) member ?_ ?_ ?_ ?_⟩
  · simp [readsRaw, leftShape, rightShape, assocLeft, assocRight, binderFree, binderFreeList]
  · rw [leftShape]
    simp [assocLeft, matchPattern, matchArgs, mergeBindings]
  · rw [premises]
    exact .nil _
  · rw [rightShape]
    simp [assocRight, applyBindings]

/-- A detected binary commutativity schema earns symmetry of the generated
typed structural split for the whole authored language. -/
theorem authored_ac_split_commutative {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {former : Former} {equation : Equation}
    {firstName secondName : String}
    (base : BasePremiseEvaluator)
    (arity : former.declaration.params =
      [.simple firstName (.base former.declaration.category),
        .simple secondName (.base former.declaration.category)])
    (found : findCommutativity language former.declaration.label = some equation)
    (first second : Pattern → Prop) (term : Pattern) :
    SplitHolds language free bound (EquationEquiv base language) former first second term ↔
      SplitHolds language free bound (EquationEquiv base language) former second first term :=
  ac_split_commutative arity (equationSetoid base language).iseqv
    (fun left right _ _ => detected_commutative base found left right) first second term

/-- A detected association schema and derived contextual congruence earn the
associative separating law without an externally supplied association law. -/
theorem authored_ac_split_associative {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {former : Former} {equation : Equation}
    {firstName secondName : String}
    (base : BasePremiseEvaluator)
    (member : former ∈ structuralFormers language)
    (arity : former.declaration.params =
      [.simple firstName (.base former.declaration.category),
        .simple secondName (.base former.declaration.category)])
    (found : findAssociativity language former.declaration.label = some equation)
    (first second third : Pattern → Prop) (term : Pattern) :
    SplitHolds language free bound (EquationEquiv base language) former first
        (SplitHolds language free bound (EquationEquiv base language) former second third) term ↔
      SplitHolds language free bound (EquationEquiv base language) former
        (SplitHolds language free bound (EquationEquiv base language) former first second) third term := by
  apply ac_split_associative member arity (equationSetoid base language).iseqv
  · intro left left' right right' firstEquation secondEquation
    exact equationEquiv_apply_of_forall₂ former.declaration.label
      (.cons firstEquation (.cons secondEquation .nil))
  · intro left middle right _ _ _
    exact detected_associative base found left middle right

end Mettapedia.OSLF.NativeTypes.Structural
