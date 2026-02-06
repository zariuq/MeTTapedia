import Mathlib.Order.Heyting.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.CategoryTheory.LambdaTheory
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# MeTTaIL Semantic Interpretation

This file defines the interpretation domain for MeTTaIL language definitions:
objects, constructors, pattern interpretation, and well-formedness.

The actual categorical semantics (type systems, modal operators, Galois connections)
are constructed in:
- `Framework/RewriteSystem.lean` — abstract OSLF algorithm
- `Framework/RhoInstance.lean` — concrete ρ-calculus instance (0 sorries)

## References

- Williams & Stay, "Native Type Theory" (ACT 2021)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.MeTTaIL.Semantics

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Interpretation Domain -/

/-- The objects of the interpreted λ-theory are the type names -/
structure InterpObj (L : LanguageDef) where
  name : String
  isType : name ∈ L.types
deriving DecidableEq

namespace InterpObj

/-- Construct an object from a type name (if valid) -/
def mk? (L : LanguageDef) (name : String) : Option (InterpObj L) :=
  if h : name ∈ L.types then some ⟨name, h⟩ else none

/-- The first type is the "process" type by convention -/
def procType (L : LanguageDef) (h : L.types ≠ []) : InterpObj L :=
  ⟨L.types.head h, List.head_mem h⟩

end InterpObj

/-! ## Constructor Signatures -/

/-- A constructor's signature -/
structure ConstructorSig (L : LanguageDef) where
  name : String
  argTypes : List (InterpObj L)
  resultType : InterpObj L

/-! ## Pattern Interpretation -/

/-- A context for pattern interpretation -/
abbrev PatternContext (L : LanguageDef) := List (String × InterpObj L)

/-- Pattern interpretation result -/
inductive PatternInterp (L : LanguageDef) where
  | term : InterpObj L → PatternInterp L
  | error : String → PatternInterp L

/-- Interpret a pattern in a given context (simplified, non-recursive version) -/
def interpretPatternShallow (L : LanguageDef) (ctx : PatternContext L) :
    Pattern → PatternInterp L
  | .var name =>
    match ctx.find? (fun p => p.1 == name) with
    | some (_, ty) => .term ty
    | none => .error s!"Unbound variable: {name}"
  | .apply constructor _ =>
    match L.terms.find? (fun r => r.label == constructor) with
    | some rule =>
      match InterpObj.mk? L rule.category with
      | some ty => .term ty
      | none => .error s!"Invalid constructor type: {constructor}"
    | none => .error s!"Unknown constructor: {constructor}"
  | .lambda _ _ => .error "Lambda not supported in shallow interpretation"
  | .multiLambda _ _ => .error "MultiLambda not supported in shallow interpretation"
  | .subst _ _ _ => .error "Subst not supported in shallow interpretation"
  | .collection _ _ _ => .error "Collection not supported in shallow interpretation"

/-! ## Well-Formedness -/

/-- A well-formed language has at least one type -/
structure WellFormedLanguage where
  lang : LanguageDef
  hasTypes : lang.types ≠ []

/-! ## ρ-Calculus Facts -/

/-- The ρ-calculus is well-formed -/
def rhoCalc_wellFormed : WellFormedLanguage where
  lang := rhoCalc
  hasTypes := by simp [rhoCalc]

/-- The ρ-calculus has two types: Proc and Name -/
theorem rhoCalc_has_two_types : rhoCalc.types.length = 2 := by
  simp [rhoCalc]

/-- The process type in ρ-calculus is "Proc" -/
theorem rhoCalc_proc_type :
    (InterpObj.procType rhoCalc rhoCalc_wellFormed.hasTypes).name = "Proc" := by
  simp [InterpObj.procType, rhoCalc]

/-- The ρ-calculus has 6 constructors -/
theorem rhoCalc_has_six_constructors : rhoCalc.terms.length = 6 := by
  simp [rhoCalc]

end Mettapedia.OSLF.MeTTaIL.Semantics
