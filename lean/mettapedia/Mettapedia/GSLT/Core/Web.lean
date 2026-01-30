import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finite.Defs
import Mettapedia.GSLT.Core.LambdaTheoryCategory

/-!
# Webs and Coding Functions

This file formalizes webs and coding functions from Bucciarelli-Salibra
"Graph Lambda Theories" (2008).

## Main Definitions

* `Web` - An infinite set, the base of a graph model
* `CodingFunction` - Maps (finite subset, element) → element
* `GraphModel` - A web with a coding function D = (|D|, c_D)

## Key Insights from Bucciarelli-Salibra

A **graph model** D = (|D|, c_D) consists of:
- |D|: an infinite set (the "web")
- c_D: Pf(|D|) × |D| → |D| (the "coding function")

where Pf(X) denotes finite subsets of X.

The lambda-theory Th(D) induced by a graph model D is the set of
equations valid in D. Graph models provide a rich class of lambda-theories
including the sensible theories.

## References

- Bucciarelli & Salibra, "Graph Lambda Theories" (2008), Definition 2
- Engeler, "Algebras and combinators" (1981)
- Plotkin, "Set-theoretical and other elementary models of the λ-calculus" (1993)
-/

namespace Mettapedia.GSLT.Core

open Set Finset

/-! ## Webs

A web is an infinite set that serves as the base of a graph model.
-/

/-- A web is an infinite set.

    In Bucciarelli-Salibra, a web is simply |D| - an infinite set.
    We bundle the carrier with the proof of infiniteness.

    We require DecidableEq for operations on finite subsets.
-/
structure Web where
  /-- The carrier set -/
  carrier : Type*
  /-- Decidable equality on the carrier -/
  decEq : DecidableEq carrier
  /-- The carrier is infinite -/
  infinite : Infinite carrier

attribute [instance] Web.decEq

namespace Web

variable (W : Web)

/-- The carrier type of a web -/
abbrev Carrier := W.carrier

/-- A web has infinitely many elements -/
instance : Infinite W.carrier := W.infinite

/-- The finite power set Pf(|D|) - finite subsets of the web -/
def FiniteSubsets : Type* := Finset W.carrier

/-- A singleton web element as a finite subset -/
def singleton (x : W.carrier) : W.FiniteSubsets := ({x} : Finset W.carrier)

/-- The empty finite subset -/
def emptySubset : W.FiniteSubsets := (∅ : Finset W.carrier)

/-- Union of finite subsets -/
def unionSubsets (s t : W.FiniteSubsets) : W.FiniteSubsets := (s ∪ t : Finset W.carrier)

end Web

/-! ## Coding Functions

A coding function encodes (finite subset, element) pairs as elements.
-/

/-- A coding function for a web.

    The coding function c : Pf(|D|) × |D| → |D| is the key structure
    that allows representing lambda terms as graph elements.

    The pair (a, d) represents "d applied to arguments in a".
-/
structure CodingFunction (W : Web) where
  /-- The coding function itself -/
  code : W.FiniteSubsets × W.carrier → W.carrier
  /-- The coding function is injective (encoding is unambiguous) -/
  injective : Function.Injective code

namespace CodingFunction

variable {W : Web} (c : CodingFunction W)

/-- Apply the coding function -/
def apply (a : W.FiniteSubsets) (d : W.carrier) : W.carrier :=
  c.code (a, d)

/-- Notation for coding: c(a, d) -/
scoped notation:max c "⟨" a ", " d "⟩" => CodingFunction.apply c a d

/-- The range of the coding function -/
def range : Set W.carrier := Set.range c.code

/-- Elements not in the range (potential "atoms") -/
def atoms : Set W.carrier := c.rangeᶜ

/-- Injectivity means we can decode uniquely -/
theorem decode_unique {a₁ a₂ : W.FiniteSubsets} {d₁ d₂ : W.carrier}
    (h : c.code (a₁, d₁) = c.code (a₂, d₂)) : a₁ = a₂ ∧ d₁ = d₂ :=
  Prod.ext_iff.mp (c.injective h)

end CodingFunction

/-! ## Graph Models

A graph model combines a web with a coding function.
-/

/-- A graph model D = (|D|, c_D).

    Graph models are reflexive objects in the category of sets,
    providing models of untyped lambda calculus.

    The key property is that D ≅ (Pf(D) → D), giving self-application.
-/
structure GraphModel where
  /-- The underlying web -/
  web : Web
  /-- The coding function -/
  coding : CodingFunction web

namespace GraphModel

variable (D : GraphModel)

/-- The carrier of a graph model -/
abbrev Carrier := D.web.carrier

/-- Finite subsets of the carrier -/
abbrev FiniteSubsets := D.web.FiniteSubsets

/-- Apply coding -/
def code (a : D.FiniteSubsets) (d : D.Carrier) : D.Carrier :=
  D.coding.apply a d

/-- The "application" in a graph model: d applied to e.

    In graph models, application is defined as:
    d · e = { c(a, d') | (a, d') ∈ d, e ∈ a }

    For now, we define a simpler version using the coding function.
-/
def apply (_d e : D.Carrier) : Set D.Carrier :=
  { x | ∃ (a : Finset D.Carrier) (d' : D.Carrier),
        x = D.code a d' ∧ e ∈ a }

end GraphModel

/-! ## Graph Theory Induced by a Graph Model

The lambda-theory Th(D) induced by a graph model D is the set of
λ-equations valid in D.
-/

/-- A lambda-equation is a pair of lambda-terms.

    For simplicity, we represent terms as an abstract type.
    The full formalization would use de Bruijn indices or
    named variables with alpha-equivalence.
-/
structure LambdaEquation where
  /-- Left-hand side of the equation -/
  lhs : String  -- Placeholder; would be LambdaTerm
  /-- Right-hand side of the equation -/
  rhs : String  -- Placeholder; would be LambdaTerm

/-- The lambda-theory induced by a graph model.

    Th(D) = { M = N | ∀ρ. ⟦M⟧ρ = ⟦N⟧ρ in D }

    For now, we define this abstractly as a set of equations.
-/
def GraphModel.theory (_D : GraphModel) : Set LambdaEquation :=
  { _eq | True }  -- Placeholder; needs interpretation function

/-! ## Properties of Graph Theories

Key properties from Bucciarelli-Salibra:
- Sensibility: equates all unsolvable terms
- Semisensibility: unsolvable terms only equal unsolvables
-/

/-- A lambda-theory is sensible if all unsolvable terms are equal.

    Formally: Ω = I (or equivalently, Ω = λx.Ω)
    where Ω = (λx.xx)(λx.xx) is the paradigmatic unsolvable term.
-/
def LambdaTheorySensible (_T : Set LambdaEquation) : Prop :=
  -- Placeholder: would check that omega = arbitrary unsolvable
  True

/-- A lambda-theory is semisensible if unsolvable terms only equal unsolvables.

    This is weaker than sensibility: unsolvables form an equivalence class,
    but we don't require them all to be equal.
-/
def LambdaTheorySemisensible (_T : Set LambdaEquation) : Prop :=
  -- Placeholder: unsolvable = term implies term is unsolvable
  True

/-! ## Summary

This file establishes the foundational structures for graph models:

1. **Web**: Infinite set serving as the base
2. **CodingFunction**: Injective encoding (finite subset, element) → element
3. **GraphModel**: Web + coding function, D = (|D|, c_D)
4. **Th(D)**: Lambda-theory induced by a graph model

**Key Properties (to be formalized)**:
- Graph models satisfy all λβ-equations
- Sensible theories equate all unsolvable terms
- The Böhm theory B is the maximal sensible graph theory

**Next Steps**:
- Full lambda-term syntax with de Bruijn indices
- Interpretation function ⟦-⟧ : Term → D
- Böhm tree construction
- Weak product of graph models
-/

end Mettapedia.GSLT.Core
