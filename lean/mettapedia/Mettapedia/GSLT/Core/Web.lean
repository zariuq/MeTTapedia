import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finite.Defs
import Mathlib.Order.ScottContinuity
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

- Bucciarelli & Salibra, "Graph Lambda Theories" (2008), §2.3
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

    The pair (a, d) records output d supported by the finite input a.
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

/-- A graph model D = (|D|, c_D). Its semantic domain is the powerset
of the web, ordered by inclusion. Finite-input coding gives a retraction
of Scott-continuous endomaps into that domain, not an isomorphism of the
web with a set-theoretic function space. -/
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

/-- Application on the powerset domain: an output belongs when a coded
finite input is contained in the argument and its code belongs to the
function. This is F(X)(Y) in the source graph-model semantics. -/
def apply (functions arguments : Set D.Carrier) : Set D.Carrier :=
  { x | ∃ a : Finset D.Carrier,
      (↑a : Set D.Carrier) ⊆ arguments ∧ D.code a x ∈ functions }

/-- Finite-input graph encoding G(f). It is defined for every set function;
the retraction law below requires actual Scott continuity. -/
def abstraction (f : Set D.Carrier → Set D.Carrier) : Set D.Carrier :=
  { token | ∃ (a : Finset D.Carrier) (x : D.Carrier),
      token = D.code a x ∧ x ∈ f (↑a : Set D.Carrier) }

@[simp]
theorem code_mem_abstraction (f : Set D.Carrier → Set D.Carrier)
    (a : Finset D.Carrier) (x : D.Carrier) :
    D.code a x ∈ D.abstraction f ↔ x ∈ f (↑a : Set D.Carrier) := by
  constructor
  · rintro ⟨b, y, hCode, hy⟩
    obtain ⟨rfl, rfl⟩ := D.coding.decode_unique hCode
    exact hy
  · intro hx
    exact ⟨a, x, rfl, hx⟩

theorem apply_mono {functions functions' arguments arguments' : Set D.Carrier}
    (hFunctions : functions ⊆ functions') (hArguments : arguments ⊆ arguments') :
    D.apply functions arguments ⊆ D.apply functions' arguments' := by
  rintro x ⟨a, ha, hx⟩
  exact ⟨a, ha.trans hArguments, hFunctions hx⟩

theorem abstraction_mono {f g : Set D.Carrier → Set D.Carrier}
    (h : ∀ arguments, f arguments ⊆ g arguments) :
    D.abstraction f ⊆ D.abstraction g := by
  rintro token ⟨a, x, rfl, hx⟩
  exact ⟨a, x, rfl, h _ hx⟩

@[simp]
theorem apply_empty (arguments : Set D.Carrier) : D.apply ∅ arguments = ∅ := by
  ext x
  simp [apply]

/-- The exact finite-observation law, without a continuity hypothesis. -/
theorem mem_apply_abstraction (f : Set D.Carrier → Set D.Carrier)
    (arguments : Set D.Carrier) (x : D.Carrier) :
    x ∈ D.apply (D.abstraction f) arguments ↔
      ∃ a : Finset D.Carrier, (↑a : Set D.Carrier) ⊆ arguments ∧ x ∈ f ↑a := by
  simp only [apply, Set.mem_ofPred_eq, code_mem_abstraction]

/-- Monotonicity alone gives only the forward inclusion. -/
theorem apply_abstraction_subset (f : Set D.Carrier → Set D.Carrier)
    (h : Monotone f) (arguments : Set D.Carrier) :
    D.apply (D.abstraction f) arguments ⊆ f arguments := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := (D.mem_apply_abstraction f arguments x).mp hx
  exact h ha hx

/-- Powerset Scott continuity entails support by a finite subargument. -/
theorem finite_support_of_scottContinuous (f : Set D.Carrier → Set D.Carrier)
    (h : ScottContinuous f) (arguments : Set D.Carrier) (x : D.Carrier) :
    x ∈ f arguments ↔
      ∃ a : Finset D.Carrier, (↑a : Set D.Carrier) ⊆ arguments ∧ x ∈ f ↑a := by
  constructor
  · intro hx
    let finiteInputs : Set (Set D.Carrier) :=
      { input | ∃ a : Finset D.Carrier, (↑a : Set D.Carrier) ⊆ arguments ∧ input = ↑a }
    have hNonempty : finiteInputs.Nonempty :=
      ⟨∅, ∅, by simp, by simp⟩
    have hDirected : DirectedOn (· ≤ ·) finiteInputs := by
      rintro A ⟨a, ha, rfl⟩ B ⟨b, hb, rfl⟩
      refine ⟨↑(a ∪ b), ⟨a ∪ b, ?_, rfl⟩, ?_, ?_⟩
      · simpa only [Finset.coe_union] using Set.union_subset ha hb
      · exact_mod_cast Finset.subset_union_left
      · exact_mod_cast Finset.subset_union_right
    have hLub : IsLUB finiteInputs arguments := by
      constructor
      · rintro A ⟨a, ha, rfl⟩
        exact ha
      · intro upper hUpper y hy
        have hSingleton : ({y} : Set D.Carrier) ∈ finiteInputs :=
          ⟨({y} : Finset D.Carrier), by simpa using hy, by simp⟩
        exact hUpper hSingleton (by simp)
    have hImageLub := h hNonempty hDirected hLub
    have hUnion : f arguments = ⋃₀ (f '' finiteInputs) :=
      hImageLub.unique (isLUB_sSup (f '' finiteInputs))
    rw [hUnion] at hx
    obtain ⟨_, ⟨input, ⟨a, ha, rfl⟩, rfl⟩, hx⟩ := hx
    exact ⟨a, ha, hx⟩
  · rintro ⟨a, ha, hx⟩
    exact h.monotone ha hx

/-- The source retraction F(G(f)) = f for Scott-continuous f. -/
theorem apply_abstraction (f : Set D.Carrier → Set D.Carrier)
    (h : ScottContinuous f) (arguments : Set D.Carrier) :
    D.apply (D.abstraction f) arguments = f arguments := by
  ext x
  exact (D.mem_apply_abstraction f arguments x).trans
    (D.finite_support_of_scottContinuous f h arguments x).symm

/-- Every decoded graph is genuinely Scott-continuous in its argument. -/
theorem scottContinuous_apply (functions : Set D.Carrier) :
    ScottContinuous (D.apply functions) := by
  intro family hNonempty hDirected arguments hLub
  constructor
  · rintro _ ⟨input, hInput, rfl⟩
    exact D.apply_mono (by rfl) (hLub.1 hInput)
  · intro upper hUpper x hx
    obtain ⟨a, ha, hx⟩ := hx
    have hUnion : arguments = ⋃₀ family := hLub.unique (isLUB_sSup family)
    rw [hUnion] at ha
    obtain ⟨input, hInput, ha⟩ :=
      hDirected.exists_mem_subset_of_finite_of_subset_sUnion hNonempty a.finite_toSet ha
    exact hUpper (Set.mem_image_of_mem (D.apply functions) hInput) ⟨a, ha, hx⟩

/-- Application is Scott-continuous jointly in function and argument. -/
theorem scottContinuous_apply_pair :
    ScottContinuous (fun inputs : Set D.Carrier × Set D.Carrier =>
      D.apply inputs.1 inputs.2) := by
  intro family hNonempty hDirected inputs hLub
  constructor
  · rintro _ ⟨input, hInput, rfl⟩
    exact D.apply_mono (hLub.1 hInput).1 (hLub.1 hInput).2
  · intro upper hUpper x hx
    obtain ⟨a, ha, hx⟩ := hx
    have hLeftLub := (isLUB_prod.mp hLub).1
    have hRightLub := (isLUB_prod.mp hLub).2
    have hLeftUnion : inputs.1 = ⋃₀ (Prod.fst '' family) :=
      hLeftLub.unique (isLUB_sSup _)
    have hRightUnion : inputs.2 = ⋃₀ (Prod.snd '' family) :=
      hRightLub.unique (isLUB_sSup _)
    rw [hLeftUnion] at hx
    obtain ⟨_, ⟨left, hLeft, rfl⟩, hx⟩ := hx
    rw [hRightUnion] at ha
    have hRightNonempty : (Prod.snd '' family).Nonempty := hNonempty.image _
    have hRightDirected : DirectedOn (· ⊆ ·) (Prod.snd '' family) :=
      DirectedOn.mono_comp (g := Prod.snd) (fun {_ _} h => h.2) hDirected
    obtain ⟨_, ⟨right, hRight, rfl⟩, ha⟩ :=
      hRightDirected.exists_mem_subset_of_finite_of_subset_sUnion hRightNonempty
        a.finite_toSet ha
    obtain ⟨both, hBoth, hLeftBoth, hRightBoth⟩ := hDirected left hLeft right hRight
    exact hUpper (Set.mem_image_of_mem _ hBoth)
      ⟨a, ha.trans hRightBoth.2, hLeftBoth.1 hx⟩

/-- Finite graph encoding preserves directed suprema in pointwise function order. -/
theorem scottContinuous_abstraction :
    ScottContinuous (D.abstraction : (Set D.Carrier → Set D.Carrier) → Set D.Carrier) := by
  intro family _ _ f hLub
  constructor
  · rintro _ ⟨g, hg, rfl⟩
    exact D.abstraction_mono (hLub.1 hg)
  · intro upper hUpper token hx
    obtain ⟨a, x, rfl, hx⟩ := hx
    have hAtLub := (isLUB_pi.mp hLub) (↑a : Set D.Carrier)
    have hUnion : f ↑a = ⋃₀ ((fun g => g (↑a : Set D.Carrier)) '' family) :=
      hAtLub.unique (isLUB_sSup _)
    rw [hUnion] at hx
    obtain ⟨_, ⟨g, hg, rfl⟩, hx⟩ := hx
    exact hUpper (Set.mem_image_of_mem _ hg) ⟨a, x, rfl, hx⟩

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
  lhs : String  -- Current external carrier; interpreted through `Semantics`.
  /-- Right-hand side of the equation -/
  rhs : String

/-- The semantic data needed to interpret the current external term carrier
(`String`) in a graph model.  A future intrinsic lambda-term syntax can
instantiate the same boundary with its own environment type and interpreter. -/
structure GraphModel.Semantics (D : GraphModel) where
  /-- Valuation environments for free variables. -/
  Environment : Type*
  /-- Interpretation of one external term under an environment. -/
  interpret : String → Environment → Set D.Carrier

/-- Equality of external terms under an explicitly supplied powerset interpretation.
Lambda-theory closure additionally requires congruence and β-validity of that
interpretation; neither follows from this unrestricted data record alone.

`Th(D) = { M = N | ∀ρ, ⟦M⟧ρ = ⟦N⟧ρ in D }`.
-/
def GraphModel.theory (D : GraphModel) (semantics : D.Semantics) :
    Set LambdaEquation :=
  { equation | ∀ environment,
      semantics.interpret equation.lhs environment =
        semantics.interpret equation.rhs environment }

/-! ## Properties of Graph Theories

Key properties from Bucciarelli-Salibra:
- Sensibility: equates all unsolvable terms
- Semisensibility: unsolvable terms only equal unsolvables
-/

/-- All unsolvable terms are equated, for an explicitly supplied predicate.
The source's notion of a sensible lambda theory additionally requires
consistency. It may equate Ω with λx.Ω, but not with the solvable identity I. -/
def LambdaTheorySensible (Unsolvable : String → Prop)
    (T : Set LambdaEquation) : Prop :=
  ∀ left right, Unsolvable left → Unsolvable right →
    ({ lhs := left, rhs := right } : LambdaEquation) ∈ T

/-- Every admitted equation preserves the supplied unsolvability predicate.
This does not require equating all unsolvable terms; neither implication
between these two raw relation predicates holds without further hypotheses. -/
def LambdaTheorySemisensible (Unsolvable : String → Prop)
    (T : Set LambdaEquation) : Prop :=
  ∀ equation ∈ T, Unsolvable equation.lhs ↔ Unsolvable equation.rhs

/-! ## Predicate controls -/

/-- Every pair of unsolvable terms belongs to the total theory. -/
example (Unsolvable : String → Prop) :
    LambdaTheorySensible Unsolvable Set.univ := by
  intro left right leftUnsolvable rightUnsolvable
  simp

/-- The empty theory is semisensible because it equates no terms. -/
example (Unsolvable : String → Prop) :
    LambdaTheorySemisensible Unsolvable ∅ := by
  intro equation membership
  cases membership

/-- Sensibility is not automatic: the empty theory fails when an
unsolvable term exists. -/
example :
    ¬ LambdaTheorySensible (fun term => term = "Omega") ∅ := by
  intro sensible
  have membership := sensible "Omega" "Omega" rfl rfl
  simp at membership

/-- Semisensibility is also substantive: the total theory equates an
unsolvable term with a selected solvable one. -/
example :
    ¬ LambdaTheorySemisensible (fun term => term = "Omega") Set.univ := by
  intro semisensible
  have preserves := semisensible
    ({ lhs := "Omega", rhs := "I" } : LambdaEquation) (by simp)
  have : ("I" : String) = "Omega" := preserves.mp rfl
  contradiction

/-! ## Summary

This file establishes the foundational structures for graph models:

1. **Web**: Infinite set serving as the base
2. **CodingFunction**: Injective encoding (finite subset, element) → element
3. **GraphModel**: Web + coding function, D = (|D|, c_D)
4. **Th(D)**: External equations valid under a supplied powerset interpretation

**Key Properties (to be formalized)**:
- Graph models satisfy all λβ-equations
- Sensible theories equate all unsolvable terms
- The Böhm theory B is the maximal sensible graph theory

**Next Steps**:
- Full lambda-term syntax with de Bruijn indices
- Interpretation function ⟦-⟧ : Term → Env → P(D)
- Böhm tree construction
- Weak product of graph models
-/

end Mettapedia.GSLT.Core
