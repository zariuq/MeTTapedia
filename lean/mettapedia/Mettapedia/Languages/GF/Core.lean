/-
# GF Core - Grammatical Framework Foundation

Core abstractions from the Grammatical Framework:
- Categories (types in the grammar)
- Abstract syntax (language-independent trees)
- Concrete syntax (language-specific linearization)
- Bisimulation equivalence (when trees mean the same thing)

## References
- GF Resource Grammar Library: ~/claude/gf-rgl/
- GF Tutorial: http://www.grammaticalframework.org/
-/

namespace Mettapedia.Languages.GF.Core

/-! ## Categories

GF categories represent grammatical types:
- Base categories: S (sentence), NP (noun phrase), CN (common noun), etc.
- Function categories: arrows between categories
-/

inductive Category where
  | base : String → Category
  | arrow : Category → Category → Category
  deriving DecidableEq, Repr

namespace Category

/-- Sentence category -/
def S : Category := base "S"

/-- Noun phrase -/
def NP : Category := base "NP"

/-- Common noun -/
def CN : Category := base "CN"

/-- Verb phrase -/
def VP : Category := base "VP"

/-- Adjective phrase -/
def AP : Category := base "AP"

/-- Adjective -/
def A : Category := base "A"

/-- Determiner -/
def Det : Category := base "Det"

end Category

/-! ## Abstract Syntax

Abstract syntax trees represent the meaning/structure independent of any specific language.
For MVP, we use a simplified representation without full dependent trees.
-/

/-- Abstract syntax tree with a category -/
structure AbstractTree where
  cat : Category
  /-- Tree identifier (for simplified MVP - full version would have constructor+args) -/
  id : Nat
  deriving DecidableEq, Repr


/-! ## Concrete Syntax

Concrete syntax maps abstract trees to strings in a specific language.
Linearization may depend on morphological parameters (case, number, gender, etc.).
-/

/-- Concrete form with parameterized linearization -/
structure ConcreteForm (Params : Type) where
  linearize : Params → String


/-! ## Grammar

A GF grammar consists of:
- Abstract syntax (categories and functions)
- Concrete syntax (linearization rules per category)
-/

/-- GF grammar with parameterized concrete syntax -/
structure Grammar (Params : Type) where
  /-- Name of the grammar -/
  name : String
  /-- Abstract categories in this grammar -/
  categories : List Category
  /-- Linearization function for each category -/
  concrete : Category → ConcreteForm Params


/-! ## Note on Bisimulation Equivalence

Proper linguistic bisimulation requires comparing tree *structure* and *linearization*,
not just category labels. The simplified `AbstractTree` type (category + id) is too
weak for this. Meaningful bisimulation is defined in:
- `Abstract.lean`: `NodeEquiv` for tree-structural equivalence
- `Czech/Properties.lean`: `LinguisticallyEquivalent` for inflectional equivalence
-/

end Mettapedia.Languages.GF.Core
