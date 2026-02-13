/-
# GF → OSLF Bridge: Types for GF Languages

Expresses GF grammars as OSLF LanguageDef instances so the OSLF pipeline
automatically generates a spatial-behavioral type system (◇, □, Galois
connection, native types) for any GF-defined grammar.

## Pipeline

```
GF Grammar ──→ LanguageDef ──→ langOSLF ──→ OSLFTypeSystem
  (Category,     (types,         (Pred, ◇, □,
   FunctionSig,   GrammarRule,    Galois connection)
   AbstractNode)  Pattern)
```

## Key Design

- GF Categories → OSLF sorts (preserving arrow structure via encoding)
- GF FunctionSigs → OSLF GrammarRules (with fresh arg0/arg1/... names)
- GF equations (UseN identity) → OSLF equations
- GF rewrites (agreement normalization) → OSLF rewrites (non-vacuous ◇/□)

## References

- GF Tutorial: http://www.grammaticalframework.org/
- Meredith & Stay, "Operational Semantics in Logical Form"
- Williams & Stay, "Native Type Theory" (ACT 2021)
-/

import Mettapedia.Languages.GF.Abstract
import Mettapedia.Languages.GF.Core
import Mettapedia.Languages.GF.Czech.Linearization
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.CategoryBridge

namespace Mettapedia.Languages.GF.OSLFBridge

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.Czech.Linearization
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.CategoryBridge

/-! ## Phase 1: GF Grammar → LanguageDef

Convert GF abstract syntax structures into OSLF LanguageDef components.
-/

/-- Encode a GF Category as a string sort name, preserving arrow structure.
    `Category.base "S"` → `"S"`
    `Category.arrow (base "Det") (arrow (base "CN") (base "NP"))`
      → `"Det→CN→NP"` -/
@[reducible] def gfCategoryToType : Category → String
  | .base s => s
  | .arrow dom rest => gfCategoryToType dom ++ "→" ++ gfCategoryToType rest

/-- Collect all base category names from a function type's arguments.
    `Det → CN → NP` yields `["Det", "CN"]` -/
@[reducible] def gfCategoryArgs : Category → List String
  | .base _ => []
  | .arrow dom rest => gfCategoryToType dom :: gfCategoryArgs rest

/-- Extract the result category name from a function type.
    `Det → CN → NP` yields `"NP"` -/
@[reducible] def gfCategoryResult : Category → String
  | .base s => s
  | .arrow _ rest => gfCategoryResult rest

/-- Generate a fresh argument name from an index. -/
private def argName (i : Nat) : String := s!"arg{i}"

/-- Convert a GF FunctionSig into an OSLF GrammarRule.
    Uses fresh arg0/arg1/... names to avoid duplicates when
    a function has repeated argument categories. -/
@[reducible] def gfFunctionSigToGrammarRule (f : FunctionSig) : GrammarRule :=
  let args := gfCategoryArgs f.type
  let indexed := args.zip (List.range args.length)
  let params := indexed.map fun ⟨cat, i⟩ =>
    TermParam.simple (argName i) (TypeExpr.base cat)
  let synPat := indexed.map fun ⟨_, i⟩ =>
    SyntaxItem.nonTerminal (argName i)
  { label := f.name
  , category := gfCategoryResult f.type
  , params := params
  , syntaxPattern := synPat }

/-- Convert a GF AbstractNode to an OSLF Pattern.
    - Leaves become free variables (Pattern.fvar)
    - Applications become Pattern.apply with the function name -/
def gfAbstractToPattern : AbstractNode → Pattern
  | .leaf name _ => .fvar name
  | .apply f args => .apply f.name (args.map gfAbstractToPattern)

/-- Build an OSLF LanguageDef from GF abstract syntax components. -/
def gfGrammarLanguageDef
    (name : String)
    (cats : List Category)
    (funs : List FunctionSig)
    (rewrites : List RewriteRule := [])
    (equations : List Equation := []) : LanguageDef :=
  { name := name
  , types := cats.map gfCategoryToType
  , terms := funs.map gfFunctionSigToGrammarRule
  , equations := equations
  , rewrites := rewrites
  , congruenceCollections := [] }

/-! ## Phase 2: Czech GF Fragment as LanguageDef

A concrete Czech GF grammar with non-trivial rewrite dynamics.

### GF Equations (bidirectional)

- **UseN identity**: `UseN(x) = x` — In Czech, N and CN are the same
  (no articles), so UseN is the identity function.

### GF Rewrites (directional reductions)

- **UseN elimination**: `UseN(x) ~> x` — Simplify by removing identity wrapper.
  This gives the OSLF ◇/□ non-trivial behavior: a term `UseN(house)` CAN
  reduce to `house`, so `◇(is_house)(UseN(house))` holds.
- **PositA elimination**: `PositA(x) ~> x` — Positive degree is identity.
  `PositA(big)` reduces to `big`.
-/

/-- Czech GF abstract categories. -/
def czechGFCategories : List Category :=
  [Category.S, Category.NP, Category.CN, Category.VP,
   Category.Det, Category.A, Category.AP, .base "N"]

/-- Czech GF abstract functions as OSLF grammar rules. -/
def czechGFGrammarRules : List GrammarRule :=
  ([ FunctionSig.DetCN
   , FunctionSig.PredVP
   , FunctionSig.UseN
   , FunctionSig.ModCN
   , FunctionSig.PositA
   ]).map gfFunctionSigToGrammarRule

/-- UseN elimination: UseN(x) ~> x.
    In Czech, N = CN (no articles), so UseN is identity.
    This is the directional version of the GF equation. -/
def useNElimRewrite : RewriteRule :=
  { name := "UseNElim"
  , typeContext := [("x", TypeExpr.base "N")]
  , premises := []
  , left := .apply "UseN" [.fvar "x"]
  , right := .fvar "x" }

/-- PositA elimination: PositA(x) ~> x.
    Positive adjective degree is identity in Czech. -/
def positAElimRewrite : RewriteRule :=
  { name := "PositAElim"
  , typeContext := [("x", TypeExpr.base "A")]
  , premises := []
  , left := .apply "PositA" [.fvar "x"]
  , right := .fvar "x" }

/-- UseN identity equation: UseN(x) = x. -/
def useNIdentityEquation : Equation :=
  { name := "UseNIdentity"
  , typeContext := [("x", TypeExpr.base "N")]
  , premises := []
  , left := .apply "UseN" [.fvar "x"]
  , right := .fvar "x" }

/-- The Czech GF grammar as an OSLF LanguageDef with non-trivial dynamics.

    Includes UseN/PositA elimination rewrites so that ◇/□ are non-vacuous:
    terms like `UseN(house)` can reduce to `house`, giving the modal
    operators actual behavioral content. -/
def czechGFLanguageDef : LanguageDef :=
  { name := "CzechGF"
  , types := ["S", "NP", "CN", "VP", "Det", "A", "AP", "N"]
  , terms := czechGFGrammarRules
  , equations := [useNIdentityEquation]
  , rewrites := [useNElimRewrite, positAElimRewrite]
  , congruenceCollections := [] }

/-! ## Phase 3: OSLF Type System for Czech GF

Apply the pipeline. The Galois connection ◇ ⊣ □ is automatic.
-/

/-- The rewrite system generated from Czech GF grammar.
    Sorts = String, procSort = "S" (sentences are the process sort). -/
def czechGFRewriteSystem : RewriteSystem :=
  langRewriteSystem czechGFLanguageDef "S"

/-- The full OSLF type system for Czech GF. -/
def czechGFOSLF : OSLFTypeSystem czechGFRewriteSystem :=
  langOSLF czechGFLanguageDef "S"

/-- The Galois connection ◇ ⊣ □ for Czech GF — proven automatically. -/
theorem czechGF_galois :
    GaloisConnection
      (langDiamond czechGFLanguageDef)
      (langBox czechGFLanguageDef) :=
  langGalois czechGFLanguageDef

/-- Native types for Czech GF: (sort, predicate) pairs. -/
def czechGFNativeType := langNativeType czechGFLanguageDef "S"

/-! ## Phase 4: Non-Vacuous Modal Tests

Executable tests demonstrating that ◇/□ have actual behavioral content.
-/

section ModalTests
open Mettapedia.OSLF.MeTTaIL.Engine

-- Test: UseN(house) reduces to house via UseNElim.
#eval! do
  let term := Pattern.apply "UseN" [.fvar "house"]
  let reducts := rewriteWithContextWithPremises czechGFLanguageDef term
  IO.println s!"UseN(house) reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"  -> {r}"
  IO.println s!"  ◇ non-vacuous: {!reducts.isEmpty}"

-- Test: PositA(big) reduces to big via PositAElim.
#eval! do
  let term := Pattern.apply "PositA" [.fvar "big"]
  let reducts := rewriteWithContextWithPremises czechGFLanguageDef term
  IO.println s!"PositA(big) reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"  -> {r}"

-- Test: bare leaf fvar "house" is irreducible (no ◇⊤).
#eval! do
  let term := Pattern.fvar "house"
  let reducts := rewriteWithContextWithPremises czechGFLanguageDef term
  IO.println s!"house reducts ({reducts.length}): irreducible = {reducts.isEmpty}"

end ModalTests

/-! ## Phase 5: Bridge Theorems -/

/-- gfAbstractToPattern on a leaf is a free variable. -/
@[simp] theorem gfAbstractToPattern_leaf (name : String) (cat : Category) :
    gfAbstractToPattern (.leaf name cat) = Pattern.fvar name := by
  simp [gfAbstractToPattern]

/-- gfAbstractToPattern on an application is Pattern.apply. -/
@[simp] theorem gfAbstractToPattern_apply (f : FunctionSig) (args : List AbstractNode) :
    gfAbstractToPattern (.apply f args) =
    Pattern.apply f.name (args.map gfAbstractToPattern) := by
  simp [gfAbstractToPattern]

/-- gfCategoryResult extracts the result from a simple base category. -/
@[simp] theorem gfCategoryResult_base (s : String) :
    gfCategoryResult (.base s) = s := by
  simp [gfCategoryResult]

/-- gfCategoryResult extracts the final result from an arrow type. -/
@[simp] theorem gfCategoryResult_arrow (dom rest : Category) :
    gfCategoryResult (.arrow dom rest) = gfCategoryResult rest := by
  simp [gfCategoryResult]

/-- gfCategoryToType preserves base category names. -/
@[simp] theorem gfCategoryToType_base (s : String) :
    gfCategoryToType (.base s) = s := by
  simp [gfCategoryToType]

/-- gfCategoryToType encodes arrows with "→". -/
theorem gfCategoryToType_arrow (dom rest : Category) :
    gfCategoryToType (.arrow dom rest) =
    gfCategoryToType dom ++ "→" ++ gfCategoryToType rest := by
  simp [gfCategoryToType]

/-- NodeEquiv under Czech linearization implies identical surface forms
    for all morphological parameters. This is a linearization-level
    equivalence, not an OSLF reduction-level one. -/
theorem gfNodeEquiv_surface_eq
    (env : CzechLinEnv) (n₁ n₂ : AbstractNode)
    (h : Abstract.NodeEquiv (czechLinearize env) n₁ n₂)
    (φ : String → Prop) (params : Czech.CzechParams) :
    φ (czechLinearize env n₁ params) ↔ φ (czechLinearize env n₂ params) := by
  rw [h params]

/-! ## Phase 6: Category Bridge Integration -/

/-- OSLF fiber families indexed by Czech GF sorts. -/
abbrev czechGFOSLFFiberFamily := langOSLFFiberFamily czechGFLanguageDef "S"

/-- Predicate fibration over Czech GF sorts (presheaf-topos primary). -/
noncomputable def czechGFPredFibration :=
  predFibration czechGFRewriteSystem

/-- Agreement: OSLF fibers coincide with presheaf-primary backend. -/
noncomputable def czechGF_presheafAgreement :=
  langOSLFFibrationUsing_presheafAgreement czechGFLanguageDef "S"

/-- Language presheaf λ-theory for Czech GF. -/
noncomputable def czechGFPresheafLambdaTheory :=
  languagePresheafLambdaTheory czechGFLanguageDef

/-- Modal adjunction ◇ ⊣ □ for Czech GF as a categorical adjunction. -/
noncomputable def czechGFModalAdjunction :=
  langModalAdjunction czechGFLanguageDef

/-! ## Phase 7: Generic GF Grammar → OSLF Pipeline -/

/-- Given any list of GF categories and functions, produce an OSLF type system. -/
noncomputable def gfGrammarOSLF
    (name : String)
    (cats : List Category)
    (funs : List FunctionSig)
    (procSort : String := "S") :
    OSLFTypeSystem (langRewriteSystem (gfGrammarLanguageDef name cats funs) procSort) :=
  langOSLF (gfGrammarLanguageDef name cats funs) procSort

/-- Any GF grammar gets a Galois connection for free. -/
theorem gfGrammar_galois
    (name : String)
    (cats : List Category)
    (funs : List FunctionSig) :
    GaloisConnection
      (langDiamond (gfGrammarLanguageDef name cats funs))
      (langBox (gfGrammarLanguageDef name cats funs)) :=
  langGalois (gfGrammarLanguageDef name cats funs)

/-- Any GF grammar gets a presheaf λ-theory for free. -/
noncomputable def gfGrammarPresheafLambdaTheory
    (name : String)
    (cats : List Category)
    (funs : List FunctionSig) :=
  languagePresheafLambdaTheory (gfGrammarLanguageDef name cats funs)

-- Verify key constructions type-check
#check czechGFOSLF
#check czechGF_galois
#check czechGFNativeType
#check czechGFOSLFFiberFamily
#check @gfGrammarOSLF
#check @gfGrammar_galois

end Mettapedia.Languages.GF.OSLFBridge
