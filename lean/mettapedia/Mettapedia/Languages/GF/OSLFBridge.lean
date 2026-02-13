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
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.CategoryBridge

namespace Mettapedia.Languages.GF.OSLFBridge

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.Czech.Linearization
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Formula
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

/-- All GF RGL categories as Category values. -/
def allGFCategories : List Category :=
  Category.allCategoryNames.map Category.base

/-- All GF RGL grammar functions as OSLF grammar rules. -/
def allGFGrammarRules : List GrammarRule :=
  FunctionSig.allFunctions.map gfFunctionSigToGrammarRule

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

/-- UseComp elimination: UseComp(x) ~> x.
    Copula complement is identity wrapper. -/
def useCompElimRewrite : RewriteRule :=
  { name := "UseCompElim"
  , typeContext := [("x", TypeExpr.base "Comp")]
  , premises := []
  , left := .apply "UseComp" [.fvar "x"]
  , right := .fvar "x" }

/-- UseV elimination: UseV(x) ~> x.
    A bare verb used as VP is identity. -/
def useVElimRewrite : RewriteRule :=
  { name := "UseVElim"
  , typeContext := [("x", TypeExpr.base "V")]
  , premises := []
  , left := .apply "UseV" [.fvar "x"]
  , right := .fvar "x" }

/-- UseN2 elimination: UseN2(x) ~> x.
    Relational noun used as CN drops relational argument. -/
def useN2ElimRewrite : RewriteRule :=
  { name := "UseN2Elim"
  , typeContext := [("x", TypeExpr.base "N2")]
  , premises := []
  , left := .apply "UseN2" [.fvar "x"]
  , right := .fvar "x" }

/-- UseA2 elimination: UseA2(x) ~> x.
    Two-place adjective used as AP drops complement. -/
def useA2ElimRewrite : RewriteRule :=
  { name := "UseA2Elim"
  , typeContext := [("x", TypeExpr.base "A2")]
  , premises := []
  , left := .apply "UseA2" [.fvar "x"]
  , right := .fvar "x" }

/-- All identity-wrapper elimination rewrites.
    These give ◇/□ non-vacuous behavioral content. -/
def allIdentityRewrites : List RewriteRule :=
  [ useNElimRewrite, positAElimRewrite, useCompElimRewrite
  , useVElimRewrite, useN2ElimRewrite, useA2ElimRewrite ]

/-- The full GF RGL grammar as an OSLF LanguageDef.

    Includes all 169 core grammar functions and identity-wrapper
    elimination rewrites so that ◇/□ are non-vacuous:
    terms like `UseN(house)` can reduce to `house`, giving the modal
    operators actual behavioral content. -/
def gfRGLLanguageDef : LanguageDef :=
  { name := "GF_RGL"
  , types := Category.allCategoryNames
  , terms := allGFGrammarRules
  , equations := [useNIdentityEquation]
  , rewrites := allIdentityRewrites
  , congruenceCollections := [] }

/-- Czech GF grammar — same abstract syntax as full RGL but named for Czech. -/
def czechGFLanguageDef : LanguageDef := gfRGLLanguageDef

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

-- Verify: 169 core grammar functions, 70+ categories
#eval! do
  IO.println s!"GF RGL categories: {gfRGLLanguageDef.types.length}"
  IO.println s!"GF RGL grammar rules: {gfRGLLanguageDef.terms.length}"
  IO.println s!"GF RGL rewrites: {gfRGLLanguageDef.rewrites.length}"
  IO.println s!"FunctionSig.allCoreFunctions: {FunctionSig.allCoreFunctions.length}"

-- Test: UseN(house) reduces to house via UseNElim.
#eval! do
  let term := Pattern.apply "UseN" [.fvar "house"]
  let reducts := rewriteWithContextWithPremises gfRGLLanguageDef term
  IO.println s!"UseN(house) reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"  -> {r}"
  IO.println s!"  ◇ non-vacuous: {!reducts.isEmpty}"

-- Test: PositA(big) reduces to big via PositAElim.
#eval! do
  let term := Pattern.apply "PositA" [.fvar "big"]
  let reducts := rewriteWithContextWithPremises gfRGLLanguageDef term
  IO.println s!"PositA(big) reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"  -> {r}"

-- Test: UseV(sleep) reduces to sleep via UseVElim.
#eval! do
  let term := Pattern.apply "UseV" [.fvar "sleep"]
  let reducts := rewriteWithContextWithPremises gfRGLLanguageDef term
  IO.println s!"UseV(sleep) reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"  -> {r}"

-- Test: UseComp(warm) reduces to warm via UseCompElim.
#eval! do
  let term := Pattern.apply "UseComp" [.fvar "warm"]
  let reducts := rewriteWithContextWithPremises gfRGLLanguageDef term
  IO.println s!"UseComp(warm) reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"  -> {r}"

-- Test: bare leaf fvar "house" is irreducible (no ◇⊤).
#eval! do
  let term := Pattern.fvar "house"
  let reducts := rewriteWithContextWithPremises gfRGLLanguageDef term
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

/-! ## Phase 6: English GF → OSLF

English uses the same abstract syntax as Czech (GF RGL is language-independent
at the abstract level). The English LanguageDef is identical to Czech's —
the differentiation happens at the concrete linearization level.
-/

/-- English GF grammar — same abstract syntax, named for English. -/
def englishGFLanguageDef : LanguageDef :=
  { gfRGLLanguageDef with name := "EnglishGF" }

/-- The rewrite system generated from English GF grammar. -/
def englishGFRewriteSystem : RewriteSystem :=
  langRewriteSystem englishGFLanguageDef "S"

/-- The full OSLF type system for English GF. -/
def englishGFOSLF : OSLFTypeSystem englishGFRewriteSystem :=
  langOSLF englishGFLanguageDef "S"

/-- English gets a Galois connection for free (same as Czech). -/
theorem englishGF_galois :
    GaloisConnection
      (langDiamond englishGFLanguageDef)
      (langBox englishGFLanguageDef) :=
  langGalois englishGFLanguageDef

/-- English native type for the process sort "S". -/
def englishGFNativeType := langNativeType englishGFLanguageDef "S"

/-- English OSLF fiber family. -/
noncomputable abbrev englishGFOSLFFiberFamily :=
  langOSLFFiberFamily englishGFLanguageDef "S"

/-- English presheaf λ-theory. -/
noncomputable def englishGFPresheafLambdaTheory :=
  languagePresheafLambdaTheory englishGFLanguageDef

-- Verify key constructions type-check
#check gfRGLLanguageDef
#check czechGFOSLF
#check czechGF_galois
#check czechGFNativeType
#check czechGFOSLFFiberFamily
#check englishGFOSLF
#check englishGF_galois
#check englishGFNativeType
#check englishGFOSLFFiberFamily
#check @gfGrammarOSLF
#check @gfGrammar_galois

/-! ## Phase 8: GF Abstract Trees → OSLF Semantic Bridge

Connects GF abstract syntax trees to the OSLF formula checker and
denotational semantics. This is the theorem-level bridge from
GF term predicates to `checkLangUsing` / `sem`.

Pipeline:
```
AbstractNode →[gfAbstractToPattern]→ Pattern
  →[checkLangUsing gfRGLLanguageDef]→ CheckResult
  →[checkLangUsing_sat_sound]→ sem (langReduces gfRGLLanguageDef) I φ p
  →[langDiamond_spec]→ ◇/□ modal satisfaction
```
-/

open Mettapedia.OSLF.MeTTaIL.Engine

/-- If `checkLangUsing` returns `.sat` on a GF abstract tree converted to
    a Pattern, then the formula's denotational semantics hold for that tree.

    This is the master bridge: GF abstract syntax → OSLF semantics. -/
theorem gfAbstract_checkSat_sound
    {lang : LanguageDef}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {node : AbstractNode} {φ : OSLFFormula}
    (h : checkLangUsing .empty lang I_check fuel
           (gfAbstractToPattern node) φ = .sat) :
    sem (langReduces lang) I_sem φ (gfAbstractToPattern node) := by
  exact checkLangUsing_sat_sound h_atoms h

/-- If a GF abstract tree reduces under the RGL language, then the
    OSLF diamond modality witnesses that reduction.

    ◇(φ)(tree) holds when tree ⇝ q and φ(q). -/
theorem gfAbstract_diamond_of_reduces
    {lang : LanguageDef}
    {φ : Pattern → Prop} {node : AbstractNode} {q : Pattern}
    (hReduce : langReduces lang (gfAbstractToPattern node) q)
    (hφ : φ q) :
    langDiamond lang φ (gfAbstractToPattern node) := by
  rw [langDiamond_spec]
  exact ⟨q, hReduce, hφ⟩

/-- Executable reduction on a GF tree implies the declarative relation.

    Uses the soundness/completeness bridge: if the rewrite engine produces
    `q` from the Pattern of a GF tree, then `langReduces` holds. -/
theorem gfAbstract_exec_implies_reduces
    {lang : LanguageDef} {node : AbstractNode} {q : Pattern}
    (h : q ∈ rewriteWithContextWithPremises lang (gfAbstractToPattern node)) :
    langReduces lang (gfAbstractToPattern node) q := by
  exact exec_to_langReducesUsing .empty lang
    (show langReducesExecUsing .empty lang (gfAbstractToPattern node) q from h)

/-- Combining exec + diamond: if the engine reduces a GF tree to q,
    and φ(q) holds, then ◇(φ)(tree) holds in the OSLF type system.

    This is the practical bridge: run the rewriter, get a reduct,
    check a predicate on it, conclude ◇-satisfaction. -/
theorem gfAbstract_diamond_of_exec
    {lang : LanguageDef}
    {φ : Pattern → Prop} {node : AbstractNode} {q : Pattern}
    (hExec : q ∈ rewriteWithContextWithPremises lang (gfAbstractToPattern node))
    (hφ : φ q) :
    langDiamond lang φ (gfAbstractToPattern node) :=
  gfAbstract_diamond_of_reduces (gfAbstract_exec_implies_reduces hExec) hφ

/-! ### Concrete GF → OSLF checker demonstrations -/

section GFCheckerDemo

/-- Atom check: pattern matches a specific free variable name -/
def gfAtomCheck_isName (target : String) : AtomCheck :=
  fun _a p => match p with
    | .fvar n => n == target
    | _ => false

/-- Atom semantics: pattern IS the named free variable -/
def gfAtomSem_isName (target : String) : AtomSem :=
  fun _a p => p = .fvar target

/-- Soundness: the atom check implies the atom semantics -/
theorem gfAtomCheck_isName_sound (target : String) :
    ∀ a p, gfAtomCheck_isName target a p = true → gfAtomSem_isName target a p := by
  intro a p h
  simp only [gfAtomCheck_isName] at h
  simp only [gfAtomSem_isName]
  match p with
  | .fvar n =>
    simp [BEq.beq] at h
    exact congrArg Pattern.fvar h
  | .apply _ _ => simp at h
  | .collection _ _ _ => simp at h

end GFCheckerDemo

-- Check ◇(is_house) on UseN(house):
-- UseN(house) ⇝ house (via UseNElim), and house is house.
-- The checker should return `.sat`.
#eval! do
  let tree := AbstractNode.apply
    { name := "UseN", type := .arrow (.base "N") (.base "CN") }
    [.leaf "house" (.base "N")]
  let pat := gfAbstractToPattern tree
  let φ := OSLFFormula.dia (.atom "is_house")
  let result := checkLangUsing .empty gfRGLLanguageDef
    (gfAtomCheck_isName "house") 3 pat φ
  IO.println s!"UseN(house) |= ◇(is_house): {repr result}"

-- Check ◇(is_big) on PositA(big):
-- PositA(big) ⇝ big (via PositAElim), and big is big.
#eval! do
  let tree := AbstractNode.apply
    { name := "PositA", type := .arrow (.base "A") (.base "AP") }
    [.leaf "big" (.base "A")]
  let pat := gfAbstractToPattern tree
  let φ := OSLFFormula.dia (.atom "is_big")
  let result := checkLangUsing .empty gfRGLLanguageDef
    (gfAtomCheck_isName "big") 3 pat φ
  IO.println s!"PositA(big) |= ◇(is_big): {repr result}"

-- Check that irreducible terms do NOT satisfy ◇:
-- bare "house" has no reducts, so ◇(anything) is unsat.
#eval! do
  let pat := Pattern.fvar "house"
  let φ := OSLFFormula.dia (.atom "is_house")
  let result := checkLangUsing .empty gfRGLLanguageDef
    (gfAtomCheck_isName "house") 3 pat φ
  IO.println s!"house |= ◇(is_house): {repr result}"
  -- Expected: .unsat (no reducts to check)

end Mettapedia.Languages.GF.OSLFBridge
