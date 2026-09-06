/-
# GF syntax classification and OSLF semantic typing

Connects GF abstract syntax trees to the OSLF type system at the
theorem level. Provides:

1. **Sort assignment**: every GF abstract tree gets an OSLF sort
2. **Syntax classifiers**: constructor-sensitive predicates for parsing
3. **Semantic native types**: modulo-equations predicates for OSLF
4. **Parse disambiguation**: different abstract trees → different syntax classes
5. **Multi-sorted examples**: exercising N, CN, NP, VP, S sorts

## Pipeline

```
AbstractNode → Pattern → syntax classifier
                         └→ closure under equations → OSLF native type
```

## References
- Williams & Stay, "Native Type Theory" (ACT 2021)
- OSLFBridge.lean: GF → LanguageDef conversion
- TypeSynthesis.lean: langOSLF, langNativeType, NativeTypeOf
-/

import Mettapedia.Languages.GF.OSLFBridge_handcrafted

namespace Mettapedia.Languages.GF.Typing

open Mettapedia.Languages.GF.HandCrafted.Core
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.RewriteSystem
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-! ## Sort Assignment

Every GF abstract tree has a result category (sort).
Leaves carry their category annotation; applications use
the function signature's result category.
-/

/-- Extract the result category (sort) from a GF abstract tree.
    - Leaf: the category annotation
    - Application: the result category of the function signature -/
def gfNodeCategory : AbstractNode → String
  | .leaf _ cat => gfCategoryResult cat
  | .apply f _ => gfCategoryResult f.type

/-- Look up a grammar rule label in the language definition. -/
def findGrammarRule (lang : LanguageDef) (label : String) : Option GrammarRule :=
  lang.terms.find? fun r => r.label == label

/-- The sort of a pattern, determined by the outermost constructor.
    Returns the `category` field of the matching grammar rule. -/
def patternSort (lang : LanguageDef) : Pattern → Option String
  | .apply f _ => (findGrammarRule lang f).map GrammarRule.category
  | _ => none  -- leaves, collections, lambdas need context to determine sort

/-- Sort assignment is consistent: the pattern sort of a converted
    GF application node equals its grammar-derived category.

    This holds because `gfFunctionSigToGrammarRule` preserves the
    category as `gfCategoryResult f.type`, and `gfAbstractToPattern`
    preserves the function name. -/
theorem patternSort_of_apply (f : FunctionSig) (args : List AbstractNode)
    (hFind : findGrammarRule gfLegacySemanticLanguageDef f.name =
             some (gfFunctionSigToGrammarRule f)) :
    patternSort gfLegacySemanticLanguageDef (gfAbstractToPattern (.apply f args)) =
    some (gfCategoryResult f.type) := by
  simp only [gfAbstractToPattern, patternSort, hFind, Option.map,
             gfFunctionSigToGrammarRule]

/-! ## Syntax classifiers and semantic native types for GF

Constructor shape is intensional syntax information.  It is useful while
parsing, but it is not automatically an OSLF predicate: GF's equation
`UseN(x) = x` deliberately identifies representatives with different outer
constructors.  A semantic native type therefore contains an equation-invariant
predicate, obtained either by proving invariance or by saturation.
-/

/-- A constructor-sensitive type used by the GF parser and elaborator before
quotient semantics.  This is intentionally not an OSLF native type. -/
structure GFSyntaxType where
  sort : String
  pred : Pattern → Prop

/-- A genuine GF OSLF native type: its predicate respects all authored GF
equations. -/
abbrev GFSemanticType := langNativeType gfLegacySemanticLanguageDef "S"

/-- Bool check: was a pattern built by a specific grammar rule? -/
def gfConstructorCheck (label : String) : Pattern → Bool
  | .apply f _ => f == label
  | _ => false

/-- Build an intensional syntax classifier for a grammar-rule constructor. -/
def gfConstructorSyntaxType (sort : String) (label : String) : GFSyntaxType :=
  { sort := sort
    pred := fun p => gfConstructorCheck label p = true }

/-- Admit an arbitrary raw GF observation into OSLF by taking its least
equation-invariant extension. -/
def gfSemanticType (sort : String) (φ : Pattern → Prop) : GFSemanticType :=
  { sort := sort
    pred := saturatePredicate (langGSLT gfLegacySemanticLanguageDef) φ }

/-- Semantic type satisfaction is application of the certified invariant
predicate to an authored representative. -/
theorem gfSatisfiesSemanticType (p : Pattern) (nt : GFSemanticType) :
    (langOSLF gfLegacySemanticLanguageDef "S").satisfies p nt.pred ↔ nt.pred.1 p :=
  Iff.rfl

/-! ## General Theorems about Constructor Types

These are universally quantified — they hold for ALL patterns, not
just specific examples. They establish the mathematical properties
of the GF constructor type system.
-/

/-- Characterization: a pattern satisfies a constructor check iff
    it's an apply-node with the matching label. -/
theorem gfConstructorCheck_iff (label : String) (p : Pattern) :
    gfConstructorCheck label p = true ↔ ∃ args, p = .apply label args := by
  constructor
  · intro h
    match p with
    | .apply f args =>
      simp [gfConstructorCheck, beq_iff_eq] at h
      exact ⟨args, by rw [h]⟩
    | .bvar _ => simp [gfConstructorCheck] at h
    | .fvar _ => simp [gfConstructorCheck] at h
    | .collection _ _ _ => simp [gfConstructorCheck] at h
    | .lambda _ _ => simp [gfConstructorCheck] at h
    | .multiLambda _ _ _ => simp [gfConstructorCheck] at h
    | .subst _ _ => simp [gfConstructorCheck] at h
  · rintro ⟨args, hp⟩
    subst hp
    simp [gfConstructorCheck]

/-- Constructor types are exclusive: a pattern cannot satisfy two
    constructor types with different labels simultaneously. -/
theorem constructor_types_exclusive (l₁ l₂ : String) (h : l₁ ≠ l₂) (p : Pattern) :
    gfConstructorCheck l₁ p = true → gfConstructorCheck l₂ p = false := by
  intro h₁
  obtain ⟨args, rfl⟩ := (gfConstructorCheck_iff l₁ _).mp h₁
  simp [gfConstructorCheck, h]

/-- Different constructor classifiers are disjoint at the syntax layer.  This
must not be promoted to OSLF without an equation-invariance proof. -/
theorem constructor_syntax_types_disjoint
    (s₁ s₂ l₁ l₂ : String) (h : l₁ ≠ l₂) (p : Pattern) :
    (gfConstructorSyntaxType s₁ l₁).pred p →
    ¬ (gfConstructorSyntaxType s₂ l₂).pred p := by
  intro h₁ h₂
  change gfConstructorCheck l₁ p = true at h₁
  change gfConstructorCheck l₂ p = true at h₂
  have := constructor_types_exclusive l₁ l₂ h p h₁
  rw [h₂] at this
  exact absurd this (by decide)

/-- Every GF application node satisfies its own constructor type. -/
theorem apply_satisfies_own_type (f : FunctionSig) (args : List AbstractNode) :
    gfConstructorCheck f.name (gfAbstractToPattern (.apply f args)) = true := by
  simp [gfConstructorCheck]

/-- Leaves NEVER satisfy any constructor type — they are untyped atoms. -/
theorem leaf_never_satisfies_constructor (name : String) (cat : Category) (label : String) :
    gfConstructorCheck label (gfAbstractToPattern (.leaf name cat)) = false := by
  simp [gfConstructorCheck]

/-- Constructor types partition the apply-nodes: every apply-node satisfies
    exactly one constructor type (its own label), and no others. -/
theorem apply_unique_constructor_type (f : FunctionSig) (args : List AbstractNode)
    (label : String) :
    gfConstructorCheck label (gfAbstractToPattern (.apply f args)) = true ↔
    label = f.name := by
  simp [gfConstructorCheck, beq_iff_eq]
  exact eq_comm

/-- The sort of a GF application node is determined entirely by the function
    signature, not the arguments. This is a key property of multi-sorted
    algebras: the sort is determined by the outermost operation. -/
theorem sort_independent_of_args (f : FunctionSig) (args₁ args₂ : List AbstractNode) :
    gfNodeCategory (.apply f args₁) = gfNodeCategory (.apply f args₂) := by
  simp [gfNodeCategory]

/-- Diamond applied to a saturated constructor observation reaches an equation
class containing a representative with that constructor.  It does not claim
that the operational target itself has that raw outer shape. -/
theorem diamond_constructor_implies_equivalent_reduct (label : String) (p : Pattern)
    (h : langDiamond gfLegacySemanticLanguageDef
      (saturatePredicate (langGSLT gfLegacySemanticLanguageDef)
        (fun q => gfConstructorCheck label q = true)) p) :
    ∃ q representative args,
      langSemanticReduces gfLegacySemanticLanguageDef p q ∧
      (langGSLT gfLegacySemanticLanguageDef).Equiv q representative ∧
      representative = .apply label args := by
  rw [langDiamond_spec] at h
  obtain ⟨q, hred, representative, equivalent, hshape⟩ := h
  obtain ⟨args, representativeEq⟩ :=
    (gfConstructorCheck_iff label representative).mp hshape
  exact ⟨q, representative, args, hred, equivalent, representativeEq⟩

/-- Box applied to a saturated constructor observation says every semantic
predecessor has an equation-equivalent representative with that constructor.

    Box is the backward modality: □φ(p) ↔ ∀ q, q ⇝ p → φ(q).
    The representative qualification is essential when equations erase a
    wrapper such as `UseN`. -/
theorem box_constructor_means_equivalent_predecessors (label : String) (p : Pattern)
    (h : langBox gfLegacySemanticLanguageDef
      (saturatePredicate (langGSLT gfLegacySemanticLanguageDef)
        (fun q => gfConstructorCheck label q = true)) p) :
    ∀ q, langSemanticReduces gfLegacySemanticLanguageDef q p →
      ∃ representative args,
        (langGSLT gfLegacySemanticLanguageDef).Equiv q representative ∧
        representative = .apply label args := by
  rw [langBox_spec] at h
  intro q hred
  obtain ⟨representative, equivalent, hshape⟩ := h q hred
  obtain ⟨args, representativeEq⟩ :=
    (gfConstructorCheck_iff label representative).mp hshape
  exact ⟨representative, args, equivalent, representativeEq⟩

/-! ## Type-Checking GF Terms

Concrete examples separating GF syntax classes from semantic OSLF types.
-/

-- Helper: build GF abstract trees for common constructions
def mkLeaf (name : String) (cat : String) : AbstractNode :=
  .leaf name (.base cat)

def mkApp1 (fname : String) (dom res : String) (arg : AbstractNode) : AbstractNode :=
  .apply { name := fname, type := .arrow (.base dom) (.base res) } [arg]

def mkApp2 (fname : String) (d1 d2 res : String)
    (a1 a2 : AbstractNode) : AbstractNode :=
  .apply { name := fname, type := .arrow (.base d1) (.arrow (.base d2) (.base res)) } [a1, a2]

/-! ### Sort Examples -/

-- "house" : N
private def house_tree := mkLeaf "house" "N"
-- UseN(house) : CN
private def useN_house := mkApp1 "UseN" "N" "CN" house_tree
-- DetCN(the, UseN(house)) : NP
private def theHouse := mkApp2 "DetCN" "Det" "CN" "NP"
  (mkLeaf "the_Det" "Det") useN_house
-- PredVP(theHouse, UseV(walk)) : Cl
private def theHouseWalks := mkApp2 "PredVP" "NP" "VP" "Cl"
  theHouse (mkApp1 "UseV" "V" "VP" (mkLeaf "walk_V" "V"))

-- Sort assignments
theorem house_sort : gfNodeCategory house_tree = "N" := rfl
theorem useN_house_sort : gfNodeCategory useN_house = "CN" := rfl
theorem theHouse_sort : gfNodeCategory theHouse = "NP" := rfl
theorem theHouseWalks_sort : gfNodeCategory theHouseWalks = "Cl" := rfl

-- Multi-sorted: different trees at different sorts
theorem sorts_differ_N_CN : gfNodeCategory house_tree ≠ gfNodeCategory useN_house := by
  decide
theorem sorts_differ_CN_NP : gfNodeCategory useN_house ≠ gfNodeCategory theHouse := by
  decide
theorem sorts_differ_NP_Cl : gfNodeCategory theHouse ≠ gfNodeCategory theHouseWalks := by
  decide

/-! ### Syntax-classification examples -/

-- Syntax class: "is a CN built by UseN"
private def useN_SyntaxType : GFSyntaxType :=
  gfConstructorSyntaxType "CN" "UseN"

-- Syntax class: "is a CN built by AdjCN"
private def adjCN_SyntaxType : GFSyntaxType :=
  gfConstructorSyntaxType "CN" "AdjCN"

-- Syntax class: "is an NP built by DetCN"
private def detCN_SyntaxType : GFSyntaxType :=
  gfConstructorSyntaxType "NP" "DetCN"

-- Syntax class: "is a Cl built by PredVP"
private def predVP_SyntaxType : GFSyntaxType :=
  gfConstructorSyntaxType "Cl" "PredVP"

-- Classification: UseN(house) has the UseN syntax shape.
theorem useN_house_has_syntax_type :
    useN_SyntaxType.pred (gfAbstractToPattern useN_house) := by
  show gfConstructorCheck "UseN" (gfAbstractToPattern useN_house) = true
  simp [gfConstructorCheck, useN_house, mkApp1, house_tree, mkLeaf]

-- Classification: theHouse has the DetCN syntax shape.
theorem theHouse_has_syntax_type :
    detCN_SyntaxType.pred (gfAbstractToPattern theHouse) := by
  show gfConstructorCheck "DetCN" (gfAbstractToPattern theHouse) = true
  simp [gfConstructorCheck, theHouse, mkApp2, mkApp1, mkLeaf, useN_house, house_tree]

-- Classification: theHouseWalks has the PredVP syntax shape.
theorem theHouseWalks_has_syntax_type :
    predVP_SyntaxType.pred (gfAbstractToPattern theHouseWalks) := by
  show gfConstructorCheck "PredVP" (gfAbstractToPattern theHouseWalks) = true
  simp [gfConstructorCheck, theHouseWalks, mkApp2, mkApp1, mkLeaf, theHouse, useN_house, house_tree]

/-! ## Parse Disambiguation via Types

"The old man the boats" has two well-typed abstract trees:
- Parse 1: AdjCN(old, man) + walk → adjective reading
- Parse 2: UseN(old) + ComplSlash(man, boats) → verb reading

These get different syntax classes because their CN subtrees are built by
different constructors (AdjCN vs UseN).  This is parser information; it is not
an OSLF distinction when the equation theory identifies those representatives.
-/

-- Parse 1: the old man walks
-- DetCN(the, AdjCN(PositA(old), UseN(man))) + PredVP(_, UseV(walk))
private def parse1_cn := mkApp2 "AdjCN" "AP" "CN" "CN"
  (mkApp1 "PositA" "A" "AP" (mkLeaf "old" "A"))
  (mkApp1 "UseN" "N" "CN" (mkLeaf "man" "N"))
private def parse1_np := mkApp2 "DetCN" "Det" "CN" "NP"
  (mkLeaf "the_Det" "Det") parse1_cn
private def parse1 := mkApp2 "PredVP" "NP" "VP" "Cl"
  parse1_np (mkApp1 "UseV" "V" "VP" (mkLeaf "walk" "V"))

-- Parse 2: the old man the boats
-- DetCN(the, UseN(old)) + PredVP(_, ComplSlash(SlashV2a(man), DetCN(the, UseN(boat))))
private def parse2_cn := mkApp1 "UseN" "N" "CN" (mkLeaf "old" "N")
private def parse2_np := mkApp2 "DetCN" "Det" "CN" "NP"
  (mkLeaf "the_Det" "Det") parse2_cn
private def parse2_obj := mkApp2 "DetCN" "Det" "CN" "NP"
  (mkLeaf "the_Det" "Det") (mkApp1 "UseN" "N" "CN" (mkLeaf "boat" "N"))
private def parse2_vp := mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
  (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "man" "V2")) parse2_obj
private def parse2 := mkApp2 "PredVP" "NP" "VP" "Cl" parse2_np parse2_vp

-- Both parses have the same top-level sort (Cl)
theorem both_parses_sort_Cl :
    gfNodeCategory parse1 = "Cl" ∧ gfNodeCategory parse2 = "Cl" :=
  ⟨rfl, rfl⟩

-- But the CN subtrees have different constructors:
-- parse1 uses AdjCN, parse2 uses UseN
theorem parse1_cn_is_AdjCN :
    adjCN_SyntaxType.pred (gfAbstractToPattern parse1_cn) := by
  show gfConstructorCheck "AdjCN" (gfAbstractToPattern parse1_cn) = true
  simp [gfConstructorCheck, parse1_cn, mkApp2, mkApp1, mkLeaf]

theorem parse2_cn_is_UseN :
    useN_SyntaxType.pred (gfAbstractToPattern parse2_cn) := by
  show gfConstructorCheck "UseN" (gfAbstractToPattern parse2_cn) = true
  simp [gfConstructorCheck, parse2_cn, mkApp1, mkLeaf]

-- parse1's CN does NOT satisfy the UseN type (it's AdjCN)
theorem parse1_cn_not_UseN :
    ¬ useN_SyntaxType.pred (gfAbstractToPattern parse1_cn) := by
  show ¬ (gfConstructorCheck "UseN" (gfAbstractToPattern parse1_cn) = true)
  simp [gfConstructorCheck, parse1_cn, mkApp2, mkApp1, mkLeaf]

-- parse2's CN does NOT satisfy the AdjCN type (it's UseN)
theorem parse2_cn_not_AdjCN :
    ¬ adjCN_SyntaxType.pred (gfAbstractToPattern parse2_cn) := by
  show ¬ (gfConstructorCheck "AdjCN" (gfAbstractToPattern parse2_cn) = true)
  simp [gfConstructorCheck, parse2_cn, mkApp1, mkLeaf]

/-- The disambiguation theorem: the two parses of "the old man ..."
    produce patterns in different constructor-sensitive syntax classes.

    Parse 1's CN subtree satisfies AdjCN-type but not UseN-type.
    Parse 2's CN subtree satisfies UseN-type but not AdjCN-type.
    Therefore the parser can distinguish them before semantic quotienting. -/
theorem garden_path_disambiguation :
    adjCN_SyntaxType.pred (gfAbstractToPattern parse1_cn) ∧
    ¬ useN_SyntaxType.pred (gfAbstractToPattern parse1_cn) ∧
    useN_SyntaxType.pred (gfAbstractToPattern parse2_cn) ∧
    ¬ adjCN_SyntaxType.pred (gfAbstractToPattern parse2_cn) :=
  ⟨parse1_cn_is_AdjCN, parse1_cn_not_UseN, parse2_cn_is_UseN, parse2_cn_not_AdjCN⟩

-- The full sentence patterns are also different
theorem parse_patterns_differ :
    gfAbstractToPattern parse1 ≠ gfAbstractToPattern parse2 := by
  simp [parse1, parse2, parse1_np, parse2_np, parse1_cn, parse2_cn, parse2_obj, parse2_vp,
        mkApp2, mkApp1, mkLeaf]

/-! ## Checker-Verified Type Assignments

Using the executable checker to verify type properties,
then connecting to denotational semantics via soundness.
-/

-- Checker verifies: UseN(house) |= ◇(is_house) → sat
#eval! do
  let pat := gfAbstractToPattern useN_house
  let result := checkLangUsing .empty gfLegacySemanticLanguageDef
    (gfAtomCheck_isName "house") 3 pat (.dia (.atom "is_house"))
  IO.println s!"UseN(house) |= ◇(is_house): {repr result}"
  -- .sat

-- Checker verifies: house |= ◇(is_house) → unsat
#eval! do
  let pat := Pattern.fvar "house"
  let result := checkLangUsing .empty gfLegacySemanticLanguageDef
    (gfAtomCheck_isName "house") 3 pat (.dia (.atom "is_house"))
  IO.println s!"house |= ◇(is_house): {repr result}"
  -- .unsat (irreducible)

-- Checker-to-semantics: proved-sound type assignment
-- If the checker says sat, semantics hold (by gfAbstract_checkSat_sound)
example (h : checkLangUsing .empty gfLegacySemanticLanguageDef
    (gfAtomCheck_isName "house") 3
    (gfAbstractToPattern useN_house) (.dia (.atom "is_house")) = .sat) :
    langFormulaSem gfLegacySemanticLanguageDef
      (saturateAtomSemUsing .empty gfLegacySemanticLanguageDef
        (gfAtomSem_isName "house"))
      (.dia (.atom "is_house")) (gfAbstractToPattern useN_house) :=
  gfAbstract_checkSat_sound (gfAtomCheck_isName_sound "house") h

/-! ## Linguistic Theorems

Theorems about GF abstract syntax and its equation-respecting OSLF semantics.
-/

/-! ### Translation Invariance

GF's key architectural insight: abstract syntax is *language-independent*.
English, Czech, Finnish — all share the same abstract trees.  Only the
concrete syntax (linearization) differs.

Because equation-respecting OSLF types are evaluated on the shared abstract
tree (via `gfAbstractToPattern`), a concrete-language translation that retains
that tree retains the type.  Linearization itself remains a distinct theorem.
-/

/-- If two concrete realizations retain the same GF abstract tree, every
semantic native type has the same truth value.  The shared-tree premise is the
actual GF translation invariant; no statement about source strings is hidden
inside this theorem. -/
theorem translation_preserves_semantic_type
    (sourceTree targetTree : AbstractNode)
    (sameAbstractTree : sourceTree = targetTree)
    (nt : GFSemanticType) :
    nt.pred.1 (gfAbstractToPattern sourceTree) ↔
      nt.pred.1 (gfAbstractToPattern targetTree) := by
  subst targetTree
  exact Iff.rfl

/-- Two abstract trees that differ structurally get different patterns. -/
theorem structural_difference_detectable (t₁ t₂ : AbstractNode)
    (h : gfAbstractToPattern t₁ ≠ gfAbstractToPattern t₂) :
    ∃ φ : Pattern → Prop,
      φ (gfAbstractToPattern t₁) ∧ ¬ φ (gfAbstractToPattern t₂) :=
  ⟨fun p => p = gfAbstractToPattern t₁, rfl, fun heq => h (heq ▸ rfl)⟩

/-! ### Semantic Accessibility (Entailment via ◇)

The ◇ modality captures a notion of *semantic containment*:
◇(is_X)(tree) means "X is semantically accessible in tree."

Linguistically: "the cat sleeps" *entails the existence of a cat*
because the abstract tree for "the cat sleeps" reduces (via grammar rules)
to expose the lexical item "cat".

This gives us a formal, computational notion of entailment that
goes beyond linearized string matching.
-/

/-- If a tree contains a lexical item (reachable via ◇), then
    the item is semantically present — it cannot be removed by
    changing the concrete realization.

    This is because ◇ is defined on abstract trees, not linearized strings.
    A French translation of "the cat sleeps" would have a different
    source form but the SAME abstract tree, so ◇(is_cat) still holds. -/
theorem semantic_presence_is_structural (tree : AbstractNode) (name : String)
    (h : langDiamond gfLegacySemanticLanguageDef
      (saturatePredicate (langGSLT gfLegacySemanticLanguageDef)
        (fun p => p = Pattern.fvar name)) (gfAbstractToPattern tree)) :
    ∃ q representative,
      langSemanticReduces gfLegacySemanticLanguageDef (gfAbstractToPattern tree) q ∧
      (langGSLT gfLegacySemanticLanguageDef).Equiv q representative ∧
      representative = Pattern.fvar name := by
  rw [langDiamond_spec] at h
  rcases h with ⟨q, hred, representative, equivalent, representativeEq⟩
  exact ⟨q, representative, hred, equivalent, representativeEq⟩

/-! ### Subcategorization as Type Theory

The V/V2 distinction captures *selectional restrictions*:
intransitive verbs (V) and transitive verbs (V2) are different types.

This isn't just a lexical tag — it has structural consequences.
A V2 verb creates a VPSlash (a VP with a gap), which must be filled
by a complement.  The type system ENFORCES argument structure.

At the abstract syntax level, this means:
- UseV(walk) has category VP (no gap)
- ComplSlash(SlashV2a(love), her) has category VP (gap filled)
- SlashV2a(love) alone has category VPSlash (gap unfilled)

    GF syntax classifiers distinguish these structurally.  Semantic OSLF types
    retain only distinctions invariant under the grammar's equations.
-/

/-- VP built from intransitive verb: constructor is "UseV" -/
private def useV_walk := mkApp1 "UseV" "V" "VP" (mkLeaf "walk" "V")
/-- VP built from transitive verb + object: constructor is "ComplSlash" -/
private def complSlash_love_her := mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
  (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "love" "V2"))
  (mkLeaf "her" "NP")

/-- Intransitive and transitive VPs have different constructors,
    therefore different syntax classes.  The grammar enforces that
    "walk" and "love her" are built differently. -/
theorem subcat_V_vs_V2 :
    gfConstructorCheck "UseV" (gfAbstractToPattern useV_walk) = true ∧
    gfConstructorCheck "ComplSlash" (gfAbstractToPattern complSlash_love_her) = true ∧
    gfConstructorCheck "ComplSlash" (gfAbstractToPattern useV_walk) = false ∧
    gfConstructorCheck "UseV" (gfAbstractToPattern complSlash_love_her) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [gfConstructorCheck, useV_walk, complSlash_love_her,
          mkApp1, mkApp2, mkLeaf]

/-- The subcategorization frame of a VP is visible in its syntax class:
    you can always tell whether a VP was built from V or V2. -/
theorem subcat_determines_type (vp : AbstractNode) :
    gfConstructorCheck "UseV" (gfAbstractToPattern vp) = true →
    gfConstructorCheck "ComplSlash" (gfAbstractToPattern vp) = false := by
  exact constructor_types_exclusive "UseV" "ComplSlash" (by decide) _

/-! ### Compositionality (Frege's Principle)

"The meaning of a compound expression is determined by the meanings
of its parts and the way they are combined."

In the intensional GF view, the syntax class of a compound expression is
determined by the constructor (= the combining rule) and the parts (= the arguments).
Two expressions built with the same rule from the same parts get the
same type.
-/

/-- Frege's principle for constructor types: the type depends on the
    constructor, not on the identity of the arguments (beyond their
    contribution to the pattern).  Same rule, same argument patterns
    → same constructor syntax class. -/
theorem frege_compositionality (f : FunctionSig)
    (args₁ args₂ : List AbstractNode) (label : String) :
    gfConstructorCheck label (gfAbstractToPattern (.apply f args₁)) =
    gfConstructorCheck label (gfAbstractToPattern (.apply f args₂)) := by
  simp [gfConstructorCheck]

/-- Stronger Frege: if the argument patterns are the same, the entire
    patterns are the same — so all predicates (including semantic OSLF
    predicates) are preserved. -/
theorem frege_strong (f : FunctionSig)
    (args₁ args₂ : List AbstractNode)
    (hargs : args₁.map gfAbstractToPattern = args₂.map gfAbstractToPattern) :
    gfAbstractToPattern (.apply f args₁) = gfAbstractToPattern (.apply f args₂) := by
  unfold gfAbstractToPattern
  exact congrArg (Pattern.apply f.name) hargs

/-! ### Ambiguity as Type Multiplicity

A linearized string is *ambiguous* iff it has multiple abstract trees.
Each abstract tree lives in a unique type fiber (by `apply_unique_constructor_type`).
Therefore: **the number of readings = the number of type fibers**.

This gives us a *measure* of ambiguity: count the distinct constructors
at any node in the parse forest.  The type system makes ambiguity
not just detectable but *quantifiable*.
-/

/-- If two abstract trees produce the same pattern, they satisfy
    the same types — they are indistinguishable to the type system.
    Conversely: type-distinct = structurally distinct. -/
theorem type_distinguishes_structure (t₁ t₂ : AbstractNode)
    (h : gfAbstractToPattern t₁ = gfAbstractToPattern t₂) (φ : Pattern → Prop) :
    φ (gfAbstractToPattern t₁) ↔ φ (gfAbstractToPattern t₂) := by
  rw [h]

/-- Two applications with different function names are ALWAYS
    type-distinguishable, regardless of their arguments.
    This is the formal content of "the type IS the disambiguation." -/
theorem different_rules_always_distinguishable
    (f₁ f₂ : FunctionSig) (h : f₁.name ≠ f₂.name)
    (args₁ args₂ : List AbstractNode) :
    ∃ φ : Pattern → Prop,
      φ (gfAbstractToPattern (.apply f₁ args₁)) ∧
      ¬ φ (gfAbstractToPattern (.apply f₂ args₂)) := by
  refine ⟨fun p => gfConstructorCheck f₁.name p = true, ?_, ?_⟩
  · exact apply_satisfies_own_type f₁ args₁
  · intro h₂
    have := (apply_unique_constructor_type f₂ args₂ f₁.name).mp h₂
    exact h this

end Mettapedia.Languages.GF.Typing
