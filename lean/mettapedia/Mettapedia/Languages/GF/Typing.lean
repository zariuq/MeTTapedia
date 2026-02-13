/-
# GF → OSLF Type-Checking Layer

Connects GF abstract syntax trees to the OSLF type system at the
theorem level. Provides:

1. **Sort assignment**: every GF abstract tree gets an OSLF sort
2. **Native types**: concrete (sort, predicate) pairs for GF terms
3. **Type satisfaction**: proofs that GF terms satisfy their types
4. **Parse disambiguation**: different abstract trees → different native types
5. **Multi-sorted examples**: exercising N, CN, NP, VP, S sorts

## Pipeline

```
AbstractNode →[gfNodeCategory]→ String (sort)
  →[gfNativeType]→ NativeTypeOf (sort, predicate)
  →[gfSatisfiesType]→ (langOSLF gfRGLLanguageDef).satisfies p φ
```

## References
- Williams & Stay, "Native Type Theory" (ACT 2021)
- OSLFBridge.lean: GF → LanguageDef conversion
- TypeSynthesis.lean: langOSLF, langNativeType, NativeTypeOf
-/

import Mettapedia.Languages.GF.OSLFBridge

namespace Mettapedia.Languages.GF.Typing

open Mettapedia.Languages.GF.Core
open Mettapedia.Languages.GF.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.RewriteSystem

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
    (hFind : findGrammarRule gfRGLLanguageDef f.name =
             some (gfFunctionSigToGrammarRule f)) :
    patternSort gfRGLLanguageDef (gfAbstractToPattern (.apply f args)) =
    some (gfCategoryResult f.type) := by
  simp only [gfAbstractToPattern, patternSort, hFind, Option.map,
             gfFunctionSigToGrammarRule]

/-! ## Native Types for GF

A native type is a (sort, predicate) pair. For GF, the predicate
identifies terms that were constructed by a specific grammar rule
or that satisfy a modal property.
-/

/-- A GF native type: a sort name and a predicate on patterns.
    This is `NativeTypeOf (langOSLF gfRGLLanguageDef "S")`. -/
abbrev GFNativeType := langNativeType gfRGLLanguageDef "S"

/-- Build a native type that checks whether a pattern was built
    by a specific grammar rule (identified by label). -/
def gfConstructorType (sort : String) (label : String) : GFNativeType :=
  { sort := sort
    pred := fun p => match p with
      | .apply f _ => f == label
      | _ => False }

/-- Build a native type from a sort and an arbitrary predicate. -/
def gfPredicateType (sort : String) (φ : Pattern → Prop) : GFNativeType :=
  { sort := sort, pred := φ }

/-- Type satisfaction: a pattern satisfies a native type iff
    the predicate holds on it.

    This follows from `langOSLF`'s definition:
    `satisfies := fun t φ => φ t`. -/
theorem gfSatisfiesType (p : Pattern) (nt : GFNativeType) :
    (langOSLF gfRGLLanguageDef "S").satisfies p nt.pred ↔ nt.pred p :=
  Iff.rfl

/-! ## Type-Checking GF Terms

Concrete examples showing GF abstract trees receiving OSLF types.
-/

-- Helper: build GF abstract trees for common constructions
private def mkLeaf (name : String) (cat : String) : AbstractNode :=
  .leaf name (.base cat)

private def mkApp1 (fname : String) (dom res : String) (arg : AbstractNode) : AbstractNode :=
  .apply { name := fname, type := .arrow (.base dom) (.base res) } [arg]

private def mkApp2 (fname : String) (d1 d2 res : String)
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

/-! ### Native Type Examples -/

-- Type: "is a CN built by UseN"
private def useN_Type : GFNativeType :=
  gfConstructorType "CN" "UseN"

-- Type: "is a CN built by AdjCN"
private def adjCN_Type : GFNativeType :=
  gfConstructorType "CN" "AdjCN"

-- Type: "is an NP built by DetCN"
private def detCN_Type : GFNativeType :=
  gfConstructorType "NP" "DetCN"

-- Type: "is a Cl built by PredVP"
private def predVP_Type : GFNativeType :=
  gfConstructorType "Cl" "PredVP"

-- Satisfaction: UseN(house) satisfies useN_Type
theorem useN_house_satisfies :
    (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern useN_house) useN_Type.pred :=
  rfl  -- satisfies = φ t, and "UseN" == "UseN" = true

-- Satisfaction: theHouse satisfies detCN_Type
theorem theHouse_satisfies :
    (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern theHouse) detCN_Type.pred :=
  rfl

-- Satisfaction: theHouseWalks satisfies predVP_Type
theorem theHouseWalks_satisfies :
    (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern theHouseWalks) predVP_Type.pred :=
  rfl

/-! ## Parse Disambiguation via Types

"The old man the boats" has two well-typed abstract trees:
- Parse 1: AdjCN(old, man) + walk → adjective reading
- Parse 2: UseN(old) + ComplSlash(man, boats) → verb reading

These get different native types because their CN subtrees
are built by different constructors (AdjCN vs UseN).
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
    (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern parse1_cn) adjCN_Type.pred := by
  decide

theorem parse2_cn_is_UseN :
    (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern parse2_cn) useN_Type.pred := by
  decide

-- parse1's CN does NOT satisfy the UseN type (it's AdjCN)
theorem parse1_cn_not_UseN :
    ¬ (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern parse1_cn) useN_Type.pred := by
  decide

-- parse2's CN does NOT satisfy the AdjCN type (it's UseN)
theorem parse2_cn_not_AdjCN :
    ¬ (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern parse2_cn) adjCN_Type.pred := by
  decide

/-- The disambiguation theorem: the two parses of "the old man ..."
    produce patterns that satisfy different native type predicates.

    Parse 1's CN subtree satisfies AdjCN-type but not UseN-type.
    Parse 2's CN subtree satisfies UseN-type but not AdjCN-type.
    Therefore they are distinguishable by the OSLF type system. -/
theorem garden_path_disambiguation :
    (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern parse1_cn) adjCN_Type.pred ∧
    ¬ (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern parse1_cn) useN_Type.pred ∧
    (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern parse2_cn) useN_Type.pred ∧
    ¬ (langOSLF gfRGLLanguageDef "S").satisfies
      (gfAbstractToPattern parse2_cn) adjCN_Type.pred :=
  ⟨parse1_cn_is_AdjCN, parse1_cn_not_UseN, parse2_cn_is_UseN, parse2_cn_not_AdjCN⟩

-- The full sentence patterns are also different
theorem parse_patterns_differ :
    gfAbstractToPattern parse1 ≠ gfAbstractToPattern parse2 := by
  decide

/-! ## Modal Type Properties

Using ◇/□ to express behavioral type properties of GF terms.
-/

/-- UseN(house) satisfies ◇(is_house) because UseN(house) ⇝ house.
    This combines the rewrite system with the type system. -/
theorem useN_house_diamond_isHouse :
    langDiamond gfRGLLanguageDef
      (fun p => p = .fvar "house")
      (gfAbstractToPattern useN_house) := by
  rw [langDiamond_spec]
  refine ⟨.fvar "house", ?_, rfl⟩
  apply exec_to_langReducesUsing .empty gfRGLLanguageDef
  show langReducesExecUsing .empty gfRGLLanguageDef
    (gfAbstractToPattern useN_house) (.fvar "house")
  native_decide

/-- PositA(big) satisfies ◇(is_big) because PositA(big) ⇝ big. -/
theorem positA_big_diamond_isBig :
    langDiamond gfRGLLanguageDef
      (fun p => p = .fvar "big")
      (gfAbstractToPattern (mkApp1 "PositA" "A" "AP" (mkLeaf "big" "A"))) := by
  rw [langDiamond_spec]
  refine ⟨.fvar "big", ?_, rfl⟩
  apply exec_to_langReducesUsing .empty gfRGLLanguageDef
  show langReducesExecUsing .empty gfRGLLanguageDef
    (gfAbstractToPattern (mkApp1 "PositA" "A" "AP" (mkLeaf "big" "A"))) (.fvar "big")
  native_decide

/-- Bare leaf "house" does NOT satisfy ◇(anything) — it's irreducible.
    The rewrite engine produces no reducts for a bare fvar. -/
theorem bare_house_no_reducts :
    rewriteWithContextWithPremisesUsing .empty gfRGLLanguageDef
      (.fvar "house") = [] := by
  native_decide

/-! ## Checker-Verified Type Assignments

Using the executable checker to verify type properties,
then connecting to denotational semantics via soundness.
-/

-- Checker verifies: UseN(house) |= ◇(is_house) → sat
#eval! do
  let pat := gfAbstractToPattern useN_house
  let result := checkLangUsing .empty gfRGLLanguageDef
    (gfAtomCheck_isName "house") 3 pat (.dia (.atom "is_house"))
  IO.println s!"UseN(house) |= ◇(is_house): {repr result}"
  -- .sat

-- Checker verifies: house |= ◇(is_house) → unsat
#eval! do
  let pat := Pattern.fvar "house"
  let result := checkLangUsing .empty gfRGLLanguageDef
    (gfAtomCheck_isName "house") 3 pat (.dia (.atom "is_house"))
  IO.println s!"house |= ◇(is_house): {repr result}"
  -- .unsat (irreducible)

-- Checker-to-semantics: proved-sound type assignment
-- If the checker says sat, semantics hold (by gfAbstract_checkSat_sound)
example (h : checkLangUsing .empty gfRGLLanguageDef
    (gfAtomCheck_isName "house") 3
    (gfAbstractToPattern useN_house) (.dia (.atom "is_house")) = .sat) :
    sem (langReduces gfRGLLanguageDef) (gfAtomSem_isName "house")
      (.dia (.atom "is_house")) (gfAbstractToPattern useN_house) :=
  gfAbstract_checkSat_sound (gfAtomCheck_isName_sound "house") h

end Mettapedia.Languages.GF.Typing
