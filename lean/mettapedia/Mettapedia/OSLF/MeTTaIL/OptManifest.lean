import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Optimization Contract Manifest

Structured manifest mapping formally verified optimization theorems to
machine-readable metadata consumable by mettail-rust and other backends.

## Pipeline

```
OptContractManifest (Lean records) ← source of truth
       ↓
renderManifestJSON                 ← auto-generated JSON
       ↓
build.rs / CI                      ← Rust consumes at build time
```

## References

- OptimizationTheorems.lean: core optimization contracts
- ZamContracts.lean: trie backend transfer
- Export.lean: existing LanguageDef → Rust export
-/

namespace Mettapedia.OSLF.MeTTaIL.OptManifest

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## §1: Manifest Types -/

/-- Which backends a contract applies to. -/
inductive BackendScope where
  | anyRelEnv   -- works for any RelationEnv (flat, trie, custom)
  | emptyRelEnv -- only RelationEnv.empty (no premise-driven relations)
deriving Repr, BEq

/-- When a contract's precondition is checked. -/
inductive OptPrecondition where
  | runtime (desc : String)      -- checked dynamically (e.g. ¬◇φ at a state)
  | compileTime (desc : String)  -- checked statically (e.g. rule subset)
  | always                       -- unconditional
deriving Repr

/-- A single optimization contract with formal backing. -/
structure OptContract where
  id : String             -- machine-readable key (e.g. "early_termination")
  name : String           -- human-readable name
  leanTheorem : String    -- fully qualified Lean theorem name
  backend : BackendScope
  precondition : OptPrecondition
  description : String    -- what the optimization does
deriving Repr

/-- A pair of languages where specialization applies:
    reductions in `baseLang` lift to `extLang`. -/
structure SpecPair where
  baseLang : String
  extLang : String
  leanTheorem : String
deriving Repr

/-- Complete optimization manifest for a language. -/
structure OptContractManifest where
  language : String
  contracts : List OptContract
  specializationPairs : List SpecPair
  congruencePolicy : List String
deriving Repr

/-! ## §2: Universal Contracts

These apply to ALL languages — they are structural properties of the
OSLF modal algebra, not language-specific. -/

def universalContracts : List OptContract :=
  [ { id := "early_termination"
      name := "Early Termination"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.diamond_false_early_termination"
      backend := .anyRelEnv
      precondition := .runtime "¬◇φ(p): no successor of p satisfies φ"
      description := "Skip successor exploration when ¬◇φ" }
  , { id := "box_memoization"
      name := "Box Memoization"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.box_memoization_safe"
      backend := .anyRelEnv
      precondition := .runtime "□φ(p): all predecessors of p satisfy φ"
      description := "Cache □-typed results for all predecessors" }
  , { id := "deterministic_diamond"
      name := "Deterministic Diamond Collapse"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.deterministic_diamond_collapse"
      backend := .anyRelEnv
      precondition := .runtime "unique successor: ∀ q', reduces p q' → q' = q"
      description := "Direct-dispatch when reduction has unique successor" }
  , { id := "deterministic_box"
      name := "Deterministic Box Collapse"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.deterministic_box_collapse"
      backend := .anyRelEnv
      precondition := .runtime "unique predecessor: ∀ q', reduces q' p → q' = q"
      description := "Direct-dispatch when predecessor is unique" }
  , { id := "rule_specialization"
      name := "Rule Specialization"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.specialization_preserves_reduction"
      backend := .anyRelEnv
      precondition := .compileTime "lang₁.rewrites ⊆ lang₂.rewrites ∧ congruenceCollections match"
      description := "Lift reductions from sub-language to super-language" }
  , { id := "diamond_mono"
      name := "Diamond Monotonicity"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.diamond_mono_rules"
      backend := .anyRelEnv
      precondition := .compileTime "lang₁.rewrites ⊆ lang₂.rewrites ∧ congruenceCollections match"
      description := "Lift ◇-witnesses from weaker to stronger language" }
  , { id := "box_contravariance"
      name := "Box Contravariance"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.box_contra_rules"
      backend := .anyRelEnv
      precondition := .compileTime "lang₁.rewrites ⊆ lang₂.rewrites ∧ congruenceCollections match"
      description := "Weaken □-guarantees when moving to stronger language" }
  , { id := "substitution_reduction_fusion"
      name := "Substitution-Reduction Fusion"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.substitution_reduction_fusion"
      backend := .emptyRelEnv
      precondition := .always
      description := "Fuse substitution + reduction passes via Beck-Chevalley Galois connection" }
  , { id := "galois_composition"
      name := "Galois Connection Composition"
      leanTheorem := "Mettapedia.OSLF.Framework.OptimizationTheorems.galois_composition"
      backend := .anyRelEnv
      precondition := .always
      description := "Chain adjoint-based optimization passes" }
  ]

/-! ## §3: Per-Language Manifest Builder -/

private def renderCollType : CollType → String
  | .vec => "Vec"
  | .hashBag => "HashBag"
  | .hashSet => "HashSet"

/-- Build an optimization manifest for a given language definition. -/
def manifestFor (lang : LanguageDef)
    (specializationPairs : List SpecPair := []) : OptContractManifest :=
  { language := lang.name
    contracts := universalContracts
    specializationPairs := specializationPairs
    congruencePolicy := lang.congruenceCollections.map renderCollType }

/-! ## §4: JSON Renderer -/

private def jsonEscape (s : String) : String :=
  (s.replace "\\" "\\\\").replace "\"" "\\\"" |>.replace "\n" "\\n"

private def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonField (indent : String) (key : String) (val : String) : String :=
  indent ++ jsonStr key ++ ": " ++ val

private def renderBackendScope : BackendScope → String
  | .anyRelEnv => jsonStr "any_relation_env"
  | .emptyRelEnv => jsonStr "empty_relation_env"

private def renderPrecondition : OptPrecondition → String
  | .runtime desc =>
    "{ " ++ jsonStr "type" ++ ": " ++ jsonStr "runtime" ++ ", " ++
            jsonStr "condition" ++ ": " ++ jsonStr desc ++ " }"
  | .compileTime desc =>
    "{ " ++ jsonStr "type" ++ ": " ++ jsonStr "compile_time" ++ ", " ++
            jsonStr "condition" ++ ": " ++ jsonStr desc ++ " }"
  | .always =>
    "{ " ++ jsonStr "type" ++ ": " ++ jsonStr "always" ++ " }"

private def renderContract (c : OptContract) : String :=
  let i := "        "
  "      {\n" ++
  jsonField i "id" (jsonStr c.id) ++ ",\n" ++
  jsonField i "name" (jsonStr c.name) ++ ",\n" ++
  jsonField i "lean_theorem" (jsonStr c.leanTheorem) ++ ",\n" ++
  jsonField i "backend" (renderBackendScope c.backend) ++ ",\n" ++
  jsonField i "precondition" (renderPrecondition c.precondition) ++ ",\n" ++
  jsonField i "description" (jsonStr c.description) ++ "\n" ++
  "      }"

private def renderSpecPair (sp : SpecPair) : String :=
  let i := "        "
  "      {\n" ++
  jsonField i "base_lang" (jsonStr sp.baseLang) ++ ",\n" ++
  jsonField i "ext_lang" (jsonStr sp.extLang) ++ ",\n" ++
  jsonField i "lean_theorem" (jsonStr sp.leanTheorem) ++ "\n" ++
  "      }"

private def jsonArray (items : List String) : String :=
  if items.isEmpty then "[]"
  else "[\n" ++ String.intercalate ",\n" items ++ "\n    ]"

/-- Render an `OptContractManifest` as a JSON string. -/
def renderManifestJSON (m : OptContractManifest) : String :=
  let contractItems := m.contracts.map renderContract
  let specItems := m.specializationPairs.map renderSpecPair
  let policyItems := m.congruencePolicy.map jsonStr
  "{\n" ++
  jsonField "  " "language" (jsonStr m.language) ++ ",\n" ++
  jsonField "  " "contracts" (jsonArray contractItems) ++ ",\n" ++
  jsonField "  " "specialization_pairs" (jsonArray specItems) ++ ",\n" ++
  jsonField "  " "congruence_policy" ("[" ++ String.intercalate ", " policyItems ++ "]") ++ "\n" ++
  "}"

end Mettapedia.OSLF.MeTTaIL.OptManifest
