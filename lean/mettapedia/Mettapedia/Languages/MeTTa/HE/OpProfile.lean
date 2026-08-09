/-!
# HE MeTTa Operator Classification

Classifies each HE MeTTa operator into exactly one implementation category.
This determines how each operator flows through the export pipeline
(HELanguageDef → TransitionSpec → RewriteIR → Rust runtime).

## Classification Categories

| Category | Where implemented | Example |
|----------|------------------|---------|
| syntaxSugar | Parser lowering only | let, let* |
| preludeEqAndType | Injected equations + type annotation | if |
| mettaCallControl | Explicit MettaCall rewrite rule | case, switch, assert |
| minimalInstruction | OSLF MeTTaMinimalInstance layer | unify, collapse-bind, superpose-bind |
| groundedBuiltin | MC_Grounded dispatch (arithmetic, etc.) | +, -, *, /, <, >, == |

## Design Invariant

Every user-visible MeTTa operator must appear in exactly one category.
The export pipeline must carry all mettaCallControl operators as explicit
rewrite rules in HELanguageDef.lean — they must NOT be handwritten in Rust.

## References

- Interpreter.lean: mettaCall (lines 307-418) — the executable spec
- HELanguageDef.lean: mettaHE.rewrites — the exportable rewrite rules
- MeTTaMinimalInstance.lean — OSLF minimal instruction set
-/

namespace Mettapedia.Languages.MeTTa.HE.OpProfile

/-- Classification of how an HE MeTTa operator is implemented. -/
inductive OpCategory where
  /-- Lowered by the parser before encoding (no runtime semantics). -/
  | syntaxSugar
  /-- Equations and type annotation injected into the space at startup. -/
  | preludeEqAndType
  /-- Explicit rewrite rule in MettaCall dispatch (HELanguageDef.lean). -/
  | mettaCallControl
  /-- Implemented via OSLF MeTTaMinimalInstance instruction layer. -/
  | minimalInstruction
  /-- Dispatched via MC_Grounded (executable grounded atoms). -/
  | groundedBuiltin
deriving DecidableEq, Repr

/-- An operator's formal classification entry. -/
structure OpEntry where
  /-- Source-level operator name as it appears in MeTTa source. -/
  name : String
  /-- Implementation category. -/
  category : OpCategory
  /-- Which Interpreter.lean branch handles this (line reference). -/
  interpreterRef : String
  /-- Which HELanguageDef rule (if any) currently covers this. -/
  languageDefRule : Option String := none
deriving Repr

/-- Complete classification of HE MeTTa Tier 1 operators.

Each entry pins down exactly where the operator's semantics live,
preventing ad-hoc Rust implementations. -/
def tier1Ops : List OpEntry :=
  [ -- Syntax sugar: lowered before encoding, no runtime dispatch needed
    { name := "let"
      category := .syntaxSugar
      interpreterRef := "N/A — desugars to (case expr ((pat body)))" }
  , { name := "let*"
      category := .syntaxSugar
      interpreterRef := "N/A — desugars to nested let" }

    -- Prelude: equations + type annotation injected into space
  , { name := "if"
      category := .preludeEqAndType
      interpreterRef := "N/A — handled by (= (if True $then $else) $then) equations"
      languageDefRule := some "MC_Equation (via injected equations)" }

    -- MettaCall control: explicit rewrite rules in HELanguageDef
    -- These correspond to the switch/assert/case branches in Interpreter.lean:342-396
  , { name := "case"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:385-396"
      languageDefRule := some "MC_Case_Start" }
  , { name := "switch"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:342-356"
      languageDefRule := some "MC_SwitchMinimal_Start (parseSwitchMinimalCallArgs accepts both switch and switch-minimal)" }
  , { name := "switch-minimal"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:342-356"
      languageDefRule := some "MC_SwitchMinimal_Start, MC_SwitchMinimal_Match, MC_SwitchMinimal_NoMatch" }
  , { name := "switch-internal"
      category := .preludeEqAndType
      interpreterRef := "stdlib.metta:352-362 (equation-defined helper)"
      languageDefRule := some "MC_Equation (via stdlib equations in space)" }
  , { name := "assert"
      category := .mettaCallControl
      interpreterRef := "Interpreter.lean:372-384"
      languageDefRule := some "MC_Assert_Start, MC_Assert_True, MC_Assert_NotTrue" }

    -- Explicit MettaCall rewrite in HELanguageDef (not a MinimalMeTTa instruction)
  , { name := "match"
      category := .mettaCallControl
      interpreterRef := "HELanguageDef.lean:962-991 (MC_Match, MC_Match_Empty)"
      languageDefRule := some "MC_Match, MC_Match_Empty" }

    -- Minimal instructions: also have HELanguageDef rules for export,
    -- though they also correspond to OSLF MeTTaMinimalInstance layer
  , { name := "unify"
      category := .minimalInstruction
      interpreterRef := "MeTTaMinimalInstance.lean:48-49 (Unify instruction)"
      languageDefRule := some "MC_Unify_Match, MC_Unify_NoMatch" }
  , { name := "superpose"
      category := .minimalInstruction
      interpreterRef := "MeTTaMinimalInstance.lean:58-60 (SuperposeBind)"
      languageDefRule := some "MC_Superpose, MC_Superpose_Empty" }
  , { name := "collapse"
      category := .minimalInstruction
      interpreterRef := "MeTTaMinimalInstance.lean:55-57 (CollapseBind)"
      languageDefRule := some "MC_Collapse" }

    -- Grounded builtins: dispatched via MC_Grounded
  , { name := "+"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319 (grounded dispatch)"
      languageDefRule := some "MC_Grounded" }
  , { name := "-"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "*"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "/"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "%"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "<"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := ">"
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  , { name := "=="
      category := .groundedBuiltin
      interpreterRef := "Interpreter.lean:319"
      languageDefRule := some "MC_Grounded" }
  ]

/-- Operators that need new rewrite rules added to HELanguageDef.lean.
These are ops whose classification requires HELanguageDef rules but none exist yet. -/
def opsNeedingNewRules : List OpEntry :=
  tier1Ops.filter (fun op =>
    op.category == .mettaCallControl && op.languageDefRule.isNone)

/-- Operators in the minimal instruction layer (future OSLF integration). -/
def opsMinimalInstruction : List OpEntry :=
  tier1Ops.filter (fun op => op.category == .minimalInstruction)

/-! ## Smoke checks -/

#eval do
  IO.println s!"Tier 1 ops: {tier1Ops.length}"
  IO.println s!"Ops needing new HELanguageDef rules: {opsNeedingNewRules.length}"
  for op in opsNeedingNewRules do
    IO.println s!"  {op.name} ({op.interpreterRef})"
  IO.println s!"Minimal instruction ops: {opsMinimalInstruction.length}"
  for op in opsMinimalInstruction do
    IO.println s!"  {op.name}"

end Mettapedia.Languages.MeTTa.HE.OpProfile
