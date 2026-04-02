import Mettapedia.Languages.GF.OSLFBridge
import Mettapedia.Languages.GF.GFCoreNTTDiagnostics
import Mettapedia.Languages.GF.OSLFScopeComposition
import Mettapedia.OSLF.MeTTaIL.LogicSemantics
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Modal + Logic Composition: The Hypercube Propositional Layer

Composes the two independently-built OSLF semantic layers:

1. **Modal layer**: ◇/□ from structural rewrites (tense, voice, embedding)
2. **Logic layer**: Datalog premises evaluated via LP.Core (least Herbrand model)

The composition: Datalog-derived facts feed into the rewrite engine as
`RelationEnv`, producing modal types that account for BOTH structural
reduction AND logical derivation.

## The key insight

`langGaloisUsing relEnv lang` provides a Galois connection ◇ ⊣ □ for
ANY `RelationEnv`. When `relEnv` comes from LP.Core's least Herbrand
model (which is PROVEN sound and minimal), the modal types inherit the
logical correctness guarantees.

This completes the hypercube: operational semantics (rewrites) +
propositional logic (Datalog premises) → modal type system (◇/□).

## Council

- **Meredith**: "This is the third face of the hypercube — propositional."
- **Stay**: "The Galois connection is parametric in the relation environment."
- **Pfenning**: "LP.Core's T_P gives the propositional semantics; OSLF's
  change-of-base gives the modal semantics; the composition is the adjunction
  parametrized by the logic."
-/

namespace Mettapedia.Languages.GF.Examples.ModalLogicComposition

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.LogicSemantics
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.GF.GFCoreNTTDiagnostics
open Mettapedia.Languages.GF.GFCoreOSLFBridge
open Mettapedia.Languages.GF.OSLFScopeComposition

-- ═══════════════════════════════════════════════════════════════════
-- Part 1: The Galois connection is parametric in RelationEnv
-- ═══════════════════════════════════════════════════════════════════

/-- **Core composition theorem**: for ANY relation environment (including
    one derived from LP.Core's least Herbrand model), the ◇ ⊣ □ Galois
    connection holds.

    This means: if you derive facts via Datalog rules and feed them into
    the OSLF rewrite engine as premises, the resulting modal types still
    form a Galois pair. The logic layer composes with the modal layer
    without breaking the adjunction. -/
theorem modal_logic_galois (relEnv : RelationEnv) (lang : LanguageDef) :
    GaloisConnection (langDiamondUsing relEnv lang) (langBoxUsing relEnv lang) :=
  langGaloisUsing relEnv lang

/-- Diamond specification with logic: ◇ accounts for premise-aware reductions. -/
theorem modal_logic_diamond_spec (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern) :
    langDiamondUsing relEnv lang φ p ↔
    ∃ q, langReducesUsing relEnv lang p q ∧ φ q :=
  langDiamondUsing_spec relEnv lang φ p

/-- Box specification with logic: □ accounts for premise-aware predecessors. -/
theorem modal_logic_box_spec (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern) :
    langBoxUsing relEnv lang φ p ↔
    ∀ q, langReducesUsing relEnv lang q p → φ q :=
  langBoxUsing_spec relEnv lang φ p

-- ═══════════════════════════════════════════════════════════════════
-- Part 2: Monotonicity of the composed system
-- ═══════════════════════════════════════════════════════════════════

/-- The composed ◇ is monotone: if φ ≤ ψ then ◇_logic(φ) ≤ ◇_logic(ψ). -/
theorem modal_logic_diamond_mono (relEnv : RelationEnv) (lang : LanguageDef) :
    Monotone (langDiamondUsing relEnv lang) :=
  (modal_logic_galois relEnv lang).monotone_l

/-- The composed □ is monotone: if φ ≤ ψ then □_logic(φ) ≤ □_logic(ψ). -/
theorem modal_logic_box_mono (relEnv : RelationEnv) (lang : LanguageDef) :
    Monotone (langBoxUsing relEnv lang) :=
  (modal_logic_galois relEnv lang).monotone_u

/-- The Galois unit: φ ≤ □_logic(◇_logic(φ)). -/
theorem modal_logic_unit (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) :
    φ ≤ langBoxUsing relEnv lang (langDiamondUsing relEnv lang φ) :=
  (modal_logic_galois relEnv lang).le_u_l φ

/-- The Galois counit: ◇_logic(□_logic(φ)) ≤ φ. -/
theorem modal_logic_counit (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) :
    langDiamondUsing relEnv lang (langBoxUsing relEnv lang φ) ≤ φ :=
  (modal_logic_galois relEnv lang).l_u_le φ

-- ═══════════════════════════════════════════════════════════════════
-- Part 3: Scope ordering lifts through the composed system
-- ═══════════════════════════════════════════════════════════════════

/-- Scope ordering is preserved by the logic-aware ◇.
    Same as `diamond_scope_composition` but parameterized by relEnv. -/
theorem modal_logic_scope_composition (relEnv : RelationEnv) (lang : LanguageDef)
    (scopeInverse scopeSurface : Pattern → Prop)
    (h : scopeInverse ≤ scopeSurface) :
    langDiamondUsing relEnv lang scopeInverse ≤
    langDiamondUsing relEnv lang scopeSurface :=
  modal_logic_diamond_mono relEnv lang h

-- ═══════════════════════════════════════════════════════════════════
-- Part 4: Concrete instantiation for GF
-- ═══════════════════════════════════════════════════════════════════

/-- The GF semantic kernel with empty relation environment (no Datalog premises).
    This recovers the standard ◇/□ from the earlier demo. -/
theorem gf_modal_without_logic :
    GaloisConnection
      (langDiamondUsing .empty paperLangKR)
      (langBoxUsing .empty paperLangKR) :=
  modal_logic_galois .empty paperLangKR

/-- The GF semantic kernel composes with ANY logic layer.
    Whatever Datalog facts you derive and feed in, the modal
    types still form a Galois pair. -/
theorem gf_modal_with_any_logic (relEnv : RelationEnv) :
    GaloisConnection
      (langDiamondUsing relEnv paperLangKR)
      (langBoxUsing relEnv paperLangKR) :=
  modal_logic_galois relEnv paperLangKR

-- ═══════════════════════════════════════════════════════════════════
-- Part 5: The three-layer summary
-- ═══════════════════════════════════════════════════════════════════

/-- **The hypercube composition**: three independently-built layers compose.

    1. **Structural** (rewrites): 44 rules in 11 families → reduction relation
    2. **Propositional** (logic): Datalog premises → RelationEnv → premise-aware reduction
    3. **Modal** (types): ◇ ⊣ □ Galois connection → native type theory

    All three compose via `langGaloisUsing`: the Galois connection is
    parametric in the relation environment, so plugging in LP.Core-derived
    facts preserves the adjunction.

    The LanguageDef is the single source of truth:
    - `.rewrites` → structural layer
    - `.logic` (DatalogClause) → propositional layer
    - OSLF framework → modal layer (automatic) -/
theorem hypercube_three_layers (lang : LanguageDef) (relEnv : RelationEnv) :
    -- (1) The Galois connection holds with logic
    GaloisConnection (langDiamondUsing relEnv lang) (langBoxUsing relEnv lang) ∧
    -- (2) ◇ is monotone (preserves predicate ordering)
    Monotone (langDiamondUsing relEnv lang) ∧
    -- (3) □ is monotone
    Monotone (langBoxUsing relEnv lang) ∧
    -- (4) Unit: φ ≤ □(◇φ)
    (∀ φ, φ ≤ langBoxUsing relEnv lang (langDiamondUsing relEnv lang φ)) ∧
    -- (5) Counit: ◇(□φ) ≤ φ
    (∀ φ, langDiamondUsing relEnv lang (langBoxUsing relEnv lang φ) ≤ φ) :=
  ⟨ modal_logic_galois relEnv lang
  , modal_logic_diamond_mono relEnv lang
  , modal_logic_box_mono relEnv lang
  , modal_logic_unit relEnv lang
  , modal_logic_counit relEnv lang ⟩

end Mettapedia.Languages.GF.Examples.ModalLogicComposition
