import Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Export

/-!
# PeTTa OSLF Instance — Pipeline to mettail-rust

Composes the PeTTa specification stack into the OSLF pipeline, producing:

1. **OSLF type system** (`pettaOSLF`) with Galois connection ◇ ⊣ □
2. **Rust export** (`pettaRenderRust`) generating `language! { ... }` macro text

## Architecture

```
PeTTaSpace
    │
    │  pettaSpaceToLangDef (LPSoundness.lean)
    ↓
LanguageDef
    │
    ├──→ langOSLF → OSLFTypeSystem    (pettaOSLF)
    │       ↓
    │    langGalois → ◇ ⊣ □           (pettaGalois)
    │
    └──→ renderLanguage → String        (pettaRenderRust)
         writeLanguage → IO Unit        (pettaWriteRust)
```

## References

- `Mettapedia.Languages.MeTTa.PeTTa.LPSoundness` — `pettaSpaceToLangDef`
- `Mettapedia.OSLF.Framework.TypeSynthesis` — `langOSLF`, `langGalois`
- `Mettapedia.OSLF.MeTTaIL.Export` — `renderLanguage`, `writeLanguage`
- `Mettapedia.OSLF.PathMap.OSLFInstance` — reference pattern
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match (Bindings applyBindings matchPattern)
open Mettapedia.OSLF.MeTTaIL.Export
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Logic.LP (leastHerbrandModel GroundAtom)
open Mettapedia.Logic.LP.MeTTaILBridge (encodeReduces mettailLPSig)

/-! ## §1 OSLF Type System -/

/-- The OSLF type system for a PeTTa space (sourceCore, no premise relations).

    The sort parameter `"Expr"` reflects PeTTa's single-sorted nature
    (all values are MeTTa expressions).  This is analogous to PathMap's
    `pathMapOSLF := langOSLF pathMapLang "V"`.

    **Canonical form**: `bundleOSLF (mkBundle .sourceCore s ts ir)`.
    This definition is a compatibility alias for existing code that
    predates the semantic bundle.  See `SemanticBundle.lean`. -/
def pettaOSLF (s : PeTTaSpace) := langOSLF (pettaSpaceToLangDef s) "Expr"

/-- The Galois connection ◇ ⊣ □ for any PeTTa space.

    This is automatic from the generic `langGalois` infrastructure. -/
theorem pettaGalois (s : PeTTaSpace) :
    GaloisConnection (langDiamond (pettaSpaceToLangDef s))
                     (langBox (pettaSpaceToLangDef s)) :=
  langGalois (pettaSpaceToLangDef s)

/-! ## §2 Diamond / Box Characterizations -/

/-- ◇φ(p) in PeTTa = ∃ q, p reduces via PeTTa rules to q ∧ φ(q). -/
theorem pettaDiamond_spec (s : PeTTaSpace) (φ : Pattern → Prop) (p : Pattern) :
    langDiamond (pettaSpaceToLangDef s) φ p ↔
    ∃ q, langReduces (pettaSpaceToLangDef s) p q ∧ φ q :=
  langDiamond_spec (pettaSpaceToLangDef s) φ p

/-- □φ(p) in PeTTa = ∀ q, q reduces via PeTTa rules to p → φ(q). -/
theorem pettaBox_spec (s : PeTTaSpace) (φ : Pattern → Prop) (p : Pattern) :
    langBox (pettaSpaceToLangDef s) φ p ↔
    ∀ q, langReduces (pettaSpaceToLangDef s) q p → φ q :=
  langBox_spec (pettaSpaceToLangDef s) φ p

/-! ## §3 LP Soundness Bridge

For LP-safe PeTTa spaces, the OSLF diamond witnesses correspond to
LP least-model membership. -/

/-- For an LP-safe PeTTa space, any OSLF diamond witness via `ruleApp` is
    backed by LP model membership.

    If `langDiamond (pettaSpaceToLangDef s) φ p` holds because some rule
    `r ∈ s.rules` fires (matching `p` with bindings `bs`, producing `q`),
    and the space is LP-safe, then `encodeReduces p q` is in the LP
    least Herbrand model. -/
theorem pettaOSLF_lp_sound (s : PeTTaSpace) (hs : isLPSafe s)
    (r : RewriteRule) (bs : Bindings) (p q : Pattern)
    (hr    : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm    : bs ∈ matchPattern r.left p)
    (hq    : applyBindings bs r.right = q) :
    encodeReduces p q ∈ leastHerbrandModel (pettaSpaceToLPKB s) :=
  petta_safe_space_ruleApp_lp_sound s hs r bs p q hr hprem hm hq

/-! ## §4 Rust Export -/

/-- Render a PeTTa space as Rust `language! { ... }` macro text for mettail-rust. -/
def pettaRenderRust (s : PeTTaSpace) : String :=
  renderLanguage (pettaSpaceToLangDef s)

/-- Write a PeTTa space as Rust `language! { ... }` macro text to a file. -/
def pettaWriteRust (path : System.FilePath) (s : PeTTaSpace) : IO Unit :=
  writeLanguage path (pettaSpaceToLangDef s)

/-! ## §5 Unfolding Lemmas -/

/-- `pettaOSLF` is exactly `langOSLF` applied to the compiled language def. -/
@[simp]
theorem pettaOSLF_eq (s : PeTTaSpace) :
    pettaOSLF s = langOSLF (pettaSpaceToLangDef s) "Expr" := rfl

/-- The PeTTa language name is "PeTTaSpace". -/
@[simp]
theorem pettaLangDef_name (s : PeTTaSpace) :
    (pettaSpaceToLangDef s).name = "PeTTaSpace" := rfl

/-- The PeTTa language has no congruence collections (flat rules only). -/
@[simp]
theorem pettaLangDef_congruenceCollections (s : PeTTaSpace) :
    (pettaSpaceToLangDef s).congruenceCollections = [] := rfl

/-! ## §6 Summary

**0 sorries. 0 axioms.**

### OSLF Pipeline
- `pettaOSLF` — `PeTTaSpace → OSLFTypeSystem` (uses `RelationEnv.empty`)
- `pettaGalois` — automatic ◇ ⊣ □ Galois connection
- `pettaDiamond_spec` / `pettaBox_spec` — operational characterizations

### LP Bridge
- `pettaOSLF_lp_sound` — diamond witnesses backed by LP model (LP-safe fragment)

### Rust Export
- `pettaRenderRust` — `PeTTaSpace → String` (Rust macro text)
- `pettaWriteRust` — `FilePath → PeTTaSpace → IO Unit`

### Staged OSLF
This file provides the `sourceCore`-level OSLF (no premise-aware relations).
For per-stage OSLF type systems with richer `relEnv`, see
`Mettapedia.Languages.MeTTa.PeTTa.StageFiber`:
- `pettaStageOSLF` — per-stage OSLF using `langOSLFUsing`
- `pettaStageOSLF_sourceCore_eq_pettaOSLF` — compatibility with `pettaOSLF`
-/

end Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance
