import Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance
import Mettapedia.OSLF.Framework.HypercubeGSLTFunctor

/-!
# PeTTa GSLT Vertex Integration

Embeds a PeTTa space into the GSLT framework as a degenerate unit-indexed
forward fiber, following the governance pattern (`GovernanceGSLTVertex.lean`).

## Architecture

```
PeTTaSpace s
    │
    │  pettaSpaceToLangDef
    ↓
LanguageDef
    │
    │  pettaIdMorphism (identity forward simulation)
    ↓
ForwardMorphism (pettaSpaceToLangDef s) (pettaSpaceToLangDef s)
    │
    │  pettaForwardFiber (unit-indexed)
    ↓
ForwardFiber Unit
```

## Design Note

Like `governanceForwardFiber`, the PeTTa fiber is unit-indexed (single vertex,
identity morphism).  This is the correct abstraction for a standalone language
that doesn't vary along the GSLT hypercube axes.  The fiber provides the
categorical hook for composing PeTTa with other GSLT-indexed languages.

## References

- `Mettapedia.OSLF.Framework.GovernanceGSLTVertex` — reference pattern
- `Mettapedia.OSLF.Framework.HypercubeGSLTFunctor` — `ForwardFiber`, `ForwardMorphism`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.GSLTVertex

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance

/-! ## §1 Identity Forward Morphism -/

/-- The identity forward simulation for a PeTTa space: the language does not
    change along the unique morphism in the unit preorder. -/
def pettaIdMorphism (s : PeTTaSpace) :
    ForwardMorphism (pettaSpaceToLangDef s) (pettaSpaceToLangDef s) where
  mapTerm := id
  forward_sim _ q hred := ⟨q, .single hred, rfl⟩

/-! ## §2 Unit-Indexed Forward Fiber -/

/-- The PeTTa forward fiber: a degenerate fiber indexed by `Unit` where the
    language is constantly `pettaSpaceToLangDef s`.  All morphisms are identities. -/
def pettaForwardFiber (s : PeTTaSpace) : ForwardFiber Unit where
  lang  := fun _ => pettaSpaceToLangDef s
  morph := fun _ => pettaIdMorphism s

/-! ## §3 Fiber Properties -/

/-- The PeTTa OSLF type system equals the one produced by `langOSLF`. -/
theorem pettaForwardFiber_oslf (s : PeTTaSpace) :
    pettaOSLF s = langOSLF (pettaSpaceToLangDef s) "Expr" := rfl

/-- ◇ in the PeTTa fiber = existence of a one-step successor. -/
theorem pettaForwardFiber_diamond (s : PeTTaSpace) (φ : Pattern → Prop) (p : Pattern) :
    langDiamond (pettaSpaceToLangDef s) φ p ↔
    ∃ q, langReduces (pettaSpaceToLangDef s) p q ∧ φ q :=
  langDiamond_spec (pettaSpaceToLangDef s) φ p

/-- □ in the PeTTa fiber = all predecessors satisfy φ. -/
theorem pettaForwardFiber_box (s : PeTTaSpace) (φ : Pattern → Prop) (p : Pattern) :
    langBox (pettaSpaceToLangDef s) φ p ↔
    ∀ q, langReduces (pettaSpaceToLangDef s) q p → φ q :=
  langBox_spec (pettaSpaceToLangDef s) φ p

/-- The identity morphism maps terms to themselves. -/
@[simp]
theorem pettaIdMorphism_mapTerm (s : PeTTaSpace) (p : Pattern) :
    (pettaIdMorphism s).mapTerm p = p := rfl

/-- The fiber's language at unit is exactly `pettaSpaceToLangDef s`. -/
@[simp]
theorem pettaForwardFiber_lang (s : PeTTaSpace) (u : Unit) :
    (pettaForwardFiber s).lang u = pettaSpaceToLangDef s := rfl

/-! ## §4 Summary

**0 sorries. 0 axioms.**

- `pettaIdMorphism` — identity forward simulation
- `pettaForwardFiber` — unit-indexed GSLT fiber
- Diamond/Box characterizations for the fiber

### Staged Fiber

The unit-indexed fiber embeds as the `sourceCore` stage of the 4-stage
`pettaStageFiber`. See `Mettapedia.Languages.MeTTa.PeTTa.StageFiber` for:
- `pettaStageFiber_sourceCore_eq_forwardFiber` — compatibility bridge
- `pettaStageOSLF_sourceCore_eq_pettaOSLF` — OSLF compatibility
-/

end Mettapedia.Languages.MeTTa.PeTTa.GSLTVertex
