import Mettapedia.Languages.MeTTa.PeTTa.OSLFPackage
import Mettapedia.Languages.MeTTa.PeTTa.GSLTVertex
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises

/-!
# PeTTa Stage Fiber — ForwardFiber over PeTTaStage

Since all 4 PeTTa stages share the same `LanguageDef`, every `ForwardMorphism`
between stages is identity. The value of the staged fiber is:
- per-stage `OSLFTypeSystem` instances with potentially different `relEnv`
- categorical composition hook for GSLT integration
- compatibility with the existing unit-indexed `pettaForwardFiber`

## Key Theorems

- `pettaStageFiber` — the fiber over `PeTTaStage`
- `pettaStageOSLF` — per-stage OSLF type system (using `langOSLFUsing`)
- `pettaStageFiber_sourceCore_eq_forwardFiber` — compatibility with existing fiber

## References

- Plan: `cosmic-scribbling-thacker.md` Step 4
- `Mettapedia.OSLF.Framework.HypercubeGSLTFunctor` — `ForwardFiber`, `ForwardMorphism`
- `Mettapedia.OSLF.Framework.TypeSynthesis` — `langOSLFUsing`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.StageFiber

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv applyPremisesWithEnv)
open Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv (empty_le)
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises (DeclReducesWithPremises
  declReducesWithPremises_mono_relEnv)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
open Mettapedia.Languages.MeTTa.PeTTa.StageIndex
open Mettapedia.Languages.MeTTa.PeTTa.OSLFPackage
open Mettapedia.Languages.MeTTa.PeTTa.LPSoundness
open Mettapedia.Languages.MeTTa.PeTTa.GSLTVertex
open Mettapedia.Languages.MeTTa.PeTTa.OSLFInstance

/-! ## §1 Identity Stage Morphism -/

/-- Identity forward morphism between any two PeTTa stages.

    Since all stages share the same `LanguageDef`, the morphism is trivially
    identity with single-step forward simulation. -/
def pettaStageIdMorphism (s : PeTTaSpace) (_v _w : PeTTaStage) (_h : _v ≤ _w) :
    ForwardMorphism (pettaSpaceToLangDef s) (pettaSpaceToLangDef s) where
  mapTerm := id
  forward_sim _ q hred := ⟨q, .single hred, rfl⟩

/-! ## §2 Forward Fiber over PeTTaStage -/

/-- The PeTTa forward fiber indexed by the 4-stage chain.

    Each stage maps to the same `LanguageDef` (`pettaSpaceToLangDef s`).
    All morphisms are identities. The semantic enrichment per stage is
    captured by `pettaPkg` (relEnv, exec/scope contracts), not by the
    fiber's language field. -/
def pettaStageFiber (s : PeTTaSpace) : ForwardFiber PeTTaStage where
  lang  := fun _ => pettaSpaceToLangDef s
  morph := fun h => pettaStageIdMorphism s _ _ h

/-! ## §3 Per-Stage OSLF Type Systems -/

/-- The OSLF type system at a given PeTTa stage.

    Uses `langOSLFUsing` with the stage's `relEnv` from `pettaPkg`.
    - At `sourceCore`: `relEnv = empty`, equivalent to `pettaOSLF`
    - At `queryCore`+: `relEnv = pettaQueryRelEnv s`, enabling premise-aware
      reductions and correspondingly richer OSLF types -/
def pettaStageOSLF (s : PeTTaSpace) (stage : PeTTaStage) :=
  langOSLFUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang "Expr"

/-- The Galois connection ◇ ⊣ □ at each stage. -/
theorem pettaStageGalois (s : PeTTaSpace) (stage : PeTTaStage) :
    GaloisConnection
      (langDiamondUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang)
      (langBoxUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang) :=
  langGaloisUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang

/-! ## §4 Compatibility Bridges -/

/-- The staged fiber at `sourceCore` agrees with the existing unit-indexed fiber. -/
theorem pettaStageFiber_sourceCore_eq_forwardFiber (s : PeTTaSpace) :
    (pettaStageFiber s).lang .sourceCore = (pettaForwardFiber s).lang () := rfl

/-- The OSLF type system at `sourceCore` agrees with `pettaOSLF`. -/
theorem pettaStageOSLF_sourceCore_eq_pettaOSLF (s : PeTTaSpace) :
    pettaStageOSLF s .sourceCore = pettaOSLF s := rfl

/-- The fiber's language at any stage is `pettaSpaceToLangDef s`. -/
@[simp]
theorem pettaStageFiber_lang (s : PeTTaSpace) (stage : PeTTaStage) :
    (pettaStageFiber s).lang stage = pettaSpaceToLangDef s := rfl

/-- The identity morphism maps terms to themselves at every stage. -/
@[simp]
theorem pettaStageIdMorphism_mapTerm (s : PeTTaSpace) (v w : PeTTaStage)
    (h : v ≤ w) (p : Pattern) :
    (pettaStageIdMorphism s v w h).mapTerm p = p := rfl

/-! ## §5 Diamond/Box at Each Stage -/

/-- ◇φ(p) at a given stage = ∃ q, p reduces (via stage's relEnv) to q ∧ φ(q). -/
theorem pettaStageDiamond_spec (s : PeTTaSpace) (stage : PeTTaStage)
    (φ : Pattern → Prop) (p : Pattern) :
    langDiamondUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang φ p ↔
    ∃ q, langReducesUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang p q ∧ φ q :=
  langDiamondUsing_spec (pettaPkg stage s).relEnv (pettaPkg stage s).lang φ p

/-- □φ(p) at a given stage = ∀ q, q reduces (via stage's relEnv) to p → φ(q). -/
theorem pettaStageBox_spec (s : PeTTaSpace) (stage : PeTTaStage)
    (φ : Pattern → Prop) (p : Pattern) :
    langBoxUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang φ p ↔
    ∀ q, langReducesUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang q p → φ q :=
  langBoxUsing_spec (pettaPkg stage s).relEnv (pettaPkg stage s).lang φ p

/-! ## §6 Stage Refinement: sourceCore ⊆ queryCore

The key refinement property: every `sourceCore` reduction is also a `queryCore`
reduction. This follows from the fact that premise-free reductions
(`r.premises = []`) produce the same results under **any** `relEnv`, since
`applyPremisesWithEnv relEnv lang [] seed = [seed]` by definition (foldl over
empty list).

For rules with premises, extending the relEnv can only add more satisfying
bindings (more tuples = more premise resolutions), never remove existing ones.
The general relEnv-monotonicity theorem is deferred; we prove the
premise-free fragment which covers the LP-safe PeTTa rules. -/

/-- `applyPremisesWithEnv` on an empty premise list returns `[seed]`,
    regardless of the relation environment. -/
theorem applyPremisesWithEnv_nil (relEnv : RelationEnv) (lang : LanguageDef)
    (seed : Mettapedia.OSLF.MeTTaIL.Match.Bindings) :
    applyPremisesWithEnv relEnv lang [] seed = [seed] := rfl

/-- Premise-free `DeclReducesWithPremises` is relEnv-agnostic:
    if a rule with `r.premises = []` fires under one relEnv, it fires
    under any relEnv (since empty premise lists are trivially satisfied). -/
theorem declReduces_premiseFree_relEnv_agnostic
    {lang : LanguageDef} {p q : Pattern}
    {relEnv₁ relEnv₂ : RelationEnv}
    (hred : DeclReducesWithPremises relEnv₁ lang p q)
    (hpf : ∀ r ∈ lang.rewrites, r.premises = []) :
    DeclReducesWithPremises relEnv₂ lang p q := by
  induction hred with
  | topRule r hr bs0 hbs0 bs hprem hq =>
    have hempty := hpf r hr
    rw [hempty] at hprem
    -- hprem : bs ∈ applyPremisesWithEnv relEnv₁ lang [] bs0 = [bs0]
    -- so bs = bs0, and we can construct with relEnv₂
    exact .topRule r hr bs0 hbs0 bs (hempty ▸ hprem) hq
  | congElem hct i hi r hr bs0 hbs0 bs hprem hq =>
    have hempty := hpf r hr
    rw [hempty] at hprem
    exact .congElem hct i hi r hr bs0 hbs0 bs (hempty ▸ hprem) hq

/-- sourceCore reductions are preserved at queryCore (and above).

    Since `pettaSpaceToLangDef s` uses `s.rules` directly and the fiber's
    `langReduces`/`langReducesUsing` wraps `DeclReducesWithPremises`,
    this theorem bridges the relEnv gap between stages.

    The premise-free assumption `hpf` holds for LP-safe PeTTa spaces
    where all rules have `r.premises = []`. -/
theorem sourceCore_refines_queryCore (s : PeTTaSpace) {p q : Pattern}
    (hpf : ∀ r ∈ s.rules, r.premises = [])
    (hred : langReducesUsing RelationEnv.empty (pettaSpaceToLangDef s) p q) :
    langReducesUsing (pettaQueryRelEnv s) (pettaSpaceToLangDef s) p q := by
  unfold langReducesUsing at hred ⊢
  exact declReduces_premiseFree_relEnv_agnostic hred (by
    intro r hr; exact hpf r hr)

/-- Generalization: sourceCore refines any later stage (under premise-free rules). -/
theorem sourceCore_refines_stage (s : PeTTaSpace) (stage : PeTTaStage) {p q : Pattern}
    (hpf : ∀ r ∈ s.rules, r.premises = [])
    (hred : langReducesUsing (pettaPkg .sourceCore s).relEnv
              (pettaPkg .sourceCore s).lang p q) :
    langReducesUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang p q := by
  simp only [pettaPkg_lang_constant] at hred ⊢
  cases stage with
  | sourceCore => exact hred
  | queryCore => exact sourceCore_refines_queryCore s hpf hred
  | statefulCore => exact sourceCore_refines_queryCore s hpf hred
  | boundaryAware => exact sourceCore_refines_queryCore s hpf hred

/-! ## §7 General RelEnv Monotonicity

The general refinement property: if `relEnv₁ ≤ relEnv₂`, then every reduction
under `relEnv₁` is also a reduction under `relEnv₂`. This subsumes the
premise-free refinement in §6 and covers rules with arbitrary premises. -/

/-- `langReducesUsing` is monotone in the relation environment. -/
theorem langReducesUsing_mono_relEnv {lang : LanguageDef}
    {relEnv₁ relEnv₂ : RelationEnv} (hle : relEnv₁ ≤ relEnv₂)
    {p q : Pattern}
    (hred : langReducesUsing relEnv₁ lang p q) :
    langReducesUsing relEnv₂ lang p q :=
  declReducesWithPremises_mono_relEnv hle hred

/-- sourceCore reductions refine queryCore (general, no premise-free assumption). -/
theorem sourceCore_refines_queryCore_general (s : PeTTaSpace) {p q : Pattern}
    (hred : langReducesUsing RelationEnv.empty (pettaSpaceToLangDef s) p q) :
    langReducesUsing (pettaQueryRelEnv s) (pettaSpaceToLangDef s) p q :=
  langReducesUsing_mono_relEnv (empty_le _) hred

/-- sourceCore reductions refine any later stage (general). -/
theorem sourceCore_refines_stage_general (s : PeTTaSpace) (stage : PeTTaStage)
    {p q : Pattern}
    (hred : langReducesUsing (pettaPkg .sourceCore s).relEnv
              (pettaPkg .sourceCore s).lang p q) :
    langReducesUsing (pettaPkg stage s).relEnv (pettaPkg stage s).lang p q := by
  simp only [pettaPkg_lang_constant] at hred ⊢
  cases stage with
  | sourceCore => exact hred
  | _ => exact sourceCore_refines_queryCore_general s hred

/-! ## §8 Honest 2-Class OSLF Acknowledgment

queryCore, statefulCore, and boundaryAware all use `pettaQueryRelEnv s` as their
`relEnv` (and the same `LanguageDef`). Therefore they produce the **same** OSLF
type system. Only 2 distinct OSLF classes exist:
- **Class A**: `sourceCore` — uses `RelationEnv.empty`
- **Class B**: `queryCore` / `statefulCore` / `boundaryAware` — uses `pettaQueryRelEnv s`

The 4 stages remain meaningful for the *semantic package* (exec/scope contract
slices), but at the OSLF level there are exactly 2 type systems. -/

/-- queryCore and statefulCore produce the same OSLF type system. -/
theorem pettaStageOSLF_queryCore_eq_statefulCore (s : PeTTaSpace) :
    pettaStageOSLF s .queryCore = pettaStageOSLF s .statefulCore := rfl

/-- queryCore and boundaryAware produce the same OSLF type system. -/
theorem pettaStageOSLF_queryCore_eq_boundaryAware (s : PeTTaSpace) :
    pettaStageOSLF s .queryCore = pettaStageOSLF s .boundaryAware := rfl

/-- statefulCore and boundaryAware produce the same OSLF type system. -/
theorem pettaStageOSLF_statefulCore_eq_boundaryAware (s : PeTTaSpace) :
    pettaStageOSLF s .statefulCore = pettaStageOSLF s .boundaryAware := rfl

/-! ## §9 Summary

**0 sorries. 0 axioms.**

- `pettaStageFiber` — 4-stage forward fiber (identity morphisms)
- `pettaStageOSLF` — per-stage OSLF type system with stage-specific `relEnv`
- `pettaStageGalois` — automatic ◇ ⊣ □ per stage
- Compatibility: `sourceCore` = existing `pettaForwardFiber` / `pettaOSLF`
- General monotonicity: `langReducesUsing_mono_relEnv`, `sourceCore_refines_stage_general`
- Honest 2-class: queryCore/statefulCore/boundaryAware share same OSLF (all `rfl`)
-/

end Mettapedia.Languages.MeTTa.PeTTa.StageFiber
