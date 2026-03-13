import Mettapedia.Languages.MeTTa.Pure.SubjectReduction
import Mettapedia.Languages.MeTTa.Core.SubjectReduction

/-!
# MeTTa-Pure: Typed Language Definition Assembly

Bundles MeTTa-Pure's kernel, typing, reduction, and subject reduction
into a single `TypedLangDef` object, and contrasts it with MeTTa's
current type system.

## Architecture

```
MeTTa-Pure   = initial intensional dependent kernel (subject reduction ✓)
MeTTa-Core   = initial admissible MeTTa home (Milestone 2, future)
MeTTa-Full-* = conservative extension profiles (HE, PeTTa, PathMap, ...)
```

MeTTa-Pure fills the architectural gap identified by
`metta_not_subject_reduction`: MeTTa's current `HasType` (annotation
lookup) provably fails subject reduction, while MeTTa-Pure's `PureHasType`
(judgment-based) is designed to satisfy it.

## Summary

- `TypedLangDef` — structure bundling language + typing + reduction + SR
- `mettaPureTyped` — MeTTa-Pure as a `TypedLangDef`
- Contrast theorem: documents the SR gap between Pure and Current
- `mettaPure_architecture_properties` — key architectural properties

## File Inventory (Milestone 1)

| File | Sorries | Axioms | Key Definitions |
|------|---------|--------|-----------------|
| `Core.lean` | 0 | 0 | `mettaPure : LanguageDef`, OSLF pipeline |
| `Typing.lean` | 0 | 0 | `PureHasType`, `PureConv` (cofinite) |
| `Reduction.lean` | 0 | 0 | `PureReduces`, `PureReducesStar` |
| `SubjectReduction.lean` | 0 | 0 | `typing_subst`, `mettaPure_subject_reduction` |
| `TypedLangDef.lean` | 0 | 0 | `TypedLangDef`, `mettaPureTyped` |
-/

namespace Mettapedia.Languages.MeTTa.Pure.Assembly

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.Fragment
open Mettapedia.Languages.MeTTa.Pure.Typing
open Mettapedia.Languages.MeTTa.Pure.Reduction
open Mettapedia.Languages.MeTTa.Pure.SubjectReduction
open Mettapedia.Languages.MeTTa.Pure.FVarSubst (PureReducesStar_implies_PureConv)
open Mettapedia.OSLF.MeTTaIL.Substitution (lc_at)

/-! ## TypedLangDef Structure -/

/-- A typed language definition: bundles a MeTTa-IL language, typing
    judgment, reduction relation, and subject reduction proof. -/
structure TypedLangDef where
  /-- The operational language (a `LanguageDef` instance). -/
  lang : LanguageDef
  /-- Context type for typing judgments. -/
  Ctx : Type
  /-- Typing judgment: `Γ ⊢ t : A`. -/
  hasType : Ctx → Pattern → Pattern → Prop
  /-- One-step reduction: `t ~> t'`. -/
  reduces : Pattern → Pattern → Prop
  /-- Subject reduction: typing is preserved under reduction. -/
  subject_reduction : ∀ {Γ t t' A},
    hasType Γ t A → reduces t t' → hasType Γ t' A

/-- MeTTa-Pure as a `TypedLangDef`.

    Uses `mettaPure_subject_reduction` from `SubjectReduction.lean`. -/
noncomputable def mettaPureTyped : TypedLangDef where
  lang := mettaPure
  Ctx := PureCtx
  hasType := PureHasType
  reduces := PureReduces
  subject_reduction := mettaPure_subject_reduction

/-! ## Contrast: MeTTa-Pure vs MeTTa-Current -/

/-- MeTTa's current `HasType` (annotation-based lookup) provably
    fails subject reduction.

    This is the sorry-free theorem from `MeTTaCore/SubjectReduction.lean`. -/
theorem metta_current_sr_fails :
    ¬ Mettapedia.Languages.MeTTa.Core.SubjectReduction
      Mettapedia.Languages.MeTTa.Core.HasType
      Mettapedia.Languages.MeTTa.Core.AtomReduces :=
  Mettapedia.Languages.MeTTa.Core.metta_not_subject_reduction

/-! ## Architectural Properties -/

/-- MeTTa-Pure has exactly 2 sorts: Tm (terms) and Ctx (contexts). -/
theorem mettaPure_two_sorts : mettaPure.types.length = 2 := by decide

/-- MeTTa-Pure has exactly 3 β-reductions (Π, Σ-fst, Σ-snd). -/
theorem mettaPure_three_betas : mettaPure.rewrites.length = 3 := by decide

/-- MeTTa-Pure is intensional: no equations (no extensional axioms). -/
theorem mettaPure_intensional : mettaPure.equations = [] := rfl

/-- MeTTa-Pure has 13 grammar rules (11 Tm + 2 Ctx constructors). -/
theorem mettaPure_thirteen_constructors : mettaPure.terms.length = 13 := by decide

/-- Every one-step reduction of a locally closed term is a definitional equality. -/
theorem mettaPure_reduction_sound {t t' : Pattern}
    (hlc : lc_at 0 t = true) (hpure : PureTmPattern t) (h : PureReduces t t') : PureConv t t' :=
  PureReduces_implies_PureConv h hlc hpure

/-- Multi-step reduction of a locally closed term is a definitional equality. -/
theorem mettaPure_reduction_star_sound {t t' : Pattern}
    (hlc : lc_at 0 t = true) (hpure : PureTmPattern t) (h : PureReducesStar t t') : PureConv t t' :=
  PureReducesStar_implies_PureConv h hlc hpure

/-- Typed one-step reduction is a definitional equality. -/
theorem mettaPure_typed_reduction_sound {Γ : PureCtx} {t t' A : Pattern}
    (ht : PureHasType Γ t A) (h : PureReduces t t') : PureConv t t' :=
  PureReduces_implies_PureConv h (typing_lc ht) (typing_term_pure ht)

/-- Typed multi-step reduction is a definitional equality. -/
theorem mettaPure_typed_reduction_star_sound {Γ : PureCtx} {t t' A : Pattern}
    (ht : PureHasType Γ t A) (h : PureReducesStar t t') : PureConv t t' :=
  PureReducesStar_implies_PureConv h (typing_lc ht) (typing_term_pure ht)

/-! ## Milestone Status

**Milestone 1** (MeTTa-Pure kernel): substitution and subject-reduction
theorems are present in `SubjectReduction.lean`.

Current integration status should be read from project build targets and
framework trackers (rather than this historical milestone note).

**Milestone 2** (Bridge to `langReduces`): future.
**Milestone 3** (MeTTa-Core assembly): future. -/

end Mettapedia.Languages.MeTTa.Pure.Assembly
