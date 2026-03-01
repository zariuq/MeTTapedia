import Mettapedia.OSLF.MeTTaPure.SubjectReduction
import Mettapedia.OSLF.MeTTaCore.SubjectReduction

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
| `SubjectReduction.lean` | 2 | 0 | `typing_subst`, `mettaPure_subject_reduction` (WIP) |
| `TypedLangDef.lean` | 0 | 0 | `TypedLangDef`, `mettaPureTyped` |
-/

namespace Mettapedia.OSLF.MeTTaPure.Assembly

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaPure.Core
open Mettapedia.OSLF.MeTTaPure.Typing
open Mettapedia.OSLF.MeTTaPure.Reduction
open Mettapedia.OSLF.MeTTaPure.SubjectReduction

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

    Uses `mettaPure_subject_reduction` (currently sorry, pending
    completion of the substitution lemma). -/
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
    ¬ Mettapedia.OSLF.MeTTaCore.SubjectReduction
      Mettapedia.OSLF.MeTTaCore.HasType
      Mettapedia.OSLF.MeTTaCore.AtomReduces :=
  Mettapedia.OSLF.MeTTaCore.metta_not_subject_reduction

/-! ## Architectural Properties -/

/-- MeTTa-Pure has exactly 2 sorts: Tm (terms) and Ctx (contexts). -/
theorem mettaPure_two_sorts : mettaPure.types.length = 2 := by decide

/-- MeTTa-Pure has exactly 3 β-reductions (Π, Σ-fst, Σ-snd). -/
theorem mettaPure_three_betas : mettaPure.rewrites.length = 3 := by decide

/-- MeTTa-Pure is intensional: no equations (no extensional axioms). -/
theorem mettaPure_intensional : mettaPure.equations = [] := rfl

/-- MeTTa-Pure has 13 grammar rules (11 Tm + 2 Ctx constructors). -/
theorem mettaPure_thirteen_constructors : mettaPure.terms.length = 13 := by decide

/-- Every one-step reduction is a definitional equality. -/
theorem mettaPure_reduction_sound :
    PureReduces t t' → PureConv t t' :=
  PureReduces_implies_PureConv

/-- Multi-step reduction is a definitional equality. -/
theorem mettaPure_reduction_star_sound :
    PureReducesStar t t' → PureConv t t' :=
  PureReducesStar_implies_PureConv

/-! ## Milestone Status

**Milestone 1** (MeTTa-Pure kernel): 4/5 files complete, 2 sorries remaining.

The crown theorem (`mettaPure_subject_reduction`) and its substitution
dependency (`typing_subst`) remain open.
It is provable by standard locally nameless metatheory:

1. **Substitution lemma**: fvar substitution preserves `PureHasType`
2. **Generation lemmas**: inversion of typing for each constructor
3. **Subject reduction**: induction on `PureHasType` × `PureReduces`

Infrastructure for (1) exists in `Substitution.lean` (`subst_intro`,
`applySubst_openBVar_comm`). The typing rules use cofinite quantification,
making the substitution lemma's β-case follow directly from `subst_intro`.

**Milestone 2** (Bridge to `langReduces`): future.
**Milestone 3** (MeTTa-Core assembly): future. -/

end Mettapedia.OSLF.MeTTaPure.Assembly
