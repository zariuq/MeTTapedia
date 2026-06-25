import Mathlib.Tactic

namespace Mettapedia.PLN.Comparisons.NARS.NARSMettaTruthFunctions

/-!
# NARS Truth Functions (MeTTa / PeTTa `lib_nars.metta`)

This file mirrors the numerical truth-value formulas used in the MeTTa NARS library:
`hyperon/PeTTa/lib/lib_nars.metta`.

We keep this file purely about formulas (no semantic derivations here).
-/

/-- A lightweight (frequency, confidence) pair. -/
structure TV where
  f : ℝ
  c : ℝ

namespace TV

@[simp] theorem eta (t : TV) : TV.mk t.f t.c = t := by
  cases t
  rfl

end TV

/-! ## Utility: confidence ↔ weight -/

noncomputable def c2w (c : ℝ) : ℝ := c / (1 - c)

noncomputable def w2c (w : ℝ) : ℝ := w / (w + 1)

/-! ## Core syllogisms -/

noncomputable def truthDeduction (t1 t2 : TV) : TV :=
  -- `lib_nars.metta`: (f1*f2, (f1*f2)*(c1*c2))
  ⟨t1.f * t2.f, (t1.f * t2.f) * (t1.c * t2.c)⟩

noncomputable def truthAbduction (t1 t2 : TV) : TV :=
  -- `lib_nars.metta`: (f2, w2c (f1*c1*c2))
  ⟨t2.f, w2c (t1.f * t1.c * t2.c)⟩

noncomputable def truthInduction (t1 t2 : TV) : TV :=
  -- `lib_nars.metta`: Induction is Abduction with swapped args.
  truthAbduction t2 t1

/-! ### Alternative names (SourceRule / SinkRule)

Category-theoretic perspective:
- **SourceRule** (Induction): B → A, B → C ⊢ A → C  (B is common source, cospan completion)
- **SinkRule** (Abduction): A → B, C → B ⊢ A → C  (B is common sink, span completion)
-/

/-- SourceRule = Induction (B is the common source) -/
noncomputable abbrev truthSourceRule := truthInduction

/-- SinkRule = Abduction (B is the common sink) -/
noncomputable abbrev truthSinkRule := truthAbduction

noncomputable def truthExemplification (t1 t2 : TV) : TV :=
  -- `lib_nars.metta`: (1, w2c (f1*f2*c1*c2))
  ⟨1, w2c (t1.f * t2.f * (t1.c * t2.c))⟩

/-! ## Structural rules and connectives -/

noncomputable def truthStructuralDeduction (t : TV) : TV :=
  truthDeduction t ⟨1, 0.9⟩

noncomputable def truthNegation (t : TV) : TV :=
  ⟨1 - t.f, t.c⟩

noncomputable def truthStructuralDeductionNegated (t : TV) : TV :=
  truthNegation (truthStructuralDeduction t)

noncomputable def truthIntersection (t1 t2 : TV) : TV :=
  ⟨t1.f * t2.f, t1.c * t2.c⟩

noncomputable def truthStructuralIntersection (t : TV) : TV :=
  truthIntersection t ⟨1, 0.9⟩

noncomputable def truthOr (a b : ℝ) : ℝ :=
  1 - (1 - a) * (1 - b)

noncomputable def truthComparison (t1 t2 : TV) : TV :=
  let f0 := truthOr t1.f t2.f
  let f :=
    if f0 = 0 then
      0
    else
      (t1.f * t2.f) / f0
  let c := w2c (f0 * (t1.c * t2.c))
  ⟨f, c⟩

noncomputable def truthAnalogy (t1 t2 : TV) : TV :=
  ⟨t1.f * t2.f, (t1.c * t2.c) * t2.f⟩

noncomputable def truthResemblance (t1 t2 : TV) : TV :=
  ⟨t1.f * t2.f, (t1.c * t2.c) * truthOr t1.f t2.f⟩

noncomputable def truthUnion (t1 t2 : TV) : TV :=
  ⟨truthOr t1.f t2.f, t1.c * t2.c⟩

noncomputable def truthDifference (t1 t2 : TV) : TV :=
  ⟨t1.f * (1 - t2.f), t1.c * t2.c⟩

/-! ## Decomposition family (NAL-3 style) -/

noncomputable def truthDecomposePNN (t1 t2 : TV) : TV :=
  let fn := t1.f * (1 - t2.f)
  ⟨1 - fn, fn * (t1.c * t2.c)⟩

noncomputable def truthDecomposeNPP (t1 t2 : TV) : TV :=
  let f := (1 - t1.f) * t2.f
  ⟨f, f * (t1.c * t2.c)⟩

noncomputable def truthDecomposePNP (t1 t2 : TV) : TV :=
  let f := t1.f * (1 - t2.f)
  ⟨f, f * (t1.c * t2.c)⟩

noncomputable def truthDecomposePPP (t1 t2 : TV) : TV :=
  truthDecomposeNPP (truthNegation t1) t2

noncomputable def truthDecomposeNNN (t1 t2 : TV) : TV :=
  let fn := (1 - t1.f) * (1 - t2.f)
  ⟨1 - fn, fn * (t1.c * t2.c)⟩

/-! ## Other utilities -/

noncomputable def truthEternalize (t : TV) : TV :=
  ⟨t.f, w2c t.c⟩

noncomputable def truthRevision (t1 t2 : TV) : TV :=
  let w1 := c2w t1.c
  let w2 := c2w t2.c
  let w := w1 + w2
  let f := (w1 * t1.f + w2 * t2.f) / w
  let c := w2c w
  ⟨min 1 f, min 0.99 (max (max c t1.c) t2.c)⟩

noncomputable def truthExpectation (t : TV) : ℝ :=
  t.c * (t.f - 0.5) + 0.5

end Mettapedia.PLN.Comparisons.NARS.NARSMettaTruthFunctions
