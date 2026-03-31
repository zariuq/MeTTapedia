import Mettapedia.Computability.PNP.VisiblePostSwitchSurface
import Mettapedia.Computability.PNP.SameRouteInterface

/-!
# P vs NP background theory: the exact switched-family choke point

This file does not prove the manuscript's hoped-for compression theorem.
Instead it isolates the exact theorem target.

Given the manuscript's exact visible post-switch input `u = (z, a, b)`, an
indexed switched family is a family of Boolean predictors on that exact input.
The optimistic route now has one clear burden:

* either show that this exact family is realized by a small bit-encoded class;
* or show that it factors through a reduced exact view, such as `((z, a), b)` or
  `(z, a)`, and that the reduced family is bit-encoded there.

Once such a bit-budget theorem is supplied, the existing same-route ERM
backbone applies immediately.
-/

namespace Mettapedia.Computability.PNP

open scoped ENNReal

universe u v

/-- An indexed Boolean predictor family on one visible input type. -/
structure IndexedPredictorFamily (Index : Type u) (Input : Type v) where
  predict : Index → Input → Bool

namespace IndexedPredictorFamily

variable {Index : Type u} {Input : Type v}

/-- The family obtained by precomposing a predictor family with one visible-data map. -/
def pullback {View : Type*}
    (H : IndexedPredictorFamily Index View) (view : Input → View) :
    IndexedPredictorFamily Index Input where
  predict i x := H.predict i (view x)

/-- `G` factors through `view` via `H`. -/
def FactorsThrough {View : Type*}
    (G : IndexedPredictorFamily Index Input)
    (view : Input → View)
    (H : IndexedPredictorFamily Index View) : Prop :=
  ∀ i x, G.predict i x = H.predict i (view x)

/-- A bit-encoded classifier family pulled back along one visible-data map. -/
def pullbackBitFamily {View : Type*} {s : ℕ}
    (view : Input → View)
    (F : BitEncodedClassifierFamily View s) :
    BitEncodedClassifierFamily Input s where
  decode c x := F.decode c (view x)

/-- Every index in `G` is realized by some code in the bit family `F`. -/
def RealizedByBitFamily {s : ℕ}
    (G : IndexedPredictorFamily Index Input)
    (F : BitEncodedClassifierFamily Input s) : Prop :=
  ∀ i, ∃ c, F.decode c = G.predict i

/-- The exact small-class target: `G` is realized by an `s`-bit encoded family. -/
def HasBitBudget (G : IndexedPredictorFamily Index Input) (s : ℕ) : Prop :=
  ∃ F : BitEncodedClassifierFamily Input s, G.RealizedByBitFamily F

theorem hasBitBudget_of_factorsThrough
    {View : Type*} {s : ℕ}
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View}
    (hfactor : G.FactorsThrough view H)
    (hsmall : H.HasBitBudget s) :
    G.HasBitBudget s := by
  rcases hsmall with ⟨F, hF⟩
  refine ⟨pullbackBitFamily view F, ?_⟩
  intro i
  rcases hF i with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  funext x
  change F.decode c (view x) = G.predict i x
  exact (congrFun hc (view x)).trans (hfactor i x).symm

section TruthTable

variable {View : Type*}

/-- Truth-table decoding on an arbitrary finite visible summary type. -/
noncomputable def fintypeTruthTableDecode [Fintype View] :
    BitCode (Fintype.card View) → View → Bool :=
  fun code x => code (Fintype.equivFin View x)

/-- Truth-table encoding on an arbitrary finite visible summary type. -/
noncomputable def fintypeTruthTableEncode [Fintype View] :
    (View → Bool) → BitCode (Fintype.card View) :=
  fun f i => f ((Fintype.equivFin View).symm i)

lemma fintypeTruthTableDecode_encode [Fintype View] (f : View → Bool) :
    fintypeTruthTableDecode (View := View)
      (fintypeTruthTableEncode (View := View) f) = f := by
  funext x
  simp [fintypeTruthTableDecode, fintypeTruthTableEncode]

lemma fintypeTruthTableEncode_decode [Fintype View]
    (code : BitCode (Fintype.card View)) :
    fintypeTruthTableEncode (View := View)
      (fintypeTruthTableDecode (View := View) code) = code := by
  funext i
  simp [fintypeTruthTableDecode, fintypeTruthTableEncode]

/-- The full Boolean function space on a finite summary type is realized by its
truth-table family. -/
noncomputable def fintypeTruthTableBitFamily [Fintype View] :
    BitEncodedClassifierFamily View (Fintype.card View) where
  decode := fintypeTruthTableDecode (View := View)

/-- Any indexed family over a finite summary surface admits the explicit
truth-table bit budget `|View|`. -/
theorem hasBitBudget_card_of_fintype [Fintype View]
    (H : IndexedPredictorFamily Index View) :
    H.HasBitBudget (Fintype.card View) := by
  refine ⟨fintypeTruthTableBitFamily (View := View), ?_⟩
  intro i
  refine ⟨fintypeTruthTableEncode (View := View) (H.predict i), ?_⟩
  exact fintypeTruthTableDecode_encode (View := View) (H.predict i)

/-- Dependence on a finite visible summary surface yields the corresponding
explicit bit budget on the original input type. -/
theorem hasBitBudget_card_of_factorsThrough_fintype
    [Fintype View]
    {G : IndexedPredictorFamily Index Input}
    {H : IndexedPredictorFamily Index View}
    {view : Input → View}
    (hfactor : G.FactorsThrough view H) :
    G.HasBitBudget (Fintype.card View) := by
  exact hasBitBudget_of_factorsThrough hfactor (hasBitBudget_card_of_fintype H)

end TruthTable

end IndexedPredictorFamily

section ExactPostSwitch

variable {Z : Type*} {k s : ℕ} {Index : Type*}

/-- The manuscript's exact switched family on the full visible post-switch input. -/
abbrev ExactVisibleSwitchedFamily (Z : Type*) (k : ℕ) (Index : Type*) :=
  IndexedPredictorFamily Index (ExactVisiblePostSwitchSurface Z k)

/-- The same family after factoring through the invariant exact view `(z, a)`. -/
abbrev InvariantVisibleSwitchedFamily (Z : Type*) (k : ℕ) (Index : Type*) :=
  IndexedPredictorFamily Index (InvariantPostSwitchSurface Z k)

/-- The same family after factoring through the exact fork view `((z, a), b)`. -/
abbrev ForkVisibleSwitchedFamily (Z : Type*) (k : ℕ) (Index : Type*) :=
  IndexedPredictorFamily Index (ForkPostSwitchSurface Z k)

/-- The strongest same-route compression claim on the exact manuscript surface. -/
abbrev ExactVisibleCompressionTarget
    (G : ExactVisibleSwitchedFamily Z k Index) (s : ℕ) : Prop :=
  G.HasBitBudget s

/-- The charitable invariant-view repair target. -/
def InvariantCompressionTarget
    (G : ExactVisibleSwitchedFamily Z k Index) (s : ℕ) : Prop :=
  ∃ H : InvariantVisibleSwitchedFamily Z k Index,
    G.FactorsThrough invariantVisibleData H ∧ H.HasBitBudget s

/-- The charitable fork-view repair target. -/
def ForkCompressionTarget
    (G : ExactVisibleSwitchedFamily Z k Index) (s : ℕ) : Prop :=
  ∃ H : ForkVisibleSwitchedFamily Z k Index,
    G.FactorsThrough forkVisibleData H ∧ H.HasBitBudget s

theorem exactVisibleCompressionTarget_of_invariantCompressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : InvariantCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rcases h with ⟨H, hfactor, hsmall⟩
  exact IndexedPredictorFamily.hasBitBudget_of_factorsThrough hfactor hsmall

theorem exactVisibleCompressionTarget_of_forkCompressionTarget
    {G : ExactVisibleSwitchedFamily Z k Index}
    (h : ForkCompressionTarget (Z := Z) (k := k) (Index := Index) G s) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G s := by
  rcases h with ⟨H, hfactor, hsmall⟩
  exact IndexedPredictorFamily.hasBitBudget_of_factorsThrough hfactor hsmall

/-- The invariant visible summary has cardinality `|Z| * 2^k`. -/
theorem card_invariantVisiblePostSwitchSurface [Fintype Z] :
    Fintype.card (InvariantPostSwitchSurface Z k) =
      Fintype.card Z * 2 ^ k := by
  simp [InvariantPostSwitchSurface, BitVec]

/-- The fork-visible summary has cardinality `|Z| * 2^k * 2^k`. -/
theorem card_forkVisiblePostSwitchSurface [Fintype Z] :
    Fintype.card (ForkPostSwitchSurface Z k) =
      Fintype.card Z * 2 ^ k * 2 ^ k := by
  simp [ForkPostSwitchSurface, InvariantPostSwitchSurface, BitVec]

/-- If the exact switched family truly factors through the invariant view
`(z, a)`, then it already has the explicit truth-table bit budget for that
summary surface. -/
theorem invariantCompressionTarget_of_factorsThrough_fintype
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : InvariantVisibleSwitchedFamily Z k Index}
    (hfactor : G.FactorsThrough invariantVisibleData H) :
    InvariantCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (Fintype.card (InvariantPostSwitchSurface Z k)) := by
  refine ⟨H, hfactor, ?_⟩
  exact IndexedPredictorFamily.hasBitBudget_card_of_fintype H

/-- The corresponding exact-surface compression target follows immediately. -/
theorem exactVisibleCompressionTarget_of_factorsThrough_invariant_fintype
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : InvariantVisibleSwitchedFamily Z k Index}
    (hfactor : G.FactorsThrough invariantVisibleData H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (Fintype.card (InvariantPostSwitchSurface Z k)) := by
  exact
    exactVisibleCompressionTarget_of_invariantCompressionTarget
      (invariantCompressionTarget_of_factorsThrough_fintype (Z := Z) (k := k)
        (Index := Index) hfactor)

/-- If the exact switched family factors through the fork view `((z, a), b)`,
then it inherits the explicit truth-table bit budget for that summary surface. -/
theorem forkCompressionTarget_of_factorsThrough_fintype
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ForkVisibleSwitchedFamily Z k Index}
    (hfactor : G.FactorsThrough forkVisibleData H) :
    ForkCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (Fintype.card (ForkPostSwitchSurface Z k)) := by
  refine ⟨H, hfactor, ?_⟩
  exact IndexedPredictorFamily.hasBitBudget_card_of_fintype H

/-- The corresponding exact-surface compression target follows immediately. -/
theorem exactVisibleCompressionTarget_of_factorsThrough_fork_fintype
    [Fintype Z]
    {G : ExactVisibleSwitchedFamily Z k Index}
    {H : ForkVisibleSwitchedFamily Z k Index}
    (hfactor : G.FactorsThrough forkVisibleData H) :
    ExactVisibleCompressionTarget (Z := Z) (k := k) (Index := Index) G
      (Fintype.card (ForkPostSwitchSurface Z k)) := by
  exact
    exactVisibleCompressionTarget_of_forkCompressionTarget
      (forkCompressionTarget_of_factorsThrough_fintype (Z := Z) (k := k)
        (Index := Index) hfactor)

/-- The exact post-switch surface is finite whenever the latent local datum `z` is finite. -/
noncomputable def exactVisibleFintype [Fintype Z] :
    Fintype (ExactVisiblePostSwitchSurface Z k) :=
  Fintype.ofEquiv (ForkPostSwitchSurface Z k) (forkVisibleEquiv (Z := Z) (k := k)).symm

noncomputable instance instFintypeExactVisiblePostSwitchSurface [Fintype Z] :
    Fintype (ExactVisiblePostSwitchSurface Z k) :=
  exactVisibleFintype (Z := Z) (k := k)

/-- Once a bit-budget theorem on the exact manuscript surface is supplied, the
same-route ERM recovery theorem applies there verbatim on any finite exact
surface. -/
theorem exactVisible_bitFamily_exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
    [Fintype (ExactVisiblePostSwitchSurface Z k)]
    (F : BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) s)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    {q : ℝ≥0∞}
    (hq : ∀ c : F.toEncodedFamily.BadCodes target, agreementMass μ target (F.decode c.1) ≤ q) :
    1 - (2 ^ s : ℝ≥0∞) * q ^ m ≤
      F.bitExactRecoverySampleMass μ target m := by
  exact
    BitEncodedClassifierFamily.exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
      (F := F) (μ := μ) (target := target) (m := m) htarget hq

/-- The finite exact-surface hypothesis follows from finiteness of the latent
local datum `z`. -/
theorem exactVisible_bitFamily_exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le_of_fintype
    [Fintype Z]
    (F : BitEncodedClassifierFamily (ExactVisiblePostSwitchSurface Z k) s)
    (μ : PMF (ExactVisiblePostSwitchSurface Z k))
    (target : ExactVisiblePostSwitchSurface Z k → Bool) (m : ℕ)
    (htarget : ∃ c : BitCode s, F.decode c = target)
    {q : ℝ≥0∞}
    (hq : ∀ c : F.toEncodedFamily.BadCodes target, agreementMass μ target (F.decode c.1) ≤ q) :
    1 - (2 ^ s : ℝ≥0∞) * q ^ m ≤
      F.bitExactRecoverySampleMass μ target m := by
  exact
    exactVisible_bitFamily_exactRecoverySampleMass_ge_one_sub_bitBudget_mul_pow_of_agreementMass_le
      (F := F) (μ := μ) (target := target) (m := m) htarget hq

end ExactPostSwitch

end Mettapedia.Computability.PNP
