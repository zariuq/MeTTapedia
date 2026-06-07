import Mathlib.Tactic
import Mettapedia.Logic.PLNProvenanceInference

/-!
# Temporal Chaining Example

This file works through the small `q/r/m` temporal sequence example that came
from the Patrick/Max discussion.

The example compares three readings of the same evidence:

1. NARS-style scalar damping.
2. Naive scalar PLN chaining and revision.
3. WM-PLN provenance-aware guidance.

The WM-PLN lesson is not merely "refuse to answer".  It is:

* direct `q -> m` evidence says the simple one-step hypothesis is bad here;
* `q -> r` and `r -> m` generate a derived `q -> m` hypothesis, but not a fresh
  observation packet;
* the more specific condition `q then r -> m` is strongly supported;
* revising the derived chain estimate with the direct estimate is legitimate
  only when the two packets have disjoint provenance, for example on an
  independent validation stream.

The accompanying PeTTa runtime probes are:

* `/home/zar/claude/hyperon/PeTTa/examples/nars_temporal_sequence_probe.metta`
* `/home/zar/claude/hyperon/PeTTa/examples/pln_temporal_sequence_probe.metta`

Those probes check the floating-point runtime formulas.  This Lean file records
the exact rational values and the WM/provenance condition that the scalar probes
cannot express.
-/

namespace Mettapedia.Logic.TemporalChainingExample

/-! ## Exact rational truth-value surface -/

/-- A rational truth value used for exact example arithmetic. -/
structure QTV where
  s : ℚ
  c : ℚ
deriving DecidableEq, Repr

namespace QTV

@[ext] theorem ext {x y : QTV} (hs : x.s = y.s) (hc : x.c = y.c) : x = y := by
  cases x
  cases y
  simp_all

end QTV

/-- Direct counted evidence: strength `pos / total`, confidence `total / (total + 1)`. -/
def direct (pos total : ℚ) : QTV :=
  ⟨pos / total, total / (total + 1)⟩

/-- Confidence-to-weight transform used by PLN/NARS-style revision. -/
def c2w (c : ℚ) : ℚ :=
  c / (1 - c)

/-- Weight-to-confidence transform used by PLN/NARS-style revision. -/
def w2c (w : ℚ) : ℚ :=
  w / (w + 1)

/-- Unclamped rational revision.  The concrete example values are already in range. -/
def revision (x y : QTV) : QTV :=
  let wx := c2w x.c
  let wy := c2w y.c
  let w := wx + wy
  ⟨(wx * x.s + wy * y.s) / w, w2c w⟩

/-- Rational mirror of the PeTTa NARS deduction rule. -/
def narsDeduction (x y : QTV) : QTV :=
  ⟨x.s * y.s, (x.s * y.s) * (x.c * y.c)⟩

/-- Rational scalar PLN deduction strength for `A -> B`, `B -> C`, so `A -> C`. -/
def scalarPLNDeductionStrength (_sA sB sC sAB sBC : ℚ) : ℚ :=
  if sB = 1 then
    sC
  else
    sAB * sBC + (1 - sAB) * (sC - sB * sBC) / (1 - sB)

/-- Scalar PLN deduction with confidence as the weakest input confidence. -/
def scalarPLNDeduction (a b c ab bc : QTV) : QTV :=
  ⟨scalarPLNDeductionStrength a.s b.s c.s ab.s bc.s,
    min a.c (min b.c (min c.c (min ab.c bc.c)))⟩

/-! ## The q/r/m stream as counted evidence -/

/-- `q -> r` holds in 7 of 9 observed `q` cases. -/
def qToR : QTV := direct 7 9

/-- `r -> m` holds in 5 of 9 observed `r` cases. -/
def rToM : QTV := direct 5 9

/-- The composite condition `q` then `r` predicts `m` in 5 of 7 observed cases. -/
def qrToM : QTV := direct 5 7

/-- Direct one-step `q -> m` evidence is negative in the observed stream: 0 of 9. -/
def qToMDirect : QTV := direct 0 9

/-- Two-step mediated `q -> r -> m` evidence occurs in 5 of 9 observed `q` cases. -/
def qToMViaRAtLag2 : QTV := direct 5 9

/-- Base rate for `q` in the 45-symbol stream. -/
def qBase : QTV := direct 9 45

/-- Base rate for `r` in the 45-symbol stream. -/
def rBase : QTV := direct 9 45

/-- Base rate for `m` in the 45-symbol stream. -/
def mBase : QTV := direct 6 45

theorem qToR_eq : qToR = ⟨7 / 9, 9 / 10⟩ := by
  norm_num [qToR, direct]

theorem rToM_eq : rToM = ⟨5 / 9, 9 / 10⟩ := by
  norm_num [rToM, direct]

theorem qrToM_eq : qrToM = ⟨5 / 7, 7 / 8⟩ := by
  norm_num [qrToM, direct]

theorem qToMDirect_eq : qToMDirect = ⟨0, 9 / 10⟩ := by
  norm_num [qToMDirect, direct]

theorem qToMViaRAtLag2_eq : qToMViaRAtLag2 = ⟨5 / 9, 9 / 10⟩ := by
  norm_num [qToMViaRAtLag2, direct]

theorem qBase_eq : qBase = ⟨1 / 5, 45 / 46⟩ := by
  norm_num [qBase, direct]

theorem rBase_eq : rBase = ⟨1 / 5, 45 / 46⟩ := by
  norm_num [rBase, direct]

theorem mBase_eq : mBase = ⟨2 / 15, 45 / 46⟩ := by
  norm_num [mBase, direct]

/-! ## Scalar calculations, recorded exactly -/

/-- NARS-damped chain estimate for `q -> m` via `q -> r -> m`. -/
def narsChainQM : QTV :=
  narsDeduction qToR rToM

/-- NARS-style revision of the chain estimate with direct negative `q -> m` evidence. -/
def narsRevisedQM : QTV :=
  revision narsChainQM qToMDirect

/-- Full scalar PLN chain estimate for `q -> m` via `q -> r -> m`. -/
def scalarPLNChainQM : QTV :=
  scalarPLNDeduction qBase rBase mBase qToR rToM

/-- Naive scalar PLN revision of the chain estimate with direct negative evidence. -/
def scalarPLNRevisedQM : QTV :=
  revision scalarPLNChainQM qToMDirect

theorem narsChainQM_eq :
    narsChainQM = ⟨35 / 81, 7 / 20⟩ := by
  norm_num [narsChainQM, narsDeduction, qToR, rToM, direct]

theorem narsRevisedQM_eq :
    narsRevisedQM = ⟨245 / 10044, 124 / 137⟩ := by
  norm_num [narsRevisedQM, revision, c2w, w2c, narsChainQM, narsDeduction,
    qToR, rToM, qToMDirect, direct]

theorem scalarPLNChainQM_eq :
    scalarPLNChainQM = ⟨71 / 162, 9 / 10⟩ := by
  norm_num [scalarPLNChainQM, scalarPLNDeduction, scalarPLNDeductionStrength,
    qBase, rBase, mBase, qToR, rToM, direct]

theorem scalarPLNRevisedQM_eq :
    scalarPLNRevisedQM = ⟨71 / 324, 18 / 19⟩ := by
  norm_num [scalarPLNRevisedQM, revision, c2w, w2c, scalarPLNChainQM,
    scalarPLNDeduction, scalarPLNDeductionStrength, qBase, rBase, mBase,
    qToR, rToM, qToMDirect, direct]

/-- WM-PLN guidance: prefer the supported specific condition over the weak
unconditional `q -> m` hypothesis. -/
theorem guidance_specific_qrToM_stronger_than_scalarPLNRevisedQM :
    scalarPLNRevisedQM.s < qrToM.s := by
  norm_num [scalarPLNRevisedQM_eq, qrToM_eq]

/-- The scalar PLN chain keeps more `q -> m` strength than the NARS-damped calculation. -/
theorem scalarPLNRevisedQM_stronger_than_narsRevisedQM :
    narsRevisedQM.s < scalarPLNRevisedQM.s := by
  norm_num [narsRevisedQM_eq, scalarPLNRevisedQM_eq]

/-- WM-PLN guidance: the direct one-step `q -> m` hypothesis is negative,
but the mediated two-step pattern and the more specific `q then r -> m`
condition are positive. -/
theorem guidance_direct_qToM_negative_but_mediated_patterns_positive :
    qToMDirect.s = 0 ∧ qToMViaRAtLag2.s = 5 / 9 ∧ qrToM.s = 5 / 7 := by
  constructor
  · norm_num [qToMDirect_eq]
  · constructor
    · norm_num [qToMViaRAtLag2_eq]
    · norm_num [qrToM_eq]

/-! ## Provenance gate: no additive revision without fresh support -/

/-- A truth value paired with a finite provenance stamp. -/
structure StampedTV (Stamp : Type) where
  tv : QTV
  stamp : Finset Stamp

namespace StampedTV

variable {Stamp : Type} [DecidableEq Stamp]

/-- Revision is fresh exactly when the two provenance stamps are disjoint. -/
def FreshForRevision (x y : StampedTV Stamp) : Prop :=
  Disjoint x.stamp y.stamp

instance instDecidableFreshForRevision
    (x y : StampedTV Stamp) :
    Decidable (FreshForRevision x y) := by
  unfold FreshForRevision
  infer_instance

/-- Revision carries the revised TV and union provenance. -/
def revise (x y : StampedTV Stamp) : StampedTV Stamp where
  tv := revision x.tv y.tv
  stamp := x.stamp ∪ y.stamp

/-- Guarded revision refuses to add evidence when stamps overlap. -/
def guardedRevision (x y : StampedTV Stamp) : Option (StampedTV Stamp) :=
  if FreshForRevision x y then
    some (revise x y)
  else
    none

@[simp] theorem revise_tv (x y : StampedTV Stamp) :
    (revise x y).tv = revision x.tv y.tv := rfl

@[simp] theorem revise_stamp (x y : StampedTV Stamp) :
    (revise x y).stamp = x.stamp ∪ y.stamp := rfl

@[simp] theorem guardedRevision_eq_some_of_fresh
    (x y : StampedTV Stamp) (h : FreshForRevision x y) :
    guardedRevision x y = some (revise x y) := by
  simp [guardedRevision, h]

@[simp] theorem guardedRevision_eq_none_of_not_fresh
    (x y : StampedTV Stamp) (h : ¬ FreshForRevision x y) :
    guardedRevision x y = none := by
  simp [guardedRevision, h]

end StampedTV

/-! ### Bridge to the full scoped tracked world-model provenance layer -/

open Mettapedia.Logic.LP
open Mettapedia.Logic.PLNProvenanceInference

section ScopedTrackedWhichStateBridge

variable {σ : LPSignature} {n m : ℕ}

/-- Full-WM version of the freshness gate at one query. -/
def scopedFreshForRevisionAt
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) : Prop :=
  ProvenanceDisjointAt W₁ W₂ q

instance instDecidableScopedFreshForRevisionAt
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    Decidable (scopedFreshForRevisionAt W₁ W₂ q) := by
  unfold scopedFreshForRevisionAt ProvenanceDisjointAt
  infer_instance

/-- Guarded scoped revision at a query: only add world-model states when the
scope supports are disjoint for that query. -/
noncomputable def guardedScopedRevisionAt
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ) :
    Option (ScopedTrackedWhichState σ n m) :=
  if scopedFreshForRevisionAt W₁ W₂ q then
    some (W₁ + W₂)
  else
    none

theorem not_scopedFreshForRevisionAt_of_shared_scope
    {W₁ W₂ : ScopedTrackedWhichState σ n m} {q : GroundAtom σ} {s : Fin m}
    (h₁ : s ∈ scopedTrackedScopeSupport W₁ q)
    (h₂ : s ∈ scopedTrackedScopeSupport W₂ q) :
    ¬ scopedFreshForRevisionAt W₁ W₂ q := by
  intro h
  exact (Finset.disjoint_left.mp h h₁) h₂

theorem guardedScopedRevisionAt_eq_none_of_not_fresh
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ)
    (h : ¬ scopedFreshForRevisionAt W₁ W₂ q) :
    guardedScopedRevisionAt W₁ W₂ q = none := by
  simp [guardedScopedRevisionAt, h]

theorem guardedScopedRevisionAt_eq_some_of_fresh
    (W₁ W₂ : ScopedTrackedWhichState σ n m) (q : GroundAtom σ)
    (h : scopedFreshForRevisionAt W₁ W₂ q) :
    guardedScopedRevisionAt W₁ W₂ q = some (W₁ + W₂) := by
  simp [guardedScopedRevisionAt, h]

/-- The full scoped WM gate blocks revision as soon as both packets use the
same scope at the queried atom. -/
theorem guardedScopedRevisionAt_blocks_shared_scope
    {W₁ W₂ : ScopedTrackedWhichState σ n m} {q : GroundAtom σ} {s : Fin m}
    (h₁ : s ∈ scopedTrackedScopeSupport W₁ q)
    (h₂ : s ∈ scopedTrackedScopeSupport W₂ q) :
    guardedScopedRevisionAt W₁ W₂ q = none := by
  exact guardedScopedRevisionAt_eq_none_of_not_fresh W₁ W₂ q
    (not_scopedFreshForRevisionAt_of_shared_scope h₁ h₂)

/-- If two states are supported in disjoint scope sets, then the full scoped WM
gate permits revision at every query. -/
theorem scopedFreshForRevisionAt_of_disjoint_supported_scopes
    {S₁ S₂ : Finset (Fin m)}
    {W₁ W₂ : ScopedTrackedWhichState σ n m}
    (h₁ : SupportedInScope W₁ S₁)
    (h₂ : SupportedInScope W₂ S₂)
    (hdisj : Disjoint S₁ S₂)
    (q : GroundAtom σ) :
    scopedFreshForRevisionAt W₁ W₂ q :=
  provenanceDisjoint_of_disjointScopes h₁ h₂ hdisj q

end ScopedTrackedWhichStateBridge

/-! ### Concrete 45-position provenance stamps -/

abbrev EventIx := Fin 45

/-- Positions of `q` in the 45-symbol stream. -/
def qStamp : Finset EventIx :=
  {⟨2, by decide⟩, ⟨8, by decide⟩, ⟨13, by decide⟩,
   ⟨17, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩,
   ⟨31, by decide⟩, ⟨36, by decide⟩, ⟨41, by decide⟩}

/-- Positions of `r` in the 45-symbol stream. -/
def rStamp : Finset EventIx :=
  {⟨3, by decide⟩, ⟨9, by decide⟩, ⟨15, by decide⟩,
   ⟨18, by decide⟩, ⟨23, by decide⟩, ⟨27, by decide⟩,
   ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨42, by decide⟩}

/-- `q` positions where the next symbol is `r`. -/
def qToRPositiveStamp : Finset EventIx :=
  {⟨2, by decide⟩, ⟨8, by decide⟩, ⟨17, by decide⟩,
   ⟨26, by decide⟩, ⟨31, by decide⟩, ⟨36, by decide⟩,
   ⟨41, by decide⟩}

/-- `r` positions where the next symbol is `m`. -/
def rToMPositiveStamp : Finset EventIx :=
  {⟨3, by decide⟩, ⟨9, by decide⟩, ⟨27, by decide⟩,
   ⟨32, by decide⟩, ⟨42, by decide⟩}

/-- `q` positions where the next two symbols form `r m`. -/
def qrToMPositiveStamp : Finset EventIx :=
  {⟨2, by decide⟩, ⟨8, by decide⟩, ⟨26, by decide⟩,
   ⟨31, by decide⟩, ⟨41, by decide⟩}

/-- Direct `q -> m` has no positive one-step observations in this stream. -/
def qToMPositiveStamp : Finset EventIx :=
  ∅

theorem qStamp_card : qStamp.card = 9 := by
  decide

theorem rStamp_card : rStamp.card = 9 := by
  decide

theorem qToRPositiveStamp_card : qToRPositiveStamp.card = 7 := by
  decide

theorem rToMPositiveStamp_card : rToMPositiveStamp.card = 5 := by
  decide

theorem qrToMPositiveStamp_card : qrToMPositiveStamp.card = 5 := by
  decide

theorem qToMPositiveStamp_card : qToMPositiveStamp.card = 0 := by
  decide

theorem counted_supports_match_direct_evidence :
    qToRPositiveStamp.card = 7 ∧ qStamp.card = 9 ∧
    rToMPositiveStamp.card = 5 ∧ rStamp.card = 9 ∧
    qrToMPositiveStamp.card = 5 ∧ qToRPositiveStamp.card = 7 ∧
    qToMPositiveStamp.card = 0 ∧ qStamp.card = 9 := by
  decide

/-- The chain estimate depends on the observations used for `q -> r` and `r -> m`. -/
def chainQMStamp : Finset EventIx :=
  qStamp ∪ rStamp

/-- The direct estimate for `q -> m` depends on the observed `q` positions. -/
def directQMStamp : Finset EventIx :=
  qStamp

def eventChainPacket : StampedTV EventIx where
  tv := scalarPLNChainQM
  stamp := chainQMStamp

def eventDirectPacket : StampedTV EventIx where
  tv := qToMDirect
  stamp := directQMStamp

theorem event_chain_and_direct_not_fresh :
    ¬ StampedTV.FreshForRevision eventChainPacket eventDirectPacket := by
  intro h
  have hdisj : Disjoint chainQMStamp directQMStamp := by
    simpa [StampedTV.FreshForRevision, eventChainPacket, eventDirectPacket]
      using h
  have hChain : (⟨2, by decide⟩ : EventIx) ∈ chainQMStamp := by
    decide
  have hDirect : (⟨2, by decide⟩ : EventIx) ∈ directQMStamp := by
    decide
  exact (Finset.disjoint_left.mp hdisj hChain) hDirect

/-- Fine-grained event stamps also block the naive chain/direct revision. -/
theorem event_guardedRevision_blocks_naive_scalar_revision :
    StampedTV.guardedRevision eventChainPacket eventDirectPacket = none := by
  exact StampedTV.guardedRevision_eq_none_of_not_fresh
    eventChainPacket eventDirectPacket event_chain_and_direct_not_fresh

/-! ### Negative example: derived and direct estimates from the same stream -/

/-- A one-scope provenance universe: all packets came from the same event stream. -/
inductive SameStreamScope where
  | stream
deriving DecidableEq, Repr

def sameStreamStamp : Finset SameStreamScope :=
  {SameStreamScope.stream}

/-- The derived chain estimate is stamped with the event stream it was computed from. -/
def sameStreamChainPacket : StampedTV SameStreamScope where
  tv := scalarPLNChainQM
  stamp := sameStreamStamp

/-- The direct `q -> m` estimate is stamped with the same event stream. -/
def sameStreamDirectPacket : StampedTV SameStreamScope where
  tv := qToMDirect
  stamp := sameStreamStamp

theorem sameStream_chain_and_direct_not_fresh :
    ¬ StampedTV.FreshForRevision sameStreamChainPacket sameStreamDirectPacket := by
  intro h
  have hdisj : Disjoint sameStreamStamp sameStreamStamp := by
    simpa [StampedTV.FreshForRevision, sameStreamChainPacket, sameStreamDirectPacket]
      using h
  have hmem : SameStreamScope.stream ∈ sameStreamStamp := by
    simp [sameStreamStamp]
  exact (Finset.disjoint_left.mp hdisj hmem) hmem

/-- WM-PLN guidance: on one stream, treat the chain estimate as a derived
hypothesis, not as fresh evidence to revise with the direct estimate. -/
theorem sameStream_guardedRevision_blocks_naive_scalar_revision :
    StampedTV.guardedRevision sameStreamChainPacket sameStreamDirectPacket = none := by
  exact StampedTV.guardedRevision_eq_none_of_not_fresh
    sameStreamChainPacket sameStreamDirectPacket sameStream_chain_and_direct_not_fresh

/-! ### Positive example: independent validation may be revised -/

/-- Two-scope universe: original stream plus a genuinely separate validation source. -/
inductive ValidationScope where
  | original
  | validation
deriving DecidableEq, Repr

def originalStamp : Finset ValidationScope :=
  {ValidationScope.original}

def validationStamp : Finset ValidationScope :=
  {ValidationScope.validation}

def validationChainPacket : StampedTV ValidationScope where
  tv := scalarPLNChainQM
  stamp := originalStamp

def validationDirectPacket : StampedTV ValidationScope where
  tv := qToMDirect
  stamp := validationStamp

theorem validation_chain_and_direct_fresh :
    StampedTV.FreshForRevision validationChainPacket validationDirectPacket := by
  decide

/-- WM-PLN guidance: an independent validation stream would make the revision
legitimate, and its stamp is the union of both sources. -/
theorem validation_guardedRevision_allows_independent_revision :
    StampedTV.guardedRevision validationChainPacket validationDirectPacket =
      some (StampedTV.revise validationChainPacket validationDirectPacket) := by
  exact StampedTV.guardedRevision_eq_some_of_fresh
    validationChainPacket validationDirectPacket validation_chain_and_direct_fresh

theorem validation_revision_tv_eq_scalarPLNRevisedQM :
    (StampedTV.revise validationChainPacket validationDirectPacket).tv = scalarPLNRevisedQM := by
  rfl

theorem validation_revision_stamp_eq_union :
    (StampedTV.revise validationChainPacket validationDirectPacket).stamp =
      originalStamp ∪ validationStamp := by
  rfl

end Mettapedia.Logic.TemporalChainingExample
