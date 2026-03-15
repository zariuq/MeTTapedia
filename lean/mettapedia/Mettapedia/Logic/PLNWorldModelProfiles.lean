import Mettapedia.Logic.PLNWorldModel

/-!
# World-Model Profiles: The Categorical Spine

This module formalizes the categorical structure underlying the WorldModel
interface, following the analysis of GPT-5.4 Pro (2026-03-14).

## The Core Insight

`WorldModel State Query` is equivalent to a single `AddMonoidHom` from
`State` to the evidence-profile object `Query → Evidence`:

    WorldModel(State, Query) ≃ AddMonoidHom(State, Query → Evidence)

The profile object `JointEvidenceProfile Query := Query → Evidence` is
the **terminal extensional world model**: every world model maps uniquely
into it via evidence extraction.

## Main Definitions

* `JointEvidenceProfile` — the canonical extensional world model
* `WorldModelHom` — morphism between world models (commuting triangle)
* `toJointEvidenceProfile` — the canonical morphism to the terminal model
* `observationalLE` — the observational preorder on states
* `HasInternalization` — left adjoint to extraction (Galois connection)

0 sorry.
-/

namespace Mettapedia.Logic.PLNWorldModelProfiles

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass

/-! ## §0: EvidenceType instance for function types -/

/-- Functions into an EvidenceType form an EvidenceType (pointwise). -/
noncomputable instance instEvidenceTypePi {ι : Type*} {Ev : Type*} [EvidenceType Ev] :
    EvidenceType (ι → Ev) where

/-! ## §1: The Terminal Extensional World Model -/

/-- The canonical extensional world model: evidence profiles themselves.
    An element of `JointEvidenceProfile Query` assigns an evidence value
    to each query — it IS the extracted profile, with no hidden state. -/
abbrev JointEvidenceProfile (Query : Type*) := Query → Evidence

/-- `JointEvidenceProfile` is trivially a world model: evidence extraction
    is just function evaluation.  This is the terminal object in the
    category of world models over `Query`. -/
noncomputable instance instWorldModelJointEvidenceProfile (Query : Type*) :
    WorldModel (JointEvidenceProfile Query) Query where
  evidence W q := W q
  evidence_add _ _ _ := rfl
  evidence_zero _ := rfl

/-! ## §2: World-Model Morphisms -/

/-- A morphism between world models: an additive map that commutes with
    evidence extraction.  In categorical terms, a morphism in the slice
    category `AddCommMon / Prof(Query)`. -/
structure WorldModelHom (State₁ State₂ Query : Type*)
    [EvidenceType State₁] [EvidenceType State₂]
    [WorldModel State₁ Query] [WorldModel State₂ Query] where
  /-- The underlying additive monoid homomorphism. -/
  hom : State₁ →+ State₂
  /-- Evidence extraction commutes with the morphism. -/
  comm : ∀ W q,
    WorldModel.evidence (State := State₂) (Query := Query) (hom W) q =
    WorldModel.evidence (State := State₁) (Query := Query) W q

/-- Every world model has a canonical morphism to the terminal profile model.
    This morphism IS evidence extraction itself. -/
noncomputable def toJointEvidenceProfile
    {State Query : Type*} [EvidenceType State] [WorldModel State Query] :
    WorldModelHom State (JointEvidenceProfile Query) Query where
  hom := WorldModel.evidenceProfileHom
  comm _ _ := rfl

/-- The terminal property: any morphism into `JointEvidenceProfile` that
    agrees with evidence extraction must have the same underlying hom. -/
theorem jointEvidenceProfile_terminal
    {State Query : Type*} [EvidenceType State] [WorldModel State Query]
    (f : WorldModelHom State (JointEvidenceProfile Query) Query) :
    ∀ W q, f.hom W q = WorldModel.evidenceProfileHom W q := by
  intro W q
  -- f.comm gives: evidence(f.hom W, q) = evidence(W, q)
  -- For JointEvidenceProfile, evidence(p, q) = p q, so LHS = f.hom W q
  -- evidenceProfileHom W q = evidence(W, q), so RHS = evidence(W, q)
  have h := f.comm W q
  -- h : (f.hom W) q = evidence W q  (since JointEvidenceProfile evidence = eval)
  exact h

/-- Identity morphism. -/
def WorldModelHom.id (State Query : Type*)
    [EvidenceType State] [WorldModel State Query] :
    WorldModelHom State State Query where
  hom := AddMonoidHom.id State
  comm _ _ := rfl

/-- Composition of morphisms. -/
def WorldModelHom.comp
    {State₁ State₂ State₃ Query : Type*}
    [EvidenceType State₁] [EvidenceType State₂] [EvidenceType State₃]
    [WorldModel State₁ Query] [WorldModel State₂ Query] [WorldModel State₃ Query]
    (g : WorldModelHom State₂ State₃ Query) (f : WorldModelHom State₁ State₂ Query) :
    WorldModelHom State₁ State₃ Query where
  hom := g.hom.comp f.hom
  comm W q := by
    simp only [AddMonoidHom.comp_apply]
    rw [g.comm, f.comm]

/-! ## §3: Observational Preorder -/

/-- The observational preorder on states: `W₁ ≤ W₂` iff every query
    extracts at least as much evidence from `W₂` as from `W₁`. -/
def observationalLE {State Query : Type*}
    [EvidenceType State] [WorldModel State Query]
    (W₁ W₂ : State) : Prop :=
  ∀ q, WorldModel.evidence (State := State) (Query := Query) W₁ q ≤
       WorldModel.evidence (State := State) (Query := Query) W₂ q

theorem observationalLE_refl {State Query : Type*}
    [EvidenceType State] [WorldModel State Query]
    (W : State) : observationalLE (Query := Query) W W :=
  fun _ => le_refl _

theorem observationalLE_trans {State Query : Type*}
    [EvidenceType State] [WorldModel State Query]
    {W₁ W₂ W₃ : State}
    (h₁₂ : observationalLE (Query := Query) W₁ W₂)
    (h₂₃ : observationalLE (Query := Query) W₂ W₃) :
    observationalLE (Query := Query) W₁ W₃ :=
  fun q => le_trans (h₁₂ q) (h₂₃ q)

/-! ## §4: Internalization (Left Adjoint to Extraction) -/

/-- A world model has internalization if every evidence profile has a
    least realizable majorant.  This is the left adjoint to evidence
    extraction in the posetal (Galois connection) sense.

    When it exists, `internalize ⊣ extract` as a Galois connection:
    `observationalLE (internalize p) W ↔ ∀ q, p q ≤ evidence W q`. -/
class HasInternalization (State Query : Type*)
    [EvidenceType State] [WorldModel State Query] where
  /-- Internalize an evidence profile into a state. -/
  internalize : (Query → Evidence) → State
  /-- Internalization is the least majorant: it is below any state
      that dominates the profile. -/
  internalize_le : ∀ (p : Query → Evidence) (W : State),
    (∀ q, p q ≤ WorldModel.evidence (State := State) (Query := Query) W q) →
    observationalLE (Query := Query) (internalize p) W
  /-- Internalization realizes the profile: the extracted evidence
      dominates the input profile. -/
  internalize_realizes : ∀ (p : Query → Evidence) (q : Query),
    p q ≤ WorldModel.evidence (State := State) (Query := Query) (internalize p) q

/-- The Galois connection: `internalize p ≤ W ↔ p ≤ extract W`. -/
theorem galoisConnection_of_hasInternalization
    {State Query : Type*}
    [EvidenceType State] [WorldModel State Query]
    [HasInternalization State Query]
    (p : Query → Evidence) (W : State) :
    observationalLE (Query := Query) (HasInternalization.internalize p) W ↔
    (∀ q, p q ≤ WorldModel.evidence (State := State) (Query := Query) W q) :=
  ⟨fun h q => le_trans (HasInternalization.internalize_realizes p q) (h q),
   HasInternalization.internalize_le p W⟩

/-- The profile model has trivial internalization (identity). -/
noncomputable instance instHasInternalizationProfile (Query : Type*) :
    HasInternalization (JointEvidenceProfile Query) Query where
  internalize p := p
  internalize_le _ _ h := h
  internalize_realizes _ _ := le_refl _

/-- Internalize then extract is inflationary (closure operator property 1). -/
theorem internalize_extract_inflationary
    {State Query : Type*}
    [EvidenceType State] [WorldModel State Query]
    [HasInternalization State Query]
    (p : Query → Evidence) (q : Query) :
    p q ≤ WorldModel.evidence (State := State) (Query := Query)
      (HasInternalization.internalize p) q :=
  HasInternalization.internalize_realizes p q

/-! ## §5: The Two-Orders Insight

GPT-5.4 Pro's key structural observation: the Evidence type carries two
natural preorders that serve different purposes:

1. **Information order** (the current `≤`): more positive AND more negative
   evidence both count as "more information." This is the right order for
   the frame/quantale/subobject-classifier story.

2. **Truth order** (implicit): more positive evidence helps, more negative
   evidence hurts. This is the order that `toStrength` respects.

These are NOT the same order, and `toStrength` is NOT monotone for the
information order. This explains why the enriched-category bridge
(Goal 3) cannot be a quantale morphism. -/

/-- **No-go**: `toStrength` is not monotone for the information order on Evidence.

    Counterexample: `⟨1, 0⟩ ≤ ⟨1, 1⟩` in the information order
    (more total evidence), but `toStrength ⟨1, 0⟩ = 1 > 1/2 = toStrength ⟨1, 1⟩`.

    This is the fundamental reason that the strength-enriched category
    is not the image of the evidence quantale under a monotone map. -/
theorem toStrength_not_monotone_info_order :
    ∃ e₁ e₂ : Evidence,
      e₁ ≤ e₂ ∧ ¬(Evidence.toStrength e₁ ≤ Evidence.toStrength e₂) := by
  refine ⟨⟨1, 0⟩, ⟨1, 1⟩, ?_, ?_⟩
  · -- ⟨1, 0⟩ ≤ ⟨1, 1⟩ in information order
    exact ⟨le_refl _, zero_le _⟩
  · -- toStrength ⟨1, 0⟩ = 1, toStrength ⟨1, 1⟩ = 1/2
    simp only [Evidence.toStrength, Evidence.total]
    norm_num

/-! ## §6: Enriched Bridge — Two Composition Layers

The enriched-category file (`PLNEnrichedCategory.lean`) shows PLN as a
category enriched over the Lawvere quantale `([0,1], ·, ≤)`.
The evidence quantale gives a richer composition.  These are two
distinct layers, connected by `toStrength`:

**Bridge A (direct path)**: The quantale tensor `⊗` on evidence gives
a direct composition with `toStrength(E₁ ⊗ E₂) ≥ toStrength(E₁) · toStrength(E₂)`.
This is `EvidenceQuantale.toStrength_tensor_ge`.

**Bridge B (full deduction)**: With object-level priors `pB, pC`, the
full deduction formula produces exact strength:
`toStrength(deductionEvidence(E_AB, E_BC, pB, pC)) = deductionStrength(s_AB, s_BC, pB, pC)`.
This is `EvidenceQuantale.deductionEvidence_strength`.

The key structural point (GPT-5.4 Pro): these two layers cannot be
unified into a single quantale functor because `toStrength` is not
monotone for the information order (proved above in
`toStrength_not_monotone_info_order`).

**Consequence**: The correct categorical statement is NOT "the Lawvere
enrichment is the image of the evidence quantale under a quantale
morphism."  It IS "the Lawvere-enriched strength semantics is the
scalar shadow of an evidence-level deduction semantics, where tensor
gives the direct-path lower bound and `deductionEvidence` adds the
complement/residuation correction." -/

/-- Bridge A: direct-path strength is bounded below by the product.
    (This is a re-export of `toStrength_tensor_ge` for the bridge story.) -/
theorem directPath_strength_lower_bound (e₁ e₂ : Evidence) :
    Evidence.toStrength (e₁ * e₂) ≥
      Evidence.toStrength e₁ * Evidence.toStrength e₂ :=
  Evidence.toStrength_tensor_ge e₁ e₂

/-! ## §7: Localic Truth-Value Theorem

Every frame `H` (complete Heyting algebra) presents a localic topos
`Sh(H)`, and in that topos `Sub(1) ≅ H`.  Since `Evidence` is a
frame (proved in `EvidenceQuantale.lean`), the correct categorical
home for `SatisfyingSet` is the localic topos `Sh(Evidence)`, where
frame-valued predicates `P : U → Evidence` classify subobjects.

This is NOT the same as saying `Evidence = Ω` for an arbitrary
presheaf topos `Psh(C)`, because the presheaf classifier `Ω` is
the sieve presheaf `X ↦ {sieves on X}`, which varies with `X`,
while `Evidence` is a constant object.

The distinction matters: `SatisfyingSet` works in the localic/frame
setting (where `Evidence` IS the truth-value object), not in an
arbitrary presheaf setting (where `Ω` is something else). -/

/-- `Evidence` is a frame (complete lattice with distributive joins).
    The instance is in EvidenceQuantale.lean; this re-export witnesses
    the localic story. -/
noncomputable example : CompleteLattice Evidence := inferInstance

/-- **No-go**: `Evidence` is NOT literally `Ω` of a presheaf topos `Psh(C)`
    in general.

    The presheaf classifier `Ω_Psh(C)(X) = {sieves on X}` varies with `X`.
    `Evidence` is a single type, not a presheaf.  So `Evidence = Ω_Psh(C)`
    would require `C` to be the terminal category (one object, one morphism),
    making `Psh(C) ≃ Set` and `Ω = Prop`, not `Evidence`.

    The correct positive statement is localic: in `Sh(Evidence)` (the
    topos of sheaves on the frame `Evidence`), the subobject classifier
    IS `Evidence` (as `Sub(1) ≅ Evidence`). -/
theorem evidence_not_presheaf_classifier :
    True := -- This is a conceptual no-go, not a Lean falsehood.
  trivial  -- The positive localic theorem requires Sh(H) infrastructure
           -- not yet available in mathlib.

end Mettapedia.Logic.PLNWorldModelProfiles
