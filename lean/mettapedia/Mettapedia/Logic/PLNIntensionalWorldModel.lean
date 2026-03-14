import Mettapedia.Logic.PLNWorldModel

/-!
# PLN Intensional World-Model Query Layer

Typed WM query family for Chapter-12-style inheritance channels:

- extensional inheritance
- intensional inheritance via ASSOC
- intensional inheritance via PAT
- mixed inheritance

This module introduces query-level infrastructure and typed rule constructors.
Specific ASSOC/PAT probabilistic semantics are represented as explicit side conditions.
-/

namespace Mettapedia.Logic.PLNIntensionalWorldModel

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel

/-- Sort index for inheritance channels. -/
inductive InheritanceSort where
  | extensional
  | intensionalAssoc
  | intensionalPAT
  | mixed
  deriving DecidableEq, Repr

/-- Sort-indexed query wrapper for inheritance channels. -/
inductive InheritanceQueryFamily (Query : Type) : InheritanceSort → Type where
  | ext : Query → InheritanceQueryFamily Query .extensional
  | assoc : Query → InheritanceQueryFamily Query .intensionalAssoc
  | pat : Query → InheritanceQueryFamily Query .intensionalPAT
  | mix : Query → InheritanceQueryFamily Query .mixed

namespace InheritanceQueryFamily

/-- Erase the sort tag. -/
def erase {Query : Type} : {s : InheritanceSort} → InheritanceQueryFamily Query s → Query
  | _, .ext q => q
  | _, .assoc q => q
  | _, .pat q => q
  | _, .mix q => q

/-- Inject an untyped query at a specific inheritance sort. -/
def ofSort {Query : Type} (s : InheritanceSort) (q : Query) : InheritanceQueryFamily Query s :=
  match s with
  | .extensional => .ext q
  | .intensionalAssoc => .assoc q
  | .intensionalPAT => .pat q
  | .mixed => .mix q

@[simp] theorem erase_ofSort {Query : Type} (s : InheritanceSort) (q : Query) :
    erase (ofSort (Query := Query) s q) = q := by
  cases s <;> rfl

end InheritanceQueryFamily

/-- Canonical typed WM adapter over inheritance channels from an untyped WM. -/
def worldModelSigmaInheritanceFromUntyped
    (State Query : Type)
    [EvidenceType State] [WorldModel State Query] :
    WorldModelSigma State InheritanceSort (InheritanceQueryFamily Query) where
  evidence W q :=
    WorldModel.evidence (State := State) (Query := Query) W (InheritanceQueryFamily.erase q.2)
  evidence_add W₁ W₂ q :=
    WorldModel.evidence_add (State := State) (Query := Query) W₁ W₂
      (InheritanceQueryFamily.erase q.2)

/-- Global typed WMΣ instance for inheritance channels, induced from an untyped WM. -/
instance instWorldModelSigmaInheritanceFromUntyped
    (State Query : Type)
    [EvidenceType State] [WorldModel State Query] :
    WorldModelSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  worldModelSigmaInheritanceFromUntyped (State := State) (Query := Query)

/-- Builder for channel-specific underlying queries. -/
structure InheritanceQueryBuilder (Atom Query : Type) where
  extensional : Atom → Atom → Query
  intensionalAssoc : Atom → Atom → Query
  intensionalPAT : Atom → Atom → Query
  mixed : Atom → Atom → Query

namespace InheritanceQueryBuilder

variable {Atom Query : Type}

/-- Extensional typed query for a pair of atoms. -/
def extQ (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    Sigma (InheritanceQueryFamily Query) :=
  ⟨.extensional, .ext (enc.extensional a b)⟩

/-- Intensional-ASSOC typed query for a pair of atoms. -/
def assocQ (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    Sigma (InheritanceQueryFamily Query) :=
  ⟨.intensionalAssoc, .assoc (enc.intensionalAssoc a b)⟩

/-- Intensional-PAT typed query for a pair of atoms. -/
def patQ (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    Sigma (InheritanceQueryFamily Query) :=
  ⟨.intensionalPAT, .pat (enc.intensionalPAT a b)⟩

/-- Mixed typed query for a pair of atoms. -/
def mixedQ (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    Sigma (InheritanceQueryFamily Query) :=
  ⟨.mixed, .mix (enc.mixed a b)⟩

@[simp] theorem extQ_erase (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    InheritanceQueryFamily.erase (extQ enc a b).2 = enc.extensional a b := rfl

@[simp] theorem assocQ_erase (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    InheritanceQueryFamily.erase (assocQ enc a b).2 = enc.intensionalAssoc a b := rfl

@[simp] theorem patQ_erase (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    InheritanceQueryFamily.erase (patQ enc a b).2 = enc.intensionalPAT a b := rfl

@[simp] theorem mixedQ_erase (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    InheritanceQueryFamily.erase (mixedQ enc a b).2 = enc.mixed a b := rfl

end InheritanceQueryBuilder

namespace InheritanceQueryBuilder

variable {State Atom Query : Type}
variable [EvidenceType State]
variable [WorldModelSigma State InheritanceSort (InheritanceQueryFamily Query)]

/-- Evidence projection for extensional inheritance queries. -/
def extensionalEvidence
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) : Evidence :=
  WorldModelSigma.evidence (State := State) (Srt := InheritanceSort)
    (Query := InheritanceQueryFamily Query) W (extQ enc a b)

/-- Evidence projection for intensional-ASSOC inheritance queries. -/
def intensionalAssocEvidence
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) : Evidence :=
  WorldModelSigma.evidence (State := State) (Srt := InheritanceSort)
    (Query := InheritanceQueryFamily Query) W (assocQ enc a b)

/-- Evidence projection for intensional-PAT inheritance queries. -/
def intensionalPATEvidence
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) : Evidence :=
  WorldModelSigma.evidence (State := State) (Srt := InheritanceSort)
    (Query := InheritanceQueryFamily Query) W (patQ enc a b)

/-- Evidence projection for mixed inheritance queries. -/
def mixedEvidence
    (W : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) : Evidence :=
  WorldModelSigma.evidence (State := State) (Srt := InheritanceSort)
    (Query := InheritanceQueryFamily Query) W (mixedQ enc a b)

@[simp] theorem extensionalEvidence_add
    (W₁ W₂ : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    extensionalEvidence W₁ enc a b + extensionalEvidence W₂ enc a b =
      extensionalEvidence (W₁ + W₂) enc a b := by
  symm
  simpa [extensionalEvidence] using
    (WorldModelSigma.evidence_add (State := State) (Srt := InheritanceSort)
      (Query := InheritanceQueryFamily Query) W₁ W₂ (extQ enc a b))

@[simp] theorem intensionalAssocEvidence_add
    (W₁ W₂ : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    intensionalAssocEvidence W₁ enc a b + intensionalAssocEvidence W₂ enc a b =
      intensionalAssocEvidence (W₁ + W₂) enc a b := by
  symm
  simpa [intensionalAssocEvidence] using
    (WorldModelSigma.evidence_add (State := State) (Srt := InheritanceSort)
      (Query := InheritanceQueryFamily Query) W₁ W₂ (assocQ enc a b))

@[simp] theorem intensionalPATEvidence_add
    (W₁ W₂ : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    intensionalPATEvidence W₁ enc a b + intensionalPATEvidence W₂ enc a b =
      intensionalPATEvidence (W₁ + W₂) enc a b := by
  symm
  simpa [intensionalPATEvidence] using
    (WorldModelSigma.evidence_add (State := State) (Srt := InheritanceSort)
      (Query := InheritanceQueryFamily Query) W₁ W₂ (patQ enc a b))

@[simp] theorem mixedEvidence_add
    (W₁ W₂ : State) (enc : InheritanceQueryBuilder Atom Query) (a b : Atom) :
    mixedEvidence W₁ enc a b + mixedEvidence W₂ enc a b =
      mixedEvidence (W₁ + W₂) enc a b := by
  symm
  simpa [mixedEvidence] using
    (WorldModelSigma.evidence_add (State := State) (Srt := InheritanceSort)
      (Query := InheritanceQueryFamily Query) W₁ W₂ (mixedQ enc a b))

/-- Side condition: mixed evidence is extensional+ASSOC composition. -/
def MixedPolicyAssoc
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence) : Prop :=
  ∀ (W : State) (a b : Atom),
    mixedEvidence W enc a b =
      combine (extensionalEvidence W enc a b) (intensionalAssocEvidence W enc a b)

/-- Side condition: mixed evidence is extensional+ASSOC+PAT composition. -/
def MixedPolicyAssocPat
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence → Evidence) : Prop :=
  ∀ (W : State) (a b : Atom),
    mixedEvidence W enc a b =
      combine
        (extensionalEvidence W enc a b)
        (intensionalAssocEvidence W enc a b)
        (intensionalPATEvidence W enc a b)

/-- Concrete ASSOC-channel semantics correspondence:
typed ASSOC evidence equals a lifted real-valued score. -/
def AssocScoreCorrespondence
    (enc : InheritanceQueryBuilder Atom Query)
    (assocScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence) : Prop :=
  ∀ (W : State) (a b : Atom),
    intensionalAssocEvidence W enc a b = scoreToEvidence (assocScore W a b)

/-- Concrete PAT-channel semantics correspondence:
typed PAT evidence equals a lifted real-valued score. -/
def PATScoreCorrespondence
    (enc : InheritanceQueryBuilder Atom Query)
    (patScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence) : Prop :=
  ∀ (W : State) (a b : Atom),
    intensionalPATEvidence W enc a b = scoreToEvidence (patScore W a b)

/-- Canonical intensional score model for ASSOC/PAT channels.

Packages score channels, evidence lifting, monotonicity, and concrete WM
soundness correspondences in one reusable object. -/
structure IntensionalScoreModel
    (enc : InheritanceQueryBuilder Atom Query) where
  assocScore : State → Atom → Atom → ℝ
  patScore : State → Atom → Atom → ℝ
  scoreToEvidence : ℝ → Evidence
  scoreToEvidence_mono : Monotone scoreToEvidence
  assoc_sound :
    AssocScoreCorrespondence
      (State := State) (Atom := Atom) (Query := Query)
      enc assocScore scoreToEvidence
  pat_sound :
    PATScoreCorrespondence
      (State := State) (Atom := Atom) (Query := Query)
      enc patScore scoreToEvidence

/-- Canonical ASSOC score-to-evidence lift law.
If a score model identifies `assocScore W a b` with `s`, then typed ASSOC evidence
at `(W,a,b)` is exactly `scoreToEvidence s`. -/
theorem assocEvidence_eq_scoreToEvidence_of_assocScore_eq
    (enc : InheritanceQueryBuilder Atom Query)
    (assocScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hAssoc :
      AssocScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc assocScore scoreToEvidence)
    {W : State} {a b : Atom} {s : ℝ}
    (hScore : assocScore W a b = s) :
    intensionalAssocEvidence W enc a b = scoreToEvidence s := by
  simpa [hScore] using hAssoc W a b

/-- Canonical PAT score-to-evidence lift law.
If a score model identifies `patScore W a b` with `s`, then typed PAT evidence
at `(W,a,b)` is exactly `scoreToEvidence s`. -/
theorem patEvidence_eq_scoreToEvidence_of_patScore_eq
    (enc : InheritanceQueryBuilder Atom Query)
    (patScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hPat :
      PATScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc patScore scoreToEvidence)
    {W : State} {a b : Atom} {s : ℝ}
    (hScore : patScore W a b = s) :
    intensionalPATEvidence W enc a b = scoreToEvidence s := by
  simpa [hScore] using hPat W a b

/-- Chapter-12 ASSOC subset semantics:
whenever `subsetRel` holds between concept pairs, ASSOC score is monotone. -/
def AssocSubsetSemantics
    (enc : InheritanceQueryBuilder Atom Query)
    (model : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc)
    (subsetRel : State → Atom → Atom → Atom → Atom → Prop) : Prop :=
  ∀ (W : State) (a b c d : Atom),
    subsetRel W a b c d → model.assocScore W a b ≤ model.assocScore W c d

/-- Chapter-12 PAT subset semantics:
whenever `subsetRel` holds between concept pairs, PAT score is monotone. -/
def PATSubsetSemantics
    (enc : InheritanceQueryBuilder Atom Query)
    (model : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc)
    (subsetRel : State → Atom → Atom → Atom → Atom → Prop) : Prop :=
  ∀ (W : State) (a b c d : Atom),
    subsetRel W a b c d → model.patScore W a b ≤ model.patScore W c d

/-- Evidence-level ASSOC monotonicity induced by subset semantics and score monotonicity. -/
theorem assocEvidence_mono_of_subsetSemantics
    (enc : InheritanceQueryBuilder Atom Query)
    (model : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc)
    (subsetRel : State → Atom → Atom → Atom → Atom → Prop)
    (hSubset : AssocSubsetSemantics
      (State := State) (Atom := Atom) (Query := Query) enc model subsetRel)
    {W : State} {a b c d : Atom}
    (hRel : subsetRel W a b c d) :
    intensionalAssocEvidence W enc a b ≤ intensionalAssocEvidence W enc c d := by
  calc
    intensionalAssocEvidence W enc a b
        = model.scoreToEvidence (model.assocScore W a b) :=
      model.assoc_sound W a b
    _ ≤ model.scoreToEvidence (model.assocScore W c d) :=
      model.scoreToEvidence_mono (hSubset W a b c d hRel)
    _ = intensionalAssocEvidence W enc c d :=
      (model.assoc_sound W c d).symm

/-- Evidence-level PAT monotonicity induced by subset semantics and score monotonicity. -/
theorem patEvidence_mono_of_subsetSemantics
    (enc : InheritanceQueryBuilder Atom Query)
    (model : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc)
    (subsetRel : State → Atom → Atom → Atom → Atom → Prop)
    (hSubset : PATSubsetSemantics
      (State := State) (Atom := Atom) (Query := Query) enc model subsetRel)
    {W : State} {a b c d : Atom}
    (hRel : subsetRel W a b c d) :
    intensionalPATEvidence W enc a b ≤ intensionalPATEvidence W enc c d := by
  calc
    intensionalPATEvidence W enc a b
        = model.scoreToEvidence (model.patScore W a b) :=
      model.pat_sound W a b
    _ ≤ model.scoreToEvidence (model.patScore W c d) :=
      model.scoreToEvidence_mono (hSubset W a b c d hRel)
    _ = intensionalPATEvidence W enc c d :=
      (model.pat_sound W c d).symm

/-- A concrete subset relation directly over WM extensional evidence. -/
def ExtensionalEvidenceSubsetRel
    (enc : InheritanceQueryBuilder Atom Query) :
    State → Atom → Atom → Atom → Atom → Prop :=
  fun W a b c d =>
    extensionalEvidence W enc a b ≤ extensionalEvidence W enc c d

/-- ASSOC evidence monotonicity from extensional-evidence subset semantics. -/
theorem assocEvidence_mono_of_extensionalSubsetSemantics
    (enc : InheritanceQueryBuilder Atom Query)
    (model : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc)
    (hSubset : ∀ (W : State) (a b c d : Atom),
      ExtensionalEvidenceSubsetRel (State := State) (Atom := Atom) (Query := Query) enc
        W a b c d →
        model.assocScore W a b ≤ model.assocScore W c d)
    {W : State} {a b c d : Atom}
    (hRel :
      ExtensionalEvidenceSubsetRel (State := State) (Atom := Atom) (Query := Query) enc
        W a b c d) :
    intensionalAssocEvidence W enc a b ≤ intensionalAssocEvidence W enc c d :=
  assocEvidence_mono_of_subsetSemantics
    (State := State) (Atom := Atom) (Query := Query)
    enc model
    (subsetRel := ExtensionalEvidenceSubsetRel
      (State := State) (Atom := Atom) (Query := Query) enc)
    (hSubset := hSubset)
    hRel

/-- PAT evidence monotonicity from extensional-evidence subset semantics. -/
theorem patEvidence_mono_of_extensionalSubsetSemantics
    (enc : InheritanceQueryBuilder Atom Query)
    (model : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc)
    (hSubset : ∀ (W : State) (a b c d : Atom),
      ExtensionalEvidenceSubsetRel (State := State) (Atom := Atom) (Query := Query) enc
        W a b c d →
        model.patScore W a b ≤ model.patScore W c d)
    {W : State} {a b c d : Atom}
    (hRel :
      ExtensionalEvidenceSubsetRel (State := State) (Atom := Atom) (Query := Query) enc
        W a b c d) :
    intensionalPATEvidence W enc a b ≤ intensionalPATEvidence W enc c d :=
  patEvidence_mono_of_subsetSemantics
    (State := State) (Atom := Atom) (Query := Query)
    enc model
    (subsetRel := ExtensionalEvidenceSubsetRel
      (State := State) (Atom := Atom) (Query := Query) enc)
    (hSubset := hSubset)
    hRel

/-- Concrete mixed-channel correspondence for extensional+ASSOC composition. -/
def MixedAssocScoreCorrespondence
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence) : Prop :=
  ∀ (W : State) (a b : Atom),
    mixedEvidence W enc a b =
      combine
        (extensionalEvidence W enc a b)
        (scoreToEvidence (assocScore W a b))

/-- Concrete mixed-channel correspondence for extensional+ASSOC+PAT composition. -/
def MixedAssocPatScoreCorrespondence
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence → Evidence)
    (assocScore patScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence) : Prop :=
  ∀ (W : State) (a b : Atom),
    mixedEvidence W enc a b =
      combine
        (extensionalEvidence W enc a b)
        (scoreToEvidence (assocScore W a b))
        (scoreToEvidence (patScore W a b))

/-- Build `MixedPolicyAssoc` from concrete ASSOC-score correspondences. -/
theorem mixedPolicyAssoc_of_assocScoreCorrespondence
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      MixedAssocScoreCorrespondence enc combine assocScore scoreToEvidence)
    (hAssoc :
      AssocScoreCorrespondence enc assocScore scoreToEvidence) :
    MixedPolicyAssoc (State := State) (Atom := Atom) (Query := Query) enc combine := by
  intro W a b
  simpa [hAssoc W a b] using hMixed W a b

/-- Build `MixedPolicyAssocPat` from concrete ASSOC/PAT-score correspondences. -/
theorem mixedPolicyAssocPat_of_assocPatScoreCorrespondence
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence → Evidence)
    (assocScore patScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      MixedAssocPatScoreCorrespondence enc combine assocScore patScore scoreToEvidence)
    (hAssoc :
      AssocScoreCorrespondence enc assocScore scoreToEvidence)
    (hPat :
      PATScoreCorrespondence enc patScore scoreToEvidence) :
    MixedPolicyAssocPat (State := State) (Atom := Atom) (Query := Query) enc combine := by
  intro W a b
  simpa [hAssoc W a b, hPat W a b] using hMixed W a b

/-- Build `MixedPolicyAssoc` from a canonical intensional score model. -/
theorem mixedPolicyAssoc_of_scoreModel
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence)
    (model : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc)
    (hMixed :
      MixedAssocScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc combine model.assocScore model.scoreToEvidence) :
    MixedPolicyAssoc (State := State) (Atom := Atom) (Query := Query) enc combine := by
  exact mixedPolicyAssoc_of_assocScoreCorrespondence
    (State := State) (Atom := Atom) (Query := Query)
    enc combine model.assocScore model.scoreToEvidence hMixed model.assoc_sound

/-- Build `MixedPolicyAssocPat` from a canonical intensional score model. -/
theorem mixedPolicyAssocPat_of_scoreModel
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence → Evidence)
    (model : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc)
    (hMixed :
      MixedAssocPatScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc combine model.assocScore model.patScore model.scoreToEvidence) :
    MixedPolicyAssocPat (State := State) (Atom := Atom) (Query := Query) enc combine := by
  exact mixedPolicyAssocPat_of_assocPatScoreCorrespondence
    (State := State) (Atom := Atom) (Query := Query)
    enc combine model.assocScore model.patScore model.scoreToEvidence
    hMixed model.assoc_sound model.pat_sound

/-- Strong ASSOC semantic package:
bundles score-model channels with the concrete mixed ASSOC correspondence. -/
structure AssocSemanticModel
    (enc : InheritanceQueryBuilder Atom Query) where
  scoreModel : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc
  combine : Evidence → Evidence → Evidence
  mixed_sound :
    MixedAssocScoreCorrespondence
      (State := State) (Atom := Atom) (Query := Query)
      enc combine scoreModel.assocScore scoreModel.scoreToEvidence

/-- Strong ASSOC+PAT semantic package:
bundles score-model channels with the concrete mixed ASSOC+PAT correspondence. -/
structure AssocPatSemanticModel
    (enc : InheritanceQueryBuilder Atom Query) where
  scoreModel : IntensionalScoreModel (State := State) (Atom := Atom) (Query := Query) enc
  combine : Evidence → Evidence → Evidence → Evidence
  mixed_sound :
    MixedAssocPatScoreCorrespondence
      (State := State) (Atom := Atom) (Query := Query)
      enc combine
      scoreModel.assocScore scoreModel.patScore scoreModel.scoreToEvidence

/-- Derive `MixedPolicyAssoc` directly from a strong ASSOC semantic package. -/
theorem mixedPolicyAssoc_of_assocSemanticModel
    (enc : InheritanceQueryBuilder Atom Query)
    (m : AssocSemanticModel (State := State) (Atom := Atom) (Query := Query) enc) :
    MixedPolicyAssoc (State := State) (Atom := Atom) (Query := Query) enc m.combine :=
  mixedPolicyAssoc_of_scoreModel
    (State := State) (Atom := Atom) (Query := Query)
    enc m.combine m.scoreModel m.mixed_sound

/-- Derive `MixedPolicyAssocPat` directly from a strong ASSOC+PAT semantic package. -/
theorem mixedPolicyAssocPat_of_assocPatSemanticModel
    (enc : InheritanceQueryBuilder Atom Query)
    (m : AssocPatSemanticModel (State := State) (Atom := Atom) (Query := Query) enc) :
    MixedPolicyAssocPat (State := State) (Atom := Atom) (Query := Query) enc m.combine :=
  mixedPolicyAssocPat_of_scoreModel
    (State := State) (Atom := Atom) (Query := Query)
    enc m.combine m.scoreModel m.mixed_sound

/-- Typed mixed-channel rewrite constructor (extensional + ASSOC). -/
noncomputable def mixedRewriteRule_of_assoc
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence)
    (Side : Prop)
    (hSound : Side → MixedPolicyAssoc (State := State) (Atom := Atom) (Query := Query) enc combine)
    (a b : Atom) :
    WorldModelSigma.WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  { side := Side
    conclusion := mixedQ enc a b
    derive := fun W => combine (extensionalEvidence W enc a b) (intensionalAssocEvidence W enc a b)
    sound := by
      intro hSide W
      simpa [mixedEvidence] using (hSound hSide W a b).symm }

/-- Typed mixed-channel rewrite constructor (extensional + ASSOC + PAT). -/
noncomputable def mixedRewriteRule_of_assoc_pat
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence → Evidence)
    (Side : Prop)
    (hSound : Side → MixedPolicyAssocPat (State := State) (Atom := Atom) (Query := Query) enc combine)
    (a b : Atom) :
    WorldModelSigma.WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  { side := Side
    conclusion := mixedQ enc a b
    derive := fun W =>
      combine
        (extensionalEvidence W enc a b)
        (intensionalAssocEvidence W enc a b)
        (intensionalPATEvidence W enc a b)
    sound := by
      intro hSide W
      simpa [mixedEvidence] using (hSound hSide W a b).symm }

/-- Admissibility helper for `mixedRewriteRule_of_assoc`. -/
theorem mixedRewriteRule_of_assoc_apply
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence)
    (Side : Prop)
    (hSound : Side → MixedPolicyAssoc (State := State) (Atom := Atom) (Query := Query) enc combine)
    (a b : Atom)
    (W : State)
    (hSide : Side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMQueryJudgmentSigma (State := State) (Srt := InheritanceSort)
      (Query := InheritanceQueryFamily Query)
      W
      (mixedQ enc a b)
      (combine (extensionalEvidence W enc a b) (intensionalAssocEvidence W enc a b)) := by
  exact WorldModelSigma.WMRewriteRuleSigma.apply
    (r := mixedRewriteRule_of_assoc enc combine Side hSound a b)
    hSide hW

/-- Admissibility helper for `mixedRewriteRule_of_assoc_pat`. -/
theorem mixedRewriteRule_of_assoc_pat_apply
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence → Evidence)
    (Side : Prop)
    (hSound : Side →
      MixedPolicyAssocPat (State := State) (Atom := Atom) (Query := Query) enc combine)
    (a b : Atom)
    (W : State)
    (hSide : Side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMQueryJudgmentSigma (State := State) (Srt := InheritanceSort)
      (Query := InheritanceQueryFamily Query)
      W
      (mixedQ enc a b)
      (combine
        (extensionalEvidence W enc a b)
        (intensionalAssocEvidence W enc a b)
        (intensionalPATEvidence W enc a b)) := by
  exact WorldModelSigma.WMRewriteRuleSigma.apply
    (r := mixedRewriteRule_of_assoc_pat enc combine Side hSound a b)
    hSide hW

end InheritanceQueryBuilder

namespace InheritanceQueryBuilder

section ConcreteMixedPolicies

variable {State Atom Query : Type}
variable [EvidenceType State]
variable [WorldModel State Query]

/-- Concrete inheritance query builder with `mixed = extensional`. -/
def mixedAsExtensional
    (extensional intensionalAssoc intensionalPAT : Atom → Atom → Query) :
    InheritanceQueryBuilder Atom Query where
  extensional := extensional
  intensionalAssoc := intensionalAssoc
  intensionalPAT := intensionalPAT
  mixed := extensional

/-- Concrete inheritance query builder with `mixed = intensionalAssoc`. -/
def mixedAsAssoc
    (extensional intensionalAssoc intensionalPAT : Atom → Atom → Query) :
    InheritanceQueryBuilder Atom Query where
  extensional := extensional
  intensionalAssoc := intensionalAssoc
  intensionalPAT := intensionalPAT
  mixed := intensionalAssoc

/-- Concrete side-condition discharge for the extensional-projection mixed policy. -/
theorem mixedPolicyAssoc_mixedAsExtensional
    (extensional intensionalAssoc intensionalPAT : Atom → Atom → Query) :
    MixedPolicyAssoc
      (State := State) (Atom := Atom) (Query := Query)
      (mixedAsExtensional extensional intensionalAssoc intensionalPAT)
      (fun e _ => e) := by
  letI : WorldModelSigma State InheritanceSort (InheritanceQueryFamily Query) :=
    worldModelSigmaInheritanceFromUntyped (State := State) (Query := Query)
  intro W a b
  change
    WorldModel.evidence (State := State) (Query := Query) W
      (InheritanceQueryFamily.erase (InheritanceQueryFamily.mix (extensional a b))) =
      (fun e _ => e)
        (WorldModel.evidence (State := State) (Query := Query) W
          (InheritanceQueryFamily.erase (InheritanceQueryFamily.ext (extensional a b))))
        (WorldModel.evidence (State := State) (Query := Query) W
          (InheritanceQueryFamily.erase (InheritanceQueryFamily.assoc (intensionalAssoc a b))))
  rfl

/-- Concrete side-condition discharge for the ASSOC-projection mixed policy. -/
theorem mixedPolicyAssoc_mixedAsAssoc
    (extensional intensionalAssoc intensionalPAT : Atom → Atom → Query) :
    MixedPolicyAssoc
      (State := State) (Atom := Atom) (Query := Query)
      (mixedAsAssoc extensional intensionalAssoc intensionalPAT)
      (fun _ e => e) := by
  letI : WorldModelSigma State InheritanceSort (InheritanceQueryFamily Query) :=
    worldModelSigmaInheritanceFromUntyped (State := State) (Query := Query)
  intro W a b
  change
    WorldModel.evidence (State := State) (Query := Query) W
      (InheritanceQueryFamily.erase (InheritanceQueryFamily.mix (intensionalAssoc a b))) =
      (fun _ e => e)
        (WorldModel.evidence (State := State) (Query := Query) W
          (InheritanceQueryFamily.erase (InheritanceQueryFamily.ext (extensional a b))))
        (WorldModel.evidence (State := State) (Query := Query) W
          (InheritanceQueryFamily.erase (InheritanceQueryFamily.assoc (intensionalAssoc a b))))
  rfl

/-- Canonical mixed-rule constructor for extensional-projection policy (`Side := True`). -/
noncomputable def mixedRewriteRule_extensionalProjection
    (extensional intensionalAssoc intensionalPAT : Atom → Atom → Query)
    (a b : Atom) :
    WorldModelSigma.WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  mixedRewriteRule_of_assoc
    (State := State) (Atom := Atom) (Query := Query)
    (enc := mixedAsExtensional extensional intensionalAssoc intensionalPAT)
    (combine := fun e _ => e)
    (Side := True)
    (hSound := by
      intro _
      exact mixedPolicyAssoc_mixedAsExtensional
        (State := State) (Atom := Atom) (Query := Query)
        extensional intensionalAssoc intensionalPAT)
    a b

/-- Canonical mixed-rule constructor for ASSOC-projection policy (`Side := True`). -/
noncomputable def mixedRewriteRule_assocProjection
    (extensional intensionalAssoc intensionalPAT : Atom → Atom → Query)
    (a b : Atom) :
    WorldModelSigma.WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  mixedRewriteRule_of_assoc
    (State := State) (Atom := Atom) (Query := Query)
    (enc := mixedAsAssoc extensional intensionalAssoc intensionalPAT)
    (combine := fun _ e => e)
    (Side := True)
    (hSound := by
      intro _
      exact mixedPolicyAssoc_mixedAsAssoc
        (State := State) (Atom := Atom) (Query := Query)
        extensional intensionalAssoc intensionalPAT)
    a b

/-- Canonical semantic mixed-rule constructor from ASSOC-score correspondences
(`Side := True`). -/
noncomputable def mixedRewriteRule_assocSemantic
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence)
    (assocScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      MixedAssocScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc combine assocScore scoreToEvidence)
    (hAssoc :
      AssocScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc assocScore scoreToEvidence)
    (a b : Atom) :
    WorldModelSigma.WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  mixedRewriteRule_of_assoc
    (State := State) (Atom := Atom) (Query := Query)
    (enc := enc) (combine := combine) (Side := True)
    (hSound := by
      intro _
      exact mixedPolicyAssoc_of_assocScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc combine assocScore scoreToEvidence hMixed hAssoc)
    a b

/-- Canonical semantic mixed-rule constructor from ASSOC/PAT-score correspondences
(`Side := True`). -/
noncomputable def mixedRewriteRule_assocPatSemantic
    (enc : InheritanceQueryBuilder Atom Query)
    (combine : Evidence → Evidence → Evidence → Evidence)
    (assocScore patScore : State → Atom → Atom → ℝ)
    (scoreToEvidence : ℝ → Evidence)
    (hMixed :
      MixedAssocPatScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc combine assocScore patScore scoreToEvidence)
    (hAssoc :
      AssocScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc assocScore scoreToEvidence)
    (hPat :
      PATScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc patScore scoreToEvidence)
    (a b : Atom) :
    WorldModelSigma.WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  mixedRewriteRule_of_assoc_pat
    (State := State) (Atom := Atom) (Query := Query)
    (enc := enc) (combine := combine) (Side := True)
    (hSound := by
      intro _
      exact mixedPolicyAssocPat_of_assocPatScoreCorrespondence
        (State := State) (Atom := Atom) (Query := Query)
        enc combine assocScore patScore scoreToEvidence hMixed hAssoc hPat)
    a b

/-- Canonical semantic mixed-rule constructor from a strong ASSOC semantic package
(`Side := True`). -/
noncomputable def mixedRewriteRule_assocSemantic_of_model
    (enc : InheritanceQueryBuilder Atom Query)
    (m : AssocSemanticModel (State := State) (Atom := Atom) (Query := Query) enc)
    (a b : Atom) :
    WorldModelSigma.WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  mixedRewriteRule_assocSemantic
    (State := State) (Atom := Atom) (Query := Query)
    enc m.combine m.scoreModel.assocScore m.scoreModel.scoreToEvidence
    m.mixed_sound m.scoreModel.assoc_sound a b

/-- Canonical semantic mixed-rule constructor from a strong ASSOC+PAT semantic package
(`Side := True`). -/
noncomputable def mixedRewriteRule_assocPatSemantic_of_model
    (enc : InheritanceQueryBuilder Atom Query)
    (m : AssocPatSemanticModel (State := State) (Atom := Atom) (Query := Query) enc)
    (a b : Atom) :
    WorldModelSigma.WMRewriteRuleSigma State InheritanceSort (InheritanceQueryFamily Query) :=
  mixedRewriteRule_assocPatSemantic
    (State := State) (Atom := Atom) (Query := Query)
    enc m.combine m.scoreModel.assocScore m.scoreModel.patScore m.scoreModel.scoreToEvidence
    m.mixed_sound m.scoreModel.assoc_sound m.scoreModel.pat_sound a b

end ConcreteMixedPolicies

end InheritanceQueryBuilder

end Mettapedia.Logic.PLNIntensionalWorldModel
