import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.EthicsFormulaWMBridge
import Mettapedia.Ethics.FOETCore
import Mettapedia.Ethics.GewirthBridge

set_option autoImplicit false

/-!
# Ethics Upper-Shard Kernel / Adapter

This module provides a layered ethics kernel above the current WM lowering.

It is **not** the final ethics ontology.  It is the adapter/kernel layer that
keeps the current WM meta-stability theorems green while the richer FOET
semantic core is being ported into mettapedia.

## Four-axis kernel (GPT-5.4 Pro / council redesign)

Following Parfit, Scanlon, Korsgaard (analytic), Weinbaum, Levinas
(continental), and Noddings, Held (care ethics), ethical claims are
factored along four independent axes:

- **Content** (`EthicalContent`): WHAT is being claimed — a proposition
  about the world, a relation between agents, or an enduring disposition.
- **Presentation** (`EthicalPresentation`): HOW the claim is modally
  expressed — as a deontic obligation/prohibition/permission, an axiological
  good/bad/permissible judgment, or a virtue/vice attribution.
- **Ground** (`EthicalGround`): WHY the claim holds — grounded in the
  Gewirth PGC, a universal duty, a care relation, a consequentialist
  calculus, or merely asserted.
- **Role** (`EthicalRole`): WHERE the claim fits in the agent's meaning-
  generation process — as a situation assessment, prediction, active goal,
  plan, or standing disposition.

The critical constraint (GPT-5.4 Pro): **grounds never replace content**.
A Gewirth-grounded claim still carries the explicit non-interference sentence
it grounds.  A duty-grounded claim still carries the presented deontic or
value content.

The `StructuredEthicalClaim` structure bundles all four axes.  The legacy
`UpperShardEthicalClaim` inductive is retained for backward compatibility
with existing downstream theorems; a conversion function bridges the two.

Only at the final lowering step does content compile to WM queries via
`EthicalAnchor`.  This keeps the WM bridge honest while preserving more
structure above it, but the lasting semantic source should come from the FOET
structured-sentence layer rather than this kernel alone.

**Grounding as proof obligation (Korsgaard).**  The `EthicalGround` type
uses tags (universe-safe), but the `Witnessed₀` predicate turns each tag
into a real proof obligation.  A Gewirth tag requires providing a
`PGCInterpretation`, `PGCAssumptions`, and `PPA` witness.  This separates
the JUDGMENT (the claim has ground G) from the EVIDENCE (here's why) —
following Martin-Löf's distinction between judgment and verification.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology

open Mettapedia.Ethics
open Mettapedia.Ethics.Gewirth
open Mettapedia.Ethics.GewirthBridge
open Mettapedia.CognitiveArchitecture.Values.Deontological
open Mettapedia.CognitiveArchitecture.Values.Relational
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification

universe u w

-- ═══════════════════════════════════════════════════════════════════════════
-- Four-axis ethical claim kernel
-- ═══════════════════════════════════════════════════════════════════════════

/-- WHAT is being claimed: a proposition about the world, a typed relation
between agents, or an enduring care-style disposition.  Content is orthogonal
to how the claim is presented or why it holds. -/
inductive EthicalContent (World : Type u) (Agent : Type u) where
  | propositional : Formula World → EthicalContent World Agent
  | relational : Agent → Agent → RelationalValueType → EthicalContent World Agent
  | dispositional : Agent → EthicalContent World Agent

/-- HOW the claim is modally expressed.  This is the logical FORM, orthogonal
to the justificatory ground.  A Gewirth right can be expressed as a deontic
obligation OR as a value judgment; both are valid presentations of the same
grounded content. -/
inductive EthicalPresentation where
  | deontic : DeonticAttribute → EthicalPresentation
  | axiological : MoralValueAttribute → EthicalPresentation
  | unmodalized : EthicalPresentation
  deriving DecidableEq

/-- FOET-ready paradigm family for structured presentations. -/
inductive EthicalParadigm where
  | deontological
  | axiological
  | utilitarian
  | virtue
  | care
  deriving DecidableEq

/-- FOET-ready structured presentation layer.

This is the migration target for replacing the thin `EthicalPresentation`
enumeration with recursive FOET-style sentences.  It is added in parallel so
the current Stage 1 kernel can stay stable while Stage 2 porting proceeds.
-/
inductive StructuredEthicalPresentation (World : Type u) where
  | deontological :
      StructuredSentence World (StructuredImperativeAtom World) →
        StructuredEthicalPresentation World
  | axiological :
      StructuredSentence World (StructuredValueAtom World) →
        StructuredEthicalPresentation World
  | utilitarian :
      StructuredSentence World (StructuredUtilityAtom World) →
        StructuredEthicalPresentation World
  | virtue :
      StructuredSentence World (StructuredVirtueTargetAtom World) →
        StructuredEthicalPresentation World
  | care :
      StructuredSentence World (StructuredValueAtom World) →
        StructuredEthicalPresentation World

def StructuredEthicalPresentation.paradigm {World : Type u} :
    StructuredEthicalPresentation World → EthicalParadigm
  | .deontological _ => .deontological
  | .axiological _ => .axiological
  | .utilitarian _ => .utilitarian
  | .virtue _ => .virtue
  | .care _ => .care

/-- Promote a deontological structured presentation into the aligned
axiological view already proved equivalent in FOET. -/
def StructuredEthicalPresentation.deontologicalToAxiological
    {World : Type u}
    (s : StructuredSentence World (StructuredImperativeAtom World)) :
    StructuredEthicalPresentation World :=
  .axiological (StructuredSentence.map imperativeToValueAtom s)

/-- Satisfaction restricted to the deontological/axiological presentation seam.

This keeps the deontic-to-value equivalence visible at the
`StructuredEthicalPresentation` layer without pretending we already have one
uniform semantics for all five paradigms. -/
def StructuredEthicalPresentation.SatDeonticOrAxiological
    {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (w : World) :
    StructuredEthicalPresentation World → Prop
  | .deontological s =>
      (StructuredSentence.semantics (World := World)
        (sumSemantics (deonticSemantics World semD) (formulaSemantics World))).Sat w s
  | .axiological s =>
      (StructuredSentence.semantics (World := World)
        (sumSemantics (valueJudgmentSemantics World semV) (formulaSemantics World))).Sat w s
  | _ => False

/-- The FOET deontic/value equivalence transported into the kernel-level
`StructuredEthicalPresentation` seam. -/
theorem StructuredEthicalPresentation.sat_deontological_iff_sat_deontologicalToAxiological
    {World : Type u}
    (semD : DeonticSemantics World) (semV : ValueSemantics World)
    (h_align : ∀ a φ w, semD.deontic a φ w ↔ semV.morally (deonticToMoralValue a) φ w)
    (w : World)
    (s : StructuredSentence World (StructuredImperativeAtom World)) :
    StructuredEthicalPresentation.SatDeonticOrAxiological semD semV w
        (.deontological s) ↔
      StructuredEthicalPresentation.SatDeonticOrAxiological semD semV w
        (StructuredEthicalPresentation.deontologicalToAxiological s) := by
  simpa [StructuredEthicalPresentation.SatDeonticOrAxiological,
    StructuredEthicalPresentation.deontologicalToAxiological] using
    sat_structuredImperative_iff_sat_structuredValue
      (semD := semD) (semV := semV) h_align w s

/-- Best-effort embedding of the thin Stage 1 presentation tag into the richer
FOET-ready paradigm family.  `unmodalized` is intentionally left unmapped,
because forcing it into a paradigm would overstate what the current kernel
knows. -/
def EthicalPresentation.legacyParadigm? : EthicalPresentation → Option EthicalParadigm
  | .deontic _ => some .deontological
  | .axiological _ => some .axiological
  | .unmodalized => none

/-- WHY the claim holds.  Orthogonal to content and form.

Following Martin-Löf / Pfenning / Coquand: we separate the JUDGMENT
("this claim has ground G") from the EVIDENCE ("here's the proof").

The ground TAG is lightweight and lives at universe `u`.  The ground
WITNESS is a separate `Prop`-valued predicate (`EthicalGround.Witnessed`)
that turns the tag into a real proof obligation.

Korsgaard: "A ground without a proof is an assertion."  In our design,
the ground tag is the assertion; the witness predicate is the proof.
Theorems that need genuine grounding require `h : ground.Witnessed₀ ...`. -/
inductive EthicalGround (Agent : Type u) where
  /-- No justification beyond assertion. -/
  | asserted : EthicalGround Agent
  /-- Claimed to be grounded in the Gewirth PGC.  The witness predicate
      requires a `PGCInterpretation`, `PGCAssumptions`, and `PPA` proof. -/
  | gewirthPGC : EthicalGround Agent
  /-- Grounded in a named universal duty. -/
  | universalDuty : UniversalDuty → EthicalGround Agent
  /-- Grounded in a care relation between two agents. -/
  | careRelation : Agent → Agent → RelationalValueType → EthicalGround Agent
  /-- Claimed to be grounded in a consequentialist calculation. -/
  | consequentialist : EthicalGround Agent

/-- A finite consequentialist witness over a live choice set.

The witness is no longer a bare "some utility differs somewhere" fact.  It
names the concrete candidates being ranked, together with a strict preference
between two of them. -/
structure ConsequentialistChoiceWitness (Action : Type) [DecidableEq Action] where
  candidates : Finset Action
  utility : Action → ℝ
  best : Action
  worst : Action
  best_mem : best ∈ candidates
  worst_mem : worst ∈ candidates
  strictly_prefers : utility worst < utility best

/-- The witness predicate at universe 0 (covers all concrete examples).

A Gewirth ground requires a `PGCInterpretation`, `PGCAssumptions`, and
`PPA` evidence.  A universal duty requires an explicit deontological layer
assigning that duty positive confidence and importance. -/
def EthicalGround.Witnessed₀ {Agent : Type u} :
    EthicalGround Agent → Prop
  | .asserted => True
  | .gewirthPGC =>
      ∃ (I : PGCInterpretation.{0}) (_ : PGCAssumptions I) (a : I.Entity) (c : I.Ctx),
        PPA I.ActsOnPurpose a c (I.worldOf c)
  | .universalDuty d =>
      ∃ (Action : Type) (layer : DeontologicalLayer Action),
        0 < (layer.dutyStrengths d).confidence.val ∧
        0 < (layer.dutyStrengths d).importance.val
  | .careRelation _ target relation =>
      ∃ state : RelationalState Agent,
        (0 : ℚ) <
          (match relation with
          | .trust => state.trust target
          | .loyalty => state.loyalty target
          | .gratitude => state.gratitude target
          | .forgiveness => state.forgiveness target
          | .love => state.love target
          | .friendship => state.friendship target).val
  | .consequentialist =>
      ∃ (Action : Type) (_ : DecidableEq Action),
        Nonempty (ConsequentialistChoiceWitness Action)

/-- Stronger candidate-local witness used when the relevant practical choice
set is already known.  This refines the global witness without forcing a
cascade through the rest of the grounded-claim API. -/
def EthicalGround.WitnessedForCandidateSet₀
    {Agent : Type u} {Action : Type} [DecidableEq Action]
    (ground : EthicalGround Agent) (candidates : Finset Action) : Prop :=
  ground.Witnessed₀ ∧
    match ground with
    | .consequentialist =>
        ∃ utility : Action → ℝ, ∃ best ∈ candidates, ∃ worst ∈ candidates,
          utility worst < utility best
    | _ => True

/-- An asserted ground is trivially witnessed. -/
theorem EthicalGround.witnessed₀_asserted {Agent : Type u} :
    (EthicalGround.asserted : EthicalGround Agent).Witnessed₀ :=
  trivial

/-- A Gewirth ground is witnessed when we have the full PGC stack.

This is the philosophical load-bearing theorem: you cannot claim Gewirth
grounding without producing the PGC interpretation, assumptions, and
purposive-agency witness.  The universe is fixed at 0 because all concrete
examples in this project use `Type 0` agents (e.g., `Nat`). -/
theorem EthicalGround.witnessed₀_gewirthPGC_of
    (I : PGCInterpretation.{0}) (h : PGCAssumptions I)
    (a : I.Entity) (c : I.Ctx)
    (hPPA : PPA I.ActsOnPurpose a c (I.worldOf c)) :
    (EthicalGround.gewirthPGC : EthicalGround I.Entity).Witnessed₀ :=
  ⟨I, h, a, c, hPPA⟩

/-- A universal duty is genuinely witnessed when it is backed by a concrete
deontological layer assigning that duty positive confidence and importance. -/
theorem EthicalGround.witnessed₀_universalDuty_of_positiveStrength
    {Agent : Type u} {Action : Type}
    (layer : DeontologicalLayer Action)
    (d : UniversalDuty)
    (hConfidence : 0 < (layer.dutyStrengths d).confidence.val)
    (hImportance : 0 < (layer.dutyStrengths d).importance.val) :
    (EthicalGround.universalDuty d : EthicalGround Agent).Witnessed₀ :=
  ⟨Action, layer, hConfidence, hImportance⟩

/-- Read off the current strength of one relational value toward one target. -/
def RelationalState.level
    {Agent : Type*} (state : RelationalState Agent)
    (relation : RelationalValueType) (target : Agent) :
    Mettapedia.CognitiveArchitecture.OpenPsi.UnitValue :=
  match relation with
  | .trust => state.trust target
  | .loyalty => state.loyalty target
  | .gratitude => state.gratitude target
  | .forgiveness => state.forgiveness target
  | .love => state.love target
  | .friendship => state.friendship target

/-- A care relation is genuinely witnessed when there is a concrete relational
state assigning positive strength to the named relation toward the target. -/
theorem EthicalGround.witnessed₀_careRelation_of_positiveLevel
    {Agent : Type u}
    (source target : Agent)
    (relation : RelationalValueType)
    (state : RelationalState Agent)
    (hLevel : (0 : ℚ) < (RelationalState.level state relation target).val) :
    (EthicalGround.careRelation source target relation : EthicalGround Agent).Witnessed₀ :=
  ⟨state, hLevel⟩

/-- A consequentialist ground is genuinely witnessed when a finite live choice
set carries a strict utility ranking between two candidates. -/
theorem EthicalGround.witnessed₀_consequentialist_of_choiceWitness
    {Agent : Type u} {Action : Type} [DecidableEq Action]
    (witness : ConsequentialistChoiceWitness Action) :
    (EthicalGround.consequentialist : EthicalGround Agent).Witnessed₀ :=
  ⟨Action, inferInstance, ⟨witness⟩⟩

/-- Candidate-local consequentialist witness over the practical options that
actually matter for the current problem. -/
theorem EthicalGround.witnessedForCandidateSet₀_consequentialist_of_strictRanking
    {Agent : Type u} {Action : Type} [DecidableEq Action]
    (candidates : Finset Action)
    (utility : Action → ℝ)
    (best worst : Action)
    (hBest : best ∈ candidates)
    (hWorst : worst ∈ candidates)
    (hStrict : utility worst < utility best) :
    (EthicalGround.consequentialist : EthicalGround Agent).WitnessedForCandidateSet₀ candidates := by
  constructor
  · exact EthicalGround.witnessed₀_consequentialist_of_choiceWitness
      { candidates := candidates
        utility := utility
        best := best
        worst := worst
        best_mem := hBest
        worst_mem := hWorst
        strictly_prefers := hStrict }
  · exact ⟨utility, best, hBest, worst, hWorst, hStrict⟩

/-- The candidate-local refinement really does imply the ordinary ground
witness used by the rest of the current kernel. -/
theorem EthicalGround.witnessed₀_of_witnessedForCandidateSet₀
    {Agent : Type u} {Action : Type} [DecidableEq Action]
    {ground : EthicalGround Agent} {candidates : Finset Action}
    (h : ground.WitnessedForCandidateSet₀ candidates) :
    ground.Witnessed₀ :=
  h.1

/-- WHERE the claim fits in the agent's meaning-generation process
(Thórisson/Talevi 2024).  Orthogonal to content, form, and ground. -/
inductive EthicalRole where
  | situation : EthicalRole
  | prediction : EthicalRole
  | activeGoal : EthicalRole
  | plan : EthicalRole
  | standingDisposition : EthicalRole
  deriving DecidableEq

/-- A structured ethical claim with all four axes independent.

This is the philosophically principled representation.  Any combination
of content, presentation, ground, and role is expressible:
- a Gewirth-grounded deontic obligation serving as an active goal,
- a care-grounded axiological judgment in the prediction role,
- an asserted dispositional claim as a standing disposition.

The `subject` field names the agent the claim is ABOUT.  Grounds never
replace content: the `content` field always carries the explicit
proposition, relation, or disposition being claimed. -/
structure StructuredEthicalClaim (World : Type u) (Agent : Type u) where
  /-- The agent this claim is about. -/
  subject : Agent
  /-- WHAT: proposition, relation, or disposition. -/
  content : EthicalContent World Agent
  /-- HOW: deontic, axiological, or unmodalized. -/
  presentation : EthicalPresentation
  /-- WHY: the justificatory source. -/
  ground : EthicalGround Agent
  /-- WHERE: role in the meaning-generation process. -/
  role : EthicalRole

/-- A thin primary WM-lowering interface whose source language is already the
four-axis structured claim kernel, rather than the legacy anchor layer. -/
structure StructuredEthicsQueryEncoder (World : Type u) (Agent : Type u) (Atom : Type*) where
  propositionalQuery :
    Agent → EthicalPresentation → EthicalGround Agent → EthicalRole →
      Formula World → ConstraintQuery Atom
  relationalQuery :
    Agent → Agent → Agent → EthicalGround Agent → EthicalRole →
      RelationalValueType → ConstraintQuery Atom
  dispositionalQuery :
    Agent → Agent → EthicalGround Agent → EthicalRole → ConstraintQuery Atom

/-- A compatibility policy for lifting the legacy anchor encoder into the
structured-claim lowering interface. -/
structure StructuredClaimLabeler (World : Type u) (Agent : Type u) (Label : Type w) where
  label : StructuredEthicalClaim World Agent → Label

/-- Honest extra hypothesis needed to transport FOET's deontic/value
equivalence through the lossy legacy lowering seam: the labeler must not change
the label when a propositional deontic claim is re-presented as its aligned
axiological translation. -/
def StructuredClaimLabeler.DeonticValueAligned
    {World : Type u} {Agent : Type u} {Label : Type w}
    (labeler : StructuredClaimLabeler World Agent Label) : Prop :=
  ∀ (subject : Agent) (ground : EthicalGround Agent) (role : EthicalRole)
      (tag : DeonticAttribute) (φ : Formula World),
    labeler.label
        ({ subject := subject
           content := .propositional φ
           presentation := .deontic tag
           ground := ground
           role := role } :
          StructuredEthicalClaim World Agent) =
      labeler.label
        ({ subject := subject
           content := .propositional φ
           presentation := .axiological (deonticToMoralValue tag)
           ground := ground
           role := role } :
          StructuredEthicalClaim World Agent)

/-- Present a labeled value sentence as a structured axiological claim. -/
def LabeledValueJudgmentSentence.toStructuredClaim
    {World : Type u} {Agent : Type u} {Label : Type w}
    (s : LabeledValueJudgmentSentence World Agent Label)
    (role : EthicalRole)
    (ground : EthicalGround Agent := .asserted)
    : StructuredEthicalClaim World Agent where
  subject := s.agent
  content := .propositional s.sentence.formula
  presentation := .axiological s.sentence.tag
  ground := ground
  role := role

/-- Present a labeled deontic sentence as a structured deontological claim. -/
def LabeledDeonticSentence.toStructuredClaim
    {World : Type u} {Agent : Type u} {Label : Type w}
    (s : LabeledDeonticSentence World Agent Label)
    (role : EthicalRole)
    (ground : EthicalGround Agent := .asserted)
    : StructuredEthicalClaim World Agent where
  subject := s.agent
  content := .propositional s.sentence.formula
  presentation := .deontic s.sentence.tag
  ground := ground
  role := role

/-- Lower a structured claim to the legacy `EthicalAnchor` for WM
compilation.  This is the adapter that keeps all downstream meta-stability
theorems green while the ontology above improves.

The lowering is intentionally lossy: the four-axis structure is richer than
the five-variant `EthicalAnchor`.  Information about ground, role, and
fine-grained content is discarded at this boundary. -/
def StructuredEthicalClaim.toLegacyAnchor
    {World : Type u} {Agent : Type u} {Label : Type w}
    (label : Label)
    (claim : StructuredEthicalClaim World Agent) :
    EthicalAnchor Agent Label :=
  match claim.content with
  | .dispositional a => .epistemicUniversalLove a
  | .relational a b r => .relational a b r
  | .propositional _ =>
      match claim.presentation with
      | .deontic attr => .deontic claim.subject attr label
      | .axiological attr => .moralValue claim.subject attr label
      | .unmodalized => .epistemicUniversalLove claim.subject

/-- When available, view a structured claim as a richer FOET-style paradigm
presentation.  This is the migration seam for replacing the thin presentation
tag with structured FOET sentences. -/
def StructuredEthicalClaim.toFOETPresentation?
    {World : Type u} {Agent : Type u}
    (claim : StructuredEthicalClaim World Agent) :
    Option (StructuredEthicalPresentation World) :=
  match claim.content, claim.presentation with
  | .propositional φ, .deontic tag =>
      some (.deontological (.atom (.inl { tag := tag, formula := φ })))
  | .propositional φ, .axiological tag =>
      some (.axiological (.atom (.inl { tag := tag, formula := φ })))
  | .propositional φ, .unmodalized =>
      some (.axiological (.atom (.inr φ)))
  | _, _ => none

/-- Primary structured lowering into WM queries. -/
def StructuredEthicalClaim.toQuery
    {World : Type u} {Agent : Type u} {Atom : Type*}
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (claim : StructuredEthicalClaim World Agent) : ConstraintQuery Atom :=
  match claim.content with
  | .propositional φ =>
      enc.propositionalQuery claim.subject claim.presentation claim.ground claim.role φ
  | .relational a b r =>
      enc.relationalQuery claim.subject a b claim.ground claim.role r
  | .dispositional a =>
      enc.dispositionalQuery claim.subject a claim.ground claim.role

/-- Structured support on a region. -/
def StructuredEthicalClaim.supportedOn
    {World : Type u} {Agent : Type u} {Atom : Type*}
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (Γ : Region Atom)
    (claim : StructuredEthicalClaim World Agent) : Prop :=
  ∀ p ∈ claim.toQuery enc, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ

theorem StructuredEthicalClaim.toQuery_supported
    {World : Type u} {Agent : Type u} {Atom : Type*}
    (enc : StructuredEthicsQueryEncoder World Agent Atom)
    (Γ : Region Atom)
    (claim : StructuredEthicalClaim World Agent)
    (hsupp : claim.supportedOn enc Γ) :
    ∀ p ∈ claim.toQuery enc, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ :=
  hsupp

/-- Lift the legacy anchor encoder into the structured lowering interface via a
label-selection policy.  This supports staged migration without making the
legacy layer the primary source language. -/
def StructuredEthicsQueryEncoder.ofLegacy
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (labeler : StructuredClaimLabeler World Agent Label)
    (enc : EthicsQueryEncoder Agent Label Atom) :
    StructuredEthicsQueryEncoder World Agent Atom where
  propositionalQuery := fun subject presentation ground role φ =>
    let claim : StructuredEthicalClaim World Agent :=
      { subject := subject
        content := .propositional φ
        presentation := presentation
        ground := ground
        role := role }
    claim.toLegacyAnchor (labeler.label claim) |>.toQuery enc
  relationalQuery := fun subject a b ground role r =>
    let claim : StructuredEthicalClaim World Agent :=
      { subject := subject
        content := .relational a b r
        presentation := .unmodalized
        ground := ground
        role := role }
    claim.toLegacyAnchor (labeler.label claim) |>.toQuery enc
  dispositionalQuery := fun subject a ground role =>
    let claim : StructuredEthicalClaim World Agent :=
      { subject := subject
        content := .dispositional a
        presentation := .unmodalized
        ground := ground
        role := role }
    claim.toLegacyAnchor (labeler.label claim) |>.toQuery enc

@[simp] theorem StructuredEthicalClaim.toQuery_ofLegacy
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (labeler : StructuredClaimLabeler World Agent Label)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (claim : StructuredEthicalClaim World Agent) :
    claim.toQuery (StructuredEthicsQueryEncoder.ofLegacy labeler enc) =
      (claim.toLegacyAnchor (labeler.label claim)).toQuery enc := by
  cases claim with
  | mk subject content presentation ground role =>
      cases content <;> rfl

/-- If the legacy labeler preserves labels across the FOET deontic/value
translation and the legacy encoder respects the same alignment, then the
structured WM lowering agrees on the two presentations. -/
theorem StructuredEthicalClaim.propositional_deontic_toAxiological_toQuery_ofLegacy_eq_of_aligned
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (labeler : StructuredClaimLabeler World Agent Label)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (hEncAlign : enc.DeonticValueAligned)
    (hLabelAlign : labeler.DeonticValueAligned)
    (subject : Agent) (ground : EthicalGround Agent) (role : EthicalRole)
    (tag : DeonticAttribute) (φ : Formula World) :
    ({ subject := subject
       content := .propositional φ
       presentation := .deontic tag
       ground := ground
       role := role } : StructuredEthicalClaim World Agent).toQuery
        (StructuredEthicsQueryEncoder.ofLegacy labeler enc) =
      ({ subject := subject
         content := .propositional φ
         presentation := .axiological (deonticToMoralValue tag)
         ground := ground
         role := role } : StructuredEthicalClaim World Agent).toQuery
        (StructuredEthicsQueryEncoder.ofLegacy labeler enc) := by
  let dClaim : StructuredEthicalClaim World Agent :=
    { subject := subject
      content := .propositional φ
      presentation := .deontic tag
      ground := ground
      role := role }
  let vClaim : StructuredEthicalClaim World Agent :=
    { subject := subject
      content := .propositional φ
      presentation := .axiological (deonticToMoralValue tag)
      ground := ground
      role := role }
  have hLabel : labeler.label dClaim = labeler.label vClaim :=
    hLabelAlign subject ground role tag φ
  have hAtom :
      enc.deonticAtom subject tag (labeler.label vClaim) =
        enc.moralValueAtom subject (deonticToMoralValue tag) (labeler.label vClaim) :=
    hEncAlign subject tag (labeler.label vClaim)
  simpa [dClaim, vClaim, StructuredEthicalClaim.toQuery_ofLegacy,
    StructuredEthicalClaim.toLegacyAnchor, EthicalAnchor.toQuery, hLabel] using
    congrArg (fun a => ([⟨a, true⟩] : ConstraintQuery Atom)) hAtom

-- Note: `toLegacyUpperShard` conversion is intentionally omitted to avoid
-- placeholder formulas.  Downstream code should migrate to
-- `StructuredEthicalClaim` directly or use `toLegacyAnchor` for WM lowering.

-- ═══════════════════════════════════════════════════════════════════════════
-- Legacy types (retained for backward compatibility)
-- ═══════════════════════════════════════════════════════════════════════════

/-- Care/disposition layer: how an agent is ethically oriented, not yet a
normative proposition about the world. -/
inductive EthicalDisposition (Agent : Type u) where
  | epistemicUniversalLove : Agent → EthicalDisposition Agent

/-- Present a disposition as a structured dispositional claim. -/
def EthicalDisposition.toStructuredClaim
    {World : Type u} {Agent : Type u}
    (d : EthicalDisposition Agent)
    (role : EthicalRole := .standingDisposition)
    (ground : EthicalGround Agent := .asserted)
    : StructuredEthicalClaim World Agent :=
  match d with
  | .epistemicUniversalLove a =>
      { subject := a
        content := .dispositional a
        presentation := .unmodalized
        ground := ground
        role := role }

/-- A structured Gewirth claim: a named right-to-non-interference witness for a
particular purposeful agent in a particular context. -/
structure LabeledGewirthRightClaim (Label : Type w) (I : PGCInterpretation) where
  context : I.Ctx
  agent : I.Entity
  label : Label

/-- Turn a Gewirth right claim into a deontic sentence over the paired
context/world semantics used by the PGC bridge. -/
def LabeledGewirthRightClaim.toDeonticSentence
    {Label : Type w} {I : PGCInterpretation}
    (claim : LabeledGewirthRightClaim Label I) :
    LabeledDeonticSentence (I.Ctx × I.World) I.Entity Label where
  agent := claim.agent
  label := claim.label
  sentence :=
    { tag := .Obligation
      formula := WorldEmbedding.ofMeaning (NonInterference I.InterferesWith claim.agent I.FWB) }

/-- Normative claims separate claims that are merely *presented* in a certain
logical form from claims that are *grounded* in a named source such as a
universal duty or the Gewirth PGC. -/
inductive NormativeClaim :
    (World : Type u) → (Agent : Type u) → (Label : Type w) → Type (max (u + 2) (w + 2)) where
  | presentedValue {World : Type u} {Agent : Type u} {Label : Type w} :
      LabeledValueJudgmentSentence World Agent Label →
        NormativeClaim World Agent Label
  | presentedDeontic {World : Type u} {Agent : Type u} {Label : Type w} :
      LabeledDeonticSentence World Agent Label →
        NormativeClaim World Agent Label
  | groundedUniversalDuty {World : Type u} {Agent : Type u} {Label : Type w} :
      Agent → UniversalDuty → NormativeClaim World Agent Label
  | groundedGewirthRight {Label : Type w} {I : PGCInterpretation} :
      LabeledGewirthRightClaim Label I →
        NormativeClaim (I.Ctx × I.World) I.Entity Label

/-- Relational claims are dyadic/value-typed and should not be confused with
propositional or deontic presentations. -/
structure RelationalClaim (Agent : Type u) where
  source : Agent
  target : Agent
  relation : RelationalValueType

/-- Present a typed relation as a structured relational claim. -/
def RelationalClaim.toStructuredClaim
    {World : Type u} {Agent : Type u}
    (r : RelationalClaim Agent)
    (role : EthicalRole)
    (ground : EthicalGround Agent := .asserted)
    : StructuredEthicalClaim World Agent where
  subject := r.source
  content := .relational r.source r.target r.relation
  presentation := .unmodalized
  ground := ground
  role := role

/-- Upper-shard ethical claims first separate into ontological categories:

- `disposition` for enduring care-style orientations,
- `normative` for evaluative/deontic claims and their principled grounds,
- `relational` for typed dyadic ethical relations.

This avoids treating logical form, ethical ground, and relational arity as if
they were peers in one flat sum. -/
inductive UpperShardEthicalClaim (World : Type u) (Agent : Type u) (Label : Type w) where
  | disposition : EthicalDisposition Agent → UpperShardEthicalClaim World Agent Label
  | normative : NormativeClaim World Agent Label → UpperShardEthicalClaim World Agent Label
  | relational : RelationalClaim Agent → UpperShardEthicalClaim World Agent Label

/-- Lower a normative claim to the thinner anchor layer only at the WM
boundary. -/
def NormativeClaim.toAnchor
    {World : Type u} {Agent : Type u} {Label : Type w}
    (claim : NormativeClaim World Agent Label) :
    EthicalAnchor Agent Label :=
  match claim with
  | .presentedValue s => s.toAnchor
  | .presentedDeontic s => s.toAnchor
  | .groundedUniversalDuty a d => .universalDuty a d
  | .groundedGewirthRight claim => claim.toDeonticSentence.toAnchor

/-- Compile a normative claim to a singleton WM query. -/
def NormativeClaim.toQuery
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (claim : NormativeClaim World Agent Label) : ConstraintQuery Atom :=
  claim.toAnchor.toQuery enc

/-- Support on a region for a normative claim. -/
def NormativeClaim.supportedOn
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (Γ : Region Atom)
    (claim : NormativeClaim World Agent Label) : Prop :=
  claim.toAnchor.supportedOn enc Γ

theorem NormativeClaim.toQuery_supported
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*} [DecidableEq Atom]
    (enc : EthicsQueryEncoder Agent Label Atom)
    (Γ : Region Atom)
    (claim : NormativeClaim World Agent Label)
    (hsupp : claim.supportedOn enc Γ) :
    ∀ p ∈ claim.toQuery enc, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ := by
  exact EthicalAnchor.toQuery_supported enc Γ claim.toAnchor hsupp

/-- When the encoder respects the FOET deontic/value alignment, the WM query
compiled from a presented deontic claim agrees with the query compiled from
its value-judgment translation. -/
theorem NormativeClaim.presented_deontic_toValue_toQuery_eq_of_aligned
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (hAlign : enc.DeonticValueAligned)
    (s : LabeledDeonticSentence World Agent Label) :
    (NormativeClaim.presentedDeontic s).toQuery enc =
      (NormativeClaim.presentedValue s.toValue).toQuery enc := by
  simpa [NormativeClaim.toQuery, NormativeClaim.toAnchor] using
    LabeledDeonticSentence.toQuery_toValue_eq_of_aligned enc hAlign s

/-- Lower a structured upper-shard claim to the thinner anchor layer only at
the WM boundary. -/
def UpperShardEthicalClaim.toAnchor
    {World : Type u} {Agent : Type u} {Label : Type w}
    (claim : UpperShardEthicalClaim World Agent Label) :
    EthicalAnchor Agent Label :=
  match claim with
  | .disposition (.epistemicUniversalLove a) => .epistemicUniversalLove a
  | .normative n => n.toAnchor
  | .relational r => .relational r.source r.target r.relation

/-- Compile an upper-shard claim to a singleton WM query. -/
def UpperShardEthicalClaim.toQuery
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (claim : UpperShardEthicalClaim World Agent Label) : ConstraintQuery Atom :=
  claim.toAnchor.toQuery enc

/-- Support on a region for an upper-shard claim. -/
def UpperShardEthicalClaim.supportedOn
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (Γ : Region Atom)
    (claim : UpperShardEthicalClaim World Agent Label) : Prop :=
  claim.toAnchor.supportedOn enc Γ

theorem UpperShardEthicalClaim.toQuery_supported
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*} [DecidableEq Atom]
    (enc : EthicsQueryEncoder Agent Label Atom)
    (Γ : Region Atom)
    (claim : UpperShardEthicalClaim World Agent Label)
    (hsupp : claim.supportedOn enc Γ) :
    ∀ p ∈ claim.toQuery enc, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ := by
  exact EthicalAnchor.toQuery_supported enc Γ claim.toAnchor hsupp

/-- When the encoder respects the FOET deontic/value alignment, the WM query
compiled from a structured deontic claim agrees with the query compiled from
its value-judgment translation. -/
theorem UpperShardEthicalClaim.deontic_toValue_toQuery_eq_of_aligned
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (hAlign : enc.DeonticValueAligned)
    (s : LabeledDeonticSentence World Agent Label) :
    (UpperShardEthicalClaim.normative (.presentedDeontic s)).toQuery enc =
      (UpperShardEthicalClaim.normative (.presentedValue s.toValue)).toQuery enc := by
  simpa [UpperShardEthicalClaim.toQuery, UpperShardEthicalClaim.toAnchor] using
    NormativeClaim.presented_deontic_toValue_toQuery_eq_of_aligned enc hAlign s

/-- The Gewirth right claim can be lowered into the general upper-shard layer
as a deontic sentence while preserving its provenance in the source type. -/
def LabeledGewirthRightClaim.toUpperShard
    {Label : Type w} {I : PGCInterpretation}
    (claim : LabeledGewirthRightClaim Label I) :
    UpperShardEthicalClaim (I.Ctx × I.World) I.Entity Label :=
  .normative (.groundedGewirthRight claim)

/-- The same Gewirth witness can also be extracted directly into the
four-axis kernel.  The PGC assumptions and PPA witness are REQUIRED — you
cannot claim Gewirth grounding without providing the proof. -/
def LabeledGewirthRightClaim.toStructuredClaim
    {Label : Type w} {I : PGCInterpretation}
    (claim : LabeledGewirthRightClaim Label I)
    (role : EthicalRole := .activeGoal) :
    StructuredEthicalClaim (I.Ctx × I.World) I.Entity :=
  LabeledDeonticSentence.toStructuredClaim claim.toDeonticSentence role .gewirthPGC

/-- The ground of a Gewirth-derived structured claim is genuinely witnessed
when PGC assumptions and PPA are provided. -/
theorem LabeledGewirthRightClaim.toStructuredClaim_ground_witnessed₀
    {Label : Type w} {I : PGCInterpretation.{0}}
    (claim : LabeledGewirthRightClaim Label I)
    (assumptions : PGCAssumptions I)
    (hPPA : PPA I.ActsOnPurpose claim.agent claim.context (I.worldOf claim.context))
    (role : EthicalRole := .activeGoal) :
    (claim.toStructuredClaim role).ground.Witnessed₀ :=
  EthicalGround.witnessed₀_gewirthPGC_of I assumptions claim.agent claim.context hPPA

/-- The PGC theorem yields satisfaction of the deontic sentence associated with
a structured Gewirth right claim. -/
theorem LabeledGewirthRightClaim.sat_toDeonticSentence_of_PPA
    {Label : Type w} {I : PGCInterpretation}
    (h : PGCAssumptions I)
    (claim : LabeledGewirthRightClaim Label I)
    (hPPA : PPA I.ActsOnPurpose claim.agent claim.context (I.worldOf claim.context)) :
    DeonticSemantics.sat
      (deonticSemanticsOfGewirthOi (Ctx := I.Ctx) I.ob I.pv)
      (claim.context, I.worldOf claim.context)
      claim.toDeonticSentence.sentence := by
  simpa [LabeledGewirthRightClaim.toDeonticSentence, DeonticSemantics.sat] using
    PGC_strong_implies_obligation_nonInterference I h claim.context claim.agent hPPA

/-- Extract a normative claim directly into the four-axis kernel. -/
def NormativeClaim.toStructuredClaim
    {World : Type u} {Agent : Type u} {Label : Type w}
    (dutyContent : Agent → UniversalDuty → Formula World)
    (role : EthicalRole)
    (claim : NormativeClaim World Agent Label) :
    StructuredEthicalClaim World Agent :=
  match claim with
  | .presentedValue s =>
      LabeledValueJudgmentSentence.toStructuredClaim s role .asserted
  | .presentedDeontic s =>
      LabeledDeonticSentence.toStructuredClaim s role .asserted
  | .groundedUniversalDuty a d =>
      { subject := a
        content := .propositional (dutyContent a d)
        presentation := .deontic .Obligation
        ground := .universalDuty d
        role := role }
  | .groundedGewirthRight claim =>
      claim.toStructuredClaim role

/-- Extract any legacy upper-shard claim into the four-axis kernel once a role
is supplied for the legacy cases that did not record it. -/
def UpperShardEthicalClaim.toStructuredClaim
    {World : Type u} {Agent : Type u} {Label : Type w}
    (dutyContent : Agent → UniversalDuty → Formula World)
    (role : EthicalRole)
    (claim : UpperShardEthicalClaim World Agent Label) :
    StructuredEthicalClaim World Agent :=
  match claim with
  | .disposition d => EthicalDisposition.toStructuredClaim d role
  | .normative n => n.toStructuredClaim dutyContent role
  | .relational r => RelationalClaim.toStructuredClaim r role

/-- Four distinguished upper-shard claims matching the protected ethics family.
This preserves ontological structure up to the WM boundary. -/
structure ProtectedUpperShardClaims (World : Type u) (Agent : Type u) (Label : Type w) where
  epistemicUniversalLove : UpperShardEthicalClaim World Agent Label
  nonMaleficence : UpperShardEthicalClaim World Agent Label
  consent : UpperShardEthicalClaim World Agent Label
  reciprocity : UpperShardEthicalClaim World Agent Label

/-- Forget the richer structure and recover the lower-level anchors. -/
def ProtectedUpperShardClaims.toProtectedEthicsAnchors
    {World : Type u} {Agent : Type u} {Label : Type w}
    (claims : ProtectedUpperShardClaims World Agent Label) :
    ProtectedEthicsAnchors Agent Label where
  epistemicUniversalLove := claims.epistemicUniversalLove.toAnchor
  nonMaleficence := claims.nonMaleficence.toAnchor
  consent := claims.consent.toAnchor
  reciprocity := claims.reciprocity.toAnchor

/-- Compile a structured protected upper-shard family into the proved protected
WM query family. -/
def ProtectedUpperShardClaims.toProtectedEthicsQueryFamily
    {World : Type u} {Agent : Type u} {Label : Type w} {Atom : Type*} [DecidableEq Atom]
    {Γ : Region Atom}
    (claims : ProtectedUpperShardClaims World Agent Label)
    (enc : EthicsQueryEncoder Agent Label Atom)
    (hEUL : claims.epistemicUniversalLove.supportedOn enc Γ)
    (hNoHarm : claims.nonMaleficence.supportedOn enc Γ)
    (hConsent : claims.consent.supportedOn enc Γ)
    (hReciprocity : claims.reciprocity.supportedOn enc Γ) :
    ProtectedEthicsQueryFamily Γ :=
  claims.toProtectedEthicsAnchors.toProtectedEthicsQueryFamily enc
    hEUL hNoHarm hConsent hReciprocity

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.Ontology
