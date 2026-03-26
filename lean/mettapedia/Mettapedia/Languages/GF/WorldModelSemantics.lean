import Mettapedia.Languages.GF.HandCrafted.Core
import Mettapedia.Languages.GF.HandCrafted.Abstract
import Mettapedia.Languages.GF.OSLFBridge_handcrafted
import Mettapedia.Languages.GF.Typing
import Mettapedia.Languages.GF.LinguisticInvariance
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Logic.OSLFEvidenceSemantics
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.OSLF.QuantifiedFormula

/-!
# BinaryEvidence-Grounded Semantics for GF via World Models

This module bridges GF abstract syntax trees to evidence-valued denotations
via the PLN world-model interface.  The key construction:

  ⟦t⟧_W := BinaryWorldModel.evidence W (queryOfAtom a (gfAbstractToPattern t))

World-model states W replace possible worlds; BinaryEvidence values (n⁺, n⁻)
replace truth values.  OSLF modalities (◇, □) still run over the rewrite
graph, but atom meaning comes from evidence extraction.

## Design choices

- **Query type**: `Query = Pattern` (patterns are the queries)
- **Atom encoding**: `queryOfAtom : String → Pattern → Pattern` tags patterns
  with atom names, so different atoms at the same pattern get distinct queries
- **Atom interpretation**: Prop-threshold on `BinaryEvidence.toStrength`

## Assumptions

1. Query extraction totality: `queryOfAtom` is total on all atom-pattern pairs
2. Threshold monotonicity: lower threshold → more atoms satisfied (proved)
3. Query encoding: atom names are incorporated into the query pattern
-/

namespace Mettapedia.Languages.GF.WorldModelSemantics

open Mettapedia.Languages.GF.HandCrafted.Core
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.Typing
open Mettapedia.Languages.GF.LinguisticInvariance
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Logic.OSLFEvidenceSemantics

open scoped ENNReal

/-! ## 0. Canonical Semantics Interface

The `GFSemantics` record bundles the four components of the GF → OSLF → BinaryEvidence
pipeline into a single frozen interface:

1. **Atom-query encoding**: how atom names and patterns become WM queries
2. **Language definition**: the OSLF reduction relation source
3. **Threshold policy**: how BinaryEvidence projects to Prop (via threshAtomSem)
4. **Checker contract**: soundness of checkLangUsing w.r.t. sem/semE

All derived operations (semE, sem, checker soundness, evidence bounds) are
methods on GFSemantics, eliminating parameter threading.

**Design principle** (Stay/Baez/Knuth/Meredith compatible):
`semE` is primary, Boolean truth is a projection/view via thresholding. -/

/-- Canonical GF → OSLF → BinaryEvidence semantics configuration.
    Bundles atom-query encoding and language definition.  All derived
    semantics (semE, sem, checker soundness) flow from this record. -/
structure GFSemantics where
  /-- How to encode an atom name and a pattern into a tagged query pattern.
      Different atoms at the same pattern produce different queries. -/
  atomQuery : String → Pattern → Pattern
  /-- The OSLF language definition providing the reduction relation. -/
  lang : LanguageDef
  /-- Injectivity: different atom names produce different queries. -/
  atomQuery_injective : ∀ a₁ a₂ p, a₁ ≠ a₂ → atomQuery a₁ p ≠ atomQuery a₂ p

namespace GFSemantics

variable {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]

/-- The reduction relation induced by this configuration's language. -/
def reduces (cfg : GFSemantics) : Pattern → Pattern → Prop :=
  langReduces cfg.lang

/-- BinaryEvidence-valued atom semantics from a world-model state. -/
noncomputable def evidenceAtomSem (cfg : GFSemantics) (W : State) : EvidenceAtomSem :=
  wmEvidenceAtomSem W cfg.atomQuery

/-- Full evidence-valued formula semantics (PRIMARY layer).
    Maps formulas to BinaryEvidence via the Frame structure (⊓ ∧, ⊔ ∨, ⇨ →, ⨆ ◇, ⨅ □). -/
noncomputable def formulaSemE (cfg : GFSemantics) (W : State)
    (φ : OSLFFormula) (p : Pattern) : BinaryEvidence :=
  semE cfg.reduces (cfg.evidenceAtomSem W) φ p

/-- Threshold-Prop atom semantics (DERIVED from evidence layer). -/
noncomputable def thresholdAtomSem (cfg : GFSemantics) (W : State)
    (τ : BinaryEvidence) : AtomSem :=
  threshAtomSem (cfg.evidenceAtomSem W) τ

/-- Full Prop-valued formula semantics (DERIVED via threshold projection). -/
noncomputable def formulaSem (cfg : GFSemantics) (W : State)
    (τ : BinaryEvidence) (φ : OSLFFormula) (p : Pattern) : Prop :=
  sem cfg.reduces (cfg.thresholdAtomSem W τ) φ p

/-- Checker soundness contract: if checkLangUsing returns .sat with a sound
    atom checker, then the Prop-level formula semantics holds.
    This is the master bridge from executable checker to denotational semantics. -/
theorem checkerSoundness (cfg : GFSemantics)
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : checkLangUsing .empty cfg.lang I_check fuel p φ = .sat) :
    sem cfg.reduces I_sem φ p :=
  checkLangUsing_sat_sound h_atoms h

/-- BinaryEvidence bound contract: for imp-free formulas, checker .sat implies
    τ ≤ semE. No totality or finite-branching assumptions needed. -/
theorem evidenceBound (cfg : GFSemantics)
    {W : State} {τ : BinaryEvidence}
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true →
      threshAtomSem (cfg.evidenceAtomSem W) τ a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hImpFree : impFree φ)
    (hSat : checkLangUsing .empty cfg.lang I_check fuel p φ = .sat) :
    τ ≤ cfg.formulaSemE W φ p :=
  threshold_reverse_impFree _ τ _ φ hImpFree p
    (checkLangUsing_sat_sound h_atoms hSat)

end GFSemantics

/-! ## 1. Atom-Query Encoder

The encoder maps (atom name, pattern) pairs to Pattern queries.
Different atoms at the same pattern produce different queries,
so the world model can assign different evidence to each. -/

/-- Encode an atom name and a pattern into a query pattern.
The atom name is incorporated as a tag so that different atoms
at the same pattern produce different queries. -/
def queryOfAtom (atomName : String) (p : Pattern) : Pattern :=
  .apply ("atom:" ++ atomName) [p]

/-- Different atom names produce different queries at the same pattern. -/
theorem queryOfAtom_injective_name (a₁ a₂ : String) (p : Pattern)
    (h : a₁ ≠ a₂) : queryOfAtom a₁ p ≠ queryOfAtom a₂ p := by
  unfold queryOfAtom
  intro heq
  injection heq with h1 _
  simp [String.ext_iff] at h1
  exact h (String.ext h1)

/-! ## 7. Garden-Path Query Distinction

Two structurally different parses produce different query patterns.
(Placed before the section so these concrete defs don't inherit section variables.) -/

/-- Garden-path parse 1: "The old man walks" (adjective reading). -/
private def gpParse1 : AbstractNode := mkApp2 "PredVP" "NP" "VP" "Cl"
  (mkApp2 "DetCN" "Det" "CN" "NP"
    (mkLeaf "the_Det" "Det")
    (mkApp2 "AdjCN" "AP" "CN" "CN"
      (mkApp1 "PositA" "A" "AP" (mkLeaf "old" "A"))
      (mkApp1 "UseN" "N" "CN" (mkLeaf "man" "N"))))
  (mkApp1 "UseV" "V" "VP" (mkLeaf "walk" "V"))

/-- Garden-path parse 2: "The old mans the boat" (verb reading). -/
private def gpParse2 : AbstractNode := mkApp2 "PredVP" "NP" "VP" "Cl"
  (mkApp2 "DetCN" "Det" "CN" "NP"
    (mkLeaf "the_Det" "Det")
    (mkApp1 "UseN" "N" "CN" (mkLeaf "old" "N")))
  (mkApp2 "ComplSlash" "VPSlash" "NP" "VP"
    (mkApp1 "SlashV2a" "V2" "VPSlash" (mkLeaf "man" "V2"))
    (mkApp2 "DetCN" "Det" "CN" "NP"
      (mkLeaf "the_Det" "Det")
      (mkApp1 "UseN" "N" "CN" (mkLeaf "boat" "N"))))

/-- The two garden-path parses produce different OSLF patterns. -/
theorem garden_path_queries_differ :
    gfAbstractToPattern gpParse1 ≠ gfAbstractToPattern gpParse2 := by
  simp [gpParse1, gpParse2, mkApp2, mkApp1, mkLeaf, List.map]

section GFSemantics

variable {State : Type*} [EvidenceType State] [BinaryWorldModel State Pattern]

/-! ## 2. Core Definitions -/

/-- BinaryEvidence-valued denotation of a GF abstract tree in world-model state W.

`⟦t⟧_W = evidence(W, gfAbstractToPattern(t))`. -/
noncomputable def gfEvidenceDenote (W : State) (t : AbstractNode) : BinaryEvidence :=
  BinaryWorldModel.evidence W (gfAbstractToPattern t)

/-- Threshold-based atom semantics grounded in a world-model state.

An atom `a` holds at pattern `p` iff
`toStrength(evidence W (queryOfAtom a p)) ≥ threshold`.
The atom name is part of the query, so different atoms can have
different evidence. -/
noncomputable def gfAtomSemFromWM (W : State) (threshold : ℝ≥0∞) : AtomSem :=
  fun atomName p =>
    threshold ≤ BinaryEvidence.toStrength (BinaryWorldModel.evidence W (queryOfAtom atomName p))

/-- Full OSLF formula semantics grounded in a world-model state.

Uses `langReduces gfRGLLanguageDef` (= `langReducesUsing .empty gfRGLLanguageDef`)
as the reduction relation, matching `checkLangUsing_sat_sound`. -/
noncomputable def gfWMFormulaSem
    (W : State) (threshold : ℝ≥0∞)
    (φ : OSLFFormula) (p : Pattern) : Prop :=
  sem (langReduces gfRGLLanguageDef) (gfAtomSemFromWM W threshold) φ p

/-! ## 3. Checker Soundness → WM Semantics

The existing `checkLangUsing_sat_sound` bridges the bounded model checker
to denotational semantics.  We instantiate it with WM-grounded atoms. -/

/-- If the OSLF checker returns `.sat` with an atom checker sound w.r.t.
the WM-grounded atom semantics, then the formula holds in the WM-grounded
denotational semantics.

This is the central soundness bridge: it connects the executable checker
to the evidence-valued semantic layer. -/
theorem oslf_sat_implies_wm_semantics
    (W : State) (threshold : ℝ≥0∞)
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true →
      (gfAtomSemFromWM W threshold) a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : checkLangUsing .empty gfRGLLanguageDef I_check fuel p φ = .sat) :
    gfWMFormulaSem W threshold φ p :=
  checkLangUsing_sat_sound h_atoms h

/-! ## 4. BinaryEvidence Revision Preserves Denotation

BinaryEvidence extraction commutes with revision (`+`) in the world-model state.
This is the key structural property: combining evidence sources is coherent
with denotation. -/

/-- Revising two world-model states and then extracting evidence for a GF tree
equals extracting evidence from each and combining via hplus. -/
theorem evidence_denote_revision (W₁ W₂ : State) (t : AbstractNode) :
    gfEvidenceDenote (W₁ + W₂) t =
      gfEvidenceDenote W₁ t + gfEvidenceDenote W₂ t := by
  simp only [gfEvidenceDenote]
  exact BinaryWorldModel.evidence_add W₁ W₂ (gfAbstractToPattern t)

/-! ## 5. Threshold Antitonicity

Lowering the threshold makes more atoms satisfied.  This is a genuine
structural theorem about the atom interpretation layer. -/

/-- If the WM atom semantics holds at threshold τ₂, it also holds at
any lower threshold τ₁ ≤ τ₂. -/
theorem atom_threshold_antitone
    (W : State) (τ₁ τ₂ : ℝ≥0∞) (h_le : τ₁ ≤ τ₂)
    (a : String) (p : Pattern)
    (h_sat : (gfAtomSemFromWM W τ₂) a p) :
    (gfAtomSemFromWM W τ₁) a p :=
  le_trans h_le h_sat

/-- Threshold antitonicity lifts to atom checker soundness:
if all checked atoms hold at τ₂, they hold at τ₁ ≤ τ₂. -/
theorem atom_check_threshold_antitone
    (W : State) (τ₁ τ₂ : ℝ≥0∞) (h_le : τ₁ ≤ τ₂)
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true →
      (gfAtomSemFromWM W τ₂) a p) :
    ∀ a p, I_check a p = true →
      (gfAtomSemFromWM W τ₁) a p :=
  fun a p hc => atom_threshold_antitone W τ₁ τ₂ h_le a p (h_atoms a p hc)

/-! ## 6. WM Query Judgment Bridge

From a WM judgment (derivable posterior state) to evidence extraction on
GF abstract trees.  This connects the PLN inference calculus to GF semantics. -/

/-- A derivable world-model state yields a well-formed query judgment
for any GF abstract tree. -/
theorem gf_wm_query_judgment
    (W : State) (t : AbstractNode) (hW : WMJudgment W) :
    WMQueryJudgment W (gfAbstractToPattern t) (gfEvidenceDenote W t) :=
  ⟨hW, rfl⟩

/-- Combining two derivable states yields a derivable query judgment
with combined evidence (via `evidence_add`). -/
theorem gf_wm_query_revise
    {W₁ W₂ : State} (t : AbstractNode)
    (h₁ : WMQueryJudgment W₁
      (gfAbstractToPattern t) (gfEvidenceDenote W₁ t))
    (h₂ : WMQueryJudgment W₂
      (gfAbstractToPattern t) (gfEvidenceDenote W₂ t)) :
    WMQueryJudgment (W₁ + W₂)
      (gfAbstractToPattern t)
      (gfEvidenceDenote W₁ t + gfEvidenceDenote W₂ t) :=
  WMJudgment.query_revise h₁ h₂

/-- Different patterns → different evidence in any discriminating world model.
Combined with `garden_path_queries_differ`, this shows the two parses
can be semantically distinguished by evidence. -/
theorem garden_path_evidence_separable
    (W : State)
    (h_disc : BinaryWorldModel.evidence W (gfAbstractToPattern gpParse1) ≠
              BinaryWorldModel.evidence W (gfAbstractToPattern gpParse2)) :
    gfEvidenceDenote W gpParse1 ≠ gfEvidenceDenote W gpParse2 :=
  h_disc

/-! ## 8. Lexical Containment Monotonicity

Delegates to proved lexical monotonicity theorems.  In the evidence domain:
if a lexical item is query-accessible in a pattern, it remains accessible
after modification. -/

/-- Adjective modification preserves lexical containment. -/
theorem wm_lexical_containment_monotone
    (adjName : String) (cn : AbstractNode) (name : String)
    (h : containsLexical name (gfAbstractToPattern cn) = true) :
    containsLexical name (gfAbstractToPattern (addAdjModifier adjName cn)) = true :=
  adjModification_preserves_lexical adjName cn name h

/-- Modification adds the adjective as new lexical content. -/
theorem wm_adjective_adds_lexical (adjName : String) (cn : AbstractNode) :
    containsLexical adjName (gfAbstractToPattern (addAdjModifier adjName cn)) = true :=
  adjModification_adds_adjective adjName cn

/-! ## 9. BinaryEvidence-Valued GF Semantics (Primary Layer)

The threshold-Prop semantics above (`gfWMFormulaSem`) is a derived view.
The PRIMARY semantics maps formulas to BinaryEvidence values via `semE` from
`OSLFEvidenceSemantics.lean`, using the Frame structure of BinaryEvidence
(⊓ for ∧, ⊔ for ∨, ⇨ for →, ⨆ for ◇, ⨅ for □). -/

/-- BinaryEvidence-valued atom semantics from a world-model state.
Each atom name and pattern produces an BinaryEvidence value via WM query. -/
noncomputable def gfEvidenceAtomSemFromWM (W : State) : EvidenceAtomSem :=
  wmEvidenceAtomSem W queryOfAtom

/-- Full evidence-valued OSLF formula semantics for GF.

This is the PRIMARY semantic layer: formulas map to BinaryEvidence, not Prop.
The threshold-Prop semantics `gfWMFormulaSem` is a corollary obtained by
thresholding this. -/
noncomputable def gfWMFormulaSemE
    (W : State) (φ : OSLFFormula) (p : Pattern) : BinaryEvidence :=
  semE (langReduces gfRGLLanguageDef) (gfEvidenceAtomSemFromWM W) φ p

/-- The threshold-Prop atom semantics is recovered by thresholding the
evidence-valued atom semantics on `BinaryEvidence.toStrength`. -/
theorem gfAtomSemFromWM_eq_threshold (W : State) (threshold : ℝ≥0∞)
    (a : String) (p : Pattern) :
    gfAtomSemFromWM W threshold a p ↔
      threshold ≤ BinaryEvidence.toStrength (gfEvidenceAtomSemFromWM W a p) := by
  rfl

/-- BinaryEvidence revision lifts to GF evidence atoms:
combining world-model states then extracting = extracting then combining. -/
theorem gfWMFormulaSemE_atom_revision (W₁ W₂ : State) (a : String) (p : Pattern) :
    gfWMFormulaSemE (W₁ + W₂) (.atom a) p =
      gfWMFormulaSemE W₁ (.atom a) p + gfWMFormulaSemE W₂ (.atom a) p := by
  simp only [gfWMFormulaSemE, semE_atom, gfEvidenceAtomSemFromWM, wmEvidenceAtomSem]
  exact BinaryWorldModel.evidence_add W₁ W₂ (queryOfAtom a p)

/-- Conjunction in evidence semantics projects to components. -/
theorem gfWMFormulaSemE_and_le_left (W : State) (φ ψ : OSLFFormula) (p : Pattern) :
    gfWMFormulaSemE W (.and φ ψ) p ≤ gfWMFormulaSemE W φ p := by
  exact semE_and_le_left _ _ _ _ _

/-- Diamond witnesses inject into evidence diamond. -/
theorem gfWMFormulaSemE_dia_le (W : State) (φ : OSLFFormula) (p q : Pattern)
    (h : langReduces gfRGLLanguageDef p q) :
    gfWMFormulaSemE W φ q ≤ gfWMFormulaSemE W (.dia φ) p := by
  exact semE_dia_le _ _ _ _ _ h

/-- GF evidence denote is a direct WM query, while gfEvidenceAtomSemFromWM goes
through the atom-tagged query encoding. They share the same WM extraction
mechanism but on different query patterns. -/
theorem gfEvidenceDenote_as_evidence (W : State) (t : AbstractNode) :
    gfEvidenceDenote W t =
      BinaryWorldModel.evidence W (gfAbstractToPattern t) := by
  rfl

/-! ## 9b. Canonical GFSemantics Instance

The `gfRGLSemantics` record bundles the above scattered definitions into
one frozen interface.  Agreement theorems verify that the record's derived
operations coincide with the existing hand-written definitions. -/

/-- The standard GF RGL semantics configuration.
    Uses `queryOfAtom` for atom-query encoding and `gfRGLLanguageDef`
    for the reduction relation. -/
def gfRGLSemantics : GFSemantics where
  atomQuery := queryOfAtom
  lang := gfRGLLanguageDef
  atomQuery_injective := queryOfAtom_injective_name

/-- Agreement: gfRGLSemantics.reduces = langReduces gfRGLLanguageDef. -/
@[simp] theorem gfRGLSemantics_reduces :
    gfRGLSemantics.reduces = langReduces gfRGLLanguageDef := rfl

/-- Agreement: record atom semantics = hand-written definition. -/
theorem gfRGLSemantics_evidenceAtomSem (W : State) :
    gfRGLSemantics.evidenceAtomSem W = gfEvidenceAtomSemFromWM W := rfl

/-- Agreement: record formula semantics = hand-written definition. -/
theorem gfRGLSemantics_formulaSemE (W : State) (φ : OSLFFormula) (p : Pattern) :
    gfRGLSemantics.formulaSemE W φ p = gfWMFormulaSemE W φ p := rfl

/-- Agreement: record Prop semantics = hand-written definition.
    (threshold expressed as BinaryEvidence via BinaryEvidence.toStrength). -/
theorem gfRGLSemantics_formulaSem (W : State) (τ : BinaryEvidence)
    (φ : OSLFFormula) (p : Pattern) :
    gfRGLSemantics.formulaSem W τ φ p =
      sem (langReduces gfRGLLanguageDef)
        (threshAtomSem (gfEvidenceAtomSemFromWM W) τ) φ p := rfl

/-! ## 10. Constructor Compositionality

### Identity wrappers

Identity-wrapper constructors (UseN, PositA, UseV, UseComp, UseN2, UseA2) have
elimination rewrites in the RGL language: `UseN(x) ⇝ x`.  The generic lemma
`langReduces_identityWrapper` factors the shared proof pattern; concrete
instances follow by instantiation.

The key semantic consequence is **evidence transparency**: evidence of φ at the
inner tree is accessible through the wrapper via ◇.

### Structural constructors

DetCN, PredVP, AdjCN have no rewrites — their evidence is determined by the WM
query on the composite pattern.  The decomposition lemmas are definitional
equalities exposing the query shape; algebraic composition laws over BinaryEvidence
would require additional WM axioms (e.g. subadditivity). -/

open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises
open Mettapedia.OSLF.MeTTaIL.Engine

/-- Generic identity-wrapper reduction: a rewrite rule with pattern
`apply name [fvar v]` ⇝ `fvar v` and no premises induces
`langReduces gfRGLLanguageDef (.apply name [p]) p` for all p. -/
theorem langReduces_identityWrapper
    (rw : RewriteRule) (wrapperName varName : String)
    (hrw : rw ∈ gfRGLLanguageDef.rewrites)
    (hleft : rw.left = .apply wrapperName [.fvar varName])
    (hright : rw.right = .fvar varName)
    (hprem : rw.premises = [])
    (p : Pattern) :
    langReduces gfRGLLanguageDef (.apply wrapperName [p]) p := by
  unfold langReduces langReducesUsing
  exact .topRule rw hrw
    [(varName, p)]
    (by simp [hleft, matchPattern, matchArgs, BEq.beq, List.length,
              mergeBindings, List.filterMap])
    [(varName, p)]
    (by simp [hprem, applyPremisesWithEnv])
    (by simp [hright, applyBindings, List.find?, BEq.beq])

private theorem mem_rewrites (rw : RewriteRule) (h : rw ∈ allIdentityRewrites) :
    rw ∈ gfRGLLanguageDef.rewrites := by
  simp [gfRGLLanguageDef]
  exact Or.inl h

private theorem mem_semantic_rewrites (rw : RewriteRule) (h : rw ∈ allSemanticRewrites) :
    rw ∈ gfRGLLanguageDef.rewrites := by
  simp [gfRGLLanguageDef]
  exact Or.inr h

/-- UseN(p) ⇝ p -/
theorem langReduces_UseN (p : Pattern) :
    langReduces gfRGLLanguageDef (.apply "UseN" [p]) p :=
  langReduces_identityWrapper useNElimRewrite "UseN" "x"
    (mem_rewrites _ (by simp [allIdentityRewrites])) rfl rfl rfl p

/-- PositA(p) ⇝ p -/
theorem langReduces_PositA (p : Pattern) :
    langReduces gfRGLLanguageDef (.apply "PositA" [p]) p :=
  langReduces_identityWrapper positAElimRewrite "PositA" "x"
    (mem_rewrites _ (by simp [allIdentityRewrites])) rfl rfl rfl p

/-- UseV(p) ⇝ p -/
theorem langReduces_UseV (p : Pattern) :
    langReduces gfRGLLanguageDef (.apply "UseV" [p]) p :=
  langReduces_identityWrapper useVElimRewrite "UseV" "x"
    (mem_rewrites _ (by simp [allIdentityRewrites])) rfl rfl rfl p

/-- UseComp(p) ⇝ p -/
theorem langReduces_UseComp (p : Pattern) :
    langReduces gfRGLLanguageDef (.apply "UseComp" [p]) p :=
  langReduces_identityWrapper useCompElimRewrite "UseComp" "x"
    (mem_rewrites _ (by simp [allIdentityRewrites])) rfl rfl rfl p

/-- UseN2(p) ⇝ p -/
theorem langReduces_UseN2 (p : Pattern) :
    langReduces gfRGLLanguageDef (.apply "UseN2" [p]) p :=
  langReduces_identityWrapper useN2ElimRewrite "UseN2" "x"
    (mem_rewrites _ (by simp [allIdentityRewrites])) rfl rfl rfl p

/-- UseA2(p) ⇝ p -/
theorem langReduces_UseA2 (p : Pattern) :
    langReduces gfRGLLanguageDef (.apply "UseA2" [p]) p :=
  langReduces_identityWrapper useA2ElimRewrite "UseA2" "x"
    (mem_rewrites _ (by simp [allIdentityRewrites])) rfl rfl rfl p

/-! ### Active-Passive Reduction

The active clause `PredVP(np₁, ComplSlash(SlashV2a(v), np₂))` — "np₁ verbs np₂" —
reduces to the passive clause `PredVP(np₂, PassV2(v))` — "np₂ is verbed".
This captures the semantic entailment: active → agentless passive. -/

/-- Active → passive reduction at the clause level.
    PredVP(np₁, ComplSlash(SlashV2a(v), np₂)) ⇝ PredVP(np₂, PassV2(v)) -/
theorem langReduces_activePassive (np₁ np₂ v : Pattern) :
    langReduces gfRGLLanguageDef
      (Pattern.apply "PredVP" [np₁,
        Pattern.apply "ComplSlash" [Pattern.apply "SlashV2a" [v], np₂]])
      (Pattern.apply "PredVP" [np₂, Pattern.apply "PassV2" [v]]) := by
  unfold langReduces langReducesUsing
  exact .topRule activePassiveRewrite
    (mem_semantic_rewrites _ (by simp [allSemanticRewrites]))
    [("v", v), ("np2", np₂), ("np1", np₁)]
    (by simp [activePassiveRewrite, matchPattern, matchArgs, BEq.beq, List.length,
              mergeBindings, List.filterMap, List.find?])
    [("v", v), ("np2", np₂), ("np1", np₁)]
    (by simp [activePassiveRewrite, applyPremisesWithEnv])
    (by simp [activePassiveRewrite, applyBindings, List.find?, BEq.beq, List.map])

/-- Active-passive evidence transparency: evidence of φ at the passive clause
    flows through from the active clause via ◇.

    semE R I φ (PredVP(np₂, PassV2(v))) ≤ semE R I (◇φ) (PredVP(np₁, ComplSlash(SlashV2a(v), np₂))) -/
theorem gfWMFormulaSemE_activePassive_transparent
    (W : State) (φ : OSLFFormula) (np₁ np₂ v : AbstractNode) :
    gfWMFormulaSemE W φ
      (gfAbstractToPattern (.apply FunctionSig.PredVP [np₂,
        .apply FunctionSig.PassV2 [v]])) ≤
    gfWMFormulaSemE W (.dia φ)
      (gfAbstractToPattern (.apply FunctionSig.PredVP [np₁,
        .apply FunctionSig.ComplSlash [.apply FunctionSig.SlashV2a [v], np₂]])) := by
  unfold gfWMFormulaSemE
  apply semE_dia_le
  simp [FunctionSig.PredVP, FunctionSig.PassV2, FunctionSig.ComplSlash,
        FunctionSig.SlashV2a, List.map]
  exact langReduces_activePassive
    (gfAbstractToPattern np₁) (gfAbstractToPattern np₂) (gfAbstractToPattern v)

/-- Generic wrapper evidence transparency: for any identity-wrapper constructor,
evidence of φ at the inner tree is accessible through the wrapper via ◇.

`semE R I φ (pattern inner) ≤ semE R I (◇φ) (pattern (f inner))` -/
theorem gfWMFormulaSemE_wrapper_transparent
    (W : State) (φ : OSLFFormula) (f : FunctionSig) (inner : AbstractNode)
    (hReduce : langReduces gfRGLLanguageDef
      (Pattern.apply f.name [gfAbstractToPattern inner])
      (gfAbstractToPattern inner)) :
    gfWMFormulaSemE W φ (gfAbstractToPattern inner) ≤
    gfWMFormulaSemE W (.dia φ) (gfAbstractToPattern (.apply f [inner])) := by
  unfold gfWMFormulaSemE
  apply semE_dia_le
  simp [List.map]
  exact hReduce

/-- UseN transparency. -/
theorem gfWMFormulaSemE_UseN_transparent
    (W : State) (φ : OSLFFormula) (n : AbstractNode) :
    gfWMFormulaSemE W φ (gfAbstractToPattern n) ≤
    gfWMFormulaSemE W (.dia φ) (gfAbstractToPattern (.apply FunctionSig.UseN [n])) :=
  gfWMFormulaSemE_wrapper_transparent W φ _ n
    (by simp [FunctionSig.UseN]; exact langReduces_UseN _)

/-- PositA transparency. -/
theorem gfWMFormulaSemE_PositA_transparent
    (W : State) (φ : OSLFFormula) (a : AbstractNode) :
    gfWMFormulaSemE W φ (gfAbstractToPattern a) ≤
    gfWMFormulaSemE W (.dia φ) (gfAbstractToPattern (.apply FunctionSig.PositA [a])) :=
  gfWMFormulaSemE_wrapper_transparent W φ _ a
    (by simp [FunctionSig.PositA]; exact langReduces_PositA _)

/-- UseV transparency. -/
theorem gfWMFormulaSemE_UseV_transparent
    (W : State) (φ : OSLFFormula) (v : AbstractNode) :
    gfWMFormulaSemE W φ (gfAbstractToPattern v) ≤
    gfWMFormulaSemE W (.dia φ) (gfAbstractToPattern (.apply FunctionSig.UseV [v])) :=
  gfWMFormulaSemE_wrapper_transparent W φ _ v
    (by simp [FunctionSig.UseV]; exact langReduces_UseV _)

/-- UseComp transparency. -/
theorem gfWMFormulaSemE_UseComp_transparent
    (W : State) (φ : OSLFFormula) (c : AbstractNode) :
    gfWMFormulaSemE W φ (gfAbstractToPattern c) ≤
    gfWMFormulaSemE W (.dia φ) (gfAbstractToPattern (.apply FunctionSig.UseComp [c])) :=
  gfWMFormulaSemE_wrapper_transparent W φ _ c
    (by simp [FunctionSig.UseComp]; exact langReduces_UseComp _)

/-- DetCN structural: evidence for DetCN(det, cn) is WM query on composite. -/
theorem gfEvidenceDenote_DetCN (W : State) (det cn : AbstractNode) :
    gfEvidenceDenote W (.apply FunctionSig.DetCN [det, cn]) =
    BinaryWorldModel.evidence W (Pattern.apply "DetCN"
      [gfAbstractToPattern det, gfAbstractToPattern cn]) := by
  simp [gfEvidenceDenote, FunctionSig.DetCN, List.map]

/-- PredVP structural: evidence for PredVP(np, vp) is WM query on composite. -/
theorem gfEvidenceDenote_PredVP (W : State) (np vp : AbstractNode) :
    gfEvidenceDenote W (.apply FunctionSig.PredVP [np, vp]) =
    BinaryWorldModel.evidence W (Pattern.apply "PredVP"
      [gfAbstractToPattern np, gfAbstractToPattern vp]) := by
  simp [gfEvidenceDenote, FunctionSig.PredVP, List.map]

/-- AdjCN structural: evidence for AdjCN(ap, cn) is WM query on composite. -/
theorem gfEvidenceDenote_AdjCN (W : State) (ap cn : AbstractNode) :
    gfEvidenceDenote W (.apply FunctionSig.AdjCN [ap, cn]) =
    BinaryWorldModel.evidence W (Pattern.apply "AdjCN"
      [gfAbstractToPattern ap, gfAbstractToPattern cn]) := by
  simp [gfEvidenceDenote, FunctionSig.AdjCN, List.map]

/-! ## 11. End-to-End Theorem Chain

### Fragment bridge

The checker `.sat` → `sem` (Prop) → `τ ≤ semE` (BinaryEvidence) chain works for the
**implication-free fragment** without any totality or finite-branching
assumptions.  The reverse bridge uses the existential witness in ◇ to provide
the evidence bound directly.

### Concrete client

`useN_house_evidence_bound` demonstrates the full chain on a specific GF tree
`UseN(house)` with formula `◇(is_house)`.

### What this is NOT

This is not full Montague-style denotational semantics: there are no typed
quantifiers, scope mechanisms, or lambda-term denotations.  It IS a behavioral
evidential semantics bridge: GF abstract syntax → OSLF operational semantics →
evidence-valued interpretation. -/

/-- End-to-end: checker `.sat` on an imp-free formula implies evidence lower
bound `τ ≤ semE R I φ p`.

No totality or finite-branching assumptions needed (reverse bridge direction).
The forward bridge `semE → sem` for ∨/◇ requires totality + finite branching
(see `threshold_or_total`, `threshold_dia_total`). -/
theorem checker_sat_implies_evidence_bound
    {I : EvidenceAtomSem} {τ : BinaryEvidence}
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true → threshAtomSem I τ a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hImpFree : impFree φ)
    (hSat : checkLangUsing .empty gfRGLLanguageDef I_check fuel p φ = .sat) :
    τ ≤ semE (langReduces gfRGLLanguageDef) I φ p :=
  threshold_reverse_impFree I τ _ φ hImpFree p
    (checkLangUsing_sat_sound h_atoms hSat)

/-- Concrete end-to-end: UseN(house) |= ◇(is_house) with evidence bound.

For any evidence assignment I with `∀ a, τ ≤ I a (.fvar "house")`,
the checker `.sat` + reverse bridge gives `τ ≤ semE (◇ is_house) (UseN house)`.

Full chain: GF tree → Pattern → checker `.sat` → `sem` → `τ ≤ semE`. -/
theorem useN_house_evidence_bound
    (I : EvidenceAtomSem) (τ : BinaryEvidence)
    (hI : ∀ a, τ ≤ I a (.fvar "house")) :
    τ ≤ semE (langReduces gfRGLLanguageDef) I
      (.dia (.atom "is_house"))
      (gfAbstractToPattern (.apply FunctionSig.UseN [.leaf "house" (.base "N")])) := by
  -- Direct semantic proof via langReduces_UseN (no native_decide needed)
  have hR : langReduces gfRGLLanguageDef
      (gfAbstractToPattern (.apply FunctionSig.UseN [.leaf "house" (.base "N")]))
      (.fvar "house") := by
    simp only [gfAbstractToPattern, List.map, FunctionSig.UseN]
    exact langReduces_UseN _
  calc τ ≤ I "is_house" (.fvar "house") := hI "is_house"
    _ = semE (langReduces gfRGLLanguageDef) I (.atom "is_house") (.fvar "house") := rfl
    _ ≤ semE (langReduces gfRGLLanguageDef) I (.dia (.atom "is_house"))
          (gfAbstractToPattern (.apply FunctionSig.UseN [.leaf "house" (.base "N")])) :=
        semE_dia_le _ _ _ _ _ hR

/-! ## 12. Temporal Tense Bridge

GF tense constructors (`TPast`, `TPres`, `TFut` via `UseCl(TTAnt(...), PPos, cl)`)
reduce to temporally-tagged patterns `⊛temporal(cl, T)` where T encodes the
tense offset (past = -1, present = 0, future = 1).

The temporal evidence semantics from `OSLFEvidenceSemantics.lean` evaluates atoms
at time-shifted WM queries, so different tenses produce different evidence values
in general.

### Positive result (entailment)

Past → present temporal accessibility: a past-tense clause is ◇-accessible from
the present-tense clause via the rewrite chain.

### Negative result (non-entailment)

Present ↛ past: a present-tense clause does NOT reduce to a past-tense clause
(no rewrite rule in that direction), so ◇(past-φ)(present-cl) is not guaranteed.
-/

/-- Past tense reduction: UseCl(TTAnt(TPast, ASimul), PPos, cl) ⇝ ⊛temporal(cl, -1). -/
theorem langReduces_pastTense (cl : Pattern) :
    langReduces gfRGLLanguageDef
      (Pattern.apply "UseCl" [
        Pattern.apply "TTAnt" [Pattern.apply "TPast" [], Pattern.apply "ASimul" []],
        Pattern.apply "PPos" [],
        cl])
      (Pattern.apply "⊛temporal" [cl, Pattern.apply "-1" []]) := by
  unfold langReduces langReducesUsing
  refine .topRule pastTenseRewrite
    (mem_semantic_rewrites _ ?_)
    [("cl", cl)]
    ?_ [("cl", cl)] ?_ ?_
  · simp [allSemanticRewrites, allTenseRewrites]
  · simp [pastTenseRewrite, matchPattern, matchArgs, BEq.beq, List.length,
          mergeBindings, List.filterMap, List.find?]
  · simp [pastTenseRewrite, applyPremisesWithEnv]
  · simp [pastTenseRewrite, applyBindings, List.find?, BEq.beq, List.map]

/-- Present tense reduction: UseCl(TTAnt(TPres, ASimul), PPos, cl) ⇝ ⊛temporal(cl, 0). -/
theorem langReduces_presentTense (cl : Pattern) :
    langReduces gfRGLLanguageDef
      (Pattern.apply "UseCl" [
        Pattern.apply "TTAnt" [Pattern.apply "TPres" [], Pattern.apply "ASimul" []],
        Pattern.apply "PPos" [],
        cl])
      (Pattern.apply "⊛temporal" [cl, Pattern.apply "0" []]) := by
  unfold langReduces langReducesUsing
  refine .topRule presentTenseRewrite
    (mem_semantic_rewrites _ ?_)
    [("cl", cl)]
    ?_ [("cl", cl)] ?_ ?_
  · simp [allSemanticRewrites, allTenseRewrites]
  · simp [presentTenseRewrite, matchPattern, matchArgs, BEq.beq, List.length,
          mergeBindings, List.filterMap, List.find?]
  · simp [presentTenseRewrite, applyPremisesWithEnv]
  · simp [presentTenseRewrite, applyBindings, List.find?, BEq.beq, List.map]

/-- Future tense reduction: UseCl(TTAnt(TFut, ASimul), PPos, cl) ⇝ ⊛temporal(cl, 1). -/
theorem langReduces_futureTense (cl : Pattern) :
    langReduces gfRGLLanguageDef
      (Pattern.apply "UseCl" [
        Pattern.apply "TTAnt" [Pattern.apply "TFut" [], Pattern.apply "ASimul" []],
        Pattern.apply "PPos" [],
        cl])
      (Pattern.apply "⊛temporal" [cl, Pattern.apply "1" []]) := by
  unfold langReduces langReducesUsing
  refine .topRule futureTenseRewrite
    (mem_semantic_rewrites _ ?_)
    [("cl", cl)]
    ?_ [("cl", cl)] ?_ ?_
  · simp [allSemanticRewrites, allTenseRewrites]
  · simp [futureTenseRewrite, matchPattern, matchArgs, BEq.beq, List.length,
          mergeBindings, List.filterMap, List.find?]
  · simp [futureTenseRewrite, applyPremisesWithEnv]
  · simp [futureTenseRewrite, applyBindings, List.find?, BEq.beq, List.map]

/-- **Positive result**: Past-tense evidence is ◇-accessible from the full
    GF sentence.  If φ holds at the past-temporal pattern, then ◇φ holds at
    the full `UseCl(TTAnt(TPast, ASimul), PPos, cl)` sentence pattern.

    This is the temporal analogue of UseN evidence transparency. -/
theorem gfWMFormulaSemE_pastTense_transparent
    (W : State) (φ : OSLFFormula) (cl : Pattern) :
    gfWMFormulaSemE W φ (Pattern.apply "⊛temporal" [cl, Pattern.apply "-1" []]) ≤
    gfWMFormulaSemE W (.dia φ)
      (Pattern.apply "UseCl" [
        Pattern.apply "TTAnt" [Pattern.apply "TPast" [], Pattern.apply "ASimul" []],
        Pattern.apply "PPos" [],
        cl]) := by
  unfold gfWMFormulaSemE
  exact semE_dia_le _ _ _ _ _ (langReduces_pastTense cl)

/-- **Positive result**: Different tenses produce structurally different patterns.
    Past ≠ present (as OSLF patterns). -/
theorem past_present_patterns_differ (cl : Pattern) :
    Pattern.apply "⊛temporal" [cl, Pattern.apply "-1" []] ≠
    Pattern.apply "⊛temporal" [cl, Pattern.apply "0" []] := by
  intro h
  simp at h

/-- Matching an `.apply` pattern against an `.apply` term with a different
    constructor name always fails. -/
private theorem matchPattern_apply_ne_nil {c1 c2 : String} {args1 args2 : List Pattern}
    (hne : c1 ≠ c2) :
    matchPattern (.apply c1 args1) (.apply c2 args2) = [] := by
  simp [matchPattern, hne]

/-- Every rewrite rule in the GF RGL language has a top-level LHS constructor
    that is a standard GF function name (not `"⊛temporal"`).

    The 10 rules are:
    - Identity: UseN, PositA, UseComp, UseV, UseN2, UseA2
    - Semantic: PredVP (active-passive)
    - Tense: UseCl (present, past, future) -/
private theorem gfRGL_rule_lhs_ne_temporal (r : RewriteRule)
    (hr : r ∈ gfRGLLanguageDef.rewrites) :
    ∀ (cl t : Pattern),
      matchPattern r.left (.apply "⊛temporal" [cl, t]) = [] := by
  intro cl t
  simp only [gfRGLLanguageDef, allIdentityRewrites, allSemanticRewrites,
    allTenseRewrites, List.mem_append, List.mem_cons,
    List.mem_nil_iff, or_false] at hr
  -- Each disjunct fixes r to a specific rewrite rule with a known LHS
  rcases hr with (h|h|h|h|h|h)|(h|h|h|h) <;> subst h <;>
    simp [matchPattern, useNElimRewrite, positAElimRewrite,
      useCompElimRewrite, useVElimRewrite, useN2ElimRewrite, useA2ElimRewrite,
      activePassiveRewrite, presentTenseRewrite, pastTenseRewrite, futureTenseRewrite]

/-- GF RGL does not allow congruence rewriting in any collection type. -/
private theorem gfRGL_no_congruence (ct : CollType) :
    ¬ LanguageDef.allowsCongruenceIn gfRGLLanguageDef ct := by
  simp [LanguageDef.allowsCongruenceIn, gfRGLLanguageDef]

/-- **Semantic negative result**: Temporal patterns are terminal in GF RGL.
    No rewrite rule has `⊛temporal(...)` as its LHS, so temporal patterns
    have no successors under `langReduces`.

    This means: to reason about relationships between tenses
    (e.g., present → past), one must go through the world model, not
    through the rewrite engine. -/
theorem temporal_irreducible (cl t : Pattern) (q : Pattern) :
    ¬ langReduces gfRGLLanguageDef (.apply "⊛temporal" [cl, t]) q := by
  intro hred
  -- langReduces = DeclReducesWithPremises with empty RelationEnv
  -- Only topRule can apply (.apply patterns don't match congElem which needs .collection)
  cases hred with
  | topRule r hr bs0 hbs0 _ _ _ =>
    have := gfRGL_rule_lhs_ne_temporal r hr cl t
    simp [this] at hbs0

/-- **Negative result**: Present-tense does NOT entail past-tense semantically.
    Since temporal patterns are irreducible, `sem R I (◇ φ) present_pattern`
    requires a WM-level connection, not a rewrite-level one.

    Specifically: for any formula φ, `¬ sem (langReduces gfRGLLanguageDef) I (◇ φ) (⊛temporal(cl, 0))`. -/
theorem present_does_not_entail_past_sem (cl : Pattern) (I : AtomSem) (φ : OSLFFormula) :
    ¬ sem (langReduces gfRGLLanguageDef) I (.dia φ)
      (Pattern.apply "⊛temporal" [cl, Pattern.apply "0" []]) := by
  intro ⟨q, hR, _⟩
  exact absurd hR (temporal_irreducible cl _ q)

/-! ## Section 12b: Temporal Reduction Policy

Temporal patterns (`⊛temporal(cl, t)`) are terminal in the syntax rewrite system
(`temporal_irreducible`). To reason about temporal dynamics (present→past, etc.),
we compose syntax rewrites with an explicit temporal step relation.

### Design

`TemporalPolicy` selects the temporal regime:
- `.syntaxOnly` — no temporal evolution (current default)
- `.withStep step` — explicit temporal step relation

`gfReducesTemporal` combines syntax rewrites and temporal steps into a single
relation suitable for `sem`/`semE` evaluation.

### Key invariant

`temporal_irreducible` remains valid as the base-policy theorem.
Temporal entailment claims live in `gfReducesTemporal`, never in `langReduces`. -/

/-- Temporal evolution policy. -/
inductive TemporalPolicy where
  | syntaxOnly : TemporalPolicy
  | withStep (step : Pattern → Pattern → Prop) : TemporalPolicy

/-- Extract the temporal step relation from a policy. -/
def temporalStep : TemporalPolicy → Pattern → Pattern → Prop
  | .syntaxOnly => fun _ _ => False
  | .withStep step => step

/-- Combined relation: GF syntax rewrites + optional temporal evolution. -/
def gfReducesTemporal (π : TemporalPolicy) : Pattern → Pattern → Prop :=
  fun p q => langReduces gfRGLLanguageDef p q ∨ temporalStep π p q

/-- Predicate: pattern is a temporal-tagged node `⊛temporal(cl, t)`. -/
def isTemporalNode : Pattern → Prop
  | .apply "⊛temporal" [_, _] => True
  | _ => False

/-- Policy axiom schema: a well-scoped temporal policy only steps temporal nodes. -/
def TemporalWellScoped (π : TemporalPolicy) : Prop :=
  ∀ {p q : Pattern}, temporalStep π p q → isTemporalNode p ∧ isTemporalNode q

/-- Disciplined temporal policy: a record packaging the well-scopedness law.
    Users provide a policy together with a proof that it only touches temporal nodes. -/
structure TemporalStepLaws (π : TemporalPolicy) : Prop where
  wellScoped : ∀ {p q : Pattern}, temporalStep π p q → isTemporalNode p ∧ isTemporalNode q

/-- syntaxOnly trivially satisfies TemporalStepLaws (no steps, vacuously true). -/
theorem syntaxOnly_laws : TemporalStepLaws .syntaxOnly :=
  ⟨fun h => absurd h (by simp [temporalStep])⟩

/-- Syntax reduction is always included in the combined relation. -/
theorem syntax_in_gfReducesTemporal (π : TemporalPolicy) {p q : Pattern}
    (h : langReduces gfRGLLanguageDef p q) :
    gfReducesTemporal π p q :=
  Or.inl h

/-- Under syntax-only policy, temporal nodes are still irreducible. -/
theorem temporal_irreducible_syntaxOnly (cl t q : Pattern) :
    ¬ gfReducesTemporal .syntaxOnly (.apply "⊛temporal" [cl, t]) q := by
  rintro (hs | ht)
  · exact temporal_irreducible cl t q hs
  · exact ht

/-- Under syntax-only policy, no ◇-progress from temporal nodes. -/
theorem present_not_entail_past_syntaxOnly
    (cl : Pattern) (I : AtomSem) (φ : OSLFFormula) :
    ¬ sem (gfReducesTemporal .syntaxOnly) I (.dia φ)
      (.apply "⊛temporal" [cl, .apply "0" []]) := by
  intro ⟨q, hR, _⟩
  exact temporal_irreducible_syntaxOnly cl (.apply "0" []) q hR

/-- If a temporal policy provides an edge from present to past, ◇ is obtainable. -/
theorem present_can_progress_of_temporalStep
    (step : Pattern → Pattern → Prop)
    (cl : Pattern)
    (hstep : step
      (.apply "⊛temporal" [cl, .apply "0" []])
      (.apply "⊛temporal" [cl, .apply "-1" []]))
    (I : AtomSem) :
    sem (gfReducesTemporal (.withStep step)) I
      (.dia .top)
      (.apply "⊛temporal" [cl, .apply "0" []]) :=
  ⟨.apply "⊛temporal" [cl, .apply "-1" []], Or.inr hstep, trivial⟩

/-- Monotonicity of `sem` in the reduction relation for the positive fragment.

    The positive fragment excludes `imp` and `box` (which are contravariant in R).
    For dia/and/or/top/bot/atom, enlarging R preserves satisfaction. -/
def positiveFormula : OSLFFormula → Prop
  | .top | .bot | .atom _ => True
  | .and φ ψ | .or φ ψ => positiveFormula φ ∧ positiveFormula ψ
  | .imp _ _ | .box _ => False
  | .dia φ => positiveFormula φ

theorem sem_mono_rel_positive
    {R1 R2 : Pattern → Pattern → Prop}
    (hR : ∀ p q, R1 p q → R2 p q)
    (I : AtomSem) {φ : OSLFFormula} (hpos : positiveFormula φ)
    {p : Pattern} (h : sem R1 I φ p) : sem R2 I φ p := by
  induction φ generalizing p with
  | top => trivial
  | bot => exact h
  | atom _ => exact h
  | and φ ψ ihφ ihψ =>
    exact ⟨ihφ hpos.1 h.1, ihψ hpos.2 h.2⟩
  | or φ ψ ihφ ihψ =>
    exact h.elim (Or.inl ∘ ihφ hpos.1) (Or.inr ∘ ihψ hpos.2)
  | imp _ _ => exact absurd hpos (by simp [positiveFormula])
  | dia φ ih =>
    obtain ⟨q, hRpq, hq⟩ := h
    exact ⟨q, hR p q hRpq, ih hpos hq⟩
  | box _ => exact absurd hpos (by simp [positiveFormula])

/-- Modal-free fragment: no dia, no box.  `sem R I φ p` is independent of R. -/
def modalFree : OSLFFormula → Prop
  | .top | .bot | .atom _ => True
  | .and φ ψ | .or φ ψ | .imp φ ψ => modalFree φ ∧ modalFree ψ
  | .dia _ | .box _ => False

/-- Modal-free formulas have R-independent semantics. -/
theorem sem_modalFree_irrel {R1 R2 : Pattern → Pattern → Prop}
    (I : AtomSem) {φ : OSLFFormula} (hmf : modalFree φ)
    {p : Pattern} : sem R1 I φ p ↔ sem R2 I φ p := by
  induction φ generalizing p with
  | top => simp [sem]
  | bot => simp [sem]
  | atom _ => simp [sem]
  | and φ ψ ihφ ihψ =>
    exact ⟨fun ⟨h1, h2⟩ => ⟨(ihφ hmf.1).mp h1, (ihψ hmf.2).mp h2⟩,
           fun ⟨h1, h2⟩ => ⟨(ihφ hmf.1).mpr h1, (ihψ hmf.2).mpr h2⟩⟩
  | or φ ψ ihφ ihψ =>
    exact ⟨fun h => h.elim (Or.inl ∘ (ihφ hmf.1).mp) (Or.inr ∘ (ihψ hmf.2).mp),
           fun h => h.elim (Or.inl ∘ (ihφ hmf.1).mpr) (Or.inr ∘ (ihψ hmf.2).mpr)⟩
  | imp φ ψ ihφ ihψ =>
    exact ⟨fun h hφ => (ihψ hmf.2).mp (h ((ihφ hmf.1).mpr hφ)),
           fun h hφ => (ihψ hmf.2).mpr (h ((ihφ hmf.1).mp hφ))⟩
  | dia _ => exact absurd hmf (by simp [modalFree])
  | box _ => exact absurd hmf (by simp [modalFree])

/-- Anti-monotonicity of `sem` in the reduction relation for `box`.

    `box φ` at `p` says: for all `q` with `R q p`, `φ` holds at `q`.
    Shrinking R (R2 ⊆ R1) means fewer such `q`, so the universal is preserved.
    The inner formula must be modal-free so its semantics doesn't depend on R. -/
theorem sem_antitone_box
    {R1 R2 : Pattern → Pattern → Prop}
    (hR : ∀ p q, R2 p q → R1 p q)
    (I : AtomSem) {φ : OSLFFormula} (hmf : modalFree φ)
    {p : Pattern} (h : sem R1 I (.box φ) p) : sem R2 I (.box φ) p := by
  intro q hR2qp
  exact (sem_modalFree_irrel I hmf).mp (h q (hR q p hR2qp))

/-- Corollary: any `sem (langReduces gfRGLLanguageDef)` result on a positive formula
    lifts to `sem (gfReducesTemporal π)`. -/
theorem sem_syntax_lifts_to_temporal (π : TemporalPolicy)
    (I : AtomSem) {φ : OSLFFormula} (hpos : positiveFormula φ)
    {p : Pattern} (h : sem (langReduces gfRGLLanguageDef) I φ p) :
    sem (gfReducesTemporal π) I φ p :=
  sem_mono_rel_positive (fun _ _ => syntax_in_gfReducesTemporal π) I hpos h

/-! ## Section 13: Presupposition Bridge

Definite descriptions in GF (DetCN(the_Det, CN)) carry an existence
presupposition: the CN must have a referent.  In evidence semantics, this
is modeled as tensor-gating:

  `⟦the CN is VP⟧ = E_∃(CN) ⊗ E_VP(the CN)`

where `E_∃(CN)` is the evidence that CN has a referent (from the WM) and
`E_VP(the CN)` is the assertion evidence (the VP property of the CN).

### Projection laws at the GF level

1. **Negation**: "The king of France is NOT bald" → presupposition survives
2. **Conditional**: "If France has a king, then the king of France is bald"
   → presupposition is filtered by the antecedent

### References

- Strawson, "On Referring" (1950)
- Heim, "On the Projection Problem for Presuppositions" (1983)
- Beaver & Geurts, "Presupposition" (SEP, 2014)
-/

/-- Existence presupposition atom: evidence that a CN has a referent.
    Encoded as atom "exists" at the CN pattern. -/
noncomputable def existsPresupEvidence (W : State) (cn : Pattern) : BinaryEvidence :=
  gfWMFormulaSemE W (.atom "exists") cn

/-- Presupposition-gated evidence for a definite description sentence.
    "The CN is VP" has evidence = E_∃(CN) ⊗ E_VP(the_CN).

    Example: "The king of France is bald"
    - presup: E_∃(king_of_france) = WM evidence that ∃ a KoF
    - assert: E_bald(DetCN(the_Det, king_of_france_CN))
    - total:  E_∃ ⊗ E_assert -/
noncomputable def definiteDescriptionEvidence
    (W : State) (cn_pattern : Pattern)
    (assertFormula : OSLFFormula) (sentence_pattern : Pattern) : BinaryEvidence :=
  existsPresupEvidence W cn_pattern *
  gfWMFormulaSemE W assertFormula sentence_pattern

/-- When existence is fully evidenced (E_∃ = one), the definite description
    reduces to pure assertion evidence. -/
theorem definiteDescription_presup_satisfied
    (W : State) (cn_pat sent_pat : Pattern)
    (assertFormula : OSLFFormula)
    (h : existsPresupEvidence W cn_pat = BinaryEvidence.one) :
    definiteDescriptionEvidence W cn_pat assertFormula sent_pat =
    gfWMFormulaSemE W assertFormula sent_pat := by
  unfold definiteDescriptionEvidence
  rw [h, BinaryEvidence.one_tensor]

/-- When existence evidence is ⊥ (presupposition failure), the definite
    description collapses to ⊥ regardless of assertion content. -/
theorem definiteDescription_presup_failure
    (W : State) (cn_pat sent_pat : Pattern)
    (assertFormula : OSLFFormula)
    (h : existsPresupEvidence W cn_pat = ⊥) :
    definiteDescriptionEvidence W cn_pat assertFormula sent_pat = ⊥ := by
  unfold definiteDescriptionEvidence
  rw [h]
  simp

/-- **Negation projection**: The presupposition of "The CN is NOT VP" is the
    same existence presupposition as "The CN is VP".

    BinaryEvidence version: the presupposition factor `E_∃(CN)` is identical
    regardless of whether the assertion is negated (via `φ → ⊥`). -/
theorem negation_preserves_definite_presup
    (W : State) (cn_pat : Pattern) (assertFormula : OSLFFormula) :
    presupGatedSemE (langReduces gfRGLLanguageDef)
      (gfEvidenceAtomSemFromWM W)
      (.atom "exists") (.imp assertFormula .bot) cn_pat =
    gfWMFormulaSemE W (.atom "exists") cn_pat *
      (gfWMFormulaSemE W assertFormula cn_pat ⇨ ⊥) := by
  unfold presupGatedSemE gfWMFormulaSemE
  simp [semE_imp, semE_bot]

/-- **Conditional filtering**: In "If P then the CN is VP", the presupposition
    `∃ CN` is filtered through P.  The evidence version: the conditional
    sentence's evidence is at most P → (∃CN ⊗ VP).

    Formal statement: the evidence of "if P then presupGated(∃CN, VP)"
    equals the Heyting implication from P-evidence to gated-evidence. -/
theorem conditional_filters_definite_presup
    (W : State) (cn_pat : Pattern)
    (antecedent assertFormula : OSLFFormula) :
    gfWMFormulaSemE W (.imp antecedent (.and (.atom "exists") assertFormula)) cn_pat =
    gfWMFormulaSemE W antecedent cn_pat ⇨
    (gfWMFormulaSemE W (.atom "exists") cn_pat ⊓
     gfWMFormulaSemE W assertFormula cn_pat) := by
  unfold gfWMFormulaSemE
  simp [semE_imp, semE_and]

/-! ## Section 14: Scope Ambiguity via Two Quantifier Readings

"Every man loves some woman" has two readings:
1. **Surface scope (wide ∀)**: ∀x. man(x) → ∃y. woman(y) ∧ loves(x,y)
   "For every man, there exists SOME woman he loves" (different women OK)
2. **Inverse scope (wide ∃)**: ∃y. woman(y) ∧ ∀x. man(x) → loves(x,y)
   "There is ONE specific woman that every man loves"

The inverse scope is STRONGER: it entails the surface scope, but not vice versa.
This is the fundamental scope ordering from quantifier theory.

### GF representation

In GF RGL, the surface form is a single parse tree:
  `UseCl(TTAnt(TPres, ASimul), PPos,
    PredVP(DetCN(every_Det, UseN(man)),
      ComplSlash(SlashV2a(love), DetCN(someSg_Det, UseN(woman)))))`

The two readings arise from different SEMANTIC interpretations (scopings)
of the same syntactic tree, expressed as different `QFormula` structures.

### References

- Montague, "The Proper Treatment of Quantification in Ordinary English" (1973)
- May, "Logical Form" (1985) — scope ambiguity via Quantifier Raising
- PLN_FactorGraph_MORK_v2.pdf §3.2 — Skolemization for scope
-/

section ScopeAmbiguity

open Mettapedia.OSLF.QuantifiedFormula

/-- Surface scope reading of "every man loves some woman":
    ∀x. man(x) → ∃y. woman(y) ∧ loves(x,y)
    Each man may love a different woman. -/
def surfaceScopeReading : QFormula :=
  .qforall "x" (.qimp (.base (.atom "is_man"))
    (.qexists "y" (.qand (.base (.atom "is_woman")) (.base (.atom "loves")))))

/-- Inverse scope reading of "every man loves some woman":
    ∃y. woman(y) ∧ ∀x. man(x) → loves(x,y)
    There is ONE specific woman all men love. -/
def inverseScopeReading : QFormula :=
  .qexists "y" (.qand (.base (.atom "is_woman"))
    (.qforall "x" (.qimp (.base (.atom "is_man")) (.base (.atom "loves")))))

/-- **Key theorem**: Inverse scope entails surface scope (abstract lattice level).

    For any complete lattice and any family `f : ι → κ → α`,
    `⨆ j, ⨅ i, f i j ≤ ⨅ i, ⨆ j, f i j`

    This is the quantifier scope ordering: ∃y.∀x.P(x,y) → ∀x.∃y.P(x,y).
    Instantiates to BinaryEvidence via `CompleteLattice BinaryEvidence`.

    Proved in `QuantifiedFormula.lean` as `iSup_iInf_le_iInf_iSup`. -/
theorem inverse_scope_le_surface_scope_evidence {ι κ : Type*}
    (f : ι → κ → BinaryEvidence) :
    (⨆ j, ⨅ i, f i j) ≤ (⨅ i, ⨆ j, f i j) :=
  iSup_iInf_le_iInf_iSup f

end ScopeAmbiguity

/-! ## Section 15: Anaphora as Variable Binding

Pronoun anaphora is modeled as variable binding in quantified formulas.
The key insight: pronouns are FREE VARIABLES that must be bound by an
antecedent quantifier for the discourse to be felicitous.

### Example: "A man walked. He sat down."

DRT/dynamic semantics reading:
  ∃x. man(x) ∧ walked(x) ∧ sat_down(x)

The pronoun "he" is resolved to the same variable `x` that was introduced
by "a man".  In our QFormula framework, this is automatic: the existential
quantifier `∃x` in the first sentence extends the VarEnv, and the pronoun
"he" in the second sentence refers to the same `x`.

### Unresolved anaphora = unbound variable

If the pronoun has no antecedent (no quantifier binds it), the VarEnv
maps it to `none`, and `envAtomSem` falls back to the base interpretation.
This models presupposition failure for anaphora (no referent found).

### References

- Kamp, "A Theory of Truth and Semantic Representation" (1981)
- Heim, "File Change Semantics" (1982)
- Groenendijk & Stokhof, "Dynamic Predicate Logic" (1991)
-/

section Anaphora

open Mettapedia.OSLF.QuantifiedFormula

/-- Discourse with anaphora: "A man walked. He sat down."
    The pronoun "he" is bound by the existential quantifier.
    Formalized as: ∃x. man(x) ∧ walked(x) ∧ sat_down(x) -/
def anaphoricDiscourse : QFormula :=
  .qexists "x"
    (.qand (.qand (.base (.atom "is_man")) (.base (.atom "walked")))
           (.base (.atom "sat_down")))

/-- Non-anaphoric version: two independent sentences.
    "A man walked. Someone sat down."
    ∃x. man(x) ∧ walked(x) ∧ ∃y. sat_down(y) -/
def nonAnaphoricDiscourse : QFormula :=
  .qand
    (.qexists "x" (.qand (.base (.atom "is_man")) (.base (.atom "walked"))))
    (.qexists "y" (.base (.atom "sat_down")))

/-- **Abstract scope projection**: `∃x.(P(x) ∧ Q(x)) ≤ (∃x.P(x)) ∧ (∃x.Q(x))`.

    Anaphoric binding is stronger: requiring the SAME entity for P and Q
    gives at most as much evidence as allowing different entities.

    Proved at the lattice level: ⨆ (inf ∘ pair) ≤ (⨆ left) ⊓ (⨆ right). -/
theorem iSup_inf_le_inf_iSup {α : Type*} {ι : Type*}
    [CompleteLattice α] (f g : ι → α) :
    (⨆ i, f i ⊓ g i) ≤ (⨆ i, f i) ⊓ (⨆ i, g i) := by
  apply le_inf
  · exact iSup_mono (fun i => inf_le_left)
  · exact iSup_mono (fun i => inf_le_right)

end Anaphora

/-! ## 22. Canonical Paper Theorems

Named theorem endpoints for the publishable framework.
Map to Table 5 in the paper. -/

section PaperTheorems

open Mettapedia.Languages.GF.LinguisticInvariance
open Mettapedia.Logic.PLNWorldModel

/-- **Translation preserves evidence (all W).**
    Same abstract tree → same evidence in all world-model states.
    The proof is trivially `congrArg` because `gfEvidenceDenote W t`
    depends only on `gfAbstractToPattern t`, not on linearization.

    Paper claim: "Meaning is computed from the shared abstract tree,
    so translation (different linearizations) preserves evidence." -/
theorem translation_preserves_evidence_allW
    {t₁ t₂ : AbstractNode}
    (hPat : gfAbstractToPattern t₁ = gfAbstractToPattern t₂) :
    ∀ W : State, gfEvidenceDenote W t₁ = gfEvidenceDenote W t₂ :=
  fun _ => by simp [gfEvidenceDenote, hPat]

/-- **Checker .sat → WM semantics (general formulas).**
    If the OSLF checker returns `.sat` with WM-grounded atom checking,
    then the formula holds in WM-grounded denotational semantics.

    This is `oslf_sat_implies_wm_semantics` with a paper-facing name. -/
theorem checker_sat_implies_wm_semantics_general
    (W : State) (threshold : ℝ≥0∞)
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true → (gfAtomSemFromWM W threshold) a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (hSat : checkLangUsing .empty gfRGLLanguageDef I_check fuel p φ = .sat) :
    gfWMFormulaSem W threshold φ p :=
  oslf_sat_implies_wm_semantics W threshold h_atoms hSat

/-- **Checker .sat on atom → WM formula semantics.** -/
theorem checker_sat_atom_implies_wm_semantics
    (W : State) (threshold : ℝ≥0∞)
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true → (gfAtomSemFromWM W threshold) a p)
    {fuel : Nat} {p : Pattern} {a : String}
    (hSat : checkLangUsing .empty gfRGLLanguageDef I_check fuel p (.atom a) = .sat) :
    gfWMFormulaSem W threshold (.atom a) p :=
  oslf_sat_implies_wm_semantics W threshold h_atoms hSat

/-- **WM query judgment for atoms.**
    A derivable world-model state yields a query judgment for any atom query.
    Independent of the checker — purely a WM property. -/
theorem atom_wm_query_judgment
    (W : State) (hW : WMJudgment W) (a : String) (p : Pattern) :
    WMQueryJudgment W (queryOfAtom a p) (BinaryWorldModel.evidence W (queryOfAtom a p)) :=
  ⟨hW, rfl⟩

/-- **Combined: checker .sat on atom → WM semantics + WM query judgment.**
    Packages checker soundness with query judgment for atom formulas.
    Composed from `checker_sat_atom_implies_wm_semantics` and
    `atom_wm_query_judgment`. -/
theorem checker_sat_atom_implies_wm_query_judgment
    (W : State) (threshold : ℝ≥0∞)
    {I_check : AtomCheck}
    (h_atoms : ∀ a p, I_check a p = true → (gfAtomSemFromWM W threshold) a p)
    (hW : WMJudgment W)
    {fuel : Nat} {p : Pattern} {a : String}
    (hSat : checkLangUsing .empty gfRGLLanguageDef I_check fuel p (.atom a) = .sat) :
    gfWMFormulaSem W threshold (.atom a) p ∧
    WMQueryJudgment W (queryOfAtom a p) (BinaryWorldModel.evidence W (queryOfAtom a p)) :=
  ⟨checker_sat_atom_implies_wm_semantics W threshold h_atoms hSat,
   atom_wm_query_judgment W hW a p⟩

/-- **Lexical evidence monotonicity assumption.**
    A world-model state W satisfies this if patterns with more lexical
    content have at least as much evidence. This is a reasonable WM
    property, not universally true but common in knowledge-base semantics. -/
def LexicalEvidenceMonotone (W : State) : Prop :=
  ∀ p q : Pattern,
    (∀ name, containsLexical name p = true → containsLexical name q = true) →
    BinaryWorldModel.evidence W p ≤ BinaryWorldModel.evidence W q

/-- **Positive example**: a WM state where evidence is constant (e.g., ⊤ for all
    patterns) satisfies `LexicalEvidenceMonotone` — the inclusion hypothesis is
    unused because `e ≤ e` always holds. -/
theorem lexicalMono_of_const_evidence (W : State)
    (hconst : ∀ p q : Pattern, BinaryWorldModel.evidence W p = BinaryWorldModel.evidence W q) :
    LexicalEvidenceMonotone W :=
  fun p q _ => le_of_eq (hconst p q)

/-- **Negative example**: `LexicalEvidenceMonotone` is a genuine assumption —
    it does NOT follow from the WM axioms alone. Given a state where a
    superset-pattern has strictly less evidence, the assumption fails. -/
theorem lexicalMono_not_trivial (W : State) (p q : Pattern)
    (hlex : ∀ name, containsLexical name p = true → containsLexical name q = true)
    (hlt : BinaryWorldModel.evidence W q < BinaryWorldModel.evidence W p) :
    ¬ LexicalEvidenceMonotone W := by
  intro hmono
  exact lt_irrefl _ (lt_of_lt_of_le hlt (hmono p q hlex))

/-- **AdjCN preserves evidence (conditional).**
    Under the `LexicalEvidenceMonotone` assumption, adjective modification
    does not decrease evidence: `⟦CN⟧_W ≤ ⟦AdjCN(adj, CN)⟧_W`.

    The proof uses `adjModification_preserves_lexical` (all lexical items
    of CN are preserved in AdjCN) + the monotonicity assumption.

    Paper claim: "AdjCN evidence monotonicity holds conditionally on a
    natural WM assumption." -/
theorem adjCN_preserves_evidence_if
    (W : State) (hLexMono : LexicalEvidenceMonotone W)
    (adjName : String) (cn : AbstractNode) :
    gfEvidenceDenote W cn ≤ gfEvidenceDenote W (addAdjModifier adjName cn) := by
  unfold gfEvidenceDenote
  exact hLexMono _ _ (adjModification_preserves_lexical adjName cn)

end PaperTheorems

end GFSemantics

end Mettapedia.Languages.GF.WorldModelSemantics
