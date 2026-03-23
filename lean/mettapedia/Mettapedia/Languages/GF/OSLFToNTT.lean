import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.Languages.GF.VisibleLayerGFInstance
import Mettapedia.Languages.GF.StoreToLogicalForm
import Mettapedia.Languages.GF.WorldModelVisibleBridge
import Mettapedia.Languages.GF.OSLFBridge_handcrafted
import Mettapedia.OSLF.QuantifiedFormula2
import Mettapedia.CategoryTheory.NativeTypeTheory
import Mettapedia.CategoryTheory.PLNInstance
import Mettapedia.Languages.GF.Examples.EveryManWalks

/-!
# OSLF → NTT Composition

Composes the OSLF evidence semantics with NativeTypeTheory (Grothendieck
construction ∫ Sub), completing the pipeline:

```
  GF → Pattern → GrammarState → QFormula2 → BinaryEvidence → NativeTypeTheory
```

The bridge exploits `PLNFiber X = BinaryEvidence`, making the Grothendieck
fiber directly the evidence value from `qsemE2`/`gsemE2Full`.
-/

namespace Mettapedia.Languages.GF.OSLFToNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.Languages.GF.VisibleLayer
open Mettapedia.Languages.GF.VisibleLayerGFInstance
open Mettapedia.Languages.GF.StoreToLogicalForm
open Mettapedia.Languages.GF.WorldModelVisibleBridge
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.CategoryTheory.NativeTypeTheory
open Mettapedia.Languages.GF.Examples.EveryManWalks
open Mettapedia.Logic.EvidenceQuantale

/-! ## 1. BinaryEvidence → NT Object -/

/-- Construct an NT object from a PLN proposition type and an evidence value. -/
def evidenceToNT (X : PLNObj) (e : BinaryEvidence) : NativeTypeBundle :=
  Sigma.mk X e

theorem evidenceToNT_fst (X : PLNObj) (e : BinaryEvidence) :
    (evidenceToNT X e).1 = X := rfl

theorem evidenceToNT_snd (X : PLNObj) (e : BinaryEvidence) :
    (evidenceToNT X e).2 = e := rfl

/-- BinaryEvidence ordering lifts to NT morphisms. -/
def evidenceToNT_hom (X : PLNObj) (e₁ e₂ : BinaryEvidence) (h : e₁ ≤ e₂) :
    Hom (evidenceToNT X e₁) (evidenceToNT X e₂) :=
  PLift.up h

/-! ## 2. QFormula2 → NT via BinaryEvidence Evaluation -/

/-- Evaluate a quantified formula to an NT object. -/
noncomputable def formulaToNT (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2) (φ : QFormula2) (p : Pattern)
    (X : PLNObj) : NativeTypeBundle :=
  evidenceToNT X (qsemE2 R I Dom env φ p)

/-- Signature canary for `formulaToNT`.
    If `formulaToNT` changes shape, this definition fails to typecheck. -/
abbrev FormulaToNTSig : Type :=
  (Pattern → Pattern → Prop) → QEvidenceAtomSem →
  Domain2 → VarEnv2 → QFormula2 → Pattern → PLNObj → NativeTypeBundle

noncomputable def formulaToNT_signature_canary : FormulaToNTSig := formulaToNT

/-- Formula entailment lifts to NT morphisms. -/
noncomputable def formulaToNT_hom (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2) (p : Pattern) (X : PLNObj)
    (φ ψ : QFormula2)
    (hle : qsemE2 R I Dom env φ p ≤ qsemE2 R I Dom env ψ p) :
    Hom (formulaToNT R I Dom env φ p X) (formulaToNT R I Dom env ψ p X) :=
  PLift.up hle

/-! ## 3. GrammarState → NT via gsemE2Full -/

/-- Evaluate a grammar state to an NT object via the full combined semantics. -/
noncomputable def grammarStateToNT (cfg : VisibleCfg) (π : WorldModelSemantics.TemporalPolicy)
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (s : GrammarState) (X : PLNObj) : NativeTypeBundle :=
  evidenceToNT X (gsemE2Full cfg π I Dom φ s)

/-- Signature canary for `grammarStateToNT`.
    If `grammarStateToNT` changes shape, this definition fails to typecheck. -/
abbrev GrammarStateToNTSig : Type :=
  VisibleCfg → WorldModelSemantics.TemporalPolicy →
  QEvidenceAtomSem → Domain2 → QFormula2 → GrammarState → PLNObj → NativeTypeBundle

noncomputable def grammarStateToNT_signature_canary : GrammarStateToNTSig := grammarStateToNT

theorem grammarStateToNT_snd (cfg : VisibleCfg) (π : WorldModelSemantics.TemporalPolicy)
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (s : GrammarState) (X : PLNObj) :
    (grammarStateToNT cfg π I Dom φ s X).2 = gsemE2Full cfg π I Dom φ s := rfl

/-! ## 4. Pipeline Composition Theorems -/

/-- ⊥ evidence always lifts: morphism from `⟨X, ⊥⟩` to any `⟨X, e⟩`. -/
def evidenceToNT_bot_hom (X : PLNObj) (e : BinaryEvidence) :
    Hom (evidenceToNT X ⊥) (evidenceToNT X e) :=
  PLift.up bot_le

/-- Scope ordering lifts to NT: inverse scope (∃∀) ≤ surface scope (∀∃). -/
noncomputable def scope_ordering_NT
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem)
    (Dom : Domain2) (env : VarEnv2)
    {x y : String} (hne : x ≠ y)
    (φ : QFormula2) (p : Pattern) (X : PLNObj) :
    Hom (formulaToNT R I Dom env (.qexists y (.qforall x φ)) p X)
        (formulaToNT R I Dom env (.qforall x (.qexists y φ)) p X) :=
  PLift.up (scope_ordering_qsemE2 R I Dom env hne φ p)

/-- Closed formula evaluation is environment-independent at the NT level. -/
theorem formulaToNT_closed_env_irrel
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2)
    (env₁ env₂ : VarEnv2) (φ : QFormula2) (hcl : closedQF2 φ) (p : Pattern)
    (X : PLNObj) :
    formulaToNT R I Dom env₁ φ p X = formulaToNT R I Dom env₂ φ p X := by
  simp only [formulaToNT, evidenceToNT]
  exact congrArg (Sigma.mk X) (qsemE2_closed_env_irrel R I Dom hcl env₁ env₂ p)

/-! ## 5. Concrete Example: "Every man walks" → NT -/

/-- "Every man walks" produces the expected NT object:
    the evidence fiber is `⨅ d, (man(d) ⇨ walks(d))`. -/
theorem emw_NT
    (R : Pattern → Pattern → Prop) (I : QEvidenceAtomSem) (Dom : Domain2)
    (X : PLNObj) :
    formulaToNT R I Dom emptyEnv2 emw_formula emw_afterV1_term X =
    evidenceToNT X (⨅ (d : Dom), (I "man_N" [d.val] emw_afterV1_term ⇨
                                   I "walk_V" [d.val] emw_afterV1_term)) := by
  simp only [formulaToNT, emw_formula, qsemE2, extendEnv2, evalTerms, evalTerm, emptyEnv2]
  rfl

/-! ## 6. WM-Dynamics → NTT Morphisms -/

/-- V4 (pronoun binding) produces an NT morphism: pre-state has ⊥ evidence
    (unresolved pronoun), post-state has real evidence, so `⊥ ≤ real`. -/
noncomputable def V4_dynamics_NT_morphism
    {cfg : VisibleCfg} {π : WorldModelSemantics.TemporalPolicy}
    (pr r : String) (pos : Pattern) (s : GrammarState)
    (href_pos : StoreAtom.ref r pos ∈ s.store)
    (hfresh : ∀ r', StoreAtom.bind pr r' ∉ s.store)
    (hfb : functionalBind s.store) (hur : uniqueRef s.store)
    (pred : String) (I : QEvidenceAtomSem) (Dom : Domain2) (X : PLNObj) :
    let s' : GrammarState := ⟨s.term, s.store + {.bind pr r}⟩
    Hom (grammarStateToNT cfg π I Dom (.qatom ⟨pred, [.var pr]⟩) s X)
        (grammarStateToNT cfg π I Dom (.qatom ⟨pred, [.var pr]⟩) s' X) := by
  have hpre := (V4_post_step_semantic_change (cfg := cfg) (π := π)
    pr r pos s href_pos hfresh hfb hur pred I Dom).2.1
  simp only [grammarStateToNT]
  rw [hpre]
  exact evidenceToNT_bot_hom X _

/-- Closed formulas produce equal NT objects regardless of store changes,
    because closed formulas are environment-independent.

    This covers V2 (scope choice), V3 (referent intro), V4 (pronoun bind)
    when the formula is closed: the store changes but the NT object doesn't. -/
theorem closed_frame_NT_eq
    {cfg : VisibleCfg} {π : WorldModelSemantics.TemporalPolicy}
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2) (hcl : closedQF2 φ)
    (s : GrammarState) (a : StoreAtom) (X : PLNObj) :
    let s' : GrammarState := ⟨s.term, s.store + {a}⟩
    grammarStateToNT cfg π I Dom φ s X = grammarStateToNT cfg π I Dom φ s' X := by
  intro s'
  simp only [grammarStateToNT, evidenceToNT]
  exact congrArg (Sigma.mk X) (frame_closed_any_atom I Dom φ hcl a s)

/-! ## 7. Categorical Perspective

```
  languagePresheafLambdaTheory gfRGLLanguageDef   -- Presheaf category (OSLF)
         ↓ languageSortFiber                      -- Sort-fiber extraction
  languageSortFiber gfRGLLanguageDef s            -- Subobjects at sort s
         ↓ qsemE2 evaluation                     -- BinaryEvidence semantics
  BinaryEvidence                                         -- Frame-valued truth
         ↓ evidenceToNT                           -- Grothendieck pairing
  NativeTypeTheory                                 -- NTT category (∫ Sub)
```

Properties preserved: monotonicity (`formulaToNT_hom`), scope ordering
(`scope_ordering_NT`), environment independence (`closed_frame_NT_eq`),
⊥ activation (`V4_dynamics_NT_morphism`).
-/

end Mettapedia.Languages.GF.OSLFToNTT
