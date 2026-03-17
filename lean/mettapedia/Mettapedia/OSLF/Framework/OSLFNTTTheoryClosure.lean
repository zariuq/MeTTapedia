import Mettapedia.OSLF.Framework.OSLFNTTWMBridge
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelCategoricalBridge
import Mettapedia.Logic.PLNWorldModelFixpointClosure

/-!
# OSLF -> NTT Theory Closure

Closure-oriented bridge layer over the canonical formula endpoint:

- define a derivation relation (`OSLFTheoryStep`) and its reflexive-transitive closure,
- expose endpoint bridge packages (`FormulaEndpointBridge`,
  `FormulaCategoricalEndpointBridge`),
- transport derivations to WM strength obligations through an explicit interface,
- package one-step/star derivations as WM consequence rules.
-/

namespace Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.OSLF.Framework.OSLFNTTWMBridge
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine

universe u v x

variable {State : Type x} [EvidenceType State] [BinaryWorldModel State Pattern]

/-- Theory-level one-step relation for OSLF formulas over MeTTaFull constructors. -/
abbrev OSLFTheoryStep (relEnv : RelationEnv) : Pattern → Pattern → Prop :=
  Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv
    Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull

/-- Reflexive-transitive closure of `OSLFTheoryStep`. -/
abbrev OSLFTheoryStepStar (relEnv : RelationEnv) : Pattern → Pattern → Prop :=
  Relation.ReflTransGen (OSLFTheoryStep relEnv)

/-- Formula-level endpoint bridge package over all source patterns. -/
abbrev FormulaEndpointBridge
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)} : Prop :=
  ∀ p : Pattern,
    FormulaGraphEndpoint
      (State := State) (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
      (X := X) (p := p)

/-- Canonical formula endpoint bridge is derivable directly from
`oslf_formula_ntt_graph_triangle`. -/
theorem formulaEndpointBridge_of_oslf_formula_ntt_graph_triangle
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)} :
    FormulaEndpointBridge
      (State := State) (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
      (X := X) := by
  intro p
  exact oslf_formula_ntt_graph_triangle
    (relEnv := relEnv) (W := W) (queryOfAtom := queryOfAtom)
    (φf := φf) (Xobj := Xobj) (X := X) (p := p)

/-- Categorical formula endpoint bridge package over all source patterns. -/
abbrev FormulaCategoricalEndpointBridge
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (φcat : H.query Bobj) : Prop :=
  ∀ p : Pattern,
    FormulaGraphEndpoint
      (State := State) (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
      (X := X) (p := p)
      ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat W φcat

/-- Canonical categorical formula endpoint bridge is derivable directly from
`oslf_formula_ntt_graph_triangle_categorical`. -/
theorem formulaCategoricalEndpointBridge_of_oslf_formula_ntt_graph_triangle
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (φcat : H.query Bobj) :
    FormulaCategoricalEndpointBridge
      (State := State) (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
      (X := X) (φcat := φcat) := by
  intro p
  exact oslf_formula_ntt_graph_triangle_categorical
    (H := H) (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
    (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
    (relEnv := relEnv) (W := W)
    (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
    (X := X) (p := p) (φcat := φcat)

/-- Build the unified categorical bridge package from separate formula-level and
categorical endpoint components. -/
theorem formulaCategoricalEndpointBridge_of_components
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (relEnv : RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (φcat : H.query Bobj)
    (hFormula :
      FormulaEndpointBridge
        (State := State) (relEnv := relEnv) (W := W)
        (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj) (X := X))
    (hCat :
      EndpointStatement (H := H) pi1 pi2 fcat gcat W φcat) :
    FormulaCategoricalEndpointBridge
      (State := State) (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj)
      (X := X) (φcat := φcat) := by
  intro p
  exact ⟨hFormula p, hCat⟩

/-- Local WM strength obligation for a fixed state/query pair. -/
abbrev WMStrengthObligation
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (q₁ q₂ : Query) : Prop :=
  BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
    BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂

/-- Local WM evidence obligation for a fixed state/query pair.

This is the evidence-level counterpart of `WMStrengthObligation`, used when
`toStrength` monotonicity is not available from the ambient semantics.
-/
abbrev WMEvidenceObligation
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query]
    (W : State) (q₁ q₂ : Query) : Prop :=
  BinaryWorldModel.evidence (State := State) (Query := Query) W q₁ ≤
    BinaryWorldModel.evidence (State := State) (Query := Query) W q₂

/-- State-indexed WM evidence consequence rule. -/
structure WMEvidenceConsequenceRuleOn
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query] where
  side : State → Prop := fun _ => True
  premise : Query
  conclusion : Query
  sound :
    ∀ {W : State}, side W →
      WMEvidenceObligation State Query W premise conclusion

/-- BinaryEvidence-level interface: theory-level OSLF steps discharge WM evidence
obligations. Strength-level obligations can then be recovered separately when a
state/query family has a proved strength-monotone transport. -/
structure OSLFNTTWMEvidenceInterface
    (relEnv : RelationEnv)
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query] where
  encode : Pattern → Query
  side : State → Prop := fun _ => True
  step_sound :
    ∀ {W : State} {p q : Pattern},
      side W →
      OSLFTheoryStep relEnv p q →
      WMEvidenceObligation State Query W (encode p) (encode q)

namespace OSLFNTTWMEvidenceInterface

variable {relEnv : RelationEnv}
variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Reflexive-transitive closure transport to WM evidence obligations. -/
theorem stepStar_sound
    (I : OSLFNTTWMEvidenceInterface relEnv State Query)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : OSLFTheoryStepStar relEnv p q) :
    WMEvidenceObligation State Query W (I.encode p) (I.encode q) := by
  induction hstar with
  | refl =>
      exact le_rfl
  | tail hxy hyz ih =>
      exact le_trans ih (I.step_sound hW hyz)

end OSLFNTTWMEvidenceInterface

/-- Interface: how theory-level OSLF steps discharge WM obligations. -/
structure OSLFNTTWMInterface
    (relEnv : RelationEnv)
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query] where
  encode : Pattern → Query
  side : State → Prop := fun _ => True
  step_sound :
    ∀ {W : State} {p q : Pattern},
      side W →
      OSLFTheoryStep relEnv p q →
      WMStrengthObligation State Query W (encode p) (encode q)

namespace OSLFNTTWMInterface

variable {relEnv : RelationEnv}
variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Reflexive-transitive closure transport to WM obligations. -/
theorem stepStar_sound
    (I : OSLFNTTWMInterface relEnv State Query)
    {W : State} {p q : Pattern}
    (hW : I.side W)
    (hstar : OSLFTheoryStepStar relEnv p q) :
    WMStrengthObligation State Query W (I.encode p) (I.encode q) := by
  induction hstar with
  | refl =>
      exact le_rfl
  | tail hxy hyz ih =>
      exact le_trans ih (I.step_sound hW hyz)

end OSLFNTTWMInterface

/-- Lift an evidence-level interface to a strength-level interface when the
strength view is known to be monotone with respect to evidence under the given
side-condition. -/
def OSLFNTTWMEvidenceInterface.to_strengthInterface
    {relEnv : RelationEnv}
    {State Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (I : OSLFNTTWMEvidenceInterface relEnv State Query)
    (hStrengthMono :
      ∀ {W : State} {q₁ q₂ : Query},
        I.side W →
        BinaryWorldModel.evidence (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.evidence (State := State) (Query := Query) W q₂ →
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂) :
    OSLFNTTWMInterface relEnv State Query where
  encode := I.encode
  side := I.side
  step_sound := by
    intro W p q hW hstep
    exact hStrengthMono hW (I.step_sound hW hstep)

variable {State Query : Type*}
variable [EvidenceType State] [BinaryWorldModel State Query]

/-- Package one theory step as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_oslfTheoryStep
    {relEnv : RelationEnv}
    (I : OSLFNTTWMInterface relEnv State Query)
    {p q : Pattern}
    (hstep : OSLFTheoryStep relEnv p q) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode p
  conclusion := I.encode q
  sound := by
    intro W hW
    exact I.step_sound hW hstep

/-- Package a theory-star derivation as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_oslfTheoryStepStar
    {relEnv : RelationEnv}
    (I : OSLFNTTWMInterface relEnv State Query)
    {p q : Pattern}
    (hstar : OSLFTheoryStepStar relEnv p q) :
    WMConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode p
  conclusion := I.encode q
  sound := by
    intro W hW
    exact I.stepStar_sound hW hstar

/-- Package one theory step as a state-indexed WM evidence consequence rule. -/
def wmEvidenceConsequenceRuleOn_of_oslfTheoryStep
    {relEnv : RelationEnv}
    (I : OSLFNTTWMEvidenceInterface relEnv State Query)
    {p q : Pattern}
    (hstep : OSLFTheoryStep relEnv p q) :
    WMEvidenceConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode p
  conclusion := I.encode q
  sound := by
    intro W hW
    exact I.step_sound hW hstep

/-- Package a theory-star derivation as a state-indexed WM evidence consequence
rule. -/
def wmEvidenceConsequenceRuleOn_of_oslfTheoryStepStar
    {relEnv : RelationEnv}
    (I : OSLFNTTWMEvidenceInterface relEnv State Query)
    {p q : Pattern}
    (hstar : OSLFTheoryStepStar relEnv p q) :
    WMEvidenceConsequenceRuleOn State Query where
  side := I.side
  premise := I.encode p
  conclusion := I.encode q
  sound := by
    intro W hW
    exact I.stepStar_sound hW hstar

/-- Promote an evidence-level consequence rule to a strength-level WM rule under
side-conditioned evidence->strength transport. -/
def WMEvidenceConsequenceRuleOn.toStrengthRuleOn
    (r : WMEvidenceConsequenceRuleOn State Query)
    (hStrengthMono :
      ∀ {W : State} {q₁ q₂ : Query},
        r.side W →
        BinaryWorldModel.evidence (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.evidence (State := State) (Query := Query) W q₂ →
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂) :
    WMConsequenceRuleOn State Query where
  side := r.side
  premise := r.premise
  conclusion := r.conclusion
  sound := by
    intro W hW
    exact hStrengthMono hW (r.sound hW)

/-- Rule pools over evidence-level consequence rules. -/
abbrev WMEvidenceRuleSet
    (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query] :=
  Set (WMEvidenceConsequenceRuleOn State Query)

/-- Convert an evidence-rule pool into a strength-rule pool using a global
evidence->strength transport law. -/
def WMEvidenceRuleSet.toStrengthRuleSet
    (R : WMEvidenceRuleSet State Query)
    (hStrengthMono :
      ∀ {W : State} {q₁ q₂ : Query},
        BinaryWorldModel.evidence (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.evidence (State := State) (Query := Query) W q₂ →
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂) :
    Mettapedia.Logic.PLNWorldModelFixpointClosure.RuleSet State Query :=
  { r | ∃ re ∈ R,
      r = re.toStrengthRuleOn
        (hStrengthMono := fun _hside hle => hStrengthMono hle) }

theorem WMEvidenceRuleSet.mem_toStrengthRuleSet
    (R : WMEvidenceRuleSet State Query)
    (hStrengthMono :
      ∀ {W : State} {q₁ q₂ : Query},
        BinaryWorldModel.evidence (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.evidence (State := State) (Query := Query) W q₂ →
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂)
    {re : WMEvidenceConsequenceRuleOn State Query}
    (hre : re ∈ R) :
    re.toStrengthRuleOn
      (hStrengthMono := fun _hside hle => hStrengthMono hle)
      ∈ WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono := by
  exact ⟨re, hre, rfl⟩

/-- Rule-pool closure lemma directly consumable after converting an evidence-rule
pool to WM consequence constructors. -/
theorem immediateIter_subset_leastRuleClosure_of_evidenceRuleSet
    (R : WMEvidenceRuleSet State Query)
    (hStrengthMono :
      ∀ {W : State} {q₁ q₂ : Query},
        BinaryWorldModel.evidence (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.evidence (State := State) (Query := Query) W q₂ →
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂)
    (W : State) (seed : Set Query) (n : ℕ) :
    Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter
      (State := State) (Query := Query)
      (R := WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono)
      (W := W) (seed := seed) n
      ⊆
    Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure
      (State := State) (Query := Query)
      (R := WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono)
      (W := W) (seed := seed) := by
  exact
    Mettapedia.Logic.PLNWorldModelFixpointClosure.immediateIter_subset_leastRuleClosure
      (State := State) (Query := Query)
      (R := WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono)
      (W := W) (seed := seed) n

/-- Rule-closure lemma directly consumable after converting an evidence-rule
pool to WM consequence constructors. -/
theorem leastRuleClosure_rule_closed_of_evidenceRuleSet
    (R : WMEvidenceRuleSet State Query)
    (hStrengthMono :
      ∀ {W : State} {q₁ q₂ : Query},
        BinaryWorldModel.evidence (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.evidence (State := State) (Query := Query) W q₂ →
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂)
    (W : State) (seed : Set Query)
    {re : WMEvidenceConsequenceRuleOn State Query}
    (hre : re ∈ R)
    (hside : re.side W)
    (hprem :
      re.premise ∈
        Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Query)
          (R := WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono)
          (W := W) (seed := seed)) :
    re.conclusion ∈
      Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure
        (State := State) (Query := Query)
        (R := WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono)
        (W := W) (seed := seed) := by
  let r : WMConsequenceRuleOn State Query :=
    re.toStrengthRuleOn
      (hStrengthMono := fun _hside hle => hStrengthMono hle)
  have hr : r ∈
      WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono := by
    exact WMEvidenceRuleSet.mem_toStrengthRuleSet
      (State := State) (Query := Query)
      (R := R) (hStrengthMono := hStrengthMono) hre
  have hside' : r.side W := hside
  have hprem' :
      r.premise ∈
        Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Query)
          (R := WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono)
          (W := W) (seed := seed) := hprem
  have hconc' :=
    Mettapedia.Logic.PLNWorldModelFixpointClosure.leastRuleClosure_rule_closed
      (State := State) (Query := Query)
      (R := WMEvidenceRuleSet.toStrengthRuleSet (State := State) (Query := Query) R hStrengthMono)
      (W := W) (seed := seed) (r := r) hr hside' hprem'
  simpa [r, WMEvidenceConsequenceRuleOn.toStrengthRuleOn] using hconc'

/-- Direct star-wrapper: package a theory-star derivation as a WM consequence
rule by first building an evidence-rule and then applying evidence->strength
transport. -/
def wmConsequenceRuleOn_of_oslfTheoryStepStar_viaEvidence
    {relEnv : RelationEnv}
    (I : OSLFNTTWMEvidenceInterface relEnv State Query)
    (hStrengthMono :
      ∀ {W : State} {q₁ q₂ : Query},
        I.side W →
        BinaryWorldModel.evidence (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.evidence (State := State) (Query := Query) W q₂ →
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₁ ≤
          BinaryWorldModel.queryStrength (State := State) (Query := Query) W q₂)
    {p q : Pattern}
    (hstar : OSLFTheoryStepStar relEnv p q) :
    WMConsequenceRuleOn State Query :=
  (wmEvidenceConsequenceRuleOn_of_oslfTheoryStepStar
      (State := State) (Query := Query) (I := I) hstar).toStrengthRuleOn
    (hStrengthMono := hStrengthMono)

section FormulaEvidenceFragment

/-- Pointwise evidence model used for semE-induced closure in this fragment. -/
abbrev SemEState := Pattern → Mettapedia.Logic.EvidenceQuantale.BinaryEvidence
/-- Query type for the semE pointwise model. -/
abbrev SemEQuery := Pattern

noncomputable instance semEStateEvidenceType : EvidenceType SemEState := by
  exact { toAddCommMonoid := inferInstance }

instance semEStateWorldModel : BinaryWorldModel SemEState SemEQuery where
  evidence W q := W q
  evidence_add W₁ W₂ q := by
    simp

/-- OSLF formulas for which we prove one-step evidence monotonicity from
atom-level step monotonicity. This intentionally excludes implication and modal
operators because those require additional assumptions. -/
inductive StepEvidenceMonotoneFragment : OSLFFormula → Prop where
  | top : StepEvidenceMonotoneFragment .top
  | bot : StepEvidenceMonotoneFragment .bot
  | atom (a : String) : StepEvidenceMonotoneFragment (.atom a)
  | and {φ ψ : OSLFFormula} :
      StepEvidenceMonotoneFragment φ →
      StepEvidenceMonotoneFragment ψ →
      StepEvidenceMonotoneFragment (.and φ ψ)
  | or {φ ψ : OSLFFormula} :
      StepEvidenceMonotoneFragment φ →
      StepEvidenceMonotoneFragment ψ →
      StepEvidenceMonotoneFragment (.or φ ψ)

/-- One-step evidence monotonicity for the positive fragment
`top/bot/atom/and/or`, derived from atom-level step monotonicity. -/
theorem semE_step_mono_of_atom_step_mono
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        I a p ≤ I a q)
    {φ : OSLFFormula}
    (hφ : StepEvidenceMonotoneFragment φ)
    {p q : Pattern}
    (hstep : OSLFTheoryStep relEnv p q) :
    semE (OSLFTheoryStep relEnv) I φ p ≤
      semE (OSLFTheoryStep relEnv) I φ q := by
  induction hφ generalizing p q with
  | top =>
      simp [semE_top]
  | bot =>
      simp [semE_bot]
  | atom a =>
      simpa [semE_atom] using hAtom a hstep
  | and hφ hψ ihφ ihψ =>
      exact inf_le_inf (ihφ hstep) (ihψ hstep)
  | or hφ hψ ihφ ihψ =>
      exact sup_le_sup (ihφ hstep) (ihψ hstep)

/-- Implication step-monotonicity from explicit antecedent/consequent transport:
if antecedent evidence is antitone and consequent evidence is monotone along
the step, implication evidence is monotone. -/
theorem semE_step_mono_imp_of
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula)
    {p q : Pattern}
    (hAnte : semE (OSLFTheoryStep relEnv) I φ q ≤ semE (OSLFTheoryStep relEnv) I φ p)
    (hCons : semE (OSLFTheoryStep relEnv) I ψ p ≤ semE (OSLFTheoryStep relEnv) I ψ q) :
    semE (OSLFTheoryStep relEnv) I (.imp φ ψ) p ≤
      semE (OSLFTheoryStep relEnv) I (.imp φ ψ) q := by
  simpa [semE_imp] using himp_le_himp hAnte hCons

/-- Diamond step-monotonicity under successor-set inclusion:
if every one-step successor of `p` is also a one-step successor of `q`, then
diamond evidence at `p` is below diamond evidence at `q`. -/
theorem semE_step_mono_dia_of_successor_inclusion
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (φ : OSLFFormula)
    {p q : Pattern}
    (hSuccIncl :
      ∀ {u : Pattern},
        OSLFTheoryStep relEnv p u →
        OSLFTheoryStep relEnv q u) :
    semE (OSLFTheoryStep relEnv) I (.dia φ) p ≤
      semE (OSLFTheoryStep relEnv) I (.dia φ) q := by
  simp only [semE_dia]
  refine iSup_le ?_
  intro u
  exact semE_dia_le
    (R := OSLFTheoryStep relEnv) (I := I) (φ := φ)
    (p := q) (q := u.1) (h := hSuccIncl u.2)

/-- Box step-monotonicity under predecessor-set inclusion:
if every predecessor of `q` is also a predecessor of `p`, then box evidence at
`p` is below box evidence at `q`. -/
theorem semE_step_mono_box_of_predecessor_inclusion
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (φ : OSLFFormula)
    {p q : Pattern}
    (hPredIncl :
      ∀ {u : Pattern},
        OSLFTheoryStep relEnv u q →
        OSLFTheoryStep relEnv u p) :
    semE (OSLFTheoryStep relEnv) I (.box φ) p ≤
      semE (OSLFTheoryStep relEnv) I (.box φ) q := by
  simp only [semE_box]
  refine le_iInf ?_
  intro u
  exact semE_box_le
    (R := OSLFTheoryStep relEnv) (I := I) (φ := φ)
    (p := p) (q := u.1) (h := hPredIncl u.2)

/-- Canonical pointwise state induced by evidence semantics of a fixed formula. -/
noncomputable def semEState
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (φ : OSLFFormula) : SemEState :=
  fun p => semE (OSLFTheoryStep relEnv) I φ p

/-- The semE-induced pointwise state satisfies evidence-level one-step
monotonicity for formulas in the positive fragment when atoms are step-monotone. -/
theorem semEState_step_evidence_mono
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        I a p ≤ I a q)
    {φ : OSLFFormula}
    (hφ : StepEvidenceMonotoneFragment φ)
    {p q : Pattern}
    (hstep : OSLFTheoryStep relEnv p q) :
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φ) p q := by
  simpa [WMEvidenceObligation, BinaryWorldModel.evidence, semEState] using
    (semE_step_mono_of_atom_step_mono
      (relEnv := relEnv) (I := I) (hAtom := hAtom)
      (hφ := hφ) (p := p) (q := q) hstep)

/-- BinaryEvidence-level interface induced by a semE state over the positive fragment.

`side` pins the state to the canonical semantic state `semEState relEnv I φ`.
This avoids pretending that arbitrary states satisfy formula-specific monotonicity.
-/
def semEFragmentEvidenceInterface
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        I a p ≤ I a q)
    (φ : OSLFFormula)
    (hφ : StepEvidenceMonotoneFragment φ) :
    OSLFNTTWMEvidenceInterface relEnv SemEState SemEQuery where
  encode := fun p => p
  side := fun W => W = semEState relEnv I φ
  step_sound := by
    intro W p q hW hstep
    subst hW
    exact semEState_step_evidence_mono
      (relEnv := relEnv) (I := I) (hAtom := hAtom)
      (hφ := hφ) (p := p) (q := q) hstep

/-- Assumption-indexed fragment extending `StepEvidenceMonotoneFragment` with
controlled implication/diamond/box cases. -/
inductive StepEvidenceMonotoneControlledFragment
    (relEnv : RelationEnv) (I : EvidenceAtomSem) : OSLFFormula → Prop where
  | top : StepEvidenceMonotoneControlledFragment relEnv I .top
  | bot : StepEvidenceMonotoneControlledFragment relEnv I .bot
  | atom (a : String) :
      StepEvidenceMonotoneControlledFragment relEnv I (.atom a)
  | and {φ ψ : OSLFFormula} :
      StepEvidenceMonotoneControlledFragment relEnv I φ →
      StepEvidenceMonotoneControlledFragment relEnv I ψ →
      StepEvidenceMonotoneControlledFragment relEnv I (.and φ ψ)
  | or {φ ψ : OSLFFormula} :
      StepEvidenceMonotoneControlledFragment relEnv I φ →
      StepEvidenceMonotoneControlledFragment relEnv I ψ →
      StepEvidenceMonotoneControlledFragment relEnv I (.or φ ψ)
  | imp {φ ψ : OSLFFormula} :
      StepEvidenceMonotoneControlledFragment relEnv I ψ →
      (∀ {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        semE (OSLFTheoryStep relEnv) I φ q ≤ semE (OSLFTheoryStep relEnv) I φ p) →
      StepEvidenceMonotoneControlledFragment relEnv I (.imp φ ψ)
  | dia {φ : OSLFFormula} :
      StepEvidenceMonotoneControlledFragment relEnv I φ →
      (∀ {p q u : Pattern},
        OSLFTheoryStep relEnv p q →
        OSLFTheoryStep relEnv p u →
        OSLFTheoryStep relEnv q u) →
      StepEvidenceMonotoneControlledFragment relEnv I (.dia φ)
  | box {φ : OSLFFormula} :
      StepEvidenceMonotoneControlledFragment relEnv I φ →
      (∀ {p q u : Pattern},
        OSLFTheoryStep relEnv p q →
        OSLFTheoryStep relEnv u q →
        OSLFTheoryStep relEnv u p) →
      StepEvidenceMonotoneControlledFragment relEnv I (.box φ)

/-- One-step evidence monotonicity for the controlled fragment. -/
theorem semE_step_mono_controlled_of_atom_step_mono
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        I a p ≤ I a q)
    {φ : OSLFFormula}
    (hφ : StepEvidenceMonotoneControlledFragment relEnv I φ)
    {p q : Pattern}
    (hstep : OSLFTheoryStep relEnv p q) :
    semE (OSLFTheoryStep relEnv) I φ p ≤
      semE (OSLFTheoryStep relEnv) I φ q := by
  induction hφ generalizing p q with
  | top =>
      simp [semE_top]
  | bot =>
      simp [semE_bot]
  | atom a =>
      simpa [semE_atom] using hAtom a hstep
  | and hφ hψ ihφ ihψ =>
      exact inf_le_inf (ihφ hstep) (ihψ hstep)
  | or hφ hψ ihφ ihψ =>
      exact sup_le_sup (ihφ hstep) (ihψ hstep)
  | imp hψ hAnte ihψ =>
      exact semE_step_mono_imp_of
        (relEnv := relEnv) (I := I) (φ := _) (ψ := _)
        (hAnte := hAnte hstep) (hCons := ihψ hstep)
  | dia hφ hSucc ihφ =>
      exact semE_step_mono_dia_of_successor_inclusion
        (relEnv := relEnv) (I := I) (φ := _)
        (hSuccIncl := fun hu => hSucc hstep hu)
  | box hφ hPred ihφ =>
      exact semE_step_mono_box_of_predecessor_inclusion
        (relEnv := relEnv) (I := I) (φ := _)
        (hPredIncl := fun hu => hPred hstep hu)

/-- Explicit policy object for controlled semE step monotonicity assumptions.

This factors the previous ad-hoc implication/modal side-conditions into a
reusable contract that can be shared across bridge layers. -/
structure ControlledStepPolicy
    (relEnv : RelationEnv) (I : EvidenceAtomSem) where
  atom_step_mono :
    ∀ (a : String) {p q : Pattern},
      OSLFTheoryStep relEnv p q →
      I a p ≤ I a q
  impAnte : OSLFFormula → Prop
  imp_step_antitone :
    ∀ {φ : OSLFFormula} {p q : Pattern},
      impAnte φ →
      OSLFTheoryStep relEnv p q →
      semE (OSLFTheoryStep relEnv) I φ q ≤ semE (OSLFTheoryStep relEnv) I φ p
  dia_successor_closed :
    ∀ {p q u : Pattern},
      OSLFTheoryStep relEnv p q →
      OSLFTheoryStep relEnv p u →
      OSLFTheoryStep relEnv q u
  box_predecessor_closed :
    ∀ {p q u : Pattern},
      OSLFTheoryStep relEnv p q →
      OSLFTheoryStep relEnv u q →
      OSLFTheoryStep relEnv u p

/-- Controlled fragment indexed by a `ControlledStepPolicy`.

Implication nodes require antecedents tagged by `policy.impAnte`; modal nodes
reuse the global relation-closure guarantees in the policy. -/
inductive StepEvidenceControlledByPolicy
    {relEnv : RelationEnv} {I : EvidenceAtomSem}
    (policy : ControlledStepPolicy relEnv I) : OSLFFormula → Prop where
  | top : StepEvidenceControlledByPolicy policy .top
  | bot : StepEvidenceControlledByPolicy policy .bot
  | atom (a : String) : StepEvidenceControlledByPolicy policy (.atom a)
  | and {φ ψ : OSLFFormula} :
      StepEvidenceControlledByPolicy policy φ →
      StepEvidenceControlledByPolicy policy ψ →
      StepEvidenceControlledByPolicy policy (.and φ ψ)
  | or {φ ψ : OSLFFormula} :
      StepEvidenceControlledByPolicy policy φ →
      StepEvidenceControlledByPolicy policy ψ →
      StepEvidenceControlledByPolicy policy (.or φ ψ)
  | imp {φ ψ : OSLFFormula} :
      StepEvidenceControlledByPolicy policy ψ →
      policy.impAnte φ →
      StepEvidenceControlledByPolicy policy (.imp φ ψ)
  | dia {φ : OSLFFormula} :
      StepEvidenceControlledByPolicy policy φ →
      StepEvidenceControlledByPolicy policy (.dia φ)
  | box {φ : OSLFFormula} :
      StepEvidenceControlledByPolicy policy φ →
      StepEvidenceControlledByPolicy policy (.box φ)

namespace StepEvidenceControlledByPolicy

/-- Turn a policy-indexed controlled-fragment witness into the existing
assumption-indexed fragment witness. -/
theorem toAssumptionFragment
    {relEnv : RelationEnv} {I : EvidenceAtomSem}
    {policy : ControlledStepPolicy relEnv I}
    {φ : OSLFFormula}
    (hφ : StepEvidenceControlledByPolicy policy φ) :
    StepEvidenceMonotoneControlledFragment relEnv I φ := by
  induction hφ with
  | top =>
      exact .top
  | bot =>
      exact .bot
  | atom a =>
      exact .atom a
  | and hφ hψ ihφ ihψ =>
      exact .and ihφ ihψ
  | or hφ hψ ihφ ihψ =>
      exact .or ihφ ihψ
  | imp hψ hAnte ihψ =>
      refine .imp ihψ ?_
      intro p q hstep
      exact policy.imp_step_antitone hAnte hstep
  | dia hφ ihφ =>
      refine .dia ihφ ?_
      intro p q u hstep hpu
      exact policy.dia_successor_closed hstep hpu
  | box hφ ihφ =>
      refine .box ihφ ?_
      intro p q u hstep huq
      exact policy.box_predecessor_closed hstep huq

end StepEvidenceControlledByPolicy

/-- One-step semE monotonicity directly from a `ControlledStepPolicy` and its
policy-indexed controlled fragment. -/
theorem semE_step_mono_of_policy
    {relEnv : RelationEnv}
    {I : EvidenceAtomSem}
    (policy : ControlledStepPolicy relEnv I)
    {φ : OSLFFormula}
    (hφ : StepEvidenceControlledByPolicy policy φ)
    {p q : Pattern}
    (hstep : OSLFTheoryStep relEnv p q) :
    semE (OSLFTheoryStep relEnv) I φ p ≤
      semE (OSLFTheoryStep relEnv) I φ q := by
  exact semE_step_mono_controlled_of_atom_step_mono
    (relEnv := relEnv) (I := I)
    (hAtom := policy.atom_step_mono)
    (hφ := StepEvidenceControlledByPolicy.toAssumptionFragment hφ)
    hstep

/-- Unified semE-fragment endpoint:
combines the categorical formula endpoint package with one-step evidence
closure on the same semantic state. -/
theorem semE_fragment_formulaCategoricalEndpoint_step
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (I : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        I a p ≤ I a q)
    (φ : OSLFFormula)
    (hφ : StepEvidenceMonotoneFragment φ)
    (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstep : OSLFTheoryStep relEnv p q)
    (φcat : H.query Bobj) :
    FormulaCategoricalEndpointBridge
      (State := SemEState) (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (relEnv := relEnv) (W := semEState relEnv I φ)
      (queryOfAtom := queryOfAtom) (φf := φ) (Xobj := Xobj)
      (X := X) (φcat := φcat)
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φ) p q := by
  constructor
  · exact formulaCategoricalEndpointBridge_of_oslf_formula_ntt_graph_triangle
      (State := SemEState) (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (relEnv := relEnv) (W := semEState relEnv I φ)
      (queryOfAtom := queryOfAtom) (φf := φ) (Xobj := Xobj)
      (X := X) (φcat := φcat)
  · exact semEState_step_evidence_mono
      (relEnv := relEnv) (I := I) (hAtom := hAtom)
      (hφ := hφ) (p := p) (q := q) hstep

/-- Star-closure variant of `semE_fragment_formulaCategoricalEndpoint_step`.

The categorical endpoint component is formula-structural (state/query surface),
while the evidence closure component is transported along `OSLFTheoryStepStar`
through `semEFragmentEvidenceInterface`. -/
theorem semE_fragment_formulaCategoricalEndpoint_stepStar
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (I : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        I a p ≤ I a q)
    (φ : OSLFFormula)
    (hφ : StepEvidenceMonotoneFragment φ)
    (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    FormulaCategoricalEndpointBridge
      (State := SemEState) (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (relEnv := relEnv) (W := semEState relEnv I φ)
      (queryOfAtom := queryOfAtom) (φf := φ) (Xobj := Xobj)
      (X := X) (φcat := φcat)
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φ) p q := by
  constructor
  · exact formulaCategoricalEndpointBridge_of_oslf_formula_ntt_graph_triangle
      (State := SemEState) (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (relEnv := relEnv) (W := semEState relEnv I φ)
      (queryOfAtom := queryOfAtom) (φf := φ) (Xobj := Xobj)
      (X := X) (φcat := φcat)
  · let Iev := semEFragmentEvidenceInterface
      (relEnv := relEnv) (I := I) (hAtom := hAtom) (φ := φ) hφ
    have hSide : Iev.side (semEState relEnv I φ) := rfl
    exact Iev.stepStar_sound hSide hstar

/-- Policy-driven semE evidence interface on the canonical semantic state.

This removes ad-hoc monotonicity assumptions from endpoint consumers by
packaging all required controlled-fragment assumptions in `ControlledStepPolicy`.
-/
def semEPolicyEvidenceInterface
    (relEnv : RelationEnv)
    (I : EvidenceAtomSem)
    (policy : ControlledStepPolicy relEnv I)
    (φ : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy φ) :
    OSLFNTTWMEvidenceInterface relEnv SemEState SemEQuery where
  encode := fun p => p
  side := fun W => W = semEState relEnv I φ
  step_sound := by
    intro W p q hW hstep
    subst hW
    exact semE_step_mono_of_policy
      (policy := policy) (hφ := hφ) hstep

/-- Policy-driven star-closure endpoint:
categorical formula endpoint + semE evidence closure transported along
`OSLFTheoryStepStar` via a policy-indexed interface. -/
theorem semE_fragment_formulaCategoricalEndpoint_stepStar_of_policy
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (I : EvidenceAtomSem)
    (policy : ControlledStepPolicy relEnv I)
    (φ : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy φ)
    (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    (p q : Pattern)
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    FormulaCategoricalEndpointBridge
      (State := SemEState) (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (relEnv := relEnv) (W := semEState relEnv I φ)
      (queryOfAtom := queryOfAtom) (φf := φ) (Xobj := Xobj)
      (X := X) (φcat := φcat)
    ∧
    WMEvidenceObligation SemEState SemEQuery
      (semEState relEnv I φ) p q := by
  constructor
  · exact formulaCategoricalEndpointBridge_of_oslf_formula_ntt_graph_triangle
      (State := SemEState) (H := H)
      (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
      (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
      (relEnv := relEnv) (W := semEState relEnv I φ)
      (queryOfAtom := queryOfAtom) (φf := φ) (Xobj := Xobj)
      (X := X) (φcat := φcat)
  · let Iev := semEPolicyEvidenceInterface
      (relEnv := relEnv) (I := I) (policy := policy) (φ := φ) hφ
    have hSide : Iev.side (semEState relEnv I φ) := rfl
    exact Iev.stepStar_sound hSide hstar

/-- Build an evidence-rule constructor directly from the semE categorical
endpoint + theory-star closure package. -/
def semE_fragment_evidenceRuleOn_of_formulaCategoricalEndpoint_stepStar
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (I : EvidenceAtomSem)
    (hAtom :
      ∀ (a : String) {p q : Pattern},
        OSLFTheoryStep relEnv p q →
        I a p ≤ I a q)
    (φ : OSLFFormula)
    (hφ : StepEvidenceMonotoneFragment φ)
    (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    {p q : Pattern}
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    WMEvidenceConsequenceRuleOn SemEState SemEQuery where
  side := fun W => W = semEState relEnv I φ
  premise := p
  conclusion := q
  sound := by
    intro W hW
    subst hW
    exact
      (semE_fragment_formulaCategoricalEndpoint_stepStar
        (H := H)
        (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
        (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
        (relEnv := relEnv) (queryOfAtom := queryOfAtom)
        (I := I) (hAtom := hAtom) (φ := φ) (hφ := hφ)
        (Xobj := Xobj) (X := X) (p := p) (q := q)
        (hstar := hstar) (φcat := φcat)).2

/-- Policy-driven evidence-rule constructor from the semE categorical star
endpoint package. -/
def semE_fragment_evidenceRuleOn_of_formulaCategoricalEndpoint_stepStar_of_policy
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine SemEState)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : RelationEnv)
    (queryOfAtom : String → Pattern → Pattern)
    (I : EvidenceAtomSem)
    (policy : ControlledStepPolicy relEnv I)
    (φ : OSLFFormula)
    (hφ : StepEvidenceControlledByPolicy policy φ)
    (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj
      Mettapedia.OSLF.Framework.MeTTaToNTT.mettaFull)}
    {p q : Pattern}
    (hstar : OSLFTheoryStepStar relEnv p q)
    (φcat : H.query Bobj) :
    WMEvidenceConsequenceRuleOn SemEState SemEQuery where
  side := fun W => W = semEState relEnv I φ
  premise := p
  conclusion := q
  sound := by
    intro W hW
    subst hW
    exact
      (semE_fragment_formulaCategoricalEndpoint_stepStar_of_policy
        (H := H)
        (pi1 := pi1) (pi2 := pi2) (fcat := fcat) (gcat := gcat)
        (hpb := hpb) (hmfcat := hmfcat) (hmpi2 := hmpi2)
        (relEnv := relEnv) (queryOfAtom := queryOfAtom)
        (I := I) (policy := policy) (φ := φ) (hφ := hφ)
        (Xobj := Xobj) (X := X) (p := p) (q := q)
        (hstar := hstar) (φcat := φcat)).2

/-- Negative semE guardrail:
evidence monotonicity alone does not force strength monotonicity, even on a
canonical semE-induced state. This blocks unconditional removal of
evidence->strength assumptions. -/
theorem semEState_evidence_mono_not_strength_mono :
    ∃ (relEnv : RelationEnv) (I : EvidenceAtomSem) (p q : Pattern),
      WMEvidenceObligation SemEState SemEQuery
        (semEState relEnv I (.atom "a")) p q
      ∧
      ¬ WMStrengthObligation SemEState SemEQuery
        (semEState relEnv I (.atom "a")) p q := by
  let p : Pattern := .fvar "p"
  let q : Pattern := .fvar "q"
  let hi : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence := ⟨1, 0⟩
  let lo : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence := ⟨1, 1⟩
  let I : EvidenceAtomSem :=
    fun _ r => if r = p then hi else if r = q then lo else (⊥ : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
  let relEnv : RelationEnv := RelationEnv.empty
  refine ⟨relEnv, I, p, q, ?_, ?_⟩
  · change hi ≤ lo
    simp [hi, lo, Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.le_def]
  · intro h
    have hle' :
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength hi ≤
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength lo := by
      simpa [WMStrengthObligation, BinaryWorldModel.queryStrength, semEState, semE_atom, I, p, q, hi, lo] using h
    have hnum : ((1 : ENNReal) + 1) ≤ (1 : ENNReal) := by
      simpa [hi, lo,
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength,
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.total] using hle'
    have hfalse : ¬ (((1 : ENNReal) + 1) ≤ (1 : ENNReal)) := by
      norm_num
    exact hfalse hnum

end FormulaEvidenceFragment

section ConcretePointwiseModel

/-- Concrete state/query model for closure testing:
state is a pointwise evidence assignment over patterns, and queries are patterns. -/
abbrev StepState := Pattern → Mettapedia.Logic.EvidenceQuantale.BinaryEvidence
abbrev StepQuery := Pattern

noncomputable instance stepStateEvidenceType : EvidenceType StepState := by
  exact { toAddCommMonoid := inferInstance }

instance stepStateWorldModel : BinaryWorldModel StepState StepQuery where
  evidence W q := W q
  evidence_add W₁ W₂ q := by
    simp

/-- Side-condition used by the concrete pointwise model:
the state is monotone in query-strength along OSLF one-step reduction. -/
def pointwiseStepSide (relEnv : RelationEnv) (W : StepState) : Prop :=
  ∀ {p q : Pattern},
    OSLFTheoryStep relEnv p q →
      BinaryWorldModel.queryStrength (State := StepState) (Query := StepQuery) W p ≤
        BinaryWorldModel.queryStrength (State := StepState) (Query := StepQuery) W q

/-- Canonical concrete interface instance for the pointwise model. -/
def pointwiseStepInterface (relEnv : RelationEnv) :
    OSLFNTTWMInterface relEnv StepState StepQuery where
  encode := fun p => p
  side := pointwiseStepSide relEnv
  step_sound := by
    intro W p q hW hstep
    exact hW hstep

/-- Negative guardrail: step-soundness is not automatic without a side-condition.
Given any concrete reduction step `p ↦ q`, there exists a pointwise state that
violates step monotonicity of query-strength. -/
theorem pointwiseStepSide_not_automatic
    (relEnv : RelationEnv)
    {p q : Pattern}
    (hneq : p ≠ q)
    (hstep : OSLFTheoryStep relEnv p q) :
    ∃ W : StepState, ¬ pointwiseStepSide relEnv W := by
  classical
  let hi : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence := ⟨1, 0⟩
  let lo : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence := ⟨1, 1⟩
  let W : StepState :=
    fun r => if r = p then hi else if r = q then lo else (⊥ : Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
  refine ⟨W, ?_⟩
  intro hmono
  have hle :
      BinaryWorldModel.queryStrength (State := StepState) (Query := StepQuery) W p ≤
        BinaryWorldModel.queryStrength (State := StepState) (Query := StepQuery) W q :=
    hmono hstep
  have hneq' : q ≠ p := by
    intro hqp
    exact hneq hqp.symm
  have hWp : W p = hi := by
    simp [W]
  have hWq : W q = lo := by
    simp [W, hneq']
  have hle' :
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength hi ≤
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength lo := by
    simpa [BinaryWorldModel.queryStrength, stepStateWorldModel, hWp, hWq] using hle
  have hnum : ((1 : ENNReal) + 1) ≤ (1 : ENNReal) := by
    simpa [hi, lo,
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.toStrength,
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence.total] using hle'
  have hfalse : ¬ (((1 : ENNReal) + 1) ≤ (1 : ENNReal)) := by
    norm_num
  exact hfalse hnum

end ConcretePointwiseModel

end Mettapedia.OSLF.Framework.OSLFNTTTheoryClosure
