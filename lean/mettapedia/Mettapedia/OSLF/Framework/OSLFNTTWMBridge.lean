import Mettapedia.OSLF.Framework.MeTTaLegacyToNTT
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNWorldModelCategoricalBridge
import Mettapedia.Logic.OSLFEvidenceSemantics
import Mettapedia.OSLF.Framework.ToposReduction

/-!
# OSLF -> NTT -> WM Triangle Bridge

This module exposes a concrete atom-level endpoint for the composed route:

- OSLF atom evidence semantics,
- MeTTaFullLegacy-to-NTT evidence lifting, and
- WM query-judgment obligations.

It is intentionally assumption-parameterized and does not change PureKernel/
OSLF semantics.
-/

namespace Mettapedia.OSLF.Framework.OSLFNTTWMBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Formula
open Mettapedia.CategoryTheory.PLNInstance
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWMOSLFBridge
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.OSLF.Framework
open Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine

section AtomTriangle

variable {State : Type*}
variable [EvidenceType State] [BinaryWorldModel State Pattern]

/--
Atom-level OSLF -> NTT -> WM triangle endpoint.

From a ξPLN evidence derivation for atom `(a, p)`, we get all three views:

1. OSLF atom semantics computes the derived evidence.
2. The NTT lifting of the same atom has matching evidence component.
3. The encoded WM query judgment holds for the derived evidence.
-/
theorem oslf_atom_ntt_wm_triangle
    (relEnv : MeTTaIL.Engine.RelationEnv)
    (W : State)
    (Ξ : XiPLN (State := State) (Query := Pattern))
    (a : String) (p : Pattern) (X : PLNObj) (e : BinaryEvidence)
    (hDer : XiDerivesAtomEvidence Ξ W a p e)
    (hW : WMJudgment W) :
    semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
      (wmEvidenceAtomSemQ W Ξ.queryOfAtom) (.atom a) p = e
    ∧ (MeTTaToNTT.mettaFormulaToNT relEnv W Ξ.queryOfAtom (.atom a) p X).2 = e
    ∧ WMQueryJudgment W (Ξ.queryOfAtom a p) e := by
  have hSem :
      semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
        (wmEvidenceAtomSemQ W Ξ.queryOfAtom) (.atom a) p = e :=
    xiDerivesAtomEvidence_sound (Ξ := Ξ)
      (R := Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
      hDer

  have hAtomEq : BinaryWorldModel.evidence W (Ξ.queryOfAtom a p) = e := by
    simpa [wmEvidenceAtomSemQ] using hSem

  have hQ : WMQueryJudgment W (Ξ.queryOfAtom a p) e :=
    xiDerivesAtomEvidence_to_wmQueryJudgment (Ξ := Ξ) hDer hW

  refine ⟨hSem, ?_, hQ⟩
  calc
    (MeTTaToNTT.mettaFormulaToNT relEnv W Ξ.queryOfAtom (.atom a) p X).2
        = MeTTaToNTT.mettaSemE relEnv W Ξ.queryOfAtom (.atom a) p := by
            rfl
    _ = BinaryWorldModel.evidence W (Ξ.queryOfAtom a p) := by
          simp [MeTTaToNTT.mettaSemE, wmEvidenceAtomSem]
    _ = e := hAtomEq

/--
Categorical-surface wrapper: same atom-level endpoint, with explicit
WM categorical endpoint surface argument to align with WM bridge APIs.
-/
theorem oslf_atom_ntt_wm_triangle_categorical
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    (_hcat :
      Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointSurface (H := H))
    {XH : H.Obj} (_φc : H.query XH)
    (relEnv : MeTTaIL.Engine.RelationEnv)
    (W : State)
    (Ξ : XiPLN (State := State) (Query := Pattern))
    (a : String) (p : Pattern) (X : PLNObj) (e : BinaryEvidence)
    (hDer : XiDerivesAtomEvidence Ξ W a p e)
    (hW : WMJudgment W) :
    semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
      (wmEvidenceAtomSemQ W Ξ.queryOfAtom) (.atom a) p = e
    ∧ (MeTTaToNTT.mettaFormulaToNT relEnv W Ξ.queryOfAtom (.atom a) p X).2 = e
    ∧ WMQueryJudgment W (Ξ.queryOfAtom a p) e :=
  oslf_atom_ntt_wm_triangle
    (relEnv := relEnv) (W := W) (Ξ := Ξ)
    (a := a) (p := p) (X := X) (e := e) hDer hW

end AtomTriangle

section FormulaTriangle

variable {State : Type*}
variable [EvidenceType State] [BinaryWorldModel State Pattern]

/--
Formula-level OSLF -> NTT evidence-component endpoint.

This is the formula generalization of the atom `.2` bridge: the evidence
component of `mettaFormulaToNT` is exactly OSLF `semE`.
-/
theorem oslf_formula_ntt_evidence_component
    (relEnv : MeTTaIL.Engine.RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (p : Pattern) (X : PLNObj) :
    semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
      (wmEvidenceAtomSemQ W queryOfAtom) φf p
      =
    (MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf p X).2 := by
  simp [MeTTaToNTT.mettaSemE, wmEvidenceAtomSemQ_pattern_eq]

/--
Formula-level explicit reduction-graph witness transport for diamond predicates.

This makes the graph witness explicit at formula level (predicate over target
states given by formula evidence).
-/
theorem oslf_dia_formula_graph_witness_transport
    (relEnv : MeTTaIL.Engine.RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)}
    (p : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing
        relEnv MeTTaToNTT.mettaFull
        (fun q =>
          semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
            (wmEvidenceAtomSemQ W queryOfAtom) φf q ≠ ⊥)
        p
      ↔
    ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
        relEnv MeTTaToNTT.mettaFull).Edge.obj X,
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
        relEnv MeTTaToNTT.mettaFull).source.app X e).down = p ∧
      (semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
        (wmEvidenceAtomSemQ W queryOfAtom) φf
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
          relEnv MeTTaToNTT.mettaFull).target.app X e).down ≠ ⊥) := by
  simpa using
    (Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphStep
      (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
      (relEnv := relEnv) (lang := MeTTaToNTT.mettaFull)
      (X := X)
      (φ := fun q =>
        semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
          (wmEvidenceAtomSemQ W queryOfAtom) φf q ≠ ⊥)
      (p := p))

/--
Formula-level NTT-view graph witness transport.

Same graph witness theorem as `oslf_dia_formula_graph_witness_transport`, now
stated directly over `mettaFormulaToNT ... .2`.
-/
theorem oslf_dia_formula_ntt_graph_witness_transport
    (relEnv : MeTTaIL.Engine.RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)}
    (p : Pattern) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing
        relEnv MeTTaToNTT.mettaFull
        (fun q =>
          (MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf q Xobj).2 ≠ ⊥)
        p
      ↔
    ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
        relEnv MeTTaToNTT.mettaFull).Edge.obj X,
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
        relEnv MeTTaToNTT.mettaFull).source.app X e).down = p ∧
      ((MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
          relEnv MeTTaToNTT.mettaFull).target.app X e).down
        Xobj).2 ≠ ⊥) := by
  simpa [MeTTaToNTT.mettaFormulaToNT_snd, MeTTaToNTT.mettaSemE] using
    (oslf_dia_formula_graph_witness_transport
      (relEnv := relEnv) (W := W) (queryOfAtom := queryOfAtom)
      (φf := φf) (X := X) (p := p))

/--
Unified formula-level endpoint:
1. OSLF formula evidence agrees with NTT evidence component.
2. Diamond-style transport has explicit reduction-graph witnesses.
-/
theorem oslf_formula_ntt_graph_triangle
    (relEnv : MeTTaIL.Engine.RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)}
    (p : Pattern) :
    semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
      (wmEvidenceAtomSemQ W queryOfAtom) φf p
      =
      (MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf p Xobj).2
    ∧
    (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing
        relEnv MeTTaToNTT.mettaFull
        (fun q =>
          (MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf q Xobj).2 ≠ ⊥)
        p
      ↔
    ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
        relEnv MeTTaToNTT.mettaFull).Edge.obj X,
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
        relEnv MeTTaToNTT.mettaFull).source.app X e).down = p ∧
      ((MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
          relEnv MeTTaToNTT.mettaFull).target.app X e).down
        Xobj).2 ≠ ⊥)) := by
  constructor
  · exact oslf_formula_ntt_evidence_component
      (relEnv := relEnv) (W := W) (queryOfAtom := queryOfAtom)
      (φf := φf) (p := p) (X := Xobj)
  · exact oslf_dia_formula_ntt_graph_witness_transport
      (relEnv := relEnv) (W := W) (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := X) (p := p)

end FormulaTriangle

section FormulaCategoricalEndpoint

variable {State : Type*}
variable [EvidenceType State] [BinaryWorldModel State Pattern]

/-- Formula-level endpoint surface reused by categorical wrappers. -/
abbrev FormulaGraphEndpoint
    (relEnv : MeTTaIL.Engine.RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)}
    (p : Pattern) : Prop :=
  semE (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv MeTTaToNTT.mettaFull)
      (wmEvidenceAtomSemQ W queryOfAtom) φf p
      =
      (MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf p Xobj).2
    ∧
    (Mettapedia.OSLF.Framework.TypeSynthesis.langDiamondUsing
        relEnv MeTTaToNTT.mettaFull
        (fun q =>
          (MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf q Xobj).2 ≠ ⊥)
        p
      ↔
    ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
        relEnv MeTTaToNTT.mettaFull).Edge.obj X,
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
        relEnv MeTTaToNTT.mettaFull).source.app X e).down = p ∧
      ((MeTTaToNTT.mettaFormulaToNT relEnv W queryOfAtom φf
        ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)
          relEnv MeTTaToNTT.mettaFull).target.app X e).down
        Xobj).2 ≠ ⊥))

/--
Formula-level unified categorical endpoint:

1. OSLF formula evidence agrees with the NTT evidence component and carries the
   explicit reduction-graph witness transport for `◇`.
2. The same state/query surface satisfies the WM institution+Beck-Chevalley
   endpoint statement.
-/
theorem oslf_formula_ntt_graph_triangle_categorical
    (H : Mettapedia.Logic.PLNWorldModelHyperdoctrine.WMHyperdoctrine State)
    {P Aobj Bobj D : H.Obj}
    (pi1 : P ⟶ Aobj) (pi2 : P ⟶ Bobj) (fcat : Aobj ⟶ D) (gcat : Bobj ⟶ D)
    (hpb : CategoryTheory.IsPullback pi1 pi2 fcat gcat)
    (hmfcat : CategoryTheory.Mono fcat) (hmpi2 : CategoryTheory.Mono pi2)
    (relEnv : MeTTaIL.Engine.RelationEnv)
    (W : State)
    (queryOfAtom : String → Pattern → Pattern)
    (φf : OSLFFormula) (Xobj : PLNObj)
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj MeTTaToNTT.mettaFull)}
    (p : Pattern)
    (φcat : H.query Bobj) :
    FormulaGraphEndpoint
      (State := State) (relEnv := relEnv) (W := W)
      (queryOfAtom := queryOfAtom) (φf := φf) (Xobj := Xobj) (X := X) (p := p)
      ∧
    EndpointStatement (H := H) pi1 pi2 fcat gcat W φcat := by
  letI : CategoryTheory.Mono fcat := hmfcat
  letI : CategoryTheory.Mono pi2 := hmpi2
  constructor
  · exact oslf_formula_ntt_graph_triangle
      (relEnv := relEnv) (W := W) (queryOfAtom := queryOfAtom)
      (φf := φf) (Xobj := Xobj) (X := X) (p := p)
  · exact institution_beckChevalley_endpoint
      (H := H) pi1 pi2 fcat gcat hpb W φcat

end FormulaCategoricalEndpoint

end Mettapedia.OSLF.Framework.OSLFNTTWMBridge
