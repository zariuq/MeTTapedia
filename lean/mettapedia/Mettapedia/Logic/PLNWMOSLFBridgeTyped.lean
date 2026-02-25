import Mettapedia.Logic.PLNWorldModelTyped
import Mettapedia.Logic.OSLFEvidenceSemantics

/-!
# PLN ↔ WMΣ ↔ OSLF Bridge (Typed Queries)

Typed variant of `PLNWMOSLFBridge` where WM queries are sort-indexed:
`Query : Srt → Type`.

Atoms are encoded into typed WM queries via:
`queryOfAtom : String → Pattern → Sigma Query`.
-/

namespace Mettapedia.Logic.PLNWMOSLFBridgeTyped

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.OSLFEvidenceSemantics

open scoped ENNReal

/-! ## Core Bridge -/

section CoreBridge

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Atom-evidence semantics from typed WM queries. -/
noncomputable def wmEvidenceAtomSemQSigma
    (W : State) (queryOfAtom : String → Pattern → Sigma Query) : EvidenceAtomSem :=
  fun a p => WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p)

/-- Strength-threshold atom semantics from typed WM queries. -/
noncomputable def thresholdAtomSemOfWMQSigma
    (W : State) (tau : ℝ≥0∞)
    (queryOfAtom : String → Pattern → Sigma Query) : AtomSem :=
  fun a p =>
    tau ≤ Evidence.toStrength
      (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p))

@[simp] theorem semE_atom_wmEvidenceAtomSemQSigma
    (R : Pattern → Pattern → Prop)
    (W : State) (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W queryOfAtom)
      (.atom a) p =
      WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p) := rfl

/-- Typed query judgment gives exact OSLF atom evidence under the encoder. -/
theorem wmQueryJudgmentSigma_semE_atom
    (R : Pattern → Pattern → Prop)
    (W : State) (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern) (e : Evidence)
    (hQ : WorldModelSigma.WMQueryJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      W (queryOfAtom a p) e) :
    semE R (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W queryOfAtom)
      (.atom a) p = e := by
  simp [wmEvidenceAtomSemQSigma, hQ.2]

/-- Typed WM rewrite soundness transferred to OSLF atom evidence. -/
theorem wmRewriteRuleSigma_semE_atom_eq_derive
    (R : Pattern → Pattern → Prop)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion) :
    semE R (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W queryOfAtom)
      (.atom a) p = r.derive W := by
  simp [wmEvidenceAtomSemQSigma, hEnc, (r.sound hSide W).symm]

/-- Typed threshold consequence from an evidence-level rewrite rule. -/
theorem wmRewriteRuleSigma_threshold_atom
    (R : Pattern → Pattern → Prop)
    (r : WorldModelSigma.WMRewriteRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (tau : ℝ≥0∞)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ Evidence.toStrength (r.derive W)) :
    sem R
      (thresholdAtomSemOfWMQSigma (State := State) (Srt := Srt) (Query := Query) W tau queryOfAtom)
      (.atom a) p := by
  show tau ≤ Evidence.toStrength
    (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p))
  rw [hEnc, (r.sound hSide W).symm]
  exact hTau

/-- Typed threshold consequence from a strength-level rewrite rule. -/
theorem wmStrengthRuleSigma_threshold_atom
    (R : Pattern → Pattern → Prop)
    (r : WorldModelSigma.WMStrengthRuleSigma State Srt Query)
    (hSide : r.side) (W : State)
    (tau : ℝ≥0∞)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern)
    (hEnc : queryOfAtom a p = r.conclusion)
    (hTau : tau ≤ r.derive W) :
    sem R
      (thresholdAtomSemOfWMQSigma (State := State) (Srt := Srt) (Query := Query) W tau queryOfAtom)
      (.atom a) p := by
  show tau ≤ Evidence.toStrength
    (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W (queryOfAtom a p))
  rw [hEnc]
  have hs :
      r.derive W =
        Evidence.toStrength
          (WorldModelSigma.evidence (State := State) (Srt := Srt) (Query := Query) W r.conclusion) := by
    simpa [WorldModelSigma.queryStrength] using (r.sound hSide W)
  rw [← hs]
  exact hTau

/-- Revision commutation at atom level for typed query encoders. -/
theorem semE_wm_atom_revision_qsigma
    (R : Pattern → Pattern → Prop)
    (W₁ W₂ : State)
    (queryOfAtom : String → Pattern → Sigma Query)
    (a : String) (p : Pattern) :
    semE R
      (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) (W₁ + W₂) queryOfAtom)
      (.atom a) p =
      semE R
        (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom)
        (.atom a) p +
      semE R
        (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom)
        (.atom a) p := by
  simp [wmEvidenceAtomSemQSigma, WorldModelSigma.evidence_add]

end CoreBridge

/-! ## ξPLNΣ Layer -/

section XiPLNSigma

variable {State Srt : Type*} {Query : Srt → Type*}
variable [EvidenceType State] [WorldModelSigma State Srt Query]

/-- Typed ξPLN package: OSLF atom encoder into typed WM queries plus rule sets. -/
structure XiPLNSigma where
  queryOfAtom : String → Pattern → Sigma Query
  rulesE : Set (WorldModelSigma.WMRewriteRuleSigma State Srt Query)
  rulesS : Set (WorldModelSigma.WMStrengthRuleSigma State Srt Query)

/-- Typed evidence-level ξ-derivation judgment. -/
def XiDerivesAtomEvidenceSigma
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (W : State) (a : String) (p : Pattern) (e : Evidence) : Prop :=
  ∃ r, r ∈ Ξ.rulesE ∧ r.side ∧
    Ξ.queryOfAtom a p = r.conclusion ∧
    e = r.derive W

/-- Typed strength-level ξ-derivation judgment. -/
def XiDerivesAtomStrengthSigma
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (W : State) (a : String) (p : Pattern) (s : ℝ≥0∞) : Prop :=
  ∃ r, r ∈ Ξ.rulesS ∧ r.side ∧
    Ξ.queryOfAtom a p = r.conclusion ∧
    s = r.derive W

/-- Typed ξ evidence derivations are OSLF-semantically sound. -/
theorem xiDerivesAtomEvidenceSigma_sound
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {W : State} {a : String} {p : Pattern} {e : Evidence}
    (hDer : XiDerivesAtomEvidenceSigma Ξ W a p e) :
    semE R
      (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W Ξ.queryOfAtom)
      (.atom a) p = e := by
  obtain ⟨r, _, hSide, hEnc, rfl⟩ := hDer
  exact wmRewriteRuleSigma_semE_atom_eq_derive
    (State := State) (Srt := Srt) (Query := Query) R r hSide W Ξ.queryOfAtom a p hEnc

/-- Typed ξ strength derivations imply threshold truth under OSLF semantics. -/
theorem xiDerivesAtomStrengthSigma_threshold_sound
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (R : Pattern → Pattern → Prop)
    {W : State} {a : String} {p : Pattern} {s tau : ℝ≥0∞}
    (hDer : XiDerivesAtomStrengthSigma Ξ W a p s)
    (hTau : tau ≤ s) :
    sem R
      (thresholdAtomSemOfWMQSigma (State := State) (Srt := Srt) (Query := Query) W tau Ξ.queryOfAtom)
      (.atom a) p := by
  obtain ⟨r, _, hSide, hEnc, rfl⟩ := hDer
  exact wmStrengthRuleSigma_threshold_atom
    (State := State) (Srt := Srt) (Query := Query) R r hSide W tau Ξ.queryOfAtom a p hEnc hTau

/-- Typed ξ derivations lift to typed WM query judgments. -/
theorem xiDerivesAtomEvidenceSigma_to_wmQueryJudgment
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    {W : State} {a : String} {p : Pattern} {e : Evidence}
    (hDer : XiDerivesAtomEvidenceSigma Ξ W a p e)
    (hW : WMJudgment W) :
    WorldModelSigma.WMQueryJudgmentSigma (State := State) (Srt := Srt) (Query := Query)
      W (Ξ.queryOfAtom a p) e := by
  obtain ⟨r, _, hSide, hEnc, rfl⟩ := hDer
  exact ⟨hW, by rw [hEnc]; exact r.sound hSide W⟩

/-- Typed ξ derivations lift to typed context-indexed WM query judgments. -/
theorem xiDerivesAtomEvidenceSigma_to_wmQueryJudgmentCtx
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    {Γ : Set State} {W : State} {a : String} {p : Pattern} {e : Evidence}
    (hDer : XiDerivesAtomEvidenceSigma Ξ W a p e)
    (hW : WMJudgmentCtx Γ W) :
    WorldModelSigma.WMQueryJudgmentCtxSigma (State := State) (Srt := Srt) (Query := Query)
      Γ W (Ξ.queryOfAtom a p) e := by
  obtain ⟨r, _, hSide, hEnc, rfl⟩ := hDer
  exact ⟨hW, by rw [hEnc]; exact r.sound hSide W⟩

/-- Typed ξ revision at atom-evidence level commutes with WM revision. -/
theorem xi_atom_revision_sigma
    (Ξ : XiPLNSigma (State := State) (Srt := Srt) (Query := Query))
    (R : Pattern → Pattern → Prop)
    (W₁ W₂ : State) (a : String) (p : Pattern) :
    semE R
      (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) (W₁ + W₂) Ξ.queryOfAtom)
      (.atom a) p =
      semE R
        (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W₁ Ξ.queryOfAtom)
        (.atom a) p +
      semE R
        (wmEvidenceAtomSemQSigma (State := State) (Srt := Srt) (Query := Query) W₂ Ξ.queryOfAtom)
        (.atom a) p :=
  semE_wm_atom_revision_qsigma
    (State := State) (Srt := Srt) (Query := Query) R W₁ W₂ Ξ.queryOfAtom a p

end XiPLNSigma

/-! ## Concrete Sort-Judgment-Derived Encoders

This section derives typed atom encoders from explicit sort judgments,
instead of taking `queryOfAtom` as a completely free function.

It supports:
- pluggable `typeOf`-style judgment oracles
- a concrete MeTTa syntactic default judgment
- deterministic sort inference with explicit priority
-/

namespace MeTTaTypeOf

/-- Sort tags derived from MeTTa `typeOf(space, atom, ty)` judgments. -/
inductive SortTag where
  | state
  | instr
  | atom
  | space
  deriving DecidableEq, Repr

/-- Type markers used by `typeOf` lookups for each sort. -/
structure SortTypeMarkers where
  stateTy : Pattern
  instrTy : Pattern
  atomTy  : Pattern
  spaceTy : Pattern

/-- Default markers aligned with `MeTTaCore.FullLanguageDef` type names. -/
def defaultMarkers : SortTypeMarkers where
  stateTy := .apply "State" []
  instrTy := .apply "Instr" []
  atomTy := .apply "Atom" []
  spaceTy := .apply "Space" []

/-- Sort/type judgment oracle (`typeOf(space, atom, ty)` semantics). -/
abbrev TypeOfJudgment := Pattern → Pattern → Pattern → Bool

/-- Concrete MeTTa-flavored syntactic judgment used as a default oracle.

This does not inspect atomspace premises; it classifies by constructor shape.
It is intentionally lightweight so the typed bridge layer does not depend on
the heavier MeTTa premise engine modules. -/
def syntacticTypeOfJudgment : TypeOfJudgment := fun _space atom ty =>
  match ty with
  | .apply "State" [] =>
      match atom with
      | .apply "State" _ => true
      | _ => false
  | .apply "Instr" [] =>
      match atom with
      | .apply "Eval" _ => true
      | .apply "Unify" _ => true
      | .apply "Chain" _ => true
      | .apply "TypeCheck" _ => true
      | .apply "Cast" _ => true
      | .apply "Grounded1" _ => true
      | .apply "Grounded2" _ => true
      | .apply "If" _ => true
      | .apply "Return" _ => true
      | .apply "Done" _ => true
      | _ => false
  | .apply "Space" [] =>
      match atom with
      | .apply "Space" _ => true
      | _ => false
  | .apply "Atom" [] => true
  | _ => false

/-- Sort judgment induced by `typeOf` and a marker table. -/
def hasSort (judge : TypeOfJudgment) (markers : SortTypeMarkers)
    (space atom : Pattern) (s : SortTag) : Bool :=
  match s with
  | .state => judge space atom markers.stateTy
  | .instr => judge space atom markers.instrTy
  | .atom => judge space atom markers.atomTy
  | .space => judge space atom markers.spaceTy

/-- Deterministic sort inference from `typeOf` judgments.
Priority is State > Instr > Atom > Space, with Atom fallback. -/
def inferSort (judge : TypeOfJudgment) (markers : SortTypeMarkers)
    (space atom : Pattern) : SortTag :=
  if hasSort judge markers space atom .state then .state
  else if hasSort judge markers space atom .instr then .instr
  else if hasSort judge markers space atom .atom then .atom
  else if hasSort judge markers space atom .space then .space
  else .atom

/-- A typed query constructor per inferred sort. -/
structure QueryBuilder (Query : SortTag → Type*) where
  mkState : String → Pattern → Query .state
  mkInstr : String → Pattern → Query .instr
  mkAtom : String → Pattern → Query .atom
  mkSpace : String → Pattern → Query .space

/-- Sort-derived atom encoder from concrete `typeOf` judgments.

`subjectOf a p` chooses which pattern is checked by `typeOf` for atom `(a,p)`. -/
def queryOfAtomFromTypeOfWith
    {Query : SortTag → Type*}
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers)
    (space : Pattern)
    (subjectOf : String → Pattern → Pattern)
    (builder : QueryBuilder Query) :
    String → Pattern → Sigma Query := fun a p =>
  match inferSort judge markers space (subjectOf a p) with
  | .state => ⟨.state, builder.mkState a p⟩
  | .instr => ⟨.instr, builder.mkInstr a p⟩
  | .atom => ⟨.atom, builder.mkAtom a p⟩
  | .space => ⟨.space, builder.mkSpace a p⟩

/-- Common case: infer sort from the pattern argument itself. -/
def queryOfAtomFromTypeOf
    {Query : SortTag → Type*}
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers)
    (space : Pattern)
    (builder : QueryBuilder Query) :
    String → Pattern → Sigma Query :=
  queryOfAtomFromTypeOfWith judge markers space (fun _ p => p) builder

/-- Convenience encoder using the default concrete MeTTa syntactic judgment. -/
def queryOfAtomFromSyntacticTypeOf
    {Query : SortTag → Type*}
    (markers : SortTypeMarkers := defaultMarkers)
    (space : Pattern)
    (builder : QueryBuilder Query) :
    String → Pattern → Sigma Query :=
  queryOfAtomFromTypeOf syntacticTypeOfJudgment markers space builder

theorem inferSort_eq_state
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers) (space atom : Pattern)
    (hState : hasSort judge markers space atom .state = true) :
    inferSort judge markers space atom = .state := by
  simp [inferSort, hState]

theorem inferSort_eq_instr
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers) (space atom : Pattern)
    (hState : hasSort judge markers space atom .state = false)
    (hInstr : hasSort judge markers space atom .instr = true) :
    inferSort judge markers space atom = .instr := by
  simp [inferSort, hState, hInstr]

theorem inferSort_eq_atom
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers) (space atom : Pattern)
    (hState : hasSort judge markers space atom .state = false)
    (hInstr : hasSort judge markers space atom .instr = false)
    (hAtom : hasSort judge markers space atom .atom = true) :
    inferSort judge markers space atom = .atom := by
  simp [inferSort, hState, hInstr, hAtom]

theorem inferSort_eq_space
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers) (space atom : Pattern)
    (hState : hasSort judge markers space atom .state = false)
    (hInstr : hasSort judge markers space atom .instr = false)
    (hAtom : hasSort judge markers space atom .atom = false)
    (hSpace : hasSort judge markers space atom .space = true) :
    inferSort judge markers space atom = .space := by
  simp [inferSort, hState, hInstr, hAtom, hSpace]

/-- Build a typed ξPLN package whose encoder is derived from concrete
MeTTa `typeOf` judgments. -/
def xiPLNSigmaOfTypeOf
    {State : Type*} [EvidenceType State]
    {Query : SortTag → Type*}
    [WorldModelSigma State SortTag Query]
    (judge : TypeOfJudgment)
    (markers : SortTypeMarkers)
    (space : Pattern)
    (subjectOf : String → Pattern → Pattern)
    (builder : QueryBuilder Query)
    (rulesE : Set (WorldModelSigma.WMRewriteRuleSigma State SortTag Query))
    (rulesS : Set (WorldModelSigma.WMStrengthRuleSigma State SortTag Query)) :
    XiPLNSigma (State := State) (Srt := SortTag) (Query := Query) where
  queryOfAtom := queryOfAtomFromTypeOfWith judge markers space subjectOf builder
  rulesE := rulesE
  rulesS := rulesS

/-- Convenience ξ-constructor using the concrete MeTTa syntactic judgment. -/
def xiPLNSigmaOfSyntacticTypeOf
    {State : Type*} [EvidenceType State]
    {Query : SortTag → Type*}
    [WorldModelSigma State SortTag Query]
    (markers : SortTypeMarkers := defaultMarkers)
    (space : Pattern)
    (subjectOf : String → Pattern → Pattern)
    (builder : QueryBuilder Query)
    (rulesE : Set (WorldModelSigma.WMRewriteRuleSigma State SortTag Query))
    (rulesS : Set (WorldModelSigma.WMStrengthRuleSigma State SortTag Query)) :
    XiPLNSigma (State := State) (Srt := SortTag) (Query := Query) :=
  xiPLNSigmaOfTypeOf syntacticTypeOfJudgment markers space subjectOf builder rulesE rulesS

end MeTTaTypeOf

end Mettapedia.Logic.PLNWMOSLFBridgeTyped
