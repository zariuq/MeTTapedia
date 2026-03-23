import Mettapedia.Languages.GF.OSLFBridge_handcrafted
import Mettapedia.Languages.GF.SUMO.SumoAbstract
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.Logic.PLNWorldModelSetTheoryBridge

/-!
# GF → FOL(Set) Typed Fragment Bridge

This module strengthens the earlier coarse GF→FOL(Set) stub into a typed,
relation-preserving fragment translator:

- input side: GF abstract syntax/patterns (including SUMO-GF trees),
- middle layer: typed GF set-fragment (`term`/`atom`/`formula`),
- output side: set-theory FOL queries used by the Set↔WM bridge.

The translator is intentionally partial and therefore includes both:

- positive transport endpoint (SUMO-style fixture through Set↔WM),
- explicit non-fullness/non-faithfulness criteria for unsupported patterns.
-/

namespace Mettapedia.Languages.GF.GFToFOLSetBridge

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open LO.FirstOrder.Semiformula
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.OSLFBridge
open Mettapedia.Languages.GF.SUMO.SumoAbstract
open OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelSetTheoryBridge

abbrev SetLang := Mettapedia.Logic.PLNWorldModelSetTheoryBridge.SetLang
abbrev SetQuery := Mettapedia.Logic.PLNWorldModelSetTheoryBridge.SetQuery
abbrev SetPointed := Mettapedia.Logic.PLNWorldModelSetTheoryBridge.SetPointed
abbrev SetState := Mettapedia.Logic.PLNWorldModelSetTheoryBridge.SetState
abbrev GFPattern := OSLF.MeTTaIL.Syntax.Pattern

abbrev SetOpenTerm := LO.FirstOrder.Term SetLang String
abbrev SetOpenFormula := LO.FirstOrder.Formula SetLang String

/-- Typed GF set-term fragment. -/
inductive GFSetTerm where
  | var : String → GFSetTerm
  | classConst : String → GFSetTerm
  | individualConst : String → GFSetTerm
deriving DecidableEq, Repr

/-- Typed GF set-atom fragment. -/
inductive GFSetAtom where
  | eq : GFSetTerm → GFSetTerm → GFSetAtom
  | mem : GFSetTerm → GFSetTerm → GFSetAtom
  | subset : GFSetTerm → GFSetTerm → GFSetAtom
deriving DecidableEq, Repr

/-- Typed GF set-formula fragment. -/
inductive GFSetFormula where
  | top : GFSetFormula
  | bot : GFSetFormula
  | atom : GFSetAtom → GFSetFormula
  | not : GFSetFormula → GFSetFormula
  | and : GFSetFormula → GFSetFormula → GFSetFormula
  | or : GFSetFormula → GFSetFormula → GFSetFormula
  | imp : GFSetFormula → GFSetFormula → GFSetFormula
  | iff : GFSetFormula → GFSetFormula → GFSetFormula
  | all : String → GFSetFormula → GFSetFormula
  | ex : String → GFSetFormula → GFSetFormula
deriving DecidableEq, Repr

/-- Kernel-reducible string prefix check (unlike `String.startsWith` which
uses `Slice.Pattern.ForwardPattern` and does not reduce in the kernel). -/
private def strStartsWith (s pfx : String) : Bool :=
  s.toList.take pfx.toList.length == pfx.toList

private def isClassConstHead (head : String) : Bool :=
  strStartsWith head "sumo_class_"

private def isIndividualConstHead (head : String) : Bool :=
  strStartsWith head "sumo_ind_"

private def isForallHead (head : String) : Bool :=
  strStartsWith head "sumo_forall_"

private def isExistsHead (head : String) : Bool :=
  strStartsWith head "sumo_exists_"

private def isInstanceHead (head : String) : Bool :=
  strStartsWith head "sumo_instance_"

private def classTag (s : String) : String := "class::" ++ s
private def individualTag (s : String) : String := "ind::" ++ s

/-- GF set-term fragment to open set-theory term. -/
def gfSetTermToOpenTerm : GFSetTerm → SetOpenTerm
  | .var x => (&x : SetOpenTerm)
  | .classConst c => (&(classTag c) : SetOpenTerm)
  | .individualConst c => (&(individualTag c) : SetOpenTerm)

private def liftOpenTerm : SetOpenTerm → LO.FirstOrder.Semiterm SetLang String 1
  | .bvar x => Fin.elim0 x
  | .fvar x => (&x : LO.FirstOrder.Semiterm SetLang String 1)
  | .func f _ => Empty.elim f

private def eqAtomN {n : ℕ}
    (t₁ t₂ : LO.FirstOrder.Semiterm SetLang String n) :
    LO.FirstOrder.Semiformula SetLang String n :=
  LO.FirstOrder.Semiformula.rel (L := SetLang) (ξ := String)
    (n := n) Language.Eq.eq ![t₁, t₂]

private def memAtomN {n : ℕ}
    (t₁ t₂ : LO.FirstOrder.Semiterm SetLang String n) :
    LO.FirstOrder.Semiformula SetLang String n :=
  LO.FirstOrder.Semiformula.rel (L := SetLang) (ξ := String)
    (n := n) Language.Mem.mem ![t₁, t₂]

/-- GF set-atom fragment to open set-theory formula. -/
def gfSetAtomToOpenFormula : GFSetAtom → SetOpenFormula
  | .eq t₁ t₂ =>
      eqAtomN (gfSetTermToOpenTerm t₁) (gfSetTermToOpenTerm t₂)
  | .mem t₁ t₂ =>
      memAtomN (gfSetTermToOpenTerm t₁) (gfSetTermToOpenTerm t₂)
  | .subset t₁ t₂ =>
      let z : LO.FirstOrder.Semiterm SetLang String 1 := #(0 : Fin 1)
      let lhs := memAtomN z (liftOpenTerm (gfSetTermToOpenTerm t₁))
      let rhs := memAtomN z (liftOpenTerm (gfSetTermToOpenTerm t₂))
      (∀' (lhs ➝ rhs))

private def bindVarInOpenFormula (x : String) (φ : SetOpenFormula) :
    LO.FirstOrder.Semiformula SetLang String 1 :=
  (Rew.bind (L := SetLang)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun y : String =>
        if y = x then (#(0 : Fin 1) : LO.FirstOrder.Semiterm SetLang String 1)
        else (&y : LO.FirstOrder.Semiterm SetLang String 1))) ▹ φ

/-- GF set-formula fragment to open set-theory formula. -/
def gfSetFormulaToOpenFormula : GFSetFormula → SetOpenFormula
  | .top => (⊤ : SetOpenFormula)
  | .bot => (⊥ : SetOpenFormula)
  | .atom a => gfSetAtomToOpenFormula a
  | .not φ => ∼(gfSetFormulaToOpenFormula φ)
  | .and φ ψ => gfSetFormulaToOpenFormula φ ⋏ gfSetFormulaToOpenFormula ψ
  | .or φ ψ => gfSetFormulaToOpenFormula φ ⋎ gfSetFormulaToOpenFormula ψ
  | .imp φ ψ => gfSetFormulaToOpenFormula φ ➝ gfSetFormulaToOpenFormula ψ
  | .iff φ ψ => gfSetFormulaToOpenFormula φ ⭤ gfSetFormulaToOpenFormula ψ
  | .all x φ => ∀' bindVarInOpenFormula x (gfSetFormulaToOpenFormula φ)
  | .ex x φ => ∃' bindVarInOpenFormula x (gfSetFormulaToOpenFormula φ)

/-- Open formula to syntactic formula (`String` vars reindexed to `ℕ`). -/
def openFormulaToSyntactic (φ : SetOpenFormula) :
    LO.FirstOrder.SyntacticFormula SetLang :=
  (Rew.rewriteMap (L := SetLang) (n := 0) (fun x => φ.idxOfFVar x)) ▹ φ

/-- Close an open formula by universal closure of all free variables. -/
def closeOpenFormula (φ : SetOpenFormula) : SetQuery :=
  LO.FirstOrder.Semiformula.univCl (openFormulaToSyntactic φ)

/-- Partial GF-pattern -> typed set-term fragment parser. -/
def gfPatternToSetTermFragment? : GFPattern → Option GFSetTerm
  | OSLF.MeTTaIL.Syntax.Pattern.fvar x => some (.var x)
  | OSLF.MeTTaIL.Syntax.Pattern.apply head [] =>
      if isClassConstHead head then some (.classConst head)
      else if isIndividualConstHead head then some (.individualConst head)
      else none
  | _ => none

/-- Partial GF-pattern -> typed set-formula fragment parser. -/
def gfPatternToSetFormulaFragment? : GFPattern → Option GFSetFormula
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_true" [] => some .top
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_false" [] => some .bot
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_formStm" [p] =>
      gfPatternToSetFormulaFragment? p
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_not" [p] =>
      (gfPatternToSetFormulaFragment? p).map GFSetFormula.not
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_and" [p, q] =>
      match gfPatternToSetFormulaFragment? p, gfPatternToSetFormulaFragment? q with
      | some p', some q' => some (.and p' q')
      | _, _ => none
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_or" [p, q] =>
      match gfPatternToSetFormulaFragment? p, gfPatternToSetFormulaFragment? q with
      | some p', some q' => some (.or p' q')
      | _, _ => none
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_impl" [p, q] =>
      match gfPatternToSetFormulaFragment? p, gfPatternToSetFormulaFragment? q with
      | some p', some q' => some (.imp p' q')
      | _, _ => none
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_equiv" [p, q] =>
      match gfPatternToSetFormulaFragment? p, gfPatternToSetFormulaFragment? q with
      | some p', some q' => some (.iff p' q')
      | _, _ => none
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_equal" [t₁, t₂] =>
      match gfPatternToSetTermFragment? t₁, gfPatternToSetTermFragment? t₂ with
      | some t₁', some t₂' => some (.atom (.eq t₁' t₂'))
      | _, _ => none
  | OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_subclass" [t₁, t₂] =>
      match gfPatternToSetTermFragment? t₁, gfPatternToSetTermFragment? t₂ with
      | some t₁', some t₂' => some (.atom (.subset t₁' t₂'))
      | _, _ => none
  | OSLF.MeTTaIL.Syntax.Pattern.apply head [binder, body] =>
      if isForallHead head then
        match binder, gfPatternToSetFormulaFragment? body with
        | OSLF.MeTTaIL.Syntax.Pattern.fvar x, some body' => some (.all x body')
        | _, _ => none
      else if isExistsHead head then
        match binder, gfPatternToSetFormulaFragment? body with
        | OSLF.MeTTaIL.Syntax.Pattern.fvar x, some body' => some (.ex x body')
        | _, _ => none
      else if isInstanceHead head then
        match gfPatternToSetTermFragment? binder, gfPatternToSetTermFragment? body with
        | some t₁', some t₂' => some (.atom (.mem t₁' t₂'))
        | _, _ => none
      else
        none
  | _ => none

/-- Partial GF-pattern -> set-theory query translator through typed fragment. -/
def gfPatternToSetQueryFragment? (p : GFPattern) : Option SetQuery :=
  (gfPatternToSetFormulaFragment? p).map (fun φ =>
    closeOpenFormula (gfSetFormulaToOpenFormula φ))

/-- Node-level partial translator via `gfAbstractToPattern`. -/
def gfNodeToSetQueryFragment? (t : AbstractNode) : Option SetQuery :=
  gfPatternToSetQueryFragment? (gfAbstractToPattern t)

/-- Total GF-pattern -> set query translator (fallback to `⊤` outside fragment). -/
def gfPatternToSetQuery (p : GFPattern) : SetQuery :=
  (gfPatternToSetQueryFragment? p).getD (⊤ : SetQuery)

/-- Total node-level translator via `gfAbstractToPattern`. -/
def gfNodeToSetQuery (t : AbstractNode) : SetQuery :=
  gfPatternToSetQuery (gfAbstractToPattern t)

/-! Compatibility aliases for callers still referencing the older stub names. -/
abbrev gfPatternToSetQueryStub := gfPatternToSetQuery
abbrev gfNodeToSetQueryStub := gfNodeToSetQuery

/-- Negative criterion 1: translator is intentionally partial (not full). -/
theorem gfPatternToSetFormulaFragment_nonfull :
    gfPatternToSetFormulaFragment?
      (OSLF.MeTTaIL.Syntax.Pattern.apply "sumo_agent"
        [OSLF.MeTTaIL.Syntax.Pattern.fvar "p",
         OSLF.MeTTaIL.Syntax.Pattern.fvar "a"]) = none := by
  rfl

/-- Negative criterion 2: distinct unsupported leaves collapse under total fallback. -/
theorem gfPatternToSetQuery_nonfaithful_leafs
    (x y : String) (hxy : x ≠ y) :
    gfPatternToSetQuery (OSLF.MeTTaIL.Syntax.Pattern.fvar x) =
      gfPatternToSetQuery (OSLF.MeTTaIL.Syntax.Pattern.fvar y)
    ∧ (OSLF.MeTTaIL.Syntax.Pattern.fvar x ≠
      OSLF.MeTTaIL.Syntax.Pattern.fvar y) := by
  constructor
  · simp [gfPatternToSetQuery, gfPatternToSetQueryFragment?,
      gfPatternToSetFormulaFragment?]
  · intro h
    injection h with hEq
    exact hxy hEq

/-- SUMO-style premise node in the typed fragment (`instance` relation). -/
def sumoFragmentPremiseNode : AbstractNode :=
  .apply (SumoFunctionSig.instanceRel "Entity")
    [ .leaf "x" (SumoCategory.El "Entity")
    , .apply ⟨"sumo_class_Entity", SumoCategory.SumoClass⟩ [] ]

/-- SUMO-style conclusion node (same translated relation; implication reflexivity). -/
def sumoFragmentConclusionNode : AbstractNode :=
  sumoFragmentPremiseNode

/-- Positive fragment criterion: typed parser recovers the intended relation form. -/
theorem sumoFragmentPremiseNode_parses_as_mem_atom :
    gfPatternToSetFormulaFragment? (gfAbstractToPattern sumoFragmentPremiseNode) =
      some (.atom (.mem (.var "x") (.classConst "sumo_class_Entity"))) := by
  have hname : (SumoFunctionSig.instanceRel "Entity").name = "sumo_instance_Entity" := by decide
  have hpat : gfAbstractToPattern sumoFragmentPremiseNode =
      Pattern.apply "sumo_instance_Entity" [.fvar "x", .apply "sumo_class_Entity" []] := by
    simp only [sumoFragmentPremiseNode, gfAbstractToPattern, List.map, hname]
  rw [hpat]
  decide

/-- Positive criterion: concrete SUMO fixture is translatable (inside fragment). -/
theorem sumoFragmentPremiseNode_translatable :
    ∃ q : SetQuery, gfNodeToSetQueryFragment? sumoFragmentPremiseNode = some q := by
  refine ⟨closeOpenFormula
    (gfSetFormulaToOpenFormula (.atom (.mem (.var "x") (.classConst "sumo_class_Entity")))), ?_⟩
  simpa [gfNodeToSetQueryFragment?, gfPatternToSetQueryFragment?] using
    congrArg
      (fun t =>
        Option.map (fun φ => closeOpenFormula (gfSetFormulaToOpenFormula φ)) t)
      sumoFragmentPremiseNode_parses_as_mem_atom

/-- First SUMO-style bridge endpoint:
the translated implication is provable in ZF. -/
theorem zf_provable_imp_of_sumo_fragment_translation :
    𝗭𝗙 ⊢
      (gfNodeToSetQuery sumoFragmentPremiseNode ➝
        gfNodeToSetQuery sumoFragmentConclusionNode) := by
  have hcons :
      𝗭𝗙 ⊨[SmallStruc SetLang]
        (gfNodeToSetQuery sumoFragmentPremiseNode ➝
          gfNodeToSetQuery sumoFragmentConclusionNode) := by
    intro S hS
    exact
      (Semantics.Imp.models_imply
        (𝓜 := S)
        (φ := gfNodeToSetQuery sumoFragmentPremiseNode)
        (ψ := gfNodeToSetQuery sumoFragmentConclusionNode)).2
        (by intro hPrem; simpa [sumoFragmentConclusionNode] using hPrem)
  exact FirstOrder.complete hcons

/-- The translated SUMO-fragment implication packaged as a state-indexed WM rule. -/
def zfWmRuleOfSumoFragmentTranslation : WMConsequenceRuleOn SetState SetQuery :=
  wmConsequenceRuleOn_of_provable_imp_ZF
    (φ := gfNodeToSetQuery sumoFragmentPremiseNode)
    (ψ := gfNodeToSetQuery sumoFragmentConclusionNode)
    zf_provable_imp_of_sumo_fragment_translation

/-- Multiset WM inequality endpoint for the SUMO-fragment translation on ZF-model states. -/
theorem zf_multiset_strength_le_of_sumo_fragment_translation
    (W : SetState) (hW : stateModelsZF W) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W
      (gfNodeToSetQuery sumoFragmentPremiseNode) ≤
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W
      (gfNodeToSetQuery sumoFragmentConclusionNode) := by
  exact (zfWmRuleOfSumoFragmentTranslation.sound hW)

/-! Compatibility aliases for existing references/scripts. -/
abbrev sumoStubPremiseNode := sumoFragmentPremiseNode
abbrev sumoStubConclusionNode := sumoFragmentConclusionNode
abbrev zf_provable_imp_of_sumo_stub_translation :=
  zf_provable_imp_of_sumo_fragment_translation
abbrev zfWmRuleOfSumoStubTranslation := zfWmRuleOfSumoFragmentTranslation
abbrev zf_multiset_strength_le_of_sumo_stub_translation :=
  zf_multiset_strength_le_of_sumo_fragment_translation

end Mettapedia.Languages.GF.GFToFOLSetBridge
