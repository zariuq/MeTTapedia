import Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness
import Mettapedia.Logic.PLNWorldModelKripkeConsequence
import Mettapedia.Logic.GovernanceReasoning.Core
import Foundation.Modal.Neighborhood.Logic.EMT
import Foundation.Modal.Neighborhood.Logic.ED
import Foundation.Modal.Neighborhood.Logic.EK
import Foundation.Modal.Neighborhood.Logic.EC
import Foundation.Modal.Neighborhood.Logic.EMK
import Foundation.Modal.Neighborhood.Logic.EMC
import Foundation.Modal.Entailment.Basic

/-!
# Neighborhood WM Consequence Rules (Modal/Deontic-Style Layer)

This module extends neighborhood WM closure beyond implication-only endpoints:

1. Refines proof-theoretic implication (`𝓢 ⊢ φ ➝ ψ`) into a `WMConsequenceRule`.
2. Adds modal rule families (`□→□`, `◇→◇`) on top of that refinement.
3. Provides governance-style neighborhood lifts parallel to Kripke endpoints:
   - reflexive-style: `□φ ⪯ φ` (T-like)
   - obligation/permission-style: `□φ ⪯ ◇φ` (D-like)
-/

namespace Mettapedia.Logic.PLNWorldModelNeighborhoodConsequence

open LO
open LO.Modal
open LO.Modal.Entailment
open Formula.Neighborhood
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelNeighborhood
open Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness
open Mettapedia.Logic.PLNWorldModelKripkeConsequence
open scoped ENNReal

abbrev ModalQuery := Mettapedia.Logic.PLNWorldModelNeighborhood.ModalQuery
abbrev PointedNeighborhood := Mettapedia.Logic.PLNWorldModelNeighborhood.PointedNeighborhood
abbrev NeighborhoodState := Multiset PointedNeighborhood

/-- State-indexed frame-class side condition for neighborhood WM states. -/
def inFrameClass (C : Neighborhood.FrameClass) (W : NeighborhoodState) : Prop :=
  ∀ pn ∈ W, pn.model.toFrame ∈ C

theorem inFrameClass.to_mem
    {C : Neighborhood.FrameClass}
    {W : NeighborhoodState}
    (hW : inFrameClass C W) :
    ∀ pn ∈ W, pn.model.toFrame ∈ C := by
  exact hW

/-- Rule-level refinement: provable implication yields a WM consequence rule. -/
def wmConsequenceRule_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    (φ ψ : ModalQuery)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn NeighborhoodState ModalQuery where
  side := inFrameClass C
  premise := φ
  conclusion := ψ
  sound := by
    intro W hW
    exact
      multiset_strength_le_of_provable_imp
        (S := S) (𝓢 := 𝓢) (C := C)
        (W := W) (φ := φ) (ψ := ψ)
        (inFrameClass.to_mem hW) hprov

/-- Modal family wrapper: from `⊢ □φ ➝ □ψ` to a WM consequence rule. -/
def wmBoxConsequenceRule_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    (φ ψ : ModalQuery)
    (hprov : 𝓢 ⊢ (□φ ➝ □ψ)) :
    WMConsequenceRuleOn NeighborhoodState ModalQuery :=
  wmConsequenceRule_of_provable_imp
    (S := S) (𝓢 := 𝓢) (C := C) (φ := □φ) (ψ := □ψ) hprov

/-- Modal family wrapper: from `⊢ ◇φ ➝ ◇ψ` to a WM consequence rule. -/
def wmDiaConsequenceRule_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    (φ ψ : ModalQuery)
    (hprov : 𝓢 ⊢ (◇φ ➝ ◇ψ)) :
    WMConsequenceRuleOn NeighborhoodState ModalQuery :=
  wmConsequenceRule_of_provable_imp
    (S := S) (𝓢 := 𝓢) (C := C) (φ := ◇φ) (ψ := ◇ψ) hprov

/-- Governance-style neighborhood lift parallel to Kripke `rexist_reflexive_bridge`:
`□φ ⪯ φ` under EMT frame-class side assumptions. -/
theorem wm_rexist_reflexive_strength_le_EMT
    (W : NeighborhoodState) (φ : ModalQuery)
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.EMT) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W φ := by
  have hprov : Modal.EMT ⊢ (□φ ➝ φ) := by
    exact (axiomT! (𝓢 := Modal.EMT) (φ := φ))
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.EMT) (C := Neighborhood.FrameClass.EMT)
      (W := W) (φ := □φ) (ψ := φ) hW hprov

/-- Governance-style neighborhood lift parallel to Kripke `dts_ob_pe_modal`:
`□φ ⪯ ◇φ` under ED frame-class side assumptions. -/
theorem wm_ob_pe_strength_le_ED
    (W : NeighborhoodState) (φ : ModalQuery)
    (hW : ∀ pn ∈ W, pn.model.toFrame ∈ Neighborhood.FrameClass.ED) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (◇φ) := by
  have hprov : Modal.ED ⊢ (□φ ➝ ◇φ) := by
    exact (axiomD! (𝓢 := Modal.ED) (φ := φ))
  exact
    multiset_strength_le_of_provable_imp
      (S := Logic ℕ) (𝓢 := Modal.ED) (C := Neighborhood.FrameClass.ED)
      (W := W) (φ := □φ) (ψ := ◇φ) hW hprov

/-- Rule packaging for the reflexive-style neighborhood bridge `□φ ⪯ φ`. -/
def wmRexistReflexiveConsequenceRuleNeighborhood (φ : ModalQuery) :
    WMConsequenceRuleOn NeighborhoodState ModalQuery :=
  wmConsequenceRule_of_provable_imp
    (S := Logic ℕ) (𝓢 := Modal.EMT) (C := Neighborhood.FrameClass.EMT)
    (φ := □φ) (ψ := φ) (by exact (axiomT! (𝓢 := Modal.EMT) (φ := φ)))

/-- Rule packaging for the obligation/permission-style neighborhood bridge `□φ ⪯ ◇φ`. -/
def wmDtsObPeConsequenceRuleNeighborhood (φ : ModalQuery) :
    WMConsequenceRuleOn NeighborhoodState ModalQuery :=
  wmConsequenceRule_of_provable_imp
    (S := Logic ℕ) (𝓢 := Modal.ED) (C := Neighborhood.FrameClass.ED)
    (φ := □φ) (ψ := ◇φ) (by exact (axiomD! (𝓢 := Modal.ED) (φ := φ)))

/-! ## Extended modal-family WM endpoints (K/C/Mk/McK) -/

/-- K-family WM endpoint (curried form): from a provable K-implication in a sound
frame class, obtain the corresponding multiset strength inequality. -/
theorem wm_k_curried_strength_le_of_provable
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    (W : NeighborhoodState) (φ ψ : ModalQuery)
    (hW : inFrameClass C W)
    (hprov : 𝓢 ⊢ (□(φ ➝ ψ) ➝ (□φ ➝ □ψ))) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□(φ ➝ ψ)) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ ➝ □ψ) := by
  exact
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := W) (φ := □(φ ➝ ψ)) (ψ := (□φ ➝ □ψ))
      (inFrameClass.to_mem hW) hprov

/-- C-family WM endpoint: `(□φ ⋏ □ψ) ⪯ □(φ ⋏ ψ)` from provable C-implication. -/
theorem wm_c_strength_le_of_provable
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    (W : NeighborhoodState) (φ ψ : ModalQuery)
    (hW : inFrameClass C W)
    (hprov : 𝓢 ⊢ ((□φ ⋏ □ψ) ➝ □(φ ⋏ ψ))) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ ⋏ □ψ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□(φ ⋏ ψ)) := by
  exact
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := W) (φ := (□φ ⋏ □ψ)) (ψ := □(φ ⋏ ψ))
      (inFrameClass.to_mem hW) hprov

/-- McK-family WM endpoint: `□◇φ ⪯ ◇□φ` from provable McKinsey implication. -/
theorem wm_mck_strength_le_of_provable
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    (W : NeighborhoodState) (φ : ModalQuery)
    (hW : inFrameClass C W)
    (hprov : 𝓢 ⊢ (□◇φ ➝ ◇□φ)) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□◇φ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (◇□φ) := by
  exact
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := W) (φ := □◇φ) (ψ := ◇□φ)
      (inFrameClass.to_mem hW) hprov

/-- Mk-family WM endpoint: `(□φ ⋏ ψ) ⪯ ◇(□□φ ⋏ ◇ψ)` from provable Mk implication. -/
theorem wm_mk_strength_le_of_provable
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    (W : NeighborhoodState) (φ ψ : ModalQuery)
    (hW : inFrameClass C W)
    (hprov : 𝓢 ⊢ (□φ ⋏ ψ ➝ ◇(□□φ ⋏ ◇ψ))) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ ⋏ ψ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (◇(□□φ ⋏ ◇ψ)) := by
  exact
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := W) (φ := (□φ ⋏ ψ)) (ψ := ◇(□□φ ⋏ ◇ψ))
      (inFrameClass.to_mem hW) hprov

/-- McK-family WM endpoint from an explicit McKinsey axiom assumption. -/
theorem wm_mck_strength_le_of_axiomMcK
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    [HasAxiomMcK 𝓢]
    (W : NeighborhoodState) (φ : ModalQuery)
    (hW : inFrameClass C W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□◇φ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (◇□φ) := by
  exact
    wm_mck_strength_le_of_provable
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := W) (φ := φ) hW
      (by exact (axiomMcK! (𝓢 := 𝓢) (φ := φ)))

/-- Mk-family WM endpoint from an explicit Makinson axiom assumption. -/
theorem wm_mk_strength_le_of_axiomMk
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    [HasAxiomMk 𝓢]
    (W : NeighborhoodState) (φ ψ : ModalQuery)
    (hW : inFrameClass C W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ ⋏ ψ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (◇(□□φ ⋏ ◇ψ)) := by
  exact
    wm_mk_strength_le_of_provable
      (S := S) (𝓢 := 𝓢) (C := C)
      (W := W) (φ := φ) (ψ := ψ) hW
      (by exact (axiomMk! (𝓢 := 𝓢) (φ := φ) (ψ := ψ)))

/-- McK-family consequence rule from an explicit McKinsey axiom assumption. -/
def wmMcKConsequenceRule_of_axiom
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    [HasAxiomMcK 𝓢]
    (φ : ModalQuery) :
    WMConsequenceRuleOn NeighborhoodState ModalQuery :=
  wmConsequenceRule_of_provable_imp
    (S := S) (𝓢 := 𝓢) (C := C)
    (φ := □◇φ) (ψ := ◇□φ)
    (by exact (axiomMcK! (𝓢 := 𝓢) (φ := φ)))

/-- Mk-family consequence rule from an explicit Makinson axiom assumption. -/
def wmMkConsequenceRule_of_axiom
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Neighborhood.FrameClass}
    [Sound 𝓢 C]
    [HasAxiomMk 𝓢]
    (φ ψ : ModalQuery) :
    WMConsequenceRuleOn NeighborhoodState ModalQuery :=
  wmConsequenceRule_of_provable_imp
    (S := S) (𝓢 := 𝓢) (C := C)
    (φ := (□φ ⋏ ψ)) (ψ := ◇(□□φ ⋏ ◇ψ))
    (by exact (axiomMk! (𝓢 := 𝓢) (φ := φ) (ψ := ψ)))

/-! ### Concrete neighborhood instantiations for K/C families -/

theorem wm_k_curried_strength_le_EK
    (W : NeighborhoodState) (φ ψ : ModalQuery)
    (hW : inFrameClass Neighborhood.FrameClass.EK W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□(φ ➝ ψ)) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ ➝ □ψ) := by
  exact
    wm_k_curried_strength_le_of_provable
      (S := Logic ℕ) (𝓢 := Modal.EK) (C := Neighborhood.FrameClass.EK)
      (W := W) (φ := φ) (ψ := ψ) hW
      (by exact (axiomK! (𝓢 := Modal.EK) (φ := φ) (ψ := ψ)))

theorem wm_k_curried_strength_le_EMK
    (W : NeighborhoodState) (φ ψ : ModalQuery)
    (hW : inFrameClass Neighborhood.FrameClass.EMK W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□(φ ➝ ψ)) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ ➝ □ψ) := by
  exact
    wm_k_curried_strength_le_of_provable
      (S := Logic ℕ) (𝓢 := Modal.EMK) (C := Neighborhood.FrameClass.EMK)
      (W := W) (φ := φ) (ψ := ψ) hW
      (by exact (axiomK! (𝓢 := Modal.EMK) (φ := φ) (ψ := ψ)))

theorem wm_c_strength_le_EC
    (W : NeighborhoodState) (φ ψ : ModalQuery)
    (hW : inFrameClass Neighborhood.FrameClass.EC W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ ⋏ □ψ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□(φ ⋏ ψ)) := by
  exact
    wm_c_strength_le_of_provable
      (S := Logic ℕ) (𝓢 := Modal.EC) (C := Neighborhood.FrameClass.EC)
      (W := W) (φ := φ) (ψ := ψ) hW
      (by exact (axiomC! (𝓢 := Modal.EC) (φ := φ) (ψ := ψ)))

theorem wm_c_strength_le_EMC
    (W : NeighborhoodState) (φ ψ : ModalQuery)
    (hW : inFrameClass Neighborhood.FrameClass.EMC W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□φ ⋏ □ψ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W (□(φ ⋏ ψ)) := by
  exact
    wm_c_strength_le_of_provable
      (S := Logic ℕ) (𝓢 := Modal.EMC) (C := Neighborhood.FrameClass.EMC)
      (W := W) (φ := φ) (ψ := ψ) hW
      (by exact (axiomC! (𝓢 := Modal.EMC) (φ := φ) (ψ := ψ)))

/-! ## Governance-operator translation to neighborhood queries -/

/-- Translation of governance modalities into neighborhood modal formulas. -/
def governanceModalityToNeighborhood (m : DeonticModality) (φ : ModalQuery) : ModalQuery :=
  match m with
  | .rexist => □φ
  | .obligatory => □φ
  | .permitted => ◇φ
  | .forbidden => □(∼φ)
  | .optional => (◇φ ⋏ ◇(∼φ))

@[simp] theorem governanceModalityToNeighborhood_rexist (φ : ModalQuery) :
    governanceModalityToNeighborhood .rexist φ = □φ := rfl

@[simp] theorem governanceModalityToNeighborhood_obligatory (φ : ModalQuery) :
    governanceModalityToNeighborhood .obligatory φ = □φ := rfl

@[simp] theorem governanceModalityToNeighborhood_permitted (φ : ModalQuery) :
    governanceModalityToNeighborhood .permitted φ = ◇φ := rfl

/-- Collapse governance action labels on box operators to neighborhood box. -/
def governanceBoxActionToNeighborhood (a : DeonticAct) (φ : ModalQuery) : ModalQuery :=
  match a with
  | .rexist | .obligatory | .permitted | .forbidden | .optional => □φ

@[simp] theorem governanceBoxActionToNeighborhood_rexist (φ : ModalQuery) :
    governanceBoxActionToNeighborhood .rexist φ = □φ := rfl

@[simp] theorem governanceBoxActionToNeighborhood_obligatory (φ : ModalQuery) :
    governanceBoxActionToNeighborhood .obligatory φ = □φ := rfl

@[simp] theorem governanceBoxActionToNeighborhood_forbidden (φ : ModalQuery) :
    governanceBoxActionToNeighborhood .forbidden φ = □φ := rfl

/-- Collapse governance action labels on diamond operators to neighborhood diamond. -/
def governanceDiamondActionToNeighborhood (a : DeonticAct) (φ : ModalQuery) : ModalQuery :=
  match a with
  | .rexist | .obligatory | .permitted | .forbidden | .optional => ◇φ

@[simp] theorem governanceDiamondActionToNeighborhood_permitted (φ : ModalQuery) :
    governanceDiamondActionToNeighborhood .permitted φ = ◇φ := rfl

@[simp] theorem governanceDiamondActionToNeighborhood_optional (φ : ModalQuery) :
    governanceDiamondActionToNeighborhood .optional φ = ◇φ := rfl

/-- Recursive translation from governance modal formulas to neighborhood formulas.
Mu/nu formulas are outside the current Chapter-8 bridge and map to `none`. -/
def translateGovernanceFormulaToNeighborhood :
    Formula DeonticAct 0 → Option ModalQuery
  | .tt => some ⊤
  | .ff => some ⊥
  | .neg φ =>
      Option.map (fun ψ => ∼ψ) (translateGovernanceFormulaToNeighborhood φ)
  | .conj φ ψ => do
      let φ' ← translateGovernanceFormulaToNeighborhood φ
      let ψ' ← translateGovernanceFormulaToNeighborhood ψ
      pure (φ' ⋏ ψ')
  | .disj φ ψ => do
      let φ' ← translateGovernanceFormulaToNeighborhood φ
      let ψ' ← translateGovernanceFormulaToNeighborhood ψ
      pure (φ' ⋎ ψ')
  | .diamond a φ =>
      Option.map (governanceDiamondActionToNeighborhood a)
        (translateGovernanceFormulaToNeighborhood φ)
  | .box a φ =>
      Option.map (governanceBoxActionToNeighborhood a)
        (translateGovernanceFormulaToNeighborhood φ)
  | .mu _ => none
  | .nu _ => none
  | .var i => nomatch i

@[simp] theorem translateGovernanceFormulaToNeighborhood_neg
    (φ : Formula DeonticAct 0) :
    translateGovernanceFormulaToNeighborhood (.neg φ) =
      Option.map (fun ψ => ∼ψ) (translateGovernanceFormulaToNeighborhood φ) := by
  simp [translateGovernanceFormulaToNeighborhood]

@[simp] theorem translateGovernanceFormulaToNeighborhood_conj
    (φ ψ : Formula DeonticAct 0) :
    translateGovernanceFormulaToNeighborhood (.conj φ ψ) =
      (do
        let φ' ← translateGovernanceFormulaToNeighborhood φ
        let ψ' ← translateGovernanceFormulaToNeighborhood ψ
        pure (φ' ⋏ ψ')) := by
  simp [translateGovernanceFormulaToNeighborhood]

@[simp] theorem translateGovernanceFormulaToNeighborhood_disj
    (φ ψ : Formula DeonticAct 0) :
    translateGovernanceFormulaToNeighborhood (.disj φ ψ) =
      (do
        let φ' ← translateGovernanceFormulaToNeighborhood φ
        let ψ' ← translateGovernanceFormulaToNeighborhood ψ
        pure (φ' ⋎ ψ')) := by
  simp [translateGovernanceFormulaToNeighborhood]

@[simp] theorem translateGovernanceFormulaToNeighborhood_rexistFormula
    (φ : Formula DeonticAct 0) :
    translateGovernanceFormulaToNeighborhood (rexistFormula φ) =
      Option.map (fun ψ => □ψ) (translateGovernanceFormulaToNeighborhood φ) := by
  cases htr : translateGovernanceFormulaToNeighborhood φ <;>
    simp [translateGovernanceFormulaToNeighborhood, rexistFormula, htr]

@[simp] theorem translateGovernanceFormulaToNeighborhood_obFormula
    (φ : Formula DeonticAct 0) :
    translateGovernanceFormulaToNeighborhood (obFormula φ) =
      Option.map (fun ψ => □ψ) (translateGovernanceFormulaToNeighborhood φ) := by
  cases htr : translateGovernanceFormulaToNeighborhood φ <;>
    simp [translateGovernanceFormulaToNeighborhood, obFormula, htr]

@[simp] theorem translateGovernanceFormulaToNeighborhood_peFormula
    (φ : Formula DeonticAct 0) :
    translateGovernanceFormulaToNeighborhood (peFormula φ) =
      Option.map (fun ψ => ◇ψ) (translateGovernanceFormulaToNeighborhood φ) := by
  cases htr : translateGovernanceFormulaToNeighborhood φ <;>
    simp [translateGovernanceFormulaToNeighborhood, peFormula, htr]

@[simp] theorem translateGovernanceFormulaToNeighborhood_forbiddenBox
    (φ : Formula DeonticAct 0) :
    translateGovernanceFormulaToNeighborhood (.box .forbidden φ) =
      Option.map (fun ψ => □ψ) (translateGovernanceFormulaToNeighborhood φ) := by
  cases htr : translateGovernanceFormulaToNeighborhood φ <;>
    simp [translateGovernanceFormulaToNeighborhood, htr]

@[simp] theorem translateGovernanceFormulaToNeighborhood_optionalDiamond
    (φ : Formula DeonticAct 0) :
    translateGovernanceFormulaToNeighborhood (.diamond .optional φ) =
      Option.map (fun ψ => ◇ψ) (translateGovernanceFormulaToNeighborhood φ) := by
  cases htr : translateGovernanceFormulaToNeighborhood φ <;>
    simp [translateGovernanceFormulaToNeighborhood, htr]

theorem wm_governance_rexist_strength_le
    (W : NeighborhoodState) (φ : ModalQuery)
    (hW : inFrameClass Neighborhood.FrameClass.EMT W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .rexist φ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W φ := by
  simpa [governanceModalityToNeighborhood] using
    (wm_rexist_reflexive_strength_le_EMT (W := W) (φ := φ) hW)

theorem wm_governance_ob_pe_strength_le
    (W : NeighborhoodState) (φ : ModalQuery)
    (hW : inFrameClass Neighborhood.FrameClass.ED W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .obligatory φ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .permitted φ) := by
  simpa [governanceModalityToNeighborhood] using
    (wm_ob_pe_strength_le_ED (W := W) (φ := φ) hW)

theorem wm_governance_rexist_strength_le_of_translation
    (W : NeighborhoodState) (φ : Formula DeonticAct 0) (φn : ModalQuery)
    (_htr : translateGovernanceFormulaToNeighborhood φ = some φn)
    (hW : inFrameClass Neighborhood.FrameClass.EMT W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .rexist φn) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W φn := by
  exact wm_governance_rexist_strength_le (W := W) (φ := φn) hW

theorem wm_governance_ob_pe_strength_le_of_translation
    (W : NeighborhoodState) (φ : Formula DeonticAct 0) (φn : ModalQuery)
    (_htr : translateGovernanceFormulaToNeighborhood φ = some φn)
    (hW : inFrameClass Neighborhood.FrameClass.ED W) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .obligatory φn) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .permitted φn) := by
  exact wm_governance_ob_pe_strength_le (W := W) (φ := φn) hW

theorem wm_governance_forbidden_shape_of_translation
    (W : NeighborhoodState) (φ : Formula DeonticAct 0) (φn : ModalQuery)
    (_htr : translateGovernanceFormulaToNeighborhood φ = some φn) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .forbidden φn) =
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .obligatory (∼φn)) := by
  simp [governanceModalityToNeighborhood]

theorem wm_governance_optional_shape_of_translation
    (W : NeighborhoodState) (φ : Formula DeonticAct 0) (φn : ModalQuery)
    (_htr : translateGovernanceFormulaToNeighborhood φ = some φn) :
    WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .optional φn) =
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W ((governanceModalityToNeighborhood .permitted φn) ⋏
          (governanceModalityToNeighborhood .permitted (∼φn))) := by
  simp [governanceModalityToNeighborhood]

/-- Single theorem block exposing translated governance endpoints over neighborhood WM states. -/
theorem governance_translation_endpoint_block
    (W : NeighborhoodState) (φ : ModalQuery)
    (hEMT : inFrameClass Neighborhood.FrameClass.EMT W)
    (hED : inFrameClass Neighborhood.FrameClass.ED W) :
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .rexist φ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W φ) ∧
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .obligatory φ) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .permitted φ)) := by
  constructor
  · exact wm_governance_rexist_strength_le (W := W) (φ := φ) hEMT
  · exact wm_governance_ob_pe_strength_le (W := W) (φ := φ) hED

/-- Formula-level governance endpoint block via recursive translation output. -/
theorem governance_translation_endpoint_block_of_formula
    (W : NeighborhoodState) (φ : Formula DeonticAct 0) (φn : ModalQuery)
    (_htr : translateGovernanceFormulaToNeighborhood φ = some φn)
    (hEMT : inFrameClass Neighborhood.FrameClass.EMT W)
    (hED : inFrameClass Neighborhood.FrameClass.ED W) :
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .rexist φn) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W φn) ∧
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .obligatory φn) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .permitted φn)) := by
  exact governance_translation_endpoint_block (W := W) (φ := φn) hEMT hED

/-- Formula-level governance endpoint block extended with forbidden/optional shape preservation. -/
theorem governance_translation_endpoint_block_of_formula_extended
    (W : NeighborhoodState) (φ : Formula DeonticAct 0) (φn : ModalQuery)
    (htr : translateGovernanceFormulaToNeighborhood φ = some φn)
    (hEMT : inFrameClass Neighborhood.FrameClass.EMT W)
    (hED : inFrameClass Neighborhood.FrameClass.ED W) :
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .rexist φn) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) W φn) ∧
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .obligatory φn) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .permitted φn)) ∧
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .forbidden φn) =
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .obligatory (∼φn))) ∧
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W (governanceModalityToNeighborhood .optional φn) =
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery)
        W ((governanceModalityToNeighborhood .permitted φn) ⋏
          (governanceModalityToNeighborhood .permitted (∼φn)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact wm_governance_rexist_strength_le_of_translation
      (W := W) (φ := φ) (φn := φn) htr hEMT
  · exact wm_governance_ob_pe_strength_le_of_translation
      (W := W) (φ := φ) (φn := φn) htr hED
  · exact wm_governance_forbidden_shape_of_translation
      (W := W) (φ := φ) (φn := φn) htr
  · exact wm_governance_optional_shape_of_translation
      (W := W) (φ := φ) (φn := φn) htr

section Parallel

variable {S : Type*}

/-- Kripke and neighborhood reflexive-style lifts in one parallel endpoint theorem. -/
theorem kripke_neighborhood_rexist_parallel
    (Wk : Multiset (PointedDeonticKripke S))
    (Wn : NeighborhoodState)
    (φk : Formula DeonticAct 0) (φn : ModalQuery)
    (hrefl : ∀ pk : PointedDeonticKripke S, ∀ s, pk.lts.trans s .rexist s)
    (hWn : ∀ pn ∈ Wn, pn.model.toFrame ∈ Neighborhood.FrameClass.EMT) :
    (WorldModel.queryStrength
        (State := Multiset (PointedDeonticKripke S)) (Query := Formula DeonticAct 0)
        Wk (rexistFormula φk) ≤
      WorldModel.queryStrength
        (State := Multiset (PointedDeonticKripke S)) (Query := Formula DeonticAct 0)
        Wk φk) ∧
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) Wn (□φn) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) Wn φn) := by
  constructor
  · exact wm_rexist_reflexive_strength_le (W := Wk) (φ := φk) hrefl
  · exact wm_rexist_reflexive_strength_le_EMT (W := Wn) (φ := φn) hWn

/-- Kripke and neighborhood obligation/permission-style lifts in one parallel endpoint theorem. -/
theorem kripke_neighborhood_ob_pe_parallel
    (Wk : Multiset (PointedDeonticKripke S))
    (Wn : NeighborhoodState)
    (φk : Formula DeonticAct 0) (φn : ModalQuery)
    (hser : ∀ pk : PointedDeonticKripke S, DeonticSeriality pk.lts)
    (htotal : ∀ pk : PointedDeonticKripke S, ∀ s, ∃ s', pk.lts.trans s .obligatory s')
    (hWn : ∀ pn ∈ Wn, pn.model.toFrame ∈ Neighborhood.FrameClass.ED) :
    (WorldModel.queryStrength
        (State := Multiset (PointedDeonticKripke S)) (Query := Formula DeonticAct 0)
        Wk (obFormula φk) ≤
      WorldModel.queryStrength
        (State := Multiset (PointedDeonticKripke S)) (Query := Formula DeonticAct 0)
        Wk (peFormula φk)) ∧
    (WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) Wn (□φn) ≤
      WorldModel.queryStrength (State := NeighborhoodState) (Query := ModalQuery) Wn (◇φn)) := by
  constructor
  · exact wm_dts_ob_pe_strength_le (W := Wk) (φ := φk) hser htotal
  · exact wm_ob_pe_strength_le_ED (W := Wn) (φ := φn) hWn

end Parallel

end Mettapedia.Logic.PLNWorldModelNeighborhoodConsequence
