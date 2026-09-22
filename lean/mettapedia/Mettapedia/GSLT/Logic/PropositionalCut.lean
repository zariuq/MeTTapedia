import Mettapedia.GSLT.Logic.PropositionalFormula

/-!
# Propositional cut as GSLT rewriting

Cut elimination is a procedure: rewrite steps on proof terms. This is an
instance of the kernel, not a change to it. The *logic* is
`PropositionalFormula` plus `PropositionalResolution`. Commuting conversions
are left as equations (here: none, so only Eq). Axiom cuts are renaming; a
principal conjunction cut is one contraction.

No Foundation import. No LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.PropositionalCut

open Mettapedia.GSLT
open Mettapedia.GSLT.Logic.PropositionalFormula

/-- Untyped proof trees. The GSLT carrier is the proof, not the sequent. -/
inductive Proof where
  | id : Formula → Proof
  | cut : Formula → Proof → Proof → Proof
  | andIntro : Proof → Proof → Proof
  | andElimLeft : Proof → Proof
  | andElimRight : Proof → Proof
deriving DecidableEq

/-- One cut-elimination step. Axiom cuts discard an identity; a principal
`and` cut is a single contraction into two smaller cuts. -/
inductive CutStep : Proof → Proof → Prop where
  | idLeft (A : Formula) (p : Proof) :
      CutStep (.cut A (.id A) p) p
  | idRight (A : Formula) (p : Proof) :
      CutStep (.cut A p (.id A)) p
  | andPrincipal (A B : Formula) (p q r : Proof) :
      CutStep
        (.cut (.and A B) (.andIntro p q) (.andElimLeft r))
        (.cut A p r)
  | andPrincipalRight (A B : Formula) (p q r : Proof) :
      CutStep
        (.cut (.and A B) (.andIntro p q) (.andElimRight r))
        (.cut B q r)

def propositionalGSLT : GSLT where
  Term := Proof
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := CutStep
  rewrites_resp_left := by
    intro t t' u htt step
    exact ⟨u, htt ▸ step, rfl⟩
  rewrites_resp_right := by
    intro t u u' step huu
    exact huu ▸ step

theorem axiom_cut_is_renaming (A : Formula) (p : Proof) :
    propositionalGSLT.Step (.cut A (.id A) p) p :=
  CutStep.idLeft A p

theorem principal_and_is_one_contraction (A B : Formula) (p q r : Proof) :
    propositionalGSLT.Step
      (.cut (.and A B) (.andIntro p q) (.andElimLeft r))
      (.cut A p r) :=
  CutStep.andPrincipal A B p q r

/-- A cut constructor occurs in the tree. This is the GSLT-side analogue of
Foundation's `IsCutFree` complement: cut is a node, not a sequent rule. -/
inductive HasCut : Proof → Prop where
  | atRoot {A p q} : HasCut (.cut A p q)
  | andIntro_left {p q} : HasCut p → HasCut (.andIntro p q)
  | andIntro_right {p q} : HasCut q → HasCut (.andIntro p q)
  | andElimLeft {p} : HasCut p → HasCut (.andElimLeft p)
  | andElimRight {p} : HasCut p → HasCut (.andElimRight p)

def CutFree (p : Proof) : Prop := ¬ HasCut p

/-- Number of `cut` nodes. Cut-freeness is `cutCount = 0`. Principal
`and`-cut need not strictly decrease this (the discarded conjunct may
already be cut-free); decrease is measured by `proofSize`. -/
def cutCount : Proof → Nat
  | .id _ => 0
  | .cut _ p q => cutCount p + cutCount q + 1
  | .andIntro p q => cutCount p + cutCount q
  | .andElimLeft p => cutCount p
  | .andElimRight p => cutCount p

theorem id_cutFree (A : Formula) : CutFree (.id A) := by
  intro h
  cases h

theorem cut_hasCut (A : Formula) (p q : Proof) : HasCut (.cut A p q) :=
  HasCut.atRoot

theorem cutCount_eq_zero_of_cutFree {p : Proof} (h : CutFree p) :
    cutCount p = 0 := by
  induction p with
  | id => rfl
  | cut _ p q => exact (h HasCut.atRoot).elim
  | andIntro p q ihp ihq =>
      have hp : CutFree p := fun hp => h (HasCut.andIntro_left hp)
      have hq : CutFree q := fun hq => h (HasCut.andIntro_right hq)
      simp [cutCount, ihp hp, ihq hq]
  | andElimLeft p ih =>
      exact ih (fun hp => h (HasCut.andElimLeft hp))
  | andElimRight p ih =>
      exact ih (fun hp => h (HasCut.andElimRight hp))

theorem cutFree_of_cutCount_zero {p : Proof} (h : cutCount p = 0) :
    CutFree p := by
  induction p with
  | id A => exact id_cutFree A
  | cut _ p q =>
      simp [cutCount] at h
  | andIntro p q ihp ihq =>
      have h0 : cutCount p = 0 ∧ cutCount q = 0 := Nat.add_eq_zero_iff.mp h
      intro contra
      cases contra with
      | andIntro_left hp => exact ihp h0.1 hp
      | andIntro_right hq => exact ihq h0.2 hq
  | andElimLeft p ih =>
      intro contra
      cases contra with
      | andElimLeft hp => exact ih h hp
  | andElimRight p ih =>
      intro contra
      cases contra with
      | andElimRight hp => exact ih h hp

theorem cutFree_iff_cutCount_zero (p : Proof) :
    CutFree p ↔ cutCount p = 0 :=
  ⟨cutCount_eq_zero_of_cutFree, cutFree_of_cutCount_zero⟩

theorem cutStep_source_hasCut {p q : Proof} (h : CutStep p q) : HasCut p := by
  cases h with
  | idLeft A r => exact HasCut.atRoot
  | idRight A r => exact HasCut.atRoot
  | andPrincipal A B r s t => exact HasCut.atRoot
  | andPrincipalRight A B r s t => exact HasCut.atRoot

/-- Proof size: every constructor costs one. Cut-elimination strictly
decreases this; Foundation's Tait `cut` constructor *increases* derivation
length. -/
def proofSize : Proof → Nat
  | .id _ => 1
  | .cut _ p q => proofSize p + proofSize q + 1
  | .andIntro p q => proofSize p + proofSize q + 1
  | .andElimLeft p => proofSize p + 1
  | .andElimRight p => proofSize p + 1

theorem proofSize_pos (p : Proof) : 0 < proofSize p := by
  induction p with
  | id => exact Nat.succ_pos 0
  | cut _ p q ihp ihq =>
      exact Nat.add_pos_right _ (Nat.succ_pos 0)
  | andIntro p q ihp ihq =>
      exact Nat.add_pos_right _ (Nat.succ_pos 0)
  | andElimLeft p ih => exact Nat.succ_pos _
  | andElimRight p ih => exact Nat.succ_pos _

theorem cutStep_decreases_proofSize {p q : Proof} (h : CutStep p q) :
    proofSize q < proofSize p := by
  cases h with
  | idLeft A r =>
      simp [proofSize]
      omega
  | idRight A r =>
      simp [proofSize]
      omega
  | andPrincipal A B r s t =>
      simp [proofSize]
      have : 0 < proofSize s := proofSize_pos s
      omega
  | andPrincipalRight A B r s t =>
      simp [proofSize]
      have : 0 < proofSize r := proofSize_pos r
      omega

#print axioms axiom_cut_is_renaming
#print axioms principal_and_is_one_contraction
#print axioms cutStep_decreases_proofSize
#print axioms cutStep_source_hasCut
#print axioms cutFree_iff_cutCount_zero

end Mettapedia.GSLT.Logic.PropositionalCut
