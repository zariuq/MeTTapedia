import Mettapedia.GSLT.LanguageDef.CertificateGSLTRawSubstitution
import Mettapedia.GSLT.LanguageDef.CertificateGSLTSemantics
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory

/-!
# Obligation contexts of open derivations: erasure

Plan transforms rearrange obligation contexts.  The structural moves already
exist for open derivations: concatenation of derivation vectors
(`OpenDerivationList.append`), the two projections out of a concatenated
context (`leftProjection`, `rightProjection`) and their laws
(`leftProjection_bind_append`, `rightProjection_bind_append`), which make
context concatenation a binary product in the classifying category.

This module adds two facts about the wire erasure used by the plan modules.

* The erasure of open derivations is injective (`eraseOpen_injective`), and it
  determines the goal (`eraseOpen_determines`): rule applications are
  propositions fixed by the rule instance.
* A raw closed proof is a raw open proof without citations (`rawToOpen`); the
  open checker accepts it in the empty context exactly when the kernel checker
  accepts it (`checkOpenRaw_nil_rawToOpen`), and closed erasure commutes with
  this conversion (`eraseOpen_ofClosed`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofPlans

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

variable {definition : ValidatedCalculusLanguageDef}

/-! ## Erasure is injective -/

mutual

/-- **The wire erasure determines an open derivation**, together with its
goal. -/
theorem eraseOpen_determines {context : List Pattern} :
    {first second : Pattern} →
      (left : OpenDerivation definition context first) →
      (right : OpenDerivation definition context second) →
        left.eraseOpen = right.eraseOpen → first = second ∧ HEq left right
  | _, _, .assumption index, .assumption index', erased => by
      simp only [OpenDerivation.eraseOpen, RawOpenProof.premise.injEq] at erased
      have same : index = index' := Fin.ext erased
      subst same
      exact ⟨rfl, HEq.rfl⟩
  | _, _, .assumption _, .byRule _ _ _, erased => by
      simp [OpenDerivation.eraseOpen] at erased
  | _, _, .byRule _ _ _, .assumption _, erased => by
      simp [OpenDerivation.eraseOpen] at erased
  | _, _, .byRule ruleInstance application children,
      .byRule ruleInstance' application' children', erased => by
      simp only [OpenDerivation.eraseOpen, RawOpenProof.node.injEq] at erased
      obtain ⟨sameInstance, sameChildren⟩ := erased
      obtain ⟨samePremises, sameChildrenHEq⟩ :=
        eraseOpenList_determines children children' sameChildren
      subst sameInstance
      subst samePremises
      obtain ⟨-, sameConclusion⟩ := application.outputs_unique application'
      subst sameConclusion
      cases eq_of_heq sameChildrenHEq
      exact ⟨rfl, HEq.rfl⟩

/-- The wire erasure determines an ordered vector of open derivations. -/
theorem eraseOpenList_determines {context : List Pattern} :
    {first second : List Pattern} →
      (left : OpenDerivationList definition context first) →
      (right : OpenDerivationList definition context second) →
        left.eraseOpen = right.eraseOpen → first = second ∧ HEq left right
  | _, _, .nil, .nil, _ => ⟨rfl, HEq.rfl⟩
  | _, _, .nil, .cons _ _, erased => by simp [OpenDerivationList.eraseOpen] at erased
  | _, _, .cons _ _, .nil, erased => by simp [OpenDerivationList.eraseOpen] at erased
  | _, _, .cons head tail, .cons head' tail', erased => by
      simp only [OpenDerivationList.eraseOpen, List.cons.injEq] at erased
      obtain ⟨headErased, tailErased⟩ := erased
      obtain ⟨sameHeadGoal, sameHead⟩ := eraseOpen_determines head head' headErased
      obtain ⟨sameTailGoals, sameTail⟩ := eraseOpenList_determines tail tail' tailErased
      subst sameHeadGoal
      subst sameTailGoals
      cases eq_of_heq sameHead
      cases eq_of_heq sameTail
      exact ⟨rfl, HEq.rfl⟩

end

/-- **Erasure is injective** on open derivations with a common goal. -/
theorem eraseOpen_injective {context : List Pattern} {goal : Pattern}
    {left right : OpenDerivation definition context goal}
    (erased : left.eraseOpen = right.eraseOpen) : left = right :=
  eq_of_heq (eraseOpen_determines left right erased).2

/-- Erasure is injective on open derivation vectors with common goals. -/
theorem eraseOpenList_injective {context goals : List Pattern}
    {left right : OpenDerivationList definition context goals}
    (erased : left.eraseOpen = right.eraseOpen) : left = right :=
  eq_of_heq (eraseOpenList_determines left right erased).2

/-! ## Raw closed proofs as raw open proofs -/

mutual

/-- A raw closed proof is a raw open proof citing no premise. -/
def rawToOpen : RawProof → RawOpenProof
  | .node ruleInstance children => .node ruleInstance (rawToOpenList children)

/-- Pointwise conversion of raw closed proofs. -/
def rawToOpenList : List RawProof → List RawOpenProof
  | [] => []
  | proof :: proofs => rawToOpen proof :: rawToOpenList proofs

end

mutual

/-- **The empty-context open checker is the kernel checker** on raw closed
proofs. -/
theorem checkOpenRaw_nil_rawToOpen (goal : Pattern) :
    (proof : RawProof) →
      checkOpenRaw definition [] goal (rawToOpen proof) = checkRaw definition goal proof
  | .node ruleInstance children => by
      rw [rawToOpen, checkOpenRaw, checkRaw]
      cases instantiateRule? definition ruleInstance with
      | none => rfl
      | some shape =>
          obtain ⟨premises, conclusion⟩ := shape
          simp only
          rw [checkOpenRawChildren_nil_rawToOpenList premises children]

/-- Pointwise form for ordered children. -/
theorem checkOpenRawChildren_nil_rawToOpenList :
    (goals : List Pattern) → (proofs : List RawProof) →
      checkOpenRawChildren definition [] goals (rawToOpenList proofs) =
        checkRawChildren definition goals proofs
  | [], [] => by simp [rawToOpenList, checkOpenRawChildren, checkRawChildren]
  | [], _ :: _ => by simp [rawToOpenList, checkOpenRawChildren, checkRawChildren]
  | _ :: _, [] => by simp [rawToOpenList, checkOpenRawChildren, checkRawChildren]
  | goal :: goals, proof :: proofs => by
      rw [rawToOpenList, checkOpenRawChildren, checkRawChildren,
        checkOpenRaw_nil_rawToOpen goal proof,
        checkOpenRawChildren_nil_rawToOpenList goals proofs]

end

mutual

/-- The open erasure of a closed derivation is the conversion of its closed
erasure. -/
theorem eraseOpen_ofClosed {goal : Pattern} (derivation : Derivation definition goal) :
    (OpenDerivation.ofClosed (context := []) derivation).eraseOpen =
      rawToOpen derivation.erase := by
  cases derivation with
  | byRule ruleInstance application children =>
      rw [OpenDerivation.ofClosed, OpenDerivation.eraseOpen, Derivation.erase, rawToOpen,
        eraseOpenList_ofClosed children]

/-- Pointwise form for ordered derivations. -/
theorem eraseOpenList_ofClosed {goals : List Pattern}
    (derivations : DerivationList definition goals) :
    (OpenDerivationList.ofClosed (context := []) derivations).eraseOpen =
      rawToOpenList derivations.erase := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      rw [OpenDerivationList.ofClosed, OpenDerivationList.eraseOpen, DerivationList.erase,
        rawToOpenList, eraseOpen_ofClosed head, eraseOpenList_ofClosed tail]

end

end Mettapedia.GSLT.ProofPlans
