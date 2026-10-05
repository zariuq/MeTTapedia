import Mettapedia.Languages.VibeITP.Presentation.SubstitutionCorrespondence

/-!
# Sufficient signature snapshots for substitution

Replacement terms are part of the computation: their binders are inspected
when substitution shifts an image. The snapshot therefore covers the source
and every supplied image, including images outside the nominal count.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution

open ComputationalData ComputationalShift
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

theorem BindersAgree.getD {source target : Spec.Sig} (images : List Spec.Term)
    (agree : ComputationalShift.BindersAgree source target (termHeadsList images)) (index : Nat) :
    ComputationalShift.BindersAgree source target (termHeads (images.getD index (.bvar 0))) := by
  induction images generalizing index with
  | nil => intro symbol member; cases member
  | cons first rest ih =>
      cases index with
      | zero => exact agree.left
      | succ index => exact ih agree.right index

mutual

theorem substGo_on_heads (source target : Spec.Sig) (count : Nat) (images : List Spec.Term)
    (offset : Nat) (term : Spec.Term)
    (imagesAgree : ComputationalShift.BindersAgree source target (termHeadsList images))
    (agree : ComputationalShift.BindersAgree source target (termHeads term)) :
    Spec.substGo source count images offset term = Spec.substGo target count images offset term := by
  cases term with
  | bvar index =>
      rw [Spec.substGo, Spec.substGo]
      split
      · rfl
      · split
        · exact shift_on_heads source target offset 0 _ (BindersAgree.getD images imagesAgree _)
        · rfl
  | lit _ => rfl
  | app symbol terms =>
      rw [Spec.substGo, Spec.substGo, depth_on_heads source target (.app symbol terms) agree]
      split
      · rfl
      · rw [substGoArgs_eq, substGoArgs_eq, List.drop_zero, List.drop_zero, agree.head,
          substList_on_heads source target count images offset _ terms imagesAgree agree.tail]

theorem substList_on_heads (source target : Spec.Sig) (count : Nat) (images : List Spec.Term)
    (offset : Nat) (binders : List Nat) (terms : List Spec.Term)
    (imagesAgree : ComputationalShift.BindersAgree source target (termHeadsList images))
    (agree : ComputationalShift.BindersAgree source target (termHeadsList terms)) :
    substList source count images offset binders terms = substList target count images offset binders terms := by
  cases terms with
  | nil => rfl
  | cons first rest =>
      rw [substList, substList]
      split
      · rw [substGo_on_heads source target count images (offset + binders.headD 0) first imagesAgree agree.left,
          substList_on_heads source target count images offset binders.tail rest imagesAgree agree.right]
      · rfl

end

theorem substitution_on_heads (source target : Spec.Sig) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset : Nat)
    (imagesAgree : ComputationalShift.BindersAgree source target (termHeadsList images))
    (agree : ComputationalShift.BindersAgree source target (termHeads body)) :
    Spec.substBVars source count images body offset = Spec.substBVars target count images body offset := by
  rw [Spec.substBVars, Spec.substBVars]
  split
  · rfl
  · exact substGo_on_heads source target count images offset body imagesAgree agree

def substitutionSnapshot (signature : Spec.Sig) (body : Spec.Term) (images : List Spec.Term) : SignatureTable :=
  tableFor signature (termHeads body ++ termHeadsList images)

theorem substitutionSnapshot_binders (signature : Spec.Sig) (body : Spec.Term) (images : List Spec.Term) :
    ComputationalShift.BindersAgree (signatureOf (substitutionSnapshot signature body images)) signature
      (termHeads body ++ termHeadsList images) := by
  intro symbol used
  unfold bindersOf substitutionSnapshot
  rw [tableFor_lookup signature _ symbol, if_pos used]

theorem snapshot_substitution (signature : Spec.Sig) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset : Nat) :
    Spec.substBVars (signatureOf (substitutionSnapshot signature body images)) count images body offset =
      Spec.substBVars signature count images body offset :=
  substitution_on_heads _ _ count images body offset (substitutionSnapshot_binders signature body images).right
    (substitutionSnapshot_binders signature body images).left

theorem substitution_computes_for_signature (signature : Spec.Sig) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset : Nat) :
    Applies substitutionProgram computationalHost "vibe:subst"
      [encodeTable (substitutionSnapshot signature body images), natural count,
        .list (encodeTerms images), encode body, natural offset]
      (encodeResult (Spec.substBVars signature count images body offset)) := by
  rw [← snapshot_substitution signature count images body offset]
  exact substitution_computes _ _ _ _ _

theorem substitution_signature_result_exact (signature : Spec.Sig) (count : Nat) (images : List Spec.Term)
    (body : Spec.Term) (offset : Nat) (result : Term) :
    Applies substitutionProgram computationalHost "vibe:subst"
      [encodeTable (substitutionSnapshot signature body images), natural count,
        .list (encodeTerms images), encode body, natural offset] result ↔
      result = encodeResult (Spec.substBVars signature count images body offset) := by
  rw [substitution_result_exact, snapshot_substitution]

end Mettapedia.Languages.VibeITP.Presentation.ComputationalSubstitution
