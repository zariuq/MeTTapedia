import Mettapedia.Logic.HOL.PairingReconstruction

/-!
# Uniform membership schemas for abstract pairing operations

Both operation terms remain explicit parameters. Membership specialization
and ordered-field recovery produce retained proofs under the supplied schema;
the schema must subsequently be proved and discharged for each representation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.PairingReconstructionSchemas
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {object : Ty Base}
variable (membership : ClosedTerm Const (object ⇒ object ⇒ .prop))
  (pairing : ClosedTerm Const (object ⇒ object ⇒ object))
variable {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

def member (point bound : Term Const Γ object) : Formula Const Γ :=
  .app (.app (weakenCtx Γ membership) point) bound

def pair (left right : Term Const Γ object) : Term Const Γ object :=
  .app (.app (weakenCtx Γ pairing) left) right

def operations : PairingReconstruction.Operations Const Γ object :=
  PairingReconstruction.termOperations (weakenCtx Γ membership) (weakenCtx Γ pairing)

theorem rename_member (rho : Rename Base Γ Ξ) (point bound : Term Const Γ object) :
    HOL.rename rho (member membership point bound) =
      member membership (HOL.rename rho point) (HOL.rename rho bound) := by
  simp only [member, HOL.rename, rename_weakenCtx]

theorem rename_pair (rho : Rename Base Γ Ξ) (left right : Term Const Γ object) :
    HOL.rename rho (pair pairing left right) =
      pair pairing (HOL.rename rho left) (HOL.rename rho right) := by
  simp only [pair, HOL.rename, rename_weakenCtx]

theorem subst_member (theta : Subst Const Γ Ξ) (point bound : Term Const Γ object) :
    HOL.subst theta (member membership point bound) =
      member membership (HOL.subst theta point) (HOL.subst theta bound) := by
  simp only [member, HOL.subst, subst_weakenCtx]

theorem subst_pair (theta : Subst Const Γ Ξ) (left right : Term Const Γ object) :
    HOL.subst theta (pair pairing left right) =
      pair pairing (HOL.subst theta left) (HOL.subst theta right) := by
  simp only [pair, HOL.subst, subst_weakenCtx]

def membershipStatement : ClosedFormula Const :=
  .all (.all (.all (.and
    (.imp (member membership (.var .vz) (pair pairing (.var (.vs (.vs .vz))) (.var (.vs .vz))))
      (.or (.eq (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz)))))
    (.imp (.or (.eq (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz))))
      (member membership (.var .vz) (pair pairing (.var (.vs (.vs .vz))) (.var (.vs .vz))))))))

theorem membershipStatement_form : weakenCtx Γ (membershipStatement membership pairing) =
    .all (.all (.all (.and
      (.imp (member membership (.var .vz) (pair pairing (.var (.vs (.vs .vz))) (.var (.vs .vz))))
        (.or (.eq (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz)))))
      (.imp (.or (.eq (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz))))
        (member membership (.var .vz) (pair pairing (.var (.vs (.vs .vz))) (.var (.vs .vz)))))))) := by
  let rho : Rename Base [] Γ := fun index => nomatch index
  have reading := rename_weakenCtx (Γ' := []) rho (membershipStatement membership pairing)
  rw [weakenCtx_nil] at reading
  rw [← reading]
  simp only [membershipStatement, HOL.rename, rename_member, rename_pair, Rename.lift]

private theorem substVariables {type : Ty Base} (term : Term Const Γ type) :
    HOL.subst (fun {_} index => Term.var index) term = term := subst_id term

private theorem substSuccessors {type added : Ty Base} (term : Term Const Γ type) :
    HOL.subst (fun {_} index => Term.var (Var.vs (σ := added) index)) term =
      HOL.rename Rename.weaken term := subst_ofRename Rename.weaken term

private theorem substituteWeak {type added : Ty Base}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.rename Rename.weaken term) = term := instantiate_weaken point term

def specialize (left right point : Term Const Γ object)
    (proof : ProofSyntax Const Δ (weakenCtx Γ (membershipStatement membership pairing))) :
    ProofSyntax Const Δ (.and
      (.imp (member membership point (pair pairing left right)) (.or (.eq point left) (.eq point right)))
      (.imp (.or (.eq point left) (.eq point right)) (member membership point (pair pairing left right)))) := by
  have normalized := proof.castIndices rfl (membershipStatement_form membership pairing)
  apply ProofSyntax.castIndices rfl ?_ (.allE point (.allE right (.allE left normalized)))
  simp only [instantiate, HOL.subst, subst_pair, subst_member, Subst.lift, Subst.single]
  simp only [HOL.subst_rename, HOL.subst, Subst.lift, Subst.single, Rename.weaken, HOL.rename]
  simp only [substVariables, substSuccessors, substituteWeak]

def rules (proof : ProofSyntax Const Δ (weakenCtx Γ (membershipStatement membership pairing))) :
    PairingReconstruction.Rules (operations membership pairing) Δ where
  left left right := .impE (.andER (specialize membership pairing left right left proof)) (.orIL (.eqRefl left))
  right left right := .impE (.andER (specialize membership pairing left right right proof)) (.orIR (.eqRefl right))
  elimination left right point := .andEL (specialize membership pairing left right point proof)

theorem specialize_free (left right point : Term Const Γ object)
    (proof : ProofSyntax Const Δ (weakenCtx Γ (membershipStatement membership pairing)))
    (free : proof.FunctionExtensionalityFree) :
    (specialize membership pairing left right point proof).FunctionExtensionalityFree := by
  simpa [specialize, ProofSyntax.FunctionExtensionalityFree] using free

theorem rules_free (proof : ProofSyntax Const Δ (weakenCtx Γ (membershipStatement membership pairing)))
    (free : proof.FunctionExtensionalityFree) : (rules membership pairing proof).Free where
  left left right := by
    change (specialize membership pairing left right left proof).FunctionExtensionalityFree ∧ True
    exact ⟨specialize_free membership pairing left right left proof free,trivial⟩
  right left right := by
    change (specialize membership pairing left right right proof).FunctionExtensionalityFree ∧ True
    exact ⟨specialize_free membership pairing left right right proof free,trivial⟩
  elimination left right point := by
    change (specialize membership pairing left right point proof).FunctionExtensionalityFree
    exact specialize_free membership pairing left right point proof free

def injectivity (left right first second : Term Const Γ object)
    (proof : ProofSyntax Const Δ (weakenCtx Γ (membershipStatement membership pairing))) :
    ProofSyntax Const Δ (.imp
      (.eq (PairingReconstruction.orderedBy (pair pairing) left right)
        (PairingReconstruction.orderedBy (pair pairing) first second))
      (.and (.eq left first) (.eq right second))) :=
  .impI (PairingReconstruction.orderedInjective (operations membership pairing) left right first second
    (rules membership pairing (proof.prepend _)) (.hyp 0))

theorem injectivity_free (left right first second : Term Const Γ object)
    (proof : ProofSyntax Const Δ (weakenCtx Γ (membershipStatement membership pairing)))
    (free : proof.FunctionExtensionalityFree) :
    (injectivity membership pairing left right first second proof).FunctionExtensionalityFree :=
  PairingReconstruction.orderedInjective_free (operations membership pairing) left right first second _ _
    (PairingReconstruction.termOperations_free _ _)
    (rules_free membership pairing (proof.prepend _)
      (by simpa [ProofSyntax.prepend] using free)) trivial

end Mettapedia.Logic.HOL.PairingReconstructionSchemas

