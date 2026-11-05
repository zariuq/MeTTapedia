import Mettapedia.Logic.HOL.SetPairingProofs

/-!
# Uniform retained membership schema for constructed pairs

The three object parameters remain quantified in one checked theorem. Later
consumers can instantiate this theorem rather than reconstruct the image and
selection argument at each occurrence. All theory hypotheses remain attached.
Native cached instantiation and discharge are separate consumers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetPairingSchemas
open SetComprehensionProofs SetPairingProofs
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
variable (epsilon : ClosedTerm Const (SelectionProofs.Selection SetPairingProofs.object))
variable {Δ : List (ClosedFormula Const)}

def membershipStatement : ClosedFormula Const :=
  .all (.all (.all (.and
    (.imp (member core (.var .vz) (unordered core epsilon (.var (.vs (.vs .vz))) (.var (.vs .vz))))
      (.or (.eq (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz)))))
    (.imp (.or (.eq (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz))))
      (member core (.var .vz) (unordered core epsilon (.var (.vs (.vs .vz))) (.var (.vs .vz))))))))

def membershipProof (laws : Laws core epsilon Δ) : ProofSyntax Const Δ (membershipStatement core epsilon) :=
  .allI (.allI (.allI (membership core epsilon (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)
    (((laws.weaken object).weaken object).weaken object))))

theorem membershipProof_free (laws : Laws core epsilon Δ) (free : laws.Free) :
    (membershipProof core epsilon laws).FunctionExtensionalityFree :=
  membership_free core epsilon _ _ _ _
    (Laws.weaken_free ((laws.weaken object).weaken object) object
      (Laws.weaken_free (laws.weaken object) object (laws.weaken_free object free)))

variable {Γ : Ctx Unit} {assumptions : List (Formula Const Γ)}

theorem membershipStatement_form : weakenCtx Γ (membershipStatement core epsilon) =
    .all (.all (.all (.and
      (.imp (member core (.var .vz) (unordered core epsilon (.var (.vs (.vs .vz))) (.var (.vs .vz))))
        (.or (.eq (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz)))))
      (.imp (.or (.eq (.var .vz) (.var (.vs (.vs .vz)))) (.eq (.var .vz) (.var (.vs .vz))))
        (member core (.var .vz) (unordered core epsilon (.var (.vs (.vs .vz))) (.var (.vs .vz)))))))) := by
  let rho : Rename Unit [] Γ := fun index => nomatch index
  have reading := rename_weakenCtx (Γ' := []) rho (membershipStatement core epsilon)
  rw [weakenCtx_nil] at reading
  rw [← reading]
  simp only [membershipStatement, HOL.rename, member, rename_unordered, Rename.lift]

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.rename Rename.weaken term) = term := instantiate_weaken point term

private theorem substVariables {type : Ty Unit} (term : Term Const Γ type) :
    HOL.subst (fun {_} index => Term.var index) term = term := subst_id term

private theorem substSuccessors {type added : Ty Unit} (term : Term Const Γ type) :
    HOL.subst (fun {_} index => Term.var (Var.vs (σ := added) index)) term =
      HOL.rename Rename.weaken term := subst_ofRename Rename.weaken term

def specialize (left right point : Term Const Γ object)
    (proof : ProofSyntax Const assumptions (weakenCtx Γ (membershipStatement core epsilon))) :
    ProofSyntax Const assumptions (.and
      (.imp (member core point (unordered core epsilon left right)) (.or (.eq point left) (.eq point right)))
      (.imp (.or (.eq point left) (.eq point right)) (member core point (unordered core epsilon left right)))) := by
  have normalized := proof.castIndices rfl (membershipStatement_form core epsilon)
  apply ProofSyntax.castIndices rfl ?_ (.allE point (.allE right (.allE left normalized)))
  simp only [instantiate, HOL.subst, subst_unordered, member, Subst.lift, Subst.single]
  simp only [HOL.subst_rename, HOL.subst,
    Subst.lift, Subst.single, Rename.weaken, HOL.rename]
  simp only [substVariables, substSuccessors, substituteWeak]

def rulesFromSchema (proof : ProofSyntax Const assumptions (weakenCtx Γ (membershipStatement core epsilon))) :
    MembershipRules core epsilon assumptions where
  left left right := .impE (.andER (specialize core epsilon left right left proof)) (.orIL (.eqRefl left))
  right left right := .impE (.andER (specialize core epsilon left right right proof)) (.orIR (.eqRefl right))
  elimination left right point := .andEL (specialize core epsilon left right point proof)

theorem specialize_free (left right point : Term Const Γ object)
    (proof : ProofSyntax Const assumptions (weakenCtx Γ (membershipStatement core epsilon)))
    (free : proof.FunctionExtensionalityFree) :
    (specialize core epsilon left right point proof).FunctionExtensionalityFree := by
  simpa [specialize, ProofSyntax.FunctionExtensionalityFree] using free

theorem rulesFromSchema_free (proof : ProofSyntax Const assumptions (weakenCtx Γ (membershipStatement core epsilon)))
    (free : proof.FunctionExtensionalityFree) : (rulesFromSchema core epsilon proof).Free where
  left left right := by
    change (specialize core epsilon left right left proof).FunctionExtensionalityFree ∧ True
    exact ⟨specialize_free core epsilon left right left proof free, trivial⟩
  right left right := by
    change (specialize core epsilon left right right proof).FunctionExtensionalityFree ∧ True
    exact ⟨specialize_free core epsilon left right right proof free, trivial⟩
  elimination left right point := by
    change (specialize core epsilon left right point proof).FunctionExtensionalityFree
    exact specialize_free core epsilon left right point proof free

end Mettapedia.Logic.HOL.SetPairingSchemas
