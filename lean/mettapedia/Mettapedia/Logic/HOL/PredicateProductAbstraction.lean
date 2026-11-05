import Mettapedia.Logic.HOL.PredicateProducts

/-!
# Lambda membership in a guarded dependent product

The body is checked under its actual argument guard and arbitrary retained
hypotheses. Abstraction discharges that guard using beta and dependent-product
introduction; it does not require either the domain or its fibres inhabited.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.PredicateProducts
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {domain result : Ty Base} {Δ : List (Formula Const Γ)}

@[irreducible] def lambdaMember (predicate : Term Const Γ (domain ⇒ .prop))
    (family : Term Const (domain :: Γ) (result ⇒ .prop))
    (body : Term Const (domain :: Γ) result)
    (typed : ProofSyntax Const (.app (weaken predicate) (.var .vz) :: weakenHyps Δ) (.app family body)) :
    ProofSyntax Const Δ (.app (pi predicate family) (.lam body)) := by
  have cancels : instantiate (.var (.vz : Var (domain :: Γ) domain))
      (rename (Rename.lift Rename.weaken) body) = body := by
    rw [instantiate, subst_rename]
    trans subst Subst.id body
    · apply subst_ext
      intro type index
      cases index <;> rfl
    · exact subst_id body
  let computation : ProofSyntax Const (.app (weaken predicate) (.var .vz) :: weakenHyps Δ)
      (.eq (.app (weaken (.lam body)) (.var .vz)) body) :=
    .castIndices rfl (congrArg (Term.eq (.app (weaken (.lam body)) (.var .vz))) cancels)
      (.beta (.var .vz) (rename (Rename.lift Rename.weaken) body))
  exact introduce predicate family (.lam body) (.impE (.eqPropER (.eqAppArg family computation)) typed)

theorem lambdaMember_free (predicate : Term Const Γ (domain ⇒ .prop))
    (family : Term Const (domain :: Γ) (result ⇒ .prop))
    (body : Term Const (domain :: Γ) result)
    (typed : ProofSyntax Const (.app (weaken predicate) (.var .vz) :: weakenHyps Δ) (.app family body))
    (free : typed.FunctionExtensionalityFree) :
    (lambdaMember predicate family body typed).FunctionExtensionalityFree := by
  unfold lambdaMember
  apply introduce_free
  exact ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro,free⟩

#print axioms lambdaMember
#print axioms lambdaMember_free
end Mettapedia.Logic.HOL.PredicateProducts
