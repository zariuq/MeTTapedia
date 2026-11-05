import Mettapedia.Logic.HOL.ConstructorArgumentMap

/-!
# Universal laws from retained constructor-argument recovery

The recovery callback already works at every typed substitution and every
explicit transport of the original hypotheses. Applying it in the context
of three fresh variables yields a retained universal law on the original
admission domain. No inverse on the ambient payload type is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorArgumentMap

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {first source target third : Ty Base} {premises : List (Formula Const Γ)}

def recoveryStatement (lower : Term Const Γ (source ⇒ target))
    (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third)) : Formula Const Γ :=
  .all (.all (.all (.imp
    (GuardedConstructorProjections.admitted (weaken (weaken (weaken domain)))
      (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
    (.eq (.app (weaken (weaken (weaken raise)))
      (.app (weaken (weaken (weaken lower))) (.var (.vs .vz)))) (.var (.vs .vz))))))

@[irreducible] def recoveryLaw (lower : Term Const Γ (source ⇒ target))
    (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third))
    (recover : Recovery premises lower raise domain) :
    ProofSyntax Const premises (recoveryStatement lower raise domain) := by
  let Ω := third :: source :: first :: Γ
  let rho : Rename Base Γ Ω := fun index => .vs (.vs (.vs index))
  let images : Subst Const Γ Ω := Subst.ofRename rho
  let tag : Term Const Ω first := .var (.vs (.vs .vz))
  let payload : Term Const Ω source := .var (.vs .vz)
  let children : Term Const Ω third := .var .vz
  let guarded := GuardedConstructorProjections.admitted (HOL.subst images domain) tag payload children
  let assumptions := guarded :: premises.map (HOL.subst images)
  let transport : ProofSyntax.OccurrenceMap (premises.map (HOL.subst images)) assumptions :=
    { index := Fin.succ, get_eq := fun _ => rfl }
  have recovered := recover images transport tag payload children (.hyp 0)
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.castIndices ?_ ?_ recovered
  · simp only [assumptions, guarded, GuardedConstructorProjections.admitted, ConstructorProjections.apply,
      images, weakenHyps, List.map_map, HOL.weaken, HOL.subst_ofRename,
      HOL.rename_comp, rho, Rename.weaken, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro formula _
    exact HOL.subst_ofRename _ formula
  · simp only [images, payload, HOL.subst_ofRename, HOL.weaken, HOL.rename_comp, rho, Rename.weaken]

theorem recoveryLaw_free (lower : Term Const Γ (source ⇒ target))
    (raise : Term Const Γ (target ⇒ source))
    (domain : Term Const Γ (GuardedConstructorProjections.Admission first source third))
    (recover : Recovery premises lower raise domain) (recoverFree : Recovery.Free recover) :
    (recoveryLaw lower raise domain recover).FunctionExtensionalityFree := by
  unfold recoveryLaw
  simp only [ProofSyntax.FunctionExtensionalityFree, ProofSyntax.functionExtensionalityFree_castIndices]
  apply recoverFree
  trivial

#print axioms recoveryLaw
#print axioms recoveryLaw_free

end Mettapedia.Logic.HOL.ConstructorArgumentMap
