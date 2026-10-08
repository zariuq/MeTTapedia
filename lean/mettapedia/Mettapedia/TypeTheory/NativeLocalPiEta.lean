import Mettapedia.TypeTheory.NativeLocalTypeOperations
import Mettapedia.TypeTheory.ContextualPiEta

/-!
# Generic-variable eta for native local products

Weakening a function and applying it to the newest variable recovers its
complete evaluation section. The context-comprehension identity supplies
the dependent result transport; the native abstraction equivalence then
recovers the original function.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalPiEta

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTypeOperations
open ContextualTypeOperations ContextualPiEta
open ContextualProductComparison (selfExtend)

universe u
variable {C : Type u} [Category.{u} C]
variable {X : Face.{u, u, u} C}

set_option backward.isDefEq.respectTransparency false in
theorem genericSection_eq_inverse (A : NativeType X)
    (B : NativeType (totalSpace A.decoded)) (function : (pi A B).decoded.sections) :
    genericSection (products C) (products_formation_substitution C) function =
      (functionEquiv A B).symm function := by
  let model := localModel C
  let s := model.wk A
  let lifted := totalReindexMap s A.decoded
  let g := selfExtend model (model.vz A)
  let weakened := reindexFunction (products C) (products_formation_substitution C) s function
  let body := (functionEquiv (A.reindex s) (B.reindex lifted)).symm weakened
  have functionRelated := (reindexFunction_heq (products C)
    (products_formation_substitution C) s function).symm
  have bodyRelated := functionEquiv_inverse_substitution s A B function weakened functionRelated
  have substituted := TypeOver.tmSub_heq (C := model) rfl bodyRelated g
  have actualApplication : HEq ((products C).app weakened (model.vz A))
      (model.tmSub body g) :=
    (substituteTerm_heq (C := presheafCwf C) (type := B.reindex lifted) body g).symm
  have composed := (TypeOver.tmSub_comp_heq (C := model)
    ((functionEquiv A B).symm function) lifted g).symm
  have identity : model.compS lifted g = model.idS (model.ext X A) :=
    lifted_generic_identity (C := model) A
  rw [identity] at composed
  apply eq_of_heq
  exact (genericSection_heq (products C) (products_formation_substitution C) function).trans
    (actualApplication.trans (substituted.trans (composed.trans
      ((heq_of_eq (model.tmSub_id ((functionEquiv A B).symm function))).trans (cast_heq _ _)))))

theorem products_eta (C : Type u) [Category.{u} C] :
    PiEta (products C) (products_formation_substitution C) := by
  intro X A B function
  rw [genericSection_eq_inverse A B function]
  exact eta (A := A) (B := B) function

end Mettapedia.TypeTheory.NativeLocalPiEta
