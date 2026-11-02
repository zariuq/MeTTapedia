import Mettapedia.Logic.HOL.CurriedExistentialProofs
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs

/-!
# Logical inhabitance of an indexed motive

A source method produces a value in its motive predicate. Logical induction
uses the proposition that such a value exists. Introduction retains the
produced value; elimination opens one result witness for the continuation.
The result carrier stays explicit and an empty predicate fibre stays empty.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedMotiveInhabitance

open CurriedPredicates FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {index space result : Ty Base}
    (motive : Term Const Γ (index ⇒ space ⇒ result ⇒ .prop))

def predicate : Term Const Γ (space ⇒ index ⇒ .prop) :=
  .lam (.lam (existsValue [] (.app (.app (weaken (weaken motive)) (.var .vz)) (.var (.vs .vz)))))

theorem predicate_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (predicate motive) = predicate (HOL.subst images motive) := by
  simp only [predicate, HOL.subst, existsValue_subst, subst_weaken, Subst.lift]
  rfl

def beta {assumptions : List (Formula Const Γ)} (point : Term Const Γ space) (target : Term Const Γ index) :
    ProofSyntax Const assumptions (.eq (.app (.app (predicate motive) point) target)
      (existsValue [] (.app (.app motive target) point))) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2
      (existsValue [] (.app (.app (weaken (weaken motive)) (.var .vz)) (.var (.vs .vz)))) point target)
  simp only [instantiate, existsValue_subst, HOL.subst, Subst.single, Subst.lift,
    PredicateFixedPoint.subst_single_weaken, subst_weaken]
  have cancel : HOL.subst (Subst.single target) (HOL.rename Rename.weaken point) = point :=
    PredicateFixedPoint.subst_single_weaken target point
  simp only [predicate, cancel]

theorem beta_free {assumptions : List (Formula Const Γ)} (point : Term Const Γ space) (target : Term Const Γ index) :
    (beta motive (assumptions := assumptions) point target).FunctionExtensionalityFree := by
  unfold beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

def introduce {assumptions : List (Formula Const Γ)}
    (point : Term Const Γ space) (target : Term Const Γ index) (value : Term Const Γ result)
    (typed : ProofSyntax Const assumptions (.app (.app (.app motive target) point) value)) :
    ProofSyntax Const assumptions (.app (.app (predicate motive) point) target) :=
  .impE (.eqPropER (beta motive point target))
    (existsValue_intro [] (.app (.app motive target) point) PUnit.unit value typed)

theorem introduce_free {assumptions : List (Formula Const Γ)}
    (point : Term Const Γ space) (target : Term Const Γ index) (value : Term Const Γ result)
    (typed : ProofSyntax Const assumptions (.app (.app (.app motive target) point) value))
    (free : typed.FunctionExtensionalityFree) :
    (introduce motive point target value typed).FunctionExtensionalityFree :=
  ⟨beta_free _ _ _, existsValue_intro_free _ _ _ _ _ free⟩

def eliminate {assumptions : List (Formula Const Γ)}
    (point : Term Const Γ space) (target : Term Const Γ index) (goal : Formula Const Γ)
    (present : ProofSyntax Const assumptions (.app (.app (predicate motive) point) target))
    (continuation : ProofSyntax Const
      (.app (weaken (.app (.app motive target) point)) (.var .vz) :: weakenHyps assumptions) (weaken goal)) :
    ProofSyntax Const assumptions goal := by
  have witnessed := ProofSyntax.impE (.eqPropEL (beta motive point target)) present
  have simplified : ProofSyntax Const assumptions
      (.ex (.app (weaken (.app (.app motive target) point)) (.var .vz))) := by
    apply ProofSyntax.castIndices rfl ?_ witnessed
    have identity : HOL.subst (fun entry => Term.var entry) (.app (.app motive target) point) =
        .app (.app motive target) point := ProofSyntax.term_subst_of_identity (fun _ => rfl) _
    simp only [existsValue, abstractArguments, applyArguments, identity]
  exact .exE simplified continuation

theorem eliminate_free {assumptions : List (Formula Const Γ)}
    (point : Term Const Γ space) (target : Term Const Γ index) (goal : Formula Const Γ)
    (present : ProofSyntax Const assumptions (.app (.app (predicate motive) point) target))
    (continuation : ProofSyntax Const
      (.app (weaken (.app (.app motive target) point)) (.var .vz) :: weakenHyps assumptions) (weaken goal))
    (presentFree : present.FunctionExtensionalityFree) (continuationFree : continuation.FunctionExtensionalityFree) :
    (eliminate motive point target goal present continuation).FunctionExtensionalityFree := by
  unfold eliminate
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact ⟨beta_free _ _ _, presentFree⟩
  · exact continuationFree

#print axioms predicate_subst
#print axioms introduce_free
#print axioms eliminate_free

end Mettapedia.Logic.HOL.IndexedMotiveInhabitance
