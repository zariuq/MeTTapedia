import Mettapedia.Logic.HOL.CurriedGuardProgramProofs

/-!
# Contextual constructor separation and the non-bottom motive

These proof programs retain open constructor and bottom terms. Quantifier
specialization and motive application use the ordinary substitution and beta
rules; neither operation assumes that the carrier has a chosen semantic model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorNonbottom

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {number payload space : Ty Base}
    (constructor : Term Const Γ (number ⇒ payload ⇒ (number ⇒ space) ⇒ space))
    (bottom : Term Const Γ space)

def separation : Formula Const Γ :=
  .all (.all (.all (.not (.eq
    (.app (.app (.app (weaken (weaken (weaken constructor))) (.var (.vs (.vs .vz))))
      (.var (.vs .vz))) (.var .vz))
    (weaken (weaken (weaken bottom)))))))

theorem subst_separation (images : Subst Const Γ Ξ) :
    subst images (separation constructor bottom) =
      separation (subst images constructor) (subst images bottom) := by
  simp [separation, subst, subst_weaken, Subst.lift, Rename.weaken]

private theorem subst_vars {type : Ty Base} (term : Term Const Γ type) :
    subst (fun index => .var index) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem subst_drop_shift {domain type : Ty Base}
    (argument : Term Const Γ domain) (term : Term Const Γ type) :
    subst (Subst.comp (Subst.single argument) (fun index => .var (.vs index))) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem subst_drop_two {first second type : Ty Base}
    (a : Term Const Γ first) (b : Term Const Γ second) (term : Term Const Γ type) :
    subst (Subst.comp (Subst.single b)
      (Subst.comp (Subst.lift (Subst.single a)) (fun index => .var (.vs (.vs index))))) term = term :=
  ProofSyntax.term_subst_of_identity (fun _ => rfl) term

variable {assumptions : List (Formula Const Γ)}

def specialize (tag : Term Const Γ number) (data : Term Const Γ payload)
    (children : Term Const Γ (number ⇒ space))
    (proof : ProofSyntax Const assumptions (separation constructor bottom)) :
    ProofSyntax Const assumptions
      (.not (.eq (.app (.app (.app constructor tag) data) children) bottom)) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.allE children (ProofSyntax.allE data (ProofSyntax.allE tag proof)))
  simp [instantiate, subst, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, subst_comp, subst_drop_shift, subst_drop_two, subst_vars, weaken]

theorem specialize_free (tag : Term Const Γ number) (data : Term Const Γ payload)
    (children : Term Const Γ (number ⇒ space))
    (proof : ProofSyntax Const assumptions (separation constructor bottom))
    (free : proof.FunctionExtensionalityFree) :
    (specialize constructor bottom tag data children proof).FunctionExtensionalityFree := by
  unfold specialize
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

def motive (index : Ty Base) : Term Const Γ (space ⇒ index ⇒ .prop) :=
  .lam (.lam (.not (.eq (.var (.vs .vz)) (weaken (weaken bottom)))))

theorem subst_motive (index : Ty Base) (images : Subst Const Γ Ξ) :
    subst images (motive bottom index) = motive (subst images bottom) index := by
  simp [motive, subst, subst_weaken, Subst.lift, Rename.weaken]

@[simp] private theorem single_weaken {domain type : Ty Base}
    (value : Term Const Γ domain) (term : Term Const Γ type) :
    subst (Subst.single value) (weaken term) = term :=
  instantiate_weaken value term

def motive_beta {index : Ty Base} (value : Term Const Γ space) (target : Term Const Γ index) :
    ProofSyntax Const assumptions
      (.eq (.app (.app (motive bottom index) value) target) (.not (.eq value bottom))) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2
      (.not (.eq (.var (.vs .vz)) (weaken (weaken bottom)))) value target)
  simp [motive, instantiate, subst, Subst.single, Subst.lift,
    PredicateFixedPoint.subst_single_weaken]
  exact PredicateFixedPoint.subst_single_weaken target value

theorem motive_beta_free {index : Ty Base} (value : Term Const Γ space) (target : Term Const Γ index) :
    (motive_beta bottom (assumptions := assumptions) value target).FunctionExtensionalityFree := by
  unfold motive_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

#print axioms subst_separation
#print axioms specialize_free
#print axioms subst_motive
#print axioms motive_beta_free

end Mettapedia.Logic.HOL.ConstructorNonbottom
