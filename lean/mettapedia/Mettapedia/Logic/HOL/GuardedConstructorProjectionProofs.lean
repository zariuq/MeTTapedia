import Mettapedia.Logic.HOL.GuardedConstructorProjections

/-!
# Retained computation of guarded constructor projections

An admitted source tuple gives an inhabited projection predicate. The
guarded uniqueness law applies only after the candidate's admission witness
has been recovered. Selection then yields the original second or third
field. Every proof retains the supplied guard and selection principle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.GuardedConstructorProjections
open ConstructorProjections (Constructor apply)
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {first second third carrier : Ty Base} {Δ : List (Formula Const Γ)}

private theorem subst_vars {type : Ty Base} (term : Term Const Γ type) :
    subst (fun {σ} (index : Var Γ σ) => Term.var index) term = term := subst_id term

private theorem subst_drop_shift {α type : Ty Base} (value : Term Const Γ α) (term : Term Const Γ type) :
    subst (Subst.comp (Subst.single value) (fun index => Term.var (.vs index))) term = term := by
  have identity : (Subst.comp (Subst.single value) (fun index => Term.var (.vs index)) : Subst Const Γ Γ) =
      (fun {type} (index : Var Γ type) => Term.var index) := by
    funext type index
    rfl
  rw [identity]
  exact subst_id term

def specialize (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor domain))
    (given : ProofSyntax Const Δ (admitted domain a b c)) :
    ProofSyntax Const Δ (components constructor domain a b c) := by
  have instantiated : ProofSyntax Const Δ (.imp (admitted domain a b c) (components constructor domain a b c)) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE c (.allE b (.allE a injectivity)))
    simp [instantiate,admitted,subst,subst_weaken,Subst.single,Subst.lift,Rename.weaken,
      subst_rename,subst_comp,subst_drop_shift,subst_vars]
  exact .impE instantiated given

def compare (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a a' : Term Const Γ first) (b b' : Term Const Γ second) (c c' : Term Const Γ third)
    (proof : ProofSyntax Const Δ (components constructor domain a b c)) :
    ProofSyntax Const Δ (.imp (admitted domain a' b' c')
      (.imp (.eq (apply constructor a' b' c') (apply constructor a b c)) (.and (.eq b' b) (.eq c' c)))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE c' (.allE b' (.allE a' proof)))
  simp [instantiate,admitted,subst,subst_weaken,Subst.single,Subst.lift,Rename.weaken,
    subst_rename,subst_comp,subst_drop_shift,subst_vars]

def second_exists (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (given : ProofSyntax Const Δ (admitted domain a b c)) :
    ProofSyntax Const Δ (.ex (secondBody constructor domain (apply constructor a b c))) := by
  refine .exI b (.exI a (.exI c ?_))
  apply ProofSyntax.castIndices rfl ?_ (.andI given (.eqRefl (apply constructor a b c)))
  simp [instantiate,admitted,subst,subst_weaken,Subst.single,Subst.lift,Rename.weaken,
    subst_rename,subst_comp,subst_drop_shift,subst_vars]

def third_exists (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (given : ProofSyntax Const Δ (admitted domain a b c)) :
    ProofSyntax Const Δ (.ex (thirdBody constructor domain (apply constructor a b c))) := by
  refine .exI c (.exI a (.exI b ?_))
  apply ProofSyntax.castIndices rfl ?_ (.andI given (.eqRefl (apply constructor a b c)))
  simp [instantiate,admitted,subst,subst_weaken,Subst.single,Subst.lift,Rename.weaken,
    subst_rename,subst_comp,subst_drop_shift,subst_vars]

def second_unique (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    ProofSyntax Const Δ (.imp (components constructor domain a b c)
      (.all (.imp (secondBody constructor domain (apply constructor a b c)) (.eq (.var .vz) (weaken b))))) := by
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.exE (.hyp 0)
  apply ProofSyntax.exE (.hyp 0)
  change ProofSyntax Const _ (.eq (.var (.vs (.vs .vz))) (weaken (weaken (weaken b))))
  refine .andEL (.impE (.impE (compare (weaken (weaken (weaken constructor))) (weaken (weaken (weaken domain)))
    (weaken (weaken (weaken a))) (.var (.vs .vz))
    (weaken (weaken (weaken b))) (.var (.vs (.vs .vz)))
    (weaken (weaken (weaken c))) (.var .vz) ?_) (.andEL (.hyp 0))) (.andER (.hyp 0)))
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp ⟨3,by simp [weakenHyps]⟩)
  simp [weakenHyps,weaken,rename_components]

def third_unique (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    ProofSyntax Const Δ (.imp (components constructor domain a b c)
      (.all (.imp (thirdBody constructor domain (apply constructor a b c)) (.eq (.var .vz) (weaken c))))) := by
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.exE (.hyp 0)
  apply ProofSyntax.exE (.hyp 0)
  change ProofSyntax Const _ (.eq (.var (.vs (.vs .vz))) (weaken (weaken (weaken c))))
  refine .andER (.impE (.impE (compare (weaken (weaken (weaken constructor))) (weaken (weaken (weaken domain)))
    (weaken (weaken (weaken a))) (.var (.vs .vz))
    (weaken (weaken (weaken b))) (.var .vz)
    (weaken (weaken (weaken c))) (.var (.vs (.vs .vz))) ?_) (.andEL (.hyp 0))) (.andER (.hyp 0)))
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp ⟨3,by simp [weakenHyps]⟩)
  simp [weakenHyps,weaken,rename_components]

def second_apply (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) :
    ProofSyntax Const Δ (.eq (.app (secondProjection selection constructor domain) value)
      (secondValue selection constructor domain value)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value
    (secondValue (weaken selection) (weaken constructor) (weaken domain) (.var .vz)))
  simp [secondProjection,instantiate,subst,Subst.single]

def third_apply (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) (value : Term Const Γ carrier) :
    ProofSyntax Const Δ (.eq (.app (thirdProjection selection constructor domain) value)
      (thirdValue selection constructor domain value)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value
    (thirdValue (weaken selection) (weaken constructor) (weaken domain) (.var .vz)))
  simp [thirdProjection,instantiate,subst,Subst.single]

def second_at (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor domain))
    (given : ProofSyntax Const Δ (admitted domain a b c)) :
    ProofSyntax Const Δ (.eq (.app (secondProjection selection constructor domain) (apply constructor a b c)) b) :=
  .eqTrans (second_apply selection constructor domain (apply constructor a b c))
    (ConstructorProjections.selected_eq selection (secondBody constructor domain (apply constructor a b c)) b choice
      (second_exists constructor domain a b c given)
      (.impE (second_unique constructor domain a b c) (specialize constructor domain a b c injectivity given)))

def third_at (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor domain))
    (given : ProofSyntax Const Δ (admitted domain a b c)) :
    ProofSyntax Const Δ (.eq (.app (thirdProjection selection constructor domain) (apply constructor a b c)) c) :=
  .eqTrans (third_apply selection constructor domain (apply constructor a b c))
    (ConstructorProjections.selected_eq selection (thirdBody constructor domain (apply constructor a b c)) c choice
      (third_exists constructor domain a b c given)
      (.impE (third_unique constructor domain a b c) (specialize constructor domain a b c injectivity given)))

theorem specialize_free (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor domain))
    (given : ProofSyntax Const Δ (admitted domain a b c))
    (injectivityFree : injectivity.FunctionExtensionalityFree) (givenFree : given.FunctionExtensionalityFree) :
    (specialize constructor domain a b c injectivity given).FunctionExtensionalityFree := by
  simpa [specialize,ProofSyntax.FunctionExtensionalityFree] using And.intro injectivityFree givenFree

theorem second_exists_free (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (given : ProofSyntax Const Δ (admitted domain a b c)) (free : given.FunctionExtensionalityFree) :
    (second_exists constructor domain a b c given).FunctionExtensionalityFree := by
  simpa [second_exists,ProofSyntax.FunctionExtensionalityFree] using free

theorem third_exists_free (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (given : ProofSyntax Const Δ (admitted domain a b c)) (free : given.FunctionExtensionalityFree) :
    (third_exists constructor domain a b c given).FunctionExtensionalityFree := by
  simpa [third_exists,ProofSyntax.FunctionExtensionalityFree] using free

theorem second_unique_free (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    (second_unique (Δ := Δ) constructor domain a b c).FunctionExtensionalityFree := by
  simp [second_unique,compare,ProofSyntax.FunctionExtensionalityFree]

theorem third_unique_free (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    (third_unique (Δ := Δ) constructor domain a b c).FunctionExtensionalityFree := by
  simp [third_unique,compare,ProofSyntax.FunctionExtensionalityFree]

theorem second_at_free (selection : Term Const Γ (SelectionProofs.Selection second))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor domain))
    (given : ProofSyntax Const Δ (admitted domain a b c))
    (choiceFree : choice.FunctionExtensionalityFree) (injectivityFree : injectivity.FunctionExtensionalityFree)
    (givenFree : given.FunctionExtensionalityFree) :
    (second_at selection constructor domain a b c choice injectivity given).FunctionExtensionalityFree := by
  unfold second_at
  constructor
  · simp [second_apply,ProofSyntax.FunctionExtensionalityFree]
  · apply ConstructorProjections.selected_eq_free _ _ _ _ _ _ choiceFree
    · exact second_exists_free _ _ _ _ _ given givenFree
    · exact ⟨second_unique_free _ _ _ _ _,specialize_free _ _ _ _ _ injectivity given injectivityFree givenFree⟩

theorem third_at_free (selection : Term Const Γ (SelectionProofs.Selection third))
    (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (injectivity : ProofSyntax Const Δ (fieldInjective constructor domain))
    (given : ProofSyntax Const Δ (admitted domain a b c))
    (choiceFree : choice.FunctionExtensionalityFree) (injectivityFree : injectivity.FunctionExtensionalityFree)
    (givenFree : given.FunctionExtensionalityFree) :
    (third_at selection constructor domain a b c choice injectivity given).FunctionExtensionalityFree := by
  unfold third_at
  constructor
  · simp [third_apply,ProofSyntax.FunctionExtensionalityFree]
  · apply ConstructorProjections.selected_eq_free _ _ _ _ _ _ choiceFree
    · exact third_exists_free _ _ _ _ _ given givenFree
    · exact ⟨third_unique_free _ _ _ _ _,specialize_free _ _ _ _ _ injectivity given injectivityFree givenFree⟩

def restrict_fieldInjective (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) :
    ProofSyntax Const Δ (.imp (ConstructorProjections.fieldInjective constructor) (fieldInjective constructor domain)) := by
  let Ω := third :: second :: first :: third :: second :: first :: Γ
  let a : Term Const Ω first := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  let b : Term Const Ω second := .var (.vs (.vs (.vs (.vs .vz))))
  let c : Term Const Ω third := .var (.vs (.vs (.vs .vz)))
  let a' : Term Const Ω first := .var (.vs (.vs .vz))
  let b' : Term Const Ω second := .var (.vs .vz)
  let c' : Term Const Ω third := .var .vz
  let raised : Term Const Ω (Constructor first second third carrier) :=
    weaken (weaken (weaken (weaken (weaken (weaken constructor)))))
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.impI
  change ProofSyntax Const _ (.and (.eq b' b) (.eq c' c))
  refine .impE (ConstructorProjections.compare raised a a' b b' c c'
    (ConstructorProjections.specialize raised a b c ?_)) (.hyp 0)
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp ⟨3,by simp [weakenHyps]⟩)
  simp [raised,weakenHyps,weaken,ConstructorProjections.rename_fieldInjective]

theorem restrict_fieldInjective_free (constructor : Term Const Γ (Constructor first second third carrier))
    (domain : Term Const Γ (Admission first second third)) :
    (restrict_fieldInjective (Δ := Δ) constructor domain).FunctionExtensionalityFree := by
  simp [restrict_fieldInjective,ConstructorProjections.compare,ConstructorProjections.specialize,
    ProofSyntax.FunctionExtensionalityFree]

#print axioms second_at_free
#print axioms third_at_free
#print axioms restrict_fieldInjective_free

end Mettapedia.Logic.HOL.GuardedConstructorProjections
