import Mettapedia.Logic.HOL.ConstructorPositionEdges
import Mettapedia.Logic.HOL.CurriedPredicateProofs
import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.IndexedConstructorRootProofs

/-!
# Retained beta programs for curried constructor queries

The two- and three-argument programs retain each beta step. Their result is
the actual sequential typed substitution under the remaining binders.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.CurriedGuardProgramProofs
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  {assumptions : List (Formula Const Γ)} {first second third result : Ty Base}

def beta2 (body : Term Const (second :: first :: Γ) result)
    (a : Term Const Γ first) (b : Term Const Γ second) :
    ProofSyntax Const assumptions (.eq (.app (.app (.lam (.lam body)) a) b)
      (instantiate b (HOL.subst (Subst.lift (Subst.single a)) body))) :=
  .eqTrans (.eqApp b (.beta a (.lam body)))
    (.beta b (HOL.subst (Subst.lift (Subst.single a)) body))

def beta3 (body : Term Const (third :: second :: first :: Γ) result)
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    ProofSyntax Const assumptions (.eq (.app (.app (.app (.lam (.lam (.lam body))) a) b) c)
      (instantiate c (HOL.subst (Subst.lift (Subst.single b))
        (HOL.subst (Subst.lift (Subst.lift (Subst.single a))) body)))) :=
  .eqTrans (.eqApp c (beta2 (.lam body) a b))
    (.beta c (HOL.subst (Subst.lift (Subst.single b))
      (HOL.subst (Subst.lift (Subst.lift (Subst.single a))) body)))

theorem beta2_free (body : Term Const (second :: first :: Γ) result)
    (a : Term Const Γ first) (b : Term Const Γ second) :
    (beta2 (assumptions := assumptions) body a b).FunctionExtensionalityFree := by
  simp only [beta2, ProofSyntax.FunctionExtensionalityFree, and_self]

theorem beta3_free (body : Term Const (third :: second :: first :: Γ) result)
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    (beta3 (assumptions := assumptions) body a b c).FunctionExtensionalityFree := by
  exact ⟨beta2_free (.lam body) a b, True.intro⟩

def conjunctionProgram {index space : Ty Base}
    (family : Term Const Γ (space ⇒ .prop)) (root : Term Const Γ (space ⇒ index ⇒ .prop)) :
    Term Const Γ (space ⇒ index ⇒ .prop) :=
  .lam (.lam (.and (.app (weaken (weaken family)) (.var (.vs .vz)))
    (.app (.app (weaken (weaken root)) (.var (.vs .vz))) (.var .vz))))

@[simp] theorem subst_conjunctionProgram {index space : Ty Base} {Ξ : Ctx Base}
    (theta : Subst Const Γ Ξ) (family : Term Const Γ (space ⇒ .prop))
    (root : Term Const Γ (space ⇒ index ⇒ .prop)) :
    HOL.subst theta (conjunctionProgram family root) =
      conjunctionProgram (HOL.subst theta family) (HOL.subst theta root) := by
  simp [conjunctionProgram, HOL.subst, subst_weaken, Subst.lift, Rename.weaken]

section Reading
universe u' v'
variable {Target : Type u'} {Symbols : Ty Target → Type v'}

@[simp] theorem read_conjunctionProgram {index space : Ty Base}
    (reading : TermInterpretation Base Const Target Symbols)
    (family : Term Const Γ (space ⇒ .prop)) (root : Term Const Γ (space ⇒ index ⇒ .prop)) :
    reading.term (conjunctionProgram family root) =
      conjunctionProgram (reading.term family) (reading.term root) := by
  simp only [conjunctionProgram, TermInterpretation.term_lam, TermInterpretation.term_and,
    TermInterpretation.term_app, TermInterpretation.term_weaken, TermInterpretation.term_var, Var.mapTypes]

end Reading

@[irreducible] def conjunctionProgram_beta {index space : Ty Base}
    (family : Term Const Γ (space ⇒ .prop)) (root : Term Const Γ (space ⇒ index ⇒ .prop))
    (value : Term Const Γ space) (target : Term Const Γ index) :
    ProofSyntax Const assumptions (.eq (.app (.app (conjunctionProgram family root) value) target)
      (.and (.app family value) (.app (.app root value) target))) := by
  apply ProofSyntax.castIndices rfl ?_ (beta2
    (.and (.app (weaken (weaken family)) (.var (.vs .vz)))
      (.app (.app (weaken (weaken root)) (.var (.vs .vz))) (.var .vz))) value target)
  simp [conjunctionProgram, instantiate, HOL.subst, subst_weaken, Subst.single, Subst.lift,
    subst_rename, Rename.weaken, PredicateFixedPoint.subst_single_weaken]
  exact ProofSyntax.term_subst_of_identity (fun _ => rfl) value

theorem conjunctionProgram_beta_free {index space : Ty Base}
    (family : Term Const Γ (space ⇒ .prop)) (root : Term Const Γ (space ⇒ index ⇒ .prop))
    (value : Term Const Γ space) (target : Term Const Γ index) :
    (conjunctionProgram_beta (assumptions := assumptions) family root value target).FunctionExtensionalityFree := by
  unfold conjunctionProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta2_free _ _ _

#print axioms conjunctionProgram_beta
#print axioms conjunctionProgram_beta_free
end Mettapedia.Logic.HOL.CurriedGuardProgramProofs

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}

theorem restrictedPredicate_subst (theta : Subst Const Γ Ξ) (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature)) :
    HOL.subst theta (restrictedPredicate signature occurrence condition payload) =
      restrictedPredicate signature occurrence (HOL.subst theta condition) (HOL.subst theta payload) := by
  unfold restrictedPredicate
  rw [abstractArguments_subst theta _ _ (restrictedBody_natural _ _ _ _)]
  apply congrArg (abstractArguments _)
  funext laterContext later arguments
  simp only [restrictedBody, HOL.subst_comp]
  rfl

theorem restrictedGuard_subst (theta : Subst Const Γ Ξ) (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (condition : Term Const Γ (handlerType (signature.get occurrence)))
    (payload : Term Const Γ (payloadType signature)) :
    HOL.subst theta (restrictedGuard signature occurrence condition payload) =
      restrictedGuard signature occurrence (HOL.subst theta condition) (HOL.subst theta payload) := by
  rw [restrictedGuard, existsArguments_subst, restrictedPredicate_subst]
  rfl
end Mettapedia.Logic.HOL.FiniteConstructorEncoding

namespace Mettapedia.Logic.HOL.ConstructorDataPredicates
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}

theorem guard_subst (theta : Subst Const Γ Ξ) (signature : List (List (Ty Base)))
    (conditions : Conditions Const Γ signature) (payload : Term Const Γ (payloadType signature)) :
    HOL.subst theta (guard signature conditions payload) =
      guard signature (fun occurrence => HOL.subst theta (conditions occurrence)) (HOL.subst theta payload) := by
  rw [guard, any_subst, List.map_ofFn]
  apply congrArg any
  apply congrArg List.ofFn
  funext occurrence
  exact restrictedGuard_subst theta signature occurrence (conditions occurrence) payload
end Mettapedia.Logic.HOL.ConstructorDataPredicates

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
open FiniteConstructorEncoding CurriedPredicates CurriedGuardProgramProofs
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  (inventory : ConstructorPrograms Const Γ)

theorem shapeGuard_subst (theta : Subst Const Γ Ξ) (tag : Term Const Γ inventory.number)
    (payload : Term Const Γ (payloadType inventory.fields)) :
    HOL.subst theta (inventory.shapeGuard tag payload) =
      (inventory.subst theta).shapeGuard (HOL.subst theta tag) (HOL.subst theta payload) := by
  rw [shapeGuard, ConstructorDataPredicates.guard_subst]
  congr 1
  funext occurrence
  simp only [shapeCondition, conjoin_subst, constant_subst, HOL.subst, ConstructorPrograms.subst]

theorem resultGuard_subst (theta : Subst Const Γ Ξ) (payload : Term Const Γ (payloadType inventory.fields))
    (index : Term Const Γ inventory.index) :
    HOL.subst theta (inventory.resultGuard payload index) =
      (inventory.subst theta).resultGuard (HOL.subst theta payload) (HOL.subst theta index) := by
  rw [resultGuard, ConstructorDataPredicates.guard_subst]
  congr 1
  funext occurrence
  simp only [resultCondition, conjoin_subst, equalTo, abstractArguments_subst,
    equalTo_natural, ConstructorPrograms.subst]
  apply congrArg (conjoin _ _)
  apply congrArg (abstractArguments _)
  funext laterContext later arguments
  simp only [HOL.subst_comp]
  rfl

variable {space : Ty Base}
  (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))

theorem rootCondition_subst (theta : Subst Const Γ Ξ) (value : Term Const Γ space)
    (index : Term Const Γ inventory.index) (occurrence : Fin inventory.fields.length) :
    HOL.subst theta (inventory.rootCondition construct value index occurrence) =
      (inventory.subst theta).rootCondition (HOL.subst theta construct) (HOL.subst theta value) (HOL.subst theta index) occurrence := by
  unfold rootCondition
  rw [abstractArguments_subst theta _ _ (inventory.rootBody_natural construct value index occurrence)]
  apply congrArg (abstractArguments _)
  funext laterContext later arguments
  simp only [rootBody, ConstructorPrograms.subst, HOL.subst_comp]
  rfl

theorem rootIndex_subst (theta : Subst Const Γ Ξ) (value : Term Const Γ space)
    (index : Term Const Γ inventory.index) :
    HOL.subst theta (inventory.rootIndex construct value index) =
      (inventory.subst theta).rootIndex (HOL.subst theta construct) (HOL.subst theta value) (HOL.subst theta index) := by
  rw [rootIndex, any_subst, List.map_ofFn]
  change any _ = any _
  apply congrArg any
  apply congrArg List.ofFn
  funext occurrence
  change HOL.subst theta (existsArguments (inventory.fields.get occurrence)
    (inventory.rootCondition construct value index occurrence)) = _
  exact (existsArguments_subst theta _ _).trans
    (congrArg (existsArguments (inventory.fields.get occurrence))
      (inventory.rootCondition_subst construct theta value index occurrence))

variable {assumptions : List (Formula Const Γ)}

private theorem cancel_beneath_two {first second type : Ty Base}
    (a : Term Const Γ first) (b : Term Const Γ second) (term : Term Const Γ type) :
    HOL.subst (Subst.single b) (HOL.subst (Subst.lift (Subst.single a)) (HOL.subst beneathTwo term)) = term := by
  rw [HOL.subst_comp, HOL.subst_comp]
  exact ProofSyntax.term_subst_of_identity (fun _ => rfl) term

private theorem cancel_weaken {first type : Ty Base}
    (a : Term Const Γ first) (term : Term Const Γ type) :
    HOL.subst (Subst.single a) (HOL.rename Rename.weaken term) = term :=
  PredicateFixedPoint.subst_single_weaken a term

@[irreducible] def shapeProgram_beta (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields)) :
    ProofSyntax Const assumptions (.eq (.app (.app inventory.shapeProgram tag) payload) (inventory.shapeGuard tag payload)) := by
  apply ProofSyntax.castIndices rfl ?_ (beta2
    ((inventory.subst beneathTwo).shapeGuard (.var (.vs .vz)) (.var .vz)) tag payload)
  simp only [shapeProgram, instantiate, shapeGuard_subst]
  dsimp only [ConstructorPrograms.subst]
  simp only [HOL.subst, Subst.lift, Subst.single, cancel_weaken]
  apply congrArg (Term.eq _)
  unfold shapeGuard
  apply congrArg (fun conditions => ConstructorDataPredicates.guard inventory.fields conditions payload)
  funext occurrence
  unfold shapeCondition
  simp only [cancel_beneath_two tag payload]

@[irreducible] def rootProgram_beta (value : Term Const Γ space) (index : Term Const Γ inventory.index) :
    ProofSyntax Const assumptions (.eq (.app (.app (inventory.rootProgram construct) value) index)
      (inventory.rootIndex construct value index)) := by
  apply ProofSyntax.castIndices rfl ?_ (beta2
    ((inventory.subst beneathTwo).rootIndex (HOL.subst beneathTwo construct) (.var (.vs .vz)) (.var .vz)) value index)
  simp only [rootProgram, instantiate, rootIndex_subst]
  dsimp only [ConstructorPrograms.subst]
  simp only [cancel_beneath_two value index construct, HOL.subst, Subst.lift, Subst.single, cancel_weaken]
  apply congrArg (Term.eq _)
  unfold rootIndex
  apply congrArg any
  apply congrArg List.ofFn
  funext occurrence
  apply congrArg (existsArguments (inventory.fields.get occurrence))
  unfold rootCondition
  apply congrArg (abstractArguments _)
  funext laterContext later arguments
  unfold rootBody
  simp only [cancel_beneath_two value index]

theorem shapeProgram_beta_free (tag : Term Const Γ inventory.number) (payload : Term Const Γ (payloadType inventory.fields)) :
    (inventory.shapeProgram_beta (assumptions := assumptions) tag payload).FunctionExtensionalityFree := by
  unfold shapeProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta2_free _ _ _

theorem rootProgram_beta_free (value : Term Const Γ space) (index : Term Const Γ inventory.index) :
    (inventory.rootProgram_beta construct (assumptions := assumptions) value index).FunctionExtensionalityFree := by
  unfold rootProgram_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact beta2_free _ _ _

#print axioms shapeProgram_beta
#print axioms rootProgram_beta
end Mettapedia.Logic.HOL.IndexedConstructorGuards.ConstructorPrograms
