import Mettapedia.Logic.HOL.SetDependentSumProofs

/-!
# Retained projections of constructed ordered pairs

Selection chooses a first field admitting a second field, then chooses that
second field. Reconstruction requires an actual pair-existence proof.
The beta laws on constructor pairs follow from retained injectivity.
No projection or computation axiom is added.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetPairProjectionProofs
open SetComprehensionProofs SetMembershipProofs SetPairingProofs
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

private theorem renameNewest {added prior : Ty Unit} :
    HOL.rename (Rename.weaken (σ := added)) (Term.var .vz : Term Const (prior :: Γ) prior) =
      .var (.vs .vz) := rfl

def firstBody (pair : Term Const Γ object) : Formula Const (object :: Γ) :=
  .ex (.eq (ordered core epsilon (.var (.vs .vz)) (.var .vz)) (HOL.weaken (HOL.weaken pair)))

def pairExists (pair : Term Const Γ object) : Formula Const Γ := .ex (firstBody core epsilon pair)

@[simp] theorem subst_pairExists (theta : Subst Const Γ Ξ) (pair : Term Const Γ object) :
    HOL.subst theta (pairExists core epsilon pair) = pairExists core epsilon (HOL.subst theta pair) := by
  simp only [pairExists,firstBody,HOL.subst,subst_ordered,HOL.subst_weaken,Subst.lift]
  simp only [renameNewest]

theorem rename_pairExists (rho : Rename Unit Γ Ξ) (pair : Term Const Γ object) :
    HOL.rename rho (pairExists core epsilon pair) = pairExists core epsilon (HOL.rename rho pair) := by
  simpa only [HOL.subst_ofRename] using subst_pairExists core epsilon (Subst.ofRename rho) pair

def first (pair : Term Const Γ object) : Term Const Γ object :=
  SelectionProofs.selected (weakenCtx Γ epsilon) (firstBody core epsilon pair)

def secondBody (pair : Term Const Γ object) : Formula Const (object :: Γ) :=
  .eq (ordered core epsilon (HOL.weaken (first core epsilon pair)) (.var .vz)) (HOL.weaken pair)

def second (pair : Term Const Γ object) : Term Const Γ object :=
  SelectionProofs.selected (weakenCtx Γ epsilon) (secondBody core epsilon pair)

@[simp] theorem subst_firstBody (theta : Subst Const Γ Ξ) (pair : Term Const Γ object) :
    HOL.subst (Subst.lift theta) (firstBody core epsilon pair) =
      firstBody core epsilon (HOL.subst theta pair) := by
  simp only [firstBody,HOL.subst,subst_ordered,HOL.subst_weaken,Subst.lift]
  simp only [renameNewest]

@[simp] theorem subst_first (theta : Subst Const Γ Ξ) (pair : Term Const Γ object) :
    HOL.subst theta (first core epsilon pair) = first core epsilon (HOL.subst theta pair) := by
  simp only [first,SelectionProofs.selected,HOL.subst,subst_firstBody,subst_weakenCtx]

@[simp] theorem subst_secondBody (theta : Subst Const Γ Ξ) (pair : Term Const Γ object) :
    HOL.subst (Subst.lift theta) (secondBody core epsilon pair) =
      secondBody core epsilon (HOL.subst theta pair) := by
  simp only [secondBody,HOL.subst,subst_ordered,HOL.subst_weaken,subst_first,Subst.lift]

@[simp] theorem subst_second (theta : Subst Const Γ Ξ) (pair : Term Const Γ object) :
    HOL.subst theta (second core epsilon pair) = second core epsilon (HOL.subst theta pair) := by
  simp only [second,SelectionProofs.selected,HOL.subst,subst_secondBody,subst_weakenCtx]

theorem rename_first (rho : Rename Unit Γ Ξ) (pair : Term Const Γ object) :
    HOL.rename rho (first core epsilon pair) = first core epsilon (HOL.rename rho pair) := by
  simpa only [HOL.subst_ofRename] using subst_first core epsilon (Subst.ofRename rho) pair

theorem rename_second (rho : Rename Unit Γ Ξ) (pair : Term Const Γ object) :
    HOL.rename rho (second core epsilon pair) = second core epsilon (HOL.rename rho pair) := by
  simpa only [HOL.subst_ofRename] using subst_second core epsilon (Subst.ofRename rho) pair

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

private theorem substVariables {type : Ty Unit} (term : Term Const Γ type) :
    HOL.subst (fun {_} index => Term.var index) term = term := subst_id term

private theorem substSuccessors {type added : Ty Unit} (term : Term Const Γ type) :
    HOL.subst (fun {_} index => Term.var (Var.vs (σ := added) index)) term =
      HOL.rename Rename.weaken term := subst_ofRename Rename.weaken term

def existsOfEquality (left right pair : Term Const Γ object)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) pair)) :
    ProofSyntax Const Δ (pairExists core epsilon pair) := by
  apply ProofSyntax.exI left
  apply ProofSyntax.exI right
  apply ProofSyntax.castIndices rfl ?_ equal
  simp only [instantiate,HOL.subst,subst_ordered,HOL.subst_weaken,Subst.lift,Subst.single]
  simp only [HOL.weaken,HOL.subst_rename,Subst.single,Rename.weaken]
  simp only [substVariables]

def constructorExists (left right : Term Const Γ object) :
    ProofSyntax Const Δ (pairExists core epsilon (ordered core epsilon left right)) :=
  existsOfEquality core epsilon left right _ (.eqRefl _)

def firstSpecification (pair : Term Const Γ object)
    (selection : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (existsPair : ProofSyntax Const Δ (pairExists core epsilon pair)) :
    ProofSyntax Const Δ (.ex (secondBody core epsilon pair)) := by
  apply ProofSyntax.castIndices rfl ?_
    (SelectionProofs.specification (weakenCtx Γ epsilon) (firstBody core epsilon pair) selection existsPair)
  simp only [firstBody,secondBody,first,instantiate,HOL.subst,subst_ordered,HOL.subst_weaken,Subst.lift,Subst.single]
  simp only [HOL.weaken,HOL.subst_rename,Subst.single,Rename.weaken]
  simp only [substVariables]

def reconstruct (pair : Term Const Γ object)
    (selection : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (existsPair : ProofSyntax Const Δ (pairExists core epsilon pair)) :
    ProofSyntax Const Δ (.eq (ordered core epsilon (first core epsilon pair) (second core epsilon pair)) pair) := by
  apply ProofSyntax.castIndices rfl ?_
    (SelectionProofs.specification (weakenCtx Γ epsilon) (secondBody core epsilon pair) selection
      (firstSpecification core epsilon pair selection existsPair))
  simp only [secondBody,instantiate,subst_ordered,HOL.subst,Subst.single,substituteWeak,second]

def beta (left right : Term Const Γ object) (laws : Laws core epsilon Δ) :
    ProofSyntax Const Δ (.and
      (.eq (first core epsilon (ordered core epsilon left right)) left)
      (.eq (second core epsilon (ordered core epsilon left right)) right)) :=
  orderedInjective core epsilon _ _ left right laws
    (reconstruct core epsilon _ laws.selection (constructorExists core epsilon left right))

theorem existsOfEquality_free (left right pair : Term Const Γ object)
    (equal : ProofSyntax Const Δ (.eq (ordered core epsilon left right) pair))
    (free : equal.FunctionExtensionalityFree) :
    (existsOfEquality core epsilon left right pair equal).FunctionExtensionalityFree := by
  simpa [existsOfEquality,ProofSyntax.FunctionExtensionalityFree] using free

theorem constructorExists_free (left right : Term Const Γ object) :
    (constructorExists (Δ := Δ) core epsilon left right).FunctionExtensionalityFree :=
  existsOfEquality_free core epsilon _ _ _ _ trivial

theorem firstSpecification_free (pair : Term Const Γ object)
    (selection : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (existsPair : ProofSyntax Const Δ (pairExists core epsilon pair))
    (selectionFree : selection.FunctionExtensionalityFree) (existenceFree : existsPair.FunctionExtensionalityFree) :
    (firstSpecification core epsilon pair selection existsPair).FunctionExtensionalityFree := by
  simpa [firstSpecification] using SelectionProofs.specification_free (weakenCtx Γ epsilon)
    (firstBody core epsilon pair) selection existsPair selectionFree existenceFree

theorem reconstruct_free (pair : Term Const Γ object)
    (selection : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ epsilon)))
    (existsPair : ProofSyntax Const Δ (pairExists core epsilon pair))
    (selectionFree : selection.FunctionExtensionalityFree) (existenceFree : existsPair.FunctionExtensionalityFree) :
    (reconstruct core epsilon pair selection existsPair).FunctionExtensionalityFree := by
  simpa [reconstruct] using SelectionProofs.specification_free (weakenCtx Γ epsilon)
    (secondBody core epsilon pair) selection (firstSpecification core epsilon pair selection existsPair)
    selectionFree (firstSpecification_free core epsilon _ _ _ selectionFree existenceFree)

theorem beta_free (left right : Term Const Γ object) (laws : Laws core epsilon Δ) (free : laws.Free) :
    (beta core epsilon left right laws).FunctionExtensionalityFree :=
  orderedInjective_free core epsilon _ _ _ _ laws _ free
    (reconstruct_free core epsilon _ _ _ free.selection (constructorExists_free core epsilon _ _))

end Mettapedia.Logic.HOL.SetPairProjectionProofs

