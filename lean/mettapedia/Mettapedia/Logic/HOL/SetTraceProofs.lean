import Mettapedia.Logic.HOL.SetDependentSumProofs

/-!
# Retained application for set traces

Application selects the second coordinates at an input. The coordinate bound
is justified from the ordered-pair construction and the union law. Applying
the dependent-union abstraction computes the supplied value on its domain;
the domain guard and set-extensionality premise remain explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetTraceProofs
open SetComprehensionProofs SetMembershipProofs SetPairingProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (mapping unionLaw extensionality)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

structure Laws (assumptions : List (Formula Const Γ)) where
  pairing : SetPairingProofs.Laws core epsilon assumptions
  union : ProofSyntax Const assumptions (lawAt core unionLaw)
  extensionality : ProofSyntax Const assumptions (lawAt core extensionality)

def Laws.prepend {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (formula : Formula Const Γ) : Laws core epsilon (formula :: Δ) where
  pairing := laws.pairing.prepend formula
  union := laws.union.prepend formula
  extensionality := laws.extensionality.prepend formula

def Laws.weaken {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (added : Ty Unit) : Laws core epsilon (weakenHyps (σ := added) Δ) where
  pairing := laws.pairing.weaken added
  union := weakenLaw core _ laws.union
  extensionality := weakenLaw core _ laws.extensionality

def coordinates (relation : Term Const Γ object) : Term Const Γ object :=
  .app (.const (core .union)) (.app (.const (core .union)) relation)

def application (relation point : Term Const Γ object) : Term Const Γ object :=
  separate core (coordinates core relation)
    (.lam (member core (ordered core epsilon (HOL.weaken point) (.var .vz)) (HOL.weaken relation)))

def abstraction (domain : Term Const Γ object) (family : Term Const Γ mapping) : Term Const Γ object :=
  SetDependentSumProofs.sum core epsilon domain family

@[simp] theorem subst_coordinates (theta : Subst Const Γ Ξ) (relation : Term Const Γ object) :
    HOL.subst theta (coordinates core relation) = coordinates core (HOL.subst theta relation) := by
  simp only [coordinates,HOL.subst]

@[simp] theorem subst_application (theta : Subst Const Γ Ξ) (relation point : Term Const Γ object) :
    HOL.subst theta (application core epsilon relation point) =
      application core epsilon (HOL.subst theta relation) (HOL.subst theta point) := by
  simp only [application,separate,member,HOL.subst,subst_coordinates,subst_ordered,HOL.subst_weaken,Subst.lift]

theorem rename_application (rho : Rename Unit Γ Ξ) (relation point : Term Const Γ object) :
    HOL.rename rho (application core epsilon relation point) =
      application core epsilon (HOL.rename rho relation) (HOL.rename rho point) := by
  simpa only [HOL.subst_ofRename] using subst_application core epsilon (Subst.ofRename rho) relation point

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

def pairCoordinate (relation point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core (ordered core epsilon point value) relation)) :
    ProofSyntax Const Δ (member core value (coordinates core relation)) := by
  have inner := SetFamilyUnionProofs.unionIntro core relation
    (ordered core epsilon point value) (unordered core epsilon point value) laws.union admitted
    (rightMem core epsilon (unordered core epsilon point point) (unordered core epsilon point value) laws.pairing)
  exact SetFamilyUnionProofs.unionIntro core (.app (.const (core .union)) relation)
    (unordered core epsilon point value) value laws.union inner (rightMem core epsilon point value laws.pairing)

def eliminate (relation point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core value (application core epsilon relation point))) :
    ProofSyntax Const Δ (member core (ordered core epsilon point value) relation) := by
  apply ProofSyntax.castIndices rfl ?_
    (separationProperty core (coordinates core relation) value
      (member core (ordered core epsilon (HOL.weaken point) (.var .vz)) (HOL.weaken relation))
      laws.pairing.separation admitted)
  simp only [instantiate,member,subst_ordered,HOL.subst,Subst.single,substituteWeak]

def introduce (relation point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core (ordered core epsilon point value) relation)) :
    ProofSyntax Const Δ (member core value (application core epsilon relation point)) := by
  apply separationIntro core (coordinates core relation) value
    (member core (ordered core epsilon (HOL.weaken point) (.var .vz)) (HOL.weaken relation))
    laws.pairing.separation (pairCoordinate core epsilon relation point value laws admitted)
  apply ProofSyntax.castIndices rfl ?_ admitted
  simp only [instantiate,member,subst_ordered,HOL.subst,Subst.single,substituteWeak]

def beta (domain : Term Const Γ object) (family : Term Const Γ mapping) (point : Term Const Γ object)
    (laws : Laws core epsilon Δ) (inDomain : ProofSyntax Const Δ (member core point domain)) :
    ProofSyntax Const Δ (.eq (application core epsilon (abstraction core epsilon domain family) point)
      (.app family point)) := by
  apply ProofSyntax.impE (SetComprehensionProofs.extensionality core
    (application core epsilon (abstraction core epsilon domain family) point) (.app family point) laws.extensionality)
  apply ProofSyntax.allI
  let raised := laws.weaken object
  have inDomainRaised : ProofSyntax Const (weakenHyps (σ := object) Δ)
      (member core (HOL.weaken point) (HOL.weaken domain)) := PredicateFixedPoint.weakenProof inDomain
  have forward : ProofSyntax Const (weakenHyps (σ := object) Δ) (.imp
      (member core (.var .vz) (application core epsilon
        (SetDependentSumProofs.sum core epsilon (HOL.weaken domain) (HOL.weaken family)) (HOL.weaken point)))
      (member core (.var .vz) (.app (HOL.weaken family) (HOL.weaken point)))) :=
    .impI (.andER (SetDependentSumProofs.eliminate core epsilon (HOL.weaken domain) (HOL.weaken family)
      (HOL.weaken point) (.var .vz) ((raised.prepend _).pairing) ((raised.prepend _).union)
      (eliminate core epsilon _ _ _ (raised.prepend _) (.hyp 0))))
  have backward : ProofSyntax Const (weakenHyps (σ := object) Δ) (.imp
      (member core (.var .vz) (.app (HOL.weaken family) (HOL.weaken point)))
      (member core (.var .vz) (application core epsilon
        (SetDependentSumProofs.sum core epsilon (HOL.weaken domain) (HOL.weaken family)) (HOL.weaken point)))) :=
    .impI (introduce core epsilon _ _ _ (raised.prepend _)
      (SetDependentSumProofs.introduce core epsilon (HOL.weaken domain) (HOL.weaken family)
        (HOL.weaken point) (.var .vz) ((raised.prepend _).pairing) ((raised.prepend _).union)
        (inDomainRaised.prepend _) (.hyp 0)))
  apply ProofSyntax.castIndices rfl ?_ (.andI forward backward)
  simp only [abstraction,HOL.weaken,rename_application,SetDependentSumProofs.rename_sum,member,HOL.rename]

structure Laws.Free {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) : Prop where
  pairing : laws.pairing.Free
  union : laws.union.FunctionExtensionalityFree
  extensionality : laws.extensionality.FunctionExtensionalityFree

theorem Laws.prepend_free {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (formula : Formula Const Γ) (free : laws.Free) : (laws.prepend formula).Free where
  pairing := laws.pairing.prepend_free formula free.pairing
  union := by simpa [Laws.prepend,ProofSyntax.prepend] using free.union
  extensionality := by simpa [Laws.prepend,ProofSyntax.prepend] using free.extensionality

theorem Laws.weaken_free {core : Core Const} {epsilon : ClosedTerm Const (SelectionProofs.Selection object)}
    (laws : Laws core epsilon Δ) (added : Ty Unit) (free : laws.Free) : (laws.weaken added).Free where
  pairing := laws.pairing.weaken_free added free.pairing
  union := weakenLaw_free (added := added) core _ laws.union free.union
  extensionality := weakenLaw_free (added := added) core _ laws.extensionality free.extensionality

theorem pairCoordinate_free (relation point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core (ordered core epsilon point value) relation))
    (lawsFree : laws.Free) (admittedFree : admitted.FunctionExtensionalityFree) :
    (pairCoordinate core epsilon relation point value laws admitted).FunctionExtensionalityFree := by
  apply SetFamilyUnionProofs.unionIntro_free core _ _ _ _ _ _ lawsFree.union
  · exact SetFamilyUnionProofs.unionIntro_free core _ _ _ _ _ _ lawsFree.union admittedFree
      (rightMem_free core epsilon _ _ _ lawsFree.pairing)
  · exact rightMem_free core epsilon _ _ _ lawsFree.pairing

theorem eliminate_free (relation point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core value (application core epsilon relation point)))
    (lawsFree : laws.Free) (admittedFree : admitted.FunctionExtensionalityFree) :
    (eliminate core epsilon relation point value laws admitted).FunctionExtensionalityFree := by
  simp [eliminate,separationProperty,ProofSyntax.FunctionExtensionalityFree,admittedFree]
  exact (separation_free core _ _ _ _).mpr lawsFree.pairing.separation

theorem introduce_free (relation point value : Term Const Γ object) (laws : Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core (ordered core epsilon point value) relation))
    (lawsFree : laws.Free) (admittedFree : admitted.FunctionExtensionalityFree) :
    (introduce core epsilon relation point value laws admitted).FunctionExtensionalityFree := by
  apply separationIntro_free core _ _ _ _ _ _ lawsFree.pairing.separation
  · exact pairCoordinate_free core epsilon _ _ _ _ _ lawsFree admittedFree
  · simpa using admittedFree

theorem beta_free (domain : Term Const Γ object) (family : Term Const Γ mapping) (point : Term Const Γ object)
    (laws : Laws core epsilon Δ) (inDomain : ProofSyntax Const Δ (member core point domain))
    (lawsFree : laws.Free) (domainFree : inDomain.FunctionExtensionalityFree) :
    (beta core epsilon domain family point laws inDomain).FunctionExtensionalityFree := by
  have lifted := laws.weaken_free object lawsFree
  simp only [beta,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  refine ⟨?_,?_,?_⟩
  · simpa [SetComprehensionProofs.extensionality,ProofSyntax.FunctionExtensionalityFree] using lawsFree.extensionality
  · apply SetDependentSumProofs.eliminate_free
    · exact ((laws.weaken object).prepend_free _ lifted).pairing
    · exact ((laws.weaken object).prepend_free _ lifted).union
    · exact eliminate_free core epsilon _ _ _ _ _ ((laws.weaken object).prepend_free _ lifted) trivial
  · apply introduce_free
    · exact (laws.weaken object).prepend_free _ lifted
    · apply SetDependentSumProofs.introduce_free
      · exact ((laws.weaken object).prepend_free _ lifted).pairing
      · exact ((laws.weaken object).prepend_free _ lifted).union
      · simpa [ProofSyntax.prepend,PredicateFixedPoint.weakenProof] using domainFree
      · trivial

end Mettapedia.Logic.HOL.SetTraceProofs

