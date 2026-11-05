import Mettapedia.Logic.HOL.SetTraceProofs
import Mettapedia.Logic.HOL.SetSumProjectionProofs

/-!
# Retained dependent products of set traces

A trace is bounded by pairs from the declared domain and the members of its
possible output sets. Separation keeps exactly the traces whose application
has the required fibre type. Abstraction and application typing are retained
proof programs; the body-typing and argument-domain premises are explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetTraceProductProofs
open SetComprehensionProofs SetMembershipProofs SetPairingProofs SetTraceProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (mapping)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
  (epsilon : ClosedTerm Const (SelectionProofs.Selection object))
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

def values (domain : Term Const Γ object) (family : Term Const Γ mapping) : Term Const Γ object :=
  .app (.const (core .union)) (familyUnion core domain family)

def supportFamily (domain : Term Const Γ object) (family : Term Const Γ mapping) : Term Const Γ mapping :=
  .lam (HOL.weaken (values core domain family))

def support (domain : Term Const Γ object) (family : Term Const Γ mapping) : Term Const Γ object :=
  SetDependentSumProofs.sum core epsilon domain (supportFamily core domain family)

def pointwise (domain : Term Const Γ object) (family function : Term Const Γ mapping) : Formula Const Γ :=
  .all (.imp (member core (.var .vz) (HOL.weaken domain))
    (member core (.app (HOL.weaken function) (.var .vz)) (.app (HOL.weaken family) (.var .vz))))

def guard (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) : Formula Const Γ :=
  .all (.imp (member core (.var .vz) (HOL.weaken domain))
    (member core (application core epsilon (HOL.weaken relation) (.var .vz))
      (.app (HOL.weaken family) (.var .vz))))

def product (domain : Term Const Γ object) (family : Term Const Γ mapping) : Term Const Γ object :=
  separate core (power core (support core epsilon domain family))
    (.lam (guard core epsilon (HOL.weaken domain) (HOL.weaken family) (.var .vz)))

@[simp] theorem subst_values (theta : Subst Const Γ Ξ) (domain : Term Const Γ object)
    (family : Term Const Γ mapping) : HOL.subst theta (values core domain family) =
      values core (HOL.subst theta domain) (HOL.subst theta family) := by
  simp only [values,familyUnion,image,HOL.subst]

@[simp] theorem subst_supportFamily (theta : Subst Const Γ Ξ) (domain : Term Const Γ object)
    (family : Term Const Γ mapping) : HOL.subst theta (supportFamily core domain family) =
      supportFamily core (HOL.subst theta domain) (HOL.subst theta family) := by
  simp only [supportFamily,HOL.subst,HOL.subst_weaken,subst_values]

@[simp] theorem subst_support (theta : Subst Const Γ Ξ) (domain : Term Const Γ object)
    (family : Term Const Γ mapping) : HOL.subst theta (support core epsilon domain family) =
      support core epsilon (HOL.subst theta domain) (HOL.subst theta family) := by
  simp only [support,SetDependentSumProofs.subst_sum,subst_supportFamily]

@[simp] theorem subst_pointwise (theta : Subst Const Γ Ξ) (domain : Term Const Γ object)
    (family function : Term Const Γ mapping) : HOL.subst theta (pointwise core domain family function) =
      pointwise core (HOL.subst theta domain) (HOL.subst theta family) (HOL.subst theta function) := by
  simp only [pointwise,member,HOL.subst,HOL.subst_weaken,Subst.lift]

@[simp] theorem subst_guard (theta : Subst Const Γ Ξ) (domain : Term Const Γ object)
    (family : Term Const Γ mapping) (relation : Term Const Γ object) :
    HOL.subst theta (guard core epsilon domain family relation) =
      guard core epsilon (HOL.subst theta domain) (HOL.subst theta family) (HOL.subst theta relation) := by
  simp only [guard,member,HOL.subst,HOL.subst_weaken,subst_application,Subst.lift]

@[simp] theorem subst_product (theta : Subst Const Γ Ξ) (domain : Term Const Γ object)
    (family : Term Const Γ mapping) : HOL.subst theta (product core epsilon domain family) =
      product core epsilon (HOL.subst theta domain) (HOL.subst theta family) := by
  simp only [product,separate,power,HOL.subst,subst_support,subst_guard,HOL.subst_weaken,Subst.lift]

theorem rename_support (rho : Rename Unit Γ Ξ) (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.rename rho (support core epsilon domain family) =
      support core epsilon (HOL.rename rho domain) (HOL.rename rho family) := by
  simpa only [HOL.subst_ofRename] using subst_support core epsilon (Subst.ofRename rho) domain family

theorem rename_pointwise (rho : Rename Unit Γ Ξ) (domain : Term Const Γ object)
    (family function : Term Const Γ mapping) : HOL.rename rho (pointwise core domain family function) =
      pointwise core (HOL.rename rho domain) (HOL.rename rho family) (HOL.rename rho function) := by
  simpa only [HOL.subst_ofRename] using subst_pointwise core (Subst.ofRename rho) domain family function

theorem rename_guard (rho : Rename Unit Γ Ξ) (domain : Term Const Γ object)
    (family : Term Const Γ mapping) (relation : Term Const Γ object) :
    HOL.rename rho (guard core epsilon domain family relation) =
      guard core epsilon (HOL.rename rho domain) (HOL.rename rho family) (HOL.rename rho relation) := by
  simpa only [HOL.subst_ofRename] using subst_guard core epsilon (Subst.ofRename rho) domain family relation

theorem rename_product (rho : Rename Unit Γ Ξ) (domain : Term Const Γ object) (family : Term Const Γ mapping) :
    HOL.rename rho (product core epsilon domain family) =
      product core epsilon (HOL.rename rho domain) (HOL.rename rho family) := by
  simpa only [HOL.subst_ofRename] using subst_product core epsilon (Subst.ofRename rho) domain family

private theorem substituteWeak {type added : Ty Unit}
    (point : Term Const Γ added) (term : Term Const Γ type) :
    HOL.subst (Subst.single point) (HOL.weaken term) = term := instantiate_weaken point term

def pointwiseAt (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (point : Term Const Γ object) (body : ProofSyntax Const Δ (pointwise core domain family function))
    (inDomain : ProofSyntax Const Δ (member core point domain)) :
    ProofSyntax Const Δ (member core (.app function point) (.app family point)) := by
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ (.allE point body)) inDomain
  simp only [instantiate,member,HOL.subst,Subst.single,substituteWeak]

def guardAt (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation point : Term Const Γ object) (body : ProofSyntax Const Δ (guard core epsilon domain family relation))
    (inDomain : ProofSyntax Const Δ (member core point domain)) :
    ProofSyntax Const Δ (member core (application core epsilon relation point) (.app family point)) := by
  apply ProofSyntax.impE (ProofSyntax.castIndices rfl ?_ (.allE point body)) inDomain
  simp only [instantiate,member,HOL.subst,Subst.single,substituteWeak,subst_application]

def weakenPointwise (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (body : ProofSyntax Const Δ (pointwise core domain family function)) :
    ProofSyntax Const (weakenHyps (σ := object) Δ)
      (pointwise core (HOL.weaken domain) (HOL.weaken family) (HOL.weaken function)) := by
  apply ProofSyntax.castIndices rfl ?_ (PredicateFixedPoint.weakenProof body)
  simp only [HOL.weaken,rename_pointwise]

def supportBeta (domain : Term Const Γ object) (family : Term Const Γ mapping) (point : Term Const Γ object) :
    ProofSyntax Const Δ (.eq (.app (supportFamily core domain family) point) (values core domain family)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta point (HOL.weaken (values core domain family)))
  rw [instantiate_weaken]
  rfl

def supportIntro (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (inDomain : ProofSyntax Const Δ (member core point domain))
    (inValues : ProofSyntax Const Δ (member core value (values core domain family))) :
    ProofSyntax Const Δ (member core (ordered core epsilon point value) (support core epsilon domain family)) := by
  apply SetDependentSumProofs.introduce core epsilon domain (supportFamily core domain family)
    point value laws.pairing laws.union inDomain
  exact transportBound core value (.eqSymm (supportBeta core domain family point)) inValues

def supportOfTraceMember (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (point : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (body : ProofSyntax Const Δ (pointwise core domain family function))
    (admitted : ProofSyntax Const Δ (member core point (abstraction core epsilon domain function))) :
    ProofSyntax Const Δ (member core point (support core epsilon domain family)) := by
  have fields := SetSumProjectionProofs.typedFields core epsilon domain function point laws.pairing laws.union admitted
  let left := SetPairProjectionProofs.first core epsilon point
  let right := SetPairProjectionProofs.second core epsilon point
  have typed := pointwiseAt core domain family function left body (.andEL fields)
  have outputInUnion := familyUnionIntro core domain family left (.app function left)
    laws.union laws.pairing.replacement (.andEL fields) typed
  have fieldInValues := SetFamilyUnionProofs.unionIntro core (familyUnion core domain family)
    (.app function left) right laws.union outputInUnion (.andEL (.andER fields))
  exact transportValue core _ (.andER (.andER fields))
    (supportIntro core epsilon domain family left right laws (.andEL fields) fieldInValues)

def abstractionBound (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (body : ProofSyntax Const Δ (pointwise core domain family function)) :
    ProofSyntax Const Δ (included core (abstraction core epsilon domain function) (support core epsilon domain family)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.impI (supportOfTraceMember core epsilon (HOL.weaken domain) (HOL.weaken family)
      (HOL.weaken function) (.var .vz) ((laws.weaken object).prepend _)
      ((weakenPointwise core domain family function body).prepend _) (.hyp 0)))
  simp only [abstraction,HOL.weaken,SetDependentSumProofs.rename_sum,rename_support,member]

def abstractionGuard (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (body : ProofSyntax Const Δ (pointwise core domain family function)) :
    ProofSyntax Const Δ (guard core epsilon domain family (abstraction core epsilon domain function)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.impI (transportValue core (.app (HOL.weaken family) (.var .vz))
      (.eqSymm (beta core epsilon (HOL.weaken domain) (HOL.weaken function) (.var .vz)
        ((laws.weaken object).prepend _) (.hyp 0)))
      (pointwiseAt core (HOL.weaken domain) (HOL.weaken family) (HOL.weaken function) (.var .vz)
        ((weakenPointwise core domain family function body).prepend _) (.hyp 0))))
  simp only [abstraction,HOL.weaken,SetDependentSumProofs.rename_sum,member]

def introduce (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (bounded : ProofSyntax Const Δ (included core relation (support core epsilon domain family)))
    (typed : ProofSyntax Const Δ (guard core epsilon domain family relation)) :
    ProofSyntax Const Δ (member core relation (product core epsilon domain family)) := by
  apply separationIntro core (power core (support core epsilon domain family)) relation
    (guard core epsilon (HOL.weaken domain) (HOL.weaken family) (.var .vz)) laws.pairing.separation
    (.impE (.andER (powerset core _ relation laws.pairing.power)) bounded)
  apply ProofSyntax.castIndices rfl ?_ typed
  simp only [instantiate,subst_guard,HOL.subst,Subst.single,substituteWeak]

def abstractionTyped (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (body : ProofSyntax Const Δ (pointwise core domain family function)) :
    ProofSyntax Const Δ (member core (abstraction core epsilon domain function) (product core epsilon domain family)) :=
  introduce core epsilon domain family _ laws (abstractionBound core epsilon domain family function laws body)
    (abstractionGuard core epsilon domain family function laws body)

def productGuard (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core relation (product core epsilon domain family))) :
    ProofSyntax Const Δ (guard core epsilon domain family relation) := by
  apply ProofSyntax.castIndices rfl ?_ (separationProperty core (power core (support core epsilon domain family)) relation
    (guard core epsilon (HOL.weaken domain) (HOL.weaken family) (.var .vz)) laws.pairing.separation admitted)
  simp only [instantiate,subst_guard,HOL.subst,Subst.single,substituteWeak]

def applicationTyped (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation point : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core relation (product core epsilon domain family)))
    (inDomain : ProofSyntax Const Δ (member core point domain)) :
    ProofSyntax Const Δ (member core (application core epsilon relation point) (.app family point)) :=
  guardAt core epsilon domain family relation point (productGuard core epsilon domain family relation laws admitted) inDomain

def productBound (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core relation (product core epsilon domain family))) :
    ProofSyntax Const Δ (included core relation (support core epsilon domain family)) :=
  .impE (.andEL (powerset core (support core epsilon domain family) relation laws.pairing.power))
    (.andEL (separationElim core (power core (support core epsilon domain family)) relation
      (guard core epsilon (HOL.weaken domain) (HOL.weaken family) (.var .vz)) laws.pairing.separation admitted))

def membership (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ) :
    ProofSyntax Const Δ (.and
      (.imp (member core relation (product core epsilon domain family))
        (.and (included core relation (support core epsilon domain family)) (guard core epsilon domain family relation)))
      (.imp (.and (included core relation (support core epsilon domain family)) (guard core epsilon domain family relation))
        (member core relation (product core epsilon domain family)))) :=
  .andI (.impI (.andI (productBound core epsilon domain family relation (laws.prepend _) (.hyp 0))
      (productGuard core epsilon domain family relation (laws.prepend _) (.hyp 0))))
    (.impI (introduce core epsilon domain family relation (laws.prepend _) (.andEL (.hyp 0)) (.andER (.hyp 0))))

theorem pointwiseAt_free (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (point : Term Const Γ object) (body : ProofSyntax Const Δ (pointwise core domain family function))
    (inDomain : ProofSyntax Const Δ (member core point domain))
    (bodyFree : body.FunctionExtensionalityFree) (domainFree : inDomain.FunctionExtensionalityFree) :
    (pointwiseAt core domain family function point body inDomain).FunctionExtensionalityFree := by
  simp [pointwiseAt,ProofSyntax.FunctionExtensionalityFree,bodyFree,domainFree]

theorem guardAt_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation point : Term Const Γ object) (body : ProofSyntax Const Δ (guard core epsilon domain family relation))
    (inDomain : ProofSyntax Const Δ (member core point domain))
    (bodyFree : body.FunctionExtensionalityFree) (domainFree : inDomain.FunctionExtensionalityFree) :
    (guardAt core epsilon domain family relation point body inDomain).FunctionExtensionalityFree := by
  simp [guardAt,ProofSyntax.FunctionExtensionalityFree,bodyFree,domainFree]

theorem weakenPointwise_free (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (body : ProofSyntax Const Δ (pointwise core domain family function)) (free : body.FunctionExtensionalityFree) :
    (weakenPointwise core domain family function body).FunctionExtensionalityFree := by
  simpa [weakenPointwise,PredicateFixedPoint.weakenProof] using free

theorem supportBeta_free (domain : Term Const Γ object) (family : Term Const Γ mapping) (point : Term Const Γ object) :
    (supportBeta (Δ := Δ) core domain family point).FunctionExtensionalityFree := by
  simp [supportBeta,ProofSyntax.FunctionExtensionalityFree]

theorem supportIntro_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (point value : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (inDomain : ProofSyntax Const Δ (member core point domain))
    (inValues : ProofSyntax Const Δ (member core value (values core domain family)))
    (lawsFree : laws.Free) (domainFree : inDomain.FunctionExtensionalityFree)
    (valuesFree : inValues.FunctionExtensionalityFree) :
    (supportIntro core epsilon domain family point value laws inDomain inValues).FunctionExtensionalityFree := by
  apply SetDependentSumProofs.introduce_free
  · exact lawsFree.pairing
  · exact lawsFree.union
  · exact domainFree
  · exact transportBound_free core _ _ _ (supportBeta_free core domain family point) valuesFree

theorem supportOfTraceMember_free (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (point : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (body : ProofSyntax Const Δ (pointwise core domain family function))
    (admitted : ProofSyntax Const Δ (member core point (abstraction core epsilon domain function)))
    (lawsFree : laws.Free) (bodyFree : body.FunctionExtensionalityFree)
    (admittedFree : admitted.FunctionExtensionalityFree) :
    (supportOfTraceMember core epsilon domain family function point laws body admitted).FunctionExtensionalityFree := by
  have fieldsFree := SetSumProjectionProofs.typedFields_free core epsilon domain function point
    laws.pairing laws.union admitted lawsFree.pairing lawsFree.union admittedFree
  unfold supportOfTraceMember
  apply transportValue_free
  · exact fieldsFree
  · apply supportIntro_free
    · exact lawsFree
    · exact fieldsFree
    · apply SetFamilyUnionProofs.unionIntro_free
      · exact lawsFree.union
      · apply SetFamilyUnionProofs.introduce_free
        · exact lawsFree.union
        · exact lawsFree.pairing.replacement
        · exact fieldsFree
        · exact pointwiseAt_free core domain family function _ body _ bodyFree fieldsFree
      · exact fieldsFree

theorem abstractionBound_free (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (body : ProofSyntax Const Δ (pointwise core domain family function))
    (lawsFree : laws.Free) (bodyFree : body.FunctionExtensionalityFree) :
    (abstractionBound core epsilon domain family function laws body).FunctionExtensionalityFree := by
  simp only [abstractionBound,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  apply supportOfTraceMember_free
  · exact (laws.weaken object).prepend_free _ (laws.weaken_free object lawsFree)
  · simpa [ProofSyntax.prepend] using weakenPointwise_free core domain family function body bodyFree
  · trivial

theorem abstractionGuard_free (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (body : ProofSyntax Const Δ (pointwise core domain family function))
    (lawsFree : laws.Free) (bodyFree : body.FunctionExtensionalityFree) :
    (abstractionGuard core epsilon domain family function laws body).FunctionExtensionalityFree := by
  simp only [abstractionGuard,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  apply transportValue_free
  · exact beta_free core epsilon _ _ _ _ _
      ((laws.weaken object).prepend_free _ (laws.weaken_free object lawsFree)) trivial
  · apply pointwiseAt_free
    · simpa [ProofSyntax.prepend] using weakenPointwise_free core domain family function body bodyFree
    · trivial

theorem introduce_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (bounded : ProofSyntax Const Δ (included core relation (support core epsilon domain family)))
    (typed : ProofSyntax Const Δ (guard core epsilon domain family relation))
    (lawsFree : laws.Free) (boundedFree : bounded.FunctionExtensionalityFree) (typedFree : typed.FunctionExtensionalityFree) :
    (introduce core epsilon domain family relation laws bounded typed).FunctionExtensionalityFree := by
  unfold introduce
  apply separationIntro_free
  · exact lawsFree.pairing.separation
  · exact ⟨(powerset_free core _ _ laws.pairing.power).mpr lawsFree.pairing.power,boundedFree⟩
  · simpa using typedFree

theorem abstractionTyped_free (domain : Term Const Γ object) (family function : Term Const Γ mapping)
    (laws : SetTraceProofs.Laws core epsilon Δ) (body : ProofSyntax Const Δ (pointwise core domain family function))
    (lawsFree : laws.Free) (bodyFree : body.FunctionExtensionalityFree) :
    (abstractionTyped core epsilon domain family function laws body).FunctionExtensionalityFree :=
  introduce_free core epsilon domain family _ laws _ _ lawsFree
    (abstractionBound_free core epsilon domain family function laws body lawsFree bodyFree)
    (abstractionGuard_free core epsilon domain family function laws body lawsFree bodyFree)

theorem productGuard_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core relation (product core epsilon domain family)))
    (lawsFree : laws.Free) (admittedFree : admitted.FunctionExtensionalityFree) :
    (productGuard core epsilon domain family relation laws admitted).FunctionExtensionalityFree := by
  simp [productGuard,separationProperty,ProofSyntax.FunctionExtensionalityFree,separation_free,
    lawsFree.pairing.separation,admittedFree]

theorem applicationTyped_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation point : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core relation (product core epsilon domain family)))
    (inDomain : ProofSyntax Const Δ (member core point domain))
    (lawsFree : laws.Free) (admittedFree : admitted.FunctionExtensionalityFree) (domainFree : inDomain.FunctionExtensionalityFree) :
    (applicationTyped core epsilon domain family relation point laws admitted inDomain).FunctionExtensionalityFree :=
  guardAt_free core epsilon domain family relation point _ inDomain
    (productGuard_free core epsilon domain family relation laws admitted lawsFree admittedFree) domainFree

theorem productBound_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (admitted : ProofSyntax Const Δ (member core relation (product core epsilon domain family)))
    (lawsFree : laws.Free) (admittedFree : admitted.FunctionExtensionalityFree) :
    (productBound core epsilon domain family relation laws admitted).FunctionExtensionalityFree :=
  ⟨(powerset_free core _ _ laws.pairing.power).mpr lawsFree.pairing.power,
    separationElim_free core _ _ _ laws.pairing.separation admitted lawsFree.pairing.separation admittedFree⟩

theorem membership_free (domain : Term Const Γ object) (family : Term Const Γ mapping)
    (relation : Term Const Γ object) (laws : SetTraceProofs.Laws core epsilon Δ) (lawsFree : laws.Free) :
    (membership core epsilon domain family relation laws).FunctionExtensionalityFree :=
  ⟨⟨productBound_free core epsilon domain family relation _ _ (laws.prepend_free _ lawsFree) trivial,
    productGuard_free core epsilon domain family relation _ _ (laws.prepend_free _ lawsFree) trivial⟩,
    introduce_free core epsilon domain family relation _ _ _ (laws.prepend_free _ lawsFree) trivial trivial⟩

end Mettapedia.Logic.HOL.SetTraceProductProofs
