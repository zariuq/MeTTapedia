import Mettapedia.Logic.HOL.ConstructorFieldRepresentation

/-!
# Predicate transport along a represented field embedding

The target predicate is the direct image of the supplied source predicate.
It retains the source membership and encoding equation as existential data.
Injectivity is obtained from the field roundtrip when reflecting membership
on encoded values. No image condition on an arbitrary target predicate is
assumed, and no source predicate is discarded.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.ConstructorPredicateRepresentation
open ConstructorFieldRepresentation
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {source target : Ty Base} {Δ : List (Formula Const Γ)}

def witness (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (stored : Term Const Γ target) : Formula Const (source :: Γ) :=
  .and (.app (weaken predicate) (.var .vz))
    (.eq (.app (weaken encode) (.var .vz)) (weaken stored))

def body (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (stored : Term Const Γ target) : Formula Const Γ := .ex (witness encode predicate stored)

def lift (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop)) :
    Term Const Γ (target ⇒ .prop) := .lam (body (weaken encode) (weaken predicate) (.var .vz))

theorem body_subst (images : Subst Const Γ Ξ) (encode : Term Const Γ (source ⇒ target))
    (predicate : Term Const Γ (source ⇒ .prop)) (stored : Term Const Γ target) :
    subst images (body encode predicate stored) =
      body (subst images encode) (subst images predicate) (subst images stored) := by
  simp only [body,witness,subst,subst_weaken,Subst.lift]

theorem lift_subst (images : Subst Const Γ Ξ) (encode : Term Const Γ (source ⇒ target))
    (predicate : Term Const Γ (source ⇒ .prop)) :
    subst images (lift encode predicate) = lift (subst images encode) (subst images predicate) := by
  simp only [lift,subst,body_subst,subst_weaken,Subst.lift]

theorem lift_weaken (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    {carrier : Ty Base} :
    weaken (σ := carrier) (lift encode predicate) = lift (weaken encode) (weaken predicate) := by
  simpa only [weaken,subst_ofRename] using lift_subst (Subst.ofRename (Rename.weaken (σ := carrier))) encode predicate

def application (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (stored : Term Const Γ target) :
    ProofSyntax Const Δ (.eq (.app (lift encode predicate) stored) (body encode predicate stored)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta stored (body (weaken encode) (weaken predicate) (.var .vz)))
  simp only [instantiate,body_subst,subst,Subst.single]
  rw [show subst (Subst.single stored) (weaken encode) = encode from instantiate_weaken stored encode,
    show subst (Subst.single stored) (weaken predicate) = predicate from instantiate_weaken stored predicate]
  rfl

theorem instantiate_witness (encode : Term Const Γ (source ⇒ target))
    (predicate : Term Const Γ (source ⇒ .prop)) (stored : Term Const Γ target) (field : Term Const Γ source) :
    instantiate field (witness encode predicate stored) =
      .and (.app predicate field) (.eq (.app encode field) stored) := by
  simp only [witness,instantiate,subst,Subst.single]
  rw [show subst (Subst.single field) (weaken predicate) = predicate from instantiate_weaken field predicate,
    show subst (Subst.single field) (weaken encode) = encode from instantiate_weaken field encode,
    show subst (Subst.single field) (weaken stored) = stored from instantiate_weaken field stored]

def introduce (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (field : Term Const Γ source) (member : ProofSyntax Const Δ (.app predicate field)) :
    ProofSyntax Const Δ (.app (lift encode predicate) (.app encode field)) := by
  apply ProofSyntax.impE (.eqPropER (application encode predicate (.app encode field)))
  apply ProofSyntax.exI field
  exact ProofSyntax.castIndices rfl (instantiate_witness encode predicate (.app encode field) field).symm
    (.andI member (.eqRefl _))

private def imageFromWitness (encode : Term Const Γ (source ⇒ target)) (stored : Term Const Γ target)
    (field : Term Const Γ source) (same : ProofSyntax Const Δ (.eq (.app encode field) stored)) :
    ProofSyntax Const Δ (.app (image encode) stored) := by
  apply ProofSyntax.impE (.eqPropER (image_apply encode stored))
  apply ProofSyntax.exI field
  apply ProofSyntax.castIndices rfl ?_ same
  simp only [instantiate,subst,Subst.single]
  rw [show subst (Subst.single field) (weaken encode) = encode from instantiate_weaken field encode,
    show subst (Subst.single field) (weaken stored) = stored from instantiate_weaken field stored]

def forget (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (stored : Term Const Γ target) (member : ProofSyntax Const Δ (.app (lift encode predicate) stored)) :
    ProofSyntax Const Δ (.app (image encode) stored) := by
  apply ProofSyntax.exE (.impE (.eqPropEL (application encode predicate stored)) member)
  have recovered : ProofSyntax Const (witness encode predicate stored :: weakenHyps Δ)
      (.app (image (weaken encode)) (weaken stored)) :=
    imageFromWitness (weaken encode) (weaken stored) (.var .vz) (.andER (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_ recovered
  change Term.app (image (weaken encode)) (weaken stored) = Term.app (weaken (image encode)) (weaken stored)
  rw [show weaken (σ := source) (image encode) = image (weaken encode) by
    simpa only [weaken,subst_ofRename] using image_subst (Subst.ofRename (Rename.weaken (σ := source))) encode]

def sourceMember (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (stored : Term Const Γ target)
    (law : ProofSyntax Const Δ (leftInverse encode decode))
    (member : ProofSyntax Const Δ (.app (lift encode predicate) stored)) :
    ProofSyntax Const Δ (.app predicate (.app decode stored)) := by
  apply ProofSyntax.exE (.impE (.eqPropEL (application encode predicate stored)) member)
  let condition := witness encode predicate stored
  have law' : ProofSyntax Const (condition :: weakenHyps (σ := source) Δ)
      (leftInverse (weaken encode) (weaken decode)) :=
    .castIndices rfl (leftInverse_rename Rename.weaken encode decode) ((law.rename Rename.weaken).prepend condition)
  have same : ProofSyntax Const (condition :: weakenHyps (σ := source) Δ)
      (.eq (.app (weaken decode) (weaken stored)) (.var .vz)) :=
    .eqTrans (.eqAppArg (weaken decode) (.eqSymm (.andER (.hyp 0))))
      (leftInverse_at (weaken encode) (weaken decode) (.var .vz) law')
  exact .impE (.eqPropER (.eqAppArg (weaken predicate) same)) (.andEL (.hyp 0))

def recover (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (stored : Term Const Γ target)
    (law : ProofSyntax Const Δ (leftInverse encode decode))
    (member : ProofSyntax Const Δ (.app (lift encode predicate) stored)) :
    ProofSyntax Const Δ (.eq (.app encode (.app decode stored)) stored) :=
  image_recovery encode decode stored law (forget encode predicate stored member)

def atEncoded (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (field : Term Const Γ source)
    (law : ProofSyntax Const Δ (leftInverse encode decode)) :
    ProofSyntax Const Δ (.eq (.app (lift encode predicate) (.app encode field)) (.app predicate field)) := by
  apply ProofSyntax.eqPropI
  · apply ProofSyntax.impI
    have decoded := sourceMember encode decode predicate (.app encode field) (law.prepend _) (.hyp 0)
    exact .impE (.eqPropEL (.eqAppArg predicate (leftInverse_at encode decode field (law.prepend _)))) decoded
  · exact .impI (introduce encode predicate field (.hyp 0))

def retraction (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (law : ProofSyntax Const Δ (leftInverse encode decode)) :
    ProofSyntax Const Δ (GuardedRetraction.law decode encode (lift encode predicate)) := by
  apply ProofSyntax.allI (σ := target)
  apply ProofSyntax.impI
  have law' : ProofSyntax Const
      (.app (weaken (lift encode predicate)) (.var .vz) :: weakenHyps (σ := target) Δ)
      (leftInverse (weaken encode) (weaken decode)) :=
    .castIndices rfl (leftInverse_rename Rename.weaken encode decode) ((law.rename Rename.weaken).prepend _)
  have member : ProofSyntax Const
      (.app (weaken (lift encode predicate)) (.var .vz) :: weakenHyps (σ := target) Δ)
      (.app (lift (weaken encode) (weaken predicate)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp 0)
    exact congrArg (fun guard => Term.app guard (.var .vz)) (lift_weaken encode predicate)
  exact recover (weaken encode) (weaken decode) (weaken predicate) (.var .vz) law' member

theorem application_free (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (stored : Term Const Γ target) : (application (Δ := Δ) encode predicate stored).FunctionExtensionalityFree := by
  simp only [application,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]

theorem introduce_free (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (field : Term Const Γ source) (member : ProofSyntax Const Δ (.app predicate field))
    (free : member.FunctionExtensionalityFree) : (introduce encode predicate field member).FunctionExtensionalityFree := by
  simp only [introduce,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨application_free _ _ _,free,True.intro⟩

private theorem imageFromWitness_free (encode : Term Const Γ (source ⇒ target)) (stored : Term Const Γ target)
    (field : Term Const Γ source) (same : ProofSyntax Const Δ (.eq (.app encode field) stored))
    (free : same.FunctionExtensionalityFree) :
    (imageFromWitness encode stored field same).FunctionExtensionalityFree := by
  simp only [imageFromWitness,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨image_apply_free _ _,free⟩

theorem forget_free (encode : Term Const Γ (source ⇒ target)) (predicate : Term Const Γ (source ⇒ .prop))
    (stored : Term Const Γ target) (member : ProofSyntax Const Δ (.app (lift encode predicate) stored))
    (free : member.FunctionExtensionalityFree) : (forget encode predicate stored member).FunctionExtensionalityFree := by
  unfold forget
  constructor
  · exact ⟨application_free _ _ _,free⟩
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact imageFromWitness_free _ _ _ _ True.intro

theorem sourceMember_free (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (stored : Term Const Γ target)
    (law : ProofSyntax Const Δ (leftInverse encode decode))
    (member : ProofSyntax Const Δ (.app (lift encode predicate) stored))
    (lawFree : law.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (sourceMember encode decode predicate stored law member).FunctionExtensionalityFree := by
  simp only [sourceMember,application,leftInverse_at,ProofSyntax.FunctionExtensionalityFree,
    ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
    ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename,
    true_and,and_true]
  exact ⟨memberFree,lawFree⟩

theorem recover_free (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (stored : Term Const Γ target)
    (law : ProofSyntax Const Δ (leftInverse encode decode))
    (member : ProofSyntax Const Δ (.app (lift encode predicate) stored))
    (lawFree : law.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (recover encode decode predicate stored law member).FunctionExtensionalityFree :=
  image_recovery_free _ _ _ _ _ lawFree (forget_free _ _ _ _ memberFree)

theorem atEncoded_free (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (field : Term Const Γ source)
    (law : ProofSyntax Const Δ (leftInverse encode decode)) (free : law.FunctionExtensionalityFree) :
    (atEncoded encode decode predicate field law).FunctionExtensionalityFree := by
  unfold atEncoded
  constructor
  · constructor
    · apply leftInverse_at_free
      simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using free
    · apply sourceMember_free
      · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using free
      · trivial
  · exact introduce_free _ _ _ _ True.intro

theorem retraction_free (encode : Term Const Γ (source ⇒ target)) (decode : Term Const Γ (target ⇒ source))
    (predicate : Term Const Γ (source ⇒ .prop)) (law : ProofSyntax Const Δ (leftInverse encode decode))
    (free : law.FunctionExtensionalityFree) : (retraction encode decode predicate law).FunctionExtensionalityFree := by
  unfold retraction
  apply recover_free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_rename] using free
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

#print axioms introduce
#print axioms forget
#print axioms sourceMember
#print axioms atEncoded
#print axioms retraction
#print axioms atEncoded_free
#print axioms retraction_free
end Mettapedia.Logic.HOL.ConstructorPredicateRepresentation
