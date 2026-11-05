import Mettapedia.Logic.HOL.VectorTabulationPrograms
import Mettapedia.Logic.HOL.SuccessorOrderPositionBounds
import Mettapedia.Logic.HOL.SuccessorOrderSubstitution

/-!
# Bounded element guards for the actual shifted-array tabulator

The induction invariant quantifies every input array at each length. Shifting
an array transports its bounded guard by the actual successor-order map.
Selection, recursion at `(number ⇒ element) ⇒ vector`, and natural induction
remain separate retained premises. Neither a supplied vector nor a full
element predicate is used to establish the vector guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorTabulation.Shifted
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
  (signature : IndexedVectorPredicate.Signature Const) {Γ Ξ : Ctx Base}

def bounded (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature)) : Formula Const Γ :=
  .all (.imp (.app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) (.var .vz)) (weaken length))
    (.app (weaken predicate) (.app (weaken array) (.var .vz))))

@[simp] theorem bounded_subst (images : Subst Const Γ Ξ)
    (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature)) :
    HOL.subst images (bounded signature predicate length array) =
      bounded signature (HOL.subst images predicate) (HOL.subst images length) (HOL.subst images array) := by
  simp only [bounded, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]

theorem bounded_rename (rho : Rename Base Γ Ξ)
    (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature)) :
    HOL.rename rho (bounded signature predicate length array) =
      bounded signature (HOL.rename rho predicate) (HOL.rename rho length) (HOL.rename rho array) := by
  simpa only [subst_ofRename] using bounded_subst signature (Subst.ofRename rho) predicate length array

def property (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) : Formula Const Γ :=
  .all (.imp (bounded signature (weaken predicate) (weaken length) (.var .vz))
    (signature.member (weaken predicate) (weaken length) (.app (weaken function) (.var .vz))))

@[simp] theorem property_subst (images : Subst Const Γ Ξ)
    (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    HOL.subst images (property signature predicate length function) =
      property signature (HOL.subst images predicate) (HOL.subst images length) (HOL.subst images function) := by
  simp only [property, HOL.subst, bounded_subst, signature.subst_member, subst_weaken, Subst.lift]

theorem property_rename (rho : Rename Base Γ Ξ)
    (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    HOL.rename rho (property signature predicate length function) =
      property signature (HOL.rename rho predicate) (HOL.rename rho length) (HOL.rename rho function) := by
  simpa only [subst_ofRename] using property_subst signature (Subst.ofRename rho) predicate length function

def family (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    Term Const Γ (signature.number ⇒ Result signature ⇒ .prop) :=
  .lam (.lam (property signature (weaken (weaken predicate)) (.var (.vs .vz)) (.var .vz)))

@[simp] theorem family_subst (images : Subst Const Γ Ξ)
    (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    HOL.subst images (family signature predicate) = family signature (HOL.subst images predicate) := by
  simp only [family, HOL.subst, property_subst, subst_weaken, Subst.lift]
  rfl

variable {Δ : List (Formula Const Γ)}

theorem shift_rename (rho : Rename Base Γ Ξ) (array : Term Const Γ (Array signature)) :
    HOL.rename rho (shift signature array) = shift signature (HOL.rename rho array) := by
  simpa only [subst_ofRename] using shift_subst signature (Subst.ofRename rho) array

theorem start_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (start (Γ := Γ) signature) = start (Γ := Ξ) signature := by
  simpa only [subst_ofRename] using start_subst signature (Subst.ofRename rho)

theorem method_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (method (Γ := Γ) signature) = method (Γ := Ξ) signature := by
  simpa only [subst_ofRename] using method_subst signature (Subst.ofRename rho)

theorem family_rename (rho : Rename Base Γ Ξ)
    (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    HOL.rename rho (family signature predicate) = family signature (HOL.rename rho predicate) := by
  simpa only [subst_ofRename] using family_subst signature (Subst.ofRename rho) predicate

theorem induction_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)) =
    NaturalRecursionProofs.inductionPrinciple (weakenCtx Ξ signature.zero) (weakenCtx Ξ signature.successor) := by
  simpa only [subst_ofRename] using SuccessorOrder.inductionPrinciple_subst signature.successor signature.zero
    (Subst.ofRename rho)

def boundedAt (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (position : Term Const Γ signature.number)
    (present : ProofSyntax Const Δ (bounded signature predicate length array)) :
    ProofSyntax Const Δ (.imp (.app (.app (weakenCtx Γ (SuccessorOrder.less signature.successor)) position) length)
      (.app predicate (.app array position))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE position present)
  simp only [instantiate, HOL.subst, subst_weakenCtx,
    PredicateFixedPoint.subst_single_weaken, Subst.single]

def propertyAt (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (present : ProofSyntax Const Δ (property signature predicate length function)) :
    ProofSyntax Const Δ (.imp (bounded signature predicate length array)
      (signature.member predicate length (.app function array))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE array present)
  simp only [instantiate, bounded_subst, signature.subst_member, HOL.subst,
    PredicateFixedPoint.subst_single_weaken, Subst.single]

def family_apply (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    ProofSyntax Const Δ (.eq (NaturalRecursionProofs.holds (family signature predicate) length function)
      (property signature predicate length function)) := by
  apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2
    (property signature (weaken (weaken predicate)) (.var (.vs .vz)) (.var .vz)) length function)
  simp [family, NaturalRecursionProofs.holds, instantiate, property_subst, HOL.subst,
    Subst.single, Subst.lift, weaken, HOL.subst_rename, HOL.subst_comp, Rename.weaken]
  simp only [ProofSyntax.term_subst_of_identity (fun _ => rfl)]
  apply congrArg (fun value : Term Const Γ (signature.element ⇒ .prop) => property signature value length function)
  exact ProofSyntax.term_subst_of_identity (fun _ => rfl) predicate

def boundedHead (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (present : ProofSyntax Const Δ (bounded signature predicate (.app (weakenCtx Γ signature.successor) length) array)) :
    ProofSyntax Const Δ (.app predicate (.app array (weakenCtx Γ signature.zero))) :=
  .impE (boundedAt signature predicate (.app (weakenCtx Γ signature.successor) length) array _ present)
    (SuccessorOrder.zeroLessSuccessor signature.successor signature.zero length induction)

def boundedShift (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (present : ProofSyntax Const Δ (bounded signature predicate (.app (weakenCtx Γ signature.successor) length) array)) :
    ProofSyntax Const Δ (bounded signature predicate length (shift signature array)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let bound : Formula Const (signature.number :: Γ) :=
    .app (.app (weakenCtx _ (SuccessorOrder.less signature.successor)) (.var .vz)) (weaken length)
  have current : ProofSyntax Const (bound :: weakenHyps Δ)
      (bounded signature (weaken predicate) (.app (weakenCtx _ signature.successor) (weaken length)) (weaken array)) := by
    apply ProofSyntax.castIndices rfl ?_ ((present.rename Rename.weaken).prepend bound)
    simp only [bounded_rename, HOL.rename, rename_weakenCtx]
    rfl
  have original := ProofSyntax.impE (boundedAt signature (weaken predicate) _ (weaken array)
    (.app (weakenCtx _ signature.successor) (.var .vz)) current)
    (SuccessorOrder.lessSuccessorMap signature.successor (.var .vz) (weaken length) (.hyp (Δ := bound :: weakenHyps Δ) 0))
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (.eqAppArg (weaken predicate) (shift_apply signature (weaken array) (.var .vz)))) original)
  simp only [weaken, shift_rename]

def member_equal (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (first second : Term Const Γ signature.vector)
    (equal : ProofSyntax Const Δ (.eq first second)) :
    ProofSyntax Const Δ (.eq (signature.member predicate length first) (signature.member predicate length second)) := by
  apply ProofSyntax.eqAppArg (signature.least predicate)
  change ProofSyntax Const Δ (.eq
    (.lam (.app (.app (.var .vz) (weaken length)) (weaken first)))
    (.lam (.app (.app (.var .vz) (weaken length)) (weaken second))))
  exact .eqLam (.eqAppArg (.app (.var .vz) (weaken length)) (equal.rename Rename.weaken))

def property_start (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    ProofSyntax Const Δ (property signature predicate (weakenCtx Γ signature.zero) (start signature)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let bound := bounded signature (weaken predicate) (weaken (weakenCtx Γ signature.zero)) (.var .vz)
  have nilProof : ProofSyntax Const (bound :: weakenHyps Δ)
      (signature.member (weaken predicate) (weakenCtx _ signature.zero) (weakenCtx _ signature.nil)) :=
    signature.nil_member _
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (member_equal signature (weaken predicate) (weakenCtx _ signature.zero)
      (.app (start signature) (.var .vz)) (weakenCtx _ signature.nil) (start_apply signature (.var .vz)))) nilProof)
  simp only [weaken, rename_weakenCtx, start_rename]

def property_next (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (prior : ProofSyntax Const Δ (property signature predicate length previous)) :
    ProofSyntax Const Δ (property signature predicate (.app (weakenCtx Γ signature.successor) length)
      (.app (.app (method signature) previous) length)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let bound := bounded signature (weaken predicate)
    (weaken (.app (weakenCtx Γ signature.successor) length)) (.var .vz)
  have present : ProofSyntax Const (bound :: weakenHyps Δ)
      (bounded signature (weaken predicate) (.app (weakenCtx _ signature.successor) (weaken length)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := bound :: weakenHyps Δ) 0)
    change bound = _
    simp only [bound,weaken,HOL.rename,rename_weakenCtx]
  have principle : ProofSyntax Const (bound :: weakenHyps Δ)
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx _ signature.zero) (weakenCtx _ signature.successor)) := by
    apply ProofSyntax.castIndices rfl ?_ ((induction.rename Rename.weaken).prepend bound)
    simpa only [subst_ofRename] using SuccessorOrder.inductionPrinciple_subst signature.successor signature.zero
      (Subst.ofRename (Rename.weaken (Γ := Γ) (σ := Array signature)))
  have inherited : ProofSyntax Const (bound :: weakenHyps Δ)
      (property signature (weaken predicate) (weaken length) (weaken previous)) :=
    .castIndices rfl (property_rename signature Rename.weaken predicate length previous)
      ((prior.rename Rename.weaken).prepend bound)
  have tailProof := ProofSyntax.impE
    (propertyAt signature (weaken predicate) (weaken length) (weaken previous)
      (shift signature (.var .vz)) inherited)
    (boundedShift signature (weaken predicate) (weaken length) (.var .vz) present)
  have consProof := signature.cons_member (weaken predicate) (weaken length)
    (.app (.var .vz) (weakenCtx _ signature.zero))
    (.app (weaken previous) (shift signature (.var .vz)))
    (boundedHead signature (weaken predicate) (weaken length) (.var .vz) principle present) tailProof
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (member_equal signature (weaken predicate)
      (.app (weakenCtx _ signature.successor) (weaken length))
      (.app (.app (.app (method signature) (weaken previous)) (weaken length)) (.var .vz)) _
      (method_apply signature (weaken previous) (weaken length) (.var .vz)))) consProof)
  simp only [weaken,HOL.rename,rename_weakenCtx,method_rename]

def base (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    ProofSyntax Const Δ (NaturalRecursionProofs.holds (family signature predicate)
      (weakenCtx Γ signature.zero) (start signature)) :=
  .impE (.eqPropER (family_apply signature predicate _ _)) (property_start signature predicate)

def step (predicate : Term Const Γ (signature.element ⇒ .prop))
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor))) :
    ProofSyntax Const Δ (NaturalRecursionProofs.methodPreserves
      (weakenCtx Γ signature.successor) (method signature) (family signature predicate)) := by
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let hypothesis := NaturalRecursionProofs.holds (weaken (weaken (family signature predicate)))
    (.var (.vs .vz)) (.var .vz)
  let pred : Term Const (Result signature :: signature.number :: Γ) (signature.element ⇒ .prop) :=
    weaken (weaken predicate)
  have prior : ProofSyntax Const (hypothesis :: weakenHyps (σ := Result signature) (weakenHyps Δ))
      (property signature pred (.var (.vs .vz)) (.var .vz)) := by
    apply ProofSyntax.impE (.eqPropEL (family_apply signature pred (.var (.vs .vz)) (.var .vz)))
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := hypothesis :: weakenHyps (σ := Result signature) (weakenHyps Δ)) 0)
    change hypothesis = _
    simp only [hypothesis,pred,weaken,family_rename]
  have principle : ProofSyntax Const (hypothesis :: weakenHyps (σ := Result signature) (weakenHyps Δ))
      (NaturalRecursionProofs.inductionPrinciple (weakenCtx _ signature.zero) (weakenCtx _ signature.successor)) := by
    apply ProofSyntax.castIndices rfl ?_
      (((induction.rename Rename.weaken).rename Rename.weaken).prepend hypothesis)
    simp only [induction_rename]
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (family_apply signature pred
      (.app (weakenCtx _ signature.successor) (.var (.vs .vz)))
      (.app (.app (method signature) (.var .vz)) (.var (.vs .vz)))))
      (property_next signature pred (.var (.vs .vz)) (.var .vz) principle prior))
  simp only [pred,NaturalRecursionProofs.holds,weaken,family_rename,method_rename,rename_weakenCtx]

def member (selection : ClosedTerm Const (Selection signature))
    (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (Result signature)))
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (elements : ProofSyntax Const Δ (bounded signature predicate length array)) :
    ProofSyntax Const Δ (signature.member predicate length (tabulate signature selection length array)) := by
  have every := NaturalRecursionProofs.dependent (weakenCtx Γ selection) (weakenCtx Γ signature.zero)
    (weakenCtx Γ signature.successor) (start signature) (method signature) (family signature predicate)
    choice recursion induction (base signature predicate) (step signature predicate induction)
  have atLength : ProofSyntax Const Δ (NaturalRecursionProofs.holds (family signature predicate) length
      (.app (recursor signature selection) length)) := by
    apply ProofSyntax.castIndices rfl ?_ (.allE length every)
    simp only [NaturalRecursionProofs.holds,instantiate,HOL.subst,
      PredicateFixedPoint.subst_single_weaken,Subst.single]
    rfl
  exact .impE (propertyAt signature predicate length (.app (recursor signature selection) length) array
    (.impE (.eqPropEL (family_apply signature predicate _ _)) atLength)) elements

theorem boundedAt_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (position : Term Const Γ signature.number)
    (present : ProofSyntax Const Δ (bounded signature predicate length array)) (free : present.FunctionExtensionalityFree) :
    (boundedAt signature predicate length array position present).FunctionExtensionalityFree := by
  unfold boundedAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

theorem propertyAt_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature))
    (array : Term Const Γ (Array signature)) (present : ProofSyntax Const Δ (property signature predicate length function))
    (free : present.FunctionExtensionalityFree) :
    (propertyAt signature predicate length function array present).FunctionExtensionalityFree := by
  unfold propertyAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free

theorem family_apply_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (function : Term Const Γ (Result signature)) :
    (family_apply (Δ := Δ) signature predicate length function).FunctionExtensionalityFree := by
  unfold family_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

theorem boundedHead_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (present : ProofSyntax Const Δ (bounded signature predicate (.app (weakenCtx Γ signature.successor) length) array))
    (inductionFree : induction.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (boundedHead signature predicate length array induction present).FunctionExtensionalityFree :=
  ⟨boundedAt_free _ _ _ _ _ _ presentFree,
    SuccessorOrder.zeroLessSuccessor_free _ _ _ induction inductionFree⟩

theorem boundedShift_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (present : ProofSyntax Const Δ (bounded signature predicate (.app (weakenCtx Γ signature.successor) length) array))
    (presentFree : present.FunctionExtensionalityFree) :
    (boundedShift signature predicate length array present).FunctionExtensionalityFree := by
  simp only [boundedShift,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree,
    shift_apply_free,true_and]
  exact ⟨boundedAt_free _ _ _ _ _ _ (by simpa only [ProofSyntax.prepend,
    ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.functionExtensionalityFree_mono,
    ProofSyntax.functionExtensionalityFree_rename] using presentFree),
    SuccessorOrder.lessSuccessorMap_free _ _ _ _ True.intro⟩

theorem member_equal_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (first second : Term Const Γ signature.vector)
    (equal : ProofSyntax Const Δ (.eq first second)) (free : equal.FunctionExtensionalityFree) :
    (member_equal signature predicate length first second equal).FunctionExtensionalityFree := by
  unfold member_equal
  simpa only [id_eq,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_rename] using free

theorem property_start_free (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    (property_start (Δ := Δ) signature predicate).FunctionExtensionalityFree := by
  simp only [property_start,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  exact ⟨member_equal_free _ _ _ _ _ _ (start_apply_free _ _),signature.nil_member_free _⟩

theorem property_next_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (previous : Term Const Γ (Result signature))
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (prior : ProofSyntax Const Δ (property signature predicate length previous))
    (inductionFree : induction.FunctionExtensionalityFree) (priorFree : prior.FunctionExtensionalityFree) :
    (property_next signature predicate length previous induction prior).FunctionExtensionalityFree := by
  simp only [property_next,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  constructor
  · exact member_equal_free _ _ _ _ _ _ (method_apply_free _ _ _ _)
  · apply signature.cons_member_free
    · exact boundedHead_free _ _ _ _ _ _ (by simpa only [ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_castIndices,
        ProofSyntax.functionExtensionalityFree_rename] using inductionFree) True.intro
    · exact ⟨propertyAt_free _ _ _ _ _ _ (by simpa only [ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_castIndices,
        ProofSyntax.functionExtensionalityFree_rename] using priorFree),
        boundedShift_free _ _ _ _ _ True.intro⟩

theorem base_free (predicate : Term Const Γ (signature.element ⇒ .prop)) :
    (base (Δ := Δ) signature predicate).FunctionExtensionalityFree :=
  ⟨family_apply_free _ _ _ _,property_start_free _ _⟩

theorem step_free (predicate : Term Const Γ (signature.element ⇒ .prop))
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (free : induction.FunctionExtensionalityFree) : (step signature predicate induction).FunctionExtensionalityFree := by
  simp only [step,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  refine ⟨family_apply_free _ _ _ _,property_next_free _ _ _ _ _ _ ?_ ?_⟩
  · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.functionExtensionalityFree_rename] using free
  · exact ⟨family_apply_free _ _ _ _,by simp only [ProofSyntax.functionExtensionalityFree_castIndices,
      ProofSyntax.FunctionExtensionalityFree]⟩

theorem member_free (selection : ClosedTerm Const (Selection signature))
    (predicate : Term Const Γ (signature.element ⇒ .prop))
    (length : Term Const Γ signature.number) (array : Term Const Γ (Array signature))
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) (Result signature)))
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor)))
    (elements : ProofSyntax Const Δ (bounded signature predicate length array))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (inductionFree : induction.FunctionExtensionalityFree) (elementsFree : elements.FunctionExtensionalityFree) :
    (member signature selection predicate length array choice recursion induction elements).FunctionExtensionalityFree := by
  have dependentFree : (NaturalRecursionProofs.dependent (weakenCtx Γ selection) (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) (start signature) (method signature) (family signature predicate)
      choice recursion induction (base signature predicate) (step signature predicate induction)).FunctionExtensionalityFree := by
    unfold NaturalRecursionProofs.dependent
    exact NaturalRecursionProofs.invariant_free _ _ _ _ _ _ induction _ _ _ inductionFree
      (NaturalRecursionProofs.computation_free _ _ _ _ _ _ _ choiceFree recursionFree)
      (base_free _ _) (step_free _ _ _ inductionFree)
  simpa only [member,propertyAt,ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree,family_apply_free,true_and] using And.intro dependentFree elementsFree

#print axioms boundedHead
#print axioms boundedShift
#print axioms member
#print axioms member_free
end Mettapedia.Logic.HOL.VectorTabulation.Shifted
