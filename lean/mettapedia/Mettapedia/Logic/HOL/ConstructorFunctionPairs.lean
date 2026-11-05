import Mettapedia.Logic.HOL.ConstructorProjections
import Mettapedia.Logic.HOL.VectorChildArraySuffix
import Mettapedia.Logic.HOL.PredicateSigmaProjection
import Mettapedia.Logic.HOL.CurriedGuardProgramProofs
import Mettapedia.Logic.HOL.Syntax.SubstitutionExtension

/-!
# Pairs stored in two constructor-child positions

A pair stores its two values in an actual function array. The selected third
constructor projection recovers that array; positions zero and successor zero
recover the two values. Constructor field uniqueness, function selection and
the element recursion law are explicit retained premises.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorFunctionPairs

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

structure Inputs (ops : VectorChildArrays.Operations Const) (payloadType : Ty Base) where
  raw : ClosedTerm Const (ConstructorProjections.Constructor ops.number payloadType ops.ArrayType ops.element)
  tag : ClosedTerm Const ops.number
  payload : ClosedTerm Const payloadType
  bottom : ClosedTerm Const ops.element

namespace Inputs
variable {ops : VectorChildArrays.Operations Const} {payloadType : Ty Base}
  (given : Inputs ops payloadType) {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

def children (first second : Term Const Γ ops.element) : Term Const Γ ops.ArrayType :=
  ops.prepend first (ops.prepend second (ops.padding (weakenCtx Γ given.bottom)))

theorem children_subst (images : Subst Const Γ Ξ) (first second : Term Const Γ ops.element) :
    subst images (given.children first second) = given.children (subst images first) (subst images second) := by
  simp only [children,VectorChildArrays.Operations.prepend_subst,VectorChildArrays.Operations.padding_subst,subst_weakenCtx]

def value (first second : Term Const Γ ops.element) : Term Const Γ ops.element :=
  ConstructorProjections.apply (weakenCtx Γ given.raw) (weakenCtx Γ given.tag)
    (weakenCtx Γ given.payload) (given.children first second)

theorem value_subst (images : Subst Const Γ Ξ) (first second : Term Const Γ ops.element) :
    subst images (given.value first second) = given.value (subst images first) (subst images second) := by
  simp only [value,ConstructorProjections.subst_apply,subst_weakenCtx,children_subst]

def program : Term Const Γ (ops.element ⇒ ops.element ⇒ ops.element) :=
  .lam (.lam (given.value (.var (.vs .vz)) (.var .vz)))

theorem program_subst (images : Subst Const Γ Ξ) : subst images given.program = given.program := by
  simp only [program,HOL.subst,value_subst,Subst.lift]
  rfl

theorem program_weaken : weakenCtx Γ (given.program (Γ := [])) = given.program (Γ := Γ) := by
  induction Γ with
  | nil => rfl
  | cons type rest previous =>
      rw [weakenCtx_cons,previous]
      simpa only [subst_ofRename,weaken] using given.program_subst (Subst.ofRename (Rename.weaken (σ := type)))

def branchProjection : ClosedTerm Const (ops.element ⇒ ops.ArrayType) :=
  ConstructorProjections.thirdProjection ops.elementSelection given.raw

def projectionProgram (slot : ClosedTerm Const ops.number) : Term Const Γ (ops.element ⇒ ops.element) :=
  .lam (.app (.app (weakenCtx (ops.element :: Γ) given.branchProjection) (.var .vz))
    (weakenCtx (ops.element :: Γ) slot))

theorem projectionProgram_subst (slot : ClosedTerm Const ops.number) (images : Subst Const Γ Ξ) :
    subst images (given.projectionProgram slot) = given.projectionProgram slot := by
  simp only [projectionProgram,HOL.subst,subst_weakenCtx,Subst.lift]

theorem projectionProgram_weaken (slot : ClosedTerm Const ops.number) :
    weakenCtx Γ (given.projectionProgram (Γ := []) slot) = given.projectionProgram (Γ := Γ) slot := by
  induction Γ with
  | nil => rfl
  | cons type rest previous =>
      rw [weakenCtx_cons,previous]
      simpa only [subst_ofRename,weaken] using given.projectionProgram_subst slot
        (Subst.ofRename (Rename.weaken (σ := type)))

def operations : PredicateSigma.Operations Const ops.element where
  pair := given.program
  first := given.projectionProgram ops.zero
  second := given.projectionProgram (.app ops.successor ops.zero)

@[irreducible] def pair_apply (first second : Term Const Γ ops.element) :
    ProofSyntax Const Δ (.eq (PredicateSigma.pair given.operations first second) (given.value first second)) := by
  apply ProofSyntax.castIndices rfl ?_
    (CurriedGuardProgramProofs.beta2 (given.value (.var (.vs .vz)) (.var .vz)) first second)
  rw [PredicateSigma.pair,operations,given.program_weaken]
  apply congrArg (Term.eq _)
  rw [instantiate_subst_lift,value_subst]
  rfl

theorem pair_apply_free (first second : Term Const Γ ops.element) :
    (given.pair_apply (Δ := Δ) first second).FunctionExtensionalityFree := by
  unfold pair_apply
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    (CurriedGuardProgramProofs.beta2_free _ _ _)

@[irreducible] def projection_apply (slot : ClosedTerm Const ops.number) (point : Term Const Γ ops.element) :
    ProofSyntax Const Δ (.eq (.app (weakenCtx Γ (given.projectionProgram (Γ := []) slot)) point)
      (.app (.app (weakenCtx Γ given.branchProjection) point) (weakenCtx Γ slot))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta point
    (.app (.app (weakenCtx (ops.element :: Γ) given.branchProjection) (.var .vz))
      (weakenCtx (ops.element :: Γ) slot)))
  rw [given.projectionProgram_weaken slot]
  simp only [projectionProgram,instantiate,HOL.subst,subst_weakenCtx,Subst.single]

theorem projection_apply_free (slot : ClosedTerm Const ops.number) (point : Term Const Γ ops.element) :
    (given.projection_apply (Δ := Δ) slot point).FunctionExtensionalityFree := by
  unfold projection_apply
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

structure Premises (assumptions : List (Formula Const Γ)) where
  choice : ProofSyntax Const assumptions
    (VectorChildArrays.Operations.selectionLaw ops.ArrayType ops.elementSelection)
  recursion : ProofSyntax Const assumptions (ops.recursionLaw ops.element)
  injectivity : ProofSyntax Const assumptions (ConstructorProjections.fieldInjective (weakenCtx Γ given.raw))

namespace Premises
variable {given}

def Free (premises : given.Premises Δ) : Prop :=
  premises.choice.FunctionExtensionalityFree ∧ premises.recursion.FunctionExtensionalityFree ∧
    premises.injectivity.FunctionExtensionalityFree

def rename (premises : given.Premises Δ) (rho : Rename Base Γ Ξ) :
    given.Premises (Δ.map (HOL.rename rho)) where
  choice := .castIndices rfl (by simpa only [subst_ofRename] using
    (VectorChildArrays.Operations.selectionLaw_subst (Subst.ofRename rho) ops.ArrayType ops.elementSelection))
    (premises.choice.rename rho)
  recursion := .castIndices rfl
    (by simpa only [subst_ofRename] using (ops.recursionLaw_subst (Subst.ofRename rho) ops.element))
    (premises.recursion.rename rho)
  injectivity := .castIndices rfl (by simp only [ConstructorProjections.rename_fieldInjective,rename_weakenCtx])
    (premises.injectivity.rename rho)

def weaken (premises : given.Premises Δ) (type : Ty Base) :
    given.Premises (weakenHyps (σ := type) Δ) := premises.rename Rename.weaken

theorem rename_free (premises : given.Premises Δ) (rho : Rename Base Γ Ξ) (free : premises.Free) :
    (premises.rename rho).Free := by
  simpa only [Free,rename,ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

theorem weaken_free (premises : given.Premises Δ) (type : Ty Base) (free : premises.Free) :
    (premises.weaken type).Free := premises.rename_free Rename.weaken free

end Premises

private theorem closed_app {first second : Ty Base} (function : ClosedTerm Const (first ⇒ second))
    (argument : ClosedTerm Const first) :
    weakenCtx Γ (.app function argument) = .app (weakenCtx Γ function) (weakenCtx Γ argument) := by
  induction Γ with
  | nil => rfl
  | cons type rest previous =>
      change weaken (weakenCtx rest (.app function argument)) =
        .app (weaken (weakenCtx rest function)) (weaken (weakenCtx rest argument))
      rw [previous]
      rfl

private theorem branchProjection_weaken : weakenCtx Γ given.branchProjection =
    ConstructorProjections.thirdProjection (weakenCtx Γ ops.elementSelection) (weakenCtx Γ given.raw) := by
  induction Γ with
  | nil => rfl
  | cons type rest previous =>
      change weaken (weakenCtx rest given.branchProjection) =
        ConstructorProjections.thirdProjection (weaken (weakenCtx rest ops.elementSelection))
          (weaken (weakenCtx rest given.raw))
      rw [previous]
      exact ConstructorProjections.rename_thirdProjection Rename.weaken _ _

private def recoveredChildren (first second : Term Const Γ ops.element) (premises : given.Premises Δ) :
    ProofSyntax Const Δ (.eq (.app (weakenCtx Γ given.branchProjection) (given.value first second))
      (given.children first second)) := by
  apply ProofSyntax.castIndices rfl ?_ (ConstructorProjections.third_at
    (weakenCtx Γ ops.elementSelection) (weakenCtx Γ given.raw)
    (weakenCtx Γ given.tag) (weakenCtx Γ given.payload) (given.children first second)
    premises.choice premises.injectivity)
  exact congrArg (fun projection => Term.eq (.app projection (given.value first second)) (given.children first second))
    given.branchProjection_weaken.symm

private theorem recoveredChildren_free (first second : Term Const Γ ops.element) (premises : given.Premises Δ)
    (free : premises.Free) : (given.recoveredChildren first second premises).FunctionExtensionalityFree := by
  unfold recoveredChildren
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    (ConstructorProjections.third_at_free _ _ _ _ _ _ _ free.1 free.2.2)

@[irreducible] def first_at (first second : Term Const Γ ops.element) (premises : given.Premises Δ) :
    ProofSyntax Const Δ (.eq (PredicateSigma.first given.operations (PredicateSigma.pair given.operations first second)) first) :=
  .eqTrans (given.projection_apply ops.zero _)
    (.eqTrans (.eqApp (weakenCtx Γ ops.zero) (.eqAppArg (weakenCtx Γ given.branchProjection) (given.pair_apply first second)))
      (.eqTrans (.eqApp (weakenCtx Γ ops.zero) (given.recoveredChildren first second premises))
        (ops.prepend_zero first (ops.prepend second (ops.padding (weakenCtx Γ given.bottom))) premises.choice premises.recursion)))

@[irreducible] def second_at (first second : Term Const Γ ops.element) (premises : given.Premises Δ) :
    ProofSyntax Const Δ (.eq (PredicateSigma.second given.operations (PredicateSigma.pair given.operations first second)) second) := by
  have shifted : ProofSyntax Const Δ (.eq (.app (given.children first second) (weakenCtx Γ (.app ops.successor ops.zero)))
      (.app (ops.prepend second (ops.padding (weakenCtx Γ given.bottom))) (weakenCtx Γ ops.zero))) := by
    apply ProofSyntax.castIndices rfl ?_
      (ops.prepend_successor first (ops.prepend second (ops.padding (weakenCtx Γ given.bottom)))
        (weakenCtx Γ ops.zero) premises.choice premises.recursion)
    rw [closed_app]
    rfl
  exact .eqTrans (given.projection_apply (.app ops.successor ops.zero) _)
    (.eqTrans (.eqApp (weakenCtx Γ (.app ops.successor ops.zero))
      (.eqAppArg (weakenCtx Γ given.branchProjection) (given.pair_apply first second)))
      (.eqTrans (.eqApp (weakenCtx Γ (.app ops.successor ops.zero)) (given.recoveredChildren first second premises))
        (.eqTrans shifted (ops.prepend_zero second (ops.padding (weakenCtx Γ given.bottom)) premises.choice premises.recursion))))

theorem first_at_free (first second : Term Const Γ ops.element) (premises : given.Premises Δ) (free : premises.Free) :
    (given.first_at first second premises).FunctionExtensionalityFree := by
  unfold first_at
  exact ⟨given.projection_apply_free _ _,⟨given.pair_apply_free _ _,⟨given.recoveredChildren_free _ _ _ free,
    ops.prepend_zero_free _ _ _ _ free.1 free.2.1⟩⟩⟩

theorem second_at_free (first second : Term Const Γ ops.element) (premises : given.Premises Δ) (free : premises.Free) :
    (given.second_at first second premises).FunctionExtensionalityFree := by
  unfold second_at
  exact ⟨given.projection_apply_free _ _,⟨given.pair_apply_free _ _,⟨given.recoveredChildren_free _ _ _ free,
    ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      (ops.prepend_successor_free _ _ _ _ _ free.1 free.2.1),
      ops.prepend_zero_free _ _ _ _ free.1 free.2.1⟩⟩⟩⟩

@[irreducible] def first_law (premises : given.Premises Δ) :
    ProofSyntax Const Δ (weakenCtx Γ (PredicateSigma.firstLaw given.operations)) :=
  .castIndices rfl (PredicateSigma.firstLaw_form given.operations).symm
    (.allI (.allI (given.first_at (.var (.vs .vz)) (.var .vz)
      ((premises.weaken ops.element).weaken ops.element))))

@[irreducible] def second_law (premises : given.Premises Δ) :
    ProofSyntax Const Δ (weakenCtx Γ (PredicateSigma.secondLaw given.operations)) :=
  .castIndices rfl (PredicateSigma.secondLaw_form given.operations).symm
    (.allI (.allI (given.second_at (.var (.vs .vz)) (.var .vz)
      ((premises.weaken ops.element).weaken ops.element))))

theorem first_law_free (premises : given.Premises Δ) (free : premises.Free) :
    (given.first_law premises).FunctionExtensionalityFree := by
  unfold first_law
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    (given.first_at_free _ _ _ ((premises.weaken ops.element).weaken_free ops.element
      (premises.weaken_free ops.element free)))

theorem second_law_free (premises : given.Premises Δ) (free : premises.Free) :
    (given.second_law premises).FunctionExtensionalityFree := by
  unfold second_law
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    (given.second_at_free _ _ _ ((premises.weaken ops.element).weaken_free ops.element
      (premises.weaken_free ops.element free)))

#print axioms first_at
#print axioms second_at
#print axioms first_law_free
#print axioms second_law_free

end Inputs
end Mettapedia.Logic.HOL.ConstructorFunctionPairs
