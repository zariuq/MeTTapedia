import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedBinaryValues

/-!
# Complete unary and binary COMM conclusion values

These comparisons interpret the independently authored communication schema
on supplied complete receiver functions. Ordered arguments and binder-unit
insertions are retained. They are semantic readings of declarations, not
operational evidence or assumptions about syntactic receiver representation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedCommunicationValues

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open BindingClosedPrimitiveOperations BindingClosedStructuralValues BindingClosedBinaryValues

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations AllArity.sig C)
variable {Z : C}

def receiverBody (arity : Nat) :
    Term (AllArity.communicationSignature arity) (AllArity.names arity ++ (AllArity.comm arity).ctx) .pr :=
  AllArity.continuation arity
    (fun index => .var (AllArity.namePosition (AllArity.comm arity).ctx arity index))

private theorem unary_receiver_shape : receiverBody 1 =
    (.op (.inr (MetaOp.mk (M := AllArity.communicationMetas 1) ⟨0, by decide⟩))
      (.cons (.var .zero) .nil) :
        Term (AllArity.communicationSignature 1)
          (AllArity.names 1 ++ (AllArity.comm 1).ctx) .pr) := by
  rfl

private theorem binary_receiver_shape : receiverBody 2 =
    (.op (.inr (MetaOp.mk (M := AllArity.communicationMetas 2) ⟨0, by decide⟩))
      (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)) :
        Term (AllArity.communicationSignature 2)
          (AllArity.names 2 ++ (AllArity.comm 2).ctx) .pr) := by
  rfl

private theorem unary_before_shape : (AllArity.comm 1).lhs =
    (.op (.inl AllArity.Op.par)
      (.cons (.op (.inl (AllArity.Op.out 1))
        (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
        (.cons (.op (.inl (AllArity.Op.inp 1))
          (.cons (.var .zero) (.cons (receiverBody 1) .nil))) .nil)) :
            Term (AllArity.communicationSignature 1) (AllArity.comm 1).ctx .pr) := by
  rfl

private theorem binary_before_shape : (AllArity.comm 2).lhs =
    (.op (.inl AllArity.Op.par)
      (.cons (.op (.inl (AllArity.Op.out 2))
        (.cons (.var .zero) (.cons (.var (.succ .zero))
          (.cons (.var (.succ (.succ .zero))) .nil))))
        (.cons (.op (.inl (AllArity.Op.inp 2))
          (.cons (.var .zero) (.cons (receiverBody 2) .nil))) .nil)) :
            Term (AllArity.communicationSignature 2) (AllArity.comm 2).ctx .pr) := by
  rfl

theorem unary_receiver_curry
    (parameters : Z ⟶ binding.model.family (AllArity.communicationMetas 1))
    (environment : binding.model.Env Z (AllArity.comm 1).ctx) :
    MonoidalClosed.curry
      ((binding.model.interp (AllArity.communicationMetas 1) (receiverBody 1)).value
        (tuple binding 1 ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv (AllArity.names 1) environment)) =
      parameters ≫ fst _ _ := by
  rw [← MonoidalClosed.curry_uncurry (parameters ≫ fst _ _)]
  congr 1
  rw [unary_receiver_shape]
  change lift
      (lift (fst (tuple binding 1) Z ≫ fst (names binding) (𝟙_ C)) (toUnit (tuple binding 1 ⊗ Z)))
      ((snd (tuple binding 1) Z ≫ parameters) ≫ fst _ _) ≫
        (ihom.ev (tuple binding 1)).app (processes binding) =
      MonoidalClosed.uncurry (parameters ≫ fst _ _)
  rw [MonoidalClosed.uncurry_eq]
  apply congrArg (fun paired : tuple binding 1 ⊗ Z ⟶
      tuple binding 1 ⊗ (tuple binding 1 ⟶[C] processes binding) =>
    paired ≫ (ihom.ev (tuple binding 1)).app (processes binding))
  dsimp only [tuple, names, processes, ClosedPresentation.Operations.context,
    ClosedPresentation.Operations.model, ofClosed, AllArity.names, contextOf, familyOf]
  apply hom_ext
  · rw [lift_fst]
    trans fst (tuple binding 1) Z
    · apply hom_ext
      · exact lift_fst _ _
      · exact toUnit_unique _ _
    · exact (whiskerLeft_fst (tuple binding 1) (parameters ≫ fst _ _)).symm
  · rw [lift_snd, Category.assoc]
    have read := (whiskerLeft_snd (tuple binding 1) (parameters ≫ fst _ _)).symm
    dsimp only [tuple, names, processes, ClosedPresentation.Operations.context,
      ClosedPresentation.Operations.model, ofClosed, AllArity.names, contextOf, familyOf] at read
    exact read

theorem binary_receiver_curry
    (parameters : Z ⟶ binding.model.family (AllArity.communicationMetas 2))
    (environment : binding.model.Env Z (AllArity.comm 2).ctx) :
    MonoidalClosed.curry
      ((binding.model.interp (AllArity.communicationMetas 2) (receiverBody 2)).value
        (tuple binding 2 ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv (AllArity.names 2) environment)) =
      parameters ≫ fst _ _ := by
  rw [← MonoidalClosed.curry_uncurry (parameters ≫ fst _ _)]
  congr 1
  rw [binary_receiver_shape]
  change lift
      (lift (fst (tuple binding 2) Z ≫ fst (names binding) (names binding ⊗ 𝟙_ C))
        (lift
          (lift (fst (tuple binding 2) Z ≫ snd (names binding) (names binding ⊗ 𝟙_ C))
            (snd (tuple binding 2) Z) ≫
              (fst (names binding ⊗ 𝟙_ C) Z ≫ fst (names binding) (𝟙_ C)))
          (toUnit (tuple binding 2 ⊗ Z))))
      ((snd (tuple binding 2) Z ≫ parameters) ≫ fst _ _) ≫
        (ihom.ev (tuple binding 2)).app (processes binding) =
      MonoidalClosed.uncurry (parameters ≫ fst _ _)
  rw [MonoidalClosed.uncurry_eq]
  apply congrArg (fun paired : tuple binding 2 ⊗ Z ⟶
      tuple binding 2 ⊗ (tuple binding 2 ⟶[C] processes binding) =>
    paired ≫ (ihom.ev (tuple binding 2)).app (processes binding))
  dsimp only [tuple, names, processes, ClosedPresentation.Operations.context,
    ClosedPresentation.Operations.model, ofClosed, AllArity.names, contextOf, familyOf]
  apply hom_ext
  · rw [lift_fst]
    trans fst (tuple binding 2) Z
    · apply hom_ext
      · exact lift_fst _ _
      · rw [lift_snd]
        apply hom_ext
        · simp only [Category.assoc, lift_fst, lift_fst_assoc]
          rfl
        · exact toUnit_unique _ _
    · exact (whiskerLeft_fst (tuple binding 2) (parameters ≫ fst _ _)).symm
  · rw [lift_snd, Category.assoc]
    have read := (whiskerLeft_snd (tuple binding 2) (parameters ≫ fst _ _)).symm
    dsimp only [tuple, names, processes, ClosedPresentation.Operations.context,
      ClosedPresentation.Operations.model, ofClosed, AllArity.names, contextOf, familyOf] at read
    exact read

theorem unary_after_value
    (parameters : Z ⟶ binding.model.family (AllArity.communicationMetas 1))
    (environment : binding.model.Env Z (AllArity.comm 1).ctx)
    (function : Z ⟶ (names binding ⟶[C] processes binding))
    (receiver_read : parameters ≫ fst _ _ = function ≫ unaryBody binding) :
    (binding.model.interp (AllArity.communicationMetas 1) (AllArity.comm 1).rhs).value
        Z parameters environment =
      lift (environment .nm (.succ .zero)) function ≫
        (ihom.ev (names binding)).app (processes binding) := by
  change lift (lift (environment .nm (.succ .zero)) (toUnit Z)) (parameters ≫ fst _ _) ≫
    (ihom.ev (tuple binding 1)).app (processes binding) = _
  rw [receiver_read]
  exact unary_function_evaluation binding _ function

theorem binary_after_value
    (parameters : Z ⟶ binding.model.family (AllArity.communicationMetas 2))
    (environment : binding.model.Env Z (AllArity.comm 2).ctx)
    (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding))
    (receiver_read : parameters ≫ fst _ _ = function ≫ binaryBody binding) :
    (binding.model.interp (AllArity.communicationMetas 2) (AllArity.comm 2).rhs).value
        Z parameters environment =
      lift (lift (environment .nm (.succ .zero)) (environment .nm (.succ (.succ .zero)))) function ≫
        (ihom.ev (names binding ⊗ names binding)).app (processes binding) := by
  change lift
    (lift (environment .nm (.succ .zero))
      (lift (environment .nm (.succ (.succ .zero))) (toUnit Z))) (parameters ≫ fst _ _) ≫
        (ihom.ev (tuple binding 2)).app (processes binding) = _
  rw [receiver_read]
  exact binary_function_evaluation binding _ _ function

theorem unary_before_value
    (parameters : Z ⟶ binding.model.family (AllArity.communicationMetas 1))
    (environment : binding.model.Env Z (AllArity.comm 1).ctx)
    (function : Z ⟶ (names binding ⟶[C] processes binding))
    (receiver_read : parameters ≫ fst _ _ = function ≫ unaryBody binding) :
    (binding.model.interp (AllArity.communicationMetas 1) (AllArity.comm 1).lhs).value
        Z parameters environment =
      lift (lift (environment .nm .zero) (environment .nm (.succ .zero)) ≫ (continuation binding).output)
        (lift (environment .nm .zero) function ≫ (continuation binding).input) ≫
          (continuation binding).parallel := by
  rw [unary_before_shape]
  erw [parallel_value]
  change lift
      (lift (MonoidalClosed.curry
        ((binding.model.interp (AllArity.communicationMetas 1) (.var .zero)).value
          (𝟙_ C ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment)))
        (lift (MonoidalClosed.curry
          ((binding.model.interp (AllArity.communicationMetas 1) (.var (.succ .zero))).value
            (𝟙_ C ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment))) (toUnit Z)) ≫
          binding.operation (AllArity.Op.out 1))
      (lift (MonoidalClosed.curry
        ((binding.model.interp (AllArity.communicationMetas 1) (.var .zero)).value
          (𝟙_ C ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment)))
        (lift (MonoidalClosed.curry
          ((binding.model.interp (AllArity.communicationMetas 1) (receiverBody 1)).value
            (tuple binding 1 ⊗ Z) (snd _ _ ≫ parameters)
              (binding.model.extendEnv (AllArity.names 1) environment))) (toUnit Z)) ≫
          binding.operation (AllArity.Op.inp 1)) ≫ (continuation binding).parallel = _
  erw [empty_argument binding parameters environment (.var .zero),
    empty_argument binding parameters environment (.var (.succ .zero))]
  rw [Model.interp_var, Model.interp_var]
  rw [unary_receiver_curry, receiver_read]
  apply congrArg (fun paired : Z ⟶ processes binding ⊗ processes binding =>
    paired ≫ (continuation binding).parallel)
  apply hom_ext
  · erw [lift_fst, lift_fst]
    dsimp only [continuation, output, vector]
    dsimp only [tuple, names, ClosedPresentation.Operations.context, AllArity.names, contextOf]
    simp only [comp_lift_assoc, comp_lift, lift_fst_assoc, lift_snd_assoc]
    erw [lift_fst_assoc, lift_snd_assoc, Category.comp_id, comp_toUnit]
  · erw [lift_snd, lift_snd]
    dsimp only [continuation, input]
    dsimp only [tuple, names, ClosedPresentation.Operations.context, AllArity.names, contextOf]
    simp only [comp_lift_assoc, comp_lift, lift_snd, lift_fst_assoc, comp_toUnit]
    erw [lift_fst_assoc, lift_snd_assoc, comp_toUnit]

theorem binary_tuple_packing (first second : Z ⟶ names binding) :
    lift first second ≫ (binaryTuple binding).inv = lift first (lift second (toUnit Z)) := by
  apply (cancel_mono (binaryTuple binding).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, binary_tuple_value]

theorem binary_before_value
    (parameters : Z ⟶ binding.model.family (AllArity.communicationMetas 2))
    (environment : binding.model.Env Z (AllArity.comm 2).ctx)
    (function : Z ⟶ ((names binding ⊗ names binding) ⟶[C] processes binding))
    (receiver_read : parameters ≫ fst _ _ = function ≫ binaryBody binding) :
    (binding.model.interp (AllArity.communicationMetas 2) (AllArity.comm 2).lhs).value
        Z parameters environment =
      lift
        (lift (environment .nm .zero)
          (lift (environment .nm (.succ .zero)) (environment .nm (.succ (.succ .zero)))) ≫
            (continuation binding).send)
        (lift (environment .nm .zero) function ≫ (continuation binding).receive) ≫
          (continuation binding).parallel := by
  dsimp only [Model.Env, ClosedPresentation.Operations.model, ofClosed,
    AllArity.comm, AllArity.names] at environment
  rw [binary_before_shape]
  erw [parallel_value]
  change lift
      (lift (MonoidalClosed.curry
        ((binding.model.interp (AllArity.communicationMetas 2) (.var .zero)).value
          (𝟙_ C ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment)))
        (lift (MonoidalClosed.curry
          ((binding.model.interp (AllArity.communicationMetas 2) (.var (.succ .zero))).value
            (𝟙_ C ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment)))
          (lift (MonoidalClosed.curry
            ((binding.model.interp (AllArity.communicationMetas 2) (.var (.succ (.succ .zero)))).value
              (𝟙_ C ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment)))
            (toUnit Z))) ≫ binding.operation (AllArity.Op.out 2))
      (lift (MonoidalClosed.curry
        ((binding.model.interp (AllArity.communicationMetas 2) (.var .zero)).value
          (𝟙_ C ⊗ Z) (snd _ _ ≫ parameters) (binding.model.extendEnv [] environment)))
        (lift (MonoidalClosed.curry
          ((binding.model.interp (AllArity.communicationMetas 2) (receiverBody 2)).value
            (tuple binding 2 ⊗ Z) (snd _ _ ≫ parameters)
              (binding.model.extendEnv (AllArity.names 2) environment))) (toUnit Z)) ≫
          binding.operation (AllArity.Op.inp 2)) ≫ (continuation binding).parallel = _
  erw [empty_argument binding parameters environment (.var .zero),
    empty_argument binding parameters environment (.var (.succ .zero)),
    empty_argument binding parameters environment (.var (.succ (.succ .zero)))]
  rw [Model.interp_var, Model.interp_var, Model.interp_var, binary_receiver_curry, receiver_read]
  apply congrArg (fun paired : Z ⟶ processes binding ⊗ processes binding =>
    paired ≫ (continuation binding).parallel)
  apply hom_ext
  · erw [lift_fst, lift_fst]
    change _ = lift (environment .nm .zero)
      (lift (environment .nm (.succ .zero)) (environment .nm (.succ (.succ .zero)))) ≫
        (lift (fst _ _) (snd _ _ ≫ (binaryTuple binding).inv) ≫ output binding 2)
    rw [← Category.assoc, comp_lift]
    erw [lift_fst, lift_snd_assoc, binary_tuple_packing]
    dsimp only [output, vector]
    dsimp only [tuple, names, ClosedPresentation.Operations.context, AllArity.names, contextOf]
    simp only [comp_lift_assoc, comp_lift]
    simp
    erw [lift_snd]
  · erw [lift_snd, lift_snd]
    dsimp only [continuation, input]
    dsimp only [tuple, names, ClosedPresentation.Operations.context, AllArity.names, contextOf]
    simp only [comp_lift_assoc, comp_lift, lift_snd, lift_fst_assoc, comp_toUnit]
    erw [lift_fst_assoc, lift_snd_assoc, comp_toUnit]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedCommunicationValues
