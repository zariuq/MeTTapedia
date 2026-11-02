import Mettapedia.Logic.HOL.CurriedFieldPrograms
import Mettapedia.Logic.HOL.FiniteConstructorFieldProjection
import Mettapedia.Logic.HOL.ProofSyntaxCongruence

/-!
# Typed maps between constructor field telescopes

Each output field carries an actual curried HOL program receiving the complete
original row. Earlier lengths and indices remain available to later shape
encodings. Equal-typed positions may use different programs, and rows may have
different arities. Handler precomposition is
contravariant; application to the original fields computes the covariant
mapped argument tuple by retained beta proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
universe u v
variable {Base : Type u}

structure FieldMaps (Const : Ty Base → Type v) (Γ : Ctx Base)
    (source target : List (Ty Base)) where
  output : ∀ {type : Ty Base}, Var target type → Term Const Γ (CurriedPredicates.FunctionType source type)

namespace FieldMaps
open CurriedPredicates
variable {Const : Ty Base → Type v} {Γ Ξ Ω : Ctx Base}
  {source target : List (Ty Base)} {Δ : List (Formula Const Γ)}

def subst (images : Subst Const Γ Ξ) (maps : FieldMaps Const Γ source target) : FieldMaps Const Ξ source target where
  output index := HOL.subst images (maps.output index)

theorem subst_comp (maps : FieldMaps Const Γ source target)
    (first : Subst Const Γ Ξ) (later : Subst Const Ξ Ω) :
    (maps.subst first).subst later = maps.subst (Subst.comp later first) := by
  apply congrArg FieldMaps.mk
  funext type index
  exact HOL.subst_comp later first (maps.output index)

theorem subst_identity (maps : FieldMaps Const Γ source target) :
    maps.subst (fun index => .var index) = maps := by
  cases maps with
  | mk output =>
      apply congrArg FieldMaps.mk
      funext type index
      exact ProofSyntax.term_subst_of_identity (fun _ => rfl) (output index)

theorem subst_weaken {type : Ty Base} (maps : FieldMaps Const Γ source target)
    (images : Subst Const Γ Ξ) :
    (maps.subst (Subst.ofRename (Rename.weaken (σ := type)))).subst (Subst.lift images) =
      (maps.subst images).subst (Subst.ofRename Rename.weaken) := by
  apply congrArg FieldMaps.mk
  funext output index
  simp only [subst,subst_ofRename]
  change HOL.subst (Subst.lift images) (weaken (maps.output index)) = weaken (HOL.subst images (maps.output index))
  exact HOL.subst_weaken images (maps.output index)

def collect (fields : List (Ty Base))
    (terms : ∀ {type : Ty Base}, Var fields type → Term Const Γ type) : Arguments Const Γ fields :=
  match fields with
  | [] => PUnit.unit
  | _ :: rest => (terms .vz,collect rest (fun index => terms (.vs index)))

theorem collect_subst (fields : List (Ty Base))
    (terms : ∀ {type : Ty Base}, Var fields type → Term Const Γ type) (images : Subst Const Γ Ξ) :
    substituteArguments images fields (collect fields terms) =
      collect fields (fun index => HOL.subst images (terms index)) := by
  induction fields with
  | nil => rfl
  | cons type rest previous => exact congrArg (Prod.mk (HOL.subst images (terms .vz))) (previous (fun index => terms (.vs index)))

theorem argumentAt_collect {type : Ty Base} {fields : List (Ty Base)} (index : Var fields type)
    (terms : ∀ {type : Ty Base}, Var fields type → Term Const Γ type) :
    argumentAt index (collect fields terms) = terms index := by
  induction index with
  | vz => rfl
  | vs index previous => exact previous (fun index => terms (.vs index))

def apply (maps : FieldMaps Const Γ source target) (arguments : Arguments Const Γ source) : Arguments Const Γ target :=
  collect target (fun index => applyFields source (maps.output index) arguments)

theorem argumentAt_apply (maps : FieldMaps Const Γ source target) (arguments : Arguments Const Γ source)
    {type : Ty Base} (index : Var target type) :
    argumentAt index (maps.apply arguments) = applyFields source (maps.output index) arguments :=
  argumentAt_collect index _

theorem apply_subst (maps : FieldMaps Const Γ source target) (images : Subst Const Γ Ξ)
    (arguments : Arguments Const Γ source) :
    substituteArguments images target (maps.apply arguments) =
      (maps.subst images).apply (substituteArguments images source arguments) := by
  unfold apply
  rw [collect_subst]
  apply congrArg (collect target)
  funext type index
  exact applyFields_subst images source (maps.output index) arguments

theorem apply_weaken {bound : Ty Base} (maps : FieldMaps Const Γ source target)
    (arguments : Arguments Const Γ source) :
    (maps.subst (Subst.ofRename (Rename.weaken (σ := bound)))).apply (weakenArguments bound source arguments) =
      weakenArguments bound target (maps.apply arguments) := by
  symm
  simpa only [FiniteConstructorFieldProjection.substituteArguments_shift] using
    maps.apply_subst (Subst.ofRename (Rename.weaken (σ := bound))) arguments

def handlerBody (maps : FieldMaps Const Γ source target) (handler : Term Const Γ (handlerType target)) :
    ArgumentBody Const Γ source :=
  fun images arguments => applyArguments target (HOL.subst images handler) ((maps.subst images).apply arguments)

theorem handlerBody_natural (maps : FieldMaps Const Γ source target) (handler : Term Const Γ (handlerType target)) :
    NaturalBody (maps.handlerBody handler) := by
  intro Ξ Ω first later arguments
  simp only [handlerBody,applyArguments_subst,apply_subst,subst_comp,HOL.subst_comp]
  rfl

def precompose (maps : FieldMaps Const Γ source target) (handler : Term Const Γ (handlerType target)) :
    Term Const Γ (handlerType source) :=
  abstractArguments source (maps.handlerBody handler)

theorem precompose_subst (maps : FieldMaps Const Γ source target) (handler : Term Const Γ (handlerType target))
    (images : Subst Const Γ Ξ) :
    HOL.subst images (maps.precompose handler) = (maps.subst images).precompose (HOL.subst images handler) := by
  rw [precompose,abstractArguments_subst _ _ _ (maps.handlerBody_natural handler)]
  apply congrArg (abstractArguments source)
  funext Ω later arguments
  simp only [handlerBody,subst_comp,HOL.subst_comp]
  rfl

def precompose_at (maps : FieldMaps Const Γ source target) (handler : Term Const Γ (handlerType target))
    (arguments : Arguments Const Γ source) :
    ProofSyntax Const Δ (.eq (applyArguments source (maps.precompose handler) arguments)
      (applyArguments target handler (maps.apply arguments))) := by
  apply ProofSyntax.castIndices rfl ?_ (abstractArguments_beta source (maps.handlerBody handler)
    (maps.handlerBody_natural handler) arguments)
  simp only [handlerBody,subst_identity]
  exact congrArg (Term.eq _) (congrArg (fun current => applyArguments target current (maps.apply arguments))
    (ProofSyntax.term_subst_of_identity (fun _ => rfl) handler))

theorem precompose_at_free (maps : FieldMaps Const Γ source target) (handler : Term Const Γ (handlerType target))
    (arguments : Arguments Const Γ source) :
    (maps.precompose_at (Δ := Δ) handler arguments).FunctionExtensionalityFree := by
  unfold precompose_at
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (abstractArguments_beta_free _ _ _ _)

#print axioms precompose_at
#print axioms precompose_at_free
end FieldMaps
end Mettapedia.Logic.HOL.FiniteConstructorEncoding
