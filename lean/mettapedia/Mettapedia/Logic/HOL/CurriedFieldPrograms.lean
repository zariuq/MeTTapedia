import Mettapedia.Logic.HOL.CurriedPredicateProofs

/-!
# Curried field programs with arbitrary typed results

Finite ordered fields abstract a substitution-natural term body. Application
has a retained beta derivation at every argument tuple, and abstraction
commutes with typed substitution. Predicate-valued abstraction agrees with
the existing constructor-guard operation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.CurriedPredicates
open FiniteConstructorEncoding

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {result : Ty Base}

abbrev FieldBody (Const : Ty Base → Type v) (Γ : Ctx Base)
    (fields : List (Ty Base)) (result : Ty Base) :=
  ∀ {Ξ : Ctx Base}, Subst Const Γ Ξ → Arguments Const Ξ fields → Term Const Ξ result

def NaturalFieldBody {fields : List (Ty Base)} (body : FieldBody Const Γ fields result) : Prop :=
  ∀ {Ξ Ω : Ctx Base} (earlier : Subst Const Γ Ξ) (later : Subst Const Ξ Ω)
    (arguments : Arguments Const Ξ fields),
    HOL.subst later (body earlier arguments) =
      body (fun index => HOL.subst later (earlier index)) (substituteArguments later fields arguments)

def abstractFields : {Γ : Ctx Base} → (fields : List (Ty Base)) →
    FieldBody Const Γ fields result → Term Const Γ (FunctionType fields result)
  | _, [], body => body (fun index => .var index) PUnit.unit
  | _, _ :: rest, body => .lam (abstractFields rest
      (fun images arguments => body (fun index => images (.vs index)) (images .vz,arguments)))

def bindField {type : Ty Base} {fields : List (Ty Base)}
    (body : FieldBody Const Γ (type :: fields) result) : FieldBody Const (type :: Γ) fields result :=
  fun images arguments => body (fun index => images (.vs index)) (images .vz,arguments)

theorem bindField_natural {type : Ty Base} {fields : List (Ty Base)}
    (body : FieldBody Const Γ (type :: fields) result) (natural : NaturalFieldBody body) :
    NaturalFieldBody (bindField body) := by
  intro Ξ Ω earlier later arguments
  exact natural (fun index => earlier (.vs index)) later (earlier .vz,arguments)

theorem abstractFields_subst (images : Subst Const Γ Ξ)
    (fields : List (Ty Base)) (body : FieldBody Const Γ fields result)
    (natural : NaturalFieldBody body) :
    HOL.subst images (abstractFields fields body) =
      abstractFields fields (fun later arguments =>
        body (fun index => HOL.subst later (images index)) arguments) := by
  induction fields generalizing Γ Ξ with
  | nil =>
      apply (natural (fun index => .var index) images PUnit.unit).trans
      apply congrArg (fun replacement : Subst Const Γ Ξ => body replacement PUnit.unit)
      funext type index
      exact (HOL.subst_id (images index)).symm
  | cons type rest previous =>
      change Term.lam (HOL.subst (Subst.lift images) (abstractFields rest (bindField body))) = _
      rw [previous (Subst.lift images) (bindField body) (bindField_natural body natural)]
      apply congrArg Term.lam
      apply congrArg (abstractFields rest)
      funext laterContext later arguments
      unfold bindField
      apply congrArg (fun replacement : Subst Const Γ laterContext => body replacement (later .vz,arguments))
      funext target index
      exact subst_rename later Rename.weaken (images index)

def supplyField {type : Ty Base} {fields : List (Ty Base)}
    (body : FieldBody Const Γ (type :: fields) result) (argument : Term Const Γ type) :
    FieldBody Const Γ fields result :=
  fun images arguments => body images (HOL.subst images argument,arguments)

theorem supplyField_natural {type : Ty Base} {fields : List (Ty Base)}
    (body : FieldBody Const Γ (type :: fields) result) (natural : NaturalFieldBody body)
    (argument : Term Const Γ type) : NaturalFieldBody (supplyField body argument) := by
  intro Ξ Ω earlier later arguments
  apply (natural earlier later (HOL.subst earlier argument,arguments)).trans
  exact congrArg (fun first => body (fun index => HOL.subst later (earlier index))
    (first,substituteArguments later fields arguments)) (HOL.subst_comp later earlier argument)

theorem abstractFields_instantiate {type : Ty Base} {fields : List (Ty Base)}
    (body : FieldBody Const Γ (type :: fields) result) (natural : NaturalFieldBody body)
    (argument : Term Const Γ type) :
    instantiate argument (abstractFields fields (bindField body)) =
      abstractFields fields (supplyField body argument) := by
  rw [instantiate,abstractFields_subst _ _ _ (bindField_natural body natural)]
  rfl

def abstractFields_beta {Δ : List (Formula Const Γ)}
    (fields : List (Ty Base)) (body : FieldBody Const Γ fields result)
    (natural : NaturalFieldBody body) (arguments : Arguments Const Γ fields) :
    ProofSyntax Const Δ (.eq (applyFields fields (abstractFields fields body) arguments)
      (body (fun index => .var index) arguments)) := by
  induction fields with
  | nil => cases arguments; exact .eqRefl _
  | cons type rest previous =>
      have first := applyFields_congr (assumptions := Δ) rest _ _ arguments.2
        (ProofSyntax.beta (Δ := Δ) arguments.1 (abstractFields rest (bindField body)))
      have first' := ProofSyntax.castIndices rfl
        (congrArg (fun target => Term.eq
          (applyFields rest (.app (.lam (abstractFields rest (bindField body))) arguments.1) arguments.2)
          (applyFields rest target arguments.2)) (abstractFields_instantiate body natural arguments.1)) first
      have remaining := previous (supplyField body arguments.1)
        (supplyField_natural body natural arguments.1) arguments.2
      apply ProofSyntax.castIndices rfl ?_ (.eqTrans first' remaining)
      apply congrArg (Term.eq _)
      unfold supplyField
      exact congrArg (fun first => body (fun index => .var index) (first,arguments.2))
        (HOL.subst_id arguments.1)

theorem abstractFields_beta_free {Δ : List (Formula Const Γ)}
    (fields : List (Ty Base)) (body : FieldBody Const Γ fields result)
    (natural : NaturalFieldBody body) (arguments : Arguments Const Γ fields) :
    (abstractFields_beta (Δ := Δ) fields body natural arguments).FunctionExtensionalityFree := by
  induction fields with
  | nil => exact True.intro
  | cons type rest previous =>
      unfold abstractFields_beta
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      refine ⟨?_,previous _ (supplyField_natural body natural arguments.1) arguments.2⟩
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact applyFields_congr_free _ _ _ _ _ True.intro

theorem functionType_prop (fields : List (Ty Base)) : FunctionType fields .prop = handlerType fields := by
  induction fields with
  | nil => rfl
  | cons type rest previous => exact congrArg (Ty.arr type) previous

theorem abstractFields_predicate (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields) :
    HEq (abstractFields fields body) (abstractArguments fields body) := by
  induction fields generalizing Γ with
  | nil => rfl
  | cons type rest previous =>
      simp only [abstractFields,abstractArguments]
      congr 1
      · exact functionType_prop rest
      · exact previous (bindHead body)

#print axioms abstractFields_subst
#print axioms abstractFields_beta
#print axioms abstractFields_beta_free
#print axioms abstractFields_predicate
end Mettapedia.Logic.HOL.CurriedPredicates
