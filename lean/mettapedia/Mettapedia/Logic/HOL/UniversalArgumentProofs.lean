import Mettapedia.Logic.HOL.FiniteConstructorCaseProofs

/-!
# Universal proofs over ordered field telescopes

The existing substitution-indexed argument bodies also support universal
binding. Introduction retains fresh fields in the real context; elimination
supplies the original ordered arguments. Naturality and rule-freedom laws
apply to dependent bodies, including constructor clauses with computed indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}

def forallArguments : {Γ : Ctx Base} → (fields : List (Ty Base)) →
    ArgumentBody Const Γ fields → Formula Const Γ
  | _, [], body => body Subst.id PUnit.unit
  | _, _ :: rest, body => .all (forallArguments rest (bindHead body))

theorem forallArguments_subst (images : Subst Const Γ Ξ)
    (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields) (natural : NaturalBody body) :
    HOL.subst images (forallArguments fields body) =
      forallArguments fields (fun later arguments =>
        body (fun index => HOL.subst later (images index)) arguments) := by
  induction fields generalizing Γ Ξ with
  | nil =>
      apply (natural Subst.id images PUnit.unit).trans
      apply congrArg (fun mapping : Subst Const Γ Ξ => body mapping PUnit.unit)
      funext type index
      exact (HOL.subst_id (images index)).symm
  | cons type rest previous =>
      change Term.all (HOL.subst (Subst.lift images) (forallArguments rest (bindHead body))) = _
      rw [previous (Subst.lift images) (bindHead body) (bindHead_natural body natural)]
      apply congrArg Term.all
      apply congrArg (forallArguments rest)
      funext laterContext later arguments
      unfold bindHead
      apply congrArg (fun mapping : Subst Const Γ laterContext => body mapping (later .vz, arguments))
      funext result index
      exact HOL.subst_rename later Rename.weaken (images index)

theorem forallArguments_instantiate {type : Ty Base} {fields : List (Ty Base)}
    (body : ArgumentBody Const Γ (type :: fields)) (natural : NaturalBody body)
    (argument : Term Const Γ type) :
    instantiate argument (forallArguments fields (bindHead body)) =
      forallArguments fields (supplyHead body argument) := by
  rw [instantiate, forallArguments_subst _ _ _ (bindHead_natural body natural)]
  rfl

def forallArguments_elim {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields) (natural : NaturalBody body)
    (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions (forallArguments fields body)) :
    ProofSyntax Const assumptions (body Subst.id arguments) := by
  induction fields generalizing Γ with
  | nil => exact proof
  | cons type rest previous =>
      let tailProof : ProofSyntax Const assumptions (forallArguments rest (supplyHead body arguments.1)) :=
        ProofSyntax.castIndices rfl (forallArguments_instantiate body natural arguments.1)
          (.allE arguments.1 proof)
      apply ProofSyntax.castIndices rfl ?_
        (previous (supplyHead body arguments.1) (supplyHead_natural body natural arguments.1) arguments.2 tailProof)
      simp only [supplyHead, HOL.subst_id]
      cases arguments
      rfl

theorem forallArguments_elim_free {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields) (natural : NaturalBody body)
    (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions (forallArguments fields body))
    (free : proof.FunctionExtensionalityFree) :
    (forallArguments_elim fields body natural arguments proof).FunctionExtensionalityFree := by
  induction fields generalizing Γ with
  | nil => exact free
  | cons type rest previous =>
      unfold forallArguments_elim
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply previous (supplyHead body arguments.1) (supplyHead_natural body natural arguments.1) arguments.2
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact free

abbrev ArgumentProof (assumptions : List (Formula Const Γ)) (fields : List (Ty Base))
    (body : ArgumentBody Const Γ fields) :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ fields),
    ProofSyntax Const (assumptions.map (HOL.subst images)) (body images arguments)

def bindArgumentProof {assumptions : List (Formula Const Γ)} {type : Ty Base} {fields : List (Ty Base)}
    {body : ArgumentBody Const Γ (type :: fields)}
    (branch : ArgumentProof assumptions (type :: fields) body) :
    ArgumentProof (HOL.weakenHyps (σ := type) assumptions) fields (bindHead body) := by
  intro Ξ images arguments
  let original : Subst Const Γ Ξ := fun index => images (.vs index)
  apply ProofSyntax.castIndices ?_ rfl (branch original (images .vz, arguments))
  symm
  change (assumptions.map HOL.weaken).map (HOL.subst images) = assumptions.map (HOL.subst original)
  rw [List.map_map]
  apply List.map_congr_left
  intro formula _
  exact HOL.subst_rename images Rename.weaken formula

theorem bindArgumentProof_free {assumptions : List (Formula Const Γ)} {type : Ty Base}
    {fields : List (Ty Base)} {body : ArgumentBody Const Γ (type :: fields)}
    (branch : ArgumentProof assumptions (type :: fields) body)
    (free : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) arguments,
      (branch images arguments).FunctionExtensionalityFree) :
    ∀ {Ξ : Ctx Base} (images : Subst Const (type :: Γ) Ξ) arguments,
      (bindArgumentProof branch images arguments).FunctionExtensionalityFree := by
  intro Ξ images arguments
  unfold bindArgumentProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free (fun index => images (.vs index)) (images .vz, arguments)

def forallArguments_intro {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields)
    (branch : ArgumentProof assumptions fields body) :
    ProofSyntax Const assumptions (forallArguments fields body) := by
  induction fields generalizing Γ with
  | nil =>
      apply ProofSyntax.castIndices ?_ rfl (branch Subst.id PUnit.unit)
      exact ProofSyntax.terms_subst_of_identity (fun _ => rfl) assumptions
  | cons type rest previous =>
      exact .allI (previous (bindHead body) (bindArgumentProof branch))

theorem forallArguments_intro_free {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields)
    (branch : ArgumentProof assumptions fields body)
    (free : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) arguments,
      (branch images arguments).FunctionExtensionalityFree) :
    (forallArguments_intro fields body branch).FunctionExtensionalityFree := by
  induction fields generalizing Γ with
  | nil =>
      unfold forallArguments_intro
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact free Subst.id PUnit.unit
  | cons type rest previous =>
      exact previous (bindHead body) (bindArgumentProof branch) (bindArgumentProof_free branch free)

#print axioms forallArguments_subst
#print axioms forallArguments_elim_free
#print axioms forallArguments_intro_free

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
