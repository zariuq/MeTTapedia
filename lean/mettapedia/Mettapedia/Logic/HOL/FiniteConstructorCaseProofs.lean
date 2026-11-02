import Mettapedia.Logic.HOL.FiniteConstructorGuardElimination

/-!
# Retained universal cases for constructor field telescopes

A field case supplies a proof under its actual instantiated predicate and
the original hypotheses. Its typed substitution parameter keeps surrounding
variables explicit. Universal introduction binds the fresh fields in order;
the existing existential eliminator then consumes the resulting case proof.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

def FieldCase (assumptions : List (Formula Const Γ)) (fields : List (Ty Base))
    (predicate : Term Const Γ (handlerType fields)) (target : Formula Const Γ) :=
  ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ fields),
    ProofSyntax Const
      (applyArguments fields (HOL.subst images predicate) arguments ::
        assumptions.map (HOL.subst images))
      (HOL.subst images target)

namespace FieldCase

variable {assumptions : List (Formula Const Γ)}

def bindHead {type : Ty Base} {fields : List (Ty Base)}
    {predicate : Term Const Γ (handlerType (type :: fields))} {target : Formula Const Γ}
    (branch : FieldCase assumptions (type :: fields) predicate target) :
    FieldCase (weakenHyps (σ := type) assumptions) fields
      (.app (weaken predicate) (.var .vz)) (weaken target) := by
  intro Ξ images arguments
  let original : Subst Const Γ Ξ := fun index => images (.vs index)
  apply ProofSyntax.castIndices ?_ ?_ (branch original (images .vz, arguments))
  · apply congrArg₂ List.cons
    · exact congrArg
        (fun function : Term Const Ξ (handlerType (type :: fields)) =>
          applyArguments fields (.app function (images .vz)) arguments)
        (subst_rename images Rename.weaken predicate).symm
    · symm
      change (assumptions.map HOL.weaken).map (HOL.subst images) = assumptions.map (HOL.subst original)
      rw [List.map_map]
      apply List.map_congr_left
      intro formula _
      exact subst_rename images Rename.weaken formula
  · exact (subst_rename images Rename.weaken target).symm

def introduce (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (target : Formula Const Γ) (branch : FieldCase assumptions fields predicate target) :
    ProofSyntax Const assumptions (argumentBranches fields predicate target) := by
  induction fields generalizing Γ with
  | nil =>
      apply ProofSyntax.impI
      apply ProofSyntax.castIndices ?_ ?_ (branch Subst.id PUnit.unit)
      · exact congrArg₂ List.cons (HOL.subst_id predicate)
          (ProofSyntax.terms_subst_of_identity (fun _ => rfl) assumptions)
      · exact HOL.subst_id target
  | cons type rest previous =>
      exact .allI (previous (.app (weaken predicate) (.var .vz)) (weaken target) branch.bindHead)

theorem bindHead_free {type : Ty Base} {fields : List (Ty Base)}
    {predicate : Term Const Γ (handlerType (type :: fields))} {target : Formula Const Γ}
    (branch : FieldCase assumptions (type :: fields) predicate target)
    (free : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ (type :: fields)),
      (branch images arguments).FunctionExtensionalityFree) :
    ∀ {Ξ : Ctx Base} (images : Subst Const (type :: Γ) Ξ) (arguments : Arguments Const Ξ fields),
      (branch.bindHead images arguments).FunctionExtensionalityFree := by
  intro Ξ images arguments
  unfold bindHead
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact free (fun index => images (.vs index)) (images .vz, arguments)

theorem introduce_free (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (target : Formula Const Γ) (branch : FieldCase assumptions fields predicate target)
    (free : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ fields),
      (branch images arguments).FunctionExtensionalityFree) :
    (introduce fields predicate target branch).FunctionExtensionalityFree := by
  induction fields generalizing Γ with
  | nil =>
      dsimp only [introduce, ProofSyntax.FunctionExtensionalityFree]
      exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr (free Subst.id PUnit.unit)
  | cons type rest previous =>
      dsimp only [introduce, ProofSyntax.FunctionExtensionalityFree]
      exact previous _ _ branch.bindHead (bindHead_free branch free)

def eliminate (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (target : Formula Const Γ) (branch : FieldCase assumptions fields predicate target)
    (present : ProofSyntax Const assumptions (existsArguments fields predicate)) :
    ProofSyntax Const assumptions target :=
  existsArguments_elim fields predicate target present (introduce fields predicate target branch)

theorem eliminate_free (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (target : Formula Const Γ) (branch : FieldCase assumptions fields predicate target)
    (present : ProofSyntax Const assumptions (existsArguments fields predicate))
    (free : ∀ {Ξ : Ctx Base} (images : Subst Const Γ Ξ) (arguments : Arguments Const Ξ fields),
      (branch images arguments).FunctionExtensionalityFree)
    (presentFree : present.FunctionExtensionalityFree) :
    (eliminate fields predicate target branch present).FunctionExtensionalityFree :=
  existsArguments_elim_free fields predicate target present (introduce fields predicate target branch)
    presentFree (introduce_free fields predicate target branch free)

end FieldCase

#print axioms FieldCase.bindHead
#print axioms FieldCase.introduce
#print axioms FieldCase.bindHead_free
#print axioms FieldCase.introduce_free
#print axioms FieldCase.eliminate
#print axioms FieldCase.eliminate_free

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
