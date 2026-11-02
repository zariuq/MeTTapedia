import Mettapedia.Logic.HOL.FiniteConstructorGuardProofs
import Mettapedia.Logic.HOL.PredicateFixedPoint

/-!
# Retained elimination of finite constructor guards

Finite disjunctions are eliminated by one branch per occurrence. Existential
field telescopes are eliminated against a universally bound branch proof,
with fresh fields kept in the actual HOL context. Both programs include
empty inventories and empty field telescopes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {assumptions : List (Formula Const Γ)}

def any_elim (formulas : List (Formula Const Γ)) (target : Formula Const Γ)
    (present : ProofSyntax Const assumptions (any formulas))
    (branches : (occurrence : Fin formulas.length) →
      ProofSyntax Const assumptions (.imp (formulas.get occurrence) target)) :
    ProofSyntax Const assumptions target := by
  induction formulas generalizing assumptions with
  | nil => exact .botE present
  | cons first rest previous =>
    exact .orE present
      (.impE ((branches ⟨0, by simp⟩).prepend first) (.hyp 0))
      (previous (.hyp 0) (fun occurrence =>
        (branches ⟨occurrence.val + 1, Nat.succ_lt_succ occurrence.isLt⟩).prepend (any rest)))

theorem any_elim_free (formulas : List (Formula Const Γ)) (target : Formula Const Γ)
    (present : ProofSyntax Const assumptions (any formulas))
    (branches : (occurrence : Fin formulas.length) →
      ProofSyntax Const assumptions (.imp (formulas.get occurrence) target))
    (presentFree : present.FunctionExtensionalityFree)
    (branchesFree : ∀ occurrence, (branches occurrence).FunctionExtensionalityFree) :
    (any_elim formulas target present branches).FunctionExtensionalityFree := by
  induction formulas generalizing assumptions with
  | nil => exact presentFree
  | cons first rest previous =>
    refine ⟨presentFree, ?_, ?_⟩
    · simpa only [ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono, and_true] using branchesFree ⟨0, by simp⟩
    · apply previous
      · trivial
      · intro occurrence
        exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
          (branchesFree ⟨occurrence.val + 1, Nat.succ_lt_succ occurrence.isLt⟩)

def argumentBranches : {Γ : Ctx Base} → (fields : List (Ty Base)) →
    Term Const Γ (handlerType fields) → Formula Const Γ → Formula Const Γ
  | _, [], predicate, target => .imp predicate target
  | _, _ :: rest, predicate, target =>
    .all (argumentBranches rest (.app (weaken predicate) (.var .vz)) (weaken target))

@[simp] theorem argumentBranches_subst (theta : Subst Const Γ Ξ)
    (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields)) (target : Formula Const Γ) :
    HOL.subst theta (argumentBranches fields predicate target) =
      argumentBranches fields (HOL.subst theta predicate) (HOL.subst theta target) := by
  induction fields generalizing Γ Ξ with
  | nil => rfl
  | cons type rest previous =>
    simp only [argumentBranches, HOL.subst, previous, subst_weaken, Subst.lift]

private def fresh_all {type : Ty Base} (body : Formula Const (type :: Γ))
    (proof : ProofSyntax Const assumptions (.all body)) :
    ProofSyntax Const (weakenHyps assumptions) body := by
  apply ProofSyntax.castIndices rfl ?_
    (.allE (.var .vz) (PredicateFixedPoint.weakenProof proof))
  change instantiate (.var .vz) (HOL.rename (Rename.lift Rename.weaken) body) = body
  rw [instantiate, subst_rename]
  exact ProofSyntax.term_subst_of_identity (fun index => by cases index <;> rfl) body

private theorem fresh_all_free {type : Ty Base} (body : Formula Const (type :: Γ))
    (proof : ProofSyntax Const assumptions (.all body)) (free : proof.FunctionExtensionalityFree) :
    (fresh_all body proof).FunctionExtensionalityFree := by
  simp only [fresh_all, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree, PredicateFixedPoint.weakenProof,
    ProofSyntax.functionExtensionalityFree_rename]
  exact free

def existsArguments_elim (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (target : Formula Const Γ) (present : ProofSyntax Const assumptions (existsArguments fields predicate))
    (branches : ProofSyntax Const assumptions (argumentBranches fields predicate target)) :
    ProofSyntax Const assumptions target := by
  induction fields generalizing Γ with
  | nil => exact .impE branches present
  | cons type rest previous =>
    exact .exE present (previous (.app (weaken predicate) (.var .vz)) (weaken target) (.hyp 0)
      ((fresh_all _ branches).prepend (existsArguments rest (.app (weaken predicate) (.var .vz)))))

theorem existsArguments_elim_free (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (target : Formula Const Γ) (present : ProofSyntax Const assumptions (existsArguments fields predicate))
    (branches : ProofSyntax Const assumptions (argumentBranches fields predicate target))
    (presentFree : present.FunctionExtensionalityFree) (branchesFree : branches.FunctionExtensionalityFree) :
    (existsArguments_elim fields predicate target present branches).FunctionExtensionalityFree := by
  induction fields generalizing Γ with
  | nil => exact ⟨branchesFree, presentFree⟩
  | cons type rest previous =>
    refine ⟨presentFree, ?_⟩
    apply previous
    · trivial
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (fresh_all_free _ branches branchesFree)

#print axioms any_elim
#print axioms existsArguments_elim
#print axioms existsArguments_elim_free

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
