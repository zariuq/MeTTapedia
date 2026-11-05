import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecovery
import Mettapedia.Logic.HOL.IndexedContainerInventoryProofs

/-!
# The family predicate derived from the parsed stored inventory

The family is the actual contextual least predicate refined by the same
inventory's root program at its original unindexed result. Constructor
membership is built from original field evidence and the full active-child,
edge and inactive-padding obligations. No arbitrary family predicate is
identified with this one, and no semantic inverse produces object evidence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamily
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open FiniteConstructorEncoding IndexedContainerPositionTerms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {N A E : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
  (tags : Nat → Term Const Γ N) (bottom : Term Const Γ E)

def signature := IndexedVectorTreeStoredConstructorRecovery.recursiveSignature
  given source numbers zero one successor tags bottom
def inventory := IndexedVectorTreeStoredFieldGuards.inventory given source numbers zero one tags
def construct := IndexedVectorTreeStoredConstructorRecovery.storedConstructor given
def root := (inventory given source numbers zero one tags).rootProgram (construct given)

def member : Term Const Γ (E ⇒ .prop ⇒ .prop) :=
  (signature given source numbers zero one successor tags bottom).memberProgram (root given source numbers zero one tags)

/-- Definitional coherence with the already interpreted generic inventory
program; this equation does not assert a new semantic realization. -/
theorem member_sameInventory : member given source numbers zero one successor tags bottom =
    IndexedContainerInventory.memberProgram IndexedVectorTreeStoredFieldGuards.codes
      (guards := IndexedVectorTreeStoredFieldGuards.guards given source numbers zero one)
      Subst.id tags zero successor bottom (construct given) := rfl

private def atIndex {space index : Ty Base} (program : Term Const Γ (space ⇒ index ⇒ .prop))
    (selected : Term Const Γ index) : Term Const Γ (space ⇒ .prop) :=
  .lam (.app (.app (weaken program) (.var .vz)) (weaken selected))

@[irreducible] private def atIndex_application {space index : Ty Base} (program : Term Const Γ (space ⇒ index ⇒ .prop))
    (selected : Term Const Γ index) {assumptions : List (Formula Const Γ)} (value : Term Const Γ space) :
    ProofSyntax Const assumptions (.eq (.app (atIndex program selected) value) (.app (.app program value) selected)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value (.app (.app (weaken program) (.var .vz)) (weaken selected)))
  simp only [atIndex,instantiate,HOL.subst,Subst.single]
  rw [show HOL.subst (Subst.single value) (weaken program) = program from instantiate_weaken value program,
    show HOL.subst (Subst.single value) (weaken selected) = selected from instantiate_weaken value selected]

private theorem atIndex_application_free {space index : Ty Base} (program : Term Const Γ (space ⇒ index ⇒ .prop))
    (selected : Term Const Γ index) {assumptions : List (Formula Const Γ)} (value : Term Const Γ space) :
    (atIndex_application program selected (assumptions := assumptions) value).FunctionExtensionalityFree := by
  unfold atIndex_application
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def family : Term Const Γ (E ⇒ .prop) :=
  atIndex (member given source numbers zero one successor tags bottom) .top

variable {Δ : List (Formula Const Γ)}

@[irreducible] def family_application (value : Term Const Γ E) :
    ProofSyntax Const Δ (.eq (.app (family given source numbers zero one successor tags bottom) value)
      (.app (.app (member given source numbers zero one successor tags bottom) value) .top)) :=
  atIndex_application (member given source numbers zero one successor tags bottom) .top value

theorem family_application_free (value : Term Const Γ E) :
    (family_application given source numbers zero one successor tags bottom (Δ := Δ) value).FunctionExtensionalityFree := by
  unfold family_application
  exact atIndex_application_free (member given source numbers zero one successor tags bottom) .top value

@[irreducible] def family_beta (value : Term Const Γ E) :
    ProofSyntax Const Δ (.eq (.app (family given source numbers zero one successor tags bottom) value)
      (.and (.app (signature given source numbers zero one successor tags bottom).least value)
        (.app (.app (root given source numbers zero one tags) value) .top))) :=
  .eqTrans (family_application given source numbers zero one successor tags bottom value)
    ((signature given source numbers zero one successor tags bottom).member_beta
      (root given source numbers zero one tags) value .top)

theorem family_beta_free (value : Term Const Γ E) :
    (family_beta given source numbers zero one successor tags bottom (Δ := Δ) value).FunctionExtensionalityFree := by
  unfold family_beta
  exact ⟨family_application_free given source numbers zero one successor tags bottom value,
    (signature given source numbers zero one successor tags bottom).member_beta_free
      (root given source numbers zero one tags) value .top⟩

def memberLeast (value : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app (family given source numbers zero one successor tags bottom) value)) :
    ProofSyntax Const Δ (.app (signature given source numbers zero one successor tags bottom).least value) :=
  .andEL (.impE (.eqPropEL (family_beta given source numbers zero one successor tags bottom value)) present)

def memberRoot (value : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app (family given source numbers zero one successor tags bottom) value)) :
    ProofSyntax Const Δ (.app (.app (root given source numbers zero one tags) value) .top) :=
  .andER (.impE (.eqPropEL (family_beta given source numbers zero one successor tags bottom value)) present)

theorem memberLeast_free (value : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app (family given source numbers zero one successor tags bottom) value))
    (free : present.FunctionExtensionalityFree) :
    (memberLeast given source numbers zero one successor tags bottom value present).FunctionExtensionalityFree :=
  ⟨family_beta_free given source numbers zero one successor tags bottom value,free⟩

theorem memberRoot_free (value : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app (family given source numbers zero one successor tags bottom) value))
    (free : present.FunctionExtensionalityFree) :
    (memberRoot given source numbers zero one successor tags bottom value present).FunctionExtensionalityFree :=
  ⟨family_beta_free given source numbers zero one successor tags bottom value,free⟩

#print axioms member_sameInventory
#print axioms family_beta
#print axioms memberLeast_free
#print axioms memberRoot_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamily
