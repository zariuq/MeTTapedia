import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetTheory
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSeparation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSubsetCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedAntiFoundation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedDeductionControls

/-!
# The validated varying constructive graph theory

Adoption records index the independently stated ordinary first-order
sentences actually validated by this model. Bounded Separation, arbitrary
Strong Collection and Subset Collection use the same future-indexed untyped value universe as
empty set, pairing, union, infinity and extensionality. Substitution and
deduction compute complete realizers without converting erased existence
into witness data. Graph anti-foundation is supplied separately by the
bounded diagram decoration theorem.

This fragment does not adopt powerset, unrestricted Separation,
excluded middle, membership induction or equality reflection.
The growing countermodel and an actual cyclic value respectively rule out
classical excluded-middle adoption and universal self-membership prohibition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedTheory

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization
open ContextualMaterialSetTheory (emptyAxiom pairingAxiom unionAxiom infinityAxiom
  extensionalityAxiom separationAxiom strongCollectionAxiom)
open GraphBoundedFormulaRealization (BoundedFormula toFormula)

universe u
variable {D : Type u} [Category.{u} D]

/-- These records are object-theory adoption data, not host assumptions. -/
inductive Axiom : {count : Nat} → Formula count → Type where
  | empty : Axiom emptyAxiom
  | pairing : Axiom pairingAxiom
  | union : Axiom unionAxiom
  | infinity : Axiom infinityAxiom
  | extensionality : Axiom extensionalityAxiom
  | boundedSeparation {count : Nat} (body : BoundedFormula (count+1)) :
      Axiom (separationAxiom (toFormula body))
  | strongCollection {count : Nat} (body : Formula (count+2)) :
      Axiom (strongCollectionAxiom body)
  | subsetCollection {count : Nat} (body : Formula (count+3)) :
      Axiom (GraphRealizedSetTheory.subsetCollectionAxiom body)
  | substitution {count other : Nat} {body : Formula count}
      (indices : Fin count → Fin other) (adopted : Axiom body) :
      Axiom (ContextualMaterialLogic.substitute indices body)

/-- Every named law and schema instance has its constructed realizer at
every context and assignment. -/
def validate {count : Nat} {body : Formula count} (adopted : Axiom body)
    (point : D) (environment : Environment D count point) : realize D body point environment :=
  match count, body, adopted with
  | _, _, .empty => ContextualGraphRealizedSetTheory.emptyLaw point environment
  | _, _, .pairing => ContextualGraphRealizedSetTheory.pairingLaw point environment
  | _, _, .union => ContextualGraphRealizedSetTheory.unionLaw point environment
  | _, _, .infinity => ContextualGraphRealizedSetTheory.infinityLaw point environment
  | _, _, .extensionality => ContextualGraphRealizedSetTheory.extensionalityLaw point environment
  | _, _, .boundedSeparation bounded => ContextualGraphRealizedSeparation.separationLaw bounded environment
  | _, _, .strongCollection formula => ContextualGraphRealizedCollection.strongCollectionLaw formula environment
  | _, _, .subsetCollection formula => ContextualGraphRealizedSubsetCollection.subsetCollectionLaw formula environment
  | _, _, .substitution indices previous =>
      (realize_substitution D indices _ point environment).symm ▸
        validate previous point (environment ∘ indices)

/-- Adopted assumptions retain their individual positions while the
actual deduction tree computes a realizer of its conclusion. -/
def deduction {count : Nat} {assumptions : List (Formula count)} {conclusion : Formula count}
    (proof : GraphRealizedDeduction.Proof assumptions conclusion)
    (adopted : (index : Fin assumptions.length) → Axiom assumptions[index.val])
    (point : D) (environment : Environment D count point) : realize D conclusion point environment :=
  ContextualGraphRealizedDeduction.interpret proof point environment
    (fun index => validate (adopted index) point environment)

theorem excluded_middle_not_adopted :
    ¬ Nonempty (Axiom ContextualGraphRealizedDeductionControls.excludedMiddle) := by
  rintro ⟨adopted⟩
  exact ContextualGraphRealizedDeductionControls.excluded_middle_empty
    ⟨validate adopted 0 (ContextualGraphRealizedDeductionControls.environment 1 0)⟩

def loop : Diagram D where
  nodes := {
    obj _ := PUnit.{u+1}
    map _ := TypeCat.ofHom id
    map_id _ := rfl
    map_comp _ _ := rfl }
  edge _ _ _ := True
  edge_transport := fun {_ _} _ {_ _} available => available

def loopValue (point : D) : Value D point := ⟨loop, PUnit.unit⟩

def loopMember (point : D) : Member (loopValue point) (loopValue point) :=
  Member.atChild (loopValue point) ⟨PUnit.unit, True.intro⟩

theorem loop_transport {first second : D} (arrival : first ⟶ second) :
    move D arrival (loopValue first) = loopValue second := rfl

def selfMembershipProhibition : Formula 0 := .all (.imply (.member 0 0) .bottom)

theorem self_membership_prohibition_not_adopted :
    ¬ Nonempty (Axiom selfMembershipProhibition) := by
  rintro ⟨adopted⟩
  let environment : Environment Nat 0 0 := fun index => False.elim (Nat.not_lt_zero _ index.isLt)
  let proof := validate adopted 0 environment
  exact PEmpty.elim (proof 0 (𝟙 0) (loopValue 0) 0 (𝟙 0) ⟨loopMember 0⟩)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedTheory
