import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.RhoPast
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.Hiding

/-!
# The history control after hiding: the knowledge of a heated store says nothing about its rows

The tree's history control (`NativeTypesOnTheStep.RhoNativeTypes.knowledge_not_native`) takes two
heated stores denoting one closed rho process, one with no knowledge and one with the matches of a
communication in its knowledge, and concludes that "the knowledge is empty" is a predicate of the
step that is the pullback of no predicate on processes.

At the empty context there is nothing to instantiate: every substitution is the identity
(`substitution_trivial`). A heated store's knowledge holds at the identity, so it holds at every
substitution (`heated_knowledge_equivalent`): it is equivalent to the empty store, and seen alike
from any family of terms (`heated_seen_alike`). Its projection onto what the rows mention is the
empty store, for every heated store.

* `the_pair`: the pair of the control, rebuilt from the same theorems: one process, no knowledge on
  one side and knowledge on the other.
* **`pair_hidden_alike`**: on that pair the two knowledges are equivalent, and seen alike from the
  rows by the empty store; so after hiding the two stores have the same knowledge.
* **`hidden_knowledge_native`**: the hiding-invariant form of "the knowledge is empty" (the knowledge
  is equivalent to the empty store) is the pullback of a predicate on processes, the constant one.
  So `knowledge_not_native` disappears on the projected states; what it observes is the list, not
  the knowledge's content.
* `raw_knowledge_not_hiding_invariant`: the raw predicate separates two stores whose knowledges are
  equivalent, so it is not a predicate of the hidden state.
* The store only grows before hiding (`LogicOverTheStep.RhoPast.channelStep_learns`: every
  communication adds equations); after hiding the knowledge of every heated store is the empty store
  (`hidden_store_constant`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingRho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open ContextualCommunicationProfiles (action)
open FragmentsOfTheStep.NarrowingToRho
open LogicOverTheStep.RhoPast
open Mettapedia.OSLF.Framework.DerivedModalities (pb)

/-- **At the empty context every substitution is the identity.** -/
theorem substitution_trivial (σ : Sub sig ([] : Ctx sig) []) : σ = (action []).identity := by
  funext s v
  cases v

/-- **The knowledge of a heated store at the empty context holds at every substitution.** -/
theorem heated_knowledge_solved (C : HeatedStore []) (σ : Sub sig ([] : Ctx sig) []) :
    (action []).Models σ C.1.equations := by
  rw [substitution_trivial σ]
  exact C.2.1

/-- **It is equivalent to the empty store.** -/
theorem heated_knowledge_equivalent (C : HeatedStore []) :
    (action []).Equivalent C.1.equations [] :=
  fun σ => ⟨fun _ => (action []).models_nil σ, fun _ => heated_knowledge_solved C σ⟩

/-- **It is seen alike from any family of terms by the empty store.** -/
theorem heated_seen_alike (C : HeatedStore []) (F : Process [] → Prop) :
    SeenAlike (action []) C.1.equations [] F :=
  ⟨fun σ _ => ⟨σ, (action []).models_nil σ, fun _ _ => rfl⟩,
    fun σ' _ => ⟨σ', heated_knowledge_solved C σ', fun _ _ => rfl⟩⟩

/-- **The pair of the history control**: two heated stores with one process, one with no knowledge
and one with knowledge. -/
theorem the_pair :
    ∃ C₀ C₁ : HeatedStore [], narrow C₀ = narrow C₁ ∧ C₀.1.equations = [] ∧ C₁.1.equations ≠ [] := by
  obtain ⟨C₀, P, empty, step⟩ := forgetful_store
  obtain ⟨C, rfl⟩ := narrowing_onto P
  obtain ⟨C₁, moved, image⟩ := narrowing_functionalBisimulation.zag step
  exact ⟨C₀, C₁, image.symm, empty, channelStep_learns moved⟩

/-- **On that pair the knowledges are equivalent, and both are seen alike from the rows by the empty
store**: after hiding, the two stores have the same knowledge. -/
theorem pair_hidden_alike :
    ∃ C₀ C₁ : HeatedStore [], narrow C₀ = narrow C₁ ∧ C₀.1.equations = [] ∧ C₁.1.equations ≠ [] ∧
      (action []).Equivalent C₀.1.equations C₁.1.equations ∧
      SeenAlike (action []) C₀.1.equations [] (fun _ => True) ∧
      SeenAlike (action []) C₁.1.equations [] (fun _ => True) := by
  obtain ⟨C₀, C₁, same, empty, nonempty⟩ := the_pair
  refine ⟨C₀, C₁, same, empty, nonempty, fun σ => ?_, heated_seen_alike C₀ _, heated_seen_alike C₁ _⟩
  exact ⟨fun _ => heated_knowledge_solved C₁ σ, fun _ => heated_knowledge_solved C₀ σ⟩

/-- **The history control disappears after hiding**: the hiding-invariant form of "the knowledge is
empty" is the pullback of a predicate on processes. -/
theorem hidden_knowledge_native :
    (fun C : HeatedStore [] => (action []).Equivalent C.1.equations []) = pb narrow (fun _ => True) := by
  funext C
  exact propext ⟨fun _ => trivial, fun _ => heated_knowledge_equivalent C⟩

/-- **The raw predicate is not a predicate of the hidden state**: it separates two stores whose
knowledges are equivalent. -/
theorem raw_knowledge_not_hiding_invariant :
    ¬ ∀ C₀ C₁ : HeatedStore [], (action []).Equivalent C₀.1.equations C₁.1.equations →
      (C₀.1.equations = [] ↔ C₁.1.equations = []) := by
  intro invariant
  obtain ⟨C₀, C₁, -, empty, nonempty, equivalent, -, -⟩ := pair_hidden_alike
  exact nonempty ((invariant C₀ C₁ equivalent).mp empty)

/-- **After hiding, the knowledge of every heated store is the empty store**: it does not grow along
communications, while the raw store does (`channelStep_learns`). -/
theorem hidden_store_constant (C C' : HeatedStore []) :
    (action []).Equivalent C.1.equations C'.1.equations :=
  fun σ => ⟨fun _ => heated_knowledge_solved C' σ, fun _ => heated_knowledge_solved C σ⟩

#print axioms substitution_trivial
#print axioms heated_knowledge_equivalent
#print axioms pair_hidden_alike
#print axioms hidden_knowledge_native
#print axioms raw_knowledge_not_hiding_invariant
#print axioms hidden_store_constant

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Scope.HidingRho
