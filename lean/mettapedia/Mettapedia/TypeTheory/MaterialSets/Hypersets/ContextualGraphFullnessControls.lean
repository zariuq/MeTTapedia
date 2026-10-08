import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSubsetCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphNonThinControls

/-!
# Future receipt-function and Subset Collection controls

Identity receipt functions produce an image materially equal to the
whole varying source. This applies to the authored history graph whose
child fibres grow without a finite bound. Present-only receipt functions
are insufficient: two initially empty roots admit a present function,
while no complete-future function exists between their diverging labelled
histories.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFullnessControls

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphRealizedFullness
open ContextualGraphFormulaRealization
universe u
variable {D : Type u} [Category.{u} D] {point : D}

def identitySelection (source : Value D point) : ChoiceCarrier source source :=
  fun _ _ child => child

def identityImageContains (source : Value D point) (future : D) (path : point ⟶ future)
    (value : Value D future) (member : Member value (move D path source)) :
    Member value (move D path (image source source (identitySelection source))) := by
  let origin : ImageOrigin source := ⟨future, path, member.1⟩
  let selected := childValue D (move D path source) member.1
  let available := ContextualGraphGenerators.rootIntro (imageSource source) (imageArrival source)
    (imageWitness source source (identitySelection source)) path origin (𝟙 future)
    (Category.comp_id path)
  exact Member.transportParent (Equal.ofEq (image_move source source (identitySelection source) future path).symm)
    (Member.transportChild ((Equal.ofEq (move_identity D future selected)).trans member.2.symm) available)

def identityImageAgreement (source : Value D point) :
    Equal (image source source (identitySelection source)) source :=
  extensionality
    (fun future path value member => imageSubset source source (identitySelection source) future path value
      (Member.transportParent (Equal.ofEq (image_move source source (identitySelection source) future path)) member))
    (identityImageContains source)

def identityRelationPremise (source : Value D point)
    (environment : Environment D 0 point) :
    Premise (.equal 0 1) environment source source :=
  fun _ _ value member => ⟨value, member, ⟨Equal.refl value⟩⟩

def actualIdentitySubsetCollection (environment : Environment D 0 point) :
    ContextualGraphFormulaRealization.realize D
      (GraphRealizedSetTheory.subsetCollectionAxiom (.equal 0 1)) point environment :=
  ContextualGraphRealizedSubsetCollection.subsetCollectionLaw (.equal 0 1) environment

open LabelledContextPaths
open ContextualGraphNonThinControls (root arrived firstChild newest history stage)

def growingIdentityImage (label : Nat) :
    Equal (image (root label) (root label) (identitySelection (root label))) (root label) :=
  identityImageAgreement (root label)

def growingImageNewest (label count : Nat) :
    Member (childValue World (arrived label (history label count)) (newest label count))
      (move World (history label count)
        (image (root label) (root label) (identitySelection (root label)))) :=
  identityImageContains (root label) (stage count) (history label count) _
    (Member.atChild _ (newest label count))

def presentOnlyFunction : Child World (root 0) → Child World (root 1) :=
  fun impossible => False.elim ((ContextualGraphNonThinControls.initial_children_empty 0).false impossible)

theorem noCompleteFutureFunction : IsEmpty (ChoiceCarrier (root 0) (root 1)) :=
  ⟨fun selection =>
    (ContextualGraphNonThinControls.wrong_label_children_empty Nat.one_ne_zero).false
      (selection next (extension 0) (firstChild 0))⟩

theorem presentFunctionDoesNotSupplyFutureFunction :
    Nonempty (Child World (root 0) → Child World (root 1)) ∧
      IsEmpty (ChoiceCarrier (root 0) (root 1)) :=
  ⟨⟨presentOnlyFunction⟩, noCompleteFutureFunction⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFullnessControls
