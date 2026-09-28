import Mettapedia.OSLF.Syntax.IndexedRuleFiniteListSkeleton
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalFreeGenerators
import Mettapedia.OSLF.Syntax.IndexedRuleFreeSubstitutionNaturality

/-!
# Changing the binding model of a finite operational context

A finite list of event variables retains each contextual judgment and its
position. A binding-model map changes the judgments and transports every
free authored firing tree, including existing event leaves and recursive
premises under binders.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextChange

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRuleFiniteContexts
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFreeGenerators
open Mettapedia.OSLF.Binding.IndexedRuleFreeTransport
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IndexedRuleFreeSubstitutionNaturality
open CategoryTheory

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable {A B : BindingCloneAlgebra.Algebra.{0} S}

/-- A base interpretation changes a variable's contextual judgment while
keeping its finite-list position and multiplicity. -/
def pushContext (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A)) : ListContext (rules R B) where
  length := Γ.length
  label := fun position => mapJudgment h (Γ.label position)

theorem pushContext_id (A : BindingCloneAlgebra.Algebra.{0} S)
    (Γ : ListContext (rules R A)) :
    pushContext R (FreeBindingClone.Hom.id A) Γ = Γ := by
  cases Γ with
  | mk length label =>
      congr 1

theorem pushContext_comp {C : BindingCloneAlgebra.Algebra.{0} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C)
    (Γ : ListContext (rules R A)) :
    pushContext R (FreeBindingClone.Hom.comp first second) Γ =
      pushContext R second (pushContext R first Γ) := by
  cases Γ with
  | mk length label =>
      change (ListContext.mk length
          (fun position => mapJudgment
            (FreeBindingClone.Hom.comp first second) (label position)) :
            ListContext (rules R C)) =
        ListContext.mk length
          (fun position => mapJudgment second
            (mapJudgment first (label position)))
      apply congrArg (ListContext.mk length)
      funext position
      exact AuthoredPositionedRulePolynomial.mapJudgment_comp
        first second (label position)

/-- One event variable at a specified contextual judgment. -/
def singletonList (A : BindingCloneAlgebra.Algebra.{0} S)
    (judgment : Judgment A) : ListContext (rules R A) where
  length := 1
  label := fun _ => judgment

/-- The finite context with no assumed firing events. -/
def emptyList (A : BindingCloneAlgebra.Algebra.{0} S) :
    ListContext (rules R A) where
  length := 0
  label := Fin.elim0

theorem pushContext_empty (h : FreeBindingClone.Hom A B) :
    pushContext R h (emptyList R A) = emptyList R B := by
  change (ListContext.mk 0 (fun position =>
    mapJudgment h ((emptyList R A).label position)) :
      ListContext (rules R B)) =
    ListContext.mk 0 Fin.elim0
  apply congrArg (ListContext.mk 0)
  funext position
  exact Fin.elim0 position

/-- The input variables of an authored rule constructor are exactly its
ordered premise positions, with the binder-extended judgment of each. -/
def arityList (A : BindingCloneAlgebra.Algebra.{0} S)
    {judgment : Judgment A}
    (shape : (rules R A).Shape PUnit.unit judgment) :
    ListContext (rules R A) where
  length := (R.get shape.1.index).premises.length
  label := fun position => (rules R A).next shape position

theorem pushContext_singleton (h : FreeBindingClone.Hom A B)
    (judgment : Judgment A) :
    pushContext R h (singletonList R A judgment) =
      singletonList R B (mapJudgment h judgment) := rfl

/-- The source's exact binder-local premise list reindexes to the exact
premise list of the mapped constructor. -/
theorem pushContext_arity (h : FreeBindingClone.Hom A B)
    {judgment : Judgment A}
    (shape : (rules R A).Shape PUnit.unit judgment) :
    pushContext R h (arityList R A shape) =
      arityList R B (mapShape R h shape) := by
  change (ListContext.mk (R.get shape.1.index).premises.length
      (fun position => mapJudgment h
        ((rules R A).next shape position)) : ListContext (rules R B)) =
    ListContext.mk (R.get shape.1.index).premises.length
      (fun position => (rules R B).next (mapShape R h shape) position)
  apply congrArg (ListContext.mk _)
  funext position
  exact (mapInstance_child R h shape.1 position).symm

/-- The generator arrow of an authored rule is a tree node with one leaf
for each original premise position. It is not an endpoint predicate. -/
def constructorArrowList (A : BindingCloneAlgebra.Algebra.{0} S)
    {judgment : Judgment A}
    (shape : (rules R A).Shape PUnit.unit judgment) :
    arityList R A shape ⟶ singletonList R A judgment :=
  fun _ => fun
    | ⟨_, ⟨equal⟩⟩ => by
        cases equal
        exact IndexedPolynomial.Free.node (rules R A) shape
          (fun position => IndexedPolynomial.Free.pure (rules R A)
            ⟨position, ⟨rfl⟩⟩)

/-- The typed occurrence at a list position remains that same occurrence
after changing the binding model. -/
def pushSlot (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A)) {judgment : Judgment A} :
    (toContext (rules R A) Γ).slots judgment →
      (toContext (rules R B) (pushContext R h Γ)).slots
        (mapJudgment h judgment)
  | ⟨position, ⟨equal⟩⟩ =>
      ⟨position, ⟨congrArg (mapJudgment h) equal⟩⟩

/-- Even when a model map identifies two program judgments, it cannot
identify different occurrences from the same source event context. -/
theorem pushSlot_injective (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A)) (judgment : Judgment A) :
    Function.Injective (pushSlot R h Γ (judgment := judgment)) := by
  intro first second same
  rcases first with ⟨firstPosition, ⟨firstEqual⟩⟩
  rcases second with ⟨secondPosition, ⟨secondEqual⟩⟩
  have positions : firstPosition = secondPosition :=
    congrArg Sigma.fst same
  cases positions
  rfl

/-- Translate an authored firing term together with the event variables
already in its finite context. The rule map preserves premise positions. -/
noncomputable def mapTerm (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A)) (judgment : Judgment A) :
    IndexedRuleFiniteContexts.Term (rules R A) (toContext (rules R A) Γ) judgment →
      IndexedRuleFiniteContexts.Term (rules R B)
        (toContext (rules R B) (pushContext R h Γ))
        (mapJudgment h judgment) :=
  mapFreeWithEvents R h (fun _ slot => pushSlot R h Γ slot) judgment

/-- A pre-existing event variable is transported to its same position,
without becoming a generated rule firing. -/
theorem mapTerm_pure (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A)) {judgment : Judgment A}
    (slot : (toContext (rules R A) Γ).slots judgment) :
    mapTerm R h Γ judgment
        (IndexedPolynomial.Free.pure (rules R A) slot) =
      IndexedPolynomial.Free.pure (rules R B) (pushSlot R h Γ slot) :=
  mapFreeWithEvents_existing R h
    (fun _ slot => pushSlot R h Γ slot) slot

/-- An authored constructor is translated as that same rule occurrence,
with each child transported at its binder-extended judgment. -/
theorem mapTerm_node (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A)) {judgment : Judgment A}
    (shape : (rules R A).Shape PUnit.unit judgment)
    (children : ∀ position,
      IndexedRuleFiniteContexts.Term (rules R A) (toContext (rules R A) Γ)
        ((rules R A).next shape position)) :
    mapTerm R h Γ judgment
        (IndexedPolynomial.Free.node (rules R A) shape children) =
      IndexedPolynomial.Free.node (rules R B)
        ((presentationMap R h).rules.onShape PUnit.unit judgment shape)
        (fun position =>
          ((presentationMap R h).rules.onNext PUnit.unit judgment shape position).symm ▸
            mapTerm R h Γ _
              (children (((presentationMap R h).rules.onPosition
                PUnit.unit judgment shape) position))) :=
  mapFree_node (presentationMap R h).rules
    (fun _ _ slot => pushSlot R h Γ slot) shape children

/-- Changing the binding model in two stages gives the same translation of
every complete authored firing tree as changing it in one stage. -/
theorem mapTerm_comp_base {C : BindingCloneAlgebra.Algebra.{0} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C)
    (Γ : ListContext (rules R A)) (judgment : Judgment A)
    (tree : IndexedRuleFiniteContexts.Term (rules R A)
      (toContext (rules R A) Γ) judgment) :
    mapTerm R (FreeBindingClone.Hom.comp first second) Γ judgment tree =
      mapTerm R second (pushContext R first Γ) _
        (mapTerm R first Γ judgment tree) := by
  have leafEq :
      (fun (_ : Unit) index slot =>
        pushSlot R (FreeBindingClone.Hom.comp first second) Γ
          (judgment := index) slot) =
      (fun (_ : Unit) index slot =>
        pushSlot R second (pushContext R first Γ)
          (pushSlot R first Γ (judgment := index) slot)) := by
    funext _ index slot
    rcases slot with ⟨position, ⟨equal⟩⟩
    cases equal
    rfl
  unfold mapTerm mapFreeWithEvents
  conv_lhs =>
    change mapFree
      (IndexedRulePolynomialMorphisms.Hom.comp
        (presentationMap R first).rules
        (presentationMap R second).rules)
      (fun _ _ slot => pushSlot R (FreeBindingClone.Hom.comp first second) Γ slot)
      PUnit.unit judgment tree
  exact (congrArg
    (fun leaf => mapFree
      (IndexedRulePolynomialMorphisms.Hom.comp
        (presentationMap R first).rules
        (presentationMap R second).rules)
      leaf PUnit.unit judgment tree) leafEq).trans
    (mapFree_comp
      (presentationMap R first).rules
      (presentationMap R second).rules
      (fun _ _ slot => pushSlot R first Γ slot)
      (fun _ _ slot => pushSlot R second (pushContext R first Γ) slot)
      PUnit.unit judgment tree)

/-- Identity change of the binding model leaves complete firing trees and
their ordered event leaves unchanged. -/
theorem mapTerm_id (A : BindingCloneAlgebra.Algebra.{0} S)
    (Γ : ListContext (rules R A)) (judgment : Judgment A)
    (tree : IndexedRuleFiniteContexts.Term (rules R A)
      (toContext (rules R A) Γ) judgment) :
    mapTerm R (FreeBindingClone.Hom.id A) Γ judgment tree = tree := by
  have leafEq :
      (fun (_ : Unit) index slot =>
        pushSlot R (FreeBindingClone.Hom.id A) Γ (judgment := index) slot) =
      (fun (_ : Unit) (_ : Judgment A) slot => slot) := by
    funext _ index slot
    rcases slot with ⟨position, ⟨equal⟩⟩
    cases equal
    rfl
  unfold mapTerm mapFreeWithEvents
  conv_lhs =>
    change IndexedRuleFreeTransport.mapFree
      (IndexedRulePolynomialMorphisms.Hom.id (rules R A))
      (fun _ _ slot => pushSlot R (FreeBindingClone.Hom.id A) Γ slot)
      PUnit.unit judgment tree
  exact (congrArg
    (fun leaf => IndexedRuleFreeTransport.mapFree
      (IndexedRulePolynomialMorphisms.Hom.id (rules R A))
      leaf PUnit.unit judgment tree) leafEq).trans
    (IndexedRuleFreeTransport.mapFree_id
      (rules R A) (fun _ index => (toContext (rules R A) Γ).slots index)
      PUnit.unit judgment tree)

/-- Transport a simultaneous event substitution along a binding-model map.
The target variable retains its original finite-list position, so even a
noninjective map of program judgments never has to invent a preimage. -/
noncomputable def pushSubstitution (h : FreeBindingClone.Hom A B)
    {Γ Δ : ListContext (rules R A)}
    (σ : Γ ⟶ Δ) : pushContext R h Γ ⟶ pushContext R h Δ :=
  fun _ => fun
    | ⟨position, ⟨equal⟩⟩ =>
        equal ▸ mapTerm R h Γ (Δ.label position)
          (σ (Δ.label position) ⟨position, ⟨rfl⟩⟩)

/-- Every original event variable maps to its assigned translated tree. -/
theorem pushSubstitution_slot (h : FreeBindingClone.Hom A B)
    {Γ Δ : ListContext (rules R A)} (σ : Γ ⟶ Δ)
    (position : Fin Δ.length) :
    pushSubstitution R h σ _ ⟨position, ⟨rfl⟩⟩ =
      mapTerm R h Γ _ (σ _ ⟨position, ⟨rfl⟩⟩) := rfl

/-- The event-substitution action also composes across two successive
changes of binding model. -/
theorem pushSubstitution_comp_base {C : BindingCloneAlgebra.Algebra.{0} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C)
    {Γ Δ : ListContext (rules R A)} (σ : Γ ⟶ Δ) :
    pushSubstitution R (FreeBindingClone.Hom.comp first second) σ =
      pushSubstitution R second (pushSubstitution R first σ) := by
  funext judgment slot
  rcases slot with ⟨position, ⟨equal⟩⟩
  cases equal
  change mapTerm R (FreeBindingClone.Hom.comp first second) Γ _
      (σ _ ⟨position, ⟨rfl⟩⟩) =
    mapTerm R second (pushContext R first Γ) _
      (mapTerm R first Γ _ (σ _ ⟨position, ⟨rfl⟩⟩))
  exact mapTerm_comp_base R first second Γ _ _

/-- Identity change of the binding model leaves each simultaneous event
substitution unchanged. -/
theorem pushSubstitution_id_base (A : BindingCloneAlgebra.Algebra.{0} S)
    {Γ Δ : ListContext (rules R A)} (σ : Γ ⟶ Δ) :
    pushSubstitution R (FreeBindingClone.Hom.id A) σ = σ := by
  funext judgment slot
  rcases slot with ⟨position, ⟨equal⟩⟩
  cases equal
  change mapTerm R (FreeBindingClone.Hom.id A) Γ _
      (σ _ ⟨position, ⟨rfl⟩⟩) = σ _ ⟨position, ⟨rfl⟩⟩
  exact mapTerm_id R A Γ _ _

/-- Translation of authored firing trees commutes with simultaneous
substitution of existing event variables. This supplies the composition
square for the finite operational contexts over changing program models. -/
theorem mapTerm_bind (h : FreeBindingClone.Hom A B)
    {Γ Δ : ListContext (rules R A)} (σ : Γ ⟶ Δ)
    (judgment : Judgment A)
    (tree : IndexedRuleFiniteContexts.Term (rules R A)
      (toContext (rules R A) Δ) judgment) :
    mapTerm R h Γ judgment
        (IndexedPolynomial.Free.bind (rules R A)
          (fun _ index seed => σ index seed) PUnit.unit judgment tree) =
      IndexedPolynomial.Free.bind (rules R B)
        (fun _ index seed => pushSubstitution R h σ index seed)
        PUnit.unit (mapJudgment h judgment)
        (mapTerm R h Δ judgment tree) := by
  apply mapFree_bind (presentationMap R h).rules
    (fun _ _ slot => pushSlot R h Δ slot)
    (fun _ _ slot => pushSlot R h Γ slot)
    (fun _ index seed => σ index seed)
    (fun _ index seed => pushSubstitution R h σ index seed)
  intro _ index seed
  rcases seed with ⟨position, ⟨equal⟩⟩
  cases equal
  rfl

/-- Reindexing preserves identity assignments of event variables. -/
theorem pushSubstitution_id (h : FreeBindingClone.Hom A B)
    (Γ : ListContext (rules R A)) :
    pushSubstitution R h (𝟙 Γ) = 𝟙 (pushContext R h Γ) := by
  funext judgment slot
  rcases slot with ⟨position, ⟨equal⟩⟩
  cases equal
  change mapTerm R h Γ _
      (IndexedPolynomial.Free.pure (rules R A) ⟨position, ⟨rfl⟩⟩) =
    IndexedPolynomial.Free.pure (rules R B) ⟨position, ⟨rfl⟩⟩
  exact (mapTerm_pure R h Γ
    (slot := ⟨position, ⟨rfl⟩⟩)).trans rfl

/-- Reindexing preserves composition of simultaneous event substitutions,
including substitutions whose trees contain ordered conditional-rule nodes. -/
theorem pushSubstitution_comp (h : FreeBindingClone.Hom A B)
    {Γ Δ Θ : ListContext (rules R A)} (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) :
    pushSubstitution R h (σ ≫ τ) =
      pushSubstitution R h σ ≫ pushSubstitution R h τ := by
  funext judgment slot
  rcases slot with ⟨position, ⟨equal⟩⟩
  cases equal
  change mapTerm R h Γ _
      (IndexedPolynomial.Free.bind (rules R A)
        (fun _ index seed => σ index seed) PUnit.unit _
        (τ _ ⟨position, ⟨rfl⟩⟩)) =
    IndexedPolynomial.Free.bind (rules R B)
      (fun _ index seed => pushSubstitution R h σ index seed)
      PUnit.unit _
      (mapTerm R h Δ _ (τ _ ⟨position, ⟨rfl⟩⟩))
  exact mapTerm_bind R h σ _ (τ _ ⟨position, ⟨rfl⟩⟩)

/-- Changing the binding-equation model acts functorially on the genuine
finite operational context category of authored firing-tree substitutions. -/
noncomputable def pushFunctor (h : FreeBindingClone.Hom A B) :
    ListContext (rules R A) ⥤ ListContext (rules R B) where
  obj := pushContext R h
  map := pushSubstitution R h
  map_id Γ := pushSubstitution_id R h Γ
  map_comp σ τ := pushSubstitution_comp R h σ τ

/-- Identity binding interpretation induces the identity operational
context functor. -/
theorem pushFunctor_id (A : BindingCloneAlgebra.Algebra.{0} S) :
    pushFunctor R (FreeBindingClone.Hom.id A) =
      𝟭 (ListContext (rules R A)) := by
  refine CategoryTheory.Functor.hext (fun Γ => rfl) ?_
  intro Γ Δ σ
  exact heq_of_eq (pushSubstitution_id_base R A σ)

/-- Successive binding interpretations induce the composite operational
context functor, including their actions on firing-tree substitutions. -/
theorem pushFunctor_comp {C : BindingCloneAlgebra.Algebra.{0} S}
    (first : FreeBindingClone.Hom A B)
    (second : FreeBindingClone.Hom B C) :
    pushFunctor R (FreeBindingClone.Hom.comp first second) =
      pushFunctor R first ⋙ pushFunctor R second := by
  refine CategoryTheory.Functor.hext (fun Γ => rfl) ?_
  intro Γ Δ σ
  exact heq_of_eq (pushSubstitution_comp_base R first second σ)

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalFiniteContextChange
