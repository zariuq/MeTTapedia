import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalActedFree
import Mettapedia.OSLF.Syntax.IndexedRuleFiniteListSkeleton
import Mettapedia.TypeTheory.IndexedPolynomialFreeMapInjective

/-!
# Substitution-closed event terms over an existing finite context

The finite context still enumerates bare event variables at exact judgments.
Its associated free terms also admit uses of those variables after ordinary
substitution. The comparison preserves every old rule node and leaf position.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedFiniteContext

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedFree
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open CategoryTheory
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton

variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable (A : BindingCloneAlgebra.Algebra.{0} S)

/-- Original event generators are the enumerated positions at their exact
judgments. -/
def seeds (Γ : ListContext (rules R A))
    (sort : S.Srt) (state : State A sort) : Type :=
  (toContext (rules R A) Γ).slots (state.asJudgment A)

/-- Event terms over a finite context, including substituted uses of its
variables and all authored rule constructors. -/
abbrev Term (Γ : ListContext (rules R A)) (judgment : Judgment A) : Type :=
  IntrinsicScopedConditionalActedFree.Tree R A (seeds R A Γ) judgment

/-- An old exact-judgment variable is an unchanged generator at the
identity substitution. -/
noncomputable def exactHole (Γ : ListContext (rules R A))
    {judgment : Judgment A}
    (slot : (toContext (rules R A) Γ).slots judgment) :
    Holes A (seeds R A Γ) judgment :=
  Orbit.unit A (seeds R A Γ)
    ((State.as_of A judgment).symm ▸ slot)

/-- The exact-leaf embedding does not identify different original event
positions at a fixed judgment. -/
theorem exactHole_injective (Γ : ListContext (rules R A))
    (judgment : Judgment A) :
    Function.Injective (exactHole R A Γ (judgment := judgment)) := by
  intro first second same
  unfold exactHole at same
  have castEq :
      ((State.as_of A judgment).symm ▸ first) =
        ((State.as_of A judgment).symm ▸ second) := by
    cases same
    rfl
  exact eq_of_heq ((heq_transport (State.as_of A judgment).symm first).symm.trans
    ((heq_of_eq castEq).trans
      (heq_transport (State.as_of A judgment).symm second)))

/-- Embed the previous rule-tree presentation into the
substitution-closed event syntax. -/
noncomputable def embed (Γ : ListContext (rules R A))
    (judgment : Judgment A) :
    IndexedRuleFiniteContexts.Term (rules R A)
      (toContext (rules R A) Γ) judgment →
      Term R A Γ judgment :=
  IndexedPolynomial.Free.map (rules R A)
    (fun _ _ slot => exactHole R A Γ slot) PUnit.unit judgment

/-- Embedding an old authored firing tree into the substitution-closed
syntax preserves the complete tree, including repeated event positions. -/
theorem embed_injective (Γ : ListContext (rules R A))
    (judgment : Judgment A) :
    Function.Injective (embed R A Γ judgment) :=
  IndexedPolynomial.Free.map_injective (rules R A)
    (fun _ _ slot => exactHole R A Γ slot)
    (fun _ index => exactHole_injective R A Γ index)
    PUnit.unit judgment

theorem embed_pure (Γ : ListContext (rules R A))
    {judgment : Judgment A}
    (slot : (toContext (rules R A) Γ).slots judgment) :
    embed R A Γ judgment
      (IndexedPolynomial.Free.pure (rules R A) slot) =
      IndexedPolynomial.Free.pure (rules R A)
        (exactHole R A Γ slot) := rfl

/-- An exact-position leaf of the old finite context is precisely the bare
generator of the new substitution-operational model. -/
theorem embed_exact_generator
    (Γ : ListContext (rules R A))
    {sort : S.Srt} (state : State A sort)
    (seed : seeds R A Γ sort state) :
    embed R A Γ (state.asJudgment A)
        (IndexedPolynomial.Free.pure (rules R A) seed) =
      generator R A (seeds R A Γ) seed := by
  cases state with
  | mk context source target => rfl

theorem embed_node (Γ : ListContext (rules R A))
    {judgment : Judgment A}
    (shape : Shape R A judgment)
    (children : ∀ position : Fin (R.get shape.1.index).premises.length,
      IndexedRuleFiniteContexts.Term (rules R A)
        (toContext (rules R A) Γ)
        (childJudgment R A shape.1 position)) :
    embed R A Γ judgment
      (IndexedPolynomial.Free.node (rules R A) shape children) =
      IndexedPolynomial.Free.node (rules R A) shape
        (fun position => embed R A Γ _ (children position)) := rfl

/-- Interpreting an old exact-leaf tree through the new syntax gives the
same recursive rule interpretation, with each old leaf read as its original
generator. No rule node or event position is changed by the embedding. -/
theorem interpret_embed
    (Γ : ListContext (rules R A))
    (model : SubstitutionModel R A)
    (assigned : ∀ sort (state : State A sort),
      seeds R A Γ sort state →
        model.evidence.carrier () (state.asJudgment A))
    (judgment : Judgment A)
    (tree : IndexedRuleFiniteContexts.Term (rules R A)
      (toContext (rules R A) Γ) judgment) :
    IntrinsicScopedConditionalActedFree.interpret R A (seeds R A Γ)
        model assigned judgment (embed R A Γ judgment tree) =
      IndexedPolynomial.Free.fold (rules R A)
        (fun _ j slot =>
          IntrinsicScopedConditionalActedFree.decodeHole R A
            (seeds R A Γ) model assigned j (exactHole R A Γ slot))
        model.evidence.rules PUnit.unit judgment tree := by
  unfold embed IntrinsicScopedConditionalActedFree.interpret
    IndexedPolynomial.Free.map
  rw [IndexedPolynomial.Free.fold_bind]
  rfl

/-- The exact-leaf embedding commutes with filling old event variables by
arbitrary old free rule trees. -/
theorem embed_bind
    {Γ Δ : ListContext (rules R A)}
    (fill : Γ ⟶ Δ)
    (judgment : Judgment A)
    (tree : IndexedRuleFiniteContexts.Term (rules R A)
      (toContext (rules R A) Δ) judgment) :
    embed R A Γ judgment
        (IndexedPolynomial.Free.bind (rules R A)
          (fun _ j slot => fill j slot) PUnit.unit judgment tree) =
      IndexedPolynomial.Free.fold (rules R A)
        (fun _ j slot => embed R A Γ j (fill j slot))
        (IndexedPolynomial.Free.algebra (rules R A))
        PUnit.unit judgment tree := by
  unfold embed IndexedPolynomial.Free.map
  change IndexedPolynomial.Free.bind (rules R A)
      (fun _ j slot => IndexedPolynomial.Free.pure (rules R A)
        (exactHole R A Γ slot)) PUnit.unit judgment
      (IndexedPolynomial.Free.bind (rules R A)
        (fun _ j slot => fill j slot) PUnit.unit judgment tree) =
    IndexedPolynomial.Free.bind (rules R A)
      (fun _ j slot => IndexedPolynomial.Free.bind (rules R A)
        (fun _ k old => IndexedPolynomial.Free.pure (rules R A)
          (exactHole R A Γ old)) PUnit.unit j (fill j slot))
      PUnit.unit judgment tree
  rw [IndexedPolynomial.Free.bind_assoc]

/-! ## Finite contexts and substitution-operational arrows -/

/-- A finite ordered list of bare event generators, distinguished from the
older rule-only context category by its richer arrow language. -/
structure Context where
  listed : ListContext (rules R A)

/-- An arrow assigns a substitution-closed free tree to each target event
variable at its original contextual judgment. -/
abbrev Hom (Γ Δ : Context R A) : Type :=
  ∀ sort (state : State A sort),
    seeds R A Δ.listed sort state →
      IntrinsicScopedConditionalActedFree.Tree R A
        (seeds R A Γ.listed) (state.asJudgment A)

/-- A context arrow extends uniquely to a map of free
substitution-operational models. -/
noncomputable def asModelHom {Γ Δ : Context R A}
    (f : Hom R A Γ Δ) :
    SubstitutionModel.Hom R
      (freeModel R A (seeds R A Δ.listed))
      (freeModel R A (seeds R A Γ.listed)) :=
  foldHom R A (seeds R A Δ.listed)
    (freeModel R A (seeds R A Γ.listed)) f

/-- Composition fills each target tree through the earlier arrow's unique
substitution-preserving extension. -/
noncomputable def Hom.comp {Γ Δ Θ : Context R A}
    (first : Hom R A Γ Δ) (second : Hom R A Δ Θ) :
    Hom R A Γ Θ :=
  fun _ state seed =>
    (asModelHom R A first).evidence.toFun ()
      (state.asJudgment A) (second _ state seed)

/-- Identity assigns each event variable to its bare generator. -/
noncomputable def Hom.id (Γ : Context R A) : Hom R A Γ Γ :=
  fun _ _ seed => generator R A (seeds R A Γ.listed) seed

theorem asModelHom_id (Γ : Context R A) :
    asModelHom R A (Hom.id R A Γ) =
      SubstitutionModel.Hom.id
        (freeModel R A (seeds R A Γ.listed)) := by
  have assigned : assignmentOfHom R A (seeds R A Γ.listed)
      (freeModel R A (seeds R A Γ.listed))
      (SubstitutionModel.Hom.id
        (freeModel R A (seeds R A Γ.listed))) =
      Hom.id R A Γ := by
    rfl
  rw [← assigned]
  exact foldHom_assignmentOfHom R A (seeds R A Γ.listed)
    (freeModel R A (seeds R A Γ.listed)) _

theorem asModelHom_comp {Γ Δ Θ : Context R A}
    (first : Hom R A Γ Δ) (second : Hom R A Δ Θ) :
    asModelHom R A (Hom.comp R A first second) =
      SubstitutionModel.Hom.comp
        (asModelHom R A second) (asModelHom R A first) := by
  have assigned : assignmentOfHom R A (seeds R A Θ.listed)
      (freeModel R A (seeds R A Γ.listed))
      (SubstitutionModel.Hom.comp
        (asModelHom R A second) (asModelHom R A first)) =
      Hom.comp R A first second := by
    funext sort state seed
    change (asModelHom R A first).evidence.toFun ()
        (state.asJudgment A)
        ((asModelHom R A second).evidence.toFun ()
          (state.asJudgment A)
          (generator R A (seeds R A Θ.listed) seed)) =
      (asModelHom R A first).evidence.toFun ()
        (state.asJudgment A) (second sort state seed)
    have generatorEq :
        (asModelHom R A second).evidence.toFun ()
            (state.asJudgment A)
            (generator R A (seeds R A Θ.listed) seed) =
          second sort state seed :=
      foldHom_generator R A (seeds R A Θ.listed)
        (freeModel R A (seeds R A Δ.listed)) second seed
    rw [generatorEq]
  rw [← assigned]
  exact foldHom_assignmentOfHom R A (seeds R A Θ.listed)
    (freeModel R A (seeds R A Γ.listed)) _

/-- Finite event contexts form a category. Its composition preserves the
contextual substitution action because it is induced by model morphisms. -/
noncomputable instance : Category (Context R A) where
  Hom := Hom R A
  id := Hom.id R A
  comp := Hom.comp R A
  id_comp := by
    intro Γ Δ f
    funext sort state seed
    change (asModelHom R A (Hom.id R A Γ)).evidence.toFun ()
        (state.asJudgment A) (f sort state seed) =
      f sort state seed
    rw [asModelHom_id]
    rfl
  comp_id := by
    intro Γ Δ f
    funext sort state seed
    change (asModelHom R A f).evidence.toFun ()
        (state.asJudgment A)
        (generator R A (seeds R A Δ.listed) seed) =
      f sort state seed
    exact foldHom_generator R A (seeds R A Δ.listed)
      (freeModel R A (seeds R A Γ.listed)) f seed
  assoc := by
    intro Γ Δ Θ Ψ first second third
    funext sort state seed
    change (asModelHom R A (Hom.comp R A first second)).evidence.toFun ()
        (state.asJudgment A) (third sort state seed) =
      (asModelHom R A first).evidence.toFun ()
        (state.asJudgment A)
        ((asModelHom R A second).evidence.toFun ()
          (state.asJudgment A) (third sort state seed))
    rw [asModelHom_comp]
    rfl

/-- Arrows of acted finite contexts are exactly maps between their free
substitution-operational models, in the opposite direction. -/
noncomputable def homEquiv (Γ Δ : Context R A) :
    (Γ ⟶ Δ) ≃
      SubstitutionModel.Hom R
        (freeModel R A (seeds R A Δ.listed))
        (freeModel R A (seeds R A Γ.listed)) :=
  freeModelUniversal R A (seeds R A Δ.listed)
    (freeModel R A (seeds R A Γ.listed))

/-- The acted context category embeds in the opposite category of free
substitution-operational models. -/
noncomputable def intoModels :
    Context R A ⥤ (SubstitutionModel R A)ᵒᵖ where
  obj Γ := Opposite.op (freeModel R A (seeds R A Γ.listed))
  map f := Quiver.Hom.op (asModelHom R A f)
  map_id Γ := by
    apply Quiver.Hom.unop_inj
    exact asModelHom_id R A Γ
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    exact asModelHom_comp R A f g

instance intoModels_full : (intoModels R A).Full where
  map_surjective := by
    intro Γ Δ mapped
    refine ⟨(homEquiv R A Γ Δ).symm mapped.unop, ?_⟩
    apply Quiver.Hom.unop_inj
    exact (homEquiv R A Γ Δ).apply_symm_apply mapped.unop

instance intoModels_faithful : (intoModels R A).Faithful where
  map_injective := by
    intro Γ Δ first second same
    have modelEq : asModelHom R A first = asModelHom R A second :=
      congrArg Quiver.Hom.unop same
    apply (homEquiv R A Γ Δ).injective
    exact modelEq

/-! ## Comparison with exact-leaf operational contexts -/

/-- An old exact-leaf substitution is also an acted-context arrow, by
embedding each assigned rule tree. -/
noncomputable def oldArrow
    {Γ Δ : ListContext (rules R A)} (f : Γ ⟶ Δ) :
    (⟨Γ⟩ : Context R A) ⟶ (⟨Δ⟩ : Context R A) :=
  fun _ state seed => embed R A Γ (state.asJudgment A)
    (f (state.asJudgment A) seed)

/-- Decoding one exact old leaf under an old arrow yields precisely the
embedded tree assigned to that old variable. -/
theorem decodeHole_exact
    {Γ Δ : ListContext (rules R A)} (f : Γ ⟶ Δ)
    (judgment : Judgment A)
    (slot : (toContext (rules R A) Δ).slots judgment) :
    IntrinsicScopedConditionalActedFree.decodeHole R A
        (seeds R A Δ)
        (freeModel R A (seeds R A Γ))
        (oldArrow R A f) judgment (exactHole R A Δ slot) =
      embed R A Γ judgment (f judgment slot) := by
  rcases judgment with ⟨context, sort, source, target⟩
  let state : State A sort := ⟨context, source, target⟩
  change (Orbit.unit A (seeds R A Δ) (state := state) slot).interpret
      A (seeds R A Δ) (freeModel R A (seeds R A Γ)).toAction
      (oldArrow R A f sort) =
    embed R A Γ ⟨context, sort, source, target⟩
      (f ⟨context, sort, source, target⟩ slot)
  exact Orbit.interpret_unit (state := state) A (seeds R A Δ)
    (freeModel R A (seeds R A Γ)).toAction (oldArrow R A f sort) slot

/-- The previous exact-leaf category maps into the substitution-closed
event context category without changing its event-variable positions. -/
noncomputable def oldFunctor :
    ListContext (rules R A) ⥤ Context R A where
  obj Γ := ⟨Γ⟩
  map f := oldArrow R A f
  map_id Γ := by
    funext sort state seed
    change embed R A Γ (state.asJudgment A)
        (IndexedPolynomial.Free.pure (rules R A) seed) =
      generator R A (seeds R A Γ) seed
    exact embed_exact_generator R A Γ state seed
  map_comp := by
    intro Γ Δ Θ first second
    funext sort state seed
    let judgment := state.asJudgment A
    let tree := second judgment seed
    change embed R A Γ judgment
        (IndexedPolynomial.Free.bind (rules R A)
          (fun _ j slot => first j slot) PUnit.unit judgment tree) =
      (asModelHom R A (oldArrow R A first)).evidence.toFun ()
        judgment (embed R A Δ judgment tree)
    rw [embed_bind R A first judgment tree]
    have leafEq :
        (fun (_ : Unit) j slot => embed R A Γ j (first j slot)) =
        (fun (_ : Unit) j slot =>
          IntrinsicScopedConditionalActedFree.decodeHole R A
            (seeds R A Δ)
            (freeModel R A (seeds R A Γ))
            (oldArrow R A first) j (exactHole R A Δ slot)) := by
      funext base j slot
      exact (decodeHole_exact R A first j slot).symm
    rw [leafEq]
    exact (interpret_embed R A Δ (freeModel R A (seeds R A Γ))
      (oldArrow R A first) judgment tree).symm

/-- The previous exact-leaf operational context category embeds
faithfully. Its arrows cannot collapse when substitution-closed event uses
are added. -/
instance oldFunctor_faithful : (oldFunctor R A).Faithful where
  map_injective := by
    intro Γ Δ first second same
    funext judgment slot
    rcases judgment with ⟨context, sort, source, target⟩
    let state : State A sort := ⟨context, source, target⟩
    have atSlot := congrArg
      (fun arrow : (⟨Γ⟩ : Context R A) ⟶ ⟨Δ⟩ =>
        arrow sort state slot) same
    change embed R A Γ (state.asJudgment A)
        (first (state.asJudgment A) slot) =
      embed R A Γ (state.asJudgment A)
        (second (state.asJudgment A) slot) at atSlot
    exact embed_injective R A Γ (state.asJudgment A) atSlot

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalActedFiniteContext
