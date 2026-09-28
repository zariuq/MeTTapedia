import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPresheaf

/-!
# Event presheaves of arbitrary substitution-operational models

The free firing-tree model is one instance of a more general fact. Any
lawful substitution-operational model carries an individual-evidence
presheaf on the same clone context category as its program states. This
construction retains all evidence values and uses the model's actual
substitution action; it does not replace events by an endpoint predicate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))

/-- An individual piece of evidence at its sorted source and target terms. -/
abbrev ModelEvent {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (Γ : Ctx S) : Type u :=
  Σ sort : S.Srt,
    Σ pair : A.substitution.Carrier Γ sort ×
        A.substitution.Carrier Γ sort,
      Y.evidence.carrier () ⟨Γ, sort, pair⟩

/-- Reindex one retained event using the model's specified substitution
action on its evidence. -/
noncomputable def mapModelEvent
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    {X Z : Base A} (f : X ⟶ Z) :
    ModelEvent R Y X.unop.context → ModelEvent R Y Z.unop.context
  | ⟨sort, pair, evidence⟩ =>
      ⟨sort,
        (A.substitution.toClone.substitute pair.1 f.unop,
          A.substitution.toClone.substitute pair.2 f.unop),
        Y.act ⟨X.unop.context, sort, pair⟩ evidence
          (fromPositions X.unop.context f.unop)
          ⟨Z.unop.context, sort,
            (A.substitution.toClone.substitute pair.1 f.unop,
              A.substitution.toClone.substitute pair.2 f.unop)⟩ rfl⟩

/-- Reindexing an arbitrary retained event by identity does not change its
source, target, or individual evidence value. -/
theorem mapModelEvent_id
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (X : Base A)
    (event : ModelEvent R Y X.unop.context) :
    mapModelEvent R Y (𝟙 X) event = event := by
  rcases event with ⟨sort, ⟨source, target⟩, evidence⟩
  let j : Judgment A := ⟨X.unop.context, sort, (source, target)⟩
  have envEq : fromPositions X.unop.context (𝟙 X).unop =
      (fun _ v => A.substitution.injectVar v) := by
    funext s v
    exact fromPositions_ofEnvironment
      (fun _ v => A.substitution.injectVar v) v
  have targetEq :
      (⟨X.unop.context, sort,
        (A.substitution.toClone.substitute source (𝟙 X).unop,
          A.substitution.toClone.substitute target (𝟙 X).unop)⟩ :
        Judgment A) = j := by
    exact congrArg (fun pair => (⟨X.unop.context, sort, pair⟩ : Judgment A))
      (Prod.ext (A.substitution.toClone.substitute_projects source)
        (A.substitution.toClone.substitute_projects target))
  have hCong : HEq
      (Y.act j evidence (fromPositions X.unop.context (𝟙 X).unop)
        ⟨X.unop.context, sort,
          (A.substitution.toClone.substitute source (𝟙 X).unop,
            A.substitution.toClone.substitute target (𝟙 X).unop)⟩ rfl)
      (Y.act j evidence (fun _ v => A.substitution.injectVar v)
        j (substJudgment_identity j)) :=
    SubstitutionModel.act_heq R Y rfl HEq.rfl
      (heq_of_eq envEq) targetEq rfl (substJudgment_identity j)
  have hIdentity := Y.act_identity j evidence (substJudgment_identity j)
  dsimp only [mapModelEvent]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · exact Prod.ext
        (A.substitution.toClone.substitute_projects source)
        (A.substitution.toClone.substitute_projects target)
    · exact hCong.trans (heq_of_eq hIdentity)

/-- Reindexing retained evidence along two ambient substitutions agrees
with reindexing once along their composite. -/
theorem mapModelEvent_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A)
    {X V Z : Base A} (f : X ⟶ V) (g : V ⟶ Z)
    (event : ModelEvent R Y X.unop.context) :
    mapModelEvent R Y (f ≫ g) event =
      mapModelEvent R Y g (mapModelEvent R Y f event) := by
  rcases event with ⟨sort, ⟨source, target⟩, evidence⟩
  let j : Judgment A := ⟨X.unop.context, sort, (source, target)⟩
  let σ : Environment S A.substitution.Carrier
      X.unop.context V.unop.context := fromPositions X.unop.context f.unop
  let τ : Environment S A.substitution.Carrier
      V.unop.context Z.unop.context := fromPositions V.unop.context g.unop
  let ρ : Environment S A.substitution.Carrier
      X.unop.context Z.unop.context :=
    fromPositions X.unop.context (f ≫ g).unop
  have envEq : ρ =
      (fun s v => A.substitution.substitute τ (σ s v)) := by
    funext s v
    exact fromPositions_substitute A.substitution f.unop
      (fromPositions V.unop.context g.unop) v
  have judgedEq : substJudgment j ρ =
      substJudgment j
        (fun s v => A.substitution.substitute τ (σ s v)) :=
    congrArg (substJudgment j) envEq
  have twiceEq : substJudgment (substJudgment j σ) τ =
      substJudgment j
        (fun s v => A.substitution.substitute τ (σ s v)) :=
    substJudgment_comp j σ τ
  have directToComp : HEq
      (Y.act j evidence ρ (substJudgment j ρ) rfl)
      (Y.act j evidence
        (fun s v => A.substitution.substitute τ (σ s v))
        (substJudgment j
          (fun s v => A.substitution.substitute τ (σ s v))) rfl) :=
    SubstitutionModel.act_heq R Y rfl HEq.rfl
      (heq_of_eq envEq) judgedEq rfl rfl
  have rightToComp : HEq
      (Y.act (substJudgment j σ)
        (Y.act j evidence σ (substJudgment j σ) rfl)
        τ (substJudgment (substJudgment j σ) τ) rfl)
      (Y.act (substJudgment j σ)
        (Y.act j evidence σ (substJudgment j σ) rfl)
        τ (substJudgment j
          (fun s v => A.substitution.substitute τ (σ s v))) twiceEq) :=
    SubstitutionModel.act_heq R Y rfl HEq.rfl HEq.rfl
      twiceEq rfl twiceEq
  have twiceIsComp := Y.act_comp j evidence σ τ
    (substJudgment j
      (fun s v => A.substitution.substitute τ (σ s v)))
    twiceEq rfl
  dsimp only [mapModelEvent]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · exact Prod.ext
        (A.substitution.toClone.substitute_assoc source f.unop g.unop).symm
        (A.substitution.toClone.substitute_assoc target f.unop g.unop).symm
    · exact directToComp.trans
        ((heq_of_eq twiceIsComp.symm).trans rightToComp.symm)

/-- The evidence of any lawful substitution-operational model forms a
presheaf over precisely the same contextual substitutions as programs. -/
noncomputable def modelEvents
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) : Base A ⥤ Type u where
  obj X := ModelEvent R Y X.unop.context
  map f := TypeCat.ofHom (mapModelEvent R Y f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact mapModelEvent_id R Y X event
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact mapModelEvent_comp R Y f g event

/-- The source endpoint remains a natural map of contextual states. -/
def modelSource
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) :
    modelEvents R Y ⟶ states A where
  app X := TypeCat.ofHom (fun event => ⟨event.1, event.2.1.1⟩)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨first, last⟩, evidence⟩
    rfl

/-- The target endpoint remains natural without forgetting the event. -/
def modelTarget
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) :
    modelEvents R Y ⟶ states A where
  app X := TypeCat.ofHom (fun event => ⟨event.1, event.2.1.2⟩)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨first, last⟩, evidence⟩
    rfl

/-- The general model graph retains every individual piece of operational
evidence together with its two natural endpoint maps. -/
noncomputable def modelGraph
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) :
    FreePresheafEventExtension.Graph (states A) where
  edge := modelEvents R Y
  source := modelSource R Y
  target := modelTarget R Y

/-- A morphism of substitution-operational models maps each retained event
to its interpreted evidence at the same sorted endpoints. -/
def mapModelEvents
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    modelEvents R Y ⟶ modelEvents R Z where
  app X := TypeCat.ofHom (fun event =>
    ⟨event.1, event.2.1,
      h.evidence.toFun ()
        ⟨X.unop.context, event.1, event.2.1⟩ event.2.2⟩)
  naturality X W f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨first, last⟩, evidence⟩
    let pair : A.substitution.Carrier W.unop.context sort ×
        A.substitution.Carrier W.unop.context sort :=
      (A.substitution.toClone.substitute first f.unop,
        A.substitution.toClone.substitute last f.unop)
    let jSource : Judgment A :=
      ⟨X.unop.context, sort, (first, last)⟩
    let jTarget : Judgment A := ⟨W.unop.context, sort, pair⟩
    have hPreserves := h.preserves jSource evidence
      (fromPositions X.unop.context f.unop) jTarget rfl
    change (⟨sort, pair,
        h.evidence.toFun () jTarget
          (Y.act jSource evidence
            (fromPositions X.unop.context f.unop) jTarget rfl)⟩ :
          ModelEvent R Z W.unop.context) =
      (⟨sort, pair,
        Z.act jSource (h.evidence.toFun () jSource evidence)
          (fromPositions X.unop.context f.unop) jTarget rfl⟩ :
          ModelEvent R Z W.unop.context)
    exact congrArg
      (fun value : Z.evidence.carrier () jTarget =>
        (⟨sort, pair, value⟩ : ModelEvent R Z W.unop.context))
      hPreserves

/-- Every lawful model map preserves both endpoint maps while retaining
its individual evidence map. -/
def mapModelGraph
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    modelGraph R Y ⟶ modelGraph R Z where
  edgeMap := mapModelEvents R h
  source_comm := by
    ext X event
    rfl
  target_comm := by
    ext X event
    rfl

/-- The graph construction is functorial on genuine evidence-preserving
model maps, with no extra target coverage or injectivity condition. -/
noncomputable def modelGraphFunctor
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    SubstitutionModel R A ⥤
      FreePresheafEventExtension.Graph (states A) where
  obj Y := modelGraph R Y
  map h := mapModelGraph R h
  map_id Y := by
    apply FreePresheafEventExtension.Hom.ext
    ext X event
    rfl
  map_comp f g := by
    apply FreePresheafEventExtension.Hom.ext
    ext X event
    rfl

/-- The endpoint predicate is a separate image observation of the event
graph. This image exists in the concrete presheaf model; no image structure
is claimed for an arbitrary finitely complete target. -/
noncomputable def modelReduction
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) :
    Subfunctor (FunctorToTypes.prod (states A) (states A)) :=
  FreePresheafEventImage.endpointImage (modelGraph R Y)

/-- The observed one-step relation holds exactly when the model retains
some evidence at that sorted pair of program endpoints. -/
theorem mem_modelReduction_iff
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : SubstitutionModel R A) (X : Base A)
    (sort : S.Srt)
    (first last : A.substitution.Carrier X.unop.context sort) :
    ((⟨sort, first⟩, ⟨sort, last⟩) :
      (states A).obj X × (states A).obj X) ∈
        (modelReduction R Y).obj X ↔
      Nonempty (Y.evidence.carrier ()
        (⟨X.unop.context, sort, (first, last)⟩ : Judgment A)) := by
  change (∃ event : ModelEvent R Y X.unop.context,
    ((modelSource R Y).app X event,
      (modelTarget R Y).app X event) =
      (⟨sort, first⟩, ⟨sort, last⟩)) ↔ _
  constructor
  · rintro ⟨⟨eventSort, ⟨sourceTerm, targetTerm⟩, evidence⟩,
      endpointsEq⟩
    have sourceEq := congrArg Prod.fst endpointsEq
    have targetEq := congrArg Prod.snd endpointsEq
    have sortEq : eventSort = sort := congrArg Sigma.fst sourceEq
    subst eventSort
    change (⟨sort, sourceTerm⟩ : (states A).obj X) =
      ⟨sort, first⟩ at sourceEq
    change (⟨sort, targetTerm⟩ : (states A).obj X) =
      ⟨sort, last⟩ at targetEq
    have firstEq : sourceTerm = first :=
      eq_of_heq (Sigma.mk.inj_iff.mp sourceEq).2
    have lastEq : targetTerm = last :=
      eq_of_heq (Sigma.mk.inj_iff.mp targetEq).2
    subst firstEq
    subst lastEq
    exact ⟨evidence⟩
  · rintro ⟨evidence⟩
    exact ⟨⟨sort, (first, last), evidence⟩, rfl⟩

/-- Every ordinary model interpretation preserves the one-step existence
predicate in the forward direction. It need not cover additional target
events or reflect reductions. -/
theorem modelReduction_le
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    modelReduction R Y ≤ modelReduction R Z := by
  intro X pair membership
  rcases membership with ⟨event, endpointEq⟩
  refine ⟨((mapModelEvents R h).app X) event, ?_⟩
  change (((modelSource R Z).app X)
      (((mapModelEvents R h).app X) event),
      ((modelTarget R Z).app X)
        (((mapModelEvents R h).app X) event)) = pair
  have hEndpoint :
      (((modelSource R Z).app X)
        (((mapModelEvents R h).app X) event),
        ((modelTarget R Z).app X)
          (((mapModelEvents R h).app X) event)) =
      (((modelSource R Y).app X) event,
        ((modelTarget R Y).app X) event) := rfl
  exact hEndpoint.trans endpointEq

/-- The model-level event construction specializes exactly to the already
established free firing-tree presheaf. -/
theorem free_modelEvents_eq
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    modelEvents R (SubstitutionModel.free R A) = events R A := rfl

theorem free_modelGraph_eq
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    modelGraph R (SubstitutionModel.free R A) = graph R A := rfl

theorem free_modelReduction_eq
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    modelReduction R (SubstitutionModel.free R A) = reduction R A := rfl

#print axioms modelEvents
#print axioms modelGraph
#print axioms mem_modelReduction_iff
#print axioms mapModelGraph
#print axioms modelGraphFunctor
#print axioms modelReduction_le
#print axioms free_modelEvents_eq
#print axioms free_modelReduction_eq

end Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
