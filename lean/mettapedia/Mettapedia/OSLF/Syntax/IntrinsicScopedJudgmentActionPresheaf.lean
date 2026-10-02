import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalPresheaf

/-!
# Retained evidence presheaves of contextual substitution actions

A judgment-indexed carrier with its actual substitution action determines an
event presheaf independently of a rule telescope. Its endpoint image records
existence of evidence; it retains no multiplicity information. Evidence and
programs may occupy different universes, in which case states are explicitly
lifted before forming a graph in the common presheaf universe.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentActionPresheaf

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf (Base states)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentAction (JudgmentAction)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

universe u w
variable {S : Signature}

/-- An individual piece of evidence at its sorted source and target terms. -/
abbrev Event {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) (Γ : Ctx S) : Type (max u w) :=
  Σ sort : S.Srt,
    Σ pair : A.substitution.Carrier Γ sort ×
        A.substitution.Carrier Γ sort,
      Y.carrier ⟨Γ, sort, pair⟩

/-- Reindex one retained event using the specified substitution
action on its evidence. -/
noncomputable def mapEvent
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A)
    {X Z : Base A} (f : X ⟶ Z) :
    Event Y X.unop.context → Event Y Z.unop.context
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
theorem mapEvent_id
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) (X : Base A)
    (event : Event Y X.unop.context) :
    mapEvent Y (𝟙 X) event = event := by
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
    Y.act_heq rfl HEq.rfl
      (heq_of_eq envEq) targetEq rfl (substJudgment_identity j)
  have hIdentity := Y.act_identity j evidence (substJudgment_identity j)
  dsimp only [mapEvent]
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
theorem mapEvent_comp
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A)
    {X V Z : Base A} (f : X ⟶ V) (g : V ⟶ Z)
    (event : Event Y X.unop.context) :
    mapEvent Y (f ≫ g) event =
      mapEvent Y g (mapEvent Y f event) := by
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
    Y.act_heq rfl HEq.rfl
      (heq_of_eq envEq) judgedEq rfl rfl
  have rightToComp : HEq
      (Y.act (substJudgment j σ)
        (Y.act j evidence σ (substJudgment j σ) rfl)
        τ (substJudgment (substJudgment j σ) τ) rfl)
      (Y.act (substJudgment j σ)
        (Y.act j evidence σ (substJudgment j σ) rfl)
        τ (substJudgment j
          (fun s v => A.substitution.substitute τ (σ s v))) twiceEq) :=
    Y.act_heq rfl HEq.rfl HEq.rfl
      twiceEq rfl twiceEq
  have twiceIsComp := Y.act_comp j evidence σ τ
    (substJudgment j
      (fun s v => A.substitution.substitute τ (σ s v)))
    twiceEq rfl
  dsimp only [mapEvent]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Sigma.ext
    · exact Prod.ext
        (A.substitution.toClone.substitute_assoc source f.unop g.unop).symm
        (A.substitution.toClone.substitute_assoc target f.unop g.unop).symm
    · exact directToComp.trans
        ((heq_of_eq twiceIsComp.symm).trans rightToComp.symm)

/-- The evidence of any lawful judgment action forms a
presheaf over precisely the same contextual substitutions as programs. -/
noncomputable def events
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) : Base A ⥤ Type (max u w) where
  obj X := Event Y X.unop.context
  map f := TypeCat.ofHom (mapEvent Y f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro event
    exact mapEvent_id Y X event
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro event
    exact mapEvent_comp Y f g event

/-- The source endpoint remains a natural map of contextual states. -/
def source
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, u} A) :
    events Y ⟶ states A where
  app X := TypeCat.ofHom (fun event => ⟨event.1, event.2.1.1⟩)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨first, last⟩, evidence⟩
    rfl

/-- The target endpoint remains natural without forgetting the event. -/
def target
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, u} A) :
    events Y ⟶ states A where
  app X := TypeCat.ofHom (fun event => ⟨event.1, event.2.1.2⟩)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨first, last⟩, evidence⟩
    rfl

/-- The general model graph retains every individual piece of operational
evidence together with its two natural endpoint maps. -/
noncomputable def graph
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, u} A) :
    FreePresheafEventExtension.Graph (states A) where
  edge := events Y
  source := source Y
  target := target Y


/-- Raise the state presheaf to the common universe of programs and evidence. -/
def liftedStates (A : BindingCloneAlgebra.Algebra.{u} S) :
    Base A ⥤ Type (max u w) :=
  states A ⋙ uliftFunctor.{w, u}

/-- The source of a retained event in the common universe. -/
def liftedSource {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) : events Y ⟶ liftedStates.{u, w} A where
  app X := TypeCat.ofHom (fun event => ULift.up ⟨event.1, event.2.1.1⟩)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨first, last⟩, evidence⟩
    rfl

/-- The target of a retained event in the common universe. -/
def liftedTarget {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) : events Y ⟶ liftedStates.{u, w} A where
  app X := TypeCat.ofHom (fun event => ULift.up ⟨event.1, event.2.1.2⟩)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨first, last⟩, evidence⟩
    rfl

/-- The retained graph for evidence in an arbitrary universe. -/
noncomputable def liftedGraph {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) :
    FreePresheafEventExtension.Graph (liftedStates.{u, w} A) where
  edge := events Y
  source := liftedSource Y
  target := liftedTarget Y

/-- At matching universes the explicit state lift is naturally isomorphic
to the original state presheaf. -/
def liftedStatesIso (A : BindingCloneAlgebra.Algebra.{u} S) :
    liftedStates.{u, u} A ≅ states A where
  hom := {
    app X := TypeCat.ofHom ULift.down
    naturality X Z f := by
      apply ConcreteCategory.hom_ext
      intro state
      rfl }
  inv := {
    app X := TypeCat.ofHom ULift.up
    naturality X Z f := by
      apply ConcreteCategory.hom_ext
      intro state
      rfl }
  hom_inv_id := by
    ext X state
    cases state
    rfl
  inv_hom_id := by
    ext X state
    rfl

/-- Lowering the explicit universe lift preserves the natural source map. -/
theorem liftedSource_statesIso {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, u} A) :
    liftedSource Y ≫ (liftedStatesIso A).hom = source Y := by
  ext X event
  rfl

/-- Lowering the explicit universe lift preserves the natural target map. -/
theorem liftedTarget_statesIso {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, u} A) :
    liftedTarget Y ≫ (liftedStatesIso A).hom = target Y := by
  ext X event
  rfl

/-- The endpoint pair forgets the evidence value but retains both sorted terms. -/
def endpointPair {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) {Γ : Ctx S} (event : Event Y Γ) :
    (Σ s : S.Srt, A.substitution.Carrier Γ s) ×
      (Σ s : S.Srt, A.substitution.Carrier Γ s) :=
  (⟨event.1, event.2.1.1⟩, ⟨event.1, event.2.1.2⟩)

/-- At every ordinary context, an endpoint pair has a retained witness
exactly when its indexed evidence carrier is inhabited. -/
theorem endpoint_fiber_iff {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) (Γ : Ctx S) (sort : S.Srt)
    (first last : A.substitution.Carrier Γ sort) :
    (∃ event : Event Y Γ,
      endpointPair Y event = (⟨sort, first⟩, ⟨sort, last⟩)) ↔
      Nonempty (Y.carrier (⟨Γ, sort, (first, last)⟩ : Judgment A)) := by
  constructor
  · rintro ⟨⟨eventSort, ⟨sourceTerm, targetTerm⟩, evidence⟩, endpointsEq⟩
    have sourceEq := congrArg Prod.fst endpointsEq
    have targetEq := congrArg Prod.snd endpointsEq
    have sortEq : eventSort = sort := congrArg Sigma.fst sourceEq
    subst eventSort
    change (⟨sort, sourceTerm⟩ : Σ s, A.substitution.Carrier Γ s) =
      ⟨sort, first⟩ at sourceEq
    change (⟨sort, targetTerm⟩ : Σ s, A.substitution.Carrier Γ s) =
      ⟨sort, last⟩ at targetEq
    have firstEq : sourceTerm = first := eq_of_heq (Sigma.mk.inj_iff.mp sourceEq).2
    have lastEq : targetTerm = last := eq_of_heq (Sigma.mk.inj_iff.mp targetEq).2
    subst firstEq
    subst lastEq
    exact ⟨evidence⟩
  · rintro ⟨evidence⟩
    exact ⟨⟨sort, (first, last), evidence⟩, rfl⟩

/-- The reduction observation at matching universes is the actual endpoint image. -/
noncomputable def reduction {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, u} A) :
    Subfunctor (FunctorToTypes.prod (states A) (states A)) :=
  FreePresheafEventImage.endpointImage (graph Y)

/-- Sections of the reduction image are exactly retained indexed witnesses. -/
theorem mem_reduction_iff {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, u} A) (X : Base A) (sort : S.Srt)
    (first last : A.substitution.Carrier X.unop.context sort) :
    ((⟨sort, first⟩, ⟨sort, last⟩) : (states A).obj X × (states A).obj X) ∈
        (reduction Y).obj X ↔
      Nonempty (Y.carrier ⟨X.unop.context, sort, (first, last)⟩) :=
  endpoint_fiber_iff Y X.unop.context sort first last

/-- The endpoint image in the common universe for arbitrary evidence. -/
noncomputable def liftedReduction {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) :
    Subfunctor (FunctorToTypes.prod (liftedStates.{u, w} A) (liftedStates.{u, w} A)) :=
  FreePresheafEventImage.endpointImage (liftedGraph Y)

/-- Raising the state universe leaves existence of retained evidence unchanged. -/
theorem mem_liftedReduction_iff {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) (X : Base A) (sort : S.Srt)
    (first last : A.substitution.Carrier X.unop.context sort) :
    ((ULift.up ⟨sort, first⟩, ULift.up ⟨sort, last⟩) :
      (liftedStates.{u, w} A).obj X × (liftedStates.{u, w} A).obj X) ∈
        (liftedReduction Y).obj X ↔
      Nonempty (Y.carrier ⟨X.unop.context, sort, (first, last)⟩) := by
  change (∃ event : Event Y X.unop.context,
    (ULift.up (endpointPair Y event).1, ULift.up (endpointPair Y event).2) =
      (ULift.up ⟨sort, first⟩, ULift.up ⟨sort, last⟩)) ↔ _
  constructor
  · rintro ⟨event, equal⟩
    apply (endpoint_fiber_iff Y X.unop.context sort first last).mp
    exact ⟨event, Prod.ext
      (congrArg ULift.down (congrArg Prod.fst equal))
      (congrArg ULift.down (congrArg Prod.snd equal))⟩
  · intro inhabited
    rcases (endpoint_fiber_iff Y X.unop.context sort first last).mpr inhabited with ⟨event, equal⟩
    exact ⟨event, congrArg (fun pair => (ULift.up pair.1, ULift.up pair.2)) equal⟩

/-- An endpoint predicate cannot distinguish two actual evidence values
at the same judgment. -/
theorem endpointPair_not_injective_of_distinct_evidence
    {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y : JudgmentAction.{u, w} A) (Γ : Ctx S) (sort : S.Srt)
    (first last : A.substitution.Carrier Γ sort)
    (one two : Y.carrier ⟨Γ, sort, (first, last)⟩) (distinct : one ≠ two) :
    ¬ Function.Injective (fun event : Event Y Γ => endpointPair Y event) := by
  intro injective
  have eventsEqual := injective
    (a₁ := (⟨sort, (first, last), one⟩ : Event Y Γ))
    (a₂ := (⟨sort, (first, last), two⟩ : Event Y Γ)) rfl
  have pairsEqual := eq_of_heq (Sigma.mk.inj_iff.mp eventsEqual).2
  exact distinct (eq_of_heq (Sigma.mk.inj_iff.mp pairsEqual).2)

/-- An indexed evidence map preserves the actual contextual action. -/
abbrev Preserves {A : BindingCloneAlgebra.Algebra.{u} S}
    (Y Z : JudgmentAction.{u, w} A)
    (f : ∀ j : Judgment A, Y.carrier j → Z.carrier j) : Prop :=
  ∀ (j : Judgment A) (value : Y.carrier j) {Δ : Ctx S}
    (σ : Environment S A.substitution.Carrier j.1 Δ)
    (result : Judgment A) (same : substJudgment j σ = result),
    f result (Y.act j value σ result same) = Z.act j (f j value) σ result same

/-- Every action-preserving evidence map is natural on retained events. -/
def mapEvents {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : JudgmentAction.{u, w} A}
    (f : ∀ j : Judgment A, Y.carrier j → Z.carrier j) (preserves : Preserves Y Z f) :
    events Y ⟶ events Z where
  app X := TypeCat.ofHom (fun event =>
    ⟨event.1, event.2.1, f ⟨X.unop.context, event.1, event.2.1⟩ event.2.2⟩)
  naturality X W arrow := by
    apply ConcreteCategory.hom_ext
    rintro ⟨sort, ⟨first, last⟩, evidence⟩
    let pair : A.substitution.Carrier W.unop.context sort ×
        A.substitution.Carrier W.unop.context sort :=
      (A.substitution.toClone.substitute first arrow.unop,
        A.substitution.toClone.substitute last arrow.unop)
    let jSource : Judgment A := ⟨X.unop.context, sort, (first, last)⟩
    let jTarget : Judgment A := ⟨W.unop.context, sort, pair⟩
    have hPreserves := preserves jSource evidence
      (fromPositions X.unop.context arrow.unop) jTarget rfl
    change (⟨sort, pair, f jTarget
        (Y.act jSource evidence (fromPositions X.unop.context arrow.unop) jTarget rfl)⟩ :
          Event Z W.unop.context) =
      (⟨sort, pair, Z.act jSource (f jSource evidence)
        (fromPositions X.unop.context arrow.unop) jTarget rfl⟩ : Event Z W.unop.context)
    exact congrArg (fun value : Z.carrier jTarget =>
      (⟨sort, pair, value⟩ : Event Z W.unop.context)) hPreserves

/-- The natural event map preserves both endpoint maps in the common universe. -/
def mapLiftedGraph {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : JudgmentAction.{u, w} A}
    (f : ∀ j : Judgment A, Y.carrier j → Z.carrier j) (preserves : Preserves Y Z f) :
    liftedGraph Y ⟶ liftedGraph Z where
  edgeMap := mapEvents f preserves
  source_comm := by ext X event; rfl
  target_comm := by ext X event; rfl

/-- At matching universes the same evidence map is a map over the original states. -/
def mapGraph {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : JudgmentAction.{u, u} A}
    (f : ∀ j : Judgment A, Y.carrier j → Z.carrier j) (preserves : Preserves Y Z f) :
    graph Y ⟶ graph Z where
  edgeMap := mapEvents f preserves
  source_comm := by ext X event; rfl
  target_comm := by ext X event; rfl

/-- A retained-event graph map always preserves reduction support forward.
It need not cover new target events or reflect their endpoints. -/
theorem endpointImage_le_of_hom {C : Type*} [Category C] {vertex : C ⥤ Type*}
    {G H : FreePresheafEventExtension.Graph vertex} (h : G ⟶ H) :
    FreePresheafEventImage.endpointImage G ≤ FreePresheafEventImage.endpointImage H := by
  intro X pair membership
  rcases membership with ⟨event, equal⟩
  refine ⟨h.edgeMap.app X event, ?_⟩
  have sourceEq := ConcreteCategory.congr_hom (NatTrans.congr_app h.source_comm X) event
  have targetEq := ConcreteCategory.congr_hom (NatTrans.congr_app h.target_comm X) event
  exact (Prod.ext sourceEq targetEq).trans equal

/-- Actual target-event coverage suffices for reverse reduction support.
A telescope-forgetting comparison must establish this coverage, including
extension of local assignments at retained history nodes. Injectivity and
an inverse natural map are not required. -/
theorem endpointImage_eq_of_coverage {C : Type*} [Category C] {vertex : C ⥤ Type*}
    {G H : FreePresheafEventExtension.Graph vertex} (h : G ⟶ H)
    (coverage : ∀ X, Function.Surjective (h.edgeMap.app X)) :
    FreePresheafEventImage.endpointImage G = FreePresheafEventImage.endpointImage H := by
  apply le_antisymm (endpointImage_le_of_hom h)
  intro X pair membership
  rcases membership with ⟨event, equal⟩
  rcases coverage X event with ⟨original, rfl⟩
  refine ⟨original, ?_⟩
  have sourceEq := ConcreteCategory.congr_hom (NatTrans.congr_app h.source_comm X) original
  have targetEq := ConcreteCategory.congr_hom (NatTrans.congr_app h.target_comm X) original
  exact (Prod.ext sourceEq targetEq).symm.trans equal

/-- Indexed evidence coverage supplies the exact stagewise event coverage. -/
theorem mapEvents_surjective {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : JudgmentAction.{u, w} A}
    (f : ∀ j : Judgment A, Y.carrier j → Z.carrier j) (preserves : Preserves Y Z f)
    (coverage : ∀ j, Function.Surjective (f j)) (X : Base A) :
    Function.Surjective ((mapEvents f preserves).app X) := by
  rintro ⟨sort, pair, evidence⟩
  rcases coverage ⟨X.unop.context, sort, pair⟩ evidence with ⟨original, rfl⟩
  exact ⟨⟨sort, pair, original⟩, rfl⟩

/-- Actual evidence coverage gives equal endpoint images without giving an
event bijection or an inverse natural map. -/
theorem liftedReduction_eq_of_coverage {A : BindingCloneAlgebra.Algebra.{u} S}
    {Y Z : JudgmentAction.{u, w} A}
    (f : ∀ j : Judgment A, Y.carrier j → Z.carrier j) (preserves : Preserves Y Z f)
    (coverage : ∀ j, Function.Surjective (f j)) :
    liftedReduction Y = liftedReduction Z :=
  endpointImage_eq_of_coverage (mapLiftedGraph f preserves)
    (mapEvents_surjective f preserves coverage)

end Mettapedia.OSLF.Binding.IntrinsicScopedJudgmentActionPresheaf
