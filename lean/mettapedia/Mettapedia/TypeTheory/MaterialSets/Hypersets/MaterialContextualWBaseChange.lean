import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWElimination
import Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledDependentProducts
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedUniverse

/-!
# Material contextual W base change

The native indexed comparison constructs both directions by induction and
retains every future arrow and dependent position. Here it connects the
actual material W decoders before and after context base change. Fresh
faithful context labels give an explicit representation equivalence, with
member, constructor, restriction and arbitrary natural-algebra fold laws.

An explicitly transported old graph gives a second interpretation whose
material values are preserved literally. That equality is a consequence of
the constructed W inverse; it is not asserted for arbitrary fresh labels.
All graph carriers remain at the original common graph bound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWBaseChange

open CategoryTheory
open ContextualWTypes (NaturalTree)
open PowerClassPresheafProducts (elementMap)
open ContextualWBaseChange

universe u

section Comparison

variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u} (change : NatTrans Q P)
variable (domain : P.Elements ⥤ Type u) (body : domain.Elements ⥤ Type u)
variable (worlds : ArgumentCoding P.Elements)
variable (arrows : (first second : P.Elements) → ArgumentCoding (first ⟶ second))
variable (shapes : (point : P.Elements) → PresentedType (domain.obj point))
variable (positions : (point : domain.Elements) → PresentedType (body.obj point))

abbrev targetModel (point : P.Elements) :=
  MaterialContextualWTypes.naturalModel domain body worlds arrows shapes positions point

abbrev TargetMembers (point : P.Elements) :=
  {value : HSet.{u} // value ∈ (targetModel domain body worlds arrows shapes positions point).carrier}

/-- The transported carrier uses the constructed indexed W inverse. -/
noncomputable def transportedModel (point : Q.Elements) :
    PresentedType (NaturalTree (sourceDomain change domain) (sourceBody change domain body) point) :=
  (targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).relabel
    (naturalEquiv change domain body point)

abbrev TransportedMembers (point : Q.Elements) :=
  {value : HSet.{u} // value ∈ (transportedModel change domain body worlds arrows shapes positions point).carrier}

theorem transported_value (point : Q.Elements)
    (tree : NaturalTree domain body ((elementMap change).obj point)) :
    (transportedModel change domain body worlds arrows shapes positions point).value
        (naturalEquiv change domain body point tree) =
      (targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).value tree := by
  exact (PresentedType.relabel_value _ _ _).trans
    (congrArg (targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).value
      ((naturalEquiv change domain body point).symm_apply_apply tree))

theorem transported_termGraph (point : Q.Elements)
    (tree : NaturalTree domain body ((elementMap change).obj point)) :
    HSet.mk ((transportedModel change domain body worlds arrows shapes positions point).termGraph
      (naturalEquiv change domain body point tree)) =
        HSet.mk ((targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).termGraph tree) :=
  (PresentedType.mk_termGraph _ _).trans ((transported_value change domain body worlds arrows shapes positions point tree).trans
    (PresentedType.mk_termGraph _ _).symm)

theorem transported_termGraph_eq (point : Q.Elements)
    (tree : NaturalTree domain body ((elementMap change).obj point)) :
    (transportedModel change domain body worlds arrows shapes positions point).termGraph
      (naturalEquiv change domain body point tree) =
    (targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).termGraph tree := by
  change (targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).termGraph
    ((naturalEquiv change domain body point).symm (naturalEquiv change domain body point tree)) = _
  exact congrArg (targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).termGraph
    ((naturalEquiv change domain body point).symm_apply_apply tree)

noncomputable def transportedMemberEquiv (point : Q.Elements) :
    TargetMembers domain body worlds arrows shapes positions ((elementMap change).obj point) ≃
      TransportedMembers change domain body worlds arrows shapes positions point :=
  (targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).decode.trans
    ((naturalEquiv change domain body point).trans
      (transportedModel change domain body worlds arrows shapes positions point).decode.symm)

theorem transported_member_value (point : Q.Elements)
    (member : TargetMembers domain body worlds arrows shapes positions ((elementMap change).obj point)) :
    (transportedMemberEquiv change domain body worlds arrows shapes positions point member).val = member.val :=
  (transported_value change domain body worlds arrows shapes positions point
    ((targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).decode member)).trans
      (PresentedType.value_decode _ _)

theorem transported_decode (point : Q.Elements)
    (member : TargetMembers domain body worlds arrows shapes positions ((elementMap change).obj point)) :
    (transportedModel change domain body worlds arrows shapes positions point).decode
      (transportedMemberEquiv change domain body worlds arrows shapes positions point member) =
        naturalEquiv change domain body point
          ((targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).decode member) :=
  Equiv.apply_symm_apply _ _

variable (sourceWorlds : ArgumentCoding Q.Elements)
variable (sourceArrows : (first second : Q.Elements) → ArgumentCoding (first ⟶ second))

abbrev sourceShapes (point : Q.Elements) := shapes ((elementMap change).obj point)
abbrev sourcePositions (point : (sourceDomain change domain).Elements) :=
  positions ((PowerClassPresheafBaseChange.Cat.elementsMap (elementMap change) domain).obj point)

/-- Fresh labels construct an independent material carrier and decoder. -/
abbrev sourceModel (point : Q.Elements) :=
  MaterialContextualWTypes.naturalModel (sourceDomain change domain) (sourceBody change domain body)
    sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions) point

abbrev SourceMembers (point : Q.Elements) :=
  {value : HSet.{u} // value ∈ (sourceModel change domain body shapes positions sourceWorlds sourceArrows point).carrier}

noncomputable def memberEquiv (point : Q.Elements) :
    TargetMembers domain body worlds arrows shapes positions ((elementMap change).obj point) ≃
      SourceMembers change domain body shapes positions sourceWorlds sourceArrows point :=
  (targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).decode.trans
    ((naturalEquiv change domain body point).trans
      (sourceModel change domain body shapes positions sourceWorlds sourceArrows point).decode.symm)

theorem decode_memberEquiv (point : Q.Elements)
    (member : TargetMembers domain body worlds arrows shapes positions ((elementMap change).obj point)) :
    (sourceModel change domain body shapes positions sourceWorlds sourceArrows point).decode
      (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows point member) =
        naturalEquiv change domain body point
          ((targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).decode member) :=
  Equiv.apply_symm_apply _ _

theorem memberEquiv_term (point : Q.Elements)
    (tree : NaturalTree domain body ((elementMap change).obj point)) :
    memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows point
      ((targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).decode.symm tree) =
        (sourceModel change domain body shapes positions sourceWorlds sourceArrows point).decode.symm
          (naturalEquiv change domain body point tree) := by
  exact congrArg (fun decoded =>
    (sourceModel change domain body shapes positions sourceWorlds sourceArrows point).decode.symm
      (naturalEquiv change domain body point decoded)) (Equiv.apply_symm_apply _ _)

theorem memberEquiv_restrict {X Y : Q.Elements} (arrow : X ⟶ Y)
    (member : TargetMembers domain body worlds arrows shapes positions ((elementMap change).obj X)) :
    memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows Y
      (MaterialContextualWTypes.naturalMap domain body worlds arrows shapes positions ((elementMap change).map arrow) member) =
    MaterialContextualWTypes.naturalMap (sourceDomain change domain) (sourceBody change domain body)
      sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions) arrow
        (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows X member) := by
  apply (sourceModel change domain body shapes positions sourceWorlds sourceArrows Y).decode.injective
  have first := MaterialContextualWTypes.naturalMap_decode domain body worlds arrows shapes positions
    ((elementMap change).map arrow) member
  have last := (MaterialContextualWTypes.naturalMap_decode (sourceDomain change domain) (sourceBody change domain body)
    sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions) arrow
      (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows X member)).trans
        (congrArg ((ContextualWTypes.family (sourceDomain change domain) (sourceBody change domain body)).map arrow)
          (decode_memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows X member))
  exact (decode_memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows Y _).trans
    ((congrArg (naturalEquiv change domain body Y) first).trans
      ((Subtype.ext (pullRaw_restrict change domain body arrow
        ((targetModel domain body worlds arrows shapes positions ((elementMap change).obj X)).decode member).val)).trans last.symm))

theorem memberEquiv_constructor (point : Q.Elements) (label : domain.obj ((elementMap change).obj point))
    (branches : ContextualWTypes.Branches domain body (ContextualWTypes.family domain body) label) :
    memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows point
      ((targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).decode.symm
        ((ContextualWTypes.treeAlgebra domain body).make ((elementMap change).obj point) label branches)) =
    (sourceModel change domain body shapes positions sourceWorlds sourceArrows point).decode.symm
      ((ContextualWTypes.treeAlgebra (sourceDomain change domain) (sourceBody change domain body)).make point label
        (pullTreeBranches change domain body point label branches)) :=
  (memberEquiv_term change domain body worlds arrows shapes positions sourceWorlds sourceArrows point _).trans
    (congrArg (sourceModel change domain body shapes positions sourceWorlds sourceArrows point).decode.symm
      (constructor_baseChange change domain body point label branches))

theorem materialFold_baseChange (target : P.Elements ⥤ Type u)
    (algebra : ContextualWTypes.Algebra domain body target) (point : Q.Elements)
    (member : TargetMembers domain body worlds arrows shapes positions ((elementMap change).obj point)) :
    ContextualWTypes.fold (sourceDomain change domain) (sourceBody change domain body)
      (pullAlgebra change domain body target algebra)
      ((sourceModel change domain body shapes positions sourceWorlds sourceArrows point).decode
        (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows point member)) =
    ContextualWTypes.fold domain body algebra
      ((targetModel domain body worlds arrows shapes positions ((elementMap change).obj point)).decode member) := by
  rw [decode_memberEquiv]
  exact fold_baseChange change domain body target algebra point _

/-- Representation comparisons form a natural isomorphism of the actual
member presheaves, even when their authored graph labels differ. -/
noncomputable def materialBaseChange :
    NatTrans
      (Mettapedia.GSLT.Topos.ConstructivePresheaf.restrict (elementMap change)
        (MaterialContextualWTypes.materialFamily domain body worlds arrows shapes positions))
      (MaterialContextualWTypes.materialFamily (sourceDomain change domain) (sourceBody change domain body)
        sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions)) where
  app point := TypeCat.ofHom (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows point)
  naturality _X _Y arrow := by
    apply ConcreteCategory.hom_ext
    exact memberEquiv_restrict change domain body worlds arrows shapes positions sourceWorlds sourceArrows arrow

noncomputable def materialBaseChangeInverse :
    NatTrans
      (MaterialContextualWTypes.materialFamily (sourceDomain change domain) (sourceBody change domain body)
        sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions))
      (Mettapedia.GSLT.Topos.ConstructivePresheaf.restrict (elementMap change)
        (MaterialContextualWTypes.materialFamily domain body worlds arrows shapes positions)) where
  app point := TypeCat.ofHom (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows point).symm
  naturality X Y arrow := by
    apply ConcreteCategory.hom_ext
    intro member
    apply (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows Y).injective
    exact ((memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows Y).apply_symm_apply _).trans
      ((memberEquiv_restrict change domain body worlds arrows shapes positions sourceWorlds sourceArrows arrow
        ((memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows X).symm member)).trans
          (congrArg
            (MaterialContextualWTypes.naturalMap (sourceDomain change domain) (sourceBody change domain body)
              sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions) arrow)
            ((memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows X).apply_symm_apply member))).symm

theorem materialBaseChange_left (point : Q.Elements)
    (member : TargetMembers domain body worlds arrows shapes positions ((elementMap change).obj point)) :
    (materialBaseChangeInverse change domain body worlds arrows shapes positions sourceWorlds sourceArrows).app point
      ((materialBaseChange change domain body worlds arrows shapes positions sourceWorlds sourceArrows).app point member) = member :=
  (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows point).symm_apply_apply member

theorem materialBaseChange_right (point : Q.Elements)
    (member : SourceMembers change domain body shapes positions sourceWorlds sourceArrows point) :
    (materialBaseChange change domain body worlds arrows shapes positions sourceWorlds sourceArrows).app point
      ((materialBaseChangeInverse change domain body worlds arrows shapes positions sourceWorlds sourceArrows).app point member) = member :=
  (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows point).apply_symm_apply member

theorem memberEquiv_identity (point : P.Elements)
    (member : TargetMembers domain body worlds arrows shapes positions point) :
    memberEquiv (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity P)
      domain body worlds arrows shapes positions worlds arrows point member = member := by
  apply (targetModel domain body worlds arrows shapes positions point).decode.injective
  exact (decode_memberEquiv (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity P)
    domain body worlds arrows shapes positions worlds arrows point member).trans
      (naturalEquiv_identity domain body point _)

variable {R : Cᵒᵖ ⥤ Type u} (earlier : NatTrans R Q)
variable (lastWorlds : ArgumentCoding R.Elements)
variable (lastArrows : (first second : R.Elements) → ArgumentCoding (first ⟶ second))

theorem memberEquiv_comp (point : R.Elements)
    (member : TargetMembers domain body worlds arrows shapes positions
      ((elementMap change).obj ((elementMap earlier).obj point))) :
    memberEquiv (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change)
      domain body worlds arrows shapes positions lastWorlds lastArrows point member =
    memberEquiv earlier (sourceDomain change domain) (sourceBody change domain body)
      sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions)
      lastWorlds lastArrows point
        (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows
          ((elementMap earlier).obj point) member) := by
  apply (sourceModel (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change)
    domain body shapes positions lastWorlds lastArrows point).decode.injective
  have last := (decode_memberEquiv earlier (sourceDomain change domain) (sourceBody change domain body)
    sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions)
    lastWorlds lastArrows point
      (memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows
        ((elementMap earlier).obj point) member)).trans
      (congrArg (naturalEquiv earlier (sourceDomain change domain) (sourceBody change domain body) point)
        (decode_memberEquiv change domain body worlds arrows shapes positions sourceWorlds sourceArrows
          ((elementMap earlier).obj point) member))
  exact (decode_memberEquiv (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change)
    domain body worlds arrows shapes positions lastWorlds lastArrows point member).trans
      ((naturalEquiv_comp change domain body earlier point _).trans last.symm)

theorem transported_value_comp (point : R.Elements)
    (tree : NaturalTree domain body ((elementMap change).obj ((elementMap earlier).obj point))) :
    (transportedModel (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change)
      domain body worlds arrows shapes positions point).value
        (naturalEquiv earlier (sourceDomain change domain) (sourceBody change domain body) point
          (naturalEquiv change domain body ((elementMap earlier).obj point) tree)) =
      (targetModel domain body worlds arrows shapes positions
        ((elementMap change).obj ((elementMap earlier).obj point))).value tree :=
  (congrArg (transportedModel (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change)
    domain body worlds arrows shapes positions point).value
      (naturalEquiv_comp change domain body earlier point tree).symm).trans
        (transported_value (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose earlier change)
          domain body worlds arrows shapes positions point tree)

/-- Independent faithful labels retain the source context in every root. -/
theorem source_value_retains_world {X Y : Q.Elements}
    (first : NaturalTree (sourceDomain change domain) (sourceBody change domain body) X)
    (second : NaturalTree (sourceDomain change domain) (sourceBody change domain body) Y)
    (same : (sourceModel change domain body shapes positions sourceWorlds sourceArrows X).value first =
      (sourceModel change domain body shapes positions sourceWorlds sourceArrows Y).value second) : X = Y := by
  rcases first with ⟨first, _firstNatural⟩
  rcases second with ⟨second, _secondNatural⟩
  cases first with
  | sup label children =>
    cases second with
    | sup other successors =>
      change MaterialContextualWTypes.encode (sourceDomain change domain) (sourceBody change domain body)
        sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions)
          (.sup label children) =
        MaterialContextualWTypes.encode (sourceDomain change domain) (sourceBody change domain body)
          sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions)
            (.sup other successors) at same
      have row := (MaterialContextualWTypes.mem_encode_sup_iff (sourceDomain change domain) (sourceBody change domain body)
        sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions)
          label children (HSet.kpair (ContextualWLabels.shapeTag sourceWorlds X
            ((sourceShapes change domain shapes X).value label)) ∅)).mpr (Or.inl rfl)
      rw [same] at row
      rcases (MaterialContextualWTypes.mem_encode_sup_iff (sourceDomain change domain) (sourceBody change domain body)
        sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions)
          other successors _).mp row with sameShape | ⟨branch, sameBranch⟩
      · exact sourceWorlds.injective (HSet.kpair_inj.mp (HSet.kpair_inj.mp (HSet.kpair_inj.mp sameShape).1).2).1
      · exact (ContextualWLabels.shapeTag_ne_positionTag (sourceDomain change domain) (sourceBody change domain body)
          sourceWorlds sourceArrows (sourceShapes change domain shapes) (sourcePositions change domain body positions)
            X ((sourceShapes change domain shapes X).value label) ⟨Y, other⟩ branch
              (HSet.kpair_inj.mp sameBranch).1).elim

theorem source_values_distinct_worlds {X Y : Q.Elements} (different : X ≠ Y)
    (first : NaturalTree (sourceDomain change domain) (sourceBody change domain body) X)
    (second : NaturalTree (sourceDomain change domain) (sourceBody change domain body) Y) :
    (sourceModel change domain body shapes positions sourceWorlds sourceArrows X).value first ≠
      (sourceModel change domain body shapes positions sourceWorlds sourceArrows Y).value second :=
  fun same => different (source_value_retains_world change domain body shapes positions sourceWorlds sourceArrows first second same)

theorem parallel_lifts_distinct (point : Q.Elements) {target : P.Elements}
    (first second : (elementMap change).obj point ⟶ target) (different : first ≠ second) :
    (PowerClassPresheafBaseChange.liftFuture change point).obj ⟨target, first⟩ ≠
      (PowerClassPresheafBaseChange.liftFuture change point).obj ⟨target, second⟩ := by
  intro same
  have originals := (PowerClassPresheafBaseChange.future_forward_backward change point ⟨target, first⟩).symm.trans
    ((congrArg (PowerClassPresheafBaseChange.Future.map (elementMap change) point).obj same).trans
      (PowerClassPresheafBaseChange.future_forward_backward change point ⟨target, second⟩))
  exact different (eq_of_heq (PowerClassPresheafBaseChange.Cat.dependentValue_heq
    (fun future : PowerClassPresheafBaseChange.Future.Objects ((elementMap change).obj point) => future.2) originals))

end Comparison

namespace Growing

open ContextualGeneratedUniverse

abbrev base := ContextualGeneratedUniverse.Growing.context.base
abbrev domain := ContextualGeneratedUniverse.Growing.input.family
abbrev positions := PowerClassPresheafProducts.indexedBody domain ContextualGeneratedUniverse.Growing.terminalBody.family

def tagged : ContextualGeneratedUniverse.Growing.Stagesᵒᵖ ⥤ Type where
  obj point := base.obj point × Bool
  map arrow := TypeCat.ofHom fun value => ⟨base.map arrow value.1, value.2⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    rintro ⟨value, tag⟩
    exact congrArg (fun member => (member, tag)) (base.map_id_apply point value)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    rintro ⟨value, tag⟩
    exact congrArg (fun member => (member, tag)) (base.map_comp_apply first later value)

/-- A genuinely noninjective context map, on the actual growing observed site. -/
def forgetTag : NatTrans tagged base where
  app _ := TypeCat.ofHom Prod.fst
  naturality _ _ _ := rfl

def tagIndex : Bool → Nat
  | false => 0
  | true => 1

def tagCoding : ArgumentCoding Bool where
  graph tag := OutcomeLabels.chainGraph (tagIndex tag)
  injective := by
    intro first second same
    have indices := OutcomeLabels.chainValue_injective
      ((OutcomeLabels.mk_chainGraph (tagIndex first)).symm.trans
        (same.trans (OutcomeLabels.mk_chainGraph (tagIndex second))))
    cases first <;> cases second
    · rfl
    · exact (Nat.zero_ne_one indices).elim
    · exact (Nat.zero_ne_one indices.symm).elim
    · rfl

def worlds : ArgumentCoding tagged.Elements where
  graph point := (ContextualGeneratedUniverse.Growing.context.labels.sigma
    (fun _ => tagCoding)).graph ⟨⟨point.1, point.2.1⟩, point.2.2⟩
  injective := by
    rintro ⟨X, value, tag⟩ ⟨Y, other, otherTag⟩ same
    have paired := (ContextualGeneratedUniverse.Growing.context.labels.sigma
      (fun _ => tagCoding)).injective same
    have parent := congrArg Sigma.fst paired
    have worlds : X = Y := congrArg Sigma.fst parent
    subst Y
    have values : value = other := eq_of_heq (Sigma.mk.inj_iff.mp parent).2
    subst other
    have tags : tag = otherTag := eq_of_heq (Sigma.mk.inj_iff.mp paired).2
    subst otherTag
    rfl

def arrows (first second : tagged.Elements) : ArgumentCoding (first ⟶ second) :=
  (ContextualGeneratedUniverse.Growing.arrowCoding first.1 second.1).subtype
    (fun step => tagged.map step first.2 = second.2)

def shapeModels (point : base.Elements) := ContextualGeneratedUniverse.Growing.input.model point

def positionModels (_point : domain.Elements) : PresentedType (positions.obj _point) := PresentedType.empty

abbrev targetArrows := MaterialFamily.elementArrowCoding
  (context := ContextualGeneratedUniverse.Growing.context) ContextualGeneratedUniverse.Growing.arrowCoding

def point (root : base.Elements) (tag : Bool) : tagged.Elements := ⟨root.1, root.2, tag⟩

theorem forgetTag_merges (root : base.Elements) :
    (elementMap forgetTag).obj (point root false) = (elementMap forgetTag).obj (point root true) := rfl

theorem tags_are_distinct (root : base.Elements) : point root false ≠ point root true := by
  intro same
  exact Bool.false_ne_true (congrArg (fun value : tagged.Elements => value.2.2) same)

noncomputable def leaf (root : base.Elements) (label : domain.obj root) (tag : Bool) :=
  naturalEquiv forgetTag domain positions (point root tag) (ContextualGeneratedUniverse.Growing.leaf root label)

abbrev fresh (root : base.Elements) (tag : Bool) :=
  sourceModel forgetTag domain positions shapeModels positionModels worlds arrows (point root tag)

/-- The changed model exists at every observed context, including cyclic
payloads newly available at later stages. -/
theorem changed_leaf_member (root : base.Elements) (label : domain.obj root) (tag : Bool) :
    (fresh root tag).value (leaf root label tag) ∈ (fresh root tag).carrier := (fresh root tag).value_mem _

theorem changed_cyclic_payload :
    (sourceShapes forgetTag domain shapeModels (point ContextualGeneratedUniverse.Growing.later false)).value
      PowerClassContextualMaterialization.Growing.futureArgument = HSet.quineAtom :=
  ContextualGeneratedUniverse.Growing.cyclic_leaf_shape

/-- Literal graph equality cannot replace the representation equivalence:
fresh faithful labels distinguish contexts that the base map merges. -/
theorem fresh_tags_differ (root : base.Elements) (label : domain.obj root) :
    (fresh root false).value (leaf root label false) ≠
      (fresh root true).value (leaf root label true) :=
  source_values_distinct_worlds forgetTag domain positions shapeModels positionModels worlds arrows
    (tags_are_distinct root) _ _

theorem transported_tags_agree (root : base.Elements) (label : domain.obj root) :
    (transportedModel forgetTag domain positions ContextualGeneratedUniverse.Growing.context.labels
      targetArrows shapeModels positionModels (point root false)).value (leaf root label false) =
    (transportedModel forgetTag domain positions ContextualGeneratedUniverse.Growing.context.labels
      targetArrows shapeModels positionModels (point root true)).value (leaf root label true) :=
  (transported_value forgetTag domain positions ContextualGeneratedUniverse.Growing.context.labels
    targetArrows shapeModels positionModels (point root false) _).trans
      (transported_value forgetTag domain positions ContextualGeneratedUniverse.Growing.context.labels
        targetArrows shapeModels positionModels (point root true) _).symm

def taggedFutureArrow (tag : Bool) :
    point ContextualGeneratedUniverse.Growing.old tag ⟶ point ContextualGeneratedUniverse.Growing.later tag :=
  CategoryOfElements.homMk _ _ PowerClassContextualMaterialization.Growing.futureArrow.val
    (Prod.ext PowerClassContextualMaterialization.Growing.futureArrow.property rfl)

theorem tagged_future_arrow_image (tag : Bool) :
    (elementMap forgetTag).map (taggedFutureArrow tag) = PowerClassContextualMaterialization.Growing.futureArrow := by
  apply CategoryOfElements.ext base
  rfl

/-- The newly reached stage and its exact arrow have an actual lift; the
extra tag is retained and never used to discard that future branch. -/
theorem tagged_future_lift (tag : Bool) :
    (PowerClassPresheafBaseChange.liftFuture forgetTag (point ContextualGeneratedUniverse.Growing.old tag)).obj
      ⟨ContextualGeneratedUniverse.Growing.later, PowerClassContextualMaterialization.Growing.futureArrow⟩ =
      ⟨point ContextualGeneratedUniverse.Growing.later tag, taggedFutureArrow tag⟩ :=
  by
    have image : (PowerClassPresheafBaseChange.Future.map (elementMap forgetTag)
        (point ContextualGeneratedUniverse.Growing.old tag)).obj
          ⟨point ContextualGeneratedUniverse.Growing.later tag, taggedFutureArrow tag⟩ =
        ⟨ContextualGeneratedUniverse.Growing.later, PowerClassContextualMaterialization.Growing.futureArrow⟩ :=
      PowerClassPresheafBaseChange.Future.objects_ext rfl (heq_of_eq (tagged_future_arrow_image tag))
    exact (congrArg (PowerClassPresheafBaseChange.liftFuture forgetTag
      (point ContextualGeneratedUniverse.Growing.old tag)).obj image.symm).trans
        (PowerClassPresheafBaseChange.future_backward_forward forgetTag _ _)

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWBaseChange
