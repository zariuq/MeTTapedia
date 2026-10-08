import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTypedQuotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ContextualSubstitutionEquality

/-!
# Typed substitution quotient of formed contexts

Pointwise typed substitution equality is an actual congruence on the
existing formed arrows. Its symmetry and transitivity account for the
different dependent annotations assigned by the compared substitutions.
The typed type and term families, and their display, descend to this base.

The original conversion quotient maps into this quotient because qualified
raw conversion entails typed substitution equality. No converse is used.
This constructs a base and displayed families; comprehension representability
and a classifying universal property are separate properties.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveTypedQuotient

open _root_.CategoryTheory
open TypedEquality TypedEquality.Normalization
open FormationSensitiveContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (q : Qualification S)

/-- The existing formed arrows are compared at their actual substituted
component types, rather than by untyped conversion of their codes. -/
def homTypedEquality (rules : Rules Head) : HomRel (Context rules) :=
  fun {source target} first second =>
    SubstEq rules target.raw source.raw first.substitution second.substitution

theorem homTypedEquality_refl (q : Qualification S) {source target : Context S.R} (arrow : source ⟶ target) :
    homTypedEquality S.R arrow arrow :=
  SubstEq.reflexive (homTyped q arrow)

/-- The lookup type itself is formed. Functionality therefore relates the
two substituted annotations at an actual universe. -/
theorem homTypedEquality_annotation (q : Qualification S) {source target : Context S.R}
    {first second : source ⟶ target} (same : homTypedEquality S.R first second)
    (index : Fin target.arity) :
    TypeEq S.R source.raw
      (subst first.substitution (Ctx.lookup target.raw index))
      (subst second.substitution (Ctx.lookup target.raw index)) :=
  same.annotation (contextFormed q target.formed) index

theorem homTypedEquality_symm (q : Qualification S) {source target : Context S.R}
    {first second : source ⟶ target} (same : homTypedEquality S.R first second) :
    homTypedEquality S.R second first :=
  same.symmetric (contextFormed q target.formed) (homTyped q second)

theorem homTypedEquality_trans (q : Qualification S) {source target : Context S.R}
    {first middle last : source ⟶ target}
    (earlier : homTypedEquality S.R first middle) (later : homTypedEquality S.R middle last) :
    homTypedEquality S.R first last :=
  earlier.transitive (contextFormed q target.formed) later

/-- Precomposition substitutes into the independently supplied component
equalities and their dependent types. -/
theorem homTypedEquality_precompose (q : Qualification S) {source middle target : Context S.R}
    (earlier : source ⟶ middle) {first second : middle ⟶ target}
    (same : homTypedEquality S.R first second) :
    homTypedEquality S.R (earlier ≫ first) (earlier ≫ second) :=
  same.precompose (homTyped q earlier)

/-- Postcomposition is functionality of every actual component of the
later formed substitution. -/
theorem homTypedEquality_postcompose (q : Qualification S) {source middle target : Context S.R}
    {first second : source ⟶ middle} (same : homTypedEquality S.R first second)
    (later : middle ⟶ target) :
    homTypedEquality S.R (first ≫ later) (second ≫ later) :=
  same.postcompose (homTyped q later)

theorem homTypedEquality_comp (q : Qualification S) {source middle target : Context S.R}
    {first first' : source ⟶ middle} {second second' : middle ⟶ target}
    (earlier : homTypedEquality S.R first first') (later : homTypedEquality S.R second second') :
    homTypedEquality S.R (first ≫ second) (first' ≫ second') :=
  homTypedEquality_trans q (homTypedEquality_postcompose q earlier second)
    (homTypedEquality_precompose q first' later)

theorem homTypedEquality_congruence (q : Qualification S) : Congruence (homTypedEquality S.R) where
  comp_left := homTypedEquality_precompose q
  comp_right := fun later same => homTypedEquality_postcompose q same later
  equivalence :=
    ⟨homTypedEquality_refl q, homTypedEquality_symm q, homTypedEquality_trans q⟩

abbrev typedContext (rules : Rules Head) := _root_.CategoryTheory.Quotient (homTypedEquality rules)

def typedProjection (rules : Rules Head) : Context rules ⥤ typedContext rules :=
  _root_.CategoryTheory.Quotient.functor (homTypedEquality rules)

@[simp] theorem typedProjection_obj_as (context : Context S.R) :
    ((typedProjection S.R).obj context).as = context := rfl

/-- Earned congruence makes the quotient's equality exactly the stated
dependent substitution equality. -/
theorem typedProjection_map_eq_iff (q : Qualification S) {source target : Context S.R}
    (first second : source ⟶ target) :
    (typedProjection S.R).map first = (typedProjection S.R).map second ↔
      SubstEq S.R target.raw source.raw first.substitution second.substitution := by
  let _ := homTypedEquality_congruence q
  exact _root_.CategoryTheory.Quotient.functor_map_eq_iff (homTypedEquality S.R) first second

theorem typedProjection_map_surjective (source target : Context S.R) :
    Function.Surjective (@(typedProjection S.R).map source target) :=
  (_root_.CategoryTheory.Quotient.full_functor (homTypedEquality S.R)).map_surjective

/-- The old raw-conversion base maps to the typed base by conservativity
on the actual typed substitution components. -/
def rawBaseMap : quotientContext S.R ⥤ typedContext S.R :=
  _root_.CategoryTheory.Quotient.lift (homConversion S.R) (typedProjection S.R)
    (fun _ _ _ _ converted => (typedProjection_map_eq_iff q _ _).mpr (homSubstEq q converted))

@[simp] theorem rawBaseMap_obj_as (context : quotientContext S.R) :
    ((rawBaseMap q).obj context).as = context.as := rfl

@[simp] theorem rawBaseMap_map_projected {source target : Context S.R}
    (arrow : source ⟶ target) :
    (rawBaseMap q).map ((quotientProjection S.R).map arrow) =
      (typedProjection S.R).map arrow := rfl

theorem rawBaseMap_factorization : quotientProjection S.R ⋙ rawBaseMap q = typedProjection S.R := rfl

theorem QType.reindex_typed_equal {source target : Context S.R} (type : QType q target)
    {first second : source ⟶ target} (same : homTypedEquality S.R first second) :
    type.reindex first = type.reindex second := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  apply _root_.Quotient.sound
  exact ⟨formed.level, formed.universeWitness, by
    simpa only [subst, TypeOver.reindex] using (typeTyped q formed).functional same⟩

theorem QTerm.reindex_typed_equal {source target : Context S.R} (term : QTerm q target)
    {first second : source ⟶ target} (same : homTypedEquality S.R first second) :
    term.reindex first = term.reindex second := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  apply _root_.Quotient.sound
  exact ⟨⟨pair.1.level, pair.1.universeWitness, (typeTyped q pair.1).functional same⟩,
    (termTyped q pair.2).functional same⟩

def QType.typedPresheaf : (typedContext S.R)ᵒᵖ ⥤ Type :=
  (_root_.CategoryTheory.Quotient.lift (homTypedEquality S.R) (QType.rawPresheaf q).rightOp
    (fun _ _ _ _ same => Quiver.Hom.unop_inj
      (by ext type; exact QType.reindex_typed_equal q type same))).leftOp

def QTerm.typedPresheaf : (typedContext S.R)ᵒᵖ ⥤ Type :=
  (_root_.CategoryTheory.Quotient.lift (homTypedEquality S.R) (QTerm.rawPresheaf q).rightOp
    (fun _ _ _ _ same => Quiver.Hom.unop_inj
      (by ext term; exact QTerm.reindex_typed_equal q term same))).leftOp

@[simp] theorem QType.typedPresheaf_obj (context : typedContext S.R) :
    (QType.typedPresheaf q).obj (.op context) = QType q context.as := rfl

@[simp] theorem QTerm.typedPresheaf_obj (context : typedContext S.R) :
    (QTerm.typedPresheaf q).obj (.op context) = QTerm q context.as := rfl

@[simp] theorem QType.typedPresheaf_map_projected {source target : Context S.R}
    (arrow : source ⟶ target) (type : QType q target) :
    (QType.typedPresheaf q).map ((typedProjection S.R).map arrow).op type =
      type.reindex arrow := rfl

@[simp] theorem QTerm.typedPresheaf_map_projected {source target : Context S.R}
    (arrow : source ⟶ target) (term : QTerm q target) :
    (QTerm.typedPresheaf q).map ((typedProjection S.R).map arrow).op term =
      term.reindex arrow := rfl

theorem QTerm.typedPresheaf_type_natural {source target : typedContext S.R}
    (arrow : source ⟶ target) (term : QTerm q target.as) :
    ((QTerm.typedPresheaf q).map arrow.op term).type =
      (QType.typedPresheaf q).map arrow.op term.type := by
  revert term
  refine Quot.inductionOn arrow (fun raw term => ?_)
  exact QTerm.type_reindex term raw

def typedTypeProjection : QTerm.typedPresheaf q ⟶ QType.typedPresheaf q where
  app _ := TypeCat.ofHom (QTerm.type q)
  naturality := by
    intro source target arrow
    ext term
    exact QTerm.typedPresheaf_type_natural q arrow.unop term

theorem QType.typedPresheaf_factorization :
    (typedProjection S.R).op ⋙ QType.typedPresheaf q = QType.rawPresheaf q := rfl

theorem QTerm.typedPresheaf_factorization :
    (typedProjection S.R).op ⋙ QTerm.typedPresheaf q = QTerm.rawPresheaf q := rfl

theorem QType.rawBaseMap_map {source target : quotientContext S.R} (arrow : source ⟶ target) :
    (QType.typedPresheaf q).map ((rawBaseMap q).map arrow).op =
      (QType.presheaf q).map arrow.op := by
  refine Quot.inductionOn arrow (fun raw => ?_)
  rfl

theorem QTerm.rawBaseMap_map {source target : quotientContext S.R} (arrow : source ⟶ target) :
    (QTerm.typedPresheaf q).map ((rawBaseMap q).map arrow).op =
      (QTerm.presheaf q).map arrow.op := by
  refine Quot.inductionOn arrow (fun raw => ?_)
  rfl

/-- Restriction along the actual raw-to-typed base functor recovers the
previous independently constructed raw-base type family. -/
theorem QType.rawBaseMap_factorization :
    (rawBaseMap q).op ⋙ QType.typedPresheaf q = QType.presheaf q := by
  refine Functor.hext (fun _ => rfl) ?_
  intro source target arrow
  apply heq_of_eq
  exact QType.rawBaseMap_map q arrow.unop

theorem QTerm.rawBaseMap_factorization :
    (rawBaseMap q).op ⋙ QTerm.typedPresheaf q = QTerm.presheaf q := by
  refine Functor.hext (fun _ => rfl) ?_
  intro source target arrow
  apply heq_of_eq
  exact QTerm.rawBaseMap_map q arrow.unop

theorem typedTypeProjection_rawBaseMap :
    eqToHom (QTerm.rawBaseMap_factorization q).symm ≫
      Functor.whiskerLeft (rawBaseMap q).op (typedTypeProjection q) ≫
        eqToHom (QType.rawBaseMap_factorization q) = typeProjection q := by
  ext context term
  simp only [NatTrans.comp_app, eqToHom_app]
  rfl

/-! ## Dependent fibre action over typed substitution classes -/

def TypedFibre {context : typedContext S.R} (type : QType q context.as) :=
  {term : QTerm q context.as // term.type = type}

def TypedFibre.compare {context : typedContext S.R} {first second : QType q context.as}
    (same : first = second) : TypedFibre q first ≃ TypedFibre q second where
  toFun term := ⟨term.val, term.property.trans same⟩
  invFun term := ⟨term.val, term.property.trans same.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

def TypedFibre.reindex {source target : typedContext S.R} {type : QType q target.as}
    (term : TypedFibre q type) (arrow : source ⟶ target) :
    TypedFibre q ((QType.typedPresheaf q).map arrow.op type) :=
  ⟨(QTerm.typedPresheaf q).map arrow.op term.val,
    (QTerm.typedPresheaf_type_natural q arrow term.val).trans
      (congrArg ((QType.typedPresheaf q).map arrow.op) term.property)⟩

theorem QType.typedPresheaf_identity (context : typedContext S.R) (type : QType q context.as) :
    (QType.typedPresheaf q).map (𝟙 context).op type = type := by
  change type.reindex (𝟙 context.as) = type
  exact QType.reindex_id type

theorem QType.typedPresheaf_composition {first middle last : typedContext S.R}
    (type : QType q last.as) (earlier : first ⟶ middle) (later : middle ⟶ last) :
    (QType.typedPresheaf q).map (earlier ≫ later).op type =
      (QType.typedPresheaf q).map earlier.op ((QType.typedPresheaf q).map later.op type) := by
  change (QType.typedPresheaf q).map (later.op ≫ earlier.op) type = _
  rw [Functor.map_comp]
  rfl

theorem TypedFibre.reindex_id {context : typedContext S.R} {type : QType q context.as}
    (term : TypedFibre q type) :
    TypedFibre.compare q (QType.typedPresheaf_identity q context type)
      (TypedFibre.reindex q term (𝟙 context)) = term := by
  apply Subtype.ext
  change term.val.reindex (𝟙 context.as) = term.val
  exact QTerm.reindex_id term.val

theorem TypedFibre.reindex_comp {first middle last : typedContext S.R}
    {type : QType q last.as} (term : TypedFibre q type)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    TypedFibre.compare q (QType.typedPresheaf_composition q type earlier later)
      (TypedFibre.reindex q term (earlier ≫ later)) =
      TypedFibre.reindex q (TypedFibre.reindex q term later) earlier := by
  apply Subtype.ext
  change (QTerm.typedPresheaf q).map (later.op ≫ earlier.op) term.val = _
  rw [Functor.map_comp]
  rfl

theorem TypedFibre.compare_reindex {source target : typedContext S.R}
    {first second : QType q target.as} (same : first = second) (term : TypedFibre q first)
    (arrow : source ⟶ target) :
    TypedFibre.reindex q (TypedFibre.compare q same term) arrow =
      TypedFibre.compare q (congrArg ((QType.typedPresheaf q).map arrow.op) same)
        (TypedFibre.reindex q term arrow) := rfl

end FormationSensitiveTypedQuotient
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
