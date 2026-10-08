import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTypedContextQuotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualFibres

/-!
# Formation-sensitive evidence in the full typed context model

The qualified formation-sensitive context category maps into the category
whose admissions use full typed equality. Actual formation and component
typing proofs construct that map. It descends through the typed equations
of contextual arrows and compares the two independently constructed type
and total-term presheaves, including their display maps.

The fibre maps are injective because the earned typed equations are the
same at the supplied raw telescope. No coverage of all typed admissions or
preservation of selected comprehension representatives is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveTypedAdmission

open _root_.CategoryTheory
open TypedEquality TypedEquality.Normalization
open FormationSensitiveContextual FormationSensitiveTypedQuotient

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (q : Qualification S)

/-- The actual formation spine earns admission of the same telescope. -/
def admitContext (context : Context S.R) : TypedContextual.Context S.R :=
  ⟨context.arity, context.raw, contextFormed q context.formed⟩

/-- Every supplied substitution component is admitted by conservativity. -/
def admitArrow {source target : Context S.R} (morphism : source ⟶ target) :
    admitContext q source ⟶ admitContext q target :=
  ⟨morphism.substitution, homTyped q morphism⟩

def admissionFunctor : Context S.R ⥤ TypedContextual.Context S.R where
  obj := admitContext q
  map := admitArrow q
  map_id _ := TypedContextual.Hom.ext rfl
  map_comp _ _ := TypedContextual.Hom.ext rfl

def admitType {context : Context S.R} (type : TypeOver context) :
    TypedContextual.TypeOver (admitContext q context) :=
  ⟨type.code, type.level, type.universeWitness, typeTyped q type⟩

def admitTerm {context : Context S.R} {type : TypeOver context} (term : Term context type) :
    TypedContextual.Term (admitContext q context) (admitType q type) :=
  ⟨term.code, termTyped q term⟩

theorem admitType_reindex {source target : Context S.R} (type : TypeOver target)
    (morphism : source ⟶ target) :
    admitType q (type.reindex morphism) =
      (admitType q type).reindex (admitArrow q morphism) :=
  TypedContextual.TypeOver.ext rfl rfl

theorem admitArrow_typed_equal {source target : Context S.R}
    {first second : source ⟶ target} (same : homTypedEquality S.R first second) :
    TypedContextual.homTypedEquality S.R (admitArrow q first) (admitArrow q second) := same

/-- The comparison on bases descends by the actual dependent component
equation, rather than by a quotient of only endpoint observations. -/
def typedBaseFunctor : typedContext S.R ⥤ TypedContextual.quotientContext S.R :=
  _root_.CategoryTheory.Quotient.lift (homTypedEquality S.R)
    (admissionFunctor q ⋙ TypedContextual.quotientProjection S.R)
    (fun _ _ _ _ same =>
      (TypedContextual.quotientProjection_map_eq_iff _ _).mpr (admitArrow_typed_equal q same))

@[simp] theorem typedBaseFunctor_obj (context : typedContext S.R) :
    ((typedBaseFunctor q).obj context).as = admitContext q context.as := rfl

@[simp] theorem typedBaseFunctor_map_projected {source target : Context S.R}
    (morphism : source ⟶ target) :
    (typedBaseFunctor q).map ((typedProjection S.R).map morphism) =
      (TypedContextual.quotientProjection S.R).map (admitArrow q morphism) := rfl

/-- On the supplied formation-sensitive contexts the base comparison
reflects precisely the same dependent component equations. -/
instance typedBaseFunctor_faithful : (typedBaseFunctor q).Faithful where
  map_injective := by
    intro source target first second same
    induction first using Quot.inductionOn with
    | h first =>
      induction second using Quot.inductionOn with
      | h second =>
        apply (typedProjection_map_eq_iff q first second).mpr
        exact (TypedContextual.quotientProjection_map_eq_iff
          (admitArrow q first) (admitArrow q second)).mp same

def typeClassMap {context : Context S.R} (type : QType q context) :
    TypedContextual.QType S.levels (admitContext q context) :=
  _root_.Quotient.map (admitType q) (fun _ _ same => same) type

def termClassMap {context : Context S.R} (term : QTerm q context) :
    TypedContextual.QTerm S.levels (admitContext q context) :=
  _root_.Quotient.map
    (fun pair : TotalTerm context => ⟨admitType q pair.1, admitTerm q pair.2⟩)
    (fun _ _ same => same) term

@[simp] theorem typeClassMap_mk {context : Context S.R} (type : TypeOver context) :
    typeClassMap q (QType.mk q type) = TypedContextual.QType.mk S.levels (admitType q type) := rfl

@[simp] theorem termClassMap_mk {context : Context S.R} {type : TypeOver context}
    (term : Term context type) :
    termClassMap q (QTerm.mk q term) = TypedContextual.QTerm.mk S.levels (admitTerm q term) := rfl

theorem termClassMap_type {context : Context S.R} (term : QTerm q context) :
    (termClassMap q term).type = typeClassMap q term.type := by
  induction term using _root_.Quotient.inductionOn with
  | h pair => rfl

theorem typeClassMap_injective (context : Context S.R) :
    Function.Injective (typeClassMap q (context := context)) := by
  intro first second same
  induction first using _root_.Quotient.inductionOn with
  | h first =>
    induction second using _root_.Quotient.inductionOn with
    | h second =>
      exact _root_.Quotient.sound
        ((TypedContextual.QType.mk_eq_iff S.levels (admitType q first) (admitType q second)).mp same)

theorem termClassMap_injective (context : Context S.R) :
    Function.Injective (termClassMap q (context := context)) := by
  intro first second same
  induction first using _root_.Quotient.inductionOn with
  | h first =>
    induction second using _root_.Quotient.inductionOn with
    | h second =>
      exact _root_.Quotient.sound
        ((TypedContextual.QTerm.mk_eq_iff S.levels (admitTerm q first.2) (admitTerm q second.2)).mp same)

theorem typeClassMap_reindex {source target : Context S.R} (type : QType q target)
    (morphism : source ⟶ target) :
    typeClassMap q (type.reindex morphism) =
      (typeClassMap q type).reindex (admitArrow q morphism) := by
  induction type using _root_.Quotient.inductionOn with
  | h type => exact congrArg (TypedContextual.QType.mk S.levels) (admitType_reindex q type morphism)

theorem termClassMap_reindex {source target : Context S.R} (term : QTerm q target)
    (morphism : source ⟶ target) :
    termClassMap q (term.reindex morphism) =
      (termClassMap q term).reindex (admitArrow q morphism) := by
  induction term using _root_.Quotient.inductionOn with
  | h pair =>
      apply (TypedContextual.QTerm.mk_eq_iff S.levels _ _).mpr
      exact ⟨(admitType q (pair.1.reindex morphism)).isType.refl,
        .refl (admitTerm q (pair.2.reindex morphism)).typed⟩

theorem typeClassMap_quotient_reindex {source target : typedContext S.R}
    (type : QType q target.as) (morphism : source ⟶ target) :
    typeClassMap q ((QType.typedPresheaf q).map morphism.op type) =
      (TypedContextual.QType.presheaf S.levels).map ((typedBaseFunctor q).map morphism).op
        (typeClassMap q type) := by
  induction morphism using Quot.inductionOn with
  | h raw => exact typeClassMap_reindex q type raw

theorem termClassMap_quotient_reindex {source target : typedContext S.R}
    (term : QTerm q target.as) (morphism : source ⟶ target) :
    termClassMap q ((QTerm.typedPresheaf q).map morphism.op term) =
      (TypedContextual.QTerm.presheaf S.levels).map ((typedBaseFunctor q).map morphism).op
        (termClassMap q term) := by
  induction morphism using Quot.inductionOn with
  | h raw => exact termClassMap_reindex q term raw

/-- Both maps are natural for every actual typed quotient arrow. -/
def typeComparison : QType.typedPresheaf q ⟶
    (typedBaseFunctor q).op ⋙ TypedContextual.QType.presheaf S.levels where
  app _ := TypeCat.ofHom (typeClassMap q)
  naturality := by
    intro source target morphism
    ext type
    exact typeClassMap_quotient_reindex q type morphism.unop

def termComparison : QTerm.typedPresheaf q ⟶
    (typedBaseFunctor q).op ⋙ TypedContextual.QTerm.presheaf S.levels where
  app _ := TypeCat.ofHom (termClassMap q)
  naturality := by
    intro source target morphism
    ext term
    exact termClassMap_quotient_reindex q term morphism.unop

/-- The complete type/term comparison is a commuting display square. -/
theorem display_square :
    termComparison q ≫ Functor.whiskerLeft (typedBaseFunctor q).op (TypedContextual.typeProjection S.levels) =
      typedTypeProjection q ≫ typeComparison q := by
  ext point term
  exact termClassMap_type q term

end FormationSensitiveTypedAdmission
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
