import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualQuotient

/-!
# Typed type and term fibres over typed context equations

The type relation is typed equality at some admitted universe. Total-term
equality requires both an annotation equality and a value equality at the
first annotation. Universe joins earn transitivity, and typed functionality
earns invariance under equivalent substitutions. No raw conversion admission
is required to replace an annotation by a typed-equal representative.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

def typeCodeSetoid (context : Context rules) : Setoid (TypeOver context) where
  r first second := TypeEq rules context.raw first.code second.code
  iseqv := ⟨fun type => type.isType.refl, fun same => same.symm,
    fun first second => first.trans levels second⟩

def QType (context : Context rules) := _root_.Quotient (typeCodeSetoid levels context)

def QType.mk {context : Context rules} (type : TypeOver context) : QType levels context :=
  _root_.Quotient.mk _ type

theorem QType.mk_eq_iff {context : Context rules} (first second : TypeOver context) :
    QType.mk levels first = QType.mk levels second ↔
      TypeEq rules context.raw first.code second.code := _root_.Quotient.eq

def TotalTerm (context : Context rules) := Σ type : TypeOver context, Term context type

def TotalTerm.reindex {source target : Context rules} (pair : TotalTerm target)
    (morphism : source ⟶ target) : TotalTerm source :=
  ⟨pair.1.reindex morphism, pair.2.reindex morphism⟩

def totalTermSetoid (context : Context rules) : Setoid (TotalTerm context) where
  r first second := TypeEq rules context.raw first.1.code second.1.code ∧
    Equal rules context.raw first.2.code second.2.code first.1.code
  iseqv := ⟨fun pair => ⟨pair.1.isType.refl, .refl pair.2.typed⟩,
    fun same => ⟨same.1.symm, Equal.convType (.symm same.2) same.1⟩,
    fun first second => ⟨first.1.trans levels second.1,
      .trans first.2 (Equal.convType second.2 first.1.symm)⟩⟩

def QTerm (context : Context rules) := _root_.Quotient (totalTermSetoid levels context)

def QTerm.mk {context : Context rules} {type : TypeOver context}
    (term : Term context type) : QTerm levels context := _root_.Quotient.mk _ ⟨type, term⟩

theorem QTerm.mk_eq_iff {context : Context rules} {first second : TypeOver context}
    (left : Term context first) (right : Term context second) :
    QTerm.mk levels left = QTerm.mk levels right ↔
      TypeEq rules context.raw first.code second.code ∧
        Equal rules context.raw left.code right.code first.code := _root_.Quotient.eq

def QTerm.type {context : Context rules} (term : QTerm levels context) : QType levels context :=
  _root_.Quotient.lift (s := totalTermSetoid levels context)
    (fun pair : TotalTerm context => QType.mk levels pair.1)
    (fun _ _ same => _root_.Quotient.sound same.1) term

@[simp] theorem QTerm.type_mk {context : Context rules} {type : TypeOver context}
    (term : Term context type) : (QTerm.mk levels term).type = QType.mk levels type := rfl

variable {levels}

theorem reindex_typeEquality {source target : Context rules} {first second : Tm Head target.arity}
    (same : TypeEq rules target.raw first second) (morphism : source ⟶ target) :
    TypeEq rules source.raw (subst morphism.substitution first) (subst morphism.substitution second) := by
  obtain ⟨level, universeWitness, equality⟩ := same
  exact ⟨level, universeWitness, by simpa only [subst] using equality.substitute morphism.typed⟩

def QType.reindex {source target : Context rules} (type : QType levels target)
    (morphism : source ⟶ target) : QType levels source :=
  _root_.Quotient.map (fun formed => formed.reindex morphism)
    (fun _ _ same => reindex_typeEquality same morphism) type

@[simp] theorem QType.reindex_mk {source target : Context rules} (type : TypeOver target)
    (morphism : source ⟶ target) :
    (QType.mk levels type).reindex morphism = QType.mk levels (type.reindex morphism) := rfl

theorem QType.reindex_id {context : Context rules} (type : QType levels context) :
    type.reindex (𝟙 context) = type := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact congrArg (QType.mk levels) formed.reindex_id

theorem QType.reindex_comp {first middle last : Context rules} (type : QType levels last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    type.reindex (earlier ≫ later) = (type.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact congrArg (QType.mk levels) (formed.reindex_comp earlier later)

theorem QType.reindex_congruent {source target : Context rules} (type : QType levels target)
    {first second : source ⟶ target} (same : homTypedEquality rules first second) :
    type.reindex first = type.reindex second := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact _root_.Quotient.sound ⟨formed.level, formed.universeWitness,
    by simpa only [subst, TypeOver.reindex] using formed.formed.functional same⟩

def QTerm.reindex {source target : Context rules} (term : QTerm levels target)
    (morphism : source ⟶ target) : QTerm levels source :=
  _root_.Quotient.map (sa := totalTermSetoid levels target)
    (sb := totalTermSetoid levels source) (fun pair : TotalTerm target => pair.reindex morphism)
    (fun _ _ same => ⟨reindex_typeEquality same.1 morphism, same.2.substitute morphism.typed⟩) term

@[simp] theorem QTerm.reindex_mk {source target : Context rules} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) :
    (QTerm.mk levels term).reindex morphism = QTerm.mk levels (term.reindex morphism) := rfl

theorem QTerm.type_reindex {source target : Context rules} (term : QTerm levels target)
    (morphism : source ⟶ target) :
    (term.reindex morphism).type = term.type.reindex morphism := by
  refine _root_.Quotient.inductionOn term fun _ => rfl

theorem QTerm.reindex_id {context : Context rules} (term : QTerm levels context) :
    term.reindex (𝟙 context) = term := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  apply (QTerm.mk_eq_iff levels _ _).mpr
  change TypeEq rules context.raw (subst ids pair.1.code) pair.1.code ∧
    Equal rules context.raw (subst ids pair.2.code) pair.2.code (subst ids pair.1.code)
  rw [subst_ids, subst_ids]
  exact ⟨pair.1.isType.refl, .refl pair.2.typed⟩

theorem QTerm.reindex_comp {first middle last : Context rules} (term : QTerm levels last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    term.reindex (earlier ≫ later) = (term.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  apply (QTerm.mk_eq_iff levels _ _).mpr
  change TypeEq rules first.raw
      (subst (subComp earlier.substitution later.substitution) pair.1.code)
      (subst earlier.substitution (subst later.substitution pair.1.code)) ∧
    Equal rules first.raw
      (subst (subComp earlier.substitution later.substitution) pair.2.code)
      (subst earlier.substitution (subst later.substitution pair.2.code))
      (subst (subComp earlier.substitution later.substitution) pair.1.code)
  rw [subst_subComp, subst_subComp]
  exact ⟨(pair.1.reindex (earlier ≫ later)).isType.refl,
    .refl (pair.2.reindex (earlier ≫ later)).typed⟩

theorem QTerm.reindex_congruent {source target : Context rules} (term : QTerm levels target)
    {first second : source ⟶ target} (same : homTypedEquality rules first second) :
    term.reindex first = term.reindex second := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  exact _root_.Quotient.sound ⟨⟨pair.1.level, pair.1.universeWitness,
    pair.1.formed.functional same⟩, pair.2.typed.functional same⟩

theorem QTerm.mk_convertType {context : Context rules} {first : TypeOver context}
    (term : Term context first) (second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) :
    QTerm.mk levels (term.convertType second same) = QTerm.mk levels term := by
  exact _root_.Quotient.sound ⟨same.symm, .refl (term.convertType second same).typed⟩

theorem QTerm.mk_cast {context : Context rules} {first second : TypeOver context}
    (term : Term context first) (same : first = second) :
    QTerm.mk levels (term.cast same) = QTerm.mk levels term := by
  cases same
  rfl

variable (levels)

def QType.rawPresheaf : (Context rules)ᵒᵖ ⥤ Type where
  obj context := QType levels context.unop
  map morphism := TypeCat.ofHom fun type => QType.reindex type morphism.unop
  map_id _ := by ext type; exact QType.reindex_id type
  map_comp first second := by ext type; exact QType.reindex_comp type second.unop first.unop

def QTerm.rawPresheaf : (Context rules)ᵒᵖ ⥤ Type where
  obj context := QTerm levels context.unop
  map morphism := TypeCat.ofHom fun term => QTerm.reindex term morphism.unop
  map_id _ := by ext term; exact QTerm.reindex_id term
  map_comp first second := by ext term; exact QTerm.reindex_comp term second.unop first.unop

def QType.presheaf : (quotientContext rules)ᵒᵖ ⥤ Type :=
  (_root_.CategoryTheory.Quotient.lift (homTypedEquality rules) (QType.rawPresheaf levels).rightOp
    (fun _ _ _ _ same => Quiver.Hom.unop_inj
      (by ext type; exact QType.reindex_congruent type same))).leftOp

def QTerm.presheaf : (quotientContext rules)ᵒᵖ ⥤ Type :=
  (_root_.CategoryTheory.Quotient.lift (homTypedEquality rules) (QTerm.rawPresheaf levels).rightOp
    (fun _ _ _ _ same => Quiver.Hom.unop_inj
      (by ext term; exact QTerm.reindex_congruent term same))).leftOp

@[simp] theorem QType.presheaf_obj (context : quotientContext rules) :
    (QType.presheaf levels).obj (.op context) = QType levels context.as := rfl

@[simp] theorem QTerm.presheaf_obj (context : quotientContext rules) :
    (QTerm.presheaf levels).obj (.op context) = QTerm levels context.as := rfl

@[simp] theorem QType.presheaf_map_projected {source target : Context rules}
    (morphism : source ⟶ target) (type : QType levels target) :
    (QType.presheaf levels).map ((quotientProjection rules).map morphism).op type =
      type.reindex morphism := rfl

@[simp] theorem QTerm.presheaf_map_projected {source target : Context rules}
    (morphism : source ⟶ target) (term : QTerm levels target) :
    (QTerm.presheaf levels).map ((quotientProjection rules).map morphism).op term =
      term.reindex morphism := rfl

theorem QTerm.presheaf_type_natural {source target : quotientContext rules}
    (morphism : source ⟶ target) (term : QTerm levels target.as) :
    ((QTerm.presheaf levels).map morphism.op term).type =
      (QType.presheaf levels).map morphism.op term.type := by
  revert term
  refine Quot.inductionOn morphism (fun raw term => ?_)
  exact QTerm.type_reindex term raw

def typeProjection : QTerm.presheaf levels ⟶ QType.presheaf levels where
  app _ := TypeCat.ofHom (QTerm.type levels)
  naturality := by
    intro source target morphism
    ext term
    exact QTerm.presheaf_type_natural levels morphism.unop term

end TypedContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
