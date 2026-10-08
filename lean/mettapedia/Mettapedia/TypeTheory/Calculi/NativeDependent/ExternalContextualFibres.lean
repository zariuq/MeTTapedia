import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualQuotient

/-!
# External generated type and term fibres

Types are quotiented by their generated external type equations. A total-term
equation retains both the annotation equation and the term equation at the
first annotation. Actual conversion and typed substitution congruence earn
the resulting presheaves over the contextual arrow quotient.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem typeEquality_refl {context : Context D} (type : TypeOver context) :
    Holds D (.typeEq context.raw type.code type.code) :=
  conclude (.typeReflexivity context.raw type.code) ⟨type.formed, trivial⟩

theorem typeEquality_symm {context : Context D} {first second : TypeExpr S context.arity}
    (same : Holds D (.typeEq context.raw first second)) : Holds D (.typeEq context.raw second first) :=
  conclude (.typeSymmetry context.raw first second) ⟨same, trivial⟩

theorem typeEquality_trans {context : Context D} {first middle last : TypeExpr S context.arity}
    (earlier : Holds D (.typeEq context.raw first middle))
    (later : Holds D (.typeEq context.raw middle last)) : Holds D (.typeEq context.raw first last) :=
  conclude (.typeTransitivity context.raw first middle last) ⟨earlier, later, trivial⟩

theorem termEquality_refl {context : Context D} {type : TypeOver context} (term : Term context type) :
    Holds D (.termEq context.raw term.code term.code type.code) :=
  conclude (.termReflexivity context.raw term.code type.code) ⟨term.typed, trivial⟩

theorem termEquality_symm {context : Context D} {first second : TermExpr S context.arity}
    {type : TypeExpr S context.arity} (same : Holds D (.termEq context.raw first second type)) :
    Holds D (.termEq context.raw second first type) :=
  conclude (.termSymmetry context.raw first second type) ⟨same, trivial⟩

theorem termEquality_trans {context : Context D} {first middle last : TermExpr S context.arity}
    {type : TypeExpr S context.arity} (earlier : Holds D (.termEq context.raw first middle type))
    (later : Holds D (.termEq context.raw middle last type)) :
    Holds D (.termEq context.raw first last type) :=
  conclude (.termTransitivity context.raw first middle last type) ⟨earlier, later, trivial⟩

theorem termEquality_convert {context : Context D} {first second : TermExpr S context.arity}
    {firstType secondType : TypeExpr S context.arity}
    (same : Holds D (.termEq context.raw first second firstType))
    (annotation : Holds D (.typeEq context.raw firstType secondType)) :
    Holds D (.termEq context.raw first second secondType) :=
  conclude (.equalityConversion context.raw first second firstType secondType) ⟨same, annotation, trivial⟩

def typeCodeSetoid (context : Context D) : Setoid (TypeOver context) where
  r first second := Holds D (.typeEq context.raw first.code second.code)
  iseqv := ⟨typeEquality_refl, typeEquality_symm, typeEquality_trans⟩

def QType (context : Context D) := _root_.Quotient (typeCodeSetoid context)

def QType.mk {context : Context D} (type : TypeOver context) : QType context := _root_.Quotient.mk _ type

theorem QType.mk_eq_iff {context : Context D} (first second : TypeOver context) :
    QType.mk first = QType.mk second ↔ Holds D (.typeEq context.raw first.code second.code) := _root_.Quotient.eq

def TotalTerm (context : Context D) := Σ type : TypeOver context, Term context type

def TotalTerm.reindex {source target : Context D} (value : TotalTerm target)
    (morphism : source ⟶ target) : TotalTerm source :=
  ⟨value.1.reindex morphism, value.2.reindex morphism⟩

def totalTermSetoid (context : Context D) : Setoid (TotalTerm context) where
  r first second := Holds D (.typeEq context.raw first.1.code second.1.code) ∧
    Holds D (.termEq context.raw first.2.code second.2.code first.1.code)
  iseqv := ⟨fun value => ⟨typeEquality_refl value.1, termEquality_refl value.2⟩,
    fun same => ⟨typeEquality_symm same.1, termEquality_convert (termEquality_symm same.2) same.1⟩,
    fun first second => ⟨typeEquality_trans first.1 second.1,
      termEquality_trans first.2 (termEquality_convert second.2 (typeEquality_symm first.1))⟩⟩

def QTerm (context : Context D) := _root_.Quotient (totalTermSetoid context)

def QTerm.mk {context : Context D} {type : TypeOver context} (term : Term context type) : QTerm context :=
  _root_.Quotient.mk _ ⟨type, term⟩

theorem QTerm.mk_eq_iff {context : Context D} {first second : TypeOver context}
    (left : Term context first) (right : Term context second) :
    QTerm.mk left = QTerm.mk right ↔ Holds D (.typeEq context.raw first.code second.code) ∧
      Holds D (.termEq context.raw left.code right.code first.code) := _root_.Quotient.eq

def QTerm.type {context : Context D} (term : QTerm context) : QType context :=
  _root_.Quotient.lift (s := totalTermSetoid context)
    (fun value : TotalTerm context => QType.mk value.1)
    (fun _ _ same => _root_.Quotient.sound same.1) term

@[simp] theorem QTerm.type_mk {context : Context D} {type : TypeOver context}
    (term : Term context type) : (QTerm.mk term).type = QType.mk type := rfl

theorem reindex_typeEquality {source target : Context D} {first second : TypeExpr S target.arity}
    (same : Holds D (.typeEq target.raw first second)) (morphism : source ⟶ target) :
    Holds D (.typeEq source.raw (first.substitute morphism.substitution)
      (second.substitute morphism.substitution)) :=
  conclude (.substituteTypeEquality source.raw target.raw morphism.substitution first second)
    ⟨morphism.admitted, same, trivial⟩

theorem reindex_termEquality {source target : Context D} {first second : TermExpr S target.arity}
    {type : TypeExpr S target.arity} (same : Holds D (.termEq target.raw first second type))
    (morphism : source ⟶ target) : Holds D (.termEq source.raw
      (first.substitute morphism.substitution) (second.substitute morphism.substitution)
      (type.substitute morphism.substitution)) :=
  conclude (.substituteTermEquality source.raw target.raw morphism.substitution first second type)
    ⟨morphism.admitted, same, trivial⟩

def QType.reindex {source target : Context D} (type : QType target) (morphism : source ⟶ target) : QType source :=
  _root_.Quotient.map (fun formed => formed.reindex morphism)
    (fun _ _ same => reindex_typeEquality same morphism) type

@[simp] theorem QType.reindex_mk {source target : Context D} (type : TypeOver target)
    (morphism : source ⟶ target) : (QType.mk type).reindex morphism = QType.mk (type.reindex morphism) := rfl

theorem QType.reindex_id {context : Context D} (type : QType context) : type.reindex (𝟙 context) = type := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact congrArg QType.mk formed.reindex_id

theorem QType.reindex_comp {source middle target : Context D} (type : QType target)
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    type.reindex (earlier ≫ later) = (type.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact congrArg QType.mk (formed.reindex_comp earlier later)

theorem QType.reindex_congruent {source target : Context D} (type : QType target)
    {first second : source ⟶ target} (same : homEquality D first second) :
    type.reindex first = type.reindex second := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact _root_.Quotient.sound
    (conclude (.typeSubstitutionCongruence source.raw target.raw first.substitution
      second.substitution formed.code) ⟨same, formed.formed, trivial⟩)

def QTerm.reindex {source target : Context D} (term : QTerm target) (morphism : source ⟶ target) : QTerm source :=
  _root_.Quotient.map (sa := totalTermSetoid target) (sb := totalTermSetoid source)
    (fun value : TotalTerm target => value.reindex morphism)
    (fun _ _ same => ⟨reindex_typeEquality same.1 morphism, reindex_termEquality same.2 morphism⟩) term

@[simp] theorem QTerm.reindex_mk {source target : Context D} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) :
    (QTerm.mk term).reindex morphism = QTerm.mk (term.reindex morphism) := rfl

theorem QTerm.type_reindex {source target : Context D} (term : QTerm target) (morphism : source ⟶ target) :
    (term.reindex morphism).type = term.type.reindex morphism := by
  refine _root_.Quotient.inductionOn term fun _ => rfl

theorem QTerm.reindex_id {context : Context D} (term : QTerm context) : term.reindex (𝟙 context) = term := by
  refine _root_.Quotient.inductionOn term fun value => ?_
  apply (QTerm.mk_eq_iff _ _).mpr
  change Holds D (.typeEq context.raw (value.1.code.substitute TermExpr.var) value.1.code) ∧
    Holds D (.termEq context.raw (value.2.code.substitute TermExpr.var) value.2.code
      (value.1.code.substitute TermExpr.var))
  rw [TypeExpr.substitute_identity, TermExpr.substitute_identity]
  exact ⟨typeEquality_refl value.1, termEquality_refl value.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem QTerm.reindex_comp {source middle target : Context D} (term : QTerm target)
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    term.reindex (earlier ≫ later) = (term.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn term fun value => ?_
  apply (QTerm.mk_eq_iff _ _).mpr
  change Holds D (.typeEq source.raw
      (value.1.code.substitute (composeSubstitution later.substitution earlier.substitution))
      ((value.1.code.substitute later.substitution).substitute earlier.substitution)) ∧
    Holds D (.termEq source.raw
      (value.2.code.substitute (composeSubstitution later.substitution earlier.substitution))
      ((value.2.code.substitute later.substitution).substitute earlier.substitution)
      (value.1.code.substitute (composeSubstitution later.substitution earlier.substitution)))
  erw [← TypeExpr.substitute_comp, ← TermExpr.substitute_comp]
  exact ⟨typeEquality_refl ((value.1.reindex later).reindex earlier),
    termEquality_refl ((value.2.reindex later).reindex earlier)⟩

theorem QTerm.reindex_congruent {source target : Context D} (term : QTerm target)
    {first second : source ⟶ target} (same : homEquality D first second) :
    term.reindex first = term.reindex second := by
  refine _root_.Quotient.inductionOn term fun value => ?_
  exact _root_.Quotient.sound
    ⟨conclude (.typeSubstitutionCongruence source.raw target.raw first.substitution
      second.substitution value.1.code) ⟨same, value.1.formed, trivial⟩,
      conclude (.termSubstitutionCongruence source.raw target.raw first.substitution
        second.substitution value.2.code value.1.code) ⟨same, value.2.typed, trivial⟩⟩

theorem QTerm.mk_convertType {context : Context D} {first : TypeOver context}
    (term : Term context first) (second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    QTerm.mk (term.convertType second same) = QTerm.mk term :=
  _root_.Quotient.sound ⟨typeEquality_symm same, termEquality_refl (term.convertType second same)⟩

theorem QTerm.mk_cast {context : Context D} {first second : TypeOver context}
    (term : Term context first) (same : first = second) : QTerm.mk (term.cast same) = QTerm.mk term := by
  cases same
  rfl

def QType.rawPresheaf (D : Signature S) : (Context D)ᵒᵖ ⥤ Type u where
  obj context := QType context.unop
  map morphism := TypeCat.ofHom fun type => QType.reindex type morphism.unop
  map_id _ := by ext type; exact QType.reindex_id type
  map_comp first second := by ext type; exact QType.reindex_comp type second.unop first.unop

def QTerm.rawPresheaf (D : Signature S) : (Context D)ᵒᵖ ⥤ Type u where
  obj context := QTerm context.unop
  map morphism := TypeCat.ofHom fun term => QTerm.reindex term morphism.unop
  map_id _ := by ext term; exact QTerm.reindex_id term
  map_comp first second := by ext term; exact QTerm.reindex_comp term second.unop first.unop

def QType.presheaf (D : Signature S) : (quotientContext D)ᵒᵖ ⥤ Type u :=
  (_root_.CategoryTheory.Quotient.lift (homEquality D) (QType.rawPresheaf D).rightOp
    (fun _ _ _ _ same => Quiver.Hom.unop_inj
      (by ext type; exact QType.reindex_congruent type same))).leftOp

def QTerm.presheaf (D : Signature S) : (quotientContext D)ᵒᵖ ⥤ Type u :=
  (_root_.CategoryTheory.Quotient.lift (homEquality D) (QTerm.rawPresheaf D).rightOp
    (fun _ _ _ _ same => Quiver.Hom.unop_inj
      (by ext term; exact QTerm.reindex_congruent term same))).leftOp

@[simp] theorem QType.presheaf_map_projected {source target : Context D}
    (morphism : source ⟶ target) (type : QType target) :
    (QType.presheaf D).map ((quotientProjection D).map morphism).op type = type.reindex morphism := rfl

@[simp] theorem QTerm.presheaf_map_projected {source target : Context D}
    (morphism : source ⟶ target) (term : QTerm target) :
    (QTerm.presheaf D).map ((quotientProjection D).map morphism).op term = term.reindex morphism := rfl

theorem QTerm.presheaf_type_natural {source target : quotientContext D}
    (morphism : source ⟶ target) (term : QTerm target.as) :
    ((QTerm.presheaf D).map morphism.op term).type = (QType.presheaf D).map morphism.op term.type := by
  revert term
  refine Quot.inductionOn morphism (fun raw term => ?_)
  exact QTerm.type_reindex term raw

def typeProjection (D : Signature S) : QTerm.presheaf D ⟶ QType.presheaf D where
  app _ := TypeCat.ofHom QTerm.type
  naturality := by
    intro source target morphism
    ext term
    exact QTerm.presheaf_type_natural morphism.unop term

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual
