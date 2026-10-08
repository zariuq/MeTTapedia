import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualAssumptions
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualFibres

/-!
# Generated predicate fibres over mixed contexts

Predicate equality is the authored generated equation. Substitution descends
through both that equality and the actual substitution-arrow quotient.
Entailment remains generated proof inhabitation. These are the definable
predicates of the source calculus, rather than all subobjects of its category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

theorem predicateEquality_refl {context : Context D} (predicate : PredicateOver context) :
    Holds D (.predicateEq context.raw predicate.code predicate.code) :=
  conclude (.predicateReflexivity context.raw predicate.code) ⟨predicate.formed, trivial⟩

theorem predicateEquality_symm {context : Context D} {first second : PropExpr S context.arity}
    (same : Holds D (.predicateEq context.raw first second)) :
    Holds D (.predicateEq context.raw second first) :=
  conclude (.predicateSymmetry context.raw first second) ⟨same, trivial⟩

theorem predicateEquality_trans {context : Context D} {first middle last : PropExpr S context.arity}
    (earlier : Holds D (.predicateEq context.raw first middle))
    (later : Holds D (.predicateEq context.raw middle last)) :
    Holds D (.predicateEq context.raw first last) :=
  conclude (.predicateTransitivity context.raw first middle last) ⟨earlier, later, trivial⟩

def predicateSetoid (context : Context D) : Setoid (PredicateOver context) where
  r first second := Holds D (.predicateEq context.raw first.code second.code)
  iseqv := ⟨predicateEquality_refl, predicateEquality_symm, predicateEquality_trans⟩

def QPredicate (context : Context D) := _root_.Quotient (predicateSetoid context)

def QPredicate.mk {context : Context D} (predicate : PredicateOver context) : QPredicate context :=
  _root_.Quotient.mk _ predicate

theorem QPredicate.mk_eq_iff {context : Context D} (first second : PredicateOver context) :
    QPredicate.mk first = QPredicate.mk second ↔
      Holds D (.predicateEq context.raw first.code second.code) := _root_.Quotient.eq

def QPredicate.reindex {source target : Context D} (predicate : QPredicate target)
    (morphism : source ⟶ target) : QPredicate source :=
  _root_.Quotient.map (fun formed => formed.reindex morphism) (fun first second same =>
    conclude (.substitutePredicateEquality source.raw target.raw morphism.substitution
      first.code second.code) ⟨morphism.admitted, same, trivial⟩) predicate

@[simp] theorem QPredicate.reindex_mk {source target : Context D}
    (predicate : PredicateOver target) (morphism : source ⟶ target) :
    (QPredicate.mk predicate).reindex morphism = QPredicate.mk (predicate.reindex morphism) := rfl

theorem QPredicate.reindex_id {context : Context D} (predicate : QPredicate context) :
    predicate.reindex (𝟙 context) = predicate := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  exact congrArg QPredicate.mk formed.reindex_id

theorem QPredicate.reindex_comp {source middle target : Context D}
    (predicate : QPredicate target) (earlier : source ⟶ middle) (later : middle ⟶ target) :
    predicate.reindex (earlier ≫ later) = (predicate.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  exact congrArg QPredicate.mk (formed.reindex_comp earlier later)

theorem QPredicate.reindex_congruent {source target : Context D} (predicate : QPredicate target)
    {first second : source ⟶ target} (same : homEquality D first second) :
    predicate.reindex first = predicate.reindex second := by
  refine _root_.Quotient.inductionOn predicate fun formed => ?_
  exact _root_.Quotient.sound
    (conclude (.predicateSubstitutionCongruence source.raw target.raw first.substitution
      second.substitution formed.code) ⟨same, formed.formed, trivial⟩)

def QPredicate.rawPresheaf (D : Signature S) : (Context D)ᵒᵖ ⥤ Type u where
  obj context := QPredicate context.unop
  map morphism := TypeCat.ofHom fun predicate => QPredicate.reindex predicate morphism.unop
  map_id _ := by ext predicate; exact QPredicate.reindex_id predicate
  map_comp first second := by
    ext predicate
    exact QPredicate.reindex_comp predicate second.unop first.unop

def QPredicate.presheaf (D : Signature S) : (quotientContext D)ᵒᵖ ⥤ Type u :=
  (_root_.CategoryTheory.Quotient.lift (homEquality D) (QPredicate.rawPresheaf D).rightOp
    (fun _ _ _ _ same => Quiver.Hom.unop_inj
      (by ext predicate; exact QPredicate.reindex_congruent predicate same))).leftOp

@[simp] theorem QPredicate.presheaf_map_projected {source target : Context D}
    (morphism : source ⟶ target) (predicate : QPredicate target) :
    (QPredicate.presheaf D).map ((quotientProjection D).map morphism).op predicate =
      predicate.reindex morphism := rfl

def QPredicate.entails {context : Context D} (predicate : QPredicate context) : Prop :=
  _root_.Quotient.lift (fun formed : PredicateOver context => Holds D (.entails context.raw formed.code))
    (fun first second same => propext ⟨
      fun evidence => conclude (.entailmentConversion context.raw first.code second.code)
        ⟨same, evidence, trivial⟩,
      fun evidence => conclude (.entailmentConversion context.raw second.code first.code)
        ⟨predicateEquality_symm same, evidence, trivial⟩⟩) predicate

@[simp] theorem QPredicate.entails_mk {context : Context D} (predicate : PredicateOver context) :
    (QPredicate.mk predicate).entails ↔ Holds D (.entails context.raw predicate.code) := Iff.rfl

theorem QPredicate.entails_reindex {source target : Context D} {predicate : QPredicate target}
    (evidence : predicate.entails) (morphism : source ⟶ target) :
    (predicate.reindex morphism).entails := by
  revert evidence
  refine _root_.Quotient.inductionOn predicate fun formed evidence => ?_
  exact conclude (.substituteEntailment source.raw target.raw morphism.substitution formed.code)
    ⟨morphism.admitted, evidence, trivial⟩

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual
