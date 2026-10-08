import Mettapedia.CategoryTheory.RelativeClosedSyntaxTranslationFunctor

/-!
# Composition of independently admitted expression translations

Raw composition substitutes complete first-stage target expressions through
the second translation, including all binder and equalizer annotations.
Identity and composition are proved on every raw constructor. The complete
generated-rule translation then earns the local admission of a composite.
Identity admission uses the actual authored primitive header derivations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax

open _root_.CategoryTheory

universe u v a w z b h r d

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {nextSymbols : Symbols.{b}}
variable {E : Type h} [Category.{r} E] {lastSymbols : Symbols.{d}}

def TranslationData.identity : TranslationData (C := C) (symbols := symbols)
    (D := C) (nextSymbols := symbols) where
  base := 𝟭 C
  objects := ObjectCode.name
  arrows := ArrowCode.name

def TranslationData.compose
    (first : TranslationData (C := C) (symbols := symbols) (D := D) (nextSymbols := nextSymbols))
    (last : TranslationData (C := D) (symbols := nextSymbols) (D := E) (nextSymbols := lastSymbols)) :
    TranslationData (C := C) (symbols := symbols) (D := E) (nextSymbols := lastSymbols) where
  base := first.base ⋙ last.base
  objects origin := (first.objects origin).translate last
  arrows origin := (first.arrows origin).translate last

mutual

theorem ObjectCode.translate_identity : (object : ObjectCode C symbols) →
    object.translate TranslationData.identity = object
  | .base _ => rfl
  | .name _ => rfl
  | .terminal => rfl
  | .product _ _ => by simp only [ObjectCode.translate, ObjectCode.translate_identity]
  | .exponential _ _ => by simp only [ObjectCode.translate, ObjectCode.translate_identity]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.translate, ObjectCode.translate_identity, ArrowCode.translate_identity]

theorem ArrowCode.translate_identity : (arrow : ArrowCode C symbols) →
    arrow.translate TranslationData.identity = arrow
  | .base _ => rfl
  | .name _ => rfl
  | .identity _ => by simp only [ArrowCode.translate, ObjectCode.translate_identity]
  | .compose _ _ => by simp only [ArrowCode.translate, ArrowCode.translate_identity]
  | .terminal _ => by simp only [ArrowCode.translate, ObjectCode.translate_identity]
  | .first _ _ => by simp only [ArrowCode.translate, ObjectCode.translate_identity]
  | .second _ _ => by simp only [ArrowCode.translate, ObjectCode.translate_identity]
  | .pair _ _ => by simp only [ArrowCode.translate, ArrowCode.translate_identity]
  | .evaluation _ _ => by simp only [ArrowCode.translate, ObjectCode.translate_identity]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.translate, ObjectCode.translate_identity, ArrowCode.translate_identity]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.translate, ObjectCode.translate_identity, ArrowCode.translate_identity]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.translate, ObjectCode.translate_identity, ArrowCode.translate_identity]

end

variable (first : TranslationData (C := C) (symbols := symbols) (D := D) (nextSymbols := nextSymbols))
variable (last : TranslationData (C := D) (symbols := nextSymbols) (D := E) (nextSymbols := lastSymbols))

mutual

theorem ObjectCode.translate_compose : (object : ObjectCode C symbols) →
    (object.translate first).translate last = object.translate (first.compose last)
  | .base _ => rfl
  | .name _ => rfl
  | .terminal => rfl
  | .product _ _ => by simp only [ObjectCode.translate, ObjectCode.translate_compose]
  | .exponential _ _ => by simp only [ObjectCode.translate, ObjectCode.translate_compose]
  | .equalizer _ _ _ _ => by
      simp only [ObjectCode.translate, ObjectCode.translate_compose, ArrowCode.translate_compose]

theorem ArrowCode.translate_compose : (arrow : ArrowCode C symbols) →
    (arrow.translate first).translate last = arrow.translate (first.compose last)
  | .base _ => rfl
  | .name _ => rfl
  | .identity _ => by simp only [ArrowCode.translate, ObjectCode.translate_compose]
  | .compose _ _ => by simp only [ArrowCode.translate, ArrowCode.translate_compose]
  | .terminal _ => by simp only [ArrowCode.translate, ObjectCode.translate_compose]
  | .first _ _ => by simp only [ArrowCode.translate, ObjectCode.translate_compose]
  | .second _ _ => by simp only [ArrowCode.translate, ObjectCode.translate_compose]
  | .pair _ _ => by simp only [ArrowCode.translate, ArrowCode.translate_compose]
  | .evaluation _ _ => by simp only [ArrowCode.translate, ObjectCode.translate_compose]
  | .curry _ _ _ _ => by
      simp only [ArrowCode.translate, ObjectCode.translate_compose, ArrowCode.translate_compose]
  | .equalizerArrow _ _ _ _ => by
      simp only [ArrowCode.translate, ObjectCode.translate_compose, ArrowCode.translate_compose]
  | .equalizerLift _ _ _ _ _ _ => by
      simp only [ArrowCode.translate, ObjectCode.translate_compose, ArrowCode.translate_compose]

end

theorem Judgment.translate_identity (judgment : Judgment C symbols) :
    judgment.translate TranslationData.identity = judgment := by
  cases judgment <;>
    simp only [Judgment.translate, ObjectCode.translate_identity, ArrowCode.translate_identity]

theorem Judgment.translate_compose (judgment : Judgment C symbols) :
    (judgment.translate first).translate last = judgment.translate (first.compose last) := by
  cases judgment <;>
    simp only [Judgment.translate, ObjectCode.translate_compose, ArrowCode.translate_compose]

variable {first last}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {next : Signature (C := D) (symbols := nextSymbols)}
variable {final : Signature (C := E) (symbols := lastSymbols)}

def Translation.identity (headers : HeaderFormation signature) : Translation signature signature where
  data := TranslationData.identity
  objectTyped origin := .objectName origin
  arrowTyped origin := by
    change Derivation signature (.arrow
      ((signature.source origin).translate TranslationData.identity)
      ((signature.target origin).translate TranslationData.identity) (.name origin))
    simpa only [ObjectCode.translate_identity] using
      Derivation.arrowName (signature := signature) origin (headers.source origin) (headers.target origin)
  equationTyped origin := by
    simpa only [ObjectCode.translate_identity, ArrowCode.translate_identity] using
      Derivation.declaredEquation (signature := signature) origin (headers.left origin) (headers.right origin)

def Translation.compose (first : Translation signature next) (last : Translation next final) :
    Translation signature final where
  data := first.data.compose last.data
  objectTyped origin := last.derivation (first.objectTyped origin)
  arrowTyped origin := by
    simpa only [Translation.judgment, Judgment.translate, ObjectCode.translate_compose,
      TranslationData.compose] using
      last.derivation (first.arrowTyped origin)
  equationTyped origin := by
    simpa only [Translation.judgment, Judgment.translate,
      ObjectCode.translate_compose, ArrowCode.translate_compose] using
      last.derivation (first.equationTyped origin)

namespace Translation

open GeneratedCategory

private theorem classOf_heq {source target before after : Object final}
    (first : RawHom source target) (second : RawHom before after)
    (sourceSame : source = before) (targetSame : target = after)
    (codes : first.code = second.code) : HEq (classOf first) (classOf second) := by
  subst before
  subst after
  exact heq_of_eq (congrArg classOf (RawHom.ext codes))

theorem object_identity (headers : HeaderFormation signature) (source : Object signature) :
    (identity headers).object source = source :=
  Object.ext (ObjectCode.translate_identity source.code)

theorem functor_identity (headers : HeaderFormation signature) :
    (identity headers).functor = 𝟭 (Object signature) := by
  refine _root_.CategoryTheory.Functor.hext
    (F := (identity headers).functor) (G := 𝟭 (Object signature))
    (object_identity headers) ?_
  intro source target arrow
  refine Quotient.inductionOn arrow ?_
  intro representative
  exact classOf_heq ((identity headers).rawArrow representative) representative
    (object_identity headers source) (object_identity headers target)
    (ArrowCode.translate_identity representative.code)

theorem object_compose (first : Translation signature next) (last : Translation next final)
    (source : Object signature) :
    last.object (first.object source) = (first.compose last).object source :=
  Object.ext (ObjectCode.translate_compose first.data last.data source.code)

theorem functor_compose (first : Translation signature next) (last : Translation next final) :
    first.functor ⋙ last.functor = (first.compose last).functor := by
  refine _root_.CategoryTheory.Functor.hext
    (F := first.functor ⋙ last.functor) (G := (first.compose last).functor)
    (object_compose first last) ?_
  intro source target arrow
  refine Quotient.inductionOn arrow ?_
  intro representative
  exact classOf_heq (last.rawArrow (first.rawArrow representative))
    ((first.compose last).rawArrow representative)
    (object_compose first last source) (object_compose first last target)
    (ArrowCode.translate_compose first.data last.data representative.code)

end Translation

end Mettapedia.CategoryTheory.RelativeClosedSyntax
