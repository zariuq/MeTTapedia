import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualQuantifierSubstitution

/-!
# Generated type images are existential support

The image predicate of an admitted type agrees with existential
quantification of truth. Both implications use actual image and existential
elimination rules. This comparison concerns entailment; it does not select a
data section from an image proof.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Quantifiers

open _root_.CategoryTheory
open AssumptionDisplays

universe u
variable {S : Symbols.{u}} {D : Signature S}

def rawImage {context : Context D} (domain : TypeOver context) : PredicateOver context :=
  ⟨.image domain.code, conclude (.imageFormation context.raw domain.code) ⟨domain.formed, trivial⟩⟩

def beforeBase {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    before context domain predicate ⟶ context :=
  projectionHom (assumed context predicate) (assumedType predicate domain) ≫
    assumptionInclusion context predicate

theorem beforeBase_tuple {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    (beforeBase domain predicate).substitution = fun index => .var index.succ := rfl

def beforeArgument {context : Context D} (domain : TypeOver context) (predicate : PredicateOver context) :
    Term (before context domain predicate) (domain.reindex (beforeBase domain predicate)) :=
  (newest (assumed context predicate) (assumedType predicate domain)).cast
    (TypeOver.ext (by
      change domain.code.substitute (fun index => .var index.succ) =
        domain.code.substitute (beforeBase domain predicate).substitution
      rw [beforeBase_tuple]))

theorem raw_image_le_support {context : Context D} (domain : TypeOver context) :
    Logic.RawOrder (rawImage domain) (rawExists domain (Logic.truth (extend context domain))) := by
  let assumption := rawImage domain
  let support := rawExists domain (Logic.truth (extend context domain))
  let base := beforeBase domain assumption
  let argument := beforeArgument domain assumption
  have guard : Holds D (.entails (before context domain assumption).raw
      ((Logic.truth (extend context domain)).reindex (Contextual.pair base argument)).code) :=
    conclude (.truthIntroduction (before context domain assumption).raw)
      ⟨(before context domain assumption).formed.judgment, trivial⟩
  have supplied := exists_introduce base (Logic.truth (extend context domain)) argument guard
  have branch : Holds D (.entails (before context domain assumption).raw
      (support.code.rename Fin.succ)) := by
    change Holds D (.entails (before context domain assumption).raw
      (support.code.substitute base.substitution)) at supplied
    rw [show base.substitution = fun index => .var index.succ from beforeBase_tuple _ _,
      PropExpr.substitute_variables] at supplied
    exact supplied
  exact conclude (.imageElimination (assumed context assumption).raw domain.code support.code)
    ⟨(assumedType assumption domain).formed, Logic.predicate_weaken assumption support,
      Logic.hypothesis assumption, branch, trivial⟩

theorem raw_support_le_image {context : Context D} (domain : TypeOver context) :
    Logic.RawOrder (rawExists domain (Logic.truth (extend context domain))) (rawImage domain) := by
  let assumption := rawExists domain (Logic.truth (extend context domain))
  let data := before context domain assumption
  let added := Logic.truth data
  let source := assumed data added
  let base := assumptionInclusion data added ≫ beforeBase domain assumption
  have tuple : base.substitution = fun index => .var index.succ := by
    change composeSubstitution (beforeBase domain assumption).substitution TermExpr.var = _
    exact (composeSubstitution_identity _).trans (beforeBase_tuple _ _)
  have typeFormed : Holds D (.type source.raw (domain.code.rename Fin.succ)) := by
    have supplied := (domain.reindex base).formed
    change Holds D (.type source.raw (domain.code.substitute base.substitution)) at supplied
    rw [tuple, TypeExpr.substitute_variables] at supplied
    exact supplied
  have newestTyped : Holds D (.term source.raw (.var 0) (domain.code.rename Fin.succ)) := by
    have supplied := conclude (.variable source.raw 0) ⟨source.formed.judgment, trivial⟩
    exact supplied
  have branch : Holds D (.entails source.raw ((rawImage domain).code.rename Fin.succ)) :=
    conclude (.imageIntroduction source.raw (domain.code.rename Fin.succ) (.var 0))
      ⟨typeFormed, newestTyped, trivial⟩
  exact conclude (.existentialElimination (assumed context assumption).raw domain.code .truth (.image domain.code))
    ⟨(assumedType assumption domain).formed, body_in_before domain (Logic.truth (extend context domain)) assumption,
      Logic.predicate_weaken assumption (rawImage domain), Logic.hypothesis assumption, branch, trivial⟩

theorem raw_image_support_equality {context : Context D} (domain : TypeOver context) :
    Holds D (.predicateEq context.raw (rawImage domain).code
      (rawExists domain (Logic.truth (extend context domain))).code) :=
  Logic.order_antisymm (raw_image_le_support domain) (raw_support_le_image domain)

def image {context : Context D} (domain : QType context) : QPredicate context :=
  _root_.Quotient.lift (fun formed => QPredicate.mk (rawImage formed))
    (fun first second same => _root_.Quotient.sound
      (conclude (.imageCongruence context.raw first.code second.code) ⟨same, trivial⟩)) domain

theorem image_support {context : Context D} (domain : TypeOver context) :
    image (QType.mk domain) = existsAt domain ⊤ :=
  _root_.Quotient.sound (raw_image_support_equality domain)

theorem image_reindex {source target : Context D} (morphism : source ⟶ target) (domain : QType target) :
    (image domain).reindex morphism = image (domain.reindex morphism) := by
  refine _root_.Quotient.inductionOn domain fun _ => rfl

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Quantifiers
