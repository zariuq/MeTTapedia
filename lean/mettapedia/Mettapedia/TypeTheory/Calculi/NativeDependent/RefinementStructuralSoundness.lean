import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundnessFormation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractStructuralSoundness

/-!
# Structural rules and equations have actual model readouts

Authored substitutions are interpreted componentwise and composed as genuine
model arrows. Context and annotation conversion use equality of independently
evaluated model data. Typed equation substitution follows the proved complete
syntax/model substitution theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualSumComprehension (sigma_second_heq)

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

attribute [local irreducible] products sums TypeOver.extensionSubstitution
  ContextualSumComprehension.normalize ContextualSumComprehension.reindexBody

variable (model : ModelData S C) {n k l : Nat}

theorem substitutionNil_sound (context : ContextExpr S n)
    (interpreted : Interprets model (.context context)) :
    Interprets model (.substitution context .nil Fin.elim0) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionNil_sound model.toAbstract context interpreted.toAbstract)

theorem substitutionExtend_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (type : TypeExpr S k)
    (substitution : Substitution S k n) (term : TermExpr S n)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (typeInterpreted : Interprets model (.type target type))
    (termInterpreted : Interprets model (.term source term (type.substitute substitution))) :
    Interprets model (.substitution source (.snoc target type) (extendSubstitution substitution term)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionExtend_sound model.toAbstract (model.stable_toAbstract stable) source
      target type substitution term substitutionInterpreted.toAbstract typeInterpreted.toAbstract
      termInterpreted.toAbstract)

theorem substitutionIdentity_sound (context : ContextExpr S n)
    (interpreted : Interprets model (.context context)) :
    Interprets model (.substitution context context TermExpr.var) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionIdentity_sound model.toAbstract context interpreted.toAbstract)

theorem substitutionCompose_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (middle : ContextExpr S k) (target : ContextExpr S l)
    (first : Substitution S k n) (second : Substitution S l k)
    (firstInterpreted : Interprets model (.substitution source middle first))
    (secondInterpreted : Interprets model (.substitution middle target second)) :
    Interprets model (.substitution source target (composeSubstitution second first)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionCompose_sound model.toAbstract (model.stable_toAbstract stable) source
      middle target first second firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem substitutionWeaken_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (interpreted : Interprets model (.type context type)) :
    Interprets model (.substitution (.snoc context type) context (fun index => .var index.succ)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionWeaken_sound model.toAbstract context type interpreted.toAbstract)

theorem substituteType_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (substitution : Substitution S k n)
    (type : TypeExpr S k) (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (typeInterpreted : Interprets model (.type target type)) :
    Interprets model (.type source (type.substitute substitution)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substituteType_sound model.toAbstract (model.stable_toAbstract stable) source
      target substitution type substitutionInterpreted.toAbstract typeInterpreted.toAbstract)

theorem substituteTerm_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (substitution : Substitution S k n)
    (term : TermExpr S k) (type : TypeExpr S k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (termInterpreted : Interprets model (.term target term type)) :
    Interprets model (.term source (term.substitute substitution) (type.substitute substitution)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substituteTerm_sound model.toAbstract (model.stable_toAbstract stable) source
      target substitution term type substitutionInterpreted.toAbstract termInterpreted.toAbstract)

theorem contextReflexivity_sound (context : ContextExpr S n)
    (interpreted : Interprets model (.context context)) : Interprets model (.contextEq context context) :=
  model.interprets_of_abstract
    (Abstract.ModelData.contextReflexivity_sound model.toAbstract context interpreted.toAbstract)

theorem contextSymmetry_sound (first second : ContextExpr S n)
    (interpreted : Interprets model (.contextEq first second)) : Interprets model (.contextEq second first) :=
  model.interprets_of_abstract
    (Abstract.ModelData.contextSymmetry_sound model.toAbstract first second interpreted.toAbstract)

theorem contextTransitivity_sound (first middle last : ContextExpr S n)
    (firstInterpreted : Interprets model (.contextEq first middle))
    (secondInterpreted : Interprets model (.contextEq middle last)) : Interprets model (.contextEq first last) :=
  model.interprets_of_abstract
    (Abstract.ModelData.contextTransitivity_sound model.toAbstract first middle last
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem contextExtendEquality_sound (first second : ContextExpr S n)
    (firstType secondType : TypeExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (typesInterpreted : Interprets model (.typeEq first firstType secondType)) :
    Interprets model (.contextEq (.snoc first firstType) (.snoc second secondType)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.contextExtendEquality_sound model.toAbstract first second firstType secondType
      contextsInterpreted.toAbstract typesInterpreted.toAbstract)

theorem transportType_sound (first second : ContextExpr S n) (type : TypeExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (typeInterpreted : Interprets model (.type first type)) : Interprets model (.type second type) :=
  model.interprets_of_abstract
    (Abstract.ModelData.transportType_sound model.toAbstract first second type
      contextsInterpreted.toAbstract typeInterpreted.toAbstract)

theorem transportTerm_sound (first second : ContextExpr S n) (term : TermExpr S n) (type : TypeExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (termInterpreted : Interprets model (.term first term type)) : Interprets model (.term second term type) :=
  model.interprets_of_abstract
    (Abstract.ModelData.transportTerm_sound model.toAbstract first second term type
      contextsInterpreted.toAbstract termInterpreted.toAbstract)

theorem transportSubstitution_sound (source source' : ContextExpr S n) (target target' : ContextExpr S k)
    (substitution : Substitution S k n)
    (sourcesInterpreted : Interprets model (.contextEq source source'))
    (targetsInterpreted : Interprets model (.contextEq target target'))
    (substitutionInterpreted : Interprets model (.substitution source target substitution)) :
    Interprets model (.substitution source' target' substitution) :=
  model.interprets_of_abstract
    (Abstract.ModelData.transportSubstitution_sound model.toAbstract source source' target target'
      substitution sourcesInterpreted.toAbstract targetsInterpreted.toAbstract
      substitutionInterpreted.toAbstract)

theorem typeReflexivity_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (interpreted : Interprets model (.type context type)) : Interprets model (.typeEq context type type) :=
  model.interprets_of_abstract
    (Abstract.ModelData.typeReflexivity_sound model.toAbstract context type interpreted.toAbstract)

theorem typeSymmetry_sound (context : ContextExpr S n) (first second : TypeExpr S n)
    (interpreted : Interprets model (.typeEq context first second)) : Interprets model (.typeEq context second first) :=
  model.interprets_of_abstract
    (Abstract.ModelData.typeSymmetry_sound model.toAbstract context first second interpreted.toAbstract)

theorem typeTransitivity_sound (context : ContextExpr S n) (first middle last : TypeExpr S n)
    (firstInterpreted : Interprets model (.typeEq context first middle))
    (secondInterpreted : Interprets model (.typeEq context middle last)) : Interprets model (.typeEq context first last) :=
  model.interprets_of_abstract
    (Abstract.ModelData.typeTransitivity_sound model.toAbstract context first middle last
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem termReflexivity_sound (context : ContextExpr S n) (term : TermExpr S n) (type : TypeExpr S n)
    (interpreted : Interprets model (.term context term type)) : Interprets model (.termEq context term term type) :=
  model.interprets_of_abstract
    (Abstract.ModelData.termReflexivity_sound model.toAbstract context term type interpreted.toAbstract)

theorem termSymmetry_sound (context : ContextExpr S n) (first second : TermExpr S n) (type : TypeExpr S n)
    (interpreted : Interprets model (.termEq context first second type)) :
    Interprets model (.termEq context second first type) :=
  model.interprets_of_abstract
    (Abstract.ModelData.termSymmetry_sound model.toAbstract context first second type
      interpreted.toAbstract)

theorem termTransitivity_sound (context : ContextExpr S n) (first middle last : TermExpr S n) (type : TypeExpr S n)
    (firstInterpreted : Interprets model (.termEq context first middle type))
    (secondInterpreted : Interprets model (.termEq context middle last type)) :
    Interprets model (.termEq context first last type) :=
  model.interprets_of_abstract
    (Abstract.ModelData.termTransitivity_sound model.toAbstract context first middle last type
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem equalityConversion_sound (context : ContextExpr S n) (first second : TermExpr S n)
    (firstType secondType : TypeExpr S n)
    (termsInterpreted : Interprets model (.termEq context first second firstType))
    (typesInterpreted : Interprets model (.typeEq context firstType secondType)) :
    Interprets model (.termEq context first second secondType) :=
  model.interprets_of_abstract
    (Abstract.ModelData.equalityConversion_sound model.toAbstract context first second firstType
      secondType termsInterpreted.toAbstract typesInterpreted.toAbstract)

theorem transportTypeEquality_sound (source target : ContextExpr S n) (first second : TypeExpr S n)
    (contextsInterpreted : Interprets model (.contextEq source target))
    (typesInterpreted : Interprets model (.typeEq source first second)) :
    Interprets model (.typeEq target first second) :=
  model.interprets_of_abstract
    (Abstract.ModelData.transportTypeEquality_sound model.toAbstract source target first second
      contextsInterpreted.toAbstract typesInterpreted.toAbstract)

theorem transportTermEquality_sound (source target : ContextExpr S n) (first second : TermExpr S n)
    (type : TypeExpr S n) (contextsInterpreted : Interprets model (.contextEq source target))
    (termsInterpreted : Interprets model (.termEq source first second type)) :
    Interprets model (.termEq target first second type) :=
  model.interprets_of_abstract
    (Abstract.ModelData.transportTermEquality_sound model.toAbstract source target first second type
      contextsInterpreted.toAbstract termsInterpreted.toAbstract)

theorem substituteTypeEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (substitution : Substitution S k n)
    (first second : TypeExpr S k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (typesInterpreted : Interprets model (.typeEq target first second)) :
    Interprets model (.typeEq source (first.substitute substitution) (second.substitute substitution)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substituteTypeEquality_sound model.toAbstract (model.stable_toAbstract stable)
      source target substitution first second substitutionInterpreted.toAbstract
      typesInterpreted.toAbstract)

theorem substituteTermEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (substitution : Substitution S k n)
    (first second : TermExpr S k) (type : TypeExpr S k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (termsInterpreted : Interprets model (.termEq target first second type)) :
    Interprets model (.termEq source (first.substitute substitution) (second.substitute substitution)
      (type.substitute substitution)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substituteTermEquality_sound model.toAbstract (model.stable_toAbstract stable)
      source target substitution first second type substitutionInterpreted.toAbstract
      termsInterpreted.toAbstract)

theorem substitutionReflexivity_sound (source : ContextExpr S n) (target : ContextExpr S k)
    (substitution : Substitution S k n)
    (interpreted : Interprets model (.substitution source target substitution)) :
    Interprets model (.substitutionEq source target substitution substitution) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionReflexivity_sound model.toAbstract source target substitution
      interpreted.toAbstract)

theorem substitutionSymmetry_sound (source : ContextExpr S n) (target : ContextExpr S k)
    (first second : Substitution S k n)
    (interpreted : Interprets model (.substitutionEq source target first second)) :
    Interprets model (.substitutionEq source target second first) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionSymmetry_sound model.toAbstract source target first second
      interpreted.toAbstract)

theorem substitutionTransitivity_sound (source : ContextExpr S n) (target : ContextExpr S k)
    (first middle last : Substitution S k n)
    (firstInterpreted : Interprets model (.substitutionEq source target first middle))
    (secondInterpreted : Interprets model (.substitutionEq source target middle last)) :
    Interprets model (.substitutionEq source target first last) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionTransitivity_sound model.toAbstract source target first middle last
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem substitutionExtendEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (type : TypeExpr S k)
    (first second : Substitution S k n) (firstTerm secondTerm : TermExpr S n)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (typeInterpreted : Interprets model (.type target type))
    (termsInterpreted : Interprets model (.termEq source firstTerm secondTerm (type.substitute first))) :
    Interprets model (.substitutionEq source (.snoc target type)
      (extendSubstitution first firstTerm) (extendSubstitution second secondTerm)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionExtendEquality_sound model.toAbstract (model.stable_toAbstract stable)
      source target type first second firstTerm secondTerm substitutionsInterpreted.toAbstract
      typeInterpreted.toAbstract termsInterpreted.toAbstract)

theorem typeSubstitutionCongruence_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (first second : Substitution S k n)
    (type : TypeExpr S k)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (typeInterpreted : Interprets model (.type target type)) :
    Interprets model (.typeEq source (type.substitute first) (type.substitute second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.typeSubstitutionCongruence_sound model.toAbstract (model.stable_toAbstract stable)
      source target first second type substitutionsInterpreted.toAbstract typeInterpreted.toAbstract)

theorem termSubstitutionCongruence_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S n) (target : ContextExpr S k) (first second : Substitution S k n)
    (term : TermExpr S k) (type : TypeExpr S k)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (termInterpreted : Interprets model (.term target term type)) :
    Interprets model (.termEq source (term.substitute first) (term.substitute second) (type.substitute first)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.termSubstitutionCongruence_sound model.toAbstract (model.stable_toAbstract stable)
      source target first second term type substitutionsInterpreted.toAbstract termInterpreted.toAbstract)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
