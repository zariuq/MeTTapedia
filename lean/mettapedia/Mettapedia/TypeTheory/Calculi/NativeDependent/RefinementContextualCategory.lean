import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualSubstitution

/-!
# Admitted mixed native contexts and raw comprehension

Objects and arrows carry the actual authored formation and substitution
judgments. Families are generated mixed native types, with no universe code.
Pairing and its inverse are defined by simultaneous syntax substitution and
the newest variable, before the generated equation quotient is imposed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

structure Context (D : Signature S) where
  arity : Nat
  raw : ContextExpr S arity
  formed : Formed D raw

structure Hom (source target : Context D) where
  substitution : Substitution S target.arity source.arity
  admitted : Holds D (.substitution source.raw target.raw substitution)

@[ext] theorem Hom.ext {source target : Context D} {first second : Hom source target}
    (same : first.substitution = second.substitution) : first = second := by
  cases first
  cases second
  cases same
  rfl

instance contextCategory (D : Signature S) : Category (Context D) where
  Hom := Hom
  id context := ⟨TermExpr.var,
    conclude (.substitutionIdentity context.raw) ⟨context.formed.judgment, trivial⟩⟩
  comp first second := ⟨composeSubstitution second.substitution first.substitution,
    substitutionCompose first.admitted second.admitted⟩
  id_comp morphism := Hom.ext (composeSubstitution_identity morphism.substitution)
  comp_id morphism := Hom.ext (identity_composeSubstitution morphism.substitution)
  assoc first second third := Hom.ext
    (composeSubstitution_assoc third.substitution second.substitution first.substitution).symm

theorem Hom.components {source target : Context D} (morphism : source ⟶ target) :
    Components (D := D) source.raw target.raw morphism.substitution :=
  substitutionComponents target.formed morphism.admitted

def empty (D : Signature S) : Context D := ⟨0, .nil, .nil⟩

def toEmpty (source : Context D) : source ⟶ empty D :=
  ⟨Fin.elim0, conclude (.substitutionNil source.raw) ⟨source.formed.judgment, trivial⟩⟩

theorem toEmpty_unique (source : Context D) (morphism : source ⟶ empty D) :
    morphism = toEmpty source := by
  apply Hom.ext
  funext index
  exact Fin.elim0 index

structure TypeOver (context : Context D) where
  code : TypeExpr S context.arity
  formed : Holds D (.type context.raw code)

@[ext] theorem TypeOver.ext {context : Context D} {first second : TypeOver context}
    (same : first.code = second.code) : first = second := by
  cases first
  cases second
  cases same
  rfl

def TypeOver.reindex {source target : Context D} (type : TypeOver target)
    (morphism : source ⟶ target) : TypeOver source :=
  ⟨type.code.substitute morphism.substitution, typeSubstitute morphism.admitted type.formed⟩

theorem TypeOver.reindex_id {context : Context D} (type : TypeOver context) :
    type.reindex (𝟙 context) = type := TypeOver.ext (TypeExpr.substitute_identity type.code)

theorem TypeOver.reindex_comp {source middle target : Context D} (type : TypeOver target)
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    type.reindex (earlier ≫ later) = (type.reindex later).reindex earlier :=
  TypeOver.ext (TypeExpr.substitute_comp later.substitution earlier.substitution type.code).symm

structure Term (context : Context D) (type : TypeOver context) where
  code : TermExpr S context.arity
  typed : Holds D (.term context.raw code type.code)

@[ext] theorem Term.ext {context : Context D} {type : TypeOver context}
    {first second : Term context type} (same : first.code = second.code) : first = second := by
  cases first
  cases second
  cases same
  rfl

def Term.reindex {source target : Context D} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) : Term source (type.reindex morphism) :=
  ⟨term.code.substitute morphism.substitution, termSubstitute morphism.admitted term.typed⟩

def Term.cast {context : Context D} {first second : TypeOver context}
    (same : first = second) (term : Term context first) : Term context second := same ▸ term

@[simp] theorem Term.cast_code {context : Context D} {first second : TypeOver context}
    (same : first = second) (term : Term context first) : (term.cast same).code = term.code := by
  cases same
  rfl

def Term.convertType {context : Context D} {first : TypeOver context}
    (term : Term context first) (second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) : Term context second :=
  ⟨term.code, conclude (.termConversion context.raw term.code first.code second.code)
    ⟨term.typed, same, trivial⟩⟩

@[simp] theorem Term.convertType_code {context : Context D} {first : TypeOver context}
    (term : Term context first) (second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    (term.convertType second same).code = term.code := rfl

abbrev extend (context : Context D) (type : TypeOver context) : Context D :=
  ⟨context.arity + 1, .snoc context.raw type.code, .snoc context.formed type.formed⟩

def projectionHom (context : Context D) (type : TypeOver context) :
    extend context type ⟶ context :=
  ⟨fun index => .var index.succ,
    conclude (.substitutionWeaken context.raw type.code) ⟨type.formed, trivial⟩⟩

def newest (context : Context D) (type : TypeOver context) :
    Term (extend context type) (type.reindex (projectionHom context type)) where
  code := .var 0
  typed := by
    have entry := conclude (.variable (.snoc context.raw type.code) 0)
      ⟨(extend context type).formed.judgment, trivial⟩
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, TypeOver.reindex,
      projectionHom, TypeExpr.substitute_variables] using entry

def pair {source target : Context D} {type : TypeOver target} (morphism : source ⟶ target)
    (term : Term source (type.reindex morphism)) : source ⟶ extend target type :=
  ⟨extendSubstitution morphism.substitution term.code,
    conclude (.substitutionExtend source.raw target.raw type.code morphism.substitution term.code)
      ⟨morphism.admitted, type.formed, term.typed, trivial⟩⟩

@[simp] theorem pair_projection {source target : Context D} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    pair morphism term ≫ projectionHom target type = morphism := by
  apply Hom.ext
  rfl

def pulledNewest {source target : Context D} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    Term source (type.reindex (morphism ≫ projectionHom target type)) :=
  ((newest target type).reindex morphism).cast
    (type.reindex_comp morphism (projectionHom target type)).symm

@[simp] theorem pulledNewest_code {source target : Context D} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    (pulledNewest morphism).code = morphism.substitution 0 := by
  rw [pulledNewest, Term.cast_code]
  rfl

theorem pair_eta {source target : Context D} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    pair (morphism ≫ projectionHom target type) (pulledNewest morphism) = morphism := by
  apply Hom.ext
  change extendSubstitution (tail morphism.substitution) (pulledNewest morphism).code = _
  rw [pulledNewest_code]
  exact extend_tail morphism.substitution

structure Element (source target : Context D) (type : TypeOver target) where
  base : source ⟶ target
  term : Term source (type.reindex base)

@[ext] theorem Element.ext {source target : Context D} {type : TypeOver target}
    {first second : Element source target type} (sameBase : first.base = second.base)
    (sameCode : first.term.code = second.term.code) : first = second := by
  cases first with
  | mk firstBase firstTerm =>
    cases second with
    | mk secondBase secondTerm =>
      dsimp only at sameBase sameCode
      cases sameBase
      have sameTerm := Term.ext sameCode
      cases sameTerm
      rfl

def toComprehension {source target : Context D} {type : TypeOver target}
    (element : Element source target type) : source ⟶ extend target type := pair element.base element.term

def fromComprehension {source target : Context D} {type : TypeOver target}
    (morphism : source ⟶ extend target type) : Element source target type :=
  ⟨morphism ≫ projectionHom target type, pulledNewest morphism⟩

theorem from_to {source target : Context D} {type : TypeOver target} (element : Element source target type) :
    fromComprehension (toComprehension element) = element := by
  apply Element.ext
  · exact pair_projection element.base element.term
  · exact pulledNewest_code (pair element.base element.term)

def comprehensionEquiv (source target : Context D) (type : TypeOver target) :
    Element source target type ≃ (source ⟶ extend target type) where
  toFun := toComprehension
  invFun := fromComprehension
  left_inv := from_to
  right_inv := pair_eta

def Element.precompose {first source target : Context D} {type : TypeOver target}
    (element : Element source target type) (earlier : first ⟶ source) : Element first target type :=
  ⟨earlier ≫ element.base,
    (element.term.reindex earlier).cast (type.reindex_comp earlier element.base).symm⟩

theorem comprehension_natural {first source target : Context D} {type : TypeOver target}
    (element : Element source target type) (earlier : first ⟶ source) :
    earlier ≫ toComprehension element = toComprehension (element.precompose earlier) := by
  apply Hom.ext
  simp only [toComprehension, pair, Element.precompose, Term.cast_code, Term.reindex]
  exact composeSubstitution_extend element.base.substitution element.term.code earlier.substitution

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual
