import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction

/-!
# Contexts and dependent comprehension admitted by typed equality

Context entries and substitution components are admitted by the typed
judgments, including typed conversion and function and pair eta. Families
carry explicit universe witnesses. Substitution and comprehension retain
these judgments before any quotient equations are imposed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization

variable {Head : Type} {rules : Rules Head}

structure Context (rules : Rules Head) where
  arity : Nat
  raw : Ctx Head arity
  formed : CtxFormed rules raw

structure Hom (source target : Context rules) where
  substitution : Sub Head target.arity source.arity
  typed : SubstMor rules target.raw source.raw substitution

@[ext] theorem Hom.ext {source target : Context rules} {first second : Hom source target}
    (same : first.substitution = second.substitution) : first = second := by
  cases first
  cases second
  cases same
  rfl

theorem identityTyped {n : Nat} (context : Ctx Head n) :
    SubstMor rules context context ids := by
  intro index
  simpa only [subst_ids, ids] using (Derivable.var (R := rules) (Γ := context) index)

theorem compositionTyped {n m k : Nat} {source : Ctx Head n} {middle : Ctx Head m}
    {target : Ctx Head k} {earlier : Sub Head m n} {later : Sub Head k m}
    (first : SubstMor rules middle source earlier)
    (second : SubstMor rules target middle later) :
    SubstMor rules target source (subComp earlier later) := by
  intro index
  change Typed rules source (subst earlier (later index))
    (subst (subComp earlier later) (Ctx.lookup target index))
  exact (subst_subComp earlier later (Ctx.lookup target index)) ▸ (second index).substitute first

instance contextCategory (rules : Rules Head) : Category (Context rules) where
  Hom := Hom
  id context := ⟨ids, identityTyped context.raw⟩
  comp first second :=
    ⟨subComp first.substitution second.substitution, compositionTyped first.typed second.typed⟩
  id_comp morphism := Hom.ext (subComp_ids_left morphism.substitution)
  comp_id morphism := Hom.ext (subComp_ids_right morphism.substitution)
  assoc first second third := Hom.ext
    (subComp_assoc first.substitution second.substitution third.substitution).symm

def empty (rules : Rules Head) : Context rules := ⟨0, .nil, .nil⟩

def toEmpty (source : Context rules) : source ⟶ empty rules :=
  ⟨Fin.elim0, fun index => Fin.elim0 index⟩

theorem toEmpty_unique (source : Context rules) (morphism : source ⟶ empty rules) :
    morphism = toEmpty source := by
  apply Hom.ext
  funext index
  exact Fin.elim0 index

@[reducible] def emptyTerminal (rules : Rules Head) :
    ∀ source : Context rules, Unique (source ⟶ empty rules) :=
  fun source => { default := toEmpty source, uniq := toEmpty_unique source }

/-! ## Reindexed formed types and terms -/

structure TypeOver (context : Context rules) where
  code : Tm Head context.arity
  level : Head
  universeWitness : rules.isUniverse level
  formed : Typed rules context.raw code (.head level)

@[ext] theorem TypeOver.ext {context : Context rules} {first second : TypeOver context}
    (sameCode : first.code = second.code) (sameLevel : first.level = second.level) :
    first = second := by
  cases first
  cases second
  cases sameCode
  cases sameLevel
  rfl

def TypeOver.reindex {source target : Context rules} (type : TypeOver target)
    (morphism : source ⟶ target) : TypeOver source where
  code := subst morphism.substitution type.code
  level := type.level
  universeWitness := type.universeWitness
  formed := type.formed.substitute morphism.typed

theorem TypeOver.reindex_id {context : Context rules} (type : TypeOver context) :
    type.reindex (𝟙 context) = type :=
  TypeOver.ext (subst_ids type.code) rfl

theorem TypeOver.reindex_comp {first middle last : Context rules} (type : TypeOver last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    type.reindex (earlier ≫ later) = (type.reindex later).reindex earlier :=
  TypeOver.ext (subst_subComp earlier.substitution later.substitution type.code).symm rfl

structure Term (context : Context rules) (type : TypeOver context) where
  code : Tm Head context.arity
  typed : Typed rules context.raw code type.code

@[ext] theorem Term.ext {context : Context rules} {type : TypeOver context}
    {first second : Term context type} (same : first.code = second.code) : first = second := by
  cases first
  cases second
  cases same
  rfl

def Term.reindex {source target : Context rules} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) : Term source (type.reindex morphism) :=
  ⟨subst morphism.substitution term.code, term.typed.substitute morphism.typed⟩

def Term.cast {context : Context rules} {first second : TypeOver context}
    (same : first = second) (term : Term context first) : Term context second := same ▸ term

@[simp] theorem Term.cast_code {context : Context rules} {first second : TypeOver context}
    (same : first = second) (term : Term context first) : (term.cast same).code = term.code := by
  cases same
  rfl

theorem Term.reindex_id {context : Context rules} {type : TypeOver context}
    (term : Term context type) : (term.reindex (𝟙 context)).cast type.reindex_id = term := by
  apply Term.ext
  rw [Term.cast_code]
  exact subst_ids term.code

theorem Term.reindex_comp {first middle last : Context rules} {type : TypeOver last}
    (term : Term last type) (earlier : first ⟶ middle) (later : middle ⟶ last) :
    (term.reindex (earlier ≫ later)).cast (type.reindex_comp earlier later) =
      (term.reindex later).reindex earlier := by
  apply Term.ext
  rw [Term.cast_code]
  exact (subst_subComp earlier.substitution later.substitution term.code).symm

/-- The selected annotation can be replaced by an actually typed-equal
annotation without retaining a raw-conversion admission requirement. -/
def Term.convertType {context : Context rules} {first : TypeOver context}
    (term : Term context first) (second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) : Term context second :=
  ⟨term.code, Typed.convType term.typed same⟩

@[simp] theorem Term.convertType_code {context : Context rules} {first : TypeOver context}
    (term : Term context first) (second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) :
    (term.convertType second same).code = term.code := rfl

theorem TypeOver.isType {context : Context rules} (type : TypeOver context) :
    IsType rules context.raw type.code := ⟨type.level, type.universeWitness, type.formed⟩

/-! ## Comprehension of the actual formed family -/

abbrev extend (context : Context rules) (type : TypeOver context) : Context rules :=
  ⟨context.arity + 1, .snoc context.raw type.code,
    .snoc context.formed ⟨type.level, type.universeWitness, type.formed⟩⟩

def projectionHom (context : Context rules) (type : TypeOver context) :
    extend context type ⟶ context where
  substitution := projection
  typed := by
    intro index
    change Typed rules (.snoc context.raw type.code) (.var index.succ)
      (subst projection (Ctx.lookup context.raw index))
    simpa only [subst_projection, Ctx.lookup_snoc_succ] using
      (Derivable.var (R := rules) (Γ := .snoc context.raw type.code) index.succ)

def newest (context : Context rules) (type : TypeOver context) :
    Term (extend context type) (type.reindex (projectionHom context type)) where
  code := .var 0
  typed := by
    change Typed rules (.snoc context.raw type.code) (.var 0) (subst projection type.code)
    rw [subst_projection]
    exact .var 0

def pair {source target : Context rules} {type : TypeOver target} (morphism : source ⟶ target)
    (term : Term source (type.reindex morphism)) : source ⟶ extend target type where
  substitution := consSub term.code morphism.substitution
  typed := by
    intro index
    refine Fin.cases ?_ ?_ index
    · simpa only [extend, consSub_zero, Ctx.lookup_snoc_zero, subst_consSub_rename_wk,
        TypeOver.reindex] using term.typed
    · intro prior
      simpa only [extend, consSub_succ, Ctx.lookup_snoc_succ, subst_consSub_rename_wk] using morphism.typed prior

@[simp] theorem pair_projection {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    pair morphism term ≫ projectionHom target type = morphism :=
  Hom.ext (subComp_consSub_projection term.code morphism.substitution)

def pulledNewest {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    Term source (type.reindex (morphism ≫ projectionHom target type)) :=
  ((newest target type).reindex morphism).cast
    (type.reindex_comp morphism (projectionHom target type)).symm

@[simp] theorem pulledNewest_code {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    (pulledNewest morphism).code = morphism.substitution 0 := by
  rw [pulledNewest, Term.cast_code]
  rfl

theorem pair_eta {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    pair (morphism ≫ projectionHom target type) (pulledNewest morphism) = morphism := by
  apply Hom.ext
  change consSub (pulledNewest morphism).code
    (subComp morphism.substitution projection) = morphism.substitution
  rw [pulledNewest_code]
  exact consSub_eta morphism.substitution

structure Element (source target : Context rules) (type : TypeOver target) where
  base : source ⟶ target
  term : Term source (type.reindex base)

@[ext] theorem Element.ext {source target : Context rules} {type : TypeOver target}
    {first second : Element source target type} (sameBase : first.base = second.base)
    (sameCode : first.term.code = second.term.code) : first = second := by
  cases first with
  | mk firstBase firstTerm =>
    cases second with
    | mk secondBase secondTerm =>
      dsimp at sameBase sameCode
      cases sameBase
      have sameTerm := Term.ext sameCode
      cases sameTerm
      rfl

def toComprehension {source target : Context rules} {type : TypeOver target}
    (element : Element source target type) : source ⟶ extend target type :=
  pair element.base element.term

def fromComprehension {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) : Element source target type :=
  ⟨morphism ≫ projectionHom target type, pulledNewest morphism⟩

theorem from_to {source target : Context rules} {type : TypeOver target}
    (element : Element source target type) :
    fromComprehension (toComprehension element) = element := by
  apply Element.ext
  · exact pair_projection element.base element.term
  · exact pulledNewest_code (pair element.base element.term)

theorem to_from {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ extend target type) :
    toComprehension (fromComprehension morphism) = morphism := pair_eta morphism

/-- The typed-admission natural-model comprehension square, in its
pointwise representable form. Both directions retain typed judgments. -/
def comprehensionEquiv (source target : Context rules) (type : TypeOver target) :
    Element source target type ≃ (source ⟶ extend target type) where
  toFun := toComprehension
  invFun := fromComprehension
  left_inv := from_to
  right_inv := to_from

def Element.precompose {first source target : Context rules} {type : TypeOver target}
    (element : Element source target type) (earlier : first ⟶ source) :
    Element first target type :=
  ⟨earlier ≫ element.base,
    (element.term.reindex earlier).cast (type.reindex_comp earlier element.base).symm⟩

theorem comprehension_natural {first source target : Context rules} {type : TypeOver target}
    (element : Element source target type) (earlier : first ⟶ source) :
    earlier ≫ toComprehension element = toComprehension (element.precompose earlier) := by
  apply Hom.ext
  simp only [toComprehension, pair, Element.precompose, Term.cast_code, Term.reindex]
  exact subComp_consSub earlier.substitution element.term.code element.base.substitution

theorem pair_distinguishes_codes {source target : Context rules} {type : TypeOver target}
    (morphism : source ⟶ target) {first second : Term source (type.reindex morphism)}
    (different : first.code ≠ second.code) : pair morphism first ≠ pair morphism second := by
  intro same
  exact different (congrFun (congrArg Hom.substitution same) 0)


end TypedContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
