import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SyntacticContextualCategory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity

/-! # Formation-sensitive contextual category

The construction is parameterized by the declared rules and uses the existing
formation, substitution and conversion judgments. Concrete language controls
are separate consumers, not premises of these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual

open _root_.CategoryTheory FormationSensitive

variable {Head : Type} {rules : Rules Head}

/-- Refined formation erases to the previously defined context formation;
the converse is neither assumed nor used. -/
theorem contextFormation_toRaw {n : Nat} {context : Ctx Head n}
    (formed : ContextFormation rules context) :
    Declaration.ContextWellFormed rules context := by
  induction formed with
  | nil => exact .nil
  | snoc _ type universeWitness prior =>
      exact .snoc prior type.toRaw universeWitness

structure Context (rules : Rules Head) where
  arity : Nat
  raw : Ctx Head arity
  formed : ContextFormation rules raw

def Context.toRaw (context : Context rules) : SyntacticContextual.FormedContext rules where
  arity := context.arity
  context := context.raw
  wellFormed := contextFormation_toRaw context.formed

structure Hom (source target : Context rules) where
  substitution : Sub Head target.arity source.arity
  typed : FormationSensitive.CtxMor rules target.raw source.raw substitution

@[ext] theorem Hom.ext {source target : Context rules} {first second : Hom source target}
    (same : first.substitution = second.substitution) : first = second := by
  cases first
  cases second
  cases same
  rfl

def Hom.toRaw {source target : Context rules} (morphism : Hom source target) :
    SyntacticContextual.ContextHom source.toRaw target.toRaw where
  substitution := morphism.substitution
  typed := morphism.typed.toRaw

theorem identityTyped {n : Nat} (context : Ctx Head n) :
    FormationSensitive.CtxMor rules context context ids := by
  intro index
  simpa only [subst_ids, ids] using (Typing.var (R := rules) (Γ := context) index)

theorem compositionTyped {n m k : Nat} {source : Ctx Head n} {middle : Ctx Head m}
    {target : Ctx Head k} {earlier : Sub Head m n} {later : Sub Head k m}
    (first : FormationSensitive.CtxMor rules middle source earlier)
    (second : FormationSensitive.CtxMor rules target middle later) :
    FormationSensitive.CtxMor rules target source (subComp earlier later) := by
  intro index
  change Typing rules source (subst earlier (later index))
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

def forget (rules : Rules Head) : Context rules ⥤ SyntacticContextual.FormedContext rules where
  obj := Context.toRaw
  map := Hom.toRaw

instance forget_faithful (rules : Rules Head) : (forget rules).Faithful where
  map_injective := by
    intro source target first second same
    exact Hom.ext (congrArg SyntacticContextual.ContextHom.substitution same)

theorem component_judgment {source target : Context rules} (morphism : source ⟶ target)
    (index : Fin target.arity) :
    Judgment rules source.raw (morphism.substitution index)
      (subst morphism.substitution (Ctx.lookup target.raw index)) :=
  ⟨source.formed, morphism.typed index⟩

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
  formed : Typing rules context.raw code (.head level)

@[ext] theorem TypeOver.ext {context : Context rules} {first second : TypeOver context}
    (sameCode : first.code = second.code) (sameLevel : first.level = second.level) :
    first = second := by
  cases first
  cases second
  cases sameCode
  cases sameLevel
  rfl

def TypeOver.toRaw {context : Context rules} (type : TypeOver context) :
    SyntacticContextual.TypeOver context.toRaw :=
  ⟨type.code, type.level, type.universeWitness, type.formed.toRaw⟩

theorem TypeOver.judgment {context : Context rules} (type : TypeOver context) :
    Judgment rules context.raw type.code (.head type.level) := ⟨context.formed, type.formed⟩

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

theorem TypeOver.toRaw_reindex {source target : Context rules} (type : TypeOver target)
    (morphism : source ⟶ target) :
    (type.reindex morphism).toRaw = type.toRaw.reindex morphism.toRaw := rfl

structure Term (context : Context rules) (type : TypeOver context) where
  code : Tm Head context.arity
  typed : Typing rules context.raw code type.code

@[ext] theorem Term.ext {context : Context rules} {type : TypeOver context}
    {first second : Term context type} (same : first.code = second.code) : first = second := by
  cases first
  cases second
  cases same
  rfl

theorem Term.judgment {context : Context rules} {type : TypeOver context}
    (term : Term context type) : Judgment rules context.raw term.code type.code :=
  ⟨context.formed, term.typed⟩

/-- Every actual judgment is represented, not merely judgments whose result
types were separately selected beforehand. Extracting that formed type uses
the existing regularity theorem's independent universe-rule premise. -/
theorem judgment_iff_term (context : Context rules) (regular : UniverseRegularity rules)
    (term type : Tm Head context.arity) :
    Judgment rules context.raw term type ↔
      ∃ formedType : TypeOver context, formedType.code = type ∧
        ∃ value : Term context formedType, value.code = term := by
  constructor
  · intro admitted
    obtain ⟨level, universeWitness, formed⟩ := admitted.regularity regular
    exact ⟨⟨type, level, universeWitness, formed.typing⟩, rfl,
      ⟨term, admitted.typing⟩, rfl⟩
  · rintro ⟨formedType, sameType, value, sameTerm⟩
    simpa only [sameType, sameTerm] using value.judgment

def Term.toRaw {context : Context rules} {type : TypeOver context} (term : Term context type) :
    SyntacticContextual.Term context.toRaw type.toRaw := ⟨term.code, term.typed.toRaw⟩

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

/-! ## Comprehension of the actual formed family -/

abbrev extend (context : Context rules) (type : TypeOver context) : Context rules :=
  ⟨context.arity + 1, .snoc context.raw type.code,
    .snoc context.formed type.formed type.universeWitness⟩

def projectionHom (context : Context rules) (type : TypeOver context) :
    extend context type ⟶ context where
  substitution := projection
  typed := by
    intro index
    change Typing rules (.snoc context.raw type.code) (.var index.succ)
      (subst projection (Ctx.lookup context.raw index))
    simpa only [subst_projection, Ctx.lookup_snoc_succ] using
      (Typing.var (R := rules) (Γ := .snoc context.raw type.code) index.succ)

def newest (context : Context rules) (type : TypeOver context) :
    Term (extend context type) (type.reindex (projectionHom context type)) where
  code := .var 0
  typed := by
    change Typing rules (.snoc context.raw type.code) (.var 0) (subst projection type.code)
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

/-- The formation-sensitive natural-model comprehension square, in its
pointwise representable form. Both directions retain refined judgments. -/
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


end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
