import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualFibres
import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-!
# Dependent comprehension on typed context equations

The context category, type fibres and total-term fibres all use the typed
judgments. Selecting a type-class representative is followed by actual
retyping of the supplied term using typed equality. The quotient substitution
laws and comprehension beta and eta equations are proved for these choices;
no equality of chosen raw annotations is imposed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual.QuotientCwf

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization
open Mettapedia.GSLT.Core.ContextualLadder

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}

abbrev QContext (rules : Rules Head) := quotientContext rules

variable (levels : LevelModel rules L)

abbrev Ty (context : QContext rules) := QType levels context.as
abbrev Tm (context : QContext rules) (type : Ty levels context) :=
  { term : QTerm levels context.as // term.type = type }

variable {levels}

noncomputable def typeRepresentative {context : Context rules} (type : QType levels context) :
    TypeOver context := Quotient.out type

theorem typeRepresentative_class {context : Context rules} (type : QType levels context) :
    QType.mk levels (typeRepresentative type) = type := Quotient.out_eq type

theorem cast_term_val {context : QContext rules} {first second : Ty levels context}
    (same : first = second) (castProof : Tm levels context first = Tm levels context second)
    (term : Tm levels context first) : (cast castProof term).val = term.val := by
  cases same
  rfl

abbrev project {source target : Context rules} (morphism : source ⟶ target) :
    (quotientProjection rules).obj source ⟶ (quotientProjection rules).obj target :=
  (quotientProjection rules).map morphism

noncomputable def representative {source target : QContext rules}
    (morphism : source ⟶ target) : source.as ⟶ target.as := Quot.out morphism

@[simp] theorem project_representative {source target : QContext rules}
    (morphism : source ⟶ target) : project (representative morphism) = morphism :=
  Quot.out_eq morphism

def tySub {source target : QContext rules}
    (type : Ty levels target) (morphism : source ⟶ target) : Ty levels source :=
  Quot.liftOn morphism (fun raw => type.reindex raw) (by
    intro first second same
    exact QType.reindex_congruent type
      ((HomRel.compClosure_iff_self (homTypedEquality rules) first second).mp same))

def totalSub {source target : QContext rules}
    (term : QTerm levels target.as) (morphism : source ⟶ target) : QTerm levels source.as :=
  Quot.liftOn morphism (fun raw => term.reindex raw) (by
    intro first second same
    exact QTerm.reindex_congruent term
      ((HomRel.compClosure_iff_self (homTypedEquality rules) first second).mp same))

@[simp] theorem tySub_project {source target : Context rules} (type : QType levels target)
    (morphism : source ⟶ target) : tySub type (project morphism) = type.reindex morphism := rfl

@[simp] theorem totalSub_project {source target : Context rules} (term : QTerm levels target)
    (morphism : source ⟶ target) : totalSub term (project morphism) = term.reindex morphism := rfl

theorem tySub_presheaf {source target : QContext rules} (type : Ty levels target)
    (morphism : source ⟶ target) :
    tySub type morphism = (QType.presheaf levels).map morphism.op type := by
  induction morphism using Quot.inductionOn with
  | h raw => rfl

theorem totalSub_presheaf {source target : QContext rules} (term : QTerm levels target.as)
    (morphism : source ⟶ target) :
    totalSub term morphism = (QTerm.presheaf levels).map morphism.op term := by
  induction morphism using Quot.inductionOn with
  | h raw => rfl

theorem totalSub_type {source target : QContext rules} (term : QTerm levels target.as)
    (morphism : source ⟶ target) : (totalSub term morphism).type = tySub term.type morphism := by
  induction morphism using Quot.inductionOn with
  | h raw => exact QTerm.type_reindex term raw

def tmSub {source target : QContext rules} {type : Ty levels target}
    (term : Tm levels target type) (morphism : source ⟶ target) :
    Tm levels source (tySub type morphism) :=
  ⟨totalSub term.val morphism, (totalSub_type term.val morphism).trans
    (congrArg (fun type => tySub type morphism) term.property)⟩

theorem tySub_id {context : QContext rules} (type : Ty levels context) :
    tySub type (𝟙 context) = type := QType.reindex_id type

theorem totalSub_id {context : QContext rules} (term : QTerm levels context.as) :
    totalSub term (𝟙 context) = term := QTerm.reindex_id term

theorem tySub_comp {first middle last : QContext rules} (type : Ty levels last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    tySub type (earlier ≫ later) = tySub (tySub type later) earlier := by
  induction earlier using Quot.inductionOn with
  | h earlier =>
    induction later using Quot.inductionOn with
    | h later => exact QType.reindex_comp type earlier later

theorem totalSub_comp {first middle last : QContext rules} (term : QTerm levels last.as)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    totalSub term (earlier ≫ later) = totalSub (totalSub term later) earlier := by
  induction earlier using Quot.inductionOn with
  | h earlier =>
    induction later using Quot.inductionOn with
    | h later => exact QTerm.reindex_comp term earlier later

/-- The supplied class has an actual term representative at the selected
annotation because typed conversion is an admission rule of this category. -/
noncomputable def termRepresentative {context : Context rules} (type : TypeOver context)
    (term : QTerm levels context) (atType : term.type = QType.mk levels type) : Term context type :=
  let raw := term.out
  let sameType := (congrArg (QTerm.type levels) (Quotient.out_eq term)).trans atType
  raw.2.convertType type ((QType.mk_eq_iff levels raw.1 type).mp sameType)

theorem termRepresentative_class {context : Context rules} (type : TypeOver context)
    (term : QTerm levels context) (atType : term.type = QType.mk levels type) :
    QTerm.mk levels (termRepresentative type term atType) = term := by
  let sameType := (congrArg (QTerm.type levels) (Quotient.out_eq term)).trans atType
  let converted := (QType.mk_eq_iff levels term.out.1 type).mp sameType
  exact (QTerm.mk_convertType term.out.2 type converted).trans (Quotient.out_eq term)

noncomputable def ext (context : QContext rules) (type : Ty levels context) : QContext rules :=
  (quotientProjection rules).obj (extend context.as (typeRepresentative type))

noncomputable def wk {context : QContext rules} (type : Ty levels context) :
    ext context type ⟶ context := project (projectionHom context.as (typeRepresentative type))

theorem represented_type_reindex {source target : QContext rules}
    (type : Ty levels target) (morphism : source ⟶ target) :
    QType.mk levels ((typeRepresentative type).reindex (representative morphism)) =
      tySub type morphism := by
  calc
    _ = tySub (QType.mk levels (typeRepresentative type)) (project (representative morphism)) := rfl
    _ = _ := by rw [typeRepresentative_class, project_representative]; rfl

noncomputable def vz {context : QContext rules} (type : Ty levels context) :
    Tm levels (ext context type) (tySub type (wk type)) :=
  ⟨QTerm.mk levels (newest context.as (typeRepresentative type)), by
    change QType.mk levels ((typeRepresentative type).reindex
      (projectionHom context.as (typeRepresentative type))) = _
    rw [← QType.reindex_mk, typeRepresentative_class]
    rfl⟩

noncomputable def pair {source target : QContext rules} (morphism : source ⟶ target)
    (type : Ty levels target) (term : Tm levels source (tySub type morphism)) : source ⟶ ext target type :=
  let atType := term.property.trans (represented_type_reindex type morphism).symm
  project (TypedContextual.pair (representative morphism)
    (termRepresentative ((typeRepresentative type).reindex (representative morphism)) term.val atType))

theorem wk_pair {source target : QContext rules} (morphism : source ⟶ target)
    (type : Ty levels target) (term : Tm levels source (tySub type morphism)) :
    pair morphism type term ≫ wk type = morphism := by
  let atType := term.property.trans (represented_type_reindex type morphism).symm
  let admitted := termRepresentative ((typeRepresentative type).reindex (representative morphism)) term.val atType
  exact ((quotientProjection rules).map_comp (TypedContextual.pair (representative morphism) admitted)
      (projectionHom target.as (typeRepresentative type))).symm.trans
    ((congrArg project (TypedContextual.pair_projection (representative morphism) admitted)).trans
      (project_representative morphism))

theorem raw_newest_pair {source target : Context rules} (type : TypeOver target)
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    QTerm.mk levels ((newest target type).reindex (TypedContextual.pair morphism term)) =
      QTerm.mk levels term := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  have same : (type.reindex (projectionHom target type)).reindex
      (TypedContextual.pair morphism term) = type.reindex morphism := by
    rw [← TypeOver.reindex_comp, TypedContextual.pair_projection]
  constructor
  · rw [same]
    exact (type.reindex morphism).isType.refl
  · change Equal rules source.raw term.code term.code
      (((type.reindex (projectionHom target type)).reindex
        (TypedContextual.pair morphism term)).code)
    rw [same]
    exact .refl term.typed

theorem vz_pair_value {source target : QContext rules} (morphism : source ⟶ target)
    (type : Ty levels target) (term : Tm levels source (tySub type morphism)) :
    (tmSub (vz type) (pair morphism type term)).val = term.val := by
  let atType := term.property.trans (represented_type_reindex type morphism).symm
  exact (raw_newest_pair (typeRepresentative type) (representative morphism)
      (termRepresentative _ term.val atType)).trans (termRepresentative_class _ term.val atType)

set_option backward.isDefEq.respectTransparency false in
theorem pair_unique {source target : QContext rules} (type : Ty levels target)
    (first second : source ⟶ ext target type)
    (sameBase : first ≫ wk type = second ≫ wk type)
    (sameTerm : (tmSub (vz type) first).val = (tmSub (vz type) second).val) : first = second := by
  induction first using Quot.inductionOn with
  | h first =>
    induction second using Quot.inductionOn with
    | h second =>
      apply (quotientProjection_map_eq_iff (rules := rules) first second).mpr
      have bases : homTypedEquality rules
          (first ≫ projectionHom target.as (typeRepresentative type))
          (second ≫ projectionHom target.as (typeRepresentative type)) :=
        (quotientProjection_map_eq_iff (rules := rules) _ _).mp sameBase
      have terms := Quotient.exact sameTerm
      refine ⟨first.typed, ?_⟩
      intro index
      refine Fin.cases ?_ ?_ index
      · have component := terms.2
        change Equal rules source.as.raw
          (subst first.substitution (.var (0 : Fin (target.as.arity + 1))))
          (subst second.substitution (.var (0 : Fin (target.as.arity + 1))))
          (subst first.substitution (subst projection (typeRepresentative type).code)) at component
        rw [subst_projection] at component
        simpa only [ext, quotientProjection_obj_as, extend, Ctx.lookup_snoc_zero, subst] using component
      · intro prior
        have component := bases.2 prior
        change Equal rules source.as.raw (first.substitution prior.succ) (second.substitution prior.succ)
          (subst (subComp first.substitution projection) (Ctx.lookup target.as.raw prior)) at component
        rw [← subst_subComp, subst_projection] at component
        simpa only [ext, quotientProjection_obj_as, extend, Ctx.lookup_snoc_succ] using component

theorem pair_eta {source target : QContext rules} (type : Ty levels target)
    (morphism : source ⟶ ext target type) :
    pair (morphism ≫ wk type) type
      ⟨(tmSub (vz type) morphism).val, by
        exact (tmSub (vz type) morphism).property.trans (tySub_comp type morphism (wk type)).symm⟩ = morphism := by
  apply pair_unique type
  · exact wk_pair _ _ _
  · exact vz_pair_value _ _ _

noncomputable def cwf (levels : LevelModel rules L) : Cwf where
  Ctx := QContext rules
  Sub := fun source target => source ⟶ target
  idS context := 𝟙 context
  compS later earlier := earlier ≫ later
  id_comp morphism := Category.comp_id morphism
  comp_id morphism := Category.id_comp morphism
  comp_assoc later middle earlier := (Category.assoc earlier middle later).symm
  Ty := Ty levels
  tySub := tySub
  tySub_id := tySub_id
  tySub_comp type later earlier := tySub_comp type earlier later
  Tm := Tm levels
  tmSub := tmSub
  tmSub_id term := by
    apply Subtype.ext
    rw [cast_term_val (tySub_id _).symm]
    exact totalSub_id term.val
  tmSub_comp term later earlier := by
    apply Subtype.ext
    rw [cast_term_val (tySub_comp _ earlier later).symm]
    exact totalSub_comp term.val earlier later
  ext := ext
  wk := wk
  vz := vz
  pair := pair
  wk_pair := wk_pair
  vz_pair morphism type term := by
    apply Subtype.ext
    rw [cast_term_val (by rw [← tySub_comp, wk_pair])]
    exact vz_pair_value morphism type term
  pair_eta type morphism := by
    apply pair_unique type
    · exact wk_pair _ _ _
    · rw [vz_pair_value, cast_term_val (tySub_comp type morphism (wk type)).symm]

noncomputable def withTerminal (levels : LevelModel rules L) : CwfWithTerminal where
  toCwf := cwf levels
  empty := (quotientProjection rules).obj (TypedContextual.empty rules)
  toEmpty context := project (TypedContextual.toEmpty context.as)
  toEmpty_unique := by
    intro context morphism
    induction morphism using Quot.inductionOn with
    | h raw => exact congrArg project (TypedContextual.toEmpty_unique context.as raw)

end TypedContextual.QuotientCwf
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
