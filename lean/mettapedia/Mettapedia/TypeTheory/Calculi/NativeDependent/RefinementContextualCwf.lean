import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualFibres
import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-!
# The mixed generated refinement contextual model

Substitution, type and total-term equations are all authored generated
judgments. A supplied term class is retyped at the chosen type representative
using actual generated conversion. Comprehension beta, eta and uniqueness are
earned for that selection. This constructs a category with families and a
terminal context; it does not assert arbitrary-model or classifying initiality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.QuotientCwf

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

universe u
variable {S : Symbols.{u}} {D : Signature S}

abbrev QContext (D : Signature S) := quotientContext D
abbrev Ty (context : QContext D) := QType context.as
abbrev Tm (context : QContext D) (type : Ty context) := {term : QTerm context.as // term.type = type}

noncomputable def typeRepresentative {context : Context D} (type : QType context) : TypeOver context :=
  Quotient.out type

theorem typeRepresentative_class {context : Context D} (type : QType context) :
    QType.mk (typeRepresentative type) = type := Quotient.out_eq type

theorem cast_term_val {context : QContext D} {first second : Ty context}
    (same : first = second) (castProof : Tm context first = Tm context second)
    (term : Tm context first) : (cast castProof term).val = term.val := by
  cases same
  rfl

abbrev project {source target : Context D} (morphism : source ⟶ target) :
    (quotientProjection D).obj source ⟶ (quotientProjection D).obj target :=
  (quotientProjection D).map morphism

noncomputable def representative {source target : QContext D} (morphism : source ⟶ target) :
    source.as ⟶ target.as := Quot.out morphism

@[simp] theorem project_representative {source target : QContext D} (morphism : source ⟶ target) :
    project (representative morphism) = morphism := Quot.out_eq morphism

def tySub {source target : QContext D} (type : Ty target) (morphism : source ⟶ target) : Ty source :=
  Quot.liftOn morphism (fun raw => type.reindex raw) (by
    intro first second same
    exact QType.reindex_congruent type
      ((HomRel.compClosure_iff_self (homEquality D) first second).mp same))

def totalSub {source target : QContext D} (term : QTerm target.as) (morphism : source ⟶ target) :
    QTerm source.as :=
  Quot.liftOn morphism (fun raw => term.reindex raw) (by
    intro first second same
    exact QTerm.reindex_congruent term
      ((HomRel.compClosure_iff_self (homEquality D) first second).mp same))

@[simp] theorem tySub_project {source target : Context D} (type : QType target) (morphism : source ⟶ target) :
    tySub type (project morphism) = type.reindex morphism := rfl

@[simp] theorem totalSub_project {source target : Context D} (term : QTerm target) (morphism : source ⟶ target) :
    totalSub term (project morphism) = term.reindex morphism := rfl

theorem tySub_presheaf {source target : QContext D} (type : Ty target) (morphism : source ⟶ target) :
    tySub type morphism = (QType.presheaf D).map morphism.op type := by
  induction morphism using Quot.inductionOn with
  | h raw => rfl

theorem totalSub_presheaf {source target : QContext D} (term : QTerm target.as) (morphism : source ⟶ target) :
    totalSub term morphism = (QTerm.presheaf D).map morphism.op term := by
  induction morphism using Quot.inductionOn with
  | h raw => rfl

theorem totalSub_type {source target : QContext D} (term : QTerm target.as) (morphism : source ⟶ target) :
    (totalSub term morphism).type = tySub term.type morphism := by
  induction morphism using Quot.inductionOn with
  | h raw => exact QTerm.type_reindex term raw

def tmSub {source target : QContext D} {type : Ty target} (term : Tm target type)
    (morphism : source ⟶ target) : Tm source (tySub type morphism) :=
  ⟨totalSub term.val morphism, (totalSub_type term.val morphism).trans
    (congrArg (fun type => tySub type morphism) term.property)⟩

theorem tySub_id {context : QContext D} (type : Ty context) : tySub type (𝟙 context) = type :=
  QType.reindex_id type

theorem totalSub_id {context : QContext D} (term : QTerm context.as) : totalSub term (𝟙 context) = term :=
  QTerm.reindex_id term

theorem tySub_comp {source middle target : QContext D} (type : Ty target)
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    tySub type (earlier ≫ later) = tySub (tySub type later) earlier := by
  induction earlier using Quot.inductionOn with
  | h earlier =>
    induction later using Quot.inductionOn with
    | h later => exact QType.reindex_comp type earlier later

theorem totalSub_comp {source middle target : QContext D} (term : QTerm target.as)
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    totalSub term (earlier ≫ later) = totalSub (totalSub term later) earlier := by
  induction earlier using Quot.inductionOn with
  | h earlier =>
    induction later using Quot.inductionOn with
    | h later => exact QTerm.reindex_comp term earlier later

/-- Selecting an annotation is followed by an actual authored conversion rule. -/
noncomputable def termRepresentative {context : Context D} (type : TypeOver context) (term : QTerm context)
    (atType : term.type = QType.mk type) : Term context type :=
  let raw := term.out
  let sameType := (congrArg QTerm.type (Quotient.out_eq term)).trans atType
  raw.2.convertType type ((QType.mk_eq_iff raw.1 type).mp sameType)

theorem termRepresentative_class {context : Context D} (type : TypeOver context) (term : QTerm context)
    (atType : term.type = QType.mk type) : QTerm.mk (termRepresentative type term atType) = term := by
  let sameType := (congrArg QTerm.type (Quotient.out_eq term)).trans atType
  let converted := (QType.mk_eq_iff term.out.1 type).mp sameType
  exact (QTerm.mk_convertType term.out.2 type converted).trans (Quotient.out_eq term)

noncomputable def ext (context : QContext D) (type : Ty context) : QContext D :=
  (quotientProjection D).obj (extend context.as (typeRepresentative type))

noncomputable def wk {context : QContext D} (type : Ty context) : ext context type ⟶ context :=
  project (projectionHom context.as (typeRepresentative type))

theorem represented_type_reindex {source target : QContext D} (type : Ty target) (morphism : source ⟶ target) :
    QType.mk ((typeRepresentative type).reindex (representative morphism)) = tySub type morphism := by
  calc
    _ = tySub (QType.mk (typeRepresentative type)) (project (representative morphism)) := rfl
    _ = _ := by rw [typeRepresentative_class, project_representative]; rfl

noncomputable def vz {context : QContext D} (type : Ty context) : Tm (ext context type) (tySub type (wk type)) :=
  ⟨QTerm.mk (newest context.as (typeRepresentative type)), by
    change QType.mk ((typeRepresentative type).reindex (projectionHom context.as (typeRepresentative type))) = _
    rw [← QType.reindex_mk, typeRepresentative_class]
    rfl⟩

noncomputable def pair {source target : QContext D} (morphism : source ⟶ target) (type : Ty target)
    (term : Tm source (tySub type morphism)) : source ⟶ ext target type :=
  let atType := term.property.trans (represented_type_reindex type morphism).symm
  project (Contextual.pair (representative morphism)
    (termRepresentative ((typeRepresentative type).reindex (representative morphism)) term.val atType))

theorem wk_pair {source target : QContext D} (morphism : source ⟶ target) (type : Ty target)
    (term : Tm source (tySub type morphism)) : pair morphism type term ≫ wk type = morphism := by
  let atType := term.property.trans (represented_type_reindex type morphism).symm
  let admitted := termRepresentative ((typeRepresentative type).reindex (representative morphism)) term.val atType
  exact ((quotientProjection D).map_comp (Contextual.pair (representative morphism) admitted)
      (projectionHom target.as (typeRepresentative type))).symm.trans
    ((congrArg project (Contextual.pair_projection (representative morphism) admitted)).trans
      (project_representative morphism))

theorem raw_newest_pair {source target : Context D} (type : TypeOver target) (morphism : source ⟶ target)
    (term : Term source (type.reindex morphism)) :
    QTerm.mk ((newest target type).reindex (Contextual.pair morphism term)) = QTerm.mk term := by
  apply (QTerm.mk_eq_iff _ _).mpr
  have same : (type.reindex (projectionHom target type)).reindex (Contextual.pair morphism term) =
      type.reindex morphism := by rw [← TypeOver.reindex_comp, Contextual.pair_projection]
  constructor
  · rw [same]
    exact typeEquality_refl (type.reindex morphism)
  · change Holds D (.termEq source.raw term.code term.code
      (((type.reindex (projectionHom target type)).reindex (Contextual.pair morphism term)).code))
    rw [same]
    exact termEquality_refl term

theorem vz_pair_value {source target : QContext D} (morphism : source ⟶ target) (type : Ty target)
    (term : Tm source (tySub type morphism)) : (tmSub (vz type) (pair morphism type term)).val = term.val := by
  let atType := term.property.trans (represented_type_reindex type morphism).symm
  exact (raw_newest_pair (typeRepresentative type) (representative morphism)
      (termRepresentative _ term.val atType)).trans (termRepresentative_class _ term.val atType)

set_option backward.isDefEq.respectTransparency false in
/-- The newest component and every older component determine the actual arrow class. -/
theorem pair_unique {source target : QContext D} (type : Ty target)
    (first second : source ⟶ ext target type) (sameBase : first ≫ wk type = second ≫ wk type)
    (sameTerm : (tmSub (vz type) first).val = (tmSub (vz type) second).val) : first = second := by
  induction first using Quot.inductionOn with
  | h first =>
    induction second using Quot.inductionOn with
    | h second =>
      apply (quotientProjection_map_eq_iff first second).mpr
      have bases : homEquality D (first ≫ projectionHom target.as (typeRepresentative type))
          (second ≫ projectionHom target.as (typeRepresentative type)) :=
        (quotientProjection_map_eq_iff _ _).mp sameBase
      have terms := Quotient.exact sameTerm
      apply componentEquationsSubstitution source.as.formed (extend target.as (typeRepresentative type)).formed
        first.substitution second.substitution first.components second.components
        (substitutionGuards (extend target.as (typeRepresentative type)).formed first.admitted)
        (substitutionGuards (extend target.as (typeRepresentative type)).formed second.admitted)
      intro index
      cases index using Fin.cases with
      | zero =>
        have component := terms.2
        change Holds D (.termEq source.as.raw
          (first.substitution (0 : Fin (target.as.arity + 1)))
          (second.substitution (0 : Fin (target.as.arity + 1)))
          (((typeRepresentative type).code.substitute (fun index => .var index.succ)).substitute
            first.substitution)) at component
        rw [TypeExpr.substitute_variables] at component
        simpa only [ext, quotientProjection_obj_as, extend, ContextExpr.lookup_zero] using component
      | succ prior =>
        have component := substitutionComponentEquations target.as.formed bases prior
        change Holds D (.termEq source.as.raw (first.substitution prior.succ) (second.substitution prior.succ)
          ((target.as.raw.lookup prior).substitute (tail first.substitution))) at component
        simpa only [ext, quotientProjection_obj_as, extend, ContextExpr.lookup_succ, substitute_weaken] using component

theorem pair_eta {source target : QContext D} (type : Ty target) (morphism : source ⟶ ext target type) :
    pair (morphism ≫ wk type) type
      ⟨(tmSub (vz type) morphism).val, by
        exact (tmSub (vz type) morphism).property.trans (tySub_comp type morphism (wk type)).symm⟩ = morphism := by
  apply pair_unique type
  · exact wk_pair _ _ _
  · exact vz_pair_value _ _ _

noncomputable def cwf (D : Signature S) : Cwf.{u, u, u, u} where
  Ctx := QContext D
  Sub := fun source target => source ⟶ target
  idS context := 𝟙 context
  compS later earlier := earlier ≫ later
  id_comp morphism := Category.comp_id morphism
  comp_id morphism := Category.id_comp morphism
  comp_assoc later middle earlier := (Category.assoc earlier middle later).symm
  Ty := Ty
  tySub := tySub
  tySub_id := tySub_id
  tySub_comp type later earlier := tySub_comp type earlier later
  Tm := Tm
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

noncomputable def withTerminal (D : Signature S) : CwfWithTerminal.{u, u, u, u} where
  toCwf := cwf D
  empty := (quotientProjection D).obj (Contextual.empty D)
  toEmpty context := project (Contextual.toEmpty context.as)
  toEmpty_unique := by
    intro context morphism
    induction morphism using Quot.inductionOn with
    | h raw => exact congrArg project (Contextual.toEmpty_unique context.as raw)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.QuotientCwf
