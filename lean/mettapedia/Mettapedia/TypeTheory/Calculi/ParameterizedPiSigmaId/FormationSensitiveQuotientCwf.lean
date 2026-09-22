import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualQuotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres
import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-! # Comprehension over formed conversion classes

The construction is parameterized by the declared rules and uses the existing
formation, substitution and conversion judgments. Concrete language controls
are separate consumers, not premises of these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientCwf

open _root_.CategoryTheory FormationSensitive
open Mettapedia.GSLT.Core.ContextualLadder

variable {Head : Type} {rules : Rules Head}

abbrev QContext (rules : Rules Head) := quotientContext rules

abbrev Ty (context : QContext rules) := QType context.as

abbrev Tm (context : QContext rules) (type : Ty context) :=
  { term : QTerm context.as // term.type = type }

noncomputable def typeRepresentative {context : Context rules} (type : QType context) :
    TypeOver context := Quotient.out type

theorem typeRepresentative_class {context : Context rules} (type : QType context) :
    QType.mk (typeRepresentative type) = type := Quotient.out_eq type

theorem cast_term_val {context : QContext rules} {first second : Ty context}
    (same : first = second) (castProof : Tm context first = Tm context second)
    (term : Tm context first) : (cast castProof term).val = term.val := by
  cases same
  rfl

/-- The quotient projection does not change the formed source or target. -/
abbrev project {source target : Context rules} (morphism : source ⟶ target) :
    (quotientProjection rules).obj source ⟶ (quotientProjection rules).obj target :=
  (quotientProjection rules).map morphism

noncomputable def representative {source target : QContext rules}
    (morphism : source ⟶ target) : source.as ⟶ target.as := Quot.out morphism

@[simp] theorem project_representative {source target : QContext rules}
    (morphism : source ⟶ target) : project (representative morphism) = morphism :=
  Quot.out_eq morphism

theorem type_reindex_congruent {source target : Context rules}
    (type : QType target) {first second : source ⟶ target}
    (converted : homConversion rules first second) :
    type.reindex first = type.reindex second := by
  induction type using Quotient.inductionOn with
  | h type => exact Quotient.sound (Conv.substitutePointwise converted type.code)

theorem term_reindex_congruent {source target : Context rules}
    (term : QTerm target) {first second : source ⟶ target}
    (converted : homConversion rules first second) :
    term.reindex first = term.reindex second := by
  induction term using Quotient.inductionOn with
  | h term =>
    exact Quotient.sound
      ⟨Conv.substitutePointwise converted term.1.code,
        Conv.substitutePointwise converted term.2.code⟩

/-- Types depend on the substitution class, not its chosen representative. -/
def tySub {source target : QContext rules}
    (type : Ty target) (morphism : source ⟶ target) : Ty source :=
  Quot.liftOn morphism (fun raw => type.reindex raw) (by
    intro first second converted
    exact type_reindex_congruent type
      ((HomRel.compClosure_iff_self (homConversion rules) first second).mp converted))

def totalSub {source target : QContext rules}
    (term : QTerm target.as) (morphism : source ⟶ target) : QTerm source.as :=
  Quot.liftOn morphism (fun raw => term.reindex raw) (by
    intro first second converted
    exact term_reindex_congruent term
      ((HomRel.compClosure_iff_self (homConversion rules) first second).mp converted))

@[simp] theorem tySub_project {source target : Context rules} (type : QType target)
    (morphism : source ⟶ target) : tySub type (project morphism) = type.reindex morphism := rfl

@[simp] theorem totalSub_project {source target : Context rules} (term : QTerm target)
    (morphism : source ⟶ target) : totalSub term (project morphism) = term.reindex morphism := rfl

theorem tySub_presheaf {source target : QContext rules} (type : Ty target)
    (morphism : source ⟶ target) :
    tySub type morphism = (QType.presheaf rules).map morphism.op type := by
  induction morphism using Quot.inductionOn with
  | h raw => rfl

theorem totalSub_presheaf {source target : QContext rules} (term : QTerm target.as)
    (morphism : source ⟶ target) :
    totalSub term morphism = (QTerm.presheaf rules).map morphism.op term := by
  induction morphism using Quot.inductionOn with
  | h raw => rfl

theorem totalSub_type {source target : QContext rules} (term : QTerm target.as)
    (morphism : source ⟶ target) :
    (totalSub term morphism).type = tySub term.type morphism := by
  induction morphism using Quot.inductionOn with
  | h raw => exact QTerm.type_reindex term raw

def tmSub {source target : QContext rules} {type : Ty target}
    (term : Tm target type) (morphism : source ⟶ target) :
    Tm source (tySub type morphism) :=
  ⟨totalSub term.val morphism, by rw [totalSub_type, term.property]⟩

theorem tySub_id {context : QContext rules} (type : Ty context) :
    tySub type (𝟙 context) = type := by
  change type.reindex (𝟙 context.as) = type
  exact QType.reindex_id type

theorem tySub_comp {first middle last : QContext rules} (type : Ty last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    tySub type (earlier ≫ later) = tySub (tySub type later) earlier := by
  induction earlier using Quot.inductionOn with
  | h earlier =>
    induction later using Quot.inductionOn with
    | h later => exact QType.reindex_comp type earlier later

theorem totalSub_id {context : QContext rules} (term : QTerm context.as) :
    totalSub term (𝟙 context) = term := by
  change term.reindex (𝟙 context.as) = term
  exact QTerm.reindex_id term

theorem totalSub_comp {first middle last : QContext rules} (term : QTerm last.as)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    totalSub term (earlier ≫ later) = totalSub (totalSub term later) earlier := by
  induction earlier using Quot.inductionOn with
  | h earlier =>
    induction later using Quot.inductionOn with
    | h later => exact QTerm.reindex_comp term earlier later

/-- Any typed class over an actual formed annotation has a representative
admitted at that annotation. Conversion, not raw annotation equality,
provides the admission. -/
noncomputable def termRepresentative {context : Context rules} (type : TypeOver context)
    (term : QTerm context) (atType : term.type = QType.mk type) : Term context type :=
  let raw := term.out
  let sameType : QType.mk raw.1 = QType.mk type :=
    (congrArg QTerm.type (Quotient.out_eq term)).trans atType
  raw.2.convertType type ((QType.mk_eq_iff raw.1 type).mp sameType)

theorem termRepresentative_class {context : Context rules} (type : TypeOver context)
    (term : QTerm context) (atType : term.type = QType.mk type) :
    QTerm.mk (termRepresentative type term atType) = term := by
  let raw := term.out
  have sameType : QType.mk raw.1 = QType.mk type :=
    (congrArg QTerm.type (Quotient.out_eq term)).trans atType
  calc
    QTerm.mk (termRepresentative type term atType) = QTerm.mk raw.2 := by
      apply Quotient.sound
      exact ⟨((QType.mk_eq_iff raw.1 type).mp sameType).symm, .refl _⟩
    _ = term := Quotient.out_eq term

/-- A selected formed representative gives a real context extension. -/
noncomputable def ext (context : QContext rules) (type : Ty context) : QContext rules :=
  (quotientProjection rules).obj (extend context.as (typeRepresentative type))

noncomputable def wk {context : QContext rules} (type : Ty context) :
    ext context type ⟶ context :=
  project (projectionHom context.as (typeRepresentative type))

theorem represented_type_reindex {source target : QContext rules}
    (type : Ty target) (morphism : source ⟶ target) :
    QType.mk ((typeRepresentative type).reindex (representative morphism)) = tySub type morphism := by
  have changedType := congrArg
    (fun actual : QType target.as => actual.reindex (representative morphism))
    (typeRepresentative_class type)
  have changedArrow := congrArg (fun actual : source ⟶ target => tySub type actual)
    (project_representative morphism)
  exact changedType.trans changedArrow

noncomputable def vz {context : QContext rules} (type : Ty context) :
    Tm (ext context type) (tySub type (wk type)) :=
  ⟨QTerm.mk (newest context.as (typeRepresentative type)), by
    change tySub (QType.mk (typeRepresentative type)) (wk type) = tySub type (wk type)
    exact congrArg (fun A => tySub A (wk type)) (typeRepresentative_class type)⟩

noncomputable def pair {source target : QContext rules} (morphism : source ⟶ target)
    (type : Ty target) (term : Tm source (tySub type morphism)) :
    source ⟶ ext target type :=
  project (FormationSensitiveContextual.pair (representative morphism)
    (termRepresentative ((typeRepresentative type).reindex (representative morphism)) term.val
      (term.property.trans (represented_type_reindex type morphism).symm)))

theorem wk_pair {source target : QContext rules} (morphism : source ⟶ target)
    (type : Ty target) (term : Tm source (tySub type morphism)) :
    pair morphism type term ≫ wk type = morphism := by
  let admitted := termRepresentative
    ((typeRepresentative type).reindex (representative morphism)) term.val
    (term.property.trans (represented_type_reindex type morphism).symm)
  exact ((quotientProjection rules).map_comp
      (FormationSensitiveContextual.pair (representative morphism) admitted)
      (projectionHom target.as (typeRepresentative type))).symm.trans
    ((congrArg project (FormationSensitiveContextual.pair_projection
      (representative morphism) admitted)).trans (project_representative morphism))

theorem raw_newest_pair {source target : Context rules} (type : TypeOver target)
    (morphism : source ⟶ target) (term : Term source (type.reindex morphism)) :
    QTerm.mk ((newest target type).reindex (FormationSensitiveContextual.pair morphism term)) =
      QTerm.mk term := by
  apply Quotient.sound
  constructor
  · have same : (type.reindex (projectionHom target type)).reindex
        (FormationSensitiveContextual.pair morphism term) = type.reindex morphism := by
      rw [← TypeOver.reindex_comp, FormationSensitiveContextual.pair_projection]
    change Conv rules.headEq
      (((type.reindex (projectionHom target type)).reindex
        (FormationSensitiveContextual.pair morphism term)).code)
      (type.reindex morphism).code rules.computation
    rw [same]
    exact .refl _
  · exact .refl _

theorem vz_pair_value {source target : QContext rules} (morphism : source ⟶ target)
    (type : Ty target) (term : Tm source (tySub type morphism)) :
    (tmSub (vz type) (pair morphism type term)).val = term.val := by
  let atType := term.property.trans (represented_type_reindex type morphism).symm
  exact (raw_newest_pair (typeRepresentative type) (representative morphism)
      (termRepresentative _ term.val atType)).trans (termRepresentative_class _ term.val atType)

theorem pair_unique {source target : QContext rules} (type : Ty target)
    (first second : source ⟶ ext target type)
    (sameBase : first ≫ wk type = second ≫ wk type)
    (sameTerm : (tmSub (vz type) first).val = (tmSub (vz type) second).val) :
    first = second := by
  induction first using Quot.inductionOn with
  | h first =>
    induction second using Quot.inductionOn with
    | h second =>
      apply (quotientProjection_map_eq_iff (rules := rules) first second).mpr
      have bases : homConversion rules
          (first ≫ projectionHom target.as (typeRepresentative type))
          (second ≫ projectionHom target.as (typeRepresentative type)) :=
        (quotientProjection_map_eq_iff (rules := rules) _ _).mp sameBase
      have terms := Quotient.exact sameTerm
      intro index
      refine Fin.cases ?_ ?_ index
      · exact terms.2
      · intro prior
        exact bases prior

theorem pair_eta {source target : QContext rules} (type : Ty target)
    (morphism : source ⟶ ext target type) :
    pair (morphism ≫ wk type) type
      ⟨(tmSub (vz type) morphism).val, by
        exact (tmSub (vz type) morphism).property.trans (tySub_comp type morphism (wk type)).symm⟩ = morphism := by
  apply pair_unique type
  · exact wk_pair _ _ _
  · exact vz_pair_value _ _ _

/-- The actual formed-context conversion quotient has all structural CwF
laws. Chosen type representatives affect raw context objects, not the
quotient-valued substitution and variable equations. -/
noncomputable def cwf (rules : Rules Head) : Cwf where
  Ctx := QContext rules
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

noncomputable def withTerminal (rules : Rules Head) : CwfWithTerminal where
  toCwf := cwf rules
  empty := (quotientProjection rules).obj (FormationSensitiveContextual.empty rules)
  toEmpty context := project (FormationSensitiveContextual.toEmpty context.as)
  toEmpty_unique := by
    intro context morphism
    induction morphism using Quot.inductionOn with
    | h raw =>
      exact congrArg project (FormationSensitiveContextual.toEmpty_unique context.as raw)

/-- The chosen class representative yields the same comprehension as any
actual formed annotation up to the explicit, code-preserving comparison.
No literal equality of the raw context objects is asserted. -/
noncomputable def extPresentation (context : Context rules) (type : TypeOver context) :
    ext ((quotientProjection rules).obj context) (QType.mk type) ≅
      (quotientProjection rules).obj (extend context type) :=
  (quotientProjection rules).mapIso
    (extensionComparison (typeRepresentative (QType.mk type)) type
      ((QType.mk_eq_iff _ _).mp (typeRepresentative_class (QType.mk type))))

theorem extPresentation_projection (context : Context rules) (type : TypeOver context) :
    (extPresentation context type).hom ≫ project (projectionHom context type) =
      wk (QType.mk type) := by
  let converted := (QType.mk_eq_iff _ _).mp (typeRepresentative_class (QType.mk type))
  exact ((quotientProjection rules).map_comp
      (extensionComparison (typeRepresentative (QType.mk type)) type converted).hom
      (projectionHom context type)).symm.trans
    (congrArg project (extensionComparison_projection _ _ converted))

#print axioms cwf
#print axioms withTerminal
#print axioms extPresentation_projection

end FormationSensitiveContextual.QuotientCwf
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
