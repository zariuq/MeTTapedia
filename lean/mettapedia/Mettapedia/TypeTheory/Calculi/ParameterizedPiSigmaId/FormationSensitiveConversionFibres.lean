import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualQuotient

/-! # Conversion classes of formed dependent fibres

The construction is parameterized by the declared rules and uses the existing
formation, substitution and conversion judgments. Concrete language controls
are separate consumers, not premises of these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual

open _root_.CategoryTheory FormationSensitive

variable {Head : Type} {rules : Rules Head}

/-- The selected universe witness is deliberately absent from this
level-free code relation. Both endpoint types are independently formed. -/
def typeCodeSetoid (context : Context rules) : Setoid (TypeOver context) where
  r first second := Conv rules.headEq first.code second.code rules.computation
  iseqv := ⟨fun _ => .refl _, fun converted => converted.symm,
    fun first second => .trans _ _ _ first second⟩

def QType (context : Context rules) := _root_.Quotient (typeCodeSetoid context)

def QType.mk {context : Context rules} (type : TypeOver context) : QType context :=
  _root_.Quotient.mk _ type

theorem QType.mk_eq_iff {context : Context rules} (first second : TypeOver context) :
    QType.mk first = QType.mk second ↔
      Conv rules.headEq first.code second.code rules.computation :=
  _root_.Quotient.eq

def TotalTerm (context : Context rules) := Σ type : TypeOver context, Term context type

/-- Keeping term conversion alone would discard the independently supplied
type annotation. This relation retains both conversion obligations. -/
def totalTermSetoid (context : Context rules) : Setoid (TotalTerm context) where
  r first second :=
    Conv rules.headEq first.1.code second.1.code rules.computation ∧
      Conv rules.headEq first.2.code second.2.code rules.computation
  iseqv := ⟨fun _ => ⟨.refl _, .refl _⟩,
    fun converted => ⟨converted.1.symm, converted.2.symm⟩,
    fun first second => ⟨.trans _ _ _ first.1 second.1, .trans _ _ _ first.2 second.2⟩⟩

def QTerm (context : Context rules) := _root_.Quotient (totalTermSetoid context)

def QTerm.mk {context : Context rules} {type : TypeOver context}
    (term : Term context type) : QTerm context := _root_.Quotient.mk _ ⟨type, term⟩

theorem QTerm.mk_eq_iff {context : Context rules} {first second : TypeOver context}
    (left : Term context first) (right : Term context second) :
    QTerm.mk left = QTerm.mk right ↔
      Conv rules.headEq first.code second.code rules.computation ∧
        Conv rules.headEq left.code right.code rules.computation :=
  _root_.Quotient.eq

def QTerm.type {context : Context rules} (term : QTerm context) : QType context :=
  _root_.Quotient.lift (s := totalTermSetoid context) (fun pair : TotalTerm context => QType.mk pair.1)
    (fun _ _ converted => _root_.Quotient.sound converted.1) term

@[simp] theorem QTerm.type_mk {context : Context rules} {type : TypeOver context}
    (term : Term context type) : (QTerm.mk term).type = QType.mk type := rfl

def QType.reindex {source target : Context rules} (type : QType target)
    (morphism : source ⟶ target) : QType source :=
  _root_.Quotient.map (sa := typeCodeSetoid target) (sb := typeCodeSetoid source)
    (fun formed => formed.reindex morphism)
    (fun _ _ converted => converted.substitute morphism.substitution) type

@[simp] theorem QType.reindex_mk {source target : Context rules} (type : TypeOver target)
    (morphism : source ⟶ target) :
    (QType.mk type).reindex morphism = QType.mk (type.reindex morphism) := rfl

theorem QType.reindex_id {context : Context rules} (type : QType context) :
    type.reindex (𝟙 context) = type := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact congrArg QType.mk formed.reindex_id

theorem QType.reindex_comp {first middle last : Context rules} (type : QType last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    type.reindex (earlier ≫ later) = (type.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact congrArg QType.mk (formed.reindex_comp earlier later)

/-- This is proved for the actual raw substitution, not assumed as a law
of the quotient action. No typing uniqueness is needed. -/
theorem QType.reindex_pointwise {source target : Context rules}
    (type : QType target) {first second : source ⟶ target}
    (pointwise : ∀ index, Conv rules.headEq (first.substitution index)
      (second.substitution index) rules.computation) :
    type.reindex first = type.reindex second := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact _root_.Quotient.sound (Conv.substitutePointwise pointwise formed.code)

def TotalTerm.reindex {source target : Context rules} (term : TotalTerm target)
    (morphism : source ⟶ target) : TotalTerm source :=
  ⟨term.1.reindex morphism, term.2.reindex morphism⟩

def QTerm.reindex {source target : Context rules} (term : QTerm target)
    (morphism : source ⟶ target) : QTerm source :=
  _root_.Quotient.map (sa := totalTermSetoid target) (sb := totalTermSetoid source)
    (fun pair => pair.reindex morphism)
    (fun _ _ converted => ⟨converted.1.substitute morphism.substitution,
      converted.2.substitute morphism.substitution⟩) term

@[simp] theorem QTerm.reindex_mk {source target : Context rules} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) :
    (QTerm.mk term).reindex morphism = QTerm.mk (term.reindex morphism) := rfl

theorem QTerm.type_reindex {source target : Context rules} (term : QTerm target)
    (morphism : source ⟶ target) :
    (term.reindex morphism).type = term.type.reindex morphism := by
  refine _root_.Quotient.inductionOn term fun _ => rfl

theorem QTerm.reindex_id {context : Context rules} (term : QTerm context) :
    term.reindex (𝟙 context) = term := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  apply _root_.Quotient.sound
  change Conv rules.headEq (subst ids pair.1.code) pair.1.code rules.computation ∧
    Conv rules.headEq (subst ids pair.2.code) pair.2.code rules.computation
  rw [subst_ids, subst_ids]
  exact ⟨.refl _, .refl _⟩

theorem QTerm.reindex_comp {first middle last : Context rules} (term : QTerm last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    term.reindex (earlier ≫ later) = (term.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  apply _root_.Quotient.sound
  change Conv rules.headEq (subst (subComp earlier.substitution later.substitution) pair.1.code)
      (subst earlier.substitution (subst later.substitution pair.1.code)) rules.computation ∧
    Conv rules.headEq (subst (subComp earlier.substitution later.substitution) pair.2.code)
      (subst earlier.substitution (subst later.substitution pair.2.code)) rules.computation
  rw [subst_subComp, subst_subComp]
  exact ⟨.refl _, .refl _⟩

theorem QTerm.reindex_pointwise {source target : Context rules}
    (term : QTerm target) {first second : source ⟶ target}
    (pointwise : ∀ index, Conv rules.headEq (first.substitution index)
      (second.substitution index) rules.computation) :
    term.reindex first = term.reindex second := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  exact _root_.Quotient.sound ⟨Conv.substitutePointwise pointwise pair.1.code,
    Conv.substitutePointwise pointwise pair.2.code⟩

/-- The old actual annotation-conversion operation acts on these classes;
neither annotation equality nor selection of a universe is needed. -/
theorem QTerm.mk_convertType {context : Context rules} {first : TypeOver context}
    (term : Term context first) (second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    QTerm.mk (term.convertType second converted) = QTerm.mk term :=
  _root_.Quotient.sound ⟨converted.symm, .refl _⟩

def TermFibre {context : Context rules} (type : QType context) :=
  { term : QTerm context // term.type = type }

def TermFibre.mk {context : Context rules} {type : TypeOver context}
    (term : Term context type) : TermFibre (QType.mk type) := ⟨QTerm.mk term, rfl⟩

def TermFibre.compare {context : Context rules} {first second : QType context}
    (same : first = second) : TermFibre first ≃ TermFibre second where
  toFun term := ⟨term.val, term.property.trans same⟩
  invFun term := ⟨term.val, term.property.trans same.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem TermFibre.compare_val {context : Context rules} {first second : QType context}
    (same : first = second) (term : TermFibre first) :
    (TermFibre.compare same term).val = term.val := rfl

theorem TermFibre.compare_refl {context : Context rules} {type : QType context}
    (term : TermFibre type) : TermFibre.compare rfl term = term := rfl

theorem TermFibre.compare_trans {context : Context rules} {first middle last : QType context}
    (earlier : first = middle) (later : middle = last) (term : TermFibre first) :
    TermFibre.compare later (TermFibre.compare earlier term) =
      TermFibre.compare (earlier.trans later) term := rfl

theorem TermFibre.compare_annotation {context : Context rules} {first second : TypeOver context}
    (converted : Conv rules.headEq first.code second.code rules.computation)
    (term : Term context first) :
    TermFibre.compare ((QType.mk_eq_iff first second).mpr converted) (TermFibre.mk term) =
      TermFibre.mk (term.convertType second converted) := by
  apply Subtype.ext
  exact (QTerm.mk_convertType term second converted).symm

def TermFibre.reindex {source target : Context rules} {type : QType target}
    (term : TermFibre type) (morphism : source ⟶ target) : TermFibre (type.reindex morphism) :=
  ⟨term.val.reindex morphism, (QTerm.type_reindex term.val morphism).trans
    (congrArg (fun type => type.reindex morphism) term.property)⟩

@[simp] theorem TermFibre.reindex_val {source target : Context rules} {type : QType target}
    (term : TermFibre type) (morphism : source ⟶ target) :
    (term.reindex morphism).val = term.val.reindex morphism := rfl

theorem TermFibre.reindex_id {context : Context rules} {type : QType context}
    (term : TermFibre type) :
    TermFibre.compare type.reindex_id (term.reindex (𝟙 context)) = term :=
  Subtype.ext (QTerm.reindex_id term.val)

theorem TermFibre.reindex_comp {first middle last : Context rules} {type : QType last}
    (term : TermFibre type) (earlier : first ⟶ middle) (later : middle ⟶ last) :
    TermFibre.compare (type.reindex_comp earlier later) (term.reindex (earlier ≫ later)) =
      (term.reindex later).reindex earlier :=
  Subtype.ext (QTerm.reindex_comp term.val earlier later)

theorem TermFibre.reindex_pointwise {source target : Context rules} {type : QType target}
    (term : TermFibre type) {first second : source ⟶ target}
    (pointwise : ∀ index, Conv rules.headEq (first.substitution index)
      (second.substitution index) rules.computation) :
    TermFibre.compare (QType.reindex_pointwise type pointwise) (term.reindex first) =
      term.reindex second :=
  Subtype.ext (QTerm.reindex_pointwise term.val pointwise)

theorem TermFibre.compare_reindex {source target : Context rules} {first second : QType target}
    (same : first = second) (term : TermFibre first) (morphism : source ⟶ target) :
    (TermFibre.compare same term).reindex morphism =
      TermFibre.compare (congrArg (fun type => type.reindex morphism) same)
        (term.reindex morphism) := rfl

/-- Every point of the class fibre is represented at any supplied formed
annotation in that class, using the actual refined conversion rule. This
does not choose an annotation or term globally. -/
theorem TermFibre.exists_term {context : Context rules} (type : TypeOver context)
    (term : TermFibre (QType.mk type)) :
    ∃ actual : Term context type, TermFibre.mk actual = term := by
  rcases term with ⟨term, annotated⟩
  induction term using _root_.Quotient.inductionOn with
  | _ pair =>
    change QType.mk pair.1 = QType.mk type at annotated
    let converted := (QType.mk_eq_iff pair.1 type).mp annotated
    refine ⟨pair.2.convertType type converted, ?_⟩
    apply Subtype.ext
    exact QTerm.mk_convertType pair.2 type converted

theorem TermFibre.mk_eq_iff {context : Context rules} {type : TypeOver context}
    (first second : Term context type) :
    TermFibre.mk first = TermFibre.mk second ↔
      Conv rules.headEq first.code second.code rules.computation := by
  constructor
  · intro same
    exact ((QTerm.mk_eq_iff first second).mp (congrArg Subtype.val same)).2
  · intro converted
    exact Subtype.ext (_root_.Quotient.sound ⟨.refl _, converted⟩)

/-- Level membership is independent of any selected quotient representative.
The witness is an actual type carrying refined formation at this head. -/
def QType.AtUniverse {context : Context rules} (type : QType context) (level : Head) : Prop :=
  ∃ formed : TypeOver context, QType.mk formed = type ∧ formed.level = level

theorem QType.atUniverse_mk {context : Context rules} (type : TypeOver context) :
    (QType.mk type).AtUniverse type.level := ⟨type, rfl, rfl⟩

theorem QType.AtUniverse.reindex {source target : Context rules} {type : QType target}
    {level : Head} (member : type.AtUniverse level) (morphism : source ⟶ target) :
    (type.reindex morphism).AtUniverse level := by
  obtain ⟨formed, same, rfl⟩ := member
  exact ⟨formed.reindex morphism, congrArg (fun type => type.reindex morphism) same, rfl⟩

theorem QType.AtUniverse.cumulative {context : Context rules} {type : QType context}
    {lower upper : Head} (member : type.AtUniverse lower)
    (cumulative : rules.cumulative lower upper) (universeWitness : rules.isUniverse upper) :
    type.AtUniverse upper := by
  obtain ⟨formed, same, level⟩ := member
  let raised : TypeOver context :=
    ⟨formed.code, upper, universeWitness, .cumul formed.formed (level ▸ cumulative)⟩
  exact ⟨raised, (_root_.Quotient.sound (show Conv rules.headEq raised.code formed.code
    rules.computation from .refl _)).trans same, rfl⟩

/-! ## Presheaves on the actual quotient-substitution category -/

def QType.rawPresheaf (rules : Rules Head) : (Context rules)ᵒᵖ ⥤ Type where
  obj context := QType context.unop
  map morphism := TypeCat.ofHom fun type => QType.reindex type morphism.unop
  map_id _ := by ext type; exact QType.reindex_id type
  map_comp first second := by ext type; exact QType.reindex_comp type second.unop first.unop

def QTerm.rawPresheaf (rules : Rules Head) : (Context rules)ᵒᵖ ⥤ Type where
  obj context := QTerm context.unop
  map morphism := TypeCat.ofHom fun term => QTerm.reindex term morphism.unop
  map_id _ := by ext term; exact QTerm.reindex_id term
  map_comp first second := by ext term; exact QTerm.reindex_comp term second.unop first.unop

/-- The two descended presheaves use Mathlib's quotient universal property;
the needed invariance is the actual substitution theorem proved above. -/
def QType.presheaf (rules : Rules Head) : (quotientContext rules)ᵒᵖ ⥤ Type :=
  (_root_.CategoryTheory.Quotient.lift (homConversion rules) (QType.rawPresheaf rules).rightOp
    (fun _ _ _ _ converted => Quiver.Hom.unop_inj
      (by ext type; exact QType.reindex_pointwise type converted))).leftOp

def QTerm.presheaf (rules : Rules Head) : (quotientContext rules)ᵒᵖ ⥤ Type :=
  (_root_.CategoryTheory.Quotient.lift (homConversion rules) (QTerm.rawPresheaf rules).rightOp
    (fun _ _ _ _ converted => Quiver.Hom.unop_inj
      (by ext term; exact QTerm.reindex_pointwise term converted))).leftOp

@[simp] theorem QType.presheaf_obj (context : quotientContext rules) :
    (QType.presheaf rules).obj (.op context) = QType context.as := rfl

@[simp] theorem QTerm.presheaf_obj (context : quotientContext rules) :
    (QTerm.presheaf rules).obj (.op context) = QTerm context.as := rfl

@[simp] theorem QType.presheaf_map_projected {source target : Context rules}
    (morphism : source ⟶ target) (type : QType target) :
    (QType.presheaf rules).map ((quotientProjection rules).map morphism).op type =
      type.reindex morphism := rfl

@[simp] theorem QTerm.presheaf_map_projected {source target : Context rules}
    (morphism : source ⟶ target) (term : QTerm target) :
    (QTerm.presheaf rules).map ((quotientProjection rules).map morphism).op term =
      term.reindex morphism := rfl

theorem QTerm.presheaf_type_natural {source target : quotientContext rules}
    (morphism : source ⟶ target) (term : QTerm target.as) :
    ((QTerm.presheaf rules).map morphism.op term).type =
      (QType.presheaf rules).map morphism.op term.type := by
  revert term
  refine Quot.inductionOn morphism (fun raw term => ?_)
  exact QTerm.type_reindex term raw

def quotientTypeProjection (rules : Rules Head) : QTerm.presheaf rules ⟶ QType.presheaf rules where
  app _ := TypeCat.ofHom QTerm.type
  naturality := by
    intro source target morphism
    ext term
    exact QTerm.presheaf_type_natural morphism.unop term

theorem QType.presheaf_factorization :
    (quotientProjection rules).op ⋙ QType.presheaf rules = QType.rawPresheaf rules := rfl

theorem QTerm.presheaf_factorization :
    (quotientProjection rules).op ⋙ QTerm.presheaf rules = QTerm.rawPresheaf rules := rfl


end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
