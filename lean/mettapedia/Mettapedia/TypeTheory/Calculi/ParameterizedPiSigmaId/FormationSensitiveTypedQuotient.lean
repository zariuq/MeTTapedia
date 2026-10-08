import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRetainedContextual
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRuleReadout
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Conservativity

/-!
# Typed-equality fibres over the conversion quotient

The raw conversion quotient and typed equality have different equations.
For a qualified presentation, common reducts and typed preservation give a
map from the former to the latter. The target type and total-term quotients
retain both annotation and value equality obligations. Their substitution
action descends through the actual quotient category, yielding a natural
display map and a commuting square from the original conversion fibres.

Exact supplied formation and typing trees enter through their direct
erasure. No new tree is selected from a proposition. Typed equality includes
function and pair eta, so this construction does not assert that the two
quotients are equivalent. It also does not supply an arbitrary-model
interpreter or a classifying initiality theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveTypedQuotient

open _root_.CategoryTheory
open TypedEquality TypedEquality.Normalization
open FormationSensitiveContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- The independent operational qualifications used by the existing
conservativity theorem. No arbitrary-derivation soundness is a field. -/
structure Qualification (S : Setting Head L) : Prop where
  forms : FormFacts S.R S.roles
  roots : RootPreserving S.R
  heads : HeadPreserving S.R
  church : ConversionCoherence.ChurchRosser S.R

variable (q : Qualification S)
include q

/-- Form each telescope entry in the typed judgment by induction on its
actual formation proof. -/
theorem contextFormed {n : Nat} {Γ : Ctx Head n}
    (formed : FormationSensitive.ContextFormation S.R Γ) : CtxFormed S.R Γ := by
  induction formed with
  | nil => exact .nil
  | snoc _ entry universeWitness ih =>
      exact .snoc ih ⟨_, universeWitness,
        Normalization.FormationSensitive.Typing.toTyped q.forms q.roots q.heads q.church entry ih⟩

theorem typeTyped {context : Context S.R} (type : TypeOver context) :
    Typed S.R context.raw type.code (.head type.level) :=
  Normalization.FormationSensitive.Typing.toTyped q.forms q.roots q.heads q.church
    type.formed (contextFormed q context.formed)

theorem termTyped {context : Context S.R} {type : TypeOver context}
    (term : Term context type) : Typed S.R context.raw term.code type.code :=
  Normalization.FormationSensitive.Typing.toTyped q.forms q.roots q.heads q.church
    term.typed (contextFormed q context.formed)

theorem homTyped {source target : Context S.R} (morphism : source ⟶ target) :
    SubstMor S.R target.raw source.raw morphism.substitution :=
  fun index => Normalization.FormationSensitive.Typing.toTyped q.forms q.roots q.heads q.church
    (morphism.typed index) (contextFormed q source.formed)

theorem conversionTypeEq {context : Context S.R} (first second : TypeOver context)
    (converted : Conv S.R.headEq first.code second.code S.R.computation) :
    TypeEq S.R context.raw first.code second.code :=
  Conv.toTypeEq q.forms q.roots q.heads q.church (contextFormed q context.formed)
    converted (typeTyped q first) first.universeWitness (typeTyped q second) second.universeWitness

/-- Raw-converted component substitutions satisfy the genuinely dependent
typed substitution-equality contract. The second component is retyped at
the first component's annotation before applying conservativity. -/
theorem homSubstEq {source target : Context S.R} {first second : source ⟶ target}
    (converted : homConversion S.R first second) :
    SubstEq S.R target.raw source.raw first.substitution second.substitution := by
  refine ⟨homTyped q first, ?_⟩
  intro index
  have sameType := Conv.substitutePointwise converted (Ctx.lookup target.raw index)
  obtain ⟨level, universeWitness, formed⟩ := target.formed.lookup_formed index
  have secondAtFirst := (second.typed index).conv (formed.substitute first.typed)
    universeWitness sameType.symm
  exact Conv.toEqual q.forms q.roots q.heads q.church (contextFormed q source.formed)
    (converted index) (homTyped q first index)
    (Normalization.FormationSensitive.Typing.toTyped q.forms q.roots q.heads q.church
      secondAtFirst (contextFormed q source.formed))

def typeSetoid (context : Context S.R) : Setoid (TypeOver context) where
  r first second := TypeEq S.R context.raw first.code second.code
  iseqv := ⟨fun type => ⟨_, type.universeWitness, .refl (typeTyped q type)⟩,
    fun same => same.symm, fun first second => first.trans S.levels second⟩

def QType (context : Context S.R) := _root_.Quotient (typeSetoid q context)

def QType.mk {context : Context S.R} (type : TypeOver context) : QType q context :=
  _root_.Quotient.mk _ type

theorem QType.mk_eq_iff {context : Context S.R} (first second : TypeOver context) :
    QType.mk q first = QType.mk q second ↔ TypeEq S.R context.raw first.code second.code :=
  _root_.Quotient.eq

/-- Total terms carry independently formed annotations. Equality includes
their type equality and a value equality at the first annotation. -/
def termSetoid (context : Context S.R) : Setoid (TotalTerm context) where
  r first second := TypeEq S.R context.raw first.1.code second.1.code ∧
    Equal S.R context.raw first.2.code second.2.code first.1.code
  iseqv := ⟨fun pair => ⟨⟨_, pair.1.universeWitness, .refl (typeTyped q pair.1)⟩,
      .refl (termTyped q pair.2)⟩,
    fun same => ⟨same.1.symm, Equal.convType (.symm same.2) same.1⟩,
    fun first second => ⟨first.1.trans S.levels second.1,
      .trans first.2 (Equal.convType second.2 first.1.symm)⟩⟩

def QTerm (context : Context S.R) := _root_.Quotient (termSetoid q context)

def QTerm.mk {context : Context S.R} {type : TypeOver context}
    (term : Term context type) : QTerm q context := _root_.Quotient.mk _ ⟨type, term⟩

theorem QTerm.mk_eq_iff {context : Context S.R} {first second : TypeOver context}
    (left : Term context first) (right : Term context second) :
    QTerm.mk q left = QTerm.mk q right ↔
      TypeEq S.R context.raw first.code second.code ∧
        Equal S.R context.raw left.code right.code first.code := _root_.Quotient.eq

def QTerm.type {context : Context S.R} (term : QTerm q context) : QType q context :=
  _root_.Quotient.lift (s := termSetoid q context)
    (fun pair : TotalTerm context => QType.mk q pair.1)
    (fun _ _ same => _root_.Quotient.sound same.1) term

@[simp] theorem QTerm.type_mk {context : Context S.R} {type : TypeOver context}
    (term : Term context type) : (QTerm.mk q term).type = QType.mk q type := rfl

variable {q}

def QType.reindex {source target : Context S.R} (type : QType q target)
    (morphism : source ⟶ target) : QType q source :=
  _root_.Quotient.map (fun formed => formed.reindex morphism) (by
    intro first second same
    obtain ⟨level, universeWitness, equality⟩ := same
    exact ⟨level, universeWitness, by
      simpa only [subst, TypeOver.reindex] using equality.substitute (homTyped q morphism)⟩) type

@[simp] theorem QType.reindex_mk {source target : Context S.R} (type : TypeOver target)
    (morphism : source ⟶ target) :
    (QType.mk q type).reindex morphism = QType.mk q (type.reindex morphism) := rfl

theorem QType.reindex_id {context : Context S.R} (type : QType q context) :
    type.reindex (𝟙 context) = type := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact congrArg (QType.mk q) formed.reindex_id

theorem QType.reindex_comp {first middle last : Context S.R} (type : QType q last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    type.reindex (earlier ≫ later) = (type.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  exact congrArg (QType.mk q) (formed.reindex_comp earlier later)

theorem QType.reindex_converted {source target : Context S.R} (type : QType q target)
    {first second : source ⟶ target} (converted : homConversion S.R first second) :
    type.reindex first = type.reindex second := by
  refine _root_.Quotient.inductionOn type fun formed => ?_
  apply _root_.Quotient.sound
  exact ⟨formed.level, formed.universeWitness, by
    simpa only [subst, TypeOver.reindex] using
      (typeTyped q formed).functional (homSubstEq q converted)⟩

def QTerm.reindex {source target : Context S.R} (term : QTerm q target)
    (morphism : source ⟶ target) : QTerm q source :=
  _root_.Quotient.map (fun pair : TotalTerm target => pair.reindex morphism) (by
    intro first second same
    obtain ⟨level, universeWitness, equality⟩ := same.1
    exact ⟨⟨level, universeWitness, by
      simpa only [subst, TotalTerm.reindex, TypeOver.reindex] using
        equality.substitute (homTyped q morphism)⟩,
      same.2.substitute (homTyped q morphism)⟩) term

@[simp] theorem QTerm.reindex_mk {source target : Context S.R} {type : TypeOver target}
    (term : Term target type) (morphism : source ⟶ target) :
    (QTerm.mk q term).reindex morphism = QTerm.mk q (term.reindex morphism) := rfl

theorem QTerm.type_reindex {source target : Context S.R} (term : QTerm q target)
    (morphism : source ⟶ target) :
    (term.reindex morphism).type = term.type.reindex morphism := by
  refine _root_.Quotient.inductionOn term fun _ => rfl

theorem QTerm.reindex_id {context : Context S.R} (term : QTerm q context) :
    term.reindex (𝟙 context) = term := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  apply (QTerm.mk_eq_iff q _ _).mpr
  change TypeEq S.R context.raw (subst ids pair.1.code) pair.1.code ∧
    Equal S.R context.raw (subst ids pair.2.code) pair.2.code (subst ids pair.1.code)
  rw [subst_ids, subst_ids]
  exact ⟨⟨_, pair.1.universeWitness, .refl (typeTyped q pair.1)⟩,
    .refl (termTyped q pair.2)⟩

theorem QTerm.reindex_comp {first middle last : Context S.R} (term : QTerm q last)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    term.reindex (earlier ≫ later) = (term.reindex later).reindex earlier := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  apply (QTerm.mk_eq_iff q _ _).mpr
  change TypeEq S.R first.raw
      (subst (subComp earlier.substitution later.substitution) pair.1.code)
      (subst earlier.substitution (subst later.substitution pair.1.code)) ∧
    Equal S.R first.raw
      (subst (subComp earlier.substitution later.substitution) pair.2.code)
      (subst earlier.substitution (subst later.substitution pair.2.code))
      (subst (subComp earlier.substitution later.substitution) pair.1.code)
  rw [subst_subComp, subst_subComp]
  exact ⟨⟨_, pair.1.universeWitness, .refl (typeTyped q (pair.1.reindex (earlier ≫ later)))⟩,
    .refl (termTyped q (pair.2.reindex (earlier ≫ later)))⟩

theorem QTerm.reindex_converted {source target : Context S.R} (term : QTerm q target)
    {first second : source ⟶ target} (converted : homConversion S.R first second) :
    term.reindex first = term.reindex second := by
  refine _root_.Quotient.inductionOn term fun pair => ?_
  apply _root_.Quotient.sound
  exact ⟨⟨pair.1.level, pair.1.universeWitness,
      (typeTyped q pair.1).functional (homSubstEq q converted)⟩,
    (termTyped q pair.2).functional (homSubstEq q converted)⟩

variable (q)

/-- Conservativity at both independently supplied annotations produces the
heterogeneous equality required by the total-term quotient. -/
theorem conversionTermEq {context : Context S.R} {first second : TypeOver context}
    (left : Term context first) (right : Term context second)
    (annotations : Conv S.R.headEq first.code second.code S.R.computation)
    (values : Conv S.R.headEq left.code right.code S.R.computation) :
    TypeEq S.R context.raw first.code second.code ∧
      Equal S.R context.raw left.code right.code first.code := by
  have sameType := conversionTypeEq q first second annotations
  exact ⟨sameType, Conv.toEqual q.forms q.roots q.heads q.church
    (contextFormed q context.formed) values (termTyped q left)
    (Typed.convType (termTyped q right) sameType.symm)⟩

/-- The raw-conversion type quotient maps to the typed-equality quotient. -/
def QType.ofRaw {context : Context S.R} :
    FormationSensitiveContextual.QType context → QType q context :=
  _root_.Quotient.lift (fun type => QType.mk q type)
    (fun first second converted =>
      _root_.Quotient.sound (conversionTypeEq q first second converted))

@[simp] theorem QType.ofRaw_mk {context : Context S.R} (type : TypeOver context) :
    QType.ofRaw q (FormationSensitiveContextual.QType.mk type) = QType.mk q type := rfl

/-- The value map discharges both conversion obligations; a target class
does not erase an unsupported annotation change. -/
def QTerm.ofRaw {context : Context S.R} :
    FormationSensitiveContextual.QTerm context → QTerm q context :=
  _root_.Quotient.lift (fun pair : TotalTerm context => QTerm.mk q pair.2)
    (fun first second converted => _root_.Quotient.sound
      (conversionTermEq q first.2 second.2 converted.1 converted.2))

@[simp] theorem QTerm.ofRaw_mk {context : Context S.R} {type : TypeOver context}
    (term : Term context type) :
    QTerm.ofRaw q (FormationSensitiveContextual.QTerm.mk term) = QTerm.mk q term := rfl

theorem QTerm.ofRaw_type {context : Context S.R}
    (term : FormationSensitiveContextual.QTerm context) :
    (QTerm.ofRaw q term).type = QType.ofRaw q term.type := by
  refine _root_.Quotient.inductionOn term fun _ => rfl

theorem QType.ofRaw_reindex {source target : Context S.R}
    (type : FormationSensitiveContextual.QType target) (morphism : source ⟶ target) :
    QType.ofRaw q (type.reindex morphism) = (QType.ofRaw q type).reindex morphism := by
  refine _root_.Quotient.inductionOn type fun _ => rfl

theorem QTerm.ofRaw_reindex {source target : Context S.R}
    (term : FormationSensitiveContextual.QTerm target) (morphism : source ⟶ target) :
    QTerm.ofRaw q (term.reindex morphism) = (QTerm.ofRaw q term).reindex morphism := by
  refine _root_.Quotient.inductionOn term fun _ => rfl

def QType.rawPresheaf : (Context S.R)ᵒᵖ ⥤ Type where
  obj context := QType q context.unop
  map morphism := TypeCat.ofHom fun type => QType.reindex type morphism.unop
  map_id _ := by ext type; exact QType.reindex_id type
  map_comp first second := by ext type; exact QType.reindex_comp type second.unop first.unop

def QTerm.rawPresheaf : (Context S.R)ᵒᵖ ⥤ Type where
  obj context := QTerm q context.unop
  map morphism := TypeCat.ofHom fun term => QTerm.reindex term morphism.unop
  map_id _ := by ext term; exact QTerm.reindex_id term
  map_comp first second := by ext term; exact QTerm.reindex_comp term second.unop first.unop

/-- Descent uses typed functionality for raw-converted substitutions,
including their dependent component annotations. -/
def QType.presheaf : (quotientContext S.R)ᵒᵖ ⥤ Type :=
  (_root_.CategoryTheory.Quotient.lift (homConversion S.R) (QType.rawPresheaf q).rightOp
    (fun _ _ _ _ converted => Quiver.Hom.unop_inj
      (by ext type; exact QType.reindex_converted type converted))).leftOp

def QTerm.presheaf : (quotientContext S.R)ᵒᵖ ⥤ Type :=
  (_root_.CategoryTheory.Quotient.lift (homConversion S.R) (QTerm.rawPresheaf q).rightOp
    (fun _ _ _ _ converted => Quiver.Hom.unop_inj
      (by ext term; exact QTerm.reindex_converted term converted))).leftOp

@[simp] theorem QType.presheaf_obj (context : quotientContext S.R) :
    (QType.presheaf q).obj (.op context) = QType q context.as := rfl

@[simp] theorem QTerm.presheaf_obj (context : quotientContext S.R) :
    (QTerm.presheaf q).obj (.op context) = QTerm q context.as := rfl

@[simp] theorem QType.presheaf_map_projected {source target : Context S.R}
    (morphism : source ⟶ target) (type : QType q target) :
    (QType.presheaf q).map ((quotientProjection S.R).map morphism).op type =
      type.reindex morphism := rfl

@[simp] theorem QTerm.presheaf_map_projected {source target : Context S.R}
    (morphism : source ⟶ target) (term : QTerm q target) :
    (QTerm.presheaf q).map ((quotientProjection S.R).map morphism).op term =
      term.reindex morphism := rfl

theorem QTerm.presheaf_type_natural {source target : quotientContext S.R}
    (morphism : source ⟶ target) (term : QTerm q target.as) :
    ((QTerm.presheaf q).map morphism.op term).type =
      (QType.presheaf q).map morphism.op term.type := by
  revert term
  refine Quot.inductionOn morphism (fun raw term => ?_)
  exact QTerm.type_reindex term raw

/-- The typed total-term family is displayed over its independently formed
type classes by an actual natural transformation. -/
def typeProjection : QTerm.presheaf q ⟶ QType.presheaf q where
  app _ := TypeCat.ofHom (QTerm.type q)
  naturality := by
    intro source target morphism
    ext term
    exact QTerm.presheaf_type_natural q morphism.unop term

theorem QType.ofRaw_presheaf_natural {source target : quotientContext S.R}
    (morphism : source ⟶ target) (type : FormationSensitiveContextual.QType target.as) :
    QType.ofRaw q ((FormationSensitiveContextual.QType.presheaf S.R).map morphism.op type) =
      (QType.presheaf q).map morphism.op (QType.ofRaw q type) := by
  revert type
  refine Quot.inductionOn morphism (fun raw type => ?_)
  exact QType.ofRaw_reindex q type raw

theorem QTerm.ofRaw_presheaf_natural {source target : quotientContext S.R}
    (morphism : source ⟶ target) (term : FormationSensitiveContextual.QTerm target.as) :
    QTerm.ofRaw q ((FormationSensitiveContextual.QTerm.presheaf S.R).map morphism.op term) =
      (QTerm.presheaf q).map morphism.op (QTerm.ofRaw q term) := by
  revert term
  refine Quot.inductionOn morphism (fun raw term => ?_)
  exact QTerm.ofRaw_reindex q term raw

def rawTypeMap : FormationSensitiveContextual.QType.presheaf S.R ⟶ QType.presheaf q where
  app _ := TypeCat.ofHom (QType.ofRaw q)
  naturality := by
    intro source target morphism
    ext type
    exact QType.ofRaw_presheaf_natural q morphism.unop type

def rawTermMap : FormationSensitiveContextual.QTerm.presheaf S.R ⟶ QTerm.presheaf q where
  app _ := TypeCat.ofHom (QTerm.ofRaw q)
  naturality := by
    intro source target morphism
    ext term
    exact QTerm.ofRaw_presheaf_natural q morphism.unop term

/-- The raw and typed family displays form a genuinely commuting square. -/
theorem display_square : rawTermMap q ≫ typeProjection q =
    quotientTypeProjection S.R ≫ rawTypeMap q := by
  ext context term
  exact QTerm.ofRaw_type q term

theorem QType.presheaf_factorization :
    (quotientProjection S.R).op ⋙ QType.presheaf q = QType.rawPresheaf q := rfl

theorem QTerm.presheaf_factorization :
    (quotientProjection S.R).op ⋙ QTerm.presheaf q = QTerm.rawPresheaf q := rfl

theorem QType.ofRaw_surjective {context : Context S.R} :
    Function.Surjective (QType.ofRaw q (context := context)) := by
  intro type
  refine _root_.Quotient.inductionOn type fun actual => ?_
  exact ⟨FormationSensitiveContextual.QType.mk actual, rfl⟩

theorem QTerm.ofRaw_surjective {context : Context S.R} :
    Function.Surjective (QTerm.ofRaw q (context := context)) := by
  intro term
  refine _root_.Quotient.inductionOn term fun actual => ?_
  exact ⟨FormationSensitiveContextual.QTerm.mk actual.2, rfl⟩

/-! ## Dependent fibres and their coherent change of annotation -/

def Fibre {context : quotientContext S.R} (type : QType q context.as) :=
  { term : QTerm q context.as // term.type = type }

def Fibre.compare {context : quotientContext S.R} {first second : QType q context.as}
    (same : first = second) : Fibre q first ≃ Fibre q second where
  toFun term := ⟨term.val, term.property.trans same⟩
  invFun term := ⟨term.val, term.property.trans same.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem Fibre.compare_refl {context : quotientContext S.R} {type : QType q context.as}
    (term : Fibre q type) : Fibre.compare q rfl term = term := rfl

theorem Fibre.compare_trans {context : quotientContext S.R}
    {first middle last : QType q context.as} (earlier : first = middle) (later : middle = last)
    (term : Fibre q first) :
    Fibre.compare q later (Fibre.compare q earlier term) =
      Fibre.compare q (earlier.trans later) term := rfl

def Fibre.reindex {source target : quotientContext S.R} {type : QType q target.as}
    (term : Fibre q type) (morphism : source ⟶ target) :
    Fibre q ((QType.presheaf q).map morphism.op type) :=
  ⟨(QTerm.presheaf q).map morphism.op term.val,
    (QTerm.presheaf_type_natural q morphism term.val).trans
      (congrArg ((QType.presheaf q).map morphism.op) term.property)⟩

@[simp] theorem Fibre.reindex_val {source target : quotientContext S.R}
    {type : QType q target.as} (term : Fibre q type) (morphism : source ⟶ target) :
    (Fibre.reindex q term morphism).val = (QTerm.presheaf q).map morphism.op term.val := rfl

theorem QType.presheaf_identity (context : quotientContext S.R) (type : QType q context.as) :
    (QType.presheaf q).map (𝟙 context).op type = type := by
  change type.reindex (𝟙 context.as) = type
  exact QType.reindex_id type

theorem QType.presheaf_composition {first middle last : quotientContext S.R}
    (type : QType q last.as) (earlier : first ⟶ middle) (later : middle ⟶ last) :
    (QType.presheaf q).map (earlier ≫ later).op type =
      (QType.presheaf q).map earlier.op ((QType.presheaf q).map later.op type) := by
  change (QType.presheaf q).map (later.op ≫ earlier.op) type = _
  rw [Functor.map_comp]
  rfl

theorem Fibre.reindex_id {context : quotientContext S.R} {type : QType q context.as}
    (term : Fibre q type) :
    Fibre.compare q (QType.presheaf_identity q context type)
      (Fibre.reindex q term (𝟙 context)) = term := by
  apply Subtype.ext
  change term.val.reindex (𝟙 context.as) = term.val
  exact QTerm.reindex_id term.val

theorem Fibre.reindex_comp {first middle last : quotientContext S.R}
    {type : QType q last.as} (term : Fibre q type)
    (earlier : first ⟶ middle) (later : middle ⟶ last) :
    Fibre.compare q (QType.presheaf_composition q type earlier later)
      (Fibre.reindex q term (earlier ≫ later)) =
      Fibre.reindex q (Fibre.reindex q term later) earlier := by
  apply Subtype.ext
  change (QTerm.presheaf q).map (later.op ≫ earlier.op) term.val = _
  rw [Functor.map_comp]
  rfl

theorem Fibre.compare_reindex {source target : quotientContext S.R}
    {first second : QType q target.as} (same : first = second) (term : Fibre q first)
    (morphism : source ⟶ target) :
    Fibre.reindex q (Fibre.compare q same term) morphism =
      Fibre.compare q (congrArg ((QType.presheaf q).map morphism.op) same)
        (Fibre.reindex q term morphism) := rfl

/-- The display square gives a map on each supplied raw class fibre. -/
def Fibre.ofRaw {context : Context S.R} {type : FormationSensitiveContextual.QType context}
    (term : FormationSensitiveContextual.TermFibre type) :
    Fibre q (context := (quotientProjection S.R).obj context) (QType.ofRaw q type) :=
  ⟨QTerm.ofRaw q term.val, (QTerm.ofRaw_type q term.val).trans
    (congrArg (QType.ofRaw q) term.property)⟩

theorem Fibre.ofRaw_compare {context : Context S.R}
    {first second : FormationSensitiveContextual.QType context} (same : first = second)
    (term : FormationSensitiveContextual.TermFibre first) :
    Fibre.ofRaw q (FormationSensitiveContextual.TermFibre.compare same term) =
      Fibre.compare q (congrArg (QType.ofRaw q) same) (Fibre.ofRaw q term) := rfl

theorem Fibre.ofRaw_reindex {source target : Context S.R}
    {type : FormationSensitiveContextual.QType target}
    (term : FormationSensitiveContextual.TermFibre type) (morphism : source ⟶ target) :
    Fibre.compare q (QType.ofRaw_reindex q type morphism)
      (Fibre.ofRaw q (term.reindex morphism)) =
      Fibre.reindex q (Fibre.ofRaw q term) ((quotientProjection S.R).map morphism) := by
  apply Subtype.ext
  exact QTerm.ofRaw_reindex q term.val morphism

/-! ## Exact supplied certificates -/

open FormationSensitiveRetainedContextual in
def suppliedType {context : FormationSensitiveRetainedContextual.Context S.R}
    (type : FormationSensitiveRetainedContextual.TypeOver context) : QType q context.erase :=
  QType.mk q type.erase

def suppliedTerm {context : FormationSensitiveRetainedContextual.Context S.R}
    {type : FormationSensitiveRetainedContextual.TypeOver context}
    (term : FormationSensitiveRetainedContextual.Term context type) :
    Fibre q (context := (quotientProjection S.R).obj context.erase) (suppliedType q type) :=
  ⟨QTerm.mk q term.erase, rfl⟩

/-- Pair the actual quotient point with the original ordered premise ledger.
The ledger is read from the supplied tree, not recovered from its erasure. -/
def suppliedReadout {context : FormationSensitiveRetainedContextual.Context S.R}
    {type : FormationSensitiveRetainedContextual.TypeOver context}
    (term : FormationSensitiveRetainedContextual.Term context type) :
    Fibre q (context := (quotientProjection S.R).obj context.erase) (suppliedType q type) ×
      List FormationSensitiveRuleReadout.Use :=
  ⟨suppliedTerm q term, FormationSensitiveRuleReadout.readout term.evidence⟩

theorem suppliedReadout_ledger {context : FormationSensitiveRetainedContextual.Context S.R}
    {type : FormationSensitiveRetainedContextual.TypeOver context}
    (term : FormationSensitiveRetainedContextual.Term context type) :
    (suppliedReadout q term).2 = FormationSensitiveRuleReadout.readout term.evidence := rfl

theorem suppliedTerm_ofRaw {context : FormationSensitiveRetainedContextual.Context S.R}
    {type : FormationSensitiveRetainedContextual.TypeOver context}
    (term : FormationSensitiveRetainedContextual.Term context type) :
    suppliedTerm q term = Fibre.ofRaw q (FormationSensitiveContextual.TermFibre.mk term.erase) := rfl

theorem suppliedType_reindex
    {source target : FormationSensitiveRetainedContextual.Context S.R}
    (type : FormationSensitiveRetainedContextual.TypeOver target)
    (morphism : source ⟶ target) :
    suppliedType q (type.reindex morphism) =
      (suppliedType q type).reindex morphism.erase := rfl

theorem suppliedTerm_reindex
    {source target : FormationSensitiveRetainedContextual.Context S.R}
    {type : FormationSensitiveRetainedContextual.TypeOver target}
    (term : FormationSensitiveRetainedContextual.Term target type)
    (morphism : source ⟶ target) :
    suppliedTerm q (term.reindex morphism) =
      Fibre.reindex q (suppliedTerm q term)
        ((quotientProjection S.R).map morphism.erase) := rfl

end FormationSensitiveTypedQuotient
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
