import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueLevelControls
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectListsAdequacy
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurchProgress

/-!
# Strong normalization, canonicity and weak-head forms at every declared datatype

A simple datatype `d` admissible over the object package (`hd : d.Admissible objectChurch`) is a
type in a universe, constructors whose fields are the datatype itself or closed types of the object
package, and a recursor with one computation rule for each constructor. The package with it has the
rules `dataRules d`, the annotation `dataChurch d` and the roles `dataRoles d`. For every such `d`:

* its typed terms are strongly normalizing (`dataRules_sn`, `dataRules_equal_sn`);
* two annotated terms with one erasure, typed at one type, are equal at it (`dataCoherence`);
* a typed annotated term steps or is a weak-head normal form (`dataProgressFacts`,
  `dataChurch_progress`);
* **canonicity**: a closed term typed at the datatype weak-head reduces to one of its listed
  constructors applied to as many arguments as it has fields, each argument typed at its field's
  type (`data_canonical`);
* its types and equations of types lift to the annotation, and its own types have the facts about
  weak-head forms (`dataLiftingFacts`, `dataRules_liftType`, `dataRules_liftTypeEq`,
  `dataRules_formFacts`).

What comes after strong normalization uses three facts about the annotated package that its
adequacy gives with no hypothesis: the facts about the weak-head forms of its annotated types
(`dataFormFacts`), the injectivity and no-confusion of its type formers (`dataFormerFacts`), and
that its root steps of typed terms are equalities (`dataRootAdmitted`). Strong normalization is
proved in a value model that keeps six names for itself, the transport's constants and the daimon,
so it is stated for datatypes whose names avoid them (`AvoidsModelNames`), as those of the lists do
(`listDecl_avoids`).

**The model** (`dataTExt`). The transport value model extended by the datatype: on the value side
the datatype is an inductive type with its constructors and the recursor computes by its rules; the
realizer side is the package with the datatype itself. The datatype is a valid term of its universe
by the clause of a simple inductive type, its closed field types being interpreted by the
fundamental lemma of the object package (`dataTExt_valid_type`). A constructor's declared type is
typed in the package without the recursor and the constructors, the recursor's in the package
without the recursor; their fundamental lemmas make the constructors and the recursor valid
(`dataTExt_valid_ctor`, `dataTExt_valid_rec`). So the package is sound for the model
(`dataRules_soundS`), and strong normalization follows from the model's fundamental lemma.

**Progress** (`dataProgressFacts`). The object package's constants progress as in the object
package. A constructor's declared type is the closed function type of its fields ending at the
datatype (`liftTm_ctorType`, `afterBinders_ctorType`); the recursor's has one binder for the motive,
one for each method and one for the scrutinee, of the datatype (`afterBinders_domain_recType`), and
at a constructor spine it takes the rule of that constructor (`data_recStep`). The type constants
that canonical forms and inspections name are the numbers, the codes and the datatype
(`data_relevant`).

**Canonicity** (`data_canonical`). A closed term typed at the datatype takes annotated weak-head
steps, which end since its erasure is strongly normalizing, at a typed weak-head normal form
(`data_whnf`). That form is not neutral: a closed neutral term has a principal type of `U₀`, the
sets or the power set's type (`closedNeutral_principal`), since the sets, the power set and the
codes are its only rigid constants, no name of the datatype being rigid; none of these is below
the datatype (`closedData_not_neutral`). So it is a canonical form of the datatype, a constructor
spine (`data_fits`), and the principal type of the constructor, a closed function type, types each
argument at its field (`forall₂_typed_of_cArrows`).

**Lifting** (`dataLiftingFacts`). Root steps lift to the annotation (`dataChurch_lift`), and with
coherence, root admission and declared types without abstractions every derivation of a type or of
an equation of types lifts. With strong normalization and the progress of annotated types, the
facts about the weak-head forms of the package's own types follow (`dataRules_formFacts`).

**The three faces.** This adds to the operational face (strong normalization of the package's
reduction, and closed terms of a datatype computing to its constructors) and to the intensional
face (coherence, lifting, the facts about weak-head forms). The extensional face is seen through
the value side: the datatype's values are the least set closed under its constructors, an
inductive definition read on terms, and the sets are told apart from the codes by their reading in
the domain (`set_ne_prop`).

**The lists of numbers** are an instance, `listDecl`, with `nil` and `cons` of a number and a list.
Positive examples: `cons 1 nil` is strongly normalizing (`consOneNil_sn`); a constructor of the
lists at its typed fields is `nil` or `cons a l` (`listDecl_ctor_forms`); `cons 1 nil` reduces to a
`cons` (`cons_one_nil_canonical`), and the closed recursion `append (cons 1 nil) nil` to `nil` or to
a `cons` (`appendOneNil_canonical`). Negative examples: over a
list variable `x`, `append x nil` is typed at the lists and reduces to neither `nil` nor a `cons`,
so canonicity needs closed terms (`appendVarNil_not_canonical`); and a recursor whose rule at
`cons` recurses on the same list types a term that is not strongly normalizing, so strong
normalization rests on the rules being structural (`loopRules_not_sn`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Annotated
open Package (U0 numT jName)

namespace CodeModel

/-! ## The names the value side reserves -/

/-- **A datatype avoids the names the value side reserves**: the transport's constants and the
daimon of the transport value model. -/
def AvoidsModelNames (d : Datatype Tower.Head) : Prop :=
  ∀ c ∈ dataNames d, c ∉ coeNameList ∧ c ≠ starN

/-- A name the object package does not declare is not declared by its rules either. -/
theorem objectRules_undeclared {c : DeclName} (h : objectChurch.constantType c = none) :
    objectRules.constantType c = none := by
  rw [objectChurch_constantType] at h
  unfold elabDeclarations at h
  cases found : objectRules.constantType c with
  | none => rfl
  | some type => rw [found] at h; cases h

/-- A name the object package does not declare is no instance of a quantifier code. -/
theorem allInstance?_undeclared {c : DeclName} (h : objectChurch.constantType c = none) :
    SetProfile.allInstance? c = none := by
  cases found : SetProfile.allInstance? c with
  | none => rfl
  | some type =>
      rw [SetProfile.allInstance?_eq_some found] at h
      cases (objectDecls_allName type).symm.trans h

/-- A name the object package does not declare is no instance of an equation code. -/
theorem eqInstance?_undeclared {c : DeclName} (h : objectChurch.constantType c = none) :
    SetProfile.eqInstance? c = none := by
  cases found : SetProfile.eqInstance? c with
  | none => rfl
  | some type =>
      rw [SetProfile.eqInstance?_eq_some found] at h
      cases (objectDecls_eqName type).symm.trans h

/-- **A name the object package does not declare, apart from the transport's constants, is
rigid in the transport value model.** -/
theorem tmodelRoles_undeclared {c : DeclName} (h : objectChurch.constantType c = none)
    (fresh : c ∉ coeNameList) : tmodelRoles c = .rigid := by
  have declared : ∀ {n : DeclName}, objectDeclared n = true → c ≠ n :=
    fun hn e => objectChurch_constantType_ne_none hn (e ▸ h)
  rw [tmodelRoles_eq fresh, modelRoles_of (declared (by decide)) (declared (by decide))
    (allInstance?_undeclared h) (eqInstance?_undeclared h)]
  refine roles_of_not_mem fun mem => ?_
  have all : ∀ n ∈ nonrigidNames, objectDeclared n = true := by decide
  exact declared (all c mem) rfl

/-- No name of a datatype is rigid under its roles. -/
theorem dataRoles_name_ne_rigid {d : Datatype Tower.Head} {base : Roles Tower.Head}
    (distinct : DistinctNames d.type d.ctors d.recursor) {c : DeclName} (mem : c ∈ dataNames d) :
    dataRolesOver d base c ≠ .rigid := by
  simp only [dataNames, List.mem_cons] at mem
  rcases mem with rfl | rfl | mem
  · rw [dataRoles_type]; exact nofun
  · rw [dataRoles_rec distinct]; exact nofun
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 mem
    obtain ⟨i, hi⟩ := List.getElem?_of_mem he
    rw [dataRoles_ctor distinct hi]; exact nofun

/-- The rules of a recursor, as the value side's computation at its name. -/
abbrev dataExtra (d : Datatype Tower.Head) : List (DeclName × RootComputation Tower.Head) :=
  [(d.recursor, iotaComputation d.recursor d.ctors)]

/-- The root computation of the package with a declared datatype reflects renaming. -/
theorem dataReflects (d : Datatype Tower.Head) : RootReflectsRename (dataRules d).computation :=
  RootReflectsRename.union objectReflects (iotaComputation_reflectsRename _ _)

section Model

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch) (avoid : AvoidsModelNames d)

include hd avoid in
/-- The names of the datatype are rigid in the transport value model. -/
theorem tmodelRoles_dataName {c : DeclName} (mem : c ∈ dataNames d) : tmodelRoles c = .rigid :=
  tmodelRoles_undeclared (dataNames_new hd mem) (avoid c mem).1

include hd avoid in
/-- The constructors of the numbers and of the datatype are declared on the value side. -/
theorem dataValueDeclared : ConstructorsDeclared (dataRolesOver d tmodelRoles) :=
  dataConstructorsDeclaredOver hd.distinct (tmodelRoles_dataName hd avoid)
    tmodelConstructorsDeclared tmodelRoles_num tmodelRoles_inductive

include hd avoid in
/-- The value side's roles with the datatype extend the transport value model's by its
names. -/
theorem dataValueRoles_extends : TExtends (dataRolesOver d tmodelRoles) (dataNames d) where
  old := fun h => dataRoles_outside h
  fresh := fun c mem => ⟨objectRules_undeclared (dataNames_new hd mem), (avoid c mem).1,
    (avoid c mem).2, allInstance?_undeclared (dataNames_new hd mem),
    eqInstance?_undeclared (dataNames_new hd mem)⟩

include hd in
/-- The decoder computes on its code in the package with a declared datatype, and the codes
are constructors. -/
theorem dataDecoderRoles : DecoderRoles (dataRoles d) programCodes.decoders where
  holds := (dataRoles_of_nonrigid (objectRoles_dataName hd)
    fun e => nomatch objectRoles_holds.symm.trans e).trans objectRoles_holds
  imp := dataRoles_keep (objectRoles_dataName hd) objectRoles_imp
  all := fun found => dataRoles_keep (objectRoles_dataName hd) (objectDecoderRoles.all found)
  eq := fun found => dataRoles_keep (objectRoles_dataName hd) (objectDecoderRoles.eq found)

omit avoid in
/-- A root step of the package with a declared datatype at a spine of a name the datatype does
not add is a root step of the object package: the recursor's rules are headed by the
recursor. -/
theorem dataStep_old {n : Nat} {c : DeclName} {args : List (Tower.Tm n)} {r : Tower.Tm n}
    (h : c ∉ dataNames d) (step : (dataRules d).computation.step (appSpine (.const c) args) r) :
    objectRules.computation.step (appSpine (.const c) args) r := by
  rcases step with step | iota
  · exact step
  · obtain ⟨p, ms, i, k, fields, as, m, -, -, -, -, e, -⟩ := iota
    obtain ⟨rfl, -⟩ := appSpine_const_injective e
    exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) h

/-- A constant of the package with a declared datatype: an object constant, the type, a
constructor or the recursor. -/
theorem dataRules_declared_cases {name : DeclName} {type : Tower.Tm 0}
    (declared : (dataRules d).constantType name = some type) :
    objectRules.constantType name = some type ∨ (name = d.type ∧ type = .head d.typeUniverse) ∨
      (∃ (i : Nat) (fields : List CtorField), d.ctors[i]? = some (name, fields) ∧
        type = ctorType d.type fields) ∨
      (name = d.recursor ∧ type = recType d.type d.motiveUniverse d.ctors) := by
  change sumDecls objectRules.constantType
    (inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse) name = some type
    at declared
  cases object : objectRules.constantType name with
  | some T =>
      rw [sumDecls_left object] at declared
      exact .inl declared
  | none =>
      rw [sumDecls_right object] at declared
      exact .inr (inductiveDecls_cases declared)

/-- **The transport value model extended by a declared datatype**: on the value side the
datatype and the rules of its recursor, on the realizer side the package with the datatype. -/
def dataTExt : TExtension where
  names := dataNames d
  roles := dataRolesOver d tmodelRoles
  extra := dataExtra d
  realRules := dataRules d
  realRoles := dataRoles d
  realShape := dataShape hd
  realReflects := dataReflects d
  realDecoderRoles := dataDecoderRoles hd
  realNumerals := ⟨dataRoles_keep (objectRoles_dataName hd) objectRoles_zero,
    dataRoles_keep (objectRoles_dataName hd) objectRoles_suc⟩
  realDeclared := dataConstructorsDeclared hd
  realDecodes := fun step => .inl (objectDecodes step)
  extends_ := dataValueRoles_extends hd avoid
  declared := dataValueDeclared hd avoid
  extraNames := fun entry mem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    exact List.mem_cons_of_mem _ List.mem_cons_self
  extraSpine := fun entry mem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    exact fun _ _ _ step => IotaStep.spine dataRoles_type (dataRoles_rec hd.distinct)
      (dataValueDeclared hd avoid) step
  extraHeaded := fun entry mem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    exact iotaComputation_headed
  extraDeterministic := fun entry mem => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    subst mem
    exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := d.type) dataRoles_type (dataValueDeclared hd avoid) step step'
  extraDistinct := List.nodup_singleton _
  realOld := fun h => dataRoles_outside h
  realRigid := fun mem role => absurd role (dataRoles_name_ne_rigid hd.distinct mem)
  realStepOld := dataStep_old
  realSub := ⟨id, id, id, id, id, fun declared => sumDecls_left declared, .inl⟩
  realHeadTyping := id
  realIsUniverse := id
  realJoin := id
  realCumulative := id
  realHeadEq := id
  realLevels := levelsWith ConvRules.objectLevels [.datatype d]
  realDeclaredOld := fun notNew declared => by
    rcases dataRules_declared_cases declared with object | ⟨rfl, -⟩ | ⟨i, fields, hi, -⟩ |
      ⟨rfl, -⟩
    · exact object
    · exact absurd List.mem_cons_self notNew
    · exact absurd (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_map.2 ⟨_, List.mem_of_getElem? hi, rfl⟩))) notNew
    · exact absurd (List.mem_cons_of_mem _ List.mem_cons_self) notNew
  realNewCtor := fun {c a} mem role => by
    rcases dataRoles_constructor hd.distinct role with ⟨fs, memC, rfl⟩ | ⟨notMem, -⟩
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem memC
      refine ⟨d.type, fs, ?_, rfl, List.mem_cons_self, d.ctors, dataRoles_type⟩
      show sumDecls objectRules.constantType
        (inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse) c = _
      rw [sumDecls_right (objectRules_undeclared (dataNames_new hd mem))]
      exact inductiveDecls_ctor hd.distinct hi
    · exact absurd mem notMem
  realNewInductive := fun {c cs} mem role => by
    by_cases h : c = d.type
    · subst h
      refine ⟨d.typeUniverse, hd.typeUniverse, ?_⟩
      show sumDecls objectRules.constantType
        (inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse) d.type = _
      rw [sumDecls_right (objectRules_undeclared hd.new.typeNew)]
      exact inductiveDecls_type
    · exfalso
      change dataRolesOver d objectRoles c = .inductive cs at role
      simp only [dataNames, List.mem_cons] at mem
      rcases mem with rfl | rfl | memC
      · exact h rfl
      · rw [dataRoles_rec hd.distinct] at role
        cases role
      · obtain ⟨e, he, rfl⟩ := List.mem_map.1 memC
        obtain ⟨i, hi⟩ := List.getElem?_of_mem he
        rw [dataRoles_ctor hd.distinct hi] at role
        cases role

variable (v : Nat → Nat)

/-- **The datatype is a simple inductive type in the model**: on both sides it is an inductive
type with its constructors, and the recursor computes by its rules, on the realizer side by
them only. -/
theorem data_inductiveIn :
    ModelSN.InductiveIn ((dataTExt hd avoid).model v) d.type d.recursor d.ctors where
  role := dataRoles_type (base := tmodelRoles)
  recRole := dataRoles_rec (base := tmodelRoles) hd.distinct
  iota := fun h => (dataTExt hd avoid).extraStep v List.mem_cons_self h
  realRole := dataRoles_type (base := objectRoles)
  realDeclared := dataConstructorsDeclared hd
  realRecRole := dataRoles_rec (base := objectRoles) hd.distinct
  realIota := fun {_ args r} step => by
    rcases step with step | iota
    · exfalso
      obtain ⟨c, arity, inspect, args', role, e, -, -⟩ := objectShape.spine step
      obtain ⟨rfl, -⟩ := appSpine_const_injective e
      exact nomatch (objectRoles_dataName hd (c := d.recursor)
        (List.mem_cons_of_mem _ List.mem_cons_self)).symm.trans role
    · exact iota

/-- A universe of the object package is a universe of the model. -/
theorem dataTExt_isUniverse {u : Tower.Head} (hu : objectRules.isUniverse u) :
    ((dataTExt hd avoid).model v).rules.isUniverse u :=
  ((dataTExt hd avoid).soundS_objectRules v).isUniverse hu

omit avoid in
/-- A closed field type is a closed field type of a constructor. -/
theorem mem_closedFields_entry {F : Tower.Tm 0} (h : F ∈ ValueSide.closedFields d.ctors) :
    ∃ entry ∈ d.ctors, (Field.closed F : CtorField) ∈ entry.2 := by
  obtain ⟨entry, hmem, hF⟩ := List.mem_flatMap.1 h
  obtain ⟨f, hf, e⟩ := List.mem_filterMap.1 hF
  cases f with
  | recursive => cases e
  | closed F' =>
      cases e
      exact ⟨entry, hmem, hf⟩

/-- **A closed field type is interpreted at the level of the datatype's universe** at every
world, by the fundamental lemma of the object package. -/
theorem closedField_interp {F : Tower.Tm 0} (h : F ∈ ValueSide.closedFields d.ctors) {m : Nat}
    (ξ : Consistency.World ((dataTExt hd avoid).model v).reading m) :
    ∃ P, ValueSide.InterpAt ((dataTExt hd avoid).model v).value
      (((dataTExt hd avoid).model v).levels.level d.typeUniverse) ξ (liftClosed F) P := by
  obtain ⟨entry, hmem, hF⟩ := mem_closedFields_entry h
  have typed : Typed objectRules .nil F (.head d.typeUniverse) := by
    have := CDerivable.erase (hd.fields entry hmem F hF)
    rw [CStatement.erase, erase_liftTm] at this
    exact this
  have valid := ModelSN.Typed.validS ((dataTExt hd avoid).soundS_objectRules v) typed trivial
  have hu := dataTExt_isUniverse hd avoid v hd.typeUniverse
  obtain ⟨rel, -⟩ := valid.2 (r := 0) (ξ := ξ) (σ := fun i => i.elim0)
    (σ' := fun i => i.elim0) (ς := fun i => i.elim0) trivial (ValueSide.DenS.sort hu ξ)
  rw [Normalization.subst_closed] at rel
  obtain ⟨P, hP, -, -⟩ := ValueSide.universeAt.den rel
  exact ⟨P, hP⟩

/-- **The datatype is a valid term of its universe**: the clause of a simple inductive type,
with the packs of its closed field types described by their interpretation, so that none is
chosen. -/
theorem dataTExt_valid_type :
    ModelSN.ValidTmS ((dataTExt hd avoid).model v) .nil (.const d.type) (.head d.typeUniverse) :=
  ModelSN.ValidTmS.inductiveType ((dataTExt hd avoid).laws v) (data_inductiveIn hd avoid v).role
    (data_inductiveIn hd avoid v).realRole (dataTExt_isUniverse hd avoid v hd.typeUniverse)
    (fun {_} ξ F => ValueSide.Pack.describe _ fun Q => ValueSide.InterpAt
      ((dataTExt hd avoid).model v).value (((dataTExt hd avoid).model v).levels.level
        d.typeUniverse) ξ (liftClosed F) Q)
    fun {_} ξ {F} hF => by
      obtain ⟨P, hP⟩ := closedField_interp hd avoid v hF ξ
      rw [ValueSide.Pack.describe_eq ((dataTExt hd avoid).valueLaws v).alg hP
        fun Q hQ => hQ.deterministic ((dataTExt hd avoid).valueLaws v) hP]
      exact hP

/-! ## Stages without the recursor -/

/-- The names of the stage of the datatype's type: every name but its recursor and its
constructors. -/
def dataTypeStage (d : Datatype Tower.Head) : DeclName → Bool :=
  fun c => !decide (c ∈ d.recursor :: d.ctors.map Prod.fst)

/-- The names of the stage of the datatype's constructors: every name but its recursor. -/
def dataCtorStage (d : Datatype Tower.Head) : DeclName → Bool := fun c => !decide (c = d.recursor)

/-- A level model of a package is one of the package restricted to some of its names. -/
def levelsRestrict {R : Rules Tower.Head} (levels : LevelModel R Nat) (allowed : DeclName → Bool) :
    LevelModel (R.restrict allowed) Nat :=
  { levels with }

omit avoid in
/-- The object package is contained in the package with a declared datatype restricted to names
that include the object package's. -/
theorem object_sub_dataRestrict {allowed : DeclName → Bool}
    (h : ∀ c, objectChurch.constantType c ≠ none → allowed c = true) :
    ChurchRulesSub objectChurch ((dataChurch d).restrict allowed) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun {c D} declared => by
    show (if allowed c then (dataChurch d).constantType c else none) = some D
    rw [if_pos (h c (by rw [declared]; exact nofun))]
    exact sumDecls_left declared
  computation := .inl
  requires := fun step required => ⟨_, .inl ⟨step, required⟩, fun _ member => member⟩

include hd in
theorem dataTypeStage_object {c : DeclName} (h : objectChurch.constantType c ≠ none) :
    dataTypeStage d c = true := by
  show (!decide (c ∈ d.recursor :: d.ctors.map Prod.fst)) = true
  rw [decide_eq_false fun mem => h (dataNames_new hd (List.mem_cons_of_mem _ mem))]
  rfl

include hd in
theorem dataCtorStage_object {c : DeclName} (h : objectChurch.constantType c ≠ none) :
    dataCtorStage d c = true := by
  simp only [dataCtorStage, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  rintro rfl
  exact h hd.new.recNew

include hd in
/-- The stage of the type declares the datatype's type, whose closed field types are types. -/
theorem dataTypeStage_declares :
    DeclaresDataType ((dataChurch d).restrict (dataTypeStage d)) d.type d.typeUniverse d.ctors where
  typeUniverse := hd.typeUniverse
  typeDeclared := by
    show (if dataTypeStage d d.type then (dataChurch d).constantType d.type else none) = _
    have allowed : dataTypeStage d d.type = true := by
      show (!decide (d.type ∈ d.recursor :: d.ctors.map Prod.fst)) = true
      rw [decide_eq_false fun mem => (List.mem_cons.1 mem).elim
        (fun e => hd.distinct.recNotType e.symm) hd.distinct.typeNotCtor]
      rfl
    rw [if_pos allowed]
    exact sum_type_declared objectChurch hd.new
  fieldsFormed := fun entry member F field =>
    ⟨d.typeUniverse, hd.typeUniverse,
      (hd.fields entry member F field).mono
        (object_sub_dataRestrict fun _ => dataTypeStage_object hd)⟩

include hd in
/-- The stage of the constructors declares the datatype's type and its constructors. -/
theorem dataCtorStage_declares :
    DeclaresDataCtors ((dataChurch d).restrict (dataCtorStage d)) d.type d.typeUniverse
      d.ctors where
  typeUniverse := hd.typeUniverse
  typeDeclared := by
    show (if dataCtorStage d d.type then (dataChurch d).constantType d.type else none) = _
    rw [if_pos (by
      simp only [dataCtorStage, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      exact Ne.symm hd.distinct.recNotType)]
    exact sum_type_declared objectChurch hd.new
  fieldsFormed := fun entry member F field =>
    ⟨d.typeUniverse, hd.typeUniverse,
      (hd.fields entry member F field).mono
        (object_sub_dataRestrict fun _ => dataCtorStage_object hd)⟩
  ctor := fun {i k fields} entry => by
    show (if dataCtorStage d k then (dataChurch d).constantType k else none) = _
    rw [if_pos (by
      simp only [dataCtorStage, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
      rintro rfl
      exact hd.distinct.recNotCtor (List.mem_map.2 ⟨_, List.mem_of_getElem? entry, rfl⟩))]
    exact sum_ctor_declared objectChurch hd.distinct hd.lamFree hd.new entry

/-! ## Soundness -/

/-- **Every root step of the package with a declared datatype is validated by the model**, in
every package that declares identity elimination as the object package does: the object
package's steps as in the transport value model, the recursor's rules as steps of the model's
reduction. -/
theorem data_root {R' : Rules Tower.Head}
    (declaredJ : R'.constantType jName = some (elimType (.sort Tower.zero) (.sort Tower.zero)))
    {n : Nat} {l r : Tower.Tm n} (step : (dataRules d).computation.step l r) :
    ModelSN.RootSemanticS ((dataTExt hd avoid).model v) l r ∨
      ModelSN.TypedRootS R' ((dataTExt hd avoid).model v) l r := by
  rcases step with step | iota
  · rcases step with step | step
    · exact (dataTExt hd avoid).stage_root v
        (fun _ => ⟨.sort Tower.zero, .sort Tower.zero, LevelTower.IsUniverse.sort _, declaredJ⟩)
        step
    · exact .inl (ModelSN.ModelRootS.semantic ((dataTExt hd avoid).laws v)
        ((dataTExt hd avoid).programDecodes v) (.inr step))
  · exact .inl (ModelSN.ModelRootS.semantic ((dataTExt hd avoid).laws v)
      ((dataTExt hd avoid).programDecodes v)
      (.inl ((dataTExt hd avoid).extraStep v List.mem_cons_self iota)))

omit hd avoid in
theorem dataRules_declared_j :
    (dataRules d).constantType jName = some (elimType (.sort Tower.zero) (.sort Tower.zero)) := by
  show sumDecls objectRules.constantType
    (inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse) jName = _
  rw [sumDecls_left objectRules_declared_j]
  rfl

/-- **A stage of the package with a declared datatype is sound for the model** when it has
identity elimination and its constants are valid. -/
theorem dataStage_soundS {allowed : DeclName → Bool} (hJ : allowed jName = true)
    (consts : ∀ {name : DeclName} {type : Tower.Tm 0}, allowed name = true →
      (dataRules d).constantType name = some type →
        ModelSN.ValidTmS ((dataTExt hd avoid).model v) .nil (.const name) type) :
    ModelSN.TypedSoundS ((dataRules d).restrict allowed) ((dataTExt hd avoid).model v) where
  laws := (dataTExt hd avoid).laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => data_root hd avoid v (by
    show (if allowed jName then (dataRules d).constantType jName else none) = _
    rw [if_pos hJ]
    exact dataRules_declared_j) step
  constants := fun {name type} declared => by
    change (if allowed name then (dataRules d).constantType name else none) = some type at declared
    split_ifs at declared with h
    exact consts h declared

include hd in
theorem jName_dataNames : jName ∉ dataNames d :=
  fun mem => objectChurch_constantType_ne_none (c := jName) (by decide) (dataNames_new hd mem)

/-- **Every constructor is a valid term of its declared type**: the clause of a constructor,
with its declared type valid by the fundamental lemma of the stage of the type. -/
theorem dataTExt_valid_ctor {k : DeclName} {fs : List CtorField} (mem : (k, fs) ∈ d.ctors) :
    ModelSN.ValidTmS ((dataTExt hd avoid).model v) .nil (.const k) (ctorType d.type fs) := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem mem
  obtain ⟨w, hw, typed⟩ := (dataTypeStage_declares hd).ctorType_formed
    (levelsRestrict (levelsWith ConvRules.objectLevels [.datatype d]) _) hi
  have typedRaw : Typed ((dataRules d).restrict (dataTypeStage d)) .nil (ctorType d.type fs)
      (.head w) := by
    have := CDerivable.erase typed
    rw [CStatement.erase, erase_liftTm] at this
    exact this
  have sound := dataStage_soundS hd avoid v (allowed := dataTypeStage d)
    (dataTypeStage_object hd (objectChurch_constantType_ne_none (by decide)))
    fun {name type} allowed declared => by
      rcases dataRules_declared_cases declared with object | ⟨rfl, rfl⟩ | ⟨j, fields, hj, rfl⟩ |
        ⟨rfl, rfl⟩
      · exact ((dataTExt hd avoid).soundS_objectRules v).constants object
      · exact dataTExt_valid_type hd avoid v
      · exfalso
        simp only [dataTypeStage, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
          List.mem_cons, not_or] at allowed
        exact allowed.2 (List.mem_map.2 ⟨_, List.mem_of_getElem? hj, rfl⟩)
      · exact absurd allowed (by
          unfold dataTypeStage
          rw [decide_eq_true List.mem_cons_self]
          exact Bool.false_ne_true)
  obtain ⟨validT, partsT, -⟩ := ModelSN.Derivable.validS sound typedRaw trivial
  exact ModelSN.ValidTmS.inductiveCtor ((dataTExt hd avoid).laws v)
    (data_inductiveIn hd avoid v).role (data_inductiveIn hd avoid v).realRole
    (dataConstructorsDeclared hd) mem
    (validT.validTy (dataTExt_isUniverse hd avoid v hw)) partsT

/-- **The recursor is a valid term of its declared type**: the clause of the recursor of a
simple inductive type, with its declared type valid by the fundamental lemma of the stage of
the constructors. -/
theorem dataTExt_valid_rec :
    ModelSN.ValidTmS ((dataTExt hd avoid).model v) .nil (.const d.recursor)
      (recType d.type d.motiveUniverse d.ctors) := by
  obtain ⟨w, hw, typed⟩ := (dataCtorStage_declares hd).recType_formed
    (levelsRestrict (levelsWith ConvRules.objectLevels [.datatype d]) _) hd.motiveUniverse
  have typedRaw : Typed ((dataRules d).restrict (dataCtorStage d)) .nil
      (recType d.type d.motiveUniverse d.ctors) (.head w) := by
    have := CDerivable.erase typed
    rw [CStatement.erase, erase_liftTm] at this
    exact this
  have sound := dataStage_soundS hd avoid v (allowed := dataCtorStage d)
    (dataCtorStage_object hd (objectChurch_constantType_ne_none (by decide)))
    fun {name type} allowed declared => by
      rcases dataRules_declared_cases declared with object | ⟨rfl, rfl⟩ | ⟨j, fields, hj, rfl⟩ |
        ⟨rfl, rfl⟩
      · exact ((dataTExt hd avoid).soundS_objectRules v).constants object
      · exact dataTExt_valid_type hd avoid v
      · exact dataTExt_valid_ctor hd avoid v (List.mem_of_getElem? hj)
      · exact absurd allowed (by
          unfold dataCtorStage
          rw [decide_eq_true rfl]
          exact Bool.false_ne_true)
  obtain ⟨validT, partsT, -⟩ := ModelSN.Derivable.validS sound typedRaw trivial
  exact ModelSN.ValidTmS.inductiveRec ((dataTExt hd avoid).laws v) (data_inductiveIn hd avoid v)
    (dataTExt_isUniverse hd avoid v hd.motiveUniverse)
    (validT.validTy (dataTExt_isUniverse hd avoid v hw)) partsT

/-- **Every constant of the package with a declared datatype is valid in the model.** -/
theorem dataTExt_valid_declared {name : DeclName} {type : Tower.Tm 0}
    (declared : (dataRules d).constantType name = some type) :
    ModelSN.ValidTmS ((dataTExt hd avoid).model v) .nil (.const name) type := by
  rcases dataRules_declared_cases declared with object | ⟨rfl, rfl⟩ | ⟨j, fields, hj, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact ((dataTExt hd avoid).soundS_objectRules v).constants object
  · exact dataTExt_valid_type hd avoid v
  · exact dataTExt_valid_ctor hd avoid v (List.mem_of_getElem? hj)
  · exact dataTExt_valid_rec hd avoid v

/-- **The package with a declared datatype is sound for the model, its root steps read with
their typing**: a root step of the object package as in the transport value model, a rule of
the recursor as a step of the model's reduction, and every constant valid. -/
theorem dataRules_soundS : ModelSN.TypedSoundS (dataRules d) ((dataTExt hd avoid).model v) where
  laws := (dataTExt hd avoid).laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => data_root hd avoid v dataRules_declared_j step
  constants := dataTExt_valid_declared hd avoid v

end Model

/-! ## Strong normalization -/

section SN

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch) (avoid : AvoidsModelNames d)
include hd avoid

/-- **Strong normalization of the object package with an admissible declared datatype.** Every
term typed in a formed context of the package is strongly normalizing under the package's own
reduction, and so is its type. -/
theorem dataRules_sn {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n}
    (formed : CtxFormed (dataRules d) Γ) (typed : Typed (dataRules d) Γ t A) :
    SN (dataRules d) t ∧ SN (dataRules d) A :=
  ModelSN.Typed.sn (dataRules_soundS hd avoid fun _ => 0) formed typed

/-- Both sides of a derivable equality of the package with a declared datatype in a formed
context are strongly normalizing, and so is their type. -/
theorem dataRules_equal_sn {n : Nat} {Γ : Tower.Ctx n} {a b A : Tower.Tm n}
    (formed : CtxFormed (dataRules d) Γ) (equal : Derivable (dataRules d) (.equality Γ a b A)) :
    SN (dataRules d) a ∧ SN (dataRules d) b ∧ SN (dataRules d) A :=
  ModelSN.Equal.sn (dataRules_soundS hd avoid fun _ => 0) formed equal

end SN



/-! ## Coherence -/

/-- The universe laws of the package with a declared datatype are the object package's. -/
theorem dataRules_algebra (d : Datatype Tower.Head) : CumulativeAlgebra (dataRules d) where
  trans := (ConvRules.realRules_algebra objectTExt).trans
  same_left := (ConvRules.realRules_algebra objectTExt).same_left
  same_right := (ConvRules.realRules_algebra objectTExt).same_right
  join_least := (ConvRules.realRules_algebra objectTExt).join_least

section Coherence

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch) (avoid : AvoidsModelNames d)

include hd avoid in
/-- **The facts coherence is proved from, for the package with a declared datatype**: the
injectivity and no-confusion of its annotated type formers, and strong normalization. -/
theorem dataCoherenceFacts : CoherenceFacts (dataChurch d) :=
  CoherenceFacts.ofSN (dataFormerFacts hd) fun formed typed =>
    (dataRules_sn hd avoid formed typed).1

include hd avoid in
/-- **Coherence of annotations for the package with a declared datatype**: two annotated terms
with one erasure, typed at one type, are equal at it. -/
theorem dataCoherence {n : Nat} {Γ : CCtx Tower.Head n} (formed : CCtxFormed (dataChurch d) Γ)
    {t t' A : CTm Tower.Head n} (typing : CTyped (dataChurch d) Γ t A)
    (typing' : CTyped (dataChurch d) Γ t' A) (same : t.erase = t'.erase) :
    CEqual (dataChurch d) Γ t t' A :=
  coherence (dataCoherenceFacts hd avoid) (dataExtension hd).levels (dataRules_algebra d)
    formed typing typing' same

end Coherence

/-! ## The declarations of the package with a declared datatype -/

section Declarations

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)
include hd

/-- The type of the datatype is declared at its universe. -/
theorem data_type_declared :
    (dataChurch d).constantType d.type = some (.head d.typeUniverse) :=
  sum_type_declared objectChurch hd.new

/-- A constructor is declared at the type of its fields. -/
theorem data_ctor_declared {i : Nat} {k : DeclName} {fs : List CtorField}
    (entry : d.ctors[i]? = some (k, fs)) :
    (dataChurch d).constantType k = some (liftTm (ctorType d.type fs)) :=
  sum_ctor_declared objectChurch hd.distinct hd.lamFree hd.new entry

/-- The recursor is declared at its type. -/
theorem data_rec_declared :
    (dataChurch d).constantType d.recursor =
      some (liftTm (recType d.type d.motiveUniverse d.ctors)) :=
  sum_rec_declared objectChurch hd.distinct hd.lamFree hd.new

/-- **The declared constants of the package with a declared datatype**: the object package's,
at their types there, the type of the datatype, its constructors and its recursor. -/
theorem dataChurch_declared_cases {c : DeclName} {D : CTm Tower.Head 0}
    (declared : (dataChurch d).constantType c = some D) :
    objectChurch.constantType c = some D ∨ (c = d.type ∧ D = .head d.typeUniverse) ∨
      (∃ (i : Nat) (fs : List CtorField), d.ctors[i]? = some (c, fs) ∧
        D = liftTm (ctorType d.type fs)) ∨
      (c = d.recursor ∧ D = liftTm (recType d.type d.motiveUniverse d.ctors)) := by
  have declared' : sumDecls objectChurch.constantType
      (inductiveChurch objectRules d.type d.typeUniverse d.ctors d.recursor
        d.motiveUniverse).constantType c = some D := declared
  cases hobj : objectChurch.constantType c with
  | some D₀ =>
      rw [sumDecls_left hobj] at declared'
      exact .inl declared'
  | none =>
      rw [sumDecls_right hobj] at declared'
      exact .inr (inductiveChurch_constantType objectRules hd.lamFree declared')

/-- A constant the package with a declared datatype declares is the object package's, at the
same type, or one of the datatype's names. -/
theorem dataChurch_declared_object_or {c : DeclName} {D : CTm Tower.Head 0}
    (declared : (dataChurch d).constantType c = some D) :
    objectChurch.constantType c = some D ∨ c ∈ dataNames d := by
  rcases dataChurch_declared_cases hd declared with object | ⟨rfl, -⟩ | ⟨i, fs, hi, -⟩ |
    ⟨rfl, -⟩
  · exact .inl object
  · exact .inr List.mem_cons_self
  · exact .inr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.2 ⟨_, List.mem_of_getElem? hi, rfl⟩)))
  · exact .inr (List.mem_cons_of_mem _ List.mem_cons_self)

/-- A constant the package with a declared datatype declares, outside the datatype's names, is
the object package's at the same type. -/
theorem dataChurch_declared_object {c : DeclName} {D : CTm Tower.Head 0}
    (declared : (dataChurch d).constantType c = some D) (h : c ∉ dataNames d) :
    objectChurch.constantType c = some D :=
  (dataChurch_declared_object_or hd declared).resolve_right h

omit hd in
/-- The object package's constants are declared at their types. -/
theorem data_declared_of_object {c : DeclName} {D : CTm Tower.Head 0}
    (declared : objectChurch.constantType c = some D) :
    (dataChurch d).constantType c = some D :=
  (withDeclarations_base objectChurch [.datatype d]).constantType declared

/-- The type of the datatype is no name the object package declares, so neither the numbers
nor the codes. -/
theorem data_type_ne {c : DeclName} (h : objectChurch.constantType c ≠ none) : d.type ≠ c :=
  fun e => h (e ▸ hd.new.typeNew)

/-- **A computing constant of the package with a declared datatype** is its recursor, which
inspects its last argument after the motive and the methods, or computes as in the object
package. -/
theorem dataRoles_computes {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : dataRoles d c = .computes arity inspect) :
    (c = d.recursor ∧ arity = d.ctors.length + 2 ∧
        inspect = .split (d.ctors.length + 1) .constructor fun _ => .leaf) ∨
      (c ∉ dataNames d ∧ objectRoles c = .computes arity inspect) := by
  by_cases mem : c ∈ dataNames d
  · left
    simp only [dataNames, List.mem_cons] at mem
    rcases mem with rfl | rfl | mem
    · cases (dataRoles_type (base := objectRoles)).symm.trans role
    · have h := (dataRoles_rec (base := objectRoles) hd.distinct).symm.trans role
      injection h with h₁ h₂
      exact ⟨rfl, h₁.symm, h₂.symm⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 mem
      obtain ⟨i, hi⟩ := List.getElem?_of_mem he
      cases (dataRoles_ctor (base := objectRoles) hd.distinct hi).symm.trans role
  · exact .inr ⟨mem, (dataRoles_outside mem).symm.trans role⟩

end Declarations

/-! ## Telescopes of declared types -/

section Telescopes

open Presentation.TypedEquality.Annotated.Progress (afterBinders isPiTest domainTest
  afterBinders_isPi_le)
open TelescopeAbstraction (closeType)

variable {Head : Type}

/-- **After the binders of its telescope, a declared type is its body.** -/
theorem afterBinders_liftTm_closeType (test : ∀ {m : Nat}, CTm Head m → Bool) :
    ∀ {n : Nat} (Θ : Ctx Head n) (C : Tm Head n) (k : Nat),
      afterBinders test (k + n) (liftTm (closeType Θ C)) = afterBinders test k (liftTm C)
  | _, .nil, _, _ => rfl
  | n + 1, .snoc Θ A, C, k => by
      rw [show k + (n + 1) = (k + 1) + n by omega]
      exact afterBinders_liftTm_closeType test Θ (.pi A C) (k + 1)

/-- The domain of the last binder of a declared type. -/
theorem afterBinders_domain_closeType (test : ∀ {m : Nat}, CTm Head m → Bool) {n : Nat}
    (Θ : Ctx Head n) (A : Tm Head n) (C : Tm Head (n + 1)) :
    afterBinders (domainTest test) n (liftTm (closeType (.snoc Θ A) C)) = test (liftTm A) := by
  have h := afterBinders_liftTm_closeType (domainTest test) Θ (.pi A C) 0
  rw [Nat.zero_add] at h
  exact h

/-- Every binder of the telescope of a declared type is a dependent function type. -/
theorem afterBinders_isPi_closeType :
    ∀ {n : Nat} (Θ : Ctx Head n) (C : Tm Head n) (j : Nat), j < n →
      afterBinders isPiTest j (liftTm (closeType Θ C)) = true
  | 0, _, _, j, h => absurd h (Nat.not_lt_zero j)
  | n + 1, .snoc Θ A, C, j, h => by
      have last := afterBinders_liftTm_closeType isPiTest Θ (.pi A C) 0
      rw [Nat.zero_add] at last
      exact afterBinders_isPi_le (Nat.le_of_lt_succ h) (last.trans rfl)

/-- **`F₁ → ⋯ → Fₐ → C` over closed types**, in every context. -/
def cArrows {n : Nat} : List (CTm Head 0) → CTm Head 0 → CTm Head n
  | [], C => C.liftClosed
  | F :: Fs, C => .pi F.liftClosed (cArrows Fs C)

/-- Closed function types are kept by substitution. -/
theorem cArrows_subst : ∀ (Fs : List (CTm Head 0)) (C : CTm Head 0) {n m : Nat}
    (σ : CSub Head n m), (cArrows Fs C : CTm Head n).subst σ = cArrows Fs C
  | [], C, _, _, σ => CTm.subst_liftClosed σ C
  | F :: Fs, C, _, _, σ => by
      show CTm.pi (F.liftClosed.subst σ) ((cArrows Fs C).subst (CTm.liftSub σ)) = _
      rw [CTm.subst_liftClosed, cArrows_subst Fs C]
      rfl

/-- Closed function types are kept by renaming. -/
theorem cArrows_rename : ∀ (Fs : List (CTm Head 0)) (C : CTm Head 0) {n m : Nat}
    (ρ : Ren n m), (cArrows Fs C : CTm Head n).rename ρ = cArrows Fs C
  | [], C, _, _, ρ => CTm.rename_liftClosed ρ C
  | F :: Fs, C, _, _, ρ => by
      show CTm.pi (F.liftClosed.rename ρ) ((cArrows Fs C).rename (liftRen ρ)) = _
      rw [CTm.rename_liftClosed, cArrows_rename Fs C]
      rfl

theorem liftClosed_cArrows (Fs : List (CTm Head 0)) (C : CTm Head 0) {n : Nat} :
    ((cArrows Fs C : CTm Head 0).liftClosed : CTm Head n) = cArrows Fs C :=
  cArrows_rename Fs C _

theorem cArrows_append (C : CTm Head 0) (M : List (CTm Head 0)) :
    ∀ (L : List (CTm Head 0)) {n : Nat},
      (cArrows L (cArrows M C) : CTm Head n) = cArrows (L ++ M) C
  | [], _ => liftClosed_cArrows M C
  | F :: L, _ => by
      show CTm.pi F.liftClosed (cArrows L (cArrows M C)) = CTm.pi F.liftClosed (cArrows (L ++ M) C)
      rw [cArrows_append C M L]

/-- **A telescope of closed entries is a closed function type.** -/
theorem liftTm_closeType_closed (G : Nat → Tm Head 0) :
    ∀ (N : Nat) (C : Tm Head 0),
      liftTm (closeType (ofEntries (fun j => Presentation.liftClosed (G j)) N)
          (Presentation.liftClosed C)) =
        (cArrows ((List.range N).map fun j => liftTm (G j)) (liftTm C) : CTm Head 0)
  | 0, C => by
      show liftTm (Presentation.liftClosed C : Tm Head 0) = CTm.liftClosed (liftTm C)
      rw [liftTm_liftClosed]
  | N + 1, C => by
      have step : (Tm.pi (Presentation.liftClosed (G N)) (Presentation.liftClosed C) :
          Tm Head N) = Presentation.liftClosed (Tm.pi (G N) (Presentation.liftClosed C)) := by
        show _ = Tm.pi (Presentation.liftClosed (G N)) (Presentation.rename (liftRen Fin.elim0)
          (Presentation.liftClosed C : Tm Head 1))
        rw [Presentation.rename_liftClosed]
      have last : (liftTm (Tm.pi (G N) (Presentation.liftClosed C)) : CTm Head 0) =
          cArrows [liftTm (G N)] (liftTm C) := by
        show CTm.pi (liftTm (G N)) (liftTm (Presentation.liftClosed C : Tm Head 1)) =
          CTm.pi (CTm.liftClosed (liftTm (G N))) (CTm.liftClosed (liftTm C))
        rw [liftTm_liftClosed, CTm.liftClosed_zero]
      show liftTm (closeType (ofEntries (fun j => Presentation.liftClosed (G j)) N)
        (Tm.pi (Presentation.liftClosed (G N)) (Presentation.liftClosed C))) = _
      rw [step, liftTm_closeType_closed G N, last, cArrows_append, List.range_succ,
        List.map_append, List.map_cons, List.map_nil]

/-- **The declared type of a constructor is the closed function type of its fields.** -/
theorem liftTm_ctorType (T : DeclName) (fs : List (Normalization.Field Head)) :
    liftTm (ctorType T fs) =
      (cArrows (fs.map fun f => liftTm (f.type T)) (.const T) : CTm Head 0) := by
  have h := liftTm_closeType_closed (fun j => (fs.getD j .recursive).type T) fs.length (.const T)
  have e : (List.range fs.length).map (fun j => liftTm ((fs.getD j .recursive).type T)) =
      fs.map fun f => liftTm (f.type T) := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_map, List.length_range]
    · intro j h₁ h₂
      have hj : j < fs.length := by rwa [List.length_map, List.length_range] at h₁
      rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hj, Option.getD_some]
  rw [e] at h
  exact h

variable {R : Rules Head} {P : ChurchRules R} {L : Type} [LevelOrder L]

/-- **The arguments of a spine at a closed function type**: when a principal type of the head
is `F₁ → ⋯ → Fₐ → C` over closed types, each argument of a typed spine of `a` arguments is
typed at its `Fᵢ`. -/
theorem forall₂_typed_of_cArrows (formers : CFormerFacts P) (levels : LevelModel R L)
    {n : Nat} {Γ : CCtx Head n} (formed : CCtxFormed P Γ) (C : CTm Head 0) :
    ∀ (Fs : List (CTm Head 0)) (args : List (CTm Head n)) {f T : CTm Head n},
      args.length = Fs.length → Annotated.Progress.PrincipalType P Γ f (cArrows Fs C) →
      CTyped P Γ (CTm.appSpine f args) T →
      List.Forall₂ (fun a F => CTyped P Γ a F.liftClosed) args Fs
  | [], [], _, _, _, _, _ => .nil
  | [], _ :: _, _, _, length, _, _ => absurd length (Nat.succ_ne_zero _)
  | _ :: _, [], _, _, length, _, _ => absurd length.symm (Nat.succ_ne_zero _)
  | F :: Fs, a :: as, f, _, length, principal, typing => by
      obtain ⟨S, tS⟩ := Annotated.Progress.typed_appSpine_fun as (f := .app f a) typing
      have parts := Annotated.Progress.principal_app formers levels formed (a := a)
        (A := F.liftClosed) (B := cArrows Fs C) principal
      have e : CTm.inst0 a (cArrows Fs C : CTm Head (n + 1)) = cArrows Fs C :=
        cArrows_subst Fs C _
      have principal' : Annotated.Progress.PrincipalType P Γ (.app f a) (cArrows Fs C) :=
        fun typing => by
          rw [← e]
          exact parts.1 typing
      exact .cons (parts.2 tS)
        (forall₂_typed_of_cArrows formers levels formed C Fs as (Nat.succ.inj length) principal'
          typing)

end Telescopes

/-! ## The binders of the declared types of a datatype -/

section DeclaredTypes

open Presentation.TypedEquality.Annotated.Progress (afterBinders isPiTest domainTest)
open TelescopeAbstraction (closeType)

variable {Head : Type}

/-- A constructor's declared type returns its datatype after its fields. -/
theorem afterBinders_ctorType (test : ∀ {m : Nat}, CTm Head m → Bool) (T : DeclName)
    (fs : List (Normalization.Field Head)) :
    afterBinders test fs.length (liftTm (ctorType T fs)) =
      test (.const T : CTm Head fs.length) := by
  have h := afterBinders_liftTm_closeType test (ctorTele T fs) (.const T) 0
  rw [Nat.zero_add] at h
  exact h

/-- The last entry of the recursor's telescope is the datatype, its scrutinee. -/
theorem recEntry_scrutinee (T : DeclName) (v : Head)
    (ctors : List (DeclName × List (Normalization.Field Head))) :
    recEntry T v ctors (ctors.length + 1) = .const T := by
  simp only [recEntry, List.getElem?_eq_none (Nat.le_refl ctors.length)]

/-- The recursor's declared type inspects the datatype at its scrutinee, after the motive and
the methods. -/
theorem afterBinders_domain_recType (test : ∀ {m : Nat}, CTm Head m → Bool) (T : DeclName)
    (v : Head) (ctors : List (DeclName × List (Normalization.Field Head))) :
    afterBinders (domainTest test) (ctors.length + 1) (liftTm (recType T v ctors)) =
      test (.const T : CTm Head (ctors.length + 1)) := by
  have h := afterBinders_domain_closeType test (ofEntries (recEntry T v ctors) (ctors.length + 1))
    (recEntry T v ctors (ctors.length + 1)) (recBody ctors.length)
  exact h.trans (congrArg (fun A => test (liftTm A)) (recEntry_scrutinee T v ctors))

end DeclaredTypes

/-! ## Progress at a declared datatype -/

section Progress

open Presentation.TypedEquality.Annotated.Progress (ProgressFacts FitsConst RelevantConst
  ScrutineeCanonical ScrutineeDecl afterBinders isPiTest isConstTest isIdTest domainTest
  relevant_of_result relevant_of_domain inductive_typeForm neutral_typeForm)

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)
include hd

/-- The type of the datatype is not the numbers: those are the object package's. -/
theorem data_type_ne_num : d.type ≠ numN :=
  data_type_ne hd (objectChurch_constantType_ne_none (by decide))

/-- The type of the datatype is not the codes: those are the object package's. -/
theorem data_type_ne_prop : d.type ≠ propN :=
  data_type_ne hd (objectChurch_constantType_ne_none (by decide))

/-- A constructor of the package with a declared datatype returns its type constant after its
fields: the object package's as in the object package, the datatype's at the datatype. -/
theorem data_constructorShape {k : DeclName} {arity : Nat}
    (role : dataRoles d k = .constructor arity) :
    ∃ (D : CTm Tower.Head 0) (C : DeclName), (dataChurch d).constantType k = some D ∧
      afterBinders (isConstTest C) arity D = true ∧
      ∀ j, j < arity → afterBinders isPiTest j D = true := by
  rcases dataRoles_constructor hd.distinct role with ⟨fs, mem, rfl⟩ | ⟨-, role₀⟩
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem mem
    exact ⟨_, d.type, data_ctor_declared hd hi,
      (afterBinders_ctorType (isConstTest d.type) d.type fs).trans (decide_eq_true rfl),
      fun j h => afterBinders_isPi_closeType _ _ j h⟩
  · obtain ⟨D, C, declared, result, pis⟩ := Progress.object_constructorShape role₀
    exact ⟨D, C, data_declared_of_object declared, result, pis⟩

/-- A computing constant of the package with a declared datatype has one binder per argument,
and the recursor inspects its scrutinee, of the datatype. -/
theorem data_declaredComputing {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : dataRoles d c = .computes arity inspect) :
    ∃ D, (dataChurch d).constantType c = some D ∧
      (∀ j, j < arity → afterBinders isPiTest j D = true) ∧ ScrutineeDecl arity inspect D := by
  rcases dataRoles_computes hd role with ⟨rfl, rfl, rfl⟩ | ⟨-, role₀⟩
  · exact ⟨_, data_rec_declared hd, fun j h => afterBinders_isPi_closeType _ _ j h,
      .const (d.ctors.length + 1) d.type rfl (Nat.lt_succ_self _)
        ((afterBinders_domain_recType (isConstTest d.type) d.type d.motiveUniverse d.ctors).trans
          (decide_eq_true rfl))⟩
  · obtain ⟨D, declared, pis, shape⟩ := Progress.object_declaredComputing role₀
    exact ⟨D, data_declared_of_object declared, pis, shape⟩

/-- **A canonical form of the datatype** is a listed constructor applied to as many terms as
it has fields. -/
theorem data_fits {n : Nat} {x : CTm Tower.Head n}
    (fits : FitsConst (dataChurch d) (dataRoles d) d.type x) :
    ∃ (i : Nat) (k : DeclName) (fs : List CtorField) (args : List (CTm Tower.Head n)),
      d.ctors[i]? = some (k, fs) ∧ args.length = fs.length ∧
        x = CTm.appSpine (.const k) args := by
  obtain ⟨k, arity, args, D, role, length, rfl, declared, result⟩ := fits
  rcases dataRoles_constructor hd.distinct role with ⟨fs, mem, rfl⟩ | ⟨notMem, role₀⟩
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem mem
    exact ⟨i, k, fs, args, hi, length, rfl⟩
  · exfalso
    rcases Progress.relevant_num_or_prop
        (relevant_of_result role₀ (dataChurch_declared_object hd declared notMem) result) with
      h | h
    · exact data_type_ne_num hd h
    · exact data_type_ne_prop hd h

/-- A canonical form of the numbers or of the codes in the package with a declared datatype is
one in the object package: the datatype's constructors return the datatype. -/
theorem fitsConst_object {C : DeclName} (hC : C = numN ∨ C = propN) {n : Nat}
    {x : CTm Tower.Head n} (fits : FitsConst (dataChurch d) (dataRoles d) C x) :
    FitsConst objectChurch objectRoles C x := by
  obtain ⟨k, arity, args, D, role, length, rfl, declared, result⟩ := fits
  rcases dataRoles_constructor hd.distinct role with ⟨fs, mem, rfl⟩ | ⟨notMem, role₀⟩
  · exfalso
    obtain ⟨i, hi⟩ := List.getElem?_of_mem mem
    obtain rfl := Option.some.inj ((data_ctor_declared hd hi).symm.trans declared)
    have e : d.type = C :=
      of_decide_eq_true ((afterBinders_ctorType (isConstTest C) d.type fs).symm.trans result)
    rcases hC with rfl | rfl
    · exact data_type_ne_num hd e
    · exact data_type_ne_prop hd e
  · exact ⟨k, arity, args, D, role₀, length, rfl, dataChurch_declared_object hd declared notMem,
      result⟩

/-- A canonical scrutinee of an object constant in the package with a declared datatype is one
in the object package. -/
theorem scrutineeCanonical_object {c : DeclName} {arity : Nat} {inspect : InspectTree}
    {D : CTm Tower.Head 0} (role : objectRoles c = .computes arity inspect)
    (declared : objectChurch.constantType c = some D) (shape : ScrutineeDecl arity inspect D)
    {n : Nat} {args : List (CTm Tower.Head n)}
    (canonical : ScrutineeCanonical (dataChurch d) (dataRoles d) inspect D args) :
    ScrutineeCanonical objectChurch objectRoles inspect D args := by
  cases shape with
  | leaf h =>
      subst h
      exact trivial
  | const pos C h _ _ =>
      subst h
      obtain ⟨before, x, after, e, hlen, canon⟩ := canonical
      refine ⟨before, x, after, e, hlen, ?_⟩
      rcases canon with ⟨C', hdom, fits⟩ | ⟨hid, refl⟩
      · exact .inl ⟨C', hdom, fitsConst_object hd
          (Progress.relevant_num_or_prop (relevant_of_domain role declared hdom)) fits⟩
      · exact .inr ⟨hid, refl⟩
  | ident pos h _ _ =>
      subst h
      obtain ⟨before, x, after, e, hlen, canon⟩ := canonical
      refine ⟨before, x, after, e, hlen, ?_⟩
      rcases canon with ⟨C', hdom, fits⟩ | ⟨hid, refl⟩
      · exact .inl ⟨C', hdom, fitsConst_object hd
          (Progress.relevant_num_or_prop (relevant_of_domain role declared hdom)) fits⟩
      · exact .inr ⟨hid, refl⟩

omit hd in
/-- **The recursor computes at every constructor**: applied to a motive, the methods and a
constructor spine of the datatype, it takes a root step. -/
theorem data_recStep {n : Nat} (before : List (CTm Tower.Head n))
    (hlen : before.length = d.ctors.length + 1) {i : Nat} {k : DeclName} {fs : List CtorField}
    (hi : d.ctors[i]? = some (k, fs)) (xs : List (CTm Tower.Head n)) (hxs : xs.length = fs.length) :
    ∃ r, (dataChurch d).computation.step
      (CTm.appSpine (.const d.recursor) (before ++ [CTm.appSpine (.const k) xs])) r := by
  cases before with
  | nil => exact absurd hlen (Nat.succ_ne_zero _).symm
  | cons p ms =>
      have hms : ms.length = d.ctors.length := Nat.succ.inj hlen
      have hlt : i < (ms.map CTm.erase).length := by
        rw [List.length_map, hms]
        rcases Nat.lt_or_ge i d.ctors.length with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none hge] at hi
          cases hi
      have raw : (inductiveRules objectRules d.type d.typeUniverse d.ctors d.recursor
          d.motiveUniverse).computation.step
          (CTm.appSpine (.const d.recursor) (p :: ms ++ [CTm.appSpine (.const k) xs])).erase
          (appSpine (ms.map CTm.erase)[i] (xs.map CTm.erase ++
            (recArgs fs (xs.map CTm.erase)).map
              (recApp d.recursor (p.erase :: ms.map CTm.erase)))) :=
        ⟨p.erase, ms.map CTm.erase, i, k, fs, xs.map CTm.erase, (ms.map CTm.erase)[i],
          by rw [List.length_map, hms], hi, by rw [List.length_map, hxs],
          List.getElem?_eq_getElem hlt,
          by
            rw [CTm.erase_appSpine, List.map_append, List.map_cons, List.map_cons, List.map_nil,
              CTm.erase_appSpine]
            rfl,
          rfl⟩
      obtain ⟨r, step, -⟩ := ChurchRules.ofSchemas_lift (iotaSchema d.recursor d.ctors)
        (iota_presents d.recursor d.ctors) (iotaSchema_firstOrder _ _) raw
      exact ⟨r, .inr step⟩

/-- A computing constant of the package with a declared datatype takes a root step at every
canonical scrutinee: the object package's constants by their own steps, the recursor by its
rule at the constructor. -/
theorem data_rootCoverage {c : DeclName} {arity : Nat} {inspect : InspectTree}
    {D : CTm Tower.Head 0} (role : dataRoles d c = .computes arity inspect)
    (declared : (dataChurch d).constantType c = some D) {n : Nat}
    (args : List (CTm Tower.Head n)) (length : args.length = arity)
    (canonical : ScrutineeCanonical (dataChurch d) (dataRoles d) inspect D args) :
    ∃ r, (dataChurch d).computation.step (CTm.appSpine (.const c) args) r := by
  rcases dataRoles_computes hd role with ⟨rfl, rfl, rfl⟩ | ⟨-, role₀⟩
  · obtain rfl := Option.some.inj ((data_rec_declared hd).symm.trans declared)
    obtain ⟨before, x, after, rfl, hlen, canon⟩ := canonical
    have hafter : after = [] := by
      rw [List.length_append, List.length_cons, hlen] at length
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hafter
    rcases canon with ⟨C, hdom, fits⟩ | ⟨hid, -⟩
    · have eC : d.type = C := of_decide_eq_true
        ((afterBinders_domain_recType (isConstTest C) d.type d.motiveUniverse d.ctors).symm.trans
          hdom)
      subst eC
      obtain ⟨i, k, fs, xs, hi, hxs, rfl⟩ := data_fits hd fits
      exact data_recStep before hlen hi xs hxs
    · exact absurd
        ((afterBinders_domain_recType isIdTest d.type d.motiveUniverse d.ctors).symm.trans hid)
        Bool.false_ne_true
  · obtain ⟨D₀, declared₀, -, shape⟩ := Progress.object_declaredComputing role₀
    obtain rfl := Option.some.inj ((data_declared_of_object declared₀).symm.trans declared)
    obtain ⟨r, step⟩ := Progress.object_rootCoverage role₀ declared₀ args length
      (scrutineeCanonical_object hd role₀ declared₀ shape canonical)
    exact ⟨r, .inl step⟩

/-- The type constants a canonical form or an inspection of the package with a declared
datatype names are the numbers, the codes and the datatype. -/
theorem data_relevant {C : DeclName} (rel : RelevantConst (dataChurch d) (dataRoles d) C) :
    C = numN ∨ C = propN ∨ C = d.type := by
  rcases rel with ⟨_, role⟩ | ⟨k, arity, D, role, declared, result⟩ |
    ⟨c, arity, D, pos, role, declared, domain⟩
  · rcases dataRoles_inductive objectRoles_inductive role with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact .inl rfl
    · exact .inr (.inr rfl)
  · rcases dataRoles_constructor hd.distinct role with ⟨fs, mem, rfl⟩ | ⟨notMem, role₀⟩
    · obtain ⟨i, hi⟩ := List.getElem?_of_mem mem
      obtain rfl := Option.some.inj ((data_ctor_declared hd hi).symm.trans declared)
      exact .inr (.inr (of_decide_eq_true
        ((afterBinders_ctorType (isConstTest C) d.type fs).symm.trans result)).symm)
    · rcases Progress.relevant_num_or_prop
          (relevant_of_result role₀ (dataChurch_declared_object hd declared notMem) result) with
        h | h
      · exact .inl h
      · exact .inr (.inl h)
  · rcases dataRoles_computes hd role with ⟨rfl, -, e⟩ | ⟨notMem, role₀⟩
    · injection e with e₁
      subst e₁
      obtain rfl := Option.some.inj ((data_rec_declared hd).symm.trans declared)
      exact .inr (.inr (of_decide_eq_true
        ((afterBinders_domain_recType (isConstTest C) d.type d.motiveUniverse d.ctors).symm.trans
          domain)).symm)
    · rcases Progress.relevant_num_or_prop
          (relevant_of_domain role₀ (dataChurch_declared_object hd declared notMem) domain) with
        h | h
      · exact .inl h
      · exact .inr (.inl h)

/-- The relevant type constants are types in weak-head form. -/
theorem relevant_typeForm {C : DeclName} (h : C = numN ∨ C = propN ∨ C = d.type) {n : Nat} :
    IsTypeForm (dataRoles d) (CTm.const C : CTm Tower.Head n).erase := by
  rcases h with rfl | rfl | rfl
  · exact inductive_typeForm ((dataRoles_object hd (by decide)).trans objectRoles_num)
  · exact neutral_typeForm (Neutral.rigid (c := propN) [] (dataExtension hd).roles_prop)
  · exact inductive_typeForm dataRoles_type

/-- **The obligations of progress for the package with a declared datatype**: the object
package's constants as in the object package, the datatype's constructors and recursor by their
declared types and the recursor's rules, and the no-confusion of the numbers, the codes and the
datatype, from the facts about the weak-head forms of its annotated types. -/
theorem dataProgressFacts : ProgressFacts (dataChurch d) (dataRoles d) where
  formers := dataFormerFacts hd
  constructorShape := data_constructorShape hd
  declaredComputing := data_declaredComputing hd
  rootCoverage := data_rootCoverage hd
  inductiveDeclared := fun role => by
    rcases dataRoles_inductive objectRoles_inductive role with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨.sort Tower.zero, (dataExtension hd).sort _,
        data_declared_of_object Progress.declared_num⟩
    · exact ⟨d.typeUniverse, hd.typeUniverse, data_type_declared hd⟩
  formerNeConst := by
    intro C rel n Γ X formed former equal
    have matching := ((dataFormFacts hd).forms equal formed former.typeForm
      (relevant_typeForm hd (data_relevant hd rel))).formers_left former
    exact nomatch matching.right
  constDistinct := by
    intro C C' rel rel' distinct n Γ formed equal
    have propOf : ∀ {C : DeclName}, C = numN ∨ C = propN ∨ C = d.type →
        Neutral (dataRoles d) (CTm.const C : CTm Tower.Head n).erase → C = propN := by
      intro C h neutral
      rcases h with rfl | rfl | rfl
      · exact absurd rfl (neutral.ne_inductive
          ((dataRoles_object hd (by decide)).trans objectRoles_num))
      · rfl
      · exact absurd rfl (neutral.ne_inductive dataRoles_type)
    rcases (dataFormFacts hd).forms equal formed (relevant_typeForm hd (data_relevant hd rel))
        (relevant_typeForm hd (data_relevant hd rel')) with
      matching | ⟨T, cs, _, e₁, e₂⟩ | ⟨neutral, neutral'⟩
    · rcases matching with ⟨_, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ | ⟨_, _, _, _, e, _⟩ |
        ⟨_, _, _, _, _, _, e, _⟩ <;> cases e
    · exact distinct (CTm.const.inj (e₁.trans e₂.symm))
    · exact distinct ((propOf (data_relevant hd rel) neutral).trans
        (propOf (data_relevant hd rel') neutral').symm)

/-- **Progress for the package with a declared datatype**: a typed annotated term of a formed
context takes an annotated weak-head step or is a weak-head normal form. -/
theorem dataChurch_progress {n : Nat} {Γ : CCtx Tower.Head n}
    {t T : CTm Tower.Head n} (formed : CCtxFormed (dataChurch d) Γ)
    (typing : CTyped (dataChurch d) Γ t T) :
    Annotated.Progress.Progresses (dataChurch d) (dataRoles d) t :=
  Annotated.Progress.progress (dataProgressFacts hd) (dataExtension hd).levels
    (dataRules_algebra d) formed typing

end Progress

/-! ## Closed neutral terms -/

section ClosedNeutral

open Presentation.TypedEquality.Annotated.Progress (PrincipalType SortKey ctmSize
  ctmSize_lt_appSpine typed_appSpine_fun principal_const principal_app argument_const
  argument_typed below_kind_false relevant_of_domain relevant_of_inductive afterBinders_liftClosed
  domainTest_stable isIdTest_stable isIdTest_inv ScrutineeDecl)

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)

include hd in
/-- The sets are a neutral type: a rigid constant. -/
theorem set_neutral {n : Nat} : Neutral (dataRoles d) (CTm.const setN : CTm Tower.Head n).erase :=
  Neutral.rigid (c := setN) [] (dataExtension hd).roles_set

open Presentation.TypedEquality.Impredicative.Domain in
include hd in
/-- **The sets are not the codes**: the reading reads them by different tags. -/
theorem set_ne_prop :
    ¬ CTypeEq (dataChurch d) (.nil : CCtx Tower.Head 0) (.const setN) (.const propN) := by
  rintro ⟨u, -, e⟩
  have h : cinterp (dataExtension hd).reading (.const setN : CTm Tower.Head 0) Env.nil =
      cinterp (dataExtension hd).reading (.const propN) Env.nil :=
    CEqual.sound (dataExtension hd).valid e trivial
  change (dataExtension hd).reading.const setN = (dataExtension hd).reading.const propN at h
  rw [(dataExtension hd).reading_set, (dataExtension hd).reading_prop] at h
  have m : Ideal.groundI.Mem (.tag .ground) := Ideal.mem_principal_tag.2 rfl
  rw [h] at m
  exact nomatch (Ideal.mem_principal_tag (k := .codes) (k' := .ground)).1 m

include hd in
/-- A type below a type equal to the sets is equal to the sets: no type former is the sets. -/
theorem below_set {n : Nat} {Γ : CCtx Tower.Head n} {X T : CTm Tower.Head n}
    (le : CBelow (dataChurch d) Γ X T) (formed : CCtxFormed (dataChurch d) Γ)
    (eX : CTypeEq (dataChurch d) Γ X (.const setN)) :
    CTypeEq (dataChurch d) Γ T (.const setN) := by
  refine CBelow.induction (motive := fun m Δ X T => CCtxFormed (dataChurch d) Δ →
      CTypeEq (dataChurch d) Δ X (.const setN) → CTypeEq (dataChurch d) Δ T (.const setN))
    ?equal ?univ ?pi ?sigma ?trans le formed eX
  case equal =>
    intro m Δ X T u e hu _ eX
    exact CTypeEq.trans (dataExtension hd).levels (CTypeEq.symm ⟨u, hu, e⟩) eX
  case univ =>
    intro m Δ u v _ formed eX
    exact (CTypeEq.neutral_ne_former (dataFormFacts hd) formed (set_neutral hd) (.head u)
      eX.symm).elim
  case pi =>
    intro m Δ A A' B B' _ _ _ _ _ _ _ _ _ _ _ formed eX
    exact (CTypeEq.neutral_ne_former (dataFormFacts hd) formed (set_neutral hd) (.pi A B)
      eX.symm).elim
  case sigma =>
    intro m Δ A A' B B' _ _ _ _ _ _ _ _ _ _ formed eX
    exact (CTypeEq.neutral_ne_former (dataFormFacts hd) formed (set_neutral hd) (.sigma A B)
      eX.symm).elim
  case trans =>
    intro m Δ X Y T _ _ ih₁ ih₂ formed eX
    exact ih₂ formed (ih₁ formed eX)

include hd in
/-- The sets are below no type former. -/
theorem set_below_former {B : CTm Tower.Head 0} (former : CFormer B)
    (le : CBelow (dataChurch d) .nil (.const setN) B) : False :=
  CTypeEq.neutral_ne_former (dataFormFacts hd) .nil (set_neutral hd) former
    (below_set hd le .nil
      (CIsType.refl (CBelow.isTypes (dataExtension hd).levels le .nil).1)).symm

/-- The types of the closed neutral terms: `U₀`, of the sets and the codes; the sets, of a
power set; and the type of the power set. -/
def ClosedNeutralType (X : CTm Tower.Head 0) : Prop :=
  X = cU0 ∨ X = .const setN ∨ X = .pi (.const setN) (.const setN)

/-- The rigid constants of the object package are the sets, the power set and the codes. -/
theorem objectRigid_cases {c : DeclName} {T : Tower.Tm 0}
    (declared : objectRules.constantType c = some T) (rigid : objectRoles c = .rigid) :
    c = setN ∨ c = powerN ∨ c = propN := by
  rcases objectRules_constantType_cases declared with ⟨type, rfl, -⟩ | ⟨type, rfl, -⟩ | hmem
  · rw [objectRoles_all (SetProfile.allInstance?_allName type)] at rigid
    cases rigid
  · rw [objectRoles_eq (SetProfile.eqInstance?_eqName type)] at rigid
    cases rigid
  · simp only [fixedDecls, declarations, List.cons_append, List.nil_append, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact .inr (.inr rfl)
    · rw [objectRoles_holds] at rigid; cases rigid
    · rw [objectRoles_imp] at rigid; cases rigid
    · rw [objectRoles_num] at rigid; cases rigid
    · exact .inl rfl
    · rw [objectRoles_zero] at rigid; cases rigid
    · rw [objectRoles_suc] at rigid; cases rigid
    · rw [Progress.objectRoles_add] at rigid; cases rigid
    · exact .inr (.inl rfl)
    · rw [Progress.objectRoles_pow] at rigid; cases rigid
    · rw [Progress.objectRoles_numRec] at rigid; cases rigid
    · rw [Progress.objectRoles_j] at rigid; cases rigid
    · rw [objectRoles_of_roles roles_eqAt nofun] at rigid; cases rigid
    · rw [objectRoles_of_roles roles_sucMove nofun] at rigid; cases rigid
    · rw [objectRoles_of_roles roles_keep nofun] at rigid; cases rigid
    · rw [objectRoles_of_roles roles_transport nofun] at rigid; cases rigid
    · rw [objectRoles_of_roles roles_compose nofun] at rigid; cases rigid
    · rw [Progress.objectRoles_iter] at rigid; cases rigid
    · rw [objectRoles_of_roles roles_returnIter nofun] at rigid; cases rigid
    · rw [objectRoles_of_roles roles_sucStep nofun] at rigid; cases rigid

include hd in
/-- **A rigid constant has a principal type of a closed neutral term**: `U₀` for the sets and
the codes, `set → set` for the power set. Every name of the datatype computes or constructs, so
the rigid constants are the object package's. -/
theorem rigid_principal {c : DeclName} {S : CTm Tower.Head 0} (rigid : dataRoles d c = .rigid)
    (typing : CTyped (dataChurch d) .nil (.const c) S) :
    ∃ X, PrincipalType (dataChurch d) .nil (.const c) X ∧ ClosedNeutralType X := by
  obtain ⟨D, _, declared, _, _, -⟩ := typing.generation
  have principal : PrincipalType (dataChurch d) .nil (.const c) D.liftClosed :=
    principal_const (dataExtension hd).levels .nil declared
  rw [CTm.liftClosed_zero] at principal
  refine ⟨D, principal, ?_⟩
  rcases dataChurch_declared_object_or hd declared with declared₀ | mem
  · have rigid₀ : objectRoles c = .rigid :=
      (dataRoles_object hd (by rw [← objectChurch.erase_constantType c, declared₀]; rfl)).symm.trans
        rigid
    have hT : objectRules.constantType c = some D.erase := by
      rw [← objectChurch.erase_constantType c, declared₀]
      rfl
    rcases objectRigid_cases hT rigid₀ with rfl | rfl | rfl
    · obtain rfl := Option.some.inj ((objectChurch_declared (c := setN) (T := Package.U0)
        (by decide) rfl).symm.trans declared₀)
      exact .inl rfl
    · obtain rfl := Option.some.inj ((objectChurch_declared (c := powerN) (T := powerType)
        (by decide) rfl).symm.trans declared₀)
      exact .inr (.inr rfl)
    · obtain rfl := Option.some.inj ((objectChurch_declared (c := propN) (T := Package.U0)
        (by decide) rfl).symm.trans declared₀)
      exact .inl rfl
  · exact absurd rigid (dataRoles_name_ne_rigid hd.distinct mem)

section Kinds

variable {f a X : CTm Tower.Head 0}

include hd in
/-- `U₀` is of the kind of universes. -/
theorem cU0_has : SortKey.Has (dataRules d) .univ (cU0 : CTm Tower.Head 0) :=
  ⟨.sort Tower.zero, (dataExtension hd).sort _, rfl⟩

include hd in
/-- **An application of a closed neutral term has a principal type of a closed neutral term**:
only the power set is a function, and it returns a set. -/
theorem app_principal (principal : PrincipalType (dataChurch d) .nil f X)
    (cls : ClosedNeutralType X) {T : CTm Tower.Head 0}
    (typing : CTyped (dataChurch d) .nil (.app f a) T) :
    ∃ X', PrincipalType (dataChurch d) .nil (.app f a) X' ∧ ClosedNeutralType X' := by
  obtain ⟨A, B, tf, -, -⟩ := typing.generation
  have le := principal tf
  rcases cls with rfl | rfl | rfl
  · exact (below_kind_false (dataProgressFacts hd) (dataExtension hd).levels
      (dataRules_algebra d) .nil le (k := .univ) (k' := .pi) (cU0_has hd) ⟨A, B, rfl⟩ nofun nofun
      nofun).elim
  · exact (set_below_former hd (.pi A B) le).elim
  · exact ⟨_, (principal_app (dataFormerFacts hd) (dataExtension hd).levels .nil principal).1,
      .inr (.inl rfl)⟩

include hd in
/-- A spine of a closed neutral term has a principal type of a closed neutral term. -/
theorem spine_principal : ∀ (args : List (CTm Tower.Head 0)) {f X T : CTm Tower.Head 0},
    PrincipalType (dataChurch d) .nil f X → ClosedNeutralType X →
      CTyped (dataChurch d) .nil (CTm.appSpine f args) T →
        ∃ X', PrincipalType (dataChurch d) .nil (CTm.appSpine f args) X' ∧
          ClosedNeutralType X'
  | [], _, X, _, principal, cls, _ => ⟨X, principal, cls⟩
  | a :: as, _, _, _, principal, cls, typing => by
      obtain ⟨S, tS⟩ := typed_appSpine_fun as typing
      obtain ⟨X', principal', cls'⟩ := app_principal hd principal cls tS
      exact spine_principal as principal' cls' typing

include hd in
/-- A closed neutral term's type is no dependent pair type. -/
theorem closed_not_sigma (principal : PrincipalType (dataChurch d) .nil f X)
    (cls : ClosedNeutralType X) {A : CTm Tower.Head 0} {B : CTm Tower.Head 1}
    (typing : CTyped (dataChurch d) .nil f (.sigma A B)) : False := by
  have le := principal typing
  rcases cls with rfl | rfl | rfl
  · exact below_kind_false (dataProgressFacts hd) (dataExtension hd).levels
      (dataRules_algebra d) .nil le (k := .univ) (k' := .sigma) (cU0_has hd) ⟨A, B, rfl⟩ nofun
      nofun nofun
  · exact set_below_former hd (.sigma A B) le
  · exact below_kind_false (dataProgressFacts hd) (dataExtension hd).levels
      (dataRules_algebra d) .nil le (k := .pi) (k' := .sigma) ⟨_, _, rfl⟩ ⟨A, B, rfl⟩ nofun
      nofun nofun

include hd in
/-- A closed neutral term's type is no relevant type constant: not the numbers, the codes or
the datatype. -/
theorem closed_not_relevant (principal : PrincipalType (dataChurch d) .nil f X)
    (cls : ClosedNeutralType X) {C : DeclName}
    (rel : Annotated.Progress.RelevantConst (dataChurch d) (dataRoles d) C)
    (typing : CTyped (dataChurch d) .nil f (.const C)) : False := by
  have le := principal typing
  rcases cls with rfl | rfl | rfl
  · exact below_kind_false (dataProgressFacts hd) (dataExtension hd).levels
      (dataRules_algebra d) .nil le (k := .univ) (k' := .const C) (cU0_has hd) rfl nofun nofun
      fun _ h => by cases h; exact rel
  · have e := below_set hd le .nil
      (CIsType.refl (CBelow.isTypes (dataExtension hd).levels le .nil).1)
    rcases data_relevant hd rel with rfl | rfl | rfl
    · exact CTypeEq.neutral_ne_inductive (dataFormFacts hd) .nil (set_neutral hd)
        ((dataRoles_object hd (by decide)).trans objectRoles_num) e.symm
    · exact set_ne_prop hd e.symm
    · exact CTypeEq.neutral_ne_inductive (dataFormFacts hd) .nil (set_neutral hd) dataRoles_type
        e.symm
  · exact below_kind_false (dataProgressFacts hd) (dataExtension hd).levels
      (dataRules_algebra d) .nil le (k := .pi) (k' := .const C) ⟨_, _, rfl⟩ rfl nofun nofun
      fun _ h => by cases h; exact rel

include hd in
/-- A closed neutral term's type is no identity type. -/
theorem closed_not_ident (principal : PrincipalType (dataChurch d) .nil f X)
    (cls : ClosedNeutralType X) {A x y : CTm Tower.Head 0}
    (typing : CTyped (dataChurch d) .nil f (.id A x y)) : False := by
  have le := principal typing
  rcases cls with rfl | rfl | rfl
  · exact below_kind_false (dataProgressFacts hd) (dataExtension hd).levels
      (dataRules_algebra d) .nil le (k := .univ) (k' := .ident) (cU0_has hd) ⟨A, x, y, rfl⟩ nofun
      nofun nofun
  · exact set_below_former hd (.id A x y) le
  · exact below_kind_false (dataProgressFacts hd) (dataExtension hd).levels
      (dataRules_algebra d) .nil le (k := .pi) (k' := .ident) ⟨_, _, rfl⟩ ⟨A, x, y, rfl⟩ nofun
      nofun nofun

end Kinds

include hd in
/-- **Every closed neutral term has a principal type of a closed neutral term**, by induction
on its size: a rigid spine by its head; an application by its function, which only the power
set can be; a projection or a computing constant stuck on a closed neutral term is not typed,
since no closed neutral term is a pair, a number, a code, an element of the datatype or an
identification. -/
theorem closedNeutral_principal : ∀ (N : Nat) (t : CTm Tower.Head 0), ctmSize t < N →
    ∀ {T : CTm Tower.Head 0}, CTyped (dataChurch d) .nil t T → Neutral (dataRoles d) t.erase →
      ∃ X, PrincipalType (dataChurch d) .nil t X ∧ ClosedNeutralType X
  | 0, _, small, _, _, _ => absurd small (Nat.not_lt_zero _)
  | N + 1, t, small, T, typing, neutral => by
      generalize e : t.erase = u at neutral
      cases neutral with
      | var i => exact i.elim0
      | @app f a hf =>
          obtain ⟨f', a', rfl, ef, -⟩ := CTm.erase_eq_app e
          have sizes : ctmSize f' + ctmSize a' + 1 < N + 1 := small
          obtain ⟨A, B, tf, -, -⟩ := typing.generation
          obtain ⟨X, principal, cls⟩ :=
            closedNeutral_principal N f' (by omega) tf (ef ▸ hf)
          exact app_principal hd principal cls typing
      | @fst p hp =>
          obtain ⟨p', rfl, ep⟩ := CTm.erase_eq_fst e
          have sizes : ctmSize p' + 1 < N + 1 := small
          obtain ⟨A, B, tp, -⟩ := typing.generation
          obtain ⟨X, principal, cls⟩ := closedNeutral_principal N p' (by omega) tp (ep ▸ hp)
          exact (closed_not_sigma hd principal cls tp).elim
      | @snd p hp =>
          obtain ⟨p', rfl, ep⟩ := CTm.erase_eq_snd e
          have sizes : ctmSize p' + 1 < N + 1 := small
          obtain ⟨A, B, tp, -⟩ := typing.generation
          obtain ⟨X, principal, cls⟩ := closedNeutral_principal N p' (by omega) tp (ep ▸ hp)
          exact (closed_not_sigma hd principal cls tp).elim
      | rigid args role =>
          obtain ⟨args', rfl, -⟩ := CTm.erase_eq_constSpine args e
          obtain ⟨S, tc⟩ := typed_appSpine_fun args' typing
          obtain ⟨X, principal, cls⟩ := rigid_principal hd role tc
          exact spine_principal hd args' principal cls typing
      | @stuck c arity inspect args kind x role length focus hx _ =>
          exfalso
          obtain ⟨args', rfl, eargs⟩ := CTm.erase_eq_constSpine args e
          obtain ⟨D, declared, -, shape⟩ :=
            (dataProgressFacts hd).declaredComputing role
          cases shape with
          | leaf h =>
              subst h
              exact InspectTree.Focus.not_leaf focus
          | const pos C h _ hdom =>
              subst h
              obtain ⟨before, after, hb, rfl, -, -⟩ := InspectTree.Focus.single focus
              obtain ⟨before', rest, rfl, eb, erest⟩ := List.map_eq_append_iff.1 eargs
              obtain ⟨x', after', rfl, ex, -⟩ := List.map_eq_cons_iff.1 erest
              have hb' : before'.length = pos := by rw [← hb, ← eb, List.length_map]
              have tx := argument_const (dataProgressFacts hd)
                (dataExtension hd).levels .nil declared
                (before := before') (after := after') (by rw [hb']; exact hdom) typing
              have small' : ctmSize x' < N := by
                have := ctmSize_lt_appSpine (before' ++ x' :: after') (.const c) x'
                  (List.mem_append_right _ List.mem_cons_self)
                omega
              obtain ⟨X, principal, cls⟩ :=
                closedNeutral_principal N x' small' tx (ex ▸ hx)
              exact closed_not_relevant hd principal cls
                (relevant_of_domain role declared hdom) tx
          | ident pos h _ hdom =>
              subst h
              obtain ⟨before, after, hb, rfl, -, -⟩ := InspectTree.Focus.single focus
              obtain ⟨before', rest, rfl, eb, erest⟩ := List.map_eq_append_iff.1 eargs
              obtain ⟨x', after', rfl, ex, -⟩ := List.map_eq_cons_iff.1 erest
              have hb' : before'.length = pos := by rw [← hb, ← eb, List.length_map]
              obtain ⟨A, hA, tx⟩ := argument_typed (dataFormerFacts hd)
                (dataExtension hd).levels .nil
                isIdTest_stable (principal_const (dataExtension hd).levels .nil declared)
                (before := before') (after := after')
                (afterBinders_liftClosed (domainTest_stable isIdTest_stable)
                  (by rw [hb']; exact hdom)) typing
              obtain ⟨B, y, z, rfl⟩ := isIdTest_inv hA
              have small' : ctmSize x' < N := by
                have := ctmSize_lt_appSpine (before' ++ x' :: after') (.const c) x'
                  (List.mem_append_right _ List.mem_cons_self)
                omega
              obtain ⟨X, principal, cls⟩ :=
                closedNeutral_principal N x' small' tx (ex ▸ hx)
              exact closed_not_ident hd principal cls tx

include hd in
/-- **No closed term typed at the datatype is neutral.** -/
theorem closedData_not_neutral {t : CTm Tower.Head 0}
    (typing : CTyped (dataChurch d) .nil t (.const d.type))
    (neutral : Neutral (dataRoles d) t.erase) : False := by
  obtain ⟨X, principal, cls⟩ :=
    closedNeutral_principal hd (ctmSize t + 1) t (Nat.lt_succ_self _) typing neutral
  exact closed_not_relevant hd principal cls
    (Annotated.Progress.relevant_of_inductive dataRoles_type) typing

end ClosedNeutral

/-! ## Canonicity -/

section Canonicity

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch) (avoid : AvoidsModelNames d)

include hd in
/-- A typed term of a formed context reaches, typed, a weak-head normal form, along its
terminating annotated weak-head steps. -/
theorem data_whnf {n : Nat} {Γ : CCtx Tower.Head n} (formed : CCtxFormed (dataChurch d) Γ)
    {T : CTm Tower.Head n} : ∀ {t : CTm Tower.Head n},
    Acc (fun u t => CWhStepR (dataChurch d) (dataRoles d) t u) t →
    CTyped (dataChurch d) Γ t T →
      ∃ w, Relation.ReflTransGen (CWhStepR (dataChurch d) (dataRoles d)) t w ∧
        CEqual (dataChurch d) Γ t w T ∧ CTyped (dataChurch d) Γ w T ∧
          Annotated.Progress.WhnfShape (dataRoles d) w := by
  intro t acc
  induction acc with
  | intro t _ ih =>
      intro typed
      rcases dataChurch_progress hd formed typed with ⟨t₁, step⟩ | shape
      · have e := CWhStepR.equal (dataFormerFacts hd) (dataExtension hd).levels
          (dataRootAdmitted hd) formed step typed
        have typed₁ := (CEqual.typed (dataExtension hd).levels e formed).2
        obtain ⟨w, red, e', tw, shape⟩ := ih t₁ step typed₁
        exact ⟨w, .head step red, .trans e e', tw, shape⟩
      · exact ⟨t, .refl, .refl typed, typed, shape⟩

include hd avoid in
/-- **Canonicity at a declared datatype**: every closed term typed at the datatype weak-head
reduces to one of its listed constructors applied to as many arguments as it has fields, each
argument typed at its field's type. The term's erasure is strongly normalizing, so its
weak-head steps end, at a weak-head normal form that is not neutral, since it is closed. -/
theorem data_canonical {t : CTm Tower.Head 0}
    (typed : CTyped (dataChurch d) .nil t (.const d.type)) :
    ∃ (i : Nat) (k : DeclName) (fs : List CtorField) (args : List (CTm Tower.Head 0)),
      d.ctors[i]? = some (k, fs) ∧ args.length = fs.length ∧
      List.Forall₂ (fun a (f : CtorField) =>
        CTyped (dataChurch d) .nil a (liftTm (f.type d.type)).liftClosed) args fs ∧
      CRedTm (dataHead hd) .nil t (CTm.appSpine (.const k) args) (.const d.type) := by
  have sn := (dataRules_sn hd avoid .nil (CDerivable.erase typed)).1
  obtain ⟨w, red, equal, tw, shape⟩ :=
    data_whnf hd .nil (CWhStepR.acc_of_sn sn) typed
  rcases Annotated.Progress.canonical_at (dataProgressFacts hd)
      (dataExtension hd).levels (dataRules_algebra d) .nil shape tw (k := .const d.type) rfl
      (fun _ h => by cases h; exact Annotated.Progress.relevant_of_inductive dataRoles_type) with
    neutral | fits
  · exact (closedData_not_neutral hd tw neutral).elim
  · obtain ⟨i, k, fs, args, hi, length, rfl⟩ := data_fits hd fits
    have principal : Annotated.Progress.PrincipalType (dataChurch d) .nil (.const k)
        (cArrows (fs.map fun f => liftTm (f.type d.type)) (.const d.type)) := by
      have h : Annotated.Progress.PrincipalType (dataChurch d) .nil (.const k)
          (liftTm (ctorType d.type fs)).liftClosed :=
        Annotated.Progress.principal_const (dataExtension hd).levels .nil
          (data_ctor_declared hd hi)
      rwa [liftTm_ctorType, liftClosed_cArrows] at h
    have fields := forall₂_typed_of_cArrows (dataFormerFacts hd) (dataExtension hd).levels .nil
      (.const d.type)
      (fs.map fun f => liftTm (f.type d.type)) args (by rw [List.length_map, length]) principal tw
    exact ⟨i, k, fs, args, hi, length, (List.forall₂_map_right_iff
      (R := fun a (F : CTm Tower.Head 0) => CTyped (dataChurch d) .nil a F.liftClosed)).1 fields,
      red, equal⟩

end Canonicity

/-! ## Lifting and the facts about the raw weak-head forms -/

section Lifting

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch) (avoid : AvoidsModelNames d)

/-- **Root lifting for the package with a declared datatype**: every root step of the erasure
of an annotated term is the erasure of an annotated root step, the object package's by its
schemas and the recursor's by its rules. -/
theorem dataChurch_lift {n : Nat} {l : CTm Tower.Head n} {r₀ : Tower.Tm n}
    (step : (dataRules d).computation.step l.erase r₀) :
    ∃ r, (dataChurch d).computation.step l r ∧ r.erase = r₀ := by
  rcases step with step | step
  · obtain ⟨r, s, e⟩ := objectChurch_lift step
    exact ⟨r, .inl s, e⟩
  · obtain ⟨r, s, e⟩ := ChurchRules.ofSchemas_lift (iotaSchema d.recursor d.ctors)
      (iota_presents d.recursor d.ctors) (iotaSchema_firstOrder _ _) step
    exact ⟨r, .inr s, e⟩

include hd in
/-- **No declared type of the package with a declared datatype has an abstraction.** -/
theorem dataChurch_declared_lamFree {c : DeclName} {D : CTm Tower.Head 0}
    (declared : (dataChurch d).constantType c = some D) : lamFree D.erase = true := by
  rcases dataChurch_declared_cases hd declared with declared₀ | ⟨-, rfl⟩ | ⟨i, fs, hi, rfl⟩ |
    ⟨-, rfl⟩
  · exact objectChurch_declared_lamFree declared₀
  · rfl
  · rw [erase_liftTm]
    exact lamFree_ctorType d.type fun F member => hd.lamFree _ (List.mem_of_getElem? hi) F member
  · rw [erase_liftTm]
    exact lamFree_recType _ _ hd.lamFree

include hd avoid in
/-- **The facts lifting needs, for the package with a declared datatype**: coherence, root
lifting, root admission and rigid declared types. -/
theorem dataLiftingFacts : LiftingFacts (dataChurch d) where
  coherent := fun formed typing typing' same =>
    dataCoherence hd avoid formed typing typing' same
  lift := fun step => dataChurch_lift step
  admitted := dataRootAdmitted hd
  declared := CDeclsRigid.formed (rigid_of_lamFree (dataChurch_declared_lamFree hd))

include hd avoid in
/-- **The types of the package with a declared datatype lift** to its annotation. -/
theorem dataRules_liftType {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}
    (formed : CtxFormed (dataRules d) Γ) (type : IsType (dataRules d) Γ A) :
    ∃ (Γ' : CCtx Tower.Head n) (A' : CTm Tower.Head n),
      CCtxFormed (dataChurch d) Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧
        CIsType (dataChurch d) Γ' A' :=
  lift_isType (dataExtension hd).levels (dataLiftingFacts hd avoid) formed type

include hd avoid in
/-- **The equations of types of the package with a declared datatype lift** to its
annotation. -/
theorem dataRules_liftTypeEq {n : Nat} {Γ : Tower.Ctx n} {A B : Tower.Tm n}
    (formed : CtxFormed (dataRules d) Γ) (equal : TypeEq (dataRules d) Γ A B) :
    ∃ (Γ' : CCtx Tower.Head n) (A' B' : CTm Tower.Head n),
      CCtxFormed (dataChurch d) Γ' ∧ Γ'.erase = Γ ∧ A'.erase = A ∧ B'.erase = B ∧
        CTypeEq (dataChurch d) Γ' A' B' :=
  lift_typeEq (dataExtension hd).levels (dataLiftingFacts hd avoid) formed equal

include hd avoid in
/-- **The facts about the weak-head forms of the types of the package with a declared
datatype**: a type of a formed context reduces, typed, to a type in weak-head form, and equal
types in weak-head form match. From the annotated facts, through lifting, strong normalization
and the progress of annotated types. -/
theorem dataRules_formFacts : FormFacts (dataRules d) (dataRoles d) :=
  FormFacts.ofAnnotated (dataExtension hd).levels (dataFormFacts hd) (dataRootAdmitted hd)
    (fun formed typing => (dataRules_sn hd avoid formed.erase (CDerivable.erase typing)).1)
    (dataRules_liftType hd avoid) (dataRules_liftTypeEq hd avoid)
    (fun formed hu typing => Annotated.Progress.typeProgress (dataProgressFacts hd)
      (dataExtension hd).levels (dataRules_algebra d) formed hu typing)

end Lifting

/-! ## The lists of numbers -/

section Lists

/-- The lists avoid the names the value side reserves. -/
theorem listDecl_avoids : AvoidsModelNames listDecl := by
  intro c mem
  simp only [dataNames, List.mem_cons, List.mem_map] at mem
  rcases mem with rfl | rfl | ⟨e, he, rfl⟩
  · decide
  · decide
  · simp only [listDecl, listCtors, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide

/-- **Positive example**: the one-element list of the numeral one, typed at the lists, is
strongly normalizing. -/
theorem consOneNil_sn :
    SN (dataRules listDecl) (ccons (csuc czero) cnil : CTm Tower.Head 0).erase :=
  (dataRules_sn listDecl_admissible listDecl_avoids .nil
    (CDerivable.erase (cons_one_nil_typed (Γ := .nil)))).1

/-- **The canonical forms of the lists**: a constructor of the lists applied to as many terms as
it has fields, typed at them, is `nil`, or `cons a l` with `a` a number and `l` a list. -/
theorem listDecl_ctor_forms {i : Nat} {k : DeclName} {fs : List CtorField}
    {args : List (CTm Tower.Head 0)} (hi : listDecl.ctors[i]? = some (k, fs))
    (fields : List.Forall₂ (fun a (f : CtorField) =>
      CTyped (dataChurch listDecl) .nil a (liftTm (f.type listDecl.type)).liftClosed) args fs) :
    CTm.appSpine (.const k) args = cnil ∨
      ∃ a l, CTyped (dataChurch listDecl) .nil a cnum ∧
        CTyped (dataChurch listDecl) .nil l clist ∧ CTm.appSpine (.const k) args = ccons a l := by
  match i, hi with
  | 0, hi =>
      cases hi
      cases fields
      exact .inl rfl
  | 1, hi =>
      cases hi
      obtain _ | ⟨ta, _ | ⟨tl, _ | _⟩⟩ := fields
      exact .inr ⟨_, _, ta, tl, rfl⟩
  | _ + 2, hi => exact nomatch hi

/-- `append (cons 1 nil) nil`: the recursor at a closed list, applied to the empty list. -/
abbrev appendOneNil : CTm Tower.Head 0 := .app (appendRec (ccons (csuc czero) cnil)) cnil

theorem appendOneNil_typed : CTyped (dataChurch listDecl) .nil appendOneNil clist :=
  CDerivable.appElim (appendRec_typed cons_one_nil_typed) nil_typed

/-- The context of one list. -/
abbrev cOneList : CCtx Tower.Head 1 := .snoc .nil clist

/-- `append x nil` over a list `x`: the recursor at the variable, applied to the empty list. -/
abbrev appendVarNil : CTm Tower.Head 1 := .app (appendRec (.var 0)) cnil

theorem appendVarNil_typed : CTyped (dataChurch listDecl) cOneList appendVarNil clist :=
  CDerivable.appElim (appendRec_typed (.var 0)) nil_typed

/-- `append x nil` takes no weak-head step: the recursor is stuck at the variable. -/
theorem appendVarNil_normal : (dataHead listDecl_admissible).Normal appendVarNil := by
  apply (dataExtension listDecl_admissible).neutralNormal
  refine .app ?_
  exact Neutral.stuck_single (roles := dataRoles listDecl)
    (before := [appendMotive.erase, appendBase.erase, appendStep.erase]) (after := [])
    (dataRoles_rec listDecl_admissible.distinct) rfl (.var 0)

/-- **Negative example: closedness is needed for canonicity.** Over a list variable `x`,
`append x nil` is typed at the lists and reduces neither to `nil` nor to `cons a l`: the
recursor is stuck at the variable. -/
theorem appendVarNil_not_canonical :
    ¬ CRedTm (dataHead listDecl_admissible) cOneList appendVarNil cnil clist ∧
      ∀ a l, ¬ CRedTm (dataHead listDecl_admissible) cOneList appendVarNil (ccons a l) clist := by
  refine ⟨fun h => ?_, fun a l h => ?_⟩
  · have e := (dataHead listDecl_admissible).red_normal appendVarNil_normal h.1
    cases e
  · have e := (dataHead listDecl_admissible).red_normal appendVarNil_normal h.1
    injection e with _ e₁ _
    injection e₁ with _ e₂ _
    cases e₂

end Lists

/-! ## Control: a recursor that recurses on the same list

A package with the lists' declarations whose recursor, at `cons`, recurses on the same list
types a term with no normal form. The declared types it needs are typed in packages that declare
some of the lists' names and compute nothing. -/

/-- The declarations of the package with the lists at the listed names. -/
def listTypeDecls (names : List DeclName) (c : DeclName) : Option (Tower.Tm 0) :=
  if c ∈ names then (dataRules listDecl).constantType c else none

/-- The numbers, the type of lists and its constructors, declared without computation. -/
abbrev listCtorTypes : Rules Tower.Head :=
  controlRules (listTypeDecls [numN, listN, nilN, consN]) []

theorem listTypeDecls_num {names : List DeclName} (h : numN ∈ names) :
    listTypeDecls names numN = some U0 := by
  rw [listTypeDecls, if_pos h]
  rfl

theorem listTypeDecls_list {names : List DeclName} (h : listN ∈ names) :
    listTypeDecls names listN = some U0 := by
  rw [listTypeDecls, if_pos h]
  rfl

theorem listTypeDecls_nil {names : List DeclName} (h : nilN ∈ names) :
    listTypeDecls names nilN = some (.const listN) := by
  rw [listTypeDecls, if_pos h]
  rfl

theorem listTypeDecls_cons {names : List DeclName} (h : consN ∈ names) :
    listTypeDecls names consN = some (.pi numT (.pi (.const listN) (.const listN))) := by
  rw [listTypeDecls, if_pos h]
  rfl

/-- A declaration of these packages is one of the package with the lists. -/
theorem listTypeDecls_sub {names : List DeclName} {c : DeclName} {T : Tower.Tm 0}
    (h : listTypeDecls names c = some T) :
    c ∈ names ∧ (dataRules listDecl).constantType c = some T := by
  unfold listTypeDecls at h
  split_ifs at h with mem
  exact ⟨mem, h⟩

section Typings

variable {names : List DeclName} {n : Nat} {Γ : Tower.Ctx n}

theorem numT_typedC (h : numN ∈ names) :
    Typed (controlRules (listTypeDecls names) []) Γ numT U0 :=
  .const (listTypeDecls_num h) (sortC Tower.zero) (.sort _)

theorem listT_typedC (h : listN ∈ names) :
    Typed (controlRules (listTypeDecls names) []) Γ (.const listN) U0 :=
  .const (listTypeDecls_list h) (sortC Tower.zero) (.sort _)

end Typings

/-- The declared type of the recursor of the lists, written out. -/
theorem listRecType_eq : recType listN listMotives listCtors =
    .pi (.pi (.const listN) (.head listMotives))
      (.pi (.app (.var 0) (.const nilN))
        (.pi (.pi numT (.pi (.const listN) (.pi (.app (.var 3) (.var 0))
            (.app (.var 4) (.app (.app (.const consN) (.var 2)) (.var 1))))))
          (.pi (.const listN) (.app (.var 3) (.var 0))))) := by
  decide

/-- **The declared type of the recursor of the lists is a type of `U2`**, in the package of the
numbers, the lists and their constructors. -/
theorem listRecType_typed :
    Typed listCtorTypes .nil (recType listN listMotives listCtors)
      (sortTm (.succ (.succ Tower.zero))) := by
  rw [listRecType_eq]
  have numMem : numN ∈ [numN, listN, nilN, consN] := by decide
  have listMem : listN ∈ [numN, listN, nilN, consN] := by decide
  have tNil : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed listCtorTypes Γ (.const nilN) (.const listN) :=
    fun {_ _} => .const (show listCtorTypes.constantType nilN = some (.const listN) from
      listTypeDecls_nil (names := [numN, listN, nilN, consN]) (by decide))
      (listT_typedC listMem) (.sort _)
  have tCons : ∀ {n : Nat} {Γ : Tower.Ctx n},
      Typed listCtorTypes Γ (.const consN) (.pi numT (.pi (.const listN) (.const listN))) :=
    fun {_ _} => .const (show listCtorTypes.constantType consN =
        some (.pi numT (.pi (.const listN) (.const listN))) from
      listTypeDecls_cons (names := [numN, listN, nilN, consN]) (by decide))
      (piC (numT_typedC numMem) (piC (listT_typedC listMem) (listT_typedC listMem))) (.sort _)
  have up₁ : ∀ {n : Nat} {Γ : Tower.Ctx n} {T : Tower.Tm n},
      Typed listCtorTypes Γ T U0 → Typed listCtorTypes Γ T (sortTm (.succ Tower.zero)) :=
    fun typed => raiseC typed (le_succ_eval · Tower.zero)
  have up₂ : ∀ {n : Nat} {Γ : Tower.Ctx n} {T : Tower.Tm n},
      Typed listCtorTypes Γ T (sortTm (.succ Tower.zero)) →
        Typed listCtorTypes Γ T (sortTm (.succ (.succ Tower.zero))) :=
    fun typed => raiseC typed (le_succ_eval · (.succ Tower.zero))
  -- the motive's type
  have tE0 : Typed listCtorTypes .nil (.pi (.const listN) (.head listMotives))
      (sortTm (.succ (.succ Tower.zero))) :=
    piC (up₂ (up₁ (listT_typedC listMem))) (sortC (.succ Tower.zero))
  -- the case of `nil`
  let Γ₁ : Tower.Ctx 1 := .snoc .nil (.pi (.const listN) (.head listMotives))
  have tE1 : Typed listCtorTypes Γ₁ (.app (.var 0) (.const nilN)) (sortTm (.succ Tower.zero)) :=
    .appElim (B := sortTm (.succ Tower.zero)) (.var 0) tNil
  -- the case of `cons`
  let Γ₂ : Tower.Ctx 2 := .snoc Γ₁ (.app (.var 0) (.const nilN))
  let Γ₂a : Tower.Ctx 3 := .snoc Γ₂ numT
  let Γ₂l : Tower.Ctx 4 := .snoc Γ₂a (.const listN)
  have tIH : Typed listCtorTypes Γ₂l (.app (.var 3) (.var 0)) (sortTm (.succ Tower.zero)) :=
    .appElim (B := sortTm (.succ Tower.zero)) (.var 3) (.var 0)
  let Γ₂h : Tower.Ctx 5 := .snoc Γ₂l (.app (.var 3) (.var 0))
  have tConsAL : Typed listCtorTypes Γ₂h (.app (.app (.const consN) (.var 2)) (.var 1))
      (.const listN) :=
    .appElim (B := .const listN) (.appElim (B := .pi (.const listN) (.const listN)) tCons (.var 2))
      (.var 1)
  have tGoal : Typed listCtorTypes Γ₂h
      (.app (.var 4) (.app (.app (.const consN) (.var 2)) (.var 1)))
      (sortTm (.succ Tower.zero)) :=
    .appElim (B := sortTm (.succ Tower.zero)) (.var 4) tConsAL
  have tE2 : Typed listCtorTypes Γ₂ (.pi numT (.pi (.const listN) (.pi (.app (.var 3) (.var 0))
      (.app (.var 4) (.app (.app (.const consN) (.var 2)) (.var 1))))))
      (sortTm (.succ Tower.zero)) :=
    piC (up₁ (numT_typedC numMem)) (piC (up₁ (listT_typedC listMem)) (piC tIH tGoal))
  -- the scrutinee and the result
  let Γ₃ : Tower.Ctx 3 := .snoc Γ₂ (.pi numT (.pi (.const listN) (.pi (.app (.var 3) (.var 0))
      (.app (.var 4) (.app (.app (.const consN) (.var 2)) (.var 1))))))
  have tBody : Typed listCtorTypes (.snoc Γ₃ (.const listN)) (.app (.var 3) (.var 0))
      (sortTm (.succ Tower.zero)) :=
    .appElim (B := sortTm (.succ Tower.zero)) (.var 3) (.var 0)
  exact piC tE0 (piC (up₂ tE1) (piC (up₂ tE2) (piC (up₂ (up₁ (listT_typedC listMem)))
    (up₂ tBody))))


/-- **The looping rule at `cons`**: the recursor recurses on the same list,
`list-rec P z s (cons a l) ⟶ s a l (list-rec P z s (cons a l))`. -/
def LoopStep {n : Nat} (l r : Tower.Tm n) : Prop :=
  ∃ P z s a k, l = appSpine (.const listRecN) [P, z, s, appSpine (.const consN) [a, k]] ∧
    r = .app (.app (.app s a) k) l

/-- The looping rule, as a root computation. -/
def loopComputation : RootComputation Tower.Head where
  step := LoopStep
  rename := by
    rintro n m ρ l r ⟨P, z, s, a, k, rfl, rfl⟩
    exact ⟨_, _, _, _, _, rfl, rfl⟩
  substitute := by
    rintro n m σ l r ⟨P, z, s, a, k, rfl, rfl⟩
    exact ⟨_, _, _, _, _, rfl, rfl⟩

/-- **The package with the lists whose recursor loops at `cons`**: the declarations of the
package with the lists, the object package's computations and the looping rule. -/
def loopRules : Rules Tower.Head :=
  { dataRules listDecl with
    computation := RootComputation.union objectRules.computation loopComputation }

/-- A package of the lists' declared types without computation is contained in the looping
package. -/
theorem listTypeDecls_sub_loop (names : List DeclName) :
    RulesSub (controlRules (listTypeDecls names) []) loopRules where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => (listTypeDecls_sub declared).2
  computation := fun step => by
    change (RootComputation.unionAll (computations.filter fun entry => allowedIn [] entry.1)).step
      _ _ at step
    obtain ⟨entry, mem, -⟩ := RootComputation.unionAll_step step
    simp [allowedIn] at mem

/-- The context of the recursor's motive, value at `nil` and step. -/
abbrev loopContext : Tower.Ctx 3 :=
  .snoc (.snoc (.snoc .nil (.pi (.const listN) (.head listMotives))) (.app (.var 0) (.const nilN)))
    (.pi numT (.pi (.const listN) (.pi (.app (.var 3) (.var 0))
      (.app (.var 4) (.app (.app (.const consN) (.var 2)) (.var 1))))))

/-- The one-element list of zero. -/
abbrev zeroList {n : Nat} : Tower.Tm n := appSpine (.const consN) [.const zeroN, .const nilN]

/-- The recursor at the one-element list, over the motive, value and step of the context. -/
abbrev loopTerm : Tower.Tm 3 := appSpine (.const listRecN) [.var 2, .var 1, .var 0, zeroList]

/-- The iterated reducts of `loopTerm`: the step applied to the head, the tail and the
previous one. -/
def loopTower : Nat → Tower.Tm 3
  | 0 => loopTerm
  | k + 1 => .app (.app (.app (.var 0) (.const zeroN)) (.const nilN)) (loopTower k)

/-- Each term of the tower steps to the next under the looping package. -/
theorem loopTower_step :
    ∀ k, StrongNormalization.Reduces loopRules (loopTower k) (loopTower (k + 1))
  | 0 => .root (.inr ⟨_, _, _, _, _, rfl, rfl⟩)
  | k + 1 => .congAppArg (loopTower_step k)

/-- **The tower has no end**: no term of it is strongly normalizing under the looping
package. -/
theorem loopTower_not_sn (k : Nat) : ¬ SN loopRules (loopTower k) := by
  have key : ∀ t : Tower.Tm 3, SN loopRules t → ∀ k, t = loopTower k → False := by
    intro t h
    induction h with
    | intro t _ ih =>
        intro k e
        subst e
        exact ih _ (loopTower_step k) (k + 1) rfl
  exact fun h => key _ h k rfl

section LoopTyping

theorem loop_listT {n : Nat} {Γ : Tower.Ctx n} : Typed loopRules Γ (.const listN) U0 :=
  Derivable.mono (listTypeDecls_sub_loop [numN, listN]) (listT_typedC (by decide))

/-- The context of the looping control is formed. -/
theorem loopContext_formed : CtxFormed loopRules loopContext := by
  have sub := listTypeDecls_sub_loop [numN, listN, nilN, consN]
  have numMem : numN ∈ [numN, listN, nilN, consN] := by decide
  have listMem : listN ∈ [numN, listN, nilN, consN] := by decide
  have up₁ : ∀ {n : Nat} {Γ : Tower.Ctx n} {T : Tower.Tm n},
      Typed listCtorTypes Γ T U0 → Typed listCtorTypes Γ T (sortTm (.succ Tower.zero)) :=
    fun typed => raiseC typed (le_succ_eval · Tower.zero)
  have tNil : ∀ {n : Nat} {Γ : Tower.Ctx n}, Typed listCtorTypes Γ (.const nilN) (.const listN) :=
    fun {_ _} => .const (show listCtorTypes.constantType nilN = some (.const listN) from
      listTypeDecls_nil (names := [numN, listN, nilN, consN]) (by decide))
      (listT_typedC listMem) (.sort _)
  have tCons : ∀ {n : Nat} {Γ : Tower.Ctx n},
      Typed listCtorTypes Γ (.const consN) (.pi numT (.pi (.const listN) (.const listN))) :=
    fun {_ _} => .const (show listCtorTypes.constantType consN =
        some (.pi numT (.pi (.const listN) (.const listN))) from
      listTypeDecls_cons (names := [numN, listN, nilN, consN]) (by decide))
      (piC (numT_typedC numMem) (piC (listT_typedC listMem) (listT_typedC listMem))) (.sort _)
  have tE0 : Typed listCtorTypes .nil (.pi (.const listN) (.head listMotives))
      (sortTm (.succ (.succ Tower.zero))) :=
    piC (raiseC (up₁ (listT_typedC listMem)) (le_succ_eval · (.succ Tower.zero)))
      (sortC (.succ Tower.zero))
  let Γ₁ : Tower.Ctx 1 := .snoc .nil (.pi (.const listN) (.head listMotives))
  have tE1 : Typed listCtorTypes Γ₁ (.app (.var 0) (.const nilN)) (sortTm (.succ Tower.zero)) :=
    .appElim (B := sortTm (.succ Tower.zero)) (.var 0) tNil
  let Γ₂ : Tower.Ctx 2 := .snoc Γ₁ (.app (.var 0) (.const nilN))
  have tIH : Typed listCtorTypes (.snoc (.snoc Γ₂ numT) (.const listN)) (.app (.var 3) (.var 0))
      (sortTm (.succ Tower.zero)) :=
    .appElim (B := sortTm (.succ Tower.zero)) (.var 3) (.var 0)
  have tConsAL : Typed listCtorTypes
      (.snoc (.snoc (.snoc Γ₂ numT) (.const listN)) (.app (.var 3) (.var 0)))
      (.app (.app (.const consN) (.var 2)) (.var 1)) (.const listN) :=
    .appElim (B := .const listN) (.appElim (B := .pi (.const listN) (.const listN)) tCons (.var 2))
      (.var 1)
  have tE2 : Typed listCtorTypes Γ₂ (.pi numT (.pi (.const listN) (.pi (.app (.var 3) (.var 0))
      (.app (.var 4) (.app (.app (.const consN) (.var 2)) (.var 1))))))
      (sortTm (.succ Tower.zero)) :=
    piC (up₁ (numT_typedC numMem)) (piC (up₁ (listT_typedC listMem))
      (piC tIH (.appElim (B := sortTm (.succ Tower.zero)) (.var 4) tConsAL)))
  exact .snoc (.snoc (.snoc .nil ⟨_, .sort _, Derivable.mono sub tE0⟩)
    ⟨_, .sort _, Derivable.mono sub tE1⟩) ⟨_, .sort _, Derivable.mono sub tE2⟩

/-- **`loopTerm` is typed** in the looping package, at the motive at the one-element list. -/
theorem loopTerm_typed :
    Typed loopRules loopContext loopTerm (.app (.var 2) zeroList) := by
  have sub := listTypeDecls_sub_loop [numN, listN, nilN, consN]
  have numMem : numN ∈ [numN, listN, nilN, consN] := by decide
  have listMem : listN ∈ [numN, listN, nilN, consN] := by decide
  have tRec : Typed loopRules loopContext (.const listRecN)
      (liftClosed (recType listN listMotives listCtors)) :=
    .const (show loopRules.constantType listRecN = some (recType listN listMotives listCtors) from
      rfl) (Derivable.mono sub listRecType_typed) (.sort _)
  rw [listRecType_eq] at tRec
  have tZero : Typed loopRules loopContext (.const zeroN) numT :=
    .const (show loopRules.constantType zeroN = some numT by decide)
      (Derivable.mono (listTypeDecls_sub_loop [numN, listN]) (numT_typedC (by decide))) (.sort _)
  have tNil : Typed loopRules loopContext (.const nilN) (.const listN) :=
    .const (show loopRules.constantType nilN = some (.const listN) from rfl) loop_listT (.sort _)
  have tCons : Typed loopRules loopContext (.const consN)
      (.pi numT (.pi (.const listN) (.const listN))) :=
    .const (show loopRules.constantType consN = some (.pi numT (.pi (.const listN) (.const listN)))
      from rfl) (Derivable.mono sub (piC (numT_typedC numMem)
        (piC (listT_typedC listMem) (listT_typedC listMem)))) (.sort _)
  have tList : Typed loopRules loopContext zeroList (.const listN) :=
    .appElim (B := .const listN)
      (.appElim (B := .pi (.const listN) (.const listN)) tCons tZero) tNil
  exact .appElim (.appElim (.appElim (.appElim tRec (.var 2)) (.var 1)) (.var 0)) tList

end LoopTyping

/-- **Negative example: a recursor that recurses on the same list is not strongly
normalizing.** In the package with the lists whose rule at `cons` is
`list-rec P z s (cons a l) ⟶ s a l (list-rec P z s (cons a l))`, the recursor at the
one-element list is typed in a formed context, and its reduction has no end; so the strong
normalization of `dataRules_sn` rests on the rules being structural. -/
theorem loopRules_not_sn :
    CtxFormed loopRules loopContext ∧
      Typed loopRules loopContext loopTerm (.app (.var 2) zeroList) ∧
      ¬ SN loopRules loopTerm :=
  ⟨loopContext_formed, loopTerm_typed, loopTower_not_sn 0⟩

/-! ## Canonicity at the lists

With the facts that the adequacy of the package with the lists gives, canonicity holds at the
lists: `cons 1 nil` reduces to a `cons` (`cons_one_nil_canonical`), and the closed recursion
`append (cons 1 nil) nil` to `nil` or to a `cons` (`appendOneNil_canonical`). -/

section ListsCanonical

/-- **Positive example: the one-element list of the numeral one is canonical, at `cons`.** -/
theorem cons_one_nil_canonical :
    ∃ a l, CTyped (dataChurch listDecl) .nil a cnum ∧ CTyped (dataChurch listDecl) .nil l clist ∧
      CRedTm (dataHead listDecl_admissible) .nil (ccons (csuc czero) cnil) (ccons a l) clist := by
  obtain ⟨i, k, fs, args, hi, -, fields, red⟩ := data_canonical listDecl_admissible
    listDecl_avoids cons_one_nil_typed
  rcases listDecl_ctor_forms hi fields with e | ⟨a, l, ta, tl, e⟩
  · rw [e] at red
    have same := CRedTm.nf_unique red (CRedTm.refl cons_one_nil_typed)
      (fun u => (dataHead listDecl_admissible).ctor_normal (d := listN) (c := nilN) (fs := [])
        (ms := []) u (.inr ⟨rfl, 0, [], rfl, rfl⟩) rfl)
      (fun u => (dataHead listDecl_admissible).ctor_normal (d := listN) (c := consN)
        (ms := [csuc czero, cnil]) u (.inr ⟨rfl, 1, [.closed (.const numN), .recursive], rfl, rfl⟩)
        rfl)
    cases same
  · rw [e] at red
    exact ⟨a, l, ta, tl, red⟩

/-- **Positive example: a closed recursion is canonical.** `append (cons 1 nil) nil` computes by
the recursor's rules to `nil` or to a `cons`. -/
theorem appendOneNil_canonical :
    CRedTm (dataHead listDecl_admissible) .nil appendOneNil cnil clist ∨
      ∃ a l, CTyped (dataChurch listDecl) .nil a cnum ∧ CTyped (dataChurch listDecl) .nil l clist ∧
        CRedTm (dataHead listDecl_admissible) .nil appendOneNil (ccons a l) clist := by
  obtain ⟨i, k, fs, args, hi, -, fields, red⟩ := data_canonical listDecl_admissible
    listDecl_avoids appendOneNil_typed
  rcases listDecl_ctor_forms hi fields with e | ⟨a, l, ta, tl, e⟩
  · rw [e] at red
    exact .inl red
  · rw [e] at red
    exact .inr ⟨a, l, ta, tl, red⟩

end ListsCanonical

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
