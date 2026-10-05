import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueLists
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectTrees
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Inductive
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Synthesis

/-!
# Conversion completeness at every declared datatype

A simple datatype `d` admissible over the object package (`hd : d.Admissible objectChurch`)
gives the package `dataRules d` with the roles `dataRoles d`. For every such `d` whose names
avoid the names the value model keeps for itself, the transport's constants and the daimon
(`AvoidsModelNames d`), the package's
conversion algorithm is complete: derivably equal terms of a formed context are algorithmically
equal (`dataRules_algorithmicComplete`). So a refutation by the algorithm, two terms of a
principal type that the algorithm does not relate there, shows that they are equal at no type
(`dataRules_not_equal_of_unrelated`).

**The conversion model** (`dataNewSoundN`). The package is the extension `dataTExt` of the
transport value model, and the conversion model over it reads the datatype by the three clauses
of a simple inductive type (`Conversion.ValidTmN.inductiveType`, `inductiveCtor`,
`inductiveRec`):

* the type, with its closed field types interpreted by the fundamental lemma of the object
  package in the same model (`closedField_interpN`);
* each constructor, its declared type valid by the fundamental lemma of the stage of the type
  (`dataN_valid_ctor`);
* the recursor, its declared type valid by the fundamental lemma of the stage of the
  constructors (`dataN_valid_rec`); on the realizer side it is declared at its type and computes
  by its rules (`dataRecursor`);
* the recursor's rules are steps of the value side's reduction, so they preserve meaning.

The object package's constants are valid in the same model (`objectRules_typedSoundN`). So the
package is sound for its conversion model over every lawful generic equality that respects
typed weak-head reduction and has the decoder as a congruence, and escape into it is the
generic equality (`data_equal_escapeN`).

**What completeness takes** (`real_algorithmicComplete_of_facts` at `dataTExt`):

* the facts about the weak-head forms of the package's types (`dataRules_formFacts`);
* the recursor's rules preserve typing (`data_newPreserving`), inspect only constructor forms
  (`data_newOnly`) and reflect substitutions of neutral terms (`data_newReflects`);
* the package's types are strongly normalizing (`dataRules_type_sn`);
* the new names are sound for the conversion model (`dataNewSoundN`).

The remaining hypothesis is `AvoidsModelNames d`, which strong normalization and the value model
use.

**The three faces.** This adds to the intensional face: the typed equality of the package is
decided by its conversion algorithm, read through the conversion model, whose value side is the
extensional reading of the datatype as the least relation closed under its constructors and
whose realizer side is the operational face, the package's own reduction.

Positive examples: the lists of numbers and the binary trees of numbers are complete
(`listRules_algorithmicComplete`, `btreeRules_algorithmicComplete`). Negative example: a package
whose constant reduces only to itself has no facts about its types' weak-head forms and is not
complete (`Conversion.Tower.loop_not_complete`); strong normalization of the types, which needs
the recursor's rules to be structural (`loopRules_not_sn`), is what rules this out here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization hiding World
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Presentation.TypedEquality.Annotated
open Package (U0 jName)

namespace CodeModel
namespace ConvRules

/-! ## The declarations of the package -/

section Declarations

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)
include hd

/-- The datatype is declared at its universe. -/
theorem dataRules_type_declared :
    (dataRules d).constantType d.type = some (.head d.typeUniverse) := by
  show sumDecls objectRules.constantType
    (inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse) d.type = _
  rw [sumDecls_right (objectRules_undeclared hd.new.typeNew)]
  exact inductiveDecls_type

/-- Each constructor is declared at the function type of its fields. -/
theorem dataRules_ctor_declared {k : DeclName} {fs : List CtorField} (mem : (k, fs) ∈ d.ctors) :
    (dataRules d).constantType k = some (ctorType d.type fs) := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem mem
  show sumDecls objectRules.constantType
    (inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse) k = _
  rw [sumDecls_right (objectRules_undeclared (hd.new.ctorsNew _ mem))]
  exact inductiveDecls_ctor hd.distinct hi

/-- The recursor is declared at its type. -/
theorem dataRules_rec_declared :
    (dataRules d).constantType d.recursor = some (recType d.type d.motiveUniverse d.ctors) := by
  show sumDecls objectRules.constantType
    (inductiveDecls d.type d.typeUniverse d.ctors d.recursor d.motiveUniverse) d.recursor = _
  rw [sumDecls_right (objectRules_undeclared hd.new.recNew)]
  exact inductiveDecls_rec hd.distinct

omit hd in
/-- A package restricted to some of its names is contained in it. -/
theorem restrict_sub (R : Rules Tower.Head) (allowed : DeclName → Bool) :
    RulesSub (R.restrict allowed) R where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun {c T} declared => by
    change (if allowed c then R.constantType c else none) = some T at declared
    split_ifs at declared
    exact declared
  computation := id

/-- **The recursor is declared in the package**, at its type, a type of a universe, with its
constructors declared and its role. -/
theorem dataRecursor (S : Setting Tower.Head ℕ) (hR : S.R = dataRules d)
    (hroles : S.roles = dataRoles d) :
    DeclaresRecursor S d.type d.ctors d.recursor d.motiveUniverse := by
  obtain ⟨R, roles, E, levels, shape, constructors⟩ := S
  dsimp only at hR hroles
  subst hR hroles
  obtain ⟨w, hw, typed⟩ := (dataCtorStage_declares hd).recType_formed
    (levelsRestrict (levelsWith ConvRules.objectLevels [.datatype d]) _) hd.motiveUniverse
  have typedRaw : Typed ((dataRules d).restrict (dataCtorStage d)) .nil
      (recType d.type d.motiveUniverse d.ctors) (.head w) := by
    have := CDerivable.erase typed
    rw [CStatement.erase, erase_liftTm] at this
    exact this
  exact { recRole := dataRoles_rec hd.distinct
          ctorDeclared := fun mem => dataRules_ctor_declared hd mem
          recDeclared := dataRules_rec_declared hd
          recTyped := ⟨w, hw, Derivable.mono (restrict_sub _ _) typedRaw⟩ }

/-- A root step of the package at a spine of a new name is a step of the recursor. -/
theorem dataStep_new {n : Nat} {c : DeclName} {args : List (Tower.Tm n)} {r : Tower.Tm n}
    (mem : c ∈ dataNames d) (step : (dataRules d).computation.step (appSpine (.const c) args) r) :
    IotaStep d.recursor d.ctors (appSpine (.const c) args) r := by
  rcases step with step | iota
  · exfalso
    obtain ⟨c', arity, inspect, args', role, e, -, -⟩ := objectShape.spine step
    obtain ⟨rfl, -⟩ := appSpine_const_injective e
    exact nomatch (objectRoles_dataName hd mem).symm.trans role
  · exact iota

end Declarations

/-! ## The conversion model at a declared datatype -/

section Model

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch) (avoid : AvoidsModelNames d)
  (v : Nat → Nat) (facts : FormFacts (dataRules d) (dataRoles d))
  {E : GenericEquality Tower.Head} (lawsE : E.Laws (dataRules d) (dataRoles d))
  (reduceE : RespectsReduction (dataRules d) (dataRoles d) E)
  (holdsE : HoldsCongruence E programCodes)

/-- **The conversion model of the package with a declared datatype**, at a realizer side. -/
abbrev dataNModel : NModel Tower.Head ℕ :=
  nmodel (dataTExt hd avoid) v (realSideAt (dataTExt hd avoid) facts E lawsE reduceE)

include holdsE

/-- **A closed field type is interpreted at the level of the datatype's universe** at every
world, by the fundamental lemma of the object package in the conversion model. -/
theorem closedField_interpN {F : Tower.Tm 0} (h : F ∈ ValueSide.closedFields d.ctors) {m : Nat}
    (ξ : Consistency.World (dataNModel hd avoid v facts lawsE reduceE).reading m) :
    ∃ P, NInterp (dataNModel hd avoid v facts lawsE reduceE)
      ((dataNModel hd avoid v facts lawsE reduceE).levels.level d.typeUniverse) ξ
        (liftClosed F) P := by
  obtain ⟨entry, hmem, hF⟩ := mem_closedFields_entry h
  have typed : Typed objectRules .nil F (.head d.typeUniverse) := by
    have := CDerivable.erase (hd.fields entry hmem F hF)
    rw [CStatement.erase, erase_liftTm] at this
    exact this
  have sound := objectRules_typedSoundN (dataTExt hd avoid) v facts lawsE reduceE holdsE
  have valid := Typed.validN sound typed trivial
  have hu := sound.isUniverse hd.typeUniverse
  obtain ⟨rel, -⟩ := valid.2 (r := 0) (ξ := ξ) (σ := fun i => i.elim0)
    (σ' := fun i => i.elim0) (Δ := .nil) (ς := fun i => i.elim0) (ς' := fun i => i.elim0)
    CtxFormed.nil (ValueSide.DenS.sort hu ξ)
  rw [Normalization.subst_closed] at rel
  obtain ⟨P, hP, -, -⟩ := ValueSide.universeAt.den rel
  exact ⟨P, hP⟩

/-- **The datatype is a valid term of its universe** in the conversion model: the clause of a
simple inductive type, with the packs of its closed field types described by their
interpretation. -/
theorem dataN_valid_type :
    ValidTmN (dataNModel hd avoid v facts lawsE reduceE) .nil (.const d.type)
      (.head d.typeUniverse) := by
  have sound := objectRules_typedSoundN (dataTExt hd avoid) v facts lawsE reduceE holdsE
  have laws := nmodel_laws (dataTExt hd avoid) v
    (realSideAt (dataTExt hd avoid) facts E lawsE reduceE)
  exact ValidTmN.inductiveType laws (dataRoles_type (base := tmodelRoles))
    (dataRoles_type (base := objectRoles)) (sound.isUniverse hd.typeUniverse) hd.typeUniverse
    (dataRules_type_declared hd)
    (fun {_} ξ F => ValueSide.Pack.describe _ fun Q => NInterp
      (dataNModel hd avoid v facts lawsE reduceE)
      ((dataNModel hd avoid v facts lawsE reduceE).levels.level d.typeUniverse) ξ
        (liftClosed F) Q)
    fun {_} ξ {F} hF => by
      obtain ⟨P, hP⟩ := closedField_interpN hd avoid v facts lawsE reduceE holdsE hF ξ
      rw [ValueSide.Pack.describe_eq laws.value.alg hP
        fun Q hQ => hQ.deterministic laws hP]
      exact hP

omit holdsE in
/-- **Every root step of the package is validated by the conversion model**, in every
package that declares identity elimination as the object package does: the object package's
steps as in the transport value model, the recursor's rules as steps of the model's
reduction. -/
theorem dataRootN {R' : Rules Tower.Head}
    (declaredJ : R'.constantType jName = some (elimType (.sort Tower.zero) (.sort Tower.zero)))
    {n : Nat} {l r : Tower.Tm n} (step : (dataRules d).computation.step l r) :
    RootSemanticN (dataNModel hd avoid v facts lawsE reduceE) l r ∨
      TypedRootN R' (dataNModel hd avoid v facts lawsE reduceE) l r := by
  have laws := nmodel_laws (dataTExt hd avoid) v
    (realSideAt (dataTExt hd avoid) facts E lawsE reduceE)
  rcases step with step | iota
  · rcases step with step | step
    · exact stage_root (dataTExt hd avoid) v (realSideAt_over (dataTExt hd avoid) facts lawsE
        reduceE) (allowed := fun _ => true) (fun _ => declaredJ) step
    · exact .inl (ModelRootN.semantic laws ((dataTExt hd avoid).programDecodes v)
        ⟨.inr step, (dataTExt hd avoid).realDecodes step⟩)
  · exact .inl (ModelRootN.semantic laws ((dataTExt hd avoid).programDecodes v)
      ⟨.inl ((dataTExt hd avoid).extraStep v List.mem_cons_self iota), .inr iota⟩)

omit holdsE in
/-- **A stage of the package is sound for the conversion model** when it has identity
elimination and its constants are valid. -/
theorem dataStageN_typedSoundN {allowed : DeclName → Bool} (hJ : allowed jName = true)
    (consts : ∀ {name : DeclName} {type : Tower.Tm 0}, allowed name = true →
      (dataRules d).constantType name = some type →
        ValidTmN (dataNModel hd avoid v facts lawsE reduceE) .nil (.const name) type) :
    TypedSoundN ((dataRules d).restrict allowed) (dataNModel hd avoid v facts lawsE reduceE) where
  laws := nmodel_laws _ v _
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  headTyping' := id
  isUniverse' := id
  join' := id
  cumulative' := id
  headEq' := id
  root := fun step => dataRootN hd avoid v facts lawsE reduceE (by
    show (if allowed jName then (dataRules d).constantType jName else none) = _
    rw [if_pos hJ]
    exact dataRules_declared_j) step
  constants := fun {name type} declared => by
    change (if allowed name then (dataRules d).constantType name else none) = some type at declared
    split_ifs at declared with h
    exact consts h declared

/-- **Every constructor is a valid term of its declared type** in the conversion model: the
clause of a constructor, with its declared type valid by the fundamental lemma of the stage of
the type. -/
theorem dataN_valid_ctor {k : DeclName} {fs : List CtorField} (mem : (k, fs) ∈ d.ctors) :
    ValidTmN (dataNModel hd avoid v facts lawsE reduceE) .nil (.const k) (ctorType d.type fs) := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem mem
  obtain ⟨w, hw, typed⟩ := (dataTypeStage_declares hd).ctorType_formed
    (levelsRestrict (levelsWith ConvRules.objectLevels [.datatype d]) _) hi
  have typedRaw : Typed ((dataRules d).restrict (dataTypeStage d)) .nil (ctorType d.type fs)
      (.head w) := by
    have := CDerivable.erase typed
    rw [CStatement.erase, erase_liftTm] at this
    exact this
  have objectSound := objectRules_typedSoundN (dataTExt hd avoid) v facts lawsE reduceE holdsE
  have sound := dataStageN_typedSoundN hd avoid v facts lawsE reduceE (allowed := dataTypeStage d)
    (dataTypeStage_object hd (objectChurch_constantType_ne_none (by decide)))
    fun {name type} allowed declared => by
      rcases dataRules_declared_cases declared with object | ⟨rfl, rfl⟩ | ⟨j, fields, hj, rfl⟩ |
        ⟨rfl, rfl⟩
      · exact objectSound.constants object
      · exact dataN_valid_type hd avoid v facts lawsE reduceE holdsE
      · exfalso
        simp only [dataTypeStage, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
          List.mem_cons, not_or] at allowed
        exact allowed.2 (List.mem_map.2 ⟨_, List.mem_of_getElem? hj, rfl⟩)
      · exact absurd allowed (by
          unfold dataTypeStage
          rw [decide_eq_true List.mem_cons_self]
          exact Bool.false_ne_true)
  obtain ⟨validT, partsT, -⟩ := Derivable.validTN sound typedRaw trivial
  exact ValidTmN.inductiveCtor
    (nmodel_laws (dataTExt hd avoid) v (realSideAt (dataTExt hd avoid) facts E lawsE reduceE))
    (dataRoles_type (base := tmodelRoles))
    (dataRoles_type (base := objectRoles)) mem (dataRules_ctor_declared hd mem)
    (validT.validTy (sound.isUniverse hw) (sound.isUniverse' hw)) partsT

/-- **The recursor is a valid term of its declared type** in the conversion model: the clause
of the recursor of a simple inductive type, with its declared type valid by the fundamental
lemma of the stage of the constructors. -/
theorem dataN_valid_rec :
    ValidTmN (dataNModel hd avoid v facts lawsE reduceE) .nil (.const d.recursor)
      (recType d.type d.motiveUniverse d.ctors) := by
  obtain ⟨w, hw, typed⟩ := (dataCtorStage_declares hd).recType_formed
    (levelsRestrict (levelsWith ConvRules.objectLevels [.datatype d]) _) hd.motiveUniverse
  have typedRaw : Typed ((dataRules d).restrict (dataCtorStage d)) .nil
      (recType d.type d.motiveUniverse d.ctors) (.head w) := by
    have := CDerivable.erase typed
    rw [CStatement.erase, erase_liftTm] at this
    exact this
  have objectSound := objectRules_typedSoundN (dataTExt hd avoid) v facts lawsE reduceE holdsE
  have sound := dataStageN_typedSoundN hd avoid v facts lawsE reduceE (allowed := dataCtorStage d)
    (dataCtorStage_object hd (objectChurch_constantType_ne_none (by decide)))
    fun {name type} allowed declared => by
      rcases dataRules_declared_cases declared with object | ⟨rfl, rfl⟩ | ⟨j, fields, hj, rfl⟩ |
        ⟨rfl, rfl⟩
      · exact objectSound.constants object
      · exact dataN_valid_type hd avoid v facts lawsE reduceE holdsE
      · exact dataN_valid_ctor hd avoid v facts lawsE reduceE holdsE (List.mem_of_getElem? hj)
      · exact absurd allowed (by
          unfold dataCtorStage
          rw [decide_eq_true rfl]
          exact Bool.false_ne_true)
  obtain ⟨validT, partsT, -⟩ := Derivable.validTN sound typedRaw trivial
  have decl : ValueSide.InductiveValues (dataNModel hd avoid v facts lawsE reduceE).value d.type
      d.recursor d.ctors :=
    ⟨dataRoles_type (base := tmodelRoles), dataRoles_rec (base := tmodelRoles) hd.distinct,
      fun h => (dataTExt hd avoid).extraStep v List.mem_cons_self h⟩
  exact ValidTmN.inductiveRec
    (nmodel_laws (dataTExt hd avoid) v (realSideAt (dataTExt hd avoid) facts E lawsE reduceE))
    decl (dataRecursor hd _ rfl rfl)
    (dataRoles_type (base := objectRoles)) (fun iota => .inr iota)
    (objectSound.isUniverse hd.motiveUniverse) hd.motiveUniverse
    (validT.validTy (sound.isUniverse hw) (sound.isUniverse' hw)) partsT

/-- **The new names of the package with a declared datatype are sound for its conversion
model**: the type, the constructors and the recursor are valid, and the recursor's rules are
steps of the model's reduction. -/
theorem dataNewSoundN :
    NewSoundN (dataTExt hd avoid) (dataNModel hd avoid v facts lawsE reduceE) where
  constants := fun {name type} mem declared => by
    rcases dataRules_declared_cases declared with object | ⟨rfl, rfl⟩ | ⟨j, fields, hj, rfl⟩ |
      ⟨rfl, rfl⟩
    · exact absurd (objectRules_undeclared (dataNames_new hd mem)) (by rw [object]; nofun)
    · exact dataN_valid_type hd avoid v facts lawsE reduceE holdsE
    · exact dataN_valid_ctor hd avoid v facts lawsE reduceE holdsE (List.mem_of_getElem? hj)
    · exact dataN_valid_rec hd avoid v facts lawsE reduceE holdsE
  roots := fun {n c args r} mem step => by
    have iota := dataStep_new hd mem step
    exact .inl (ModelRootN.semantic
      (nmodel_laws (dataTExt hd avoid) v (realSideAt (dataTExt hd avoid) facts E lawsE reduceE))
      ((dataTExt hd avoid).programDecodes v)
      ⟨.inl ((dataTExt hd avoid).extraStep v List.mem_cons_self iota), step⟩)

include hd avoid facts lawsE reduceE holdsE in
/-- **Escape at the package with a declared datatype**: derivably equal terms of a formed
context are related by the generic equality, at every lawful generic equality that respects
typed weak-head reduction and has the decoder as a congruence, given the facts. -/
theorem data_equal_escapeN {n : Nat} {Γ : Tower.Ctx n} {t u A : Tower.Tm n}
    (formed : CtxFormed (dataRules d) Γ) (equal : Equal (dataRules d) Γ t u A) :
    E.convTm Γ t u A :=
  real_equal_escapeN (dataTExt hd avoid) facts lawsE reduceE holdsE
    (dataNewSoundN hd avoid (fun _ => 0) facts lawsE reduceE holdsE) formed equal

end Model

/-! ## The inputs of completeness at the new names -/

section Inputs

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch)

include hd in
/-- **The recursor's rules inspect only constructor forms.** -/
theorem data_newOnly {c : DeclName} {arity : Nat} {inspect : InspectTree} (mem : c ∈ dataNames d)
    (role : dataRoles d c = .computes arity inspect) : inspect.OnlyConstructors := by
  simp only [dataNames, List.mem_cons] at mem
  rcases mem with rfl | rfl | memC
  · cases (dataRoles_type (d := d) (base := objectRoles)).symm.trans role
  · cases (dataRoles_rec (base := objectRoles) hd.distinct).symm.trans role
    exact .split fun _ => .leaf
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 memC
    obtain ⟨i, hi⟩ := List.getElem?_of_mem he
    cases (dataRoles_ctor (base := objectRoles) hd.distinct hi).symm.trans role

include hd in
/-- **The recursor's rules reflect substitutions of neutral terms**: a rule that applies to a
spine of neutral instances applies to the spine. -/
theorem data_newReflects ⦃n k : Nat⦄ ⦃σ : Sub Tower.Head n k⦄
    (neutral : NeutralSub (dataRoles d) σ) ⦃c : DeclName⦄ ⦃args : List (Tower.Tm n)⦄
    ⦃u : Tower.Tm k⦄ (mem : c ∈ dataNames d)
    (step : (dataRules d).computation.step
      (appSpine (.const c) (args.map (Presentation.subst σ))) u) :
    ∃ t', (dataRules d).computation.step (appSpine (.const c) args) t' := by
  obtain ⟨t', h⟩ := iotaComputation_reflectsNeutral (roles := dataRoles d) dataRoles_type
    (dataConstructorsDeclared hd) neutral (dataStep_new hd mem step)
  exact ⟨t', .inr h⟩

variable (avoid : AvoidsModelNames d)

include hd avoid in
/-- **The recursor's rules preserve typing**, given the facts: they are the rules of a
recursor declared at its type. -/
theorem data_newPreserving (facts : FormFacts (dataRules d) (dataRoles d)) {n : Nat}
    {Γ : Tower.Ctx n} {c : DeclName} {args : List (Tower.Tm n)} {r A : Tower.Tm n}
    (formed : CtxFormed (dataRules d) Γ) (mem : c ∈ dataNames d)
    (step : (dataRules d).computation.step (appSpine (.const c) args) r)
    (typing : Typed (dataRules d) Γ (appSpine (.const c) args) A) : Typed (dataRules d) Γ r A :=
  (dataRecursor hd (realSetting (dataTExt hd avoid)) rfl rfl).step_preserves
    (S := realSetting (dataTExt hd avoid)) facts (RulesSub.refl _) formed
    (dataStep_new hd mem step) typing

include hd avoid in
/-- **The types of the package with a declared datatype are strongly normalizing.** -/
theorem dataRules_type_sn {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}
    (formed : CtxFormed (dataRules d) Γ) (isA : IsType (dataRules d) Γ A) :
    StrongNormalization.SN (dataRules d) A := by
  obtain ⟨u, -, typed⟩ := isA
  exact (dataRules_sn hd avoid formed typed).1

end Inputs

/-! ## Completeness -/

section Completeness

variable {d : Datatype Tower.Head} (hd : d.Admissible objectChurch) (avoid : AvoidsModelNames d)
include hd avoid

/-- **Conversion completeness at every declared datatype**: for every simple datatype
admissible over the object package whose names avoid the names the value model keeps for itself,
derivably equal terms of a formed context of the package with the datatype are algorithmically
equal. -/
theorem dataRules_algorithmicComplete : AlgorithmicComplete (dataRules d) (dataRoles d) :=
  real_algorithmicComplete_of_facts (dataTExt hd avoid) (dataRules_formFacts hd avoid)
    (fun formed mem step typing =>
      data_newPreserving hd avoid (dataRules_formFacts hd avoid) formed mem step typing)
    (fun mem role => data_newOnly hd mem role)
    (fun _ _ _ neutral _ _ _ mem step => data_newReflects hd neutral mem step)
    (fun formed isA => dataRules_type_sn hd avoid formed isA)
    (fun lawsE reduceE holdsE =>
      dataNewSoundN hd avoid (fun _ => 0) (dataRules_formFacts hd avoid) lawsE reduceE holdsE)

/-- **A refutation by the algorithm at a declared datatype is sound**: two terms of a principal
type that the conversion algorithm does not relate there are equal at no type. -/
theorem dataRules_not_equal_of_unrelated {n : Nat} {Γ : Tower.Ctx n} {t u T C : Tower.Tm n}
    (formed : CtxFormed (dataRules d) Γ) (tT : Typed (dataRules d) Γ t T)
    (uT : Typed (dataRules d) Γ u T)
    (principal : ∀ {X}, Typed (dataRules d) Γ t X → TypeLe (dataRules d) Γ T X)
    (unrelated : ¬ Algorithmic (dataRules d) (dataRoles d) (.terms Γ t u T)) :
    ¬ Equal (dataRules d) Γ t u C :=
  not_equal_of_unrelated (S := realSetting (dataTExt hd avoid)) (dataRules_formFacts hd avoid)
    (realRules_roots (dataTExt hd avoid) (dataRules_formFacts hd avoid)
      fun formed mem step typing =>
        data_newPreserving hd avoid (dataRules_formFacts hd avoid) formed mem step typing)
    (realRules_heads _) (realRules_algebra _) (dataRules_algorithmicComplete hd avoid) formed tT
    uT principal unrelated

end Completeness

/-! ## Examples -/

/-- **Positive: the lists of numbers are complete.** -/
theorem listRules_algorithmicComplete :
    AlgorithmicComplete (dataRules listDecl) (dataRoles listDecl) :=
  dataRules_algorithmicComplete listDecl_admissible listDecl_avoids

/-- **Positive: the binary trees of numbers are complete.** -/
theorem btreeRules_algorithmicComplete :
    AlgorithmicComplete (dataRules btreeDecl) (dataRoles btreeDecl) :=
  dataRules_algorithmicComplete btreeDecl_admissible btreeDecl_avoids

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
