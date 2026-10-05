import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNTransport
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectSteps
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Fundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.CodeConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.StrongNormalizationModel.Inductive
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Transport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.StrongNormalization.Spines

/-!
# The transport value model on the skeleton-free value side

Route T's consistency model `tmodelC`, its daimon and the object package as its
realizer side, read by model SN over the skeleton-free value side with levels in
the natural numbers (`vmodel`):

* its laws are those of `tmodelC` with the daimon rigid and the constructors of
  the numbers declared (`vmodel_laws`);
* its reduction, roles and levels are those of `tmodelC`, which has the
  transport table, so the rows of the table hold (`vmodel_coeRules`);
* its reading of codes is the candidate reading of the object package
  (`vmodel_reading_eq`), since the numerals of the two sides agree;
* the program's codes are read by it (`TExtension.programCodes_readS`).

**Extensions by new names** (`TExtension`). Each statement is made once for every extension of
the transport value model by new constants: new roles and computations on the value side, and a
larger package with roles on the realizer side, both agreeing with the transport value model off
the new names. The transport value model is the extension by nothing (`objectTExt`,
`objectTExt_model`); the object package with a declared datatype is another. The transport table
reads every inductive type as a type constant by its role, so its rows hold in every extension
(`TExtension.coeRules`).

## Root steps

Every root step of a stage of the executable package without identity
elimination is a step of the model's reduction, so it preserves meaning, and a
stage whose constants are valid is sound (`TExtension.stage_soundS`).

Identity elimination is different. On the value side it transports its method
along the motive, `J A x P d y e ⟶ coe (P x (refl x)) (P y e) d`, while the
object package computes by its linear rule `J A x P d y (refl z) ⟶ d`, which
does not compare `x`, `y` and `z`. The root obligation of model SN reads a root
step without its typing: its two sides must be validly equal wherever each is a
valid term of one type. At `J U2 U1 (λ y _. y) num U0 (refl U0)`, whose motive
sends the point `U1` and the endpoint `U0` to themselves, both sides are valid
terms of `U0`: the transport from `U1` into `U0` is stuck on the daimon, a
valid type, and realized by the strongly normalizing object term, while the
method `num` is a type of `U0`. They are not equal: the daimon's pack is not
the numbers' pack (`vmodel_mismatchJ_not_equal`). So the linear rule's root
obligation fails (`vmodel_jRoot_not_semantic`), and the object package is not
sound for the model as the fundamental lemma states soundness
(`objectRules_not_soundS_vmodel`). The redex is no typed term: `refl U0` is no
path from `U1`. Validating the object package's identity elimination needs the
typing of its path; read with the typing facts of its redexes the rule holds,
and the object package is sound (`SNValueSound`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.StrongNormalization
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Consistency (World Morph Carrier Kind CodesRead)
open Presentation.TypedEquality.Impredicative.Realizability (Daimonic)
open Mettapedia.Logic
open Package (U0 numT jName numRecName iterName eqAtName sucMoveName keepName transportName
  composeName returnIterName sucStepName)

namespace CodeModel

/-! ## The model -/

/-- **The transport value model on the skeleton-free value side**: route T's
consistency model, with its levels in the natural numbers, the daimon, and the
object package as the realizer side. -/
def vmodel (v : Nat → Nat) : ModelSN.SNModel Tower.Head Nat where
  toModel := tmodelC v
  star := starN
  realizers := objectRealizers

/-! ## Rigid constants -/

/-- A rigid constant of the consistency model other than the decoder is rigid in
the object package. -/
theorem objectRoles_of_modelRoles {T : DeclName} (role : modelRoles T = .rigid)
    (notHolds : T ≠ holdsN) : objectRoles T = .rigid := by
  have hj : T ≠ jName := by
    intro e
    rw [e] at role
    change (if jName = jName then Role.computes 6 .leaf else _) = _ at role
    rw [if_pos rfl] at role
    cases role
  have hi : T ≠ impN := by
    intro e
    rw [e] at role
    change (if impN = jName then Role.computes 6 .leaf else
      if impN = impN then Role.constructor 2 else _) = _ at role
    rw [if_neg (by decide), if_pos rfl] at role
    cases role
  cases ha : SetProfile.allInstance? T with
  | some _ =>
      unfold modelRoles at role
      rw [if_neg hj, if_neg hi, ha] at role
      cases role
  | none =>
      cases he : SetProfile.eqInstance? T with
      | some _ =>
          unfold modelRoles at role
          rw [if_neg hj, if_neg hi, ha] at role
          simp only [Option.isSome_none, Bool.false_eq_true, if_false, he, Option.isSome_some,
            if_true] at role
          cases role
      | none =>
          rw [objectRoles_of notHolds hi ha he, ← modelRoles_of hj hi ha he]
          exact role

/-- A rigid constant of the transport value model other than the decoder is
rigid in the object package. -/
theorem objectRoles_of_tmodelRoles {T : DeclName} (role : tmodelRoles T = .rigid)
    (notHolds : T ≠ holdsN) : objectRoles T = .rigid := by
  by_cases fresh : T ∈ coeNameList
  · exfalso
    simp only [coeNameList, List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl | rfl | rfl | rfl | rfl
    · rw [tmodelRoles_coe] at role; cases role
    · rw [tmodelRoles_coeU] at role; cases role
    · rw [tmodelRoles_coeConst] at role; cases role
    · rw [tmodelRoles_coePi] at role; cases role
    · rw [tmodelRoles_coeSigma] at role; cases role
  · rw [tmodelRoles_eq fresh] at role
    exact objectRoles_of_modelRoles role notHolds

/-! ## Extensions of the model by declared names -/

namespace ConvRules

/-- The universe levels of the object package: those of the executable
package. -/
def objectLevels : LevelModel objectRules ℕ where
  level := (levels fun _ => 0).level
  successor := (levels fun _ => 0).successor
  universe_typing := (levels fun _ => 0).universe_typing
  ground_typing := (levels fun _ => 0).ground_typing
  cumulative_universe := (levels fun _ => 0).cumulative_universe
  headEq_level := (levels fun _ => 0).headEq_level
  join_level := (levels fun _ => 0).join_level
  join_exists := (levels fun _ => 0).join_exists
  join_upper := (levels fun _ => 0).join_upper
  cumulative_refl := (levels fun _ => 0).cumulative_refl
  headEq_symm := (levels fun _ => 0).headEq_symm
  headEq_trans := (levels fun _ => 0).headEq_trans
  universe_decided := (levels fun _ => 0).universe_decided

end ConvRules

/-- **An extension of the transport value model by declared names**: on the value side, roles
that extend the transport value model's by new names and further computations headed by them;
on the realizer side, a package containing the object package, with roles, whose root steps,
declared types and roles at every other name are the object package's, and whose new
constructors build new inductive types of a universe. The transport value model is the extension
by no name (`objectTExt`); the object package with a declared datatype is another. -/
structure TExtension where
  /-- The new names. -/
  names : List DeclName
  /-- The value side's roles. -/
  roles : Roles Tower.Head
  /-- The value side's computations at the new names. -/
  extra : List (DeclName × RootComputation Tower.Head)
  /-- The realizer side's rules. -/
  realRules : Rules Tower.Head
  /-- The realizer side's roles. -/
  realRoles : Roles Tower.Head
  realShape : RootShape realRules realRoles
  realReflects : RootReflectsRename realRules.computation
  realDecoderRoles : DecoderRoles realRoles programCodes.decoders
  realNumerals : NumeralRoles realRoles zeroN sucN
  realDeclared : ConstructorsDeclared realRoles
  realDecodes : ∀ {n : Nat} {l r : Tower.Tm n}, DecoderStep programCodes.decoders l r →
    realRules.computation.step l r
  extends_ : TExtends roles names
  declared : ConstructorsDeclared roles
  extraNames : ∀ entry ∈ extra, entry.1 ∈ names
  extraSpine : ∀ entry ∈ extra, SpineShaped roles entry.2
  extraHeaded : ∀ entry ∈ extra, HeadedBy entry.1 entry.2
  extraDeterministic : ∀ entry ∈ extra, Deterministic entry.2
  extraDistinct : (extra.map Prod.fst).Nodup
  /-- The realizer side's roles at every other name are the object package's. -/
  realOld : ∀ {c : DeclName}, c ∉ names → realRoles c = objectRoles c
  /-- A new name rigid on the value side is rigid on the realizer side. -/
  realRigid : ∀ {c : DeclName}, c ∈ names → roles c = .rigid → realRoles c = .rigid
  /-- The realizer side's root steps at spines of other names are the object package's. -/
  realStepOld : ∀ {n : Nat} {c : DeclName} {args : List (Tower.Tm n)} {r : Tower.Tm n},
    c ∉ names → realRules.computation.step (appSpine (.const c) args) r →
      objectRules.computation.step (appSpine (.const c) args) r
  /-- The realizer side's package contains the object package. -/
  realSub : RulesSub objectRules realRules
  /-- The realizer side's universes and their laws are the object package's. -/
  realHeadTyping : ∀ {h u : Tower.Head}, realRules.headTyping h u → objectRules.headTyping h u
  realIsUniverse : ∀ {u : Tower.Head}, realRules.isUniverse u → objectRules.isUniverse u
  realJoin : ∀ {u v w : Tower.Head}, realRules.join u v w → objectRules.join u v w
  realCumulative : ∀ {u v : Tower.Head}, realRules.cumulative u v → objectRules.cumulative u v
  realHeadEq : ∀ {h h' : Tower.Head}, realRules.headEq h h' → objectRules.headEq h h'
  /-- The universe levels of the realizer side's package. -/
  realLevels : LevelModel realRules ℕ
  /-- A name the extension does not add has, on the realizer side, its declared type in the
  object package. -/
  realDeclaredOld : ∀ {c : DeclName} {T : Tower.Tm 0}, c ∉ names →
    realRules.constantType c = some T → objectRules.constantType c = some T
  /-- **A new constructor builds a new inductive type**: it is declared at the function type of
  its fields ending at a new name, an inductive type of the realizer side. -/
  realNewCtor : ∀ {c : DeclName} {a : Nat}, c ∈ names → realRoles c = .constructor a →
    ∃ (I : DeclName) (fs : List (Normalization.Field Tower.Head)),
      realRules.constantType c = some (ctorType I fs) ∧ fs.length = a ∧ I ∈ names ∧
        ∃ cs, realRoles I = .inductive cs
  /-- **A new inductive type is declared in a universe** of the object package. -/
  realNewInductive : ∀ {c : DeclName}
    {cs : List (DeclName × List (Normalization.Field Tower.Head))}, c ∈ names →
      realRoles c = .inductive cs →
        ∃ u, objectRules.isUniverse u ∧ realRules.constantType c = some (.head u)

namespace TExtension

variable (X : TExtension)

/-- The realizer side of an extension. -/
def realizers : Realizability.Realizers Tower.Head where
  rules := X.realRules
  roles := X.realRoles
  decoders := programCodes.decoders
  zero := zeroN
  suc := sucN
  shape := X.realShape
  reflects := X.realReflects
  decoderRoles := X.realDecoderRoles
  numerals := X.realNumerals
  decodes := X.realDecodes

/-- The value side's computations of an extension: its own, then the transport value model's
read with its roles. -/
abbrev comps (v : Nat → Nat) : List (DeclName × RootComputation Tower.Head) :=
  X.extra ++ tmodelComputationsAt X.roles v

/-- **The model of an extension**: the value side over the tower with the extension's roles and
computations, the daimon, and the extension's realizer side. -/
def model (v : Nat → Nat) : ModelSN.SNModel Tower.Head Nat where
  toModel := tmodelOf v X.roles (X.comps v)
  star := starN
  realizers := X.realizers

variable (v : Nat → Nat)

/-- A computation of the transport value model, read with the extension's roles, is a step of
the model of the extension. -/
theorem step {entry : DeclName × RootComputation Tower.Head}
    (mem : entry ∈ tmodelComputationsAt X.roles v) {n : Nat} {l r : Tower.Tm n}
    (h : entry.2.step l r) : (X.model v).rules.computation.step l r :=
  tmodelOf_step (List.mem_append_right _ mem) h

/-- A computation of the extension is a step of its model. -/
theorem extraStep {entry : DeclName × RootComputation Tower.Head} (mem : entry ∈ X.extra)
    {n : Nat} {l r : Tower.Tm n} (h : entry.2.step l r) :
    (X.model v).rules.computation.step l r :=
  tmodelOf_step (List.mem_append_left _ mem) h

/-- No new name heads a computation of the transport value model. -/
theorem names_disjoint : ∀ c ∈ X.extra.map Prod.fst,
    c ∉ (tmodelComputationsAt X.roles v).map Prod.fst := by
  intro c hc hc'
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨entry', mem', e⟩ := List.mem_map.mp hc'
  obtain ⟨declared, notCoe, -, -, -⟩ := X.extends_.fresh entry.1 (X.extraNames entry mem)
  rcases tmodelComputationsAt_known X.roles v entry' mem' with h | h
  · rw [e] at h
    exact h declared
  · rw [e] at h
    exact notCoe h

/-- **The model of an extension is root-shaped and deterministic.** -/
theorem shape : RootShape (X.model v).rules X.roles :=
  tmodelShapeOf
    (fun entry mem => (List.mem_append.mp mem).elim (X.extraSpine entry)
      (tmodelComputationsAt_spine X.extends_ X.declared v entry))
    (fun entry mem => (List.mem_append.mp mem).elim (X.extraHeaded entry)
      (tmodelComputationsAt_headed X.roles v entry))
    (fun entry mem => (List.mem_append.mp mem).elim (X.extraDeterministic entry)
      (tmodelComputationsAt_deterministic X.declared v X.extends_.num entry))
    (by
      rw [List.map_append]
      exact List.nodup_append.mpr ⟨X.extraDistinct, tmodelComputationsAt_distinct X.roles v,
        fun a ha b hb e => X.names_disjoint v a ha (e ▸ hb)⟩)

/-- **The laws of the model of an extension**: those of a consistency model over the tower, the
daimon rigid, and the constructors declared. -/
theorem laws : (X.model v).Laws where
  values := tmodelOf_laws v X.extends_ (X.shape v)
  star := X.extends_.star
  starNotProp := by change starN ≠ propN; decide
  starNotHolds := by change starN ≠ holdsN; decide
  declared := X.declared

/-- The laws of the value side of the model of an extension. -/
theorem valueLaws : (X.model v).value.Laws :=
  (X.laws v).value

/-- **The transport table holds in the model of an extension**, at every type constant its
roles declare. -/
theorem coeRules : ValueSide.CoeRules (X.model v).value coeN :=
  (tmodelOf_coeTable v X.extends_ (fun _ mem => List.mem_append_right _ mem)).coeRules
    (V := (X.model v).value) (X.valueLaws v)

/-- The numbers of the realizer side are the constructors `zero` and `suc`. -/
theorem realRoles_num :
    X.realizers.roles numN =
      .inductive [(X.realizers.zero, []), (X.realizers.suc, [.recursive])] :=
  (X.realOld fun h => absurd (X.extends_.fresh numN h).1 (by decide)).trans objectRoles_num

/-- **The model reads codes by the candidate reading**: the reading of the algebra of Kripke
candidates is the candidate reading of the realizer side, since the numerals of the two sides
agree. -/
theorem reading_eq :
    (X.model v).reading =
      Realizability.candidateReading (X.model v).toSetting starN X.realizers :=
  ModelSN.kcandReading_eq X.realizers (X.model v).toSetting starN numN rfl rfl X.realRoles_num

/-- A name the object package declares, a code instance, a constant of the transport or the
daimon is no new name. -/
theorem not_new {c : DeclName}
    (known : objectRules.constantType c ≠ none ∨ c ∈ coeNameList ∨ c = starN ∨
      SetProfile.allInstance? c ≠ none ∨ SetProfile.eqInstance? c ≠ none) : c ∉ X.names := by
  intro mem
  obtain ⟨declared, notCoe, notStar, notAll, notEq⟩ := X.extends_.fresh c mem
  rcases known with h | h | h | h | h
  · exact h declared
  · exact notCoe h
  · exact notStar h
  · exact h notAll
  · exact h notEq

/-- A name the object package declares keeps its role on the realizer side. -/
theorem realRoles_declared {c : DeclName} (declared : objectRules.constantType c ≠ none) :
    X.realRoles c = objectRoles c :=
  X.realOld (X.not_new (.inl declared))

/-- A root step of the realizer side at a spine of a name the object package declares is a
root step of the object package. -/
theorem realStep_declared {c : DeclName} (declared : objectRules.constantType c ≠ none)
    {n : Nat} {args : List (Tower.Tm n)} {r : Tower.Tm n}
    (step : X.realRules.computation.step (appSpine (.const c) args) r) :
    objectRules.computation.step (appSpine (.const c) args) r :=
  X.realStepOld (X.not_new (.inl declared)) step

theorem realRoles_zero : X.realRoles zeroN = .constructor 0 :=
  (X.realRoles_declared (by decide)).trans objectRoles_zero
theorem realRoles_suc : X.realRoles sucN = .constructor 1 :=
  (X.realRoles_declared (by decide)).trans objectRoles_suc
theorem realRoles_add : X.realRoles addN = .computes 2 (.split 1 .constructor fun _ => .leaf) :=
  (X.realRoles_declared (by decide)).trans objectRoles_add
theorem realRoles_pow : X.realRoles powN = .computes 2 (.split 0 .constructor fun _ => .leaf) :=
  (X.realRoles_declared (by decide)).trans objectRoles_pow
theorem realRoles_numRec :
    X.realRoles numRecName = .computes 4 (.split 3 .constructor fun _ => .leaf) :=
  (X.realRoles_declared (by decide)).trans (objectRoles_of_roles roles_numRec nofun)
theorem realRoles_j : X.realRoles jName = .computes 6 (.split 5 .constructor fun _ => .leaf) :=
  (X.realRoles_declared (by decide)).trans
    ((objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_j)
theorem realRoles_iter :
    X.realRoles iterName = .computes 6 (.split 0 .constructor fun _ => .leaf) :=
  (X.realRoles_declared (by decide)).trans (objectRoles_of_roles roles_iter nofun)
theorem realRoles_eqAt : X.realRoles eqAtName = .computes 1 .leaf :=
  (X.realRoles_declared (by decide)).trans objectRoles_eqAt
theorem realRoles_sucMove : X.realRoles sucMoveName = .computes 2 .leaf :=
  (X.realRoles_declared (by decide)).trans objectRoles_sucMove
theorem realRoles_keep : X.realRoles keepName = .computes 4 .leaf :=
  (X.realRoles_declared (by decide)).trans objectRoles_keep
theorem realRoles_transport : X.realRoles transportName = .computes 6 .leaf :=
  (X.realRoles_declared (by decide)).trans objectRoles_transport
theorem realRoles_compose : X.realRoles composeName = .computes 6 .leaf :=
  (X.realRoles_declared (by decide)).trans objectRoles_compose
theorem realRoles_returnIter : X.realRoles returnIterName = .computes 1 .leaf :=
  (X.realRoles_declared (by decide)).trans objectRoles_returnIter
theorem realRoles_sucStep : X.realRoles sucStepName = .computes 2 .leaf :=
  (X.realRoles_declared (by decide)).trans objectRoles_sucStep

/-- A constant that does not compute on the realizer side is strongly normalizing there. -/
theorem const_sn {c : DeclName}
    (stuck : ∀ arity scrutinee, X.realRoles c ≠ .computes arity scrutinee) {n : Nat} :
    SN X.realRules (.const c : Tower.Tm n) :=
  SN.constSpine X.realShape (args := []) (fun a s role => absurd role (stuck a s)) (by simp)

/-- A rigid constant of the value side other than the decoder is rigid on the realizer
side. -/
theorem realRoles_rigid {T : DeclName} (role : X.roles T = .rigid) (notHolds : T ≠ holdsN) :
    X.realRoles T = .rigid := by
  by_cases new : T ∈ X.names
  · exact X.realRigid new role
  · rw [X.realOld new]
    rw [X.extends_.old new] at role
    exact objectRoles_of_tmodelRoles role notHolds

end TExtension

/-! ## The transport value model as an extension -/

/-- **The transport value model is the extension by no name**: the object package on the
realizer side. -/
def objectTExt : TExtension where
  names := []
  roles := tmodelRoles
  extra := []
  realRules := objectRules
  realRoles := objectRoles
  realShape := objectShape
  realReflects := objectReflects
  realDecoderRoles := objectDecoderRoles
  realNumerals := objectNumerals
  realDeclared := objectConstructorsDeclared
  realDecodes := objectDecodes
  extends_ := tmodelRoles_extends
  declared := tmodelConstructorsDeclared
  extraNames := fun _ h => nomatch h
  extraSpine := fun _ h => nomatch h
  extraHeaded := fun _ h => nomatch h
  extraDeterministic := fun _ h => nomatch h
  extraDistinct := List.nodup_nil
  realOld := fun _ => rfl
  realRigid := fun h => nomatch h
  realStepOld := fun _ step => step
  realSub := RulesSub.refl objectRules
  realHeadTyping := id
  realIsUniverse := id
  realJoin := id
  realCumulative := id
  realHeadEq := id
  realLevels := ConvRules.objectLevels
  realDeclaredOld := fun _ declared => declared
  realNewCtor := fun h => nomatch h
  realNewInductive := fun h => nomatch h

/-- The model of the extension by no name is the transport value model. -/
theorem objectTExt_model (v : Nat → Nat) : objectTExt.model v = vmodel v :=
  rfl

variable (v : Nat → Nat)

/-- **The laws of the model**: those of route T's consistency model, the daimon
rigid, and the constructors of the numbers declared as constructors. -/
theorem vmodel_laws : (vmodel v).Laws :=
  objectTExt.laws v

/-- The laws of the model's value side. -/
theorem vmodel_valueLaws : (vmodel v).value.Laws :=
  (vmodel_laws v).value

theorem vmodel_rules : (vmodel v).rules = (tmodelC v).rules := rfl
theorem vmodel_roles : (vmodel v).roles = (tmodelC v).roles := rfl
theorem vmodel_level : (vmodel v).levels.level = (tmodelC v).levels.level := rfl

/-- **The transport table holds in the model**: route T's consistency model has
the transport table (`tmodel_coeTable`). -/
theorem vmodel_coeRules : ValueSide.CoeRules (vmodel v).value coeN :=
  objectTExt.coeRules v

/-- The numbers of the realizer side are the constructors `zero` and `suc`. -/
theorem objectRoles_num_ctors :
    objectRealizers.roles numN =
      .inductive [(objectRealizers.zero, []), (objectRealizers.suc, [.recursive])] :=
  objectRoles_num

/-- **The model reads codes by the candidate reading**: the reading of the
algebra of Kripke candidates is the candidate reading of the object package,
since the numerals of the value side and of the realizer side agree. -/
theorem vmodel_reading_eq :
    (vmodel v).reading =
      Realizability.candidateReading (tmodelC v).toSetting starN objectRealizers :=
  objectTExt.reading_eq v

/-! ## The program's codes -/

namespace TExtension

variable (X : TExtension) (v : Nat → Nat)

/-- The carrier of every simple type is interpreted by the model of an extension. -/
theorem carrierOf_interpretable :
    ∀ type : HOL.Ty SetProfile.SetBase, (carrierOf type).2.Interpretable (X.model v).toModel
  | .prop => .prop
  | .base .num => .num
  | .base .set =>
      .rigid X.extends_.setRigid (by change setN ≠ propN; decide)
        (by change setN ≠ holdsN; decide)
  | .arr a b => .arr (carrierOf_interpretable a) (carrierOf_interpretable b)

/-- The carrier of a simple type, as a type of the package, is the profile's
type. -/
theorem carrierOf_term :
    ∀ type : HOL.Ty SetProfile.SetBase, (carrierOf type).2.term (X.model v).toModel = typeTerm type
  | .prop => rfl
  | .base .num => rfl
  | .base .set => rfl
  | .arr a b => by
      have ha := carrierOf_term a
      have hb := carrierOf_term b
      simp only [carrierOf, Consistency.Carrier.term, typeTerm,
        Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface.typeAt]
        at ha hb ⊢
      rw [ha, hb,
        Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface.typeAt_rename]

/-- The program's codes are read by the model of an extension. -/
theorem programCodes_read : CodesRead (X.model v).toModel programCodes where
  proofs := .sort _
  prop := rfl
  holds := rfl
  imp := rfl
  all := by
    intro a T found
    change (SetProfile.allInstance? a).map typeTerm = some T at found
    cases found' : SetProfile.allInstance? a with
    | none => rw [found'] at found; cases found
    | some type =>
        rw [found'] at found
        cases found
        refine ⟨(carrierOf type).1, (carrierOf type).2, ?_, X.carrierOf_interpretable v type,
          (X.carrierOf_term v type).symm⟩
        change (SetProfile.allInstance? a).map carrierOf = _
        rw [found']
        rfl
  eq := by
    intro e T found
    change (SetProfile.eqInstance? e).map typeTerm = some T at found
    cases found' : SetProfile.eqInstance? e with
    | none => rw [found'] at found; cases found
    | some type =>
        rw [found'] at found
        cases found
        refine ⟨(carrierOf type).1, (carrierOf type).2, ?_, X.carrierOf_interpretable v type,
          (X.carrierOf_term v type).symm⟩
        change (SetProfile.eqInstance? e).map carrierOf = _
        rw [found']
        rfl

/-- The closed type of every carrier interpretable by the model of an extension is strongly
normalizing on its realizer side. -/
theorem carrier_sn : ∀ {k : Kind} {C : Carrier k},
    C.Interpretable (X.model v).toModel → SN X.realRules (C.term (X.model v).toModel)
  | _, _, .prop => X.const_sn fun _ _ role => by
      change X.realRoles propN = _ at role
      rw [X.realRoles_declared (c := propN) (by decide), objectRoles_prop] at role
      cases role
  | _, _, .num => X.const_sn fun _ _ role => by
      change X.realRoles numN = _ at role
      rw [X.realRoles_declared (c := numN) (by decide), objectRoles_num] at role
      cases role
  | _, _, .rigid role _ notHolds => X.const_sn fun _ _ role' => by
      rw [X.realRoles_rigid role notHolds] at role'
      cases role'
  | _, _, .arr dom cod =>
      SN.pi (RootShape.spineHeaded X.realShape) (carrier_sn dom)
        (SN.rename X.realReflects wk (carrier_sn cod))

/-- The program's codes are read by the model of an extension. -/
theorem programCodes_readS : ModelSN.CodesReadS (X.model v) programCodes where
  read := X.programCodes_read v
  decoders := rfl
  propStuck := fun arity scrutinee role => by
    change X.realRoles propN = _ at role
    rw [X.realRoles_declared (c := propN) (by decide), objectRoles_prop] at role
    cases role
  carrierSN := fun hC => X.carrier_sn v hC

/-- The decoders of the program's codes are the codes of the model of an extension. -/
theorem programDecodes : Consistency.Decodes (X.model v).toModel programCodes.decoders :=
  (X.programCodes_read v).decodes

/-! ## Stages without identity elimination -/

/-- **A root step of a stage without identity elimination is a step of the
model's reduction**: the computations of the package other than identity
elimination are computations of the model of every extension. -/
theorem step_of_stage {allowed : DeclName → Bool} (noJ : allowed jName = false)
    {n : Nat} {l r : Tower.Tm n} (step : (stage allowed).computation.step l r) :
    (X.model v).rules.computation.step l r := by
  change (RootComputation.unionAll (computations.filter fun entry => allowed entry.1)).step l r
    at step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  obtain ⟨listedIn, allowedIn⟩ := List.mem_filter.mp mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listedIn
  rcases listedIn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact X.step v (tmodelListedAt X.roles v 0 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 1 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 2 (by decide)) h
  · rw [noJ] at allowedIn
    cases allowedIn
  · exact X.step v (tmodelListedAt X.roles v 4 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 5 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 6 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 7 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 8 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 9 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 10 (by decide)) h
  · exact X.step v (tmodelListedAt X.roles v 11 (by decide)) h

/-- **A stage without identity elimination whose constants are valid is sound
for the model of an extension**: its root steps are steps of the model's reduction. -/
theorem stage_soundS {allowed : DeclName → Bool} (noJ : allowed jName = false)
    (constants : ∀ {name : DeclName} {type : Tower.Tm 0}, allowed name = true →
      allTypes name = some type → ModelSN.ValidTmS (X.model v) .nil (.const name) type) :
    ModelSN.TypedSoundS (stage allowed) (X.model v) where
  laws := X.laws v
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  root := fun step => .inl (ModelSN.ModelRootS.semantic (X.laws v) (X.programDecodes v)
    (.inl (X.step_of_stage v noJ step)))
  constants := by
    intro name type declared
    change (if allowed name then allTypes name else none) = some type at declared
    split_ifs at declared with h
    exact constants h declared

/-- A stage of the listed names, without identity elimination, whose constants
are valid is sound for the model of an extension. -/
theorem stage_soundS_of {names : List DeclName} (noJ : jName ∉ names)
    (constants : ∀ name ∈ names, ∀ {type : Tower.Tm 0}, allTypes name = some type →
      ModelSN.ValidTmS (X.model v) .nil (.const name) type) :
    ModelSN.TypedSoundS (stage (allowedIn names)) (X.model v) :=
  X.stage_soundS v (by simpa [allowedIn] using noJ) fun {name _} allowed declared =>
    constants name (by simpa [allowedIn] using allowed) declared

end TExtension

/-- The decoders of the program's codes are the codes of the model. -/
theorem vprogramDecodes : Consistency.Decodes (vmodel v).toModel programCodes.decoders :=
  objectTExt.programDecodes v

/-! ## The numbers -/

namespace TExtension

variable (X : TExtension) (v : Nat → Nat)

/-- The type of the numbers does not compute on the realizer side. -/
theorem numT_sn {n : Nat} : SN X.realRules (numT : Tower.Tm n) :=
  X.const_sn fun _ _ role => by
    change X.realRoles numN = _ at role
    rw [X.realRoles_declared (c := numN) (by decide), objectRoles_num] at role
    cases role

/-- **The numbers are a valid term of `U0`**: the clause of a simple inductive type
(`ModelSN.ValidTmS.inductiveType`), which has no closed field. -/
theorem valid_num : ModelSN.ValidTmS (X.model v) .nil (.const numN) U0 :=
  ModelSN.ValidTmS.inductiveType (X.laws v) X.extends_.num X.realRoles_num
    (LevelTower.IsUniverse.sort _) (fun {m} _ _ => ValueSide.Pack.total (X.model v).value m)
    fun _ => by
      intro F hF
      rw [show ValueSide.closedFields ctors = ([] : List (Tower.Tm 0)) from rfl] at hF
      cases hF

end TExtension

/-! ## The linear rule of identity elimination

The obstruction: the object package's identity elimination at a path whose
endpoints the linear rule does not compare. -/

/-- The motive `λ y _. y`: the endpoint itself, as a type. -/
abbrev endpointMotive {n : Nat} : Tower.Tm n := .lam (.lam (.var 1))

/-- Identity elimination with the motive `λ y _. y` from the point `U1` along
`refl U0` to the endpoint `U0`, with the method `num`. The linear rule of the
object package fires at it, while `refl U0` is no path from `U1`. -/
def mismatchJ {n : Nat} : Tower.Tm n :=
  appSpine (.const jName)
    [sortTm (.succ (.succ Tower.zero)), U1, endpointMotive, numT, U0, .refl U0]

theorem subst_mismatchJ {n m : Nat} (σ : Sub Tower.Head n m) :
    Presentation.subst σ (mismatchJ : Tower.Tm n) = mismatchJ :=
  rfl

theorem rename_mismatchJ {n m : Nat} (ρ : Ren n m) :
    Presentation.rename ρ (mismatchJ : Tower.Tm n) = mismatchJ :=
  rfl

/-- **The object package computes `mismatchJ` to its method** by the linear rule
of identity elimination. -/
theorem objectStep_mismatchJ {n : Nat} :
    objectRules.computation.step (mismatchJ : Tower.Tm n) numT :=
  .inl (rules_step (listed 3 (by decide)) ⟨_, _, _, _, _, _, rfl, rfl⟩)

/-- The motive `λ y _. y` at a type and any path computes the type. -/
theorem endpointMotive_red {n : Nat} (y e : Tower.Tm n) (u : Tower.Head) (hy : y = .head u) :
    WhRed (vmodel v).rules (vmodel v).roles (.app (.app endpointMotive y) e) (.head u) := by
  subst hy
  exact .head (.appFun (.beta _ _)) (.single (.beta _ _))

/-- **On the value side `mismatchJ` is stuck on the daimon**: identity
elimination transports `num` from the motive at the point, `U1`, into the motive
at the endpoint, `U0`, and a transport into a universe from a universe of a
higher level is stuck on the daimon. -/
theorem vmodel_mismatchJ_red {n : Nat} :
    ∃ w, WhRed (vmodel v).rules (vmodel v).roles (mismatchJ : Tower.Tm n) w ∧
      Daimonic (vmodel v).roles (vmodel v).star w := by
  have rY := endpointMotive_red (v := v) (U0 : Tower.Tm n) (.refl U0) (.sort (.const 0)) rfl
  have rX :=
    endpointMotive_red (v := v) (U1 : Tower.Tm n) (.refl U1) (.sort (.succ Tower.zero)) rfl
  obtain ⟨w, rw, dw⟩ := (vmodel_coeRules v).univOther (d := numT) rY (LevelTower.IsUniverse.sort _)
    rX (.inl ⟨_, rfl, LevelTower.IsUniverse.sort _⟩)
    (fun u' e _ => by
      cases e
      exact Nat.zero_lt_one)
  exact ⟨w, .head (tmodel_j_step v _ _ _ _ _ _) rw, dw⟩

/-- The object term `mismatchJ` is strongly normalizing: its arguments are, and
it computes only at reflexivity, to its method. -/
theorem mismatchJ_sn {n : Nat} : SN objectRules (mismatchJ : Tower.Tm n) := by
  have spine := RootShape.spineHeaded objectShape
  have role : objectRoles jName = .computes 6 (.split 5 .constructor fun _ => .leaf) :=
    (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_j
  exact KCand.eliminator_mem objectShape objectReflects (KCand.sn' objectReflects) role
    objectStep_j (Q := True) (SN.head spine _) (SN.head spine _)
    (SN.lam spine (SN.lam spine (SN.var spine _))) objectTExt.numT_sn (SN.head spine _)
    ⟨SN.refl spine (SN.head spine _), fun _ _ => trivial⟩ (fun _ => objectTExt.numT_sn)

/-- `mismatchJ` is a type of every level, by the pack of daimonic types. -/
theorem vmodel_mismatchJ_interp (l : Nat) {n : Nat} (ξ : World (vmodel v).reading n) :
    ValueSide.InterpAt (vmodel v).value l ξ mismatchJ (ValueSide.Pack.total (vmodel v).value n) ∧
      ValueSide.Shape (vmodel v).value (ValueSide.InterpAt (vmodel v).value l) .pair ξ
        mismatchJ mismatchJ := by
  obtain ⟨w, red, daimonic⟩ := vmodel_mismatchJ_red (v := v) (n := n)
  have interp : ValueSide.InterpAt (vmodel v).value l ξ mismatchJ
      (ValueSide.Pack.total (vmodel v).value n) :=
    ValueSide.SInterp.daimon red daimonic
  have total := ValueSide.Shape.of_daimonic (vmodel_valueLaws v) interp red daimonic
  exact ⟨interp, .total total total⟩

/-- **`mismatchJ` is a valid term of `U0`**: at every world it is a daimonic
type, of one shape with itself, and its object term is strongly normalizing. -/
theorem vmodel_mismatchJ_valid : ModelSN.ValidTmS (vmodel v) .nil mismatchJ U0 := by
  refine ⟨ModelSN.ValidTyS.sort (LevelTower.IsUniverse.sort _), fun {_ _ ξ σ σ' ς} _ {P} den => ?_⟩
  rw [ModelSN.DenS.sort_inv (vmodel_laws v) (LevelTower.IsUniverse.sort _) den]
  rw [subst_mismatchJ, subst_mismatchJ, subst_mismatchJ]
  refine ⟨fun {_ ξ' ρ} _ => ?_, mismatchJ_sn⟩
  rw [rename_mismatchJ]
  obtain ⟨interp, shape⟩ := vmodel_mismatchJ_interp (v := v) _ ξ'
  exact ⟨_, interp, interp, shape⟩

/-- **`mismatchJ` and its method are not validly equal at `U0`**: in the closed
world the universe relates them only if they have one pack, while `mismatchJ`
has the pack of daimonic types and the numbers have their inductive pack, which
does not relate `zero` to `suc zero`. -/
theorem vmodel_mismatchJ_not_equal : ¬ ModelSN.ValidEqS (vmodel v) .nil mismatchJ numT U0 := by
  intro equal
  have laws := vmodel_valueLaws v
  let empty : Sub Tower.Head 0 0 := fun i => Fin.elim0 i
  have den : ValueSide.DenS (vmodel v).value World.closed (Presentation.subst empty U0)
      (ModelSN.universeAt (vmodel v) 0 World.closed) :=
    ValueSide.DenS.sort (V := (vmodel v).value) (LevelTower.IsUniverse.sort _) World.closed
  obtain ⟨Q, hl, hr, -⟩ :=
    equal.2.2 (σ := empty) (σ' := empty) (ς := empty) trivial den (Morph.id World.closed)
  change ValueSide.InterpAt (vmodel v).value 0 World.closed mismatchJ Q at hl
  change ValueSide.InterpAt (vmodel v).value 0 World.closed numT Q at hr
  obtain rfl := hl.deterministic laws (vmodel_mismatchJ_interp (v := v) 0 World.closed).1
  have num := hr.deterministic laws (ValueSide.InterpAt.num laws 0 .refl)
  have related₀ : (ValueSide.numIndPack (vmodel v).value 0).rel (.const zeroN)
      (.app (.const sucN) (.const zeroN)) := by
    rw [← num]
    trivial
  obtain ⟨s, hz, hs⟩ := ValueSide.numIndPack_rel.mp related₀
  have zero := Realizability.HasShape.deterministic laws.values.truth laws.star hz (.zero .refl)
  have suc := Realizability.HasShape.deterministic laws.values.truth laws.star hs
    (.suc .refl (.zero .refl))
  rw [zero] at suc
  cases suc

/-- **The root obligation of the linear rule of identity elimination fails in
the model**: at `mismatchJ` both sides of the object package's step are valid
terms of `U0`, and they are not validly equal. -/
theorem vmodel_jRoot_not_semantic :
    ¬ ModelSN.RootSemanticS (vmodel v) (mismatchJ : Tower.Tm 0) numT :=
  fun semantic => vmodel_mismatchJ_not_equal v
    (semantic (vmodel_mismatchJ_valid v) (objectTExt.valid_num v))

/-- **The object package is not sound for the model**: the linear rule of
identity elimination is one of its root steps, and its root obligation fails at
`mismatchJ`. -/
theorem objectRules_not_soundS_vmodel : ¬ ModelSN.SoundS objectRules (vmodel v) :=
  fun sound => vmodel_jRoot_not_semantic v (sound.2 objectStep_mismatchJ)

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
