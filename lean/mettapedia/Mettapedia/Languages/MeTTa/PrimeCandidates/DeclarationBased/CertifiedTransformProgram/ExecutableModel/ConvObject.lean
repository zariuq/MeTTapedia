import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencySound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelPackage
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.CodeConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Inversion

/-!
# The object package in the conversion model

The object package, the executable package with the program's codes, is a
realizer side of the conversion model at every lawful generic equality that
respects typed weak-head reduction, given facts about the weak-head forms of its
types (`objectSideAt`). The facts are an input: they are the declarative facts
of the object package, which the conversion model does not prove itself.

The side is over the executable package (`objectSideAt_over`): the object package
contains it, and its roles keep the roles of the numbers and of the constants
with computation. So every constant of the executable package is valid in the
model over it by the executable package's own proofs.

**The codes.** The model reads the program's codes (`objectCodesRead`):

* the value side reads them as the transport value model does;
* the realizer side declares them at their types (`objectRules_code_typed`), gives
  the decoder and the code constructors their roles, and keeps the type of
  codes rigid;
* the decoder is a congruence of the generic equality: an input of the side,
  which typed equality has (`objectDeclarative_holdsCongruence`);
* a typed constructor spine at the type of codes is a code constructor applied
  to its arguments, and it decodes to a typed weak-head form of a type
  (`objectRules_decodes`). The proof inverts the typing with the facts: a
  spine of implication, of a quantifier or of an equation has its arguments at
  the declared domains, and the numbers' constructors are no codes, since the
  type of the numbers is equal to no type of codes.

The declared types of the codes are typed in a package with the type of codes,
the numbers and the sets and no computation (`typeStage`), sound for the model
by the validity of those three constants (`typeStage_typedSoundN`); the
fundamental lemma of that package makes them valid types.

**Soundness.** The object package is sound for its conversion model, its root
steps read with their typing (`objectRules_typedSoundN`): the executable package's
root steps as in each stage, identity elimination at its typed instances, and a
decoding of a code as a step of the value side's decoding and of the realizer
side's computation. It holds at typed equality with only the facts as input
(`objectRules_typedSoundN_declarative`). So derivably equal terms of a formed
context are related by the generic equality, derivably equal types too, and a
typed term is related to itself by the candidate of its value
(`object_equal_escapeN`, `object_typeEq_escapeN`, `object_typed_shapeN`): a closed
term of the numbers reaches `zero`, `suc` of a term of a smaller shape, or a
neutral term (`object_closed_num_shape`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization hiding World
open Presentation.TypedEquality.Impredicative
open Presentation.TypedEquality.Impredicative.Conversion
open Presentation.TypedEquality.Impredicative.Consistency (World Morph CodesRead)
open Presentation.TypedEquality.Impredicative.Realizability (HasShape)
open TelescopeAbstraction (closeType applyClosed liftClosed_zero)
open StrongNormalization (NumShape)
open Package (U0 U1 numT jName)
open Mettapedia.Logic

namespace CodeModel
namespace ConvRules

/-! ## The object package as a realizer side -/

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

/-- The normalization setting of the object package at a generic equality. -/
def objectSettingAt (E : GenericEquality Tower.Head) : Setting Tower.Head ℕ where
  R := objectRules
  roles := objectRoles
  E := E
  levels := objectLevels
  shape := objectShape
  constructors := objectConstructorsDeclared

/-- **The object package as a realizer side** at a lawful generic equality that
respects typed weak-head reduction, with facts about the weak-head forms of its
types. -/
def objectSideAt (facts : FormFacts objectRules objectRoles) (E : GenericEquality Tower.Head)
    (lawsE : E.Laws objectRules objectRoles) (reduceE : RespectsReduction objectRules objectRoles E) :
    RealizerSide Tower.Head ℕ where
  toSetting := objectSettingAt E
  laws := lawsE
  reduce := reduceE
  facts := facts

/-- The names declared by the executable package are no codes. -/
theorem codeType_of_rules {name : DeclName} {type : Tower.Tm 0}
    (declared : rules.constantType name = some type) : programCodes.codeType name = none := by
  have mem := mem_of_lookup (show allTypes name = some type from declared)
  simp only [declarations, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

/-- **The object package contains the executable package.** -/
theorem rules_sub_objectRules : RulesSub rules objectRules where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun {name type} declared => by
    change (programCodes.codeType name).orElse (fun _ => rules.constantType name) = some type
    rw [codeType_of_rules declared]
    exact declared
  computation := fun step => .inl step

/-- The sets are rigid in the object package. -/
theorem objectRoles_set : objectRoles setN = .rigid :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_set

/-- The power set is rigid in the object package. -/
theorem objectRoles_power : objectRoles powerN = .rigid :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans roles_power

/-- The type of codes is rigid in the object package. -/
theorem objectRoles_prop : objectRoles propN = .rigid :=
  (objectRoles_of (by decide) (by decide) (by decide) (by decide)).trans
    (roles_of_not_mem (by decide))

section Side

variable (facts : FormFacts objectRules objectRoles) {E : GenericEquality Tower.Head}
  (lawsE : E.Laws objectRules objectRoles) (reduceE : RespectsReduction objectRules objectRoles E)

/-- **The object package is a realizer side over the executable package.** -/
theorem objectSideAt_over : OverRules (objectSideAt facts E lawsE reduceE) where
  sub := rules_sub_objectRules
  keep := fun declared nonrigid => objectRoles_of_roles declared nonrigid
  set := objectRoles_set
  power := objectRoles_power

end Side

/-! ## Typings of the declared types of the codes -/

section Typings

variable {R : Rules Tower.Head} (univ : RulesSub Presentation.Tower.rules R) {n : Nat} {Γ : Tower.Ctx n}
include univ

/-- A dependent function type of types of the lowest universe is a type of the
lowest universe. -/
theorem piU0 {A : Tower.Tm n} {B : Tower.Tm (n + 1)} (hA : Typed R Γ A U0)
    (hB : Typed R (.snoc Γ A) B U0) : Typed R Γ (.pi A B) U0 :=
  .cumul (.piForm hA (univ.isUniverse (.sort _)) hB (univ.isUniverse (.sort _))
    (univ.join (.sorts Tower.zero Tower.zero)))
    (univ.cumulative (fun _ => Nat.le_of_eq (Nat.max_self _)))

/-- A dependent function type of types of the next universe is a type of the next
universe. -/
theorem piU1 {A : Tower.Tm n} {B : Tower.Tm (n + 1)} (hA : Typed R Γ A U1)
    (hB : Typed R (.snoc Γ A) B U1) : Typed R Γ (.pi A B) U1 :=
  .cumul (.piForm hA (univ.isUniverse (.sort _)) hB (univ.isUniverse (.sort _))
    (univ.join (.sorts _ _)))
    (univ.cumulative (fun _ => Nat.le_of_eq (Nat.max_self _)))

/-- A type of the lowest universe is a type of the next one. -/
theorem raiseU {A : Tower.Tm n} (hA : Typed R Γ A U0) : Typed R Γ A U1 :=
  .cumul hA (univ.cumulative (fun _ => Nat.le_succ _))

/-- The lowest universe is a type of the next one. -/
theorem U0_typedU : Typed R Γ U0 U1 := .headType (univ.headTyping (.sort _))

/-- A constant declared at the lowest universe is a type of it. -/
theorem constU0 {c : DeclName} (declared : R.constantType c = some U0) :
    Typed R Γ (.const c) U0 :=
  .const declared (U0_typedU univ) (univ.isUniverse (.sort _))

/-- **A simple type of the profile is a type of the lowest universe**, in a
package declaring the type of codes, the numbers and the sets there. -/
theorem typeAt_typed (hprop : R.constantType propN = some U0)
    (hnum : R.constantType numN = some U0) (hset : R.constantType setN = some U0) :
    ∀ (type : HOL.Ty SetProfile.SetBase) {m : Nat} {Δ : Tower.Ctx m},
      Typed R Δ (FormationSensitiveHOLInterface.typeAt SetProfile.types m type) U0
  | .prop, _, _ => constU0 univ hprop
  | .base .set, _, _ => constU0 univ hset
  | .base .num, _, _ => constU0 univ hnum
  | .arr a b, _, _ => piU0 univ (typeAt_typed hprop hnum hset a)
      (typeAt_typed hprop hnum hset b)

omit univ in
/-- The carriers of the program's codes are simple types of the profile. -/
theorem programCodes_quantifiers {a : DeclName} {A : Tower.Tm 0}
    (carrier : programCodes.quantifiers a = some A) :
    ∃ type, SetProfile.allInstance? a = some type ∧ A = typeTerm type := by
  change (SetProfile.allInstance? a).map typeTerm = some A at carrier
  obtain ⟨type, found, rfl⟩ := Option.map_eq_some_iff.mp carrier
  exact ⟨type, found, rfl⟩

omit univ in
theorem programCodes_equations {e : DeclName} {A : Tower.Tm 0}
    (carrier : programCodes.equationCarrier e = some A) :
    ∃ type, SetProfile.eqInstance? e = some type ∧ A = typeTerm type := by
  change (if true = true then (SetProfile.eqInstance? e).map typeTerm else none) = some A
    at carrier
  rw [if_pos rfl] at carrier
  obtain ⟨type, found, rfl⟩ := Option.map_eq_some_iff.mp carrier
  exact ⟨type, found, rfl⟩

/-- **The declared types of the codes are types**, in a package declaring the
type of codes, the numbers and the sets at the lowest universe. -/
theorem codeType_typed (hprop : R.constantType propN = some U0)
    (hnum : R.constantType numN = some U0) (hset : R.constantType setN = some U0)
    {c : DeclName} {T : Tower.Tm 0} (declared : programCodes.codeType c = some T) :
    ∃ u, R.isUniverse u ∧ Typed R .nil T (.head u) := by
  have propT : ∀ {m : Nat} {Δ : Tower.Ctx m}, Typed R Δ (.const propN) U0 :=
    constU0 univ hprop
  unfold Codes.codeType at declared
  split_ifs at declared with hp hh hi
  · cases declared
    exact ⟨_, univ.isUniverse (.sort _), U0_typedU univ⟩
  · cases declared
    exact ⟨_, univ.isUniverse (.sort _), piU1 univ (raiseU univ propT) (U0_typedU univ)⟩
  · cases declared
    exact ⟨_, univ.isUniverse (.sort _), piU0 univ propT (piU0 univ propT propT)⟩
  · split at declared
    · rename_i A carrier
      cases declared
      obtain ⟨type, -, rfl⟩ := programCodes_quantifiers carrier
      exact ⟨_, univ.isUniverse (.sort _),
        piU0 univ (piU0 univ (typeAt_typed univ hprop hnum hset type) propT) propT⟩
    · obtain ⟨A, carrier, rfl⟩ := Option.map_eq_some_iff.mp declared
      obtain ⟨type, -, rfl⟩ := programCodes_equations carrier
      refine ⟨_, univ.isUniverse (.sort _), piU0 univ (typeAt_typed univ hprop hnum hset type)
        (piU0 univ ?_ propT)⟩
      change Typed R _ (Presentation.rename wk (FormationSensitiveHOLInterface.typeAt
        SetProfile.types 0 type)) U0
      rw [FormationSensitiveHOLInterface.typeAt_rename]
      exact typeAt_typed univ hprop hnum hset type

end Typings

/-- The tower is contained in the object package. -/
theorem tower_sub_objectRules : RulesSub Presentation.Tower.rules objectRules where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => nomatch declared
  computation := fun step => step.elim

/-- **The object package declares each code constant at its type**, a type of a
universe of the package. -/
theorem objectRules_code_typed {c : DeclName} {T : Tower.Tm 0}
    (code : programCodes.codeType c = some T) : Typed objectRules .nil (.const c) T := by
  obtain ⟨u, hu, typedT⟩ := codeType_typed tower_sub_objectRules declared_prop declared_num rfl code
  have h : Typed objectRules .nil (.const c) (liftClosed T) :=
    .const (programCodes.extend_constantType_of_code rules code) typedT hu
  rwa [liftClosed_zero] at h

/-! ## Typed constructor spines at the type of codes -/

/-- A behaviour that is no constructor. -/
def Behaviour.NotConstructor : Behaviour → Prop
  | .constructor _ => False
  | _ => True

/-- A property of both branches of a conditional holds of the conditional. -/
theorem ite_property {α : Sort _} (P : α → Prop) {p : Prop} [Decidable p] {a b : α}
    (ha : P a) (hb : P b) : P (if p then a else b) := by
  by_cases h : p
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    exact hb

/-- The constructors of the executable package are the numbers'. -/
theorem roles_constructor {k : DeclName} {a : Nat} (role : roles k = .constructor a) :
    (k = zeroN ∧ a = 0) ∨ (k = sucN ∧ a = 1) := by
  by_cases hz : k = zeroN
  · subst hz
    exact .inl ⟨rfl, (Role.constructor.inj (roles_zero.symm.trans role)).symm⟩
  by_cases hs : k = sucN
  · subst hs
    exact .inr ⟨rfl, (Role.constructor.inj (roles_suc.symm.trans role)).symm⟩
  exfalso
  by_cases hn : k = numN
  · subst hn
    rw [roles_num] at role
    cases role
  change (if k = numN then .inductive ctors else (behaviour k).role) = _ at role
  rw [if_neg hn] at role
  have key : Behaviour.NotConstructor (behaviour k) := by
    unfold behaviour
    rw [if_neg hz, if_neg hs]
    repeat' apply ite_property Behaviour.NotConstructor
    all_goals trivial
  generalize behaviour k = b at role key
  cases b with
  | constructor => exact key
  | computes => cases role
  | rigid => cases role

/-- **The constructors of the object package**: implication, the quantifier and
equation instances, and the numbers' constructors, each at its arity. -/
theorem objectRoles_constructor {k : DeclName} {a : Nat} (role : objectRoles k = .constructor a) :
    (k = impN ∧ a = 2) ∨ (∃ type, SetProfile.allInstance? k = some type ∧ a = 1) ∨
      (∃ type, SetProfile.eqInstance? k = some type ∧ a = 2) ∨ (k = zeroN ∧ a = 0) ∨
        (k = sucN ∧ a = 1) := by
  by_cases hh : k = holdsN
  · subst hh
    rw [objectRoles_holds] at role
    cases role
  by_cases hi : k = impN
  · subst hi
    rw [objectRoles_imp] at role
    exact .inl ⟨rfl, (Role.constructor.inj role).symm⟩
  cases ha : SetProfile.allInstance? k with
  | some type =>
      rw [objectRoles_all ha] at role
      exact .inr (.inl ⟨type, rfl, (Role.constructor.inj role).symm⟩)
  | none =>
      cases he : SetProfile.eqInstance? k with
      | some type =>
          rw [objectRoles_eq he] at role
          exact .inr (.inr (.inl ⟨type, rfl, (Role.constructor.inj role).symm⟩))
      | none =>
          rw [objectRoles_of hh hi ha he] at role
          exact .inr (.inr (.inr (roles_constructor role)))

section Decoding

variable (facts : FormFacts objectRules objectRoles)

/-- The object package at typed equality, as a realizer side with the facts. -/
abbrev objectDeclarativeSide : RealizerSide Tower.Head ℕ :=
  objectSideAt facts (declarative objectRules) (declarative_laws objectRoles objectLevels)
    declarative_convTm_reduce

variable {n : Nat} {Δ : Tower.Ctx n}

include facts in
/-- The type of the numbers is below no type of codes: a chain from the numbers
ends in a type equal to the numbers, which is not the rigid type of codes. -/
theorem num_not_below_prop (formed : CtxFormed objectRules Δ)
    (le : TypeLe objectRules Δ numT (.const propN)) : False := by
  have numType : IsType objectRules Δ numT := ⟨_, LevelTower.IsUniverse.sort _, num_typedO⟩
  have e := RealizerSide.typeLe_inductive (T := objectDeclarativeSide facts) (I := numN) formed
    objectRoles_num le numType.refl
  have neutral : Neutral objectRoles (.const propN : Tower.Tm n) :=
    .rigid (args := []) objectRoles_prop
  exact ((facts.forms e formed (.inr (.inr (.inr (.inr (.inl neutral)))))
    (.inr (.inr (.inr (.inr (.inr ⟨numN, _, objectRoles_num, rfl⟩)))))).neutral_left
      neutral).ne_inductive objectRoles_num rfl

/-- The simple types of the profile, as types of a context. -/
theorem typeTerm_lift (type : HOL.Ty SetProfile.SetBase) :
    (liftClosed (typeTerm type) : Tower.Tm n) =
      FormationSensitiveHOLInterface.typeAt SetProfile.types n type :=
  FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ type

include facts in
/-- **A typed constructor spine at the type of codes decodes to a typed weak-head
form of a type**, by one root step: it is a spine of implication, of a
quantifier instance or of an equation instance, with its arguments at the
declared domains; the numbers' constructors have no typing at the type of
codes. -/
theorem objectRules_decodes (formed : CtxFormed objectRules Δ) {k : DeclName}
    {args : List (Tower.Tm n)} (typing : Typed objectRules Δ (appSpine (.const k) args) (.const propN))
    (role : objectRoles k = .constructor args.length) :
    ∃ D, objectRules.computation.step (.app (.const holdsN) (appSpine (.const k) args)) D ∧
      IsTypeForm objectRoles D ∧ Typed objectRules Δ D U0 := by
  have univ := tower_sub_objectRules
  have hu : objectRules.isUniverse (.sort Tower.zero) := LevelTower.IsUniverse.sort _
  have propT : ∀ {m : Nat} {Γ : Tower.Ctx m}, Typed objectRules Γ (.const propN) U0 :=
    prop_typedO
  have typeT : ∀ (type : HOL.Ty SetProfile.SetBase) {m : Nat} {Γ : Tower.Ctx m},
      Typed objectRules Γ (FormationSensitiveHOLInterface.typeAt SetProfile.types m type) U0 :=
    fun type => typeAt_typed univ declared_prop declared_num rfl type
  rcases objectRoles_constructor role with ⟨rfl, len⟩ | ⟨type, found, len⟩ |
    ⟨type, found, len⟩ | ⟨rfl, len⟩ | ⟨rfl, len⟩
  · -- Implication: both arguments are codes, and the decoding is a dependent
    -- function type of proof types.
    match args, len with
    | [p, q], _ =>
      obtain ⟨mor, -, -⟩ :=
        Typed.telescope_inv (S := objectSettingAt (declarative objectRules)) facts formed
          (.snoc (.snoc .nil (.const propN)) (.const propN)) (.const propN) declared_imp
          (σ := consSub q (consSub p fun i => Fin.elim0 i)) typing
      have tp : Typed objectRules Δ p (.const propN) := mor 1
      have tq : Typed objectRules Δ q (.const propN) := mor 0
      refine ⟨_, .inr (DecoderStep.imp p q), .inr (.inl ⟨_, _, rfl⟩), piU0 univ
        (.appElim holds_typedO tp) (.appElim holds_typedO (Typed.weaken tq))⟩
  · -- A quantifier: its argument is a family of codes over the carrier, and the
    -- decoding is a dependent function type over the carrier.
    obtain rfl := SetProfile.allInstance?_eq_some found
    match args, len with
    | [f], _ =>
      have carrier : programCodes.quantifiers (SetProfile.allName type) = some (typeTerm type) := by
        change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = _
        rw [found]
        rfl
      obtain ⟨mor, -, -⟩ :=
        Typed.telescope_inv (S := objectSettingAt (declarative objectRules)) facts formed
          (.snoc .nil (.pi (typeTerm type) (.const propN))) (.const propN) (declared_allName type)
          (σ := consSub f fun i => Fin.elim0 i) typing
      have tf : Typed objectRules Δ f
          (.pi (FormationSensitiveHOLInterface.typeAt SetProfile.types n type) (.const propN)) := by
        have h := mor 0
        simp only [Ctx.lookup_snoc_zero, subst_rename_wk, Presentation.subst,
          FormationSensitiveHOLInterface.typeAt_subst] at h
        exact h
      refine ⟨_, .inr (DecoderStep.all carrier f), .inr (.inl ⟨_, _, rfl⟩), ?_⟩
      rw [typeTerm_lift]
      exact piU0 univ (typeT type)
        (.appElim holds_typedO (.appElim (B := .const propN) (Typed.weaken tf) (.var 0)))
  · -- An equation: both arguments are points of the carrier, and the decoding is
    -- an identity type.
    obtain rfl := SetProfile.eqInstance?_eq_some found
    match args, len with
    | [x, y], _ =>
      have carrier : programCodes.decoders.eqCarrier (SetProfile.eqName type) =
          some (typeTerm type) := by
        change (if true = true then (SetProfile.eqInstance? (SetProfile.eqName type)).map typeTerm
          else none) = _
        rw [if_pos rfl, found]
        rfl
      obtain ⟨mor, -, -⟩ :=
        Typed.telescope_inv (S := objectSettingAt (declarative objectRules)) facts formed
          (.snoc (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
            (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))
          (.const propN) (declared_eqName type)
          (σ := consSub y (consSub x fun i => Fin.elim0 i)) typing
      have tx : Typed objectRules Δ x
          (FormationSensitiveHOLInterface.typeAt SetProfile.types n type) := by
        have h := mor 1
        change Typed objectRules Δ x (Presentation.subst (consSub y (consSub x fun i => Fin.elim0 i))
          (Presentation.rename wk (Presentation.rename wk
            (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type)))) at h
        rw [FormationSensitiveHOLInterface.typeAt_rename, FormationSensitiveHOLInterface.typeAt_rename,
          FormationSensitiveHOLInterface.typeAt_subst] at h
        exact h
      have ty : Typed objectRules Δ y
          (FormationSensitiveHOLInterface.typeAt SetProfile.types n type) := by
        have h := mor 0
        change Typed objectRules Δ y (Presentation.subst (consSub y (consSub x fun i => Fin.elim0 i))
          (Presentation.rename wk
            (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))) at h
        rw [FormationSensitiveHOLInterface.typeAt_rename,
          FormationSensitiveHOLInterface.typeAt_subst] at h
        exact h
      refine ⟨_, .inr (DecoderStep.eq carrier x y), .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))), ?_⟩
      rw [typeTerm_lift]
      exact .idForm (typeT type) hu tx ty
  · -- `zero` has the type of the numbers, which is below no type of codes.
    match args, len with
    | [], _ =>
      obtain ⟨-, -, le⟩ :=
        Typed.telescope_inv (S := objectSettingAt (declarative objectRules)) facts formed
          .nil numT declared_zero (σ := fun i => Fin.elim0 i) typing
      exact (num_not_below_prop facts formed le).elim
  · -- `suc` returns the numbers, which are below no type of codes.
    match args, len with
    | [a], _ =>
      obtain ⟨-, -, le⟩ :=
        Typed.telescope_inv (S := objectSettingAt (declarative objectRules)) facts formed
          (.snoc .nil numT) numT declared_suc (σ := consSub a fun i => Fin.elim0 i) typing
      exact (num_not_below_prop facts formed le).elim

end Decoding

/-! ## The package of the types of the codes -/

/-- **The package of the type of codes, the numbers and the sets**, with the
universes of the executable package and no computation: it types the declared
types of the codes. -/
def typeStage : Rules Tower.Head :=
  { constantFreeRules rules with
    constantType := fun c => if c = propN ∨ c = numN ∨ c = setN then some U0 else none }

/-- The tower is contained in the package of the types of the codes. -/
theorem tower_sub_typeStage : RulesSub Presentation.Tower.rules typeStage where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun declared => nomatch declared
  computation := fun step => step.elim

/-- **The declared types of the codes are types of the package of the types of
the codes.** -/
theorem typeStage_codeType_typed {c : DeclName} {T : Tower.Tm 0}
    (code : programCodes.codeType c = some T) :
    ∃ u, typeStage.isUniverse u ∧ Typed typeStage .nil T (.head u) :=
  codeType_typed tower_sub_typeStage
    (show (if propN = propN ∨ propN = numN ∨ propN = setN then some U0 else none) = some U0 from
      if_pos (.inl rfl))
    (show (if numN = propN ∨ numN = numN ∨ numN = setN then some U0 else none) = some U0 from
      if_pos (.inr (.inl rfl)))
    (show (if setN = propN ∨ setN = numN ∨ setN = setN then some U0 else none) = some U0 from
      if_pos (.inr (.inr rfl))) code

section Model

variable (v : Nat → Nat) (facts : FormFacts objectRules objectRoles) {E : GenericEquality Tower.Head}
  (lawsE : E.Laws objectRules objectRoles) (reduceE : RespectsReduction objectRules objectRoles E)
  (holdsE : HoldsCongruence E programCodes)
include holdsE

/-- **The conversion model over the object package reads the program's codes**:
the value side reads them as the transport value model does, and on the
realizer side the codes are declared at their types, the decoder and the code
constructors have their roles, the type of codes is rigid, the decoder is a
congruence of the generic equality, and typed constructor spines at the type of
codes decode by the facts. -/
theorem objectCodesRead :
    CodesReadN (nmodel v (objectSideAt facts E lawsE reduceE)) programCodes where
  read := tprogramCodes_read v
  typed := objectRules_code_typed
  decoderRoles := objectDecoderRoles
  propRigid := objectRoles_prop
  proofs := LevelTower.IsUniverse.sort _
  holds := holdsE
  decodes := fun formed typing role => objectRules_decodes facts formed typing role

/-- **The package of the types of the codes is sound for the conversion model
over the object package**: the type of codes, the numbers and the sets are
valid, and it has no computation. -/
theorem typeStage_typedSoundN :
    TypedSoundN typeStage (nmodel v (objectSideAt facts E lawsE reduceE)) where
  laws := nmodel_laws v _
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
  root := fun step => nomatch step
  constants := by
    intro name type declared
    change (if name = propN ∨ name = numN ∨ name = setN then some U0 else none) = some type
      at declared
    split_ifs at declared with h
    cases declared
    rcases h with rfl | rfl | rfl
    · exact valid_propN (nmodel_laws v _) (objectCodesRead v facts lawsE reduceE holdsE)
    · exact valid_num v (objectSideAt_over facts lawsE reduceE)
    · exact valid_set v (objectSideAt_over facts lawsE reduceE)

/-- **The declared types of the codes are valid types with valid parts** in the
conversion model over the object package, by the fundamental lemma of the
package of the types of the codes. -/
theorem objectCodeTypes {c : DeclName} {T : Tower.Tm 0} (code : programCodes.codeType c = some T) :
    ValidTyN (nmodel v (objectSideAt facts E lawsE reduceE)) .nil T ∧
      StructuredN (nmodel v (objectSideAt facts E lawsE reduceE)) .nil T := by
  have sound := typeStage_typedSoundN v facts lawsE reduceE holdsE
  obtain ⟨u, hu, typedT⟩ := typeStage_codeType_typed code
  obtain ⟨validT, partsT, _⟩ := Derivable.validTN sound typedT trivial
  exact ⟨validT.validTy (sound.isUniverse hu) (sound.isUniverse' hu), partsT⟩

/-- **The object package is sound for its conversion model**, its root steps
read with their typing, at every lawful generic equality that respects typed
weak-head reduction and has the decoder as a congruence, given facts about the
weak-head forms of its types: the executable package's root steps as in each
stage, a decoding of a code as a step of the value side's decoding and of the
realizer side's computation; each code constant by the code constants of the
model, and each constant of the executable package by the executable package's
own proofs over the realizer side. -/
theorem objectRules_typedSoundN :
    TypedSoundN objectRules (nmodel v (objectSideAt facts E lawsE reduceE)) where
  laws := nmodel_laws v _
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
  root := by
    intro n l r step
    rcases step with step | step
    · exact stage_root v (objectSideAt_over facts lawsE reduceE) (allowed := fun _ => true)
        (fun _ => by rw [objectRules_declared_j]; rfl) step
    · exact .inl (ModelRootN.semantic (nmodel_laws v (objectSideAt facts E lawsE reduceE))
        (vprogramDecodes v) ⟨.inr step, programCodes.extend_decoder_step rules step⟩)
  constants := by
    intro name type declared
    change (programCodes.codeType name).orElse (fun _ => rules.constantType name) = some type
      at declared
    cases code : programCodes.codeType name with
    | some T =>
        rw [code] at declared
        cases declared
        exact valid_codeN (nmodel_laws v _) (objectCodesRead v facts lawsE reduceE holdsE)
          (objectCodeTypes v facts lawsE reduceE holdsE) code
    | none =>
        rw [code] at declared
        exact valid_declared v (objectSideAt_over facts lawsE reduceE) declared

end Model

/-! ## Typed equality -/

/-- **Typed equality has the congruence of the decoder** in the object
package. -/
theorem objectDeclarative_holdsCongruence :
    HoldsCongruence (declarative objectRules) programCodes :=
  declarative_holdsCongruence holds_typedO

/-- **The object package is sound for its conversion model at typed equality**,
given only the facts about the weak-head forms of its types. -/
theorem objectRules_typedSoundN_declarative (v : Nat → Nat)
    (facts : FormFacts objectRules objectRoles) :
    TypedSoundN objectRules (nmodel v (objectDeclarativeSide facts)) :=
  objectRules_typedSoundN v facts _ _ objectDeclarative_holdsCongruence

/-! ## Consequences at the daimon valuation -/

section Consequences

variable (facts : FormFacts objectRules objectRoles) {E : GenericEquality Tower.Head}
  (lawsE : E.Laws objectRules objectRoles) (reduceE : RespectsReduction objectRules objectRoles E)
  (holdsE : HoldsCongruence E programCodes) {n : Nat} {Γ : Tower.Ctx n}
include facts lawsE reduceE holdsE

/-- **Escape at the object package**: derivably equal terms of a formed context
are related by the generic equality, at every lawful generic equality that
respects typed weak-head reduction and has the decoder as a congruence, given
the facts. -/
theorem object_equal_escapeN {t u A : Tower.Tm n} (formed : CtxFormed objectRules Γ)
    (equal : Equal objectRules Γ t u A) : E.convTm Γ t u A :=
  Equal.escapeN (objectRules_typedSoundN (fun _ => 0) facts lawsE reduceE holdsE) formed equal

/-- **Escape for types at the object package.** -/
theorem object_typeEq_escapeN {A B : Tower.Tm n} (formed : CtxFormed objectRules Γ)
    (equal : TypeEq objectRules Γ A B) : E.convTy Γ A B :=
  TypeEq.escapeN (objectRules_typedSoundN (fun _ => 0) facts lawsE reduceE holdsE) formed equal

/-- **The evaluated candidate records the shape at the object package**: a typed
term of a formed context is related to itself, at its own type, by the
candidate of its value at the daimon valuation. -/
theorem object_typed_shapeN {t A : Tower.Tm n} (formed : CtxFormed objectRules Γ)
    (typing : Typed objectRules Γ t A) :
    ∃ P : NPack (nmodel (fun _ => 0) (objectSideAt facts E lawsE reduceE)) 0,
      DenN (nmodel (fun _ => 0) (objectSideAt facts E lawsE reduceE)) World.closed
          (Presentation.subst (fun _ => .const starN) A) P ∧
        P.Val (Presentation.subst (fun _ => .const starN) t) ∧
        (P.real (Presentation.subst (fun _ => .const starN) t)).rel Γ A t t :=
  Typed.shapeN (objectRules_typedSoundN (fun _ => 0) facts lawsE reduceE holdsE) formed typing

end Consequences

section Shapes

variable (facts : FormFacts objectRules objectRoles) {n : Nat} {Γ : Tower.Ctx n}
include facts

/-- **A code reaches a constructor spine or a neutral term**: a term typed at the
type of codes in a formed context of the object package reduces, typed, to a
code constructor applied to its arguments or to a neutral term, given the
facts. -/
theorem object_code_shape {c : Tower.Tm n} (formed : CtxFormed objectRules Γ)
    (typing : Typed objectRules Γ c (.const propN)) :
    ∃ w, RedTm objectRules objectRoles Γ c w (.const propN) ∧ IsCtorForm objectRoles w := by
  obtain ⟨P, den, -, real⟩ := object_typed_shapeN facts _ _ objectDeclarative_holdsCongruence
    formed typing
  change DenN _ World.closed (.const (tmodelC fun _ => 0).prop) P at den
  obtain rfl := ValueSide.DenS.prop_inv
    (nmodel_laws (fun _ => 0) (objectDeclarativeSide facts)).value den
  obtain ⟨-, ⟨w, red, form⟩, -⟩ := real
  exact ⟨w, red, form⟩

/-- **A closed term of the numbers reaches `zero`, `suc` of a term of a smaller
shape, or a neutral term**, in the object package, given the facts. -/
theorem object_closed_num_shape {t : Tower.Tm 0} (typing : Typed objectRules .nil t numT) :
    ∃ s, NumShapeRel (objectDeclarativeSide facts) numN zeroN sucN s .nil numT t t := by
  obtain ⟨P, den, val, real⟩ := object_typed_shapeN facts _ _ objectDeclarative_holdsCongruence
    .nil typing
  have closed : ∀ σ : Sub Tower.Head 0 0, Presentation.subst σ t = t := fun σ => by
    rw [show σ = ids from funext fun i => Fin.elim0 i, subst_ids]
  rw [closed] at val real
  have val' := val
  rw [num_den (fun _ => 0) den] at val'
  obtain ⟨s, hs, -⟩ := ValueSide.numIndPack_rel.mp val'
  exact ⟨s, (num_real (fun _ => 0) (objectSideAt_over facts _ _) den hs .nil numT t t).mp real⟩

end Shapes

/-! ## Controls -/

/-- The object package with one more root step, identifying `zero` with
`suc zero`. -/
def zeroSucObjectRules : Rules Tower.Head :=
  { objectRules with computation := RootComputation.union objectRules.computation zeroSucStep }

section Controls

variable (facts : FormFacts objectRules objectRoles) {n : Nat} {Γ : Tower.Ctx n}
include facts

/-- **The numbers' constructor `zero` is no code**: it has no typing at the type
of codes, given the facts. -/
theorem zero_not_code (formed : CtxFormed objectRules Γ) :
    ¬ Typed objectRules Γ (.const zeroN) (.const propN) := fun typing => by
  obtain ⟨-, -, le⟩ :=
    Typed.telescope_inv (S := objectSettingAt (declarative objectRules)) facts formed
      .nil numT declared_zero (σ := fun i => Fin.elim0 i) typing
  exact num_not_below_prop facts formed le

/-- **A code built by a quantifier decodes, typed**: the false code `∀ n : num,
zero = suc n` decodes by one root step to a dependent function type of the lowest
universe. -/
theorem falseCode_decodes :
    ∃ D, objectRules.computation.step (programCodes.holdsOf (falseCode (n := 0))) D ∧
      IsTypeForm objectRoles D ∧ Typed objectRules .nil D U0 :=
  objectRules_decodes facts (Δ := .nil) .nil (args := [_]) falseCode_typed
    (objectRoles_all (SetProfile.allInstance?_allName SetProfile.numTy))

/-- **The object package with a root step identifying `zero` with `suc zero` is
not sound for its conversion model**, whatever the facts. -/
theorem zeroSucObjectRules_not_typedSoundN (v : Nat → Nat) :
    ¬ TypedSoundN zeroSucObjectRules (nmodel v (objectDeclarativeSide facts)) := by
  have sub : RulesSub objectRules zeroSucObjectRules :=
    ⟨id, id, id, id, id, id, fun step => .inl step⟩
  have typed₀ : Typed zeroSucObjectRules (.nil : Tower.Ctx 0) (.const zeroN) numT :=
    Derivable.mono sub zero_typedO
  have typed₁ : Typed zeroSucObjectRules (.nil : Tower.Ctx 0)
      (.app (.const sucN) (.const zeroN)) numT :=
    Derivable.mono sub (.appElim suc_typedO zero_typedO)
  exact not_typedSoundN_of_zero_eq_suc v (objectDeclarativeSide facts)
    (.root (.inr ⟨rfl, rfl⟩) typed₀ typed₁)

end Controls

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
