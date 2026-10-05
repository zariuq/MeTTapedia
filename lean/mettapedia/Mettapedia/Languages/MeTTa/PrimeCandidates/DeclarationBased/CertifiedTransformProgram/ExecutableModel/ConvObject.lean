import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConsistencySound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelPackage
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.CodeConstants
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Inversion

/-!
# The package of an extension in the conversion model

The package of an extension of the transport value model (`TExtension`): the object
package, the executable package with the program's codes, possibly with further declared
names. Its package is a realizer side of the conversion model at every lawful generic
equality that respects typed weak-head reduction, given facts about the weak-head forms of
its types (`realSideAt`). The facts are an input: they are the declarative facts of the
package, which the conversion model does not prove itself. The object package is the
extension by no name (`objectTExt`); the object package with a declared datatype is another.

The side is over the executable package (`realSideAt_over`): the package contains it, and its
roles keep the roles of the numbers and of the constants with computation. So every constant
of the executable package is valid in the model over it by the executable package's own
proofs.

**The codes.** The model reads the program's codes (`realCodesRead`):

* the value side reads them as the transport value model does;
* the realizer side declares them at their types (`realRules_code_typed`), gives
  the decoder and the code constructors their roles, and keeps the type of
  codes rigid;
* the decoder is a congruence of the generic equality: an input of the side,
  which typed equality has (`realDeclarative_holdsCongruence`);
* a typed constructor spine at the type of codes is a code constructor applied
  to its arguments, and it decodes to a typed weak-head form of a type
  (`realRules_decodes`). The proof inverts the typing with the facts: a
  spine of implication, of a quantifier or of an equation has its arguments at
  the declared domains; the numbers' constructors are no codes, since the
  type of the numbers is equal to no type of codes, and neither are the new
  constructors, which build new inductive types (`inductive_not_below_prop`).

The declared types of the codes are typed in a package with the type of codes,
the numbers and the sets and no computation (`typeStage`), sound for the model
by the validity of those three constants (`typeStage_typedSoundN`); the
fundamental lemma of that package makes them valid types.

**Soundness.** The object package is sound for the conversion model over the package of every
extension (`objectRules_typedSoundN`), and the package itself is sound for it, its root steps
read with their typing, when its new constants are valid and its root steps at new names hold
(`NewSoundN`, `realRules_typedSoundN`): the executable package's root steps as in each stage,
identity elimination at its typed instances, and a decoding of a code as a step of the value side's
decoding and of the realizer side's computation. It holds at typed equality with only the
facts and the new names as input (`realRules_typedSoundN_declarative`). So derivably equal
terms of a formed context are related by the generic equality, derivably equal types too, and
a typed term is related to itself by the candidate of its value (`real_equal_escapeN`,
`real_typeEq_escapeN`, `real_typed_shapeN`): a closed term of the numbers reaches `zero`, `suc`
of a term of a smaller shape, or a neutral term (`real_closed_num_shape`).

Negative: the object package with one more root step identifying `zero` with `suc zero` is
sound for no such model (`zeroSucObjectRules_not_typedSoundN`).
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

/-! ## The package of an extension as a realizer side -/

/-- The normalization setting of the package of an extension at a generic equality. -/
def realSettingAt (X : TExtension) (E : GenericEquality Tower.Head) : Setting Tower.Head ℕ where
  R := X.realRules
  roles := X.realRoles
  E := E
  levels := X.realLevels
  shape := X.realShape
  constructors := X.realDeclared

/-- **The package of an extension as a realizer side** at a lawful generic equality that
respects typed weak-head reduction, with facts about the weak-head forms of its types. -/
def realSideAt (X : TExtension) (facts : FormFacts X.realRules X.realRoles)
    (E : GenericEquality Tower.Head) (lawsE : E.Laws X.realRules X.realRoles)
    (reduceE : RespectsReduction X.realRules X.realRoles E) : RealizerSide Tower.Head ℕ where
  toSetting := realSettingAt X E
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

/-- A name with computation or a constructor in the executable package is declared there. -/
theorem objectRules_declared_of_roles {c : DeclName} {role : Role Tower.Head}
    (declared : roles c = role) (nonrigid : role ≠ .rigid) :
    objectRules.constantType c ≠ none := by
  by_cases mem : c ∈ nonrigidNames
  · have all : ∀ n ∈ nonrigidNames, (allTypes n).isSome = true := by decide
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp (all c mem)
    rw [rules_sub_objectRules.constantType (show rules.constantType c = some T from hT)]
    exact Option.some_ne_none T
  · exact absurd (declared.symm.trans (roles_of_not_mem mem)) nonrigid

section Side

variable (X : TExtension)

theorem realRoles_prop : X.realRoles propN = .rigid :=
  (X.realRoles_declared (c := propN) (by decide)).trans objectRoles_prop

theorem realRoles_holds :
    X.realRoles holdsN = .computes 1 (.split 0 .constructor fun _ => .leaf) :=
  X.realDecoderRoles.holds

variable (facts : FormFacts X.realRules X.realRoles) {E : GenericEquality Tower.Head}
  (lawsE : E.Laws X.realRules X.realRoles) (reduceE : RespectsReduction X.realRules X.realRoles E)

/-- **The package of an extension is a realizer side over the executable package.** -/
theorem realSideAt_over : OverRules (realSideAt X facts E lawsE reduceE) where
  sub := rules_sub_objectRules.trans X.realSub
  keep := fun declared nonrigid =>
    (X.realRoles_declared (objectRules_declared_of_roles declared nonrigid)).trans
      (objectRoles_of_roles declared nonrigid)
  set := (X.realRoles_declared (c := setN) (by decide)).trans objectRoles_set
  power := (X.realRoles_declared (c := powerN) (by decide)).trans objectRoles_power

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

/-- The package of an extension declares each code constant at its type. -/
theorem realRules_code_typed (X : TExtension) {c : DeclName} {T : Tower.Tm 0}
    (code : programCodes.codeType c = some T) : Typed X.realRules .nil (.const c) T :=
  Derivable.mono X.realSub (objectRules_code_typed code)

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

/-- **The constructors of the package of an extension**: the object package's, at the names
the extension does not add, and new constructors, which build new inductive types. -/
theorem realRoles_constructor (X : TExtension) {k : DeclName} {a : Nat}
    (role : X.realRoles k = .constructor a) :
    (k ∉ X.names ∧ objectRoles k = .constructor a) ∨
      (k ∈ X.names ∧ ∃ (I : DeclName) (fs : List (Normalization.Field Tower.Head)),
        X.realRules.constantType k = some (ctorType I fs) ∧ fs.length = a ∧ I ∈ X.names ∧
          ∃ cs, X.realRoles I = .inductive cs) := by
  by_cases new : k ∈ X.names
  · exact .inr ⟨new, X.realNewCtor new role⟩
  · exact .inl ⟨new, (X.realOld new).symm.trans role⟩

/-- A spine of a constant applied to as many terms as a telescope has entries is the constant
applied to the telescope at the substitution of those terms. -/
theorem appSpine_eq_applyClosed (entry : (j : Nat) → Tower.Tm j) (c : DeclName) {N n : Nat}
    {args : List (Tower.Tm n)} (length : args.length = N) :
    appSpine (.const c) args = applyClosed (ofEntries entry N) (argsSub N args) (.const c) := by
  rw [applyClosed_eq_appSpine, telescopeArgs_argsSub entry N args length]

section Decoding

variable (X : TExtension) (facts : FormFacts X.realRules X.realRoles)

/-- The package of an extension at typed equality, as a realizer side with the facts. -/
abbrev realDeclarativeSide : RealizerSide Tower.Head ℕ :=
  realSideAt X facts (declarative X.realRules) (declarative_laws X.realRoles X.realLevels)
    declarative_convTm_reduce

variable {n : Nat} {Δ : Tower.Ctx n}

/-- A new inductive type is a type of the package of an extension. -/
theorem newInductive_isType {I : DeclName}
    {cs : List (DeclName × List (Normalization.Field Tower.Head))}
    (mem : I ∈ X.names) (role : X.realRoles I = .inductive cs) :
    IsType X.realRules Δ (.const I) := by
  obtain ⟨u, hu, declared⟩ := X.realNewInductive mem role
  obtain ⟨w, hw, typedU⟩ := universe_isType (S := realSettingAt X (declarative X.realRules))
    (Δ := .nil) (X.realSub.isUniverse hu)
  exact ⟨u, X.realSub.isUniverse hu, .const declared typedU hw⟩

include facts in
/-- **An inductive type is below no type of codes**: a chain from it ends in a type equal to
it, which is not the rigid type of codes. -/
theorem inductive_not_below_prop (formed : CtxFormed X.realRules Δ) {I : DeclName}
    {cs : List (DeclName × List (Normalization.Field Tower.Head))}
    (role : X.realRoles I = .inductive cs)
    (typeI : IsType X.realRules Δ (.const I))
    (le : TypeLe X.realRules Δ (.const I) (.const propN)) : False := by
  have e := RealizerSide.typeLe_inductive (T := realDeclarativeSide X facts) (I := I) formed
    role le typeI.refl
  have neutral : Neutral X.realRoles (.const propN : Tower.Tm n) :=
    .rigid (args := []) (realRoles_prop X)
  exact ((facts.forms e formed (.inr (.inr (.inr (.inr (.inl neutral)))))
    (.inr (.inr (.inr (.inr (.inr ⟨I, _, role, rfl⟩)))))).neutral_left
      neutral).ne_inductive role rfl

/-- The simple types of the profile, as types of a context. -/
theorem typeTerm_lift (type : HOL.Ty SetProfile.SetBase) :
    (liftClosed (typeTerm type) : Tower.Tm n) =
      FormationSensitiveHOLInterface.typeAt SetProfile.types n type :=
  FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ type

include facts in
/-- **A typed constructor spine at the type of codes decodes to a typed weak-head
form of a type**, by one root step: it is a spine of implication, of a
quantifier instance or of an equation instance, with its arguments at the
declared domains; the numbers' constructors and the new constructors have no typing at the
type of codes. -/
theorem realRules_decodes (formed : CtxFormed X.realRules Δ) {k : DeclName}
    {args : List (Tower.Tm n)}
    (typing : Typed X.realRules Δ (appSpine (.const k) args) (.const propN))
    (role : X.realRoles k = .constructor args.length) :
    ∃ D, X.realRules.computation.step (.app (.const holdsN) (appSpine (.const k) args)) D ∧
      IsTypeForm X.realRoles D ∧ Typed X.realRules Δ D U0 := by
  have univ := tower_sub_objectRules.trans X.realSub
  have hu : X.realRules.isUniverse (.sort Tower.zero) := X.realSub.isUniverse (.sort _)
  have propT : ∀ {m : Nat} {Γ : Tower.Ctx m}, Typed X.realRules Γ (.const propN) U0 :=
    Derivable.mono X.realSub prop_typedO
  have typeT : ∀ (type : HOL.Ty SetProfile.SetBase) {m : Nat} {Γ : Tower.Ctx m},
      Typed X.realRules Γ (FormationSensitiveHOLInterface.typeAt SetProfile.types m type) U0 :=
    fun type => typeAt_typed univ (X.realSub.constantType declared_prop)
      (X.realSub.constantType declared_num) (X.realSub.constantType rfl) type
  have holdsT : ∀ {m : Nat} {Γ : Tower.Ctx m},
      Typed X.realRules Γ (.const holdsN) (.pi (.const propN) U0) :=
    Derivable.mono X.realSub holds_typedO
  have numNotProp : ∀ {m : Nat} {Γ : Tower.Ctx m}, CtxFormed X.realRules Γ →
      TypeLe X.realRules Γ numT (.const propN) → False :=
    fun formed le => inductive_not_below_prop X facts formed X.realRoles_num
      ⟨_, hu, Derivable.mono X.realSub num_typedO⟩ le
  rcases realRoles_constructor X role with ⟨-, role⟩ | ⟨-, I, fs, declared, len, memI, cs, roleI⟩
  · rcases objectRoles_constructor role with ⟨rfl, len⟩ | ⟨type, found, len⟩ |
      ⟨type, found, len⟩ | ⟨rfl, len⟩ | ⟨rfl, len⟩
    · -- Implication: both arguments are codes, and the decoding is a dependent
      -- function type of proof types.
      match args, len with
      | [p, q], _ =>
        obtain ⟨mor, -, -⟩ :=
          Typed.telescope_inv (S := realSettingAt X (declarative X.realRules)) facts formed
            (.snoc (.snoc .nil (.const propN)) (.const propN)) (.const propN)
            (X.realSub.constantType declared_imp)
            (σ := consSub q (consSub p fun i => Fin.elim0 i)) typing
        have tp : Typed X.realRules Δ p (.const propN) := mor 1
        have tq : Typed X.realRules Δ q (.const propN) := mor 0
        refine ⟨_, X.realDecodes (DecoderStep.imp p q), .inr (.inl ⟨_, _, rfl⟩), piU0 univ
          (.appElim holdsT tp) (.appElim holdsT (Typed.weaken tq))⟩
    · -- A quantifier: its argument is a family of codes over the carrier, and the
      -- decoding is a dependent function type over the carrier.
      obtain rfl := SetProfile.allInstance?_eq_some found
      match args, len with
      | [f], _ =>
        have carrier : programCodes.quantifiers (SetProfile.allName type) =
            some (typeTerm type) := by
          change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = _
          rw [found]
          rfl
        obtain ⟨mor, -, -⟩ :=
          Typed.telescope_inv (S := realSettingAt X (declarative X.realRules)) facts formed
            (.snoc .nil (.pi (typeTerm type) (.const propN))) (.const propN)
            (X.realSub.constantType (declared_allName type))
            (σ := consSub f fun i => Fin.elim0 i) typing
        have tf : Typed X.realRules Δ f
            (.pi (FormationSensitiveHOLInterface.typeAt SetProfile.types n type)
              (.const propN)) := by
          have h := mor 0
          simp only [Ctx.lookup_snoc_zero, subst_rename_wk, Presentation.subst,
            FormationSensitiveHOLInterface.typeAt_subst] at h
          exact h
        refine ⟨_, X.realDecodes (DecoderStep.all carrier f), .inr (.inl ⟨_, _, rfl⟩), ?_⟩
        rw [typeTerm_lift]
        exact piU0 univ (typeT type)
          (.appElim holdsT (.appElim (B := .const propN) (Typed.weaken tf) (.var 0)))
    · -- An equation: both arguments are points of the carrier, and the decoding is
      -- an identity type.
      obtain rfl := SetProfile.eqInstance?_eq_some found
      match args, len with
      | [x, y], _ =>
        have carrier : programCodes.decoders.eqCarrier (SetProfile.eqName type) =
            some (typeTerm type) := by
          change (if true = true then
            (SetProfile.eqInstance? (SetProfile.eqName type)).map typeTerm else none) = _
          rw [if_pos rfl, found]
          rfl
        obtain ⟨mor, -, -⟩ :=
          Typed.telescope_inv (S := realSettingAt X (declarative X.realRules)) facts formed
            (.snoc (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
              (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))
            (.const propN) (X.realSub.constantType (declared_eqName type))
            (σ := consSub y (consSub x fun i => Fin.elim0 i)) typing
        have tx : Typed X.realRules Δ x
            (FormationSensitiveHOLInterface.typeAt SetProfile.types n type) := by
          have h := mor 1
          change Typed X.realRules Δ x
            (Presentation.subst (consSub y (consSub x fun i => Fin.elim0 i))
              (Presentation.rename wk (Presentation.rename wk
                (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type)))) at h
          rw [FormationSensitiveHOLInterface.typeAt_rename,
            FormationSensitiveHOLInterface.typeAt_rename,
            FormationSensitiveHOLInterface.typeAt_subst] at h
          exact h
        have ty : Typed X.realRules Δ y
            (FormationSensitiveHOLInterface.typeAt SetProfile.types n type) := by
          have h := mor 0
          change Typed X.realRules Δ y
            (Presentation.subst (consSub y (consSub x fun i => Fin.elim0 i))
              (Presentation.rename wk
                (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))) at h
          rw [FormationSensitiveHOLInterface.typeAt_rename,
            FormationSensitiveHOLInterface.typeAt_subst] at h
          exact h
        refine ⟨_, X.realDecodes (DecoderStep.eq carrier x y),
          .inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))), ?_⟩
        rw [typeTerm_lift]
        exact .idForm (typeT type) hu tx ty
    · -- `zero` has the type of the numbers, which is below no type of codes.
      match args, len with
      | [], _ =>
        obtain ⟨-, -, le⟩ :=
          Typed.telescope_inv (S := realSettingAt X (declarative X.realRules)) facts formed
            .nil numT (X.realSub.constantType declared_zero) (σ := fun i => Fin.elim0 i) typing
        exact (numNotProp formed le).elim
    · -- `suc` returns the numbers, which are below no type of codes.
      match args, len with
      | [a], _ =>
        obtain ⟨-, -, le⟩ :=
          Typed.telescope_inv (S := realSettingAt X (declarative X.realRules)) facts formed
            (.snoc .nil numT) numT (X.realSub.constantType declared_suc)
            (σ := consSub a fun i => Fin.elim0 i) typing
        exact (numNotProp formed le).elim
  · -- A new constructor returns its new inductive type, which is below no type of codes.
    rw [appSpine_eq_applyClosed (ctorEntry I fs) k len.symm] at typing
    obtain ⟨-, -, le⟩ :=
      Typed.telescope_inv (S := realSettingAt X (declarative X.realRules)) facts formed
        (ctorTele I fs) (.const I) declared typing
    exact (inductive_not_below_prop X facts formed roleI (newInductive_isType X memI roleI)
      le).elim

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

/-- **The new names of an extension are sound for a conversion model**: each new constant is a
valid term of its declared type, and each root step at a new name preserves meaning,
semantically or at its typed instances. The object package has no new name. -/
structure NewSoundN (X : TExtension) (M : NModel Tower.Head ℕ) : Prop where
  constants : ∀ {name : DeclName} {type : Tower.Tm 0}, name ∈ X.names →
    X.realRules.constantType name = some type → ValidTmN M .nil (.const name) type
  roots : ∀ {n : Nat} {c : DeclName} {args : List (Tower.Tm n)} {r : Tower.Tm n}, c ∈ X.names →
    X.realRules.computation.step (appSpine (.const c) args) r →
      RootSemanticN M (appSpine (.const c) args) r ∨
        TypedRootN X.realRules M (appSpine (.const c) args) r

/-- The object package has no new name. -/
theorem objectTExt_newSoundN (M : NModel Tower.Head ℕ) : NewSoundN objectTExt M :=
  ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

section Model

variable (X : TExtension) (v : Nat → Nat) (facts : FormFacts X.realRules X.realRoles)
  {E : GenericEquality Tower.Head} (lawsE : E.Laws X.realRules X.realRoles)
  (reduceE : RespectsReduction X.realRules X.realRoles E)
  (holdsE : HoldsCongruence E programCodes)
include holdsE

/-- **The conversion model over the package of an extension reads the program's codes**:
the value side reads them as the transport value model does, and on the realizer side the
codes are declared at their types, the decoder and the code constructors have their roles, the
type of codes is rigid, the decoder is a congruence of the generic equality, and typed
constructor spines at the type of codes decode by the facts. -/
theorem realCodesRead :
    CodesReadN (nmodel X v (realSideAt X facts E lawsE reduceE)) programCodes where
  read := X.programCodes_read v
  typed := realRules_code_typed X
  decoderRoles := X.realDecoderRoles
  propRigid := realRoles_prop X
  proofs := X.realSub.isUniverse (.sort _)
  holds := holdsE
  decodes := fun formed typing role => realRules_decodes X facts formed typing role

/-- **The package of the types of the codes is sound for the conversion model
over the package of an extension**: the type of codes, the numbers and the sets are
valid, and it has no computation. -/
theorem typeStage_typedSoundN :
    TypedSoundN typeStage (nmodel X v (realSideAt X facts E lawsE reduceE)) where
  laws := nmodel_laws X v _
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  headTyping' := fun typing => X.realSub.headTyping typing
  isUniverse' := fun hu => X.realSub.isUniverse hu
  join' := fun join => X.realSub.join join
  cumulative' := fun c => X.realSub.cumulative c
  headEq' := fun same => X.realSub.headEq same
  root := fun step => nomatch step
  constants := by
    intro name type declared
    change (if name = propN ∨ name = numN ∨ name = setN then some U0 else none) = some type
      at declared
    split_ifs at declared with h
    cases declared
    rcases h with rfl | rfl | rfl
    · exact valid_propN (nmodel_laws X v _) (realCodesRead X v facts lawsE reduceE holdsE)
    · exact valid_num X v (realSideAt_over X facts lawsE reduceE)
    · exact valid_set X v (realSideAt_over X facts lawsE reduceE)

/-- **The declared types of the codes are valid types with valid parts** in the
conversion model over the package of an extension, by the fundamental lemma of the
package of the types of the codes. -/
theorem realCodeTypes {c : DeclName} {T : Tower.Tm 0} (code : programCodes.codeType c = some T) :
    ValidTyN (nmodel X v (realSideAt X facts E lawsE reduceE)) .nil T ∧
      StructuredN (nmodel X v (realSideAt X facts E lawsE reduceE)) .nil T := by
  have sound := typeStage_typedSoundN X v facts lawsE reduceE holdsE
  obtain ⟨u, hu, typedT⟩ := typeStage_codeType_typed code
  obtain ⟨validT, partsT, _⟩ := Derivable.validTN sound typedT trivial
  exact ⟨validT.validTy (sound.isUniverse hu) (sound.isUniverse' hu), partsT⟩

/-- **The object package is sound for the conversion model over the package of every
extension**, its root steps read with their typing: the executable package's root steps as in
each stage, a decoding of a code as a step of the value side's decoding and of the realizer
side's computation; each code constant by the code constants of the model, and each constant
of the executable package by the executable package's own proofs over the realizer side. -/
theorem objectRules_typedSoundN :
    TypedSoundN objectRules (nmodel X v (realSideAt X facts E lawsE reduceE)) where
  laws := nmodel_laws X v _
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  headTyping' := fun typing => X.realSub.headTyping typing
  isUniverse' := fun hu => X.realSub.isUniverse hu
  join' := fun join => X.realSub.join join
  cumulative' := fun c => X.realSub.cumulative c
  headEq' := fun same => X.realSub.headEq same
  root := by
    intro n l r step
    rcases step with step | step
    · exact stage_root X v (realSideAt_over X facts lawsE reduceE) (allowed := fun _ => true)
        (fun _ => by rw [objectRules_declared_j]; rfl) step
    · exact .inl (ModelRootN.semantic (nmodel_laws X v (realSideAt X facts E lawsE reduceE))
        (X.programDecodes v) ⟨.inr step, X.realDecodes step⟩)
  constants := by
    intro name type declared
    change (programCodes.codeType name).orElse (fun _ => rules.constantType name) = some type
      at declared
    cases code : programCodes.codeType name with
    | some T =>
        rw [code] at declared
        cases declared
        exact valid_codeN (nmodel_laws X v _) (realCodesRead X v facts lawsE reduceE holdsE)
          (realCodeTypes X v facts lawsE reduceE holdsE) code
    | none =>
        rw [code] at declared
        exact valid_declared X v (realSideAt_over X facts lawsE reduceE) declared

/-- **The package of an extension is sound for its conversion model**, its root steps read
with their typing, at every lawful generic equality that respects typed weak-head reduction
and has the decoder as a congruence, given facts about the weak-head forms of its types, when
its new constants are valid and its root steps at its new names hold: the executable package's
root steps as in each stage, a decoding of a code as a step of the value side's decoding and of
the realizer side's computation; each code constant by the code constants of the model, and
each constant of the executable package by the executable package's own proofs over the
realizer side. -/
theorem realRules_typedSoundN
    (new : NewSoundN X (nmodel X v (realSideAt X facts E lawsE reduceE))) :
    TypedSoundN X.realRules (nmodel X v (realSideAt X facts E lawsE reduceE)) where
  laws := nmodel_laws X v _
  headTyping := fun typing => X.realHeadTyping typing
  isUniverse := fun hu => X.realIsUniverse hu
  join := fun join => X.realJoin join
  cumulative := fun c => X.realCumulative c
  headEq := fun same => X.realHeadEq same
  headTyping' := id
  isUniverse' := id
  join' := id
  cumulative' := id
  headEq' := id
  root := by
    intro n l r step
    obtain ⟨c, arity, inspect, args, -, rfl, -, -⟩ := X.realShape.spine step
    by_cases isNew : c ∈ X.names
    · exact new.roots isNew step
    rcases X.realStepOld isNew step with step | step
    · exact stage_root X v (realSideAt_over X facts lawsE reduceE) (allowed := fun _ => true)
        (fun _ => by rw [X.realSub.constantType objectRules_declared_j]; rfl) step
    · exact .inl (ModelRootN.semantic (nmodel_laws X v (realSideAt X facts E lawsE reduceE))
        (X.programDecodes v) ⟨.inr step, X.realDecodes step⟩)
  constants := by
    intro name type declared
    by_cases isNew : name ∈ X.names
    · exact new.constants isNew declared
    · exact (objectRules_typedSoundN X v facts lawsE reduceE holdsE).constants
        (X.realDeclaredOld isNew declared)

end Model

/-! ## Typed equality -/

/-- **Typed equality has the congruence of the decoder** in the package of an extension. -/
theorem realDeclarative_holdsCongruence (X : TExtension) :
    HoldsCongruence (declarative X.realRules) programCodes :=
  declarative_holdsCongruence (Derivable.mono X.realSub holds_typedO)

/-! ## Consequences at the daimon valuation -/

section Consequences

variable (X : TExtension) (facts : FormFacts X.realRules X.realRoles)
  {E : GenericEquality Tower.Head} (lawsE : E.Laws X.realRules X.realRoles)
  (reduceE : RespectsReduction X.realRules X.realRoles E)
  (holdsE : HoldsCongruence E programCodes)
  (new : NewSoundN X (nmodel X (fun _ => 0) (realSideAt X facts E lawsE reduceE)))
  {n : Nat} {Γ : Tower.Ctx n}
include facts lawsE reduceE holdsE new

/-- **Escape at the package of an extension**: derivably equal terms of a formed context are
related by the generic equality, at every lawful generic equality that respects typed
weak-head reduction and has the decoder as a congruence, given the facts, when the new
constants are valid and the root steps at the new names hold. -/
theorem real_equal_escapeN {t u A : Tower.Tm n} (formed : CtxFormed X.realRules Γ)
    (equal : Equal X.realRules Γ t u A) : E.convTm Γ t u A :=
  Equal.escapeN (realRules_typedSoundN X (fun _ => 0) facts lawsE reduceE holdsE new) formed equal

/-- **Escape for types at the package of an extension.** -/
theorem real_typeEq_escapeN {A B : Tower.Tm n} (formed : CtxFormed X.realRules Γ)
    (equal : TypeEq X.realRules Γ A B) : E.convTy Γ A B :=
  TypeEq.escapeN (realRules_typedSoundN X (fun _ => 0) facts lawsE reduceE holdsE new) formed equal

/-- **The evaluated candidate records the shape at the package of an extension**: a typed term
of a formed context is related to itself, at its own type, by the candidate of its value at
the daimon valuation. -/
theorem real_typed_shapeN {t A : Tower.Tm n} (formed : CtxFormed X.realRules Γ)
    (typing : Typed X.realRules Γ t A) :
    ∃ P : NPack (nmodel X (fun _ => 0) (realSideAt X facts E lawsE reduceE)) 0,
      DenN (nmodel X (fun _ => 0) (realSideAt X facts E lawsE reduceE)) World.closed
          (Presentation.subst (fun _ => .const starN) A) P ∧
        P.Val (Presentation.subst (fun _ => .const starN) t) ∧
        (P.real (Presentation.subst (fun _ => .const starN) t)).rel Γ A t t :=
  Typed.shapeN (realRules_typedSoundN X (fun _ => 0) facts lawsE reduceE holdsE new) formed typing

/-- **A code reaches a constructor spine or a neutral term**: a term typed at the
type of codes in a formed context of the package of an extension reduces, typed, to a code
constructor applied to its arguments or to a neutral term. -/
theorem real_code_shape {c : Tower.Tm n} (formed : CtxFormed X.realRules Γ)
    (typing : Typed X.realRules Γ c (.const propN)) :
    ∃ w, RedTm X.realRules X.realRoles Γ c w (.const propN) ∧ IsCtorForm X.realRoles w := by
  obtain ⟨P, den, -, real⟩ := real_typed_shapeN X facts lawsE reduceE holdsE new formed typing
  change DenN _ World.closed (.const ((X.model fun _ => 0).prop)) P at den
  obtain rfl := ValueSide.DenS.prop_inv
    (nmodel_laws X (fun _ => 0) (realSideAt X facts E lawsE reduceE)).value den
  obtain ⟨-, ⟨w, red, form⟩, -⟩ := real
  exact ⟨w, red, form⟩

/-- **A closed term of the numbers reaches `zero`, `suc` of a term of a smaller
shape, or a neutral term**, in the package of an extension. -/
theorem real_closed_num_shape {t : Tower.Tm 0} (typing : Typed X.realRules .nil t numT) :
    ∃ s, NumShapeRel (realSideAt X facts E lawsE reduceE) numN zeroN sucN s .nil numT t t := by
  obtain ⟨P, den, val, real⟩ := real_typed_shapeN X facts lawsE reduceE holdsE new .nil typing
  have closed : ∀ σ : Sub Tower.Head 0 0, Presentation.subst σ t = t := fun σ => by
    rw [show σ = ids from funext fun i => Fin.elim0 i, subst_ids]
  rw [closed] at val real
  have val' := val
  rw [num_den X (fun _ => 0) den] at val'
  obtain ⟨s, hs, -⟩ := ValueSide.numIndPack_rel.mp val'
  exact ⟨s, (num_real X (fun _ => 0) (realSideAt_over X facts _ _) den hs .nil numT t t).mp real⟩

end Consequences

/-! ## Controls -/

/-- The object package with one more root step, identifying `zero` with
`suc zero`. -/
def zeroSucObjectRules : Rules Tower.Head :=
  { objectRules with computation := RootComputation.union objectRules.computation zeroSucStep }

section Controls

variable (X : TExtension) (facts : FormFacts X.realRules X.realRoles) {n : Nat}
  {Γ : Tower.Ctx n}
include facts

/-- **The numbers' constructor `zero` is no code**: it has no typing at the type
of codes, given the facts. -/
theorem zero_not_code (formed : CtxFormed X.realRules Γ) :
    ¬ Typed X.realRules Γ (.const zeroN) (.const propN) := fun typing => by
  obtain ⟨-, -, le⟩ :=
    Typed.telescope_inv (S := realSettingAt X (declarative X.realRules)) facts formed
      .nil numT (X.realSub.constantType declared_zero) (σ := fun i => Fin.elim0 i) typing
  exact inductive_not_below_prop X facts formed (I := numN) X.realRoles_num
    ⟨_, X.realSub.isUniverse (.sort _), Derivable.mono X.realSub num_typedO⟩ le

/-- **A code built by a quantifier decodes, typed**: the false code `∀ n : num,
zero = suc n` decodes by one root step to a dependent function type of the lowest
universe. -/
theorem falseCode_decodes :
    ∃ D, X.realRules.computation.step (programCodes.holdsOf (falseCode (n := 0))) D ∧
      IsTypeForm X.realRoles D ∧ Typed X.realRules .nil D U0 :=
  realRules_decodes X facts (Δ := .nil) .nil (args := [_])
    (Derivable.mono X.realSub falseCode_typed)
    ((X.realRoles_declared (by decide)).trans
      (objectRoles_all (SetProfile.allInstance?_allName SetProfile.numTy)))

end Controls

/-- **The object package with a root step identifying `zero` with `suc zero` is
not sound for its conversion model**, whatever the facts. -/
theorem zeroSucObjectRules_not_typedSoundN (facts : FormFacts objectRules objectRoles)
    (v : Nat → Nat) :
    ¬ TypedSoundN zeroSucObjectRules
      (nmodel objectTExt v (realDeclarativeSide objectTExt facts)) := by
  have sub : RulesSub objectRules zeroSucObjectRules :=
    ⟨id, id, id, id, id, id, fun step => .inl step⟩
  have typed₀ : Typed zeroSucObjectRules (.nil : Tower.Ctx 0) (.const zeroN) numT :=
    Derivable.mono sub zero_typedO
  have typed₁ : Typed zeroSucObjectRules (.nil : Tower.Ctx 0)
      (.app (.const sucN) (.const zeroN)) numT :=
    Derivable.mono sub (.appElim suc_typedO zero_typedO)
  exact not_typedSoundN_of_zero_eq_suc objectTExt v (realDeclarativeSide objectTExt facts)
    (.root (.inr ⟨rfl, rfl⟩) typed₀ typed₁)


end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
