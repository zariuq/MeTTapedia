import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Renaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.RigidHeads
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.PatternTelescopes

/-!
# The algorithmic equality of the package of an extension at the types of codes

The package of an extension of the transport value model (`TExtension`) is the object
package, possibly with further declared names whose constructors build new inductive types. Its
decoder is a congruence of its algorithmic equality, given the facts about the weak-head forms
of its types and that its root steps at new names preserve typing (`real_holdsCongruence`).
With the lifting of spine comparisons and the soundness of its new names, the conversion model
over the algorithmic equality is then sound for the package, and escape into it is conversion
completeness (`real_algorithmicComplete`). The object package is the extension by no name; the
object package with a declared datatype is another.

The congruence is proved by induction on the comparison of the codes
(`algorithmic_decodings`), which gives, besides compared decodings of compared
codes, compared decodings at a fresh variable of compared families of codes, and
compared arguments of compared spines:

* a comparison of codes reduces them, typed, to weak-head normal forms, and
  reducing a code reduces its decoding (`holds_redTm`);
* a family of codes is compared at a fresh variable, exactly where its decoding
  needs it;
* codes in weak-head normal form are compared as spines (`spine_decodings`).
  Neutral codes decode to neutral types, compared as spines headed by the
  decoder: a spine compared with a neutral term is neutral, as the two are
  headed by the same constant and a neutral term is headed by no constructor.
  A constructor spine decodes by one root step, to a dependent function type or
  an identity type whose parts the arguments' comparisons compare.

Two facts the constructor spines need at the type of codes and at the carriers
of the quantifiers and equations:

* **the carriers are compared with themselves**: a simple type of the profile is
  algorithmically equal to itself as a type in every formed context, by
  induction on the simple type (`typeAt_types_refl`). The type of codes and the
  sets are rigid constants, compared as neutral types; the numbers are an
  inductive type; an arrow is a dependent function type of carriers;
* **a typed constructor spine at the type of codes is saturated**, given the
  facts (`ctorSpine_saturated`): a constructor applied to fewer arguments than
  it declares has a dependent function type, one applied to more has a function
  part typed at a dependent function type while its full application has the
  type of codes or an inductive type; none of these is usable at the type of codes.
  A constructor of an inductive type is typed, at every type it is usable at, by a dependent
  function type while it lacks arguments and by its inductive type once saturated
  (`inductiveSpine_types`); so the numbers' constructors and the new constructors are never
  typed at the type of codes (`inductiveSpine_not_prop`).
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
open TelescopeAbstraction (closeType)
open Mettapedia.Logic
open Package (U0 numT)

namespace CodeModel
namespace ConvRules

variable (X : TExtension) {m : Nat} {Δ : Tower.Ctx m}

/-! ## The carriers compared with themselves -/

/-- The tower is contained in the package of an extension. -/
theorem tower_sub_realRules : RulesSub Presentation.Tower.rules X.realRules :=
  tower_sub_objectRules.trans X.realSub

/-- The lowest universe is a universe of the package of an extension. -/
theorem realRules_U0 : X.realRules.isUniverse (.sort Tower.zero) :=
  X.realSub.isUniverse (LevelTower.IsUniverse.sort _)

/-- The sets are rigid in the package of an extension. -/
theorem realRoles_set : X.realRoles setN = .rigid :=
  (X.realRoles_declared (c := setN) (by decide)).trans objectRoles_set

/-- A simple type of the profile is a type of the lowest universe in the package of an
extension. -/
theorem realTypeAt_typed (type : HOL.Ty SetProfile.SetBase) {k : Nat} {Θ : Tower.Ctx k} :
    Typed X.realRules Θ (FormationSensitiveHOLInterface.typeAt SetProfile.types k type) U0 :=
  typeAt_typed (tower_sub_realRules X) (X.realSub.constantType declared_prop)
    (X.realSub.constantType declared_num) (X.realSub.constantType rfl) type

/-- A rigid type constant of the lowest universe is algorithmically equal to
itself as a type, compared as a neutral type. -/
theorem rigid_types_refl {c : DeclName} (rigid : X.realRoles c = .rigid)
    (declared : X.realRules.constantType c = some U0) :
    Algorithmic X.realRules X.realRoles (.types Δ (.const c) (.const c)) := by
  have typing : Typed X.realRules Δ (.const c) U0 := constU0 (tower_sub_realRules X) declared
  have isC : IsType X.realRules Δ (.const c) := ⟨_, realRules_U0 X, typing⟩
  have isU : IsType X.realRules Δ U0 :=
    ⟨_, X.realSub.isUniverse (LevelTower.IsUniverse.sort _), U0_typedU (tower_sub_realRules X)⟩
  have neutral : Neutral X.realRoles (.const c : Tower.Tm m) := .rigid (args := []) rigid
  exact .types (RedTy.refl isC) (RedTy.refl isC) (.inr (.inr (.inr (.inr (.inl neutral)))))
    (.inr (.inr (.inr (.inr (.inl neutral)))))
    (.neutralTypes neutral neutral (realRules_U0 X)
      (.spinesW (.const declared typing) (RedTy.refl isU) (.inl ⟨_, rfl⟩)))

/-- **A simple type of the profile is algorithmically equal to itself as a type**
in every formed context of the package of an extension. -/
theorem typeAt_types_refl : ∀ (type : HOL.Ty SetProfile.SetBase) {m : Nat} {Δ : Tower.Ctx m},
    CtxFormed X.realRules Δ →
    Algorithmic X.realRules X.realRoles
      (.types Δ (FormationSensitiveHOLInterface.typeAt SetProfile.types m type)
        (FormationSensitiveHOLInterface.typeAt SetProfile.types m type))
  | .prop, _, _, _ =>
      rigid_types_refl X (realRoles_prop X) (X.realSub.constantType declared_prop)
  | .base .set, _, _, _ => rigid_types_refl X (realRoles_set X) (X.realSub.constantType rfl)
  | .base .num, _, Δ, _ => by
      have isNum : IsType X.realRules Δ numT :=
        ⟨_, realRules_U0 X, Derivable.mono X.realSub num_typedO⟩
      exact .types (RedTy.refl isNum) (RedTy.refl isNum)
        (.inr (.inr (.inr (.inr (.inr ⟨_, _, X.realRoles_num, rfl⟩)))))
        (.inr (.inr (.inr (.inr (.inr ⟨_, _, X.realRoles_num, rfl⟩)))))
        (.inductiveType X.realRoles_num isNum)
  | .arr a b, m, Δ, formed => by
      have isA :
          IsType X.realRules Δ (FormationSensitiveHOLInterface.typeAt SetProfile.types m a) :=
        ⟨_, realRules_U0 X, realTypeAt_typed X a⟩
      have isArr : IsType X.realRules Δ
          (FormationSensitiveHOLInterface.typeAt SetProfile.types m (.arr a b)) :=
        ⟨_, realRules_U0 X, piU0 (tower_sub_realRules X) (realTypeAt_typed X a)
          (realTypeAt_typed X b)⟩
      exact .types (RedTy.refl isArr) (RedTy.refl isArr) (.inr (.inl ⟨_, _, rfl⟩))
        (.inr (.inl ⟨_, _, rfl⟩))
        (.pi isA (typeAt_types_refl a formed) (typeAt_types_refl b (.snoc formed isA)))

/-! ## Saturated constructor spines -/

omit X in
/-- A typed application spine with an argument has a function part typed at a
dependent function type. -/
theorem Typed.spine_function {R : Rules Tower.Head} {f x : Tower.Tm m} :
    ∀ (rest : List (Tower.Tm m)) {T : Tower.Tm m}, Typed R Δ (appSpine f (x :: rest)) T →
      ∃ A B, Typed R Δ f (.pi A B) := by
  intro rest
  induction rest using List.reverseRecOn with
  | nil =>
      intro T typing
      obtain ⟨A, B, tf, -, -⟩ := Typed.generation (show Typed R Δ (.app f x) T from typing)
      exact ⟨A, B, tf⟩
  | append_singleton rest y ih =>
      intro T typing
      rw [show x :: (rest ++ [y]) = (x :: rest) ++ [y] from rfl, appSpine_concat] at typing
      obtain ⟨A, B, tf, -, -⟩ := Typed.generation typing
      exact ih tf

/-- The type of codes is a neutral type. -/
theorem prop_neutral : Neutral X.realRoles (.const propN : Tower.Tm m) :=
  .rigid (args := []) (realRoles_prop X)

omit X in
/-- The dependent function type over the entries of a telescope after a position, with at
least one entry, is a dependent function type. -/
theorem piRange_succ (e : (i : Nat) → Tower.Tm i) (j : Nat) :
    ∀ (d : Nat) (C : Tower.Tm (j + (d + 1))), ∃ D, piRange e j (d + 1) C = .pi (e j) D
  | 0, C => ⟨C, rfl⟩
  | d + 1, C => piRange_succ e j d (.pi (e (j + (d + 1))) C)

section Facts

variable (facts : FormFacts X.realRules X.realRoles)
include facts

/-- **A dependent function type is usable at no type of codes.** -/
theorem pi_not_below_prop (formed : CtxFormed X.realRules Δ) {A : Tower.Tm m}
    {B : Tower.Tm (m + 1)} (isPi : IsType X.realRules Δ (.pi A B))
    (le : TypeLe X.realRules Δ (.pi A B) (.const propN)) : False := by
  have isProp : IsType X.realRules Δ (.const propN) :=
    ⟨_, realRules_U0 X, Derivable.mono X.realSub prop_typedO⟩
  obtain ⟨A', B', e, -, -⟩ := Below.pi_source (S := realSetting X) facts
    (TypeLe.toBelow le isProp) formed (IsType.refl isPi)
  have neutral := (facts.forms e formed (.inr (.inr (.inr (.inr (.inl (prop_neutral X))))))
    (.inr (.inl ⟨_, _, rfl⟩))).neutral_left (prop_neutral X)
  exact neutral.not_former.2.1 A' B' rfl

/-- **The type of codes is usable at no dependent function type.** -/
theorem prop_not_below_pi (formed : CtxFormed X.realRules Δ) {A : Tower.Tm m}
    {B : Tower.Tm (m + 1)} (isPi : IsType X.realRules Δ (.pi A B))
    (le : TypeLe X.realRules Δ (.const propN) (.pi A B)) : False := by
  obtain ⟨A₀, B₀, e, -, -⟩ := Below.pi_inv (S := realSetting X) facts (TypeLe.toBelow le isPi)
    formed (IsType.refl isPi)
  have neutral := (facts.forms e formed (.inr (.inr (.inr (.inr (.inl (prop_neutral X))))))
    (.inr (.inl ⟨_, _, rfl⟩))).neutral_left (prop_neutral X)
  exact neutral.not_former.2.1 A₀ B₀ rfl

/-- **An inductive type is usable at no dependent function type.** -/
theorem inductive_not_below_pi (formed : CtxFormed X.realRules Δ) {I : DeclName}
    {cs : List (DeclName × List (Normalization.Field Tower.Head))}
    (role : X.realRoles I = .inductive cs) {A : Tower.Tm m} {B : Tower.Tm (m + 1)}
    (isPi : IsType X.realRules Δ (.pi A B)) (le : TypeLe X.realRules Δ (.const I) (.pi A B)) :
    False := by
  obtain ⟨A₀, B₀, e, -, -⟩ := Below.pi_inv (S := realSetting X) facts (TypeLe.toBelow le isPi)
    formed (IsType.refl isPi)
  exact TypeEq.inductive_ne_pi facts role formed e

/-- A spine whose function part has the type of codes as its least type has no
argument. -/
theorem over_prop (formed : CtxFormed X.realRules Δ) {g x : Tower.Tm m}
    {rest : List (Tower.Tm m)} {T : Tower.Tm m}
    (least : ∀ {Y}, Typed X.realRules Δ g Y → TypeLe X.realRules Δ (.const propN) Y)
    (typing : Typed X.realRules Δ (appSpine g (x :: rest)) T) : False := by
  obtain ⟨A, B, tg⟩ := Typed.spine_function rest typing
  exact prop_not_below_pi X facts formed (Typed.isType (S := realSetting X) tg formed) (least tg)

/-- **The types of a typed spine of a constructor of an inductive type**: a constant declared
at a telescope ending at an inductive type `I` is, applied to fewer arguments than the
telescope has entries, typed at types a dependent function type is usable at, and applied to
as many, at types `I` is usable at; it is never applied to more. -/
theorem inductiveSpine_types (formed : CtxFormed X.realRules Δ) {k I : DeclName}
    {cs : List (DeclName × List (Normalization.Field Tower.Head))}
    (role : X.realRoles I = .inductive cs) (e : (i : Nat) → Tower.Tm i) {N : Nat}
    (declared : X.realRules.constantType k = some (closeType (ofEntries e N) (.const I)))
    {args : List (Tower.Tm m)} {T : Tower.Tm m}
    (typing : Typed X.realRules Δ (appSpine (.const k) args) T) :
    (args.length < N ∧ ∃ A B, IsType X.realRules Δ (.pi A B) ∧
        TypeLe X.realRules Δ (.pi A B) T) ∨
      (args.length = N ∧ TypeLe X.realRules Δ (.const I) T) := by
  have short : ∀ {args : List (Tower.Tm m)} {T : Tower.Tm m}, args.length ≤ N →
      Typed X.realRules Δ (appSpine (.const k) args) T →
      (args.length < N ∧ ∃ A B, IsType X.realRules Δ (.pi A B) ∧
          TypeLe X.realRules Δ (.pi A B) T) ∨
        (args.length = N ∧ TypeLe X.realRules Δ (.const I) T) := by
    intro args T hle typing
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    subst hd
    rw [closeType_ofEntries_add e args.length d (.const I)] at declared
    rw [appSpine_eq_applyClosed e k rfl] at typing
    obtain ⟨-, typed, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
      (ofEntries e args.length) (piRange e args.length d (.const I)) declared typing
    cases d with
    | zero => exact .inr ⟨rfl, le⟩
    | succ d =>
        obtain ⟨D, hD⟩ := piRange_succ e args.length d (.const I)
        rw [hD] at le typed
        exact .inl ⟨by omega, _, _, Typed.isType (S := realSetting X) typed formed, le⟩
  by_cases hle : args.length ≤ N
  · exact short hle typing
  exfalso
  obtain ⟨pre, post, rfl, hpre⟩ : ∃ pre post, args = pre ++ post ∧ pre.length = N :=
    ⟨args.take N, args.drop N, (List.take_append_drop N args).symm,
      by rw [List.length_take]; omega⟩
  obtain ⟨x, rest, rfl⟩ : ∃ x rest, post = x :: rest := by
    cases post with
    | nil => exact absurd (le_of_eq (by rw [List.append_nil, hpre])) hle
    | cons x rest => exact ⟨x, rest, rfl⟩
  rw [appSpine_append] at typing
  obtain ⟨A, B, tg⟩ := Typed.spine_function rest typing
  rcases short (le_of_eq hpre) tg with ⟨lt, -⟩ | ⟨-, le⟩
  · omega
  · exact inductive_not_below_pi X facts formed role
      (Typed.isType (S := realSetting X) tg formed) le

/-- **A spine of a constructor of an inductive type is no code**: it is never typed at the
type of codes. -/
theorem inductiveSpine_not_prop (formed : CtxFormed X.realRules Δ) {k I : DeclName}
    {cs : List (DeclName × List (Normalization.Field Tower.Head))}
    (role : X.realRoles I = .inductive cs) (typeI : IsType X.realRules Δ (.const I))
    (e : (i : Nat) → Tower.Tm i) {N : Nat}
    (declared : X.realRules.constantType k = some (closeType (ofEntries e N) (.const I)))
    {args : List (Tower.Tm m)}
    (typing : Typed X.realRules Δ (appSpine (.const k) args) (.const propN)) : False := by
  rcases inductiveSpine_types X facts formed role e declared typing with
    ⟨-, A, B, isPi, le⟩ | ⟨-, le⟩
  · exact pi_not_below_prop X facts formed isPi le
  · exact inductive_not_below_prop X facts formed role typeI le

/-- **A typed constructor spine at the type of codes is saturated**: it applies
its constructor to exactly as many arguments as the constructor declares. -/
theorem ctorSpine_saturated (formed : CtxFormed X.realRules Δ) {k : DeclName}
    {args : List (Tower.Tm m)} {a : Nat}
    (typing : Typed X.realRules Δ (appSpine (.const k) args) (.const propN))
    (role : X.realRoles k = .constructor a) : args.length = a := by
  have univ := tower_sub_realRules X
  have hu : X.realRules.isUniverse (.sort Tower.zero) := realRules_U0 X
  have propT : ∀ {k : Nat} {Θ : Tower.Ctx k}, Typed X.realRules Θ (.const propN) U0 :=
    Derivable.mono X.realSub prop_typedO
  have typeT : ∀ (type : HOL.Ty SetProfile.SetBase) {k : Nat} {Θ : Tower.Ctx k},
      Typed X.realRules Θ (FormationSensitiveHOLInterface.typeAt SetProfile.types k type) U0 :=
    fun type => realTypeAt_typed X type
  have piProp : ∀ {k : Nat} {Θ : Tower.Ctx k}, IsType X.realRules Θ
      (.pi (.const propN) (.const propN)) := ⟨_, hu, piU0 univ propT propT⟩
  have isNum : IsType X.realRules Δ numT := ⟨_, hu, Derivable.mono X.realSub num_typedO⟩
  rcases realRoles_constructor X role with ⟨-, role⟩ | ⟨-, I, fs, declared, -, memI, cs, roleI⟩
  · rcases objectRoles_constructor role with ⟨rfl, rfl⟩ | ⟨type, found, rfl⟩ |
      ⟨type, found, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- Implication declares two arguments.
      match args, typing with
      | [], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed .nil
            (.pi (.const propN) (.pi (.const propN) (.const propN)))
            (X.realSub.constantType declared_imp) (σ := fun i => Fin.elim0 i) typing
          exact (pi_not_below_prop X facts formed
            ⟨_, hu, piU0 univ propT (piU0 univ propT propT)⟩ le).elim
      | [p], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc .nil (.const propN)) (.pi (.const propN) (.const propN))
            (X.realSub.constantType declared_imp)
            (σ := consSub p fun i => Fin.elim0 i) typing
          exact (pi_not_below_prop X facts formed piProp le).elim
      | [_, _], _ => rfl
      | p :: q :: r :: rest, typing =>
          refine (over_prop X facts formed (g := appSpine (.const impN) [p, q]) (fun tg => ?_)
            typing).elim
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc (.snoc .nil (.const propN)) (.const propN)) (.const propN)
            (X.realSub.constantType declared_imp)
            (σ := consSub q (consSub p fun i => Fin.elim0 i)) tg
          exact le
    · -- A quantifier declares one argument.
      obtain rfl := SetProfile.allInstance?_eq_some found
      match args, typing with
      | [], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed .nil
            (SetProfile.allType type) (X.realSub.constantType (declared_allName type))
            (σ := fun i => Fin.elim0 i) typing
          rw [SetProfile.allType, FormationSensitiveHOLInterface.typeAt_subst] at le
          exact (pi_not_below_prop X facts formed ⟨_, hu, typeT (.arr (.arr type .prop) .prop)⟩
            le).elim
      | [_], _ => rfl
      | f :: x :: rest, typing =>
          refine (over_prop X facts formed (g := appSpine (.const (SetProfile.allName type)) [f])
            (fun tg => ?_) typing).elim
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc .nil (.pi (typeTerm type) (.const propN))) (.const propN)
            (X.realSub.constantType (declared_allName type)) (σ := consSub f fun i => Fin.elim0 i)
            tg
          exact le
    · -- An equation declares two arguments.
      obtain rfl := SetProfile.eqInstance?_eq_some found
      match args, typing with
      | [], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed .nil
            (SetProfile.eqType type) (X.realSub.constantType (declared_eqName type))
            (σ := fun i => Fin.elim0 i) typing
          rw [SetProfile.eqType, FormationSensitiveHOLInterface.typeAt_subst] at le
          exact (pi_not_below_prop X facts formed ⟨_, hu, typeT (.arr type (.arr type .prop))⟩
            le).elim
      | [x], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
            (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 (.arr type .prop))
            (X.realSub.constantType (declared_eqName type)) (σ := consSub x fun i => Fin.elim0 i)
            typing
          have isArr : IsType X.realRules Δ
              (FormationSensitiveHOLInterface.typeAt SetProfile.types m (.arr type .prop)) :=
            ⟨_, hu, typeT (.arr type .prop)⟩
          rw [FormationSensitiveHOLInterface.typeAt_subst] at le
          exact (pi_not_below_prop X facts formed isArr le).elim
      | [_, _], _ => rfl
      | x :: y :: z :: rest, typing =>
          refine (over_prop X facts formed
            (g := appSpine (.const (SetProfile.eqName type)) [x, y]) (fun tg => ?_) typing).elim
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
              (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))
            (.const propN) (X.realSub.constantType (declared_eqName type))
            (σ := consSub y (consSub x fun i => Fin.elim0 i)) tg
          exact le
    · -- `zero` is no code.
      exact (inductiveSpine_not_prop X facts formed X.realRoles_num isNum (ctorEntry numN [])
        (N := 0) (X.realSub.constantType declared_zero) typing).elim
    · -- Nor is `suc` applied to arguments.
      exact (inductiveSpine_not_prop X facts formed X.realRoles_num isNum
        (ctorEntry numN [.recursive]) (N := 1) (X.realSub.constantType declared_suc)
        typing).elim
  · -- Nor is a new constructor applied to arguments.
    exact (inductiveSpine_not_prop X facts formed roleI (newInductive_isType X memI roleI)
      (ctorEntry I fs) declared typing).elim

end Facts

/-! ## The decoder along comparisons -/

/-- What a comparison of terms gives the decoder: codes compared at the type of
codes have decodings compared at the universe of proofs, and families of codes
compared at a dependent function type into the type of codes have decodings at
a fresh variable compared in the extended context. -/
abbrev DecodingsCompared (Δ : Tower.Ctx m) (t u A : Tower.Tm m) : Prop :=
  (A = .const propN → CtxFormed X.realRules Δ →
    Algorithmic X.realRules X.realRoles
      (.terms Δ (.app (.const holdsN) t) (.app (.const holdsN) u) U0)) ∧
  (∀ D : Tower.Tm m, A = .pi D (.const propN) → CtxFormed X.realRules (.snoc Δ D) →
    Algorithmic X.realRules X.realRoles (.terms (.snoc Δ D)
      (.app (.const holdsN) (.app (Presentation.rename wk t) (.var 0)))
      (.app (.const holdsN) (.app (Presentation.rename wk u) (.var 0))) U0))

/-- What a comparison of spines gives the decoder: an application is compared
with an application, its function part as a spine at a type reducing to a
dependent function type and its argument at the domain, with the decodings of
the arguments compared; a constant is compared with itself at its declared type;
other spines are compared with spines headed by the same constant, if any. -/
def ArgumentsCompared (Δ : Tower.Ctx m) : Tower.Tm m → Tower.Tm m → Tower.Tm m → Prop
  | .app f a, u, U => ∃ (g b A : Tower.Tm m) (B : Tower.Tm (m + 1)), u = .app g b ∧
      U = inst0 a B ∧
      (∃ V, RedTy X.realRules X.realRoles Δ V (.pi A B) ∧ ArgumentsCompared Δ f g V) ∧
      Algorithmic X.realRules X.realRoles (.terms Δ a b A) ∧ DecodingsCompared X Δ a b A
  | .const k, u, U => u = .const k ∧ ∃ T, X.realRules.constantType k = some T ∧ U = liftClosed T
  | t, u, _ => spineConst t = spineConst u

/-- Spines whose arguments are compared are headed by the same constant, if any. -/
theorem ArgumentsCompared.spineConst_eq {Δ : Tower.Ctx m} {t : Tower.Tm m} :
    ∀ {u U : Tower.Tm m}, ArgumentsCompared X Δ t u U → spineConst t = spineConst u := by
  induction t with
  | app f a ihf _ =>
      intro u U compared
      obtain ⟨g, b, A, B, rfl, -, ⟨V, -, comparedF⟩, -, -⟩ := compared
      exact (ihf comparedF : spineConst f = spineConst g)
  | const k =>
      intro u U compared
      obtain ⟨rfl, -⟩ := compared
      rfl
  | var i => intro u U compared; exact compared
  | head h => intro u U compared; exact compared
  | pi A B _ _ => intro u U compared; exact compared
  | sigma A B _ _ => intro u U compared; exact compared
  | id A a b _ _ _ => intro u U compared; exact compared
  | lam body _ => intro u U compared; exact compared
  | pair a b _ _ => intro u U compared; exact compared
  | fst p _ => intro u U compared; exact compared
  | snd p _ => intro u U compared; exact compared
  | refl a _ => intro u U compared; exact compared

/-- What each judgment of the algorithmic equality gives the decoder. Comparisons
of types give nothing further. -/
abbrev DecodingsAt : AlgorithmicStatement Tower.Head → Prop
  | .types _ _ _ => True
  | .typesW _ _ _ => True
  | .terms Γ t u A => DecodingsCompared X Γ t u A
  | .termsW Γ t u A => DecodingsCompared X Γ t u A
  | .spines Γ t u U => ArgumentsCompared X Γ t u U
  | .spinesW Γ t u U => ∃ V, RedTy X.realRules X.realRoles Γ V U ∧ ArgumentsCompared X Γ t u V

section Decoder

variable (facts : FormFacts X.realRules X.realRoles)
  (newPreserving : ∀ {n : Nat} {Γ : Tower.Ctx n} {c : DeclName} {args : List (Tower.Tm n)}
    {r A : Tower.Tm n}, CtxFormed X.realRules Γ → c ∈ X.names →
      X.realRules.computation.step (appSpine (.const c) args) r →
      Typed X.realRules Γ (appSpine (.const c) args) A → Typed X.realRules Γ r A)
include facts newPreserving

/-- Weak-head reduction of a typed term of the package of an extension is a typed
reduction, given the facts. -/
theorem real_redTm (formed : CtxFormed X.realRules Δ) {t t' T : Tower.Tm m}
    (red : WhRed X.realRules X.realRoles t t') (typing : Typed X.realRules Δ t T) :
    RedTm X.realRules X.realRoles Δ t t' T := by
  obtain ⟨target, equal⟩ := real_reduces_preserve X facts newPreserving formed
    (WhRed.reduces red) typing
  exact ⟨red, typing, target, equal⟩

/-- Reducing a code reduces its decoding. -/
theorem holds_redTm (formed : CtxFormed X.realRules Δ) {c c' : Tower.Tm m}
    (red : WhRed X.realRules X.realRoles c c')
    (typing : Typed X.realRules Δ c (.const propN)) :
    RedTm X.realRules X.realRoles Δ (.app (.const holdsN) c) (.app (.const holdsN) c') U0 :=
  real_redTm X facts newPreserving formed
    (WhRed.scrutinee (before := []) (after := []) (realRoles_holds X) rfl red)
    (.appElim (Derivable.mono X.realSub holds_typedO) typing)

omit newPreserving in
/-- A spine of a constructor of the package of an extension at the type of codes is a code
constructor of the object package. -/
theorem codeSpine_old (formed : CtxFormed X.realRules Δ) {k : DeclName} {a : Nat}
    {args : List (Tower.Tm m)}
    (typing : Typed X.realRules Δ (appSpine (.const k) args) (.const propN))
    (role : X.realRoles k = .constructor a) : objectRoles k = .constructor a := by
  rcases realRoles_constructor X role with ⟨-, role⟩ | ⟨-, I, fs, declared, -, memI, cs, roleI⟩
  · exact role
  · exact (inductiveSpine_not_prop X facts formed roleI (newInductive_isType X memI roleI)
      (ctorEntry I fs) declared typing).elim

/-- **Codes compared as spines have compared decodings**: two weak-head normal
codes, compared as spines with their arguments' decodings compared, have
decodings compared at the universe of proofs. Neutral codes decode to neutral
types compared as spines headed by the decoder; constructor spines, saturated by
their typing, decode by one root step to dependent function types and identity
types whose parts are compared by the arguments' comparisons, over carriers
compared with themselves. -/
theorem spine_decodings (formed : CtxFormed X.realRules Δ) {t u U : Tower.Tm m}
    (formT : SpineForm X.realRoles t) (formU : SpineForm X.realRoles u)
    (typedT : Typed X.realRules Δ t (.const propN))
    (typedU : Typed X.realRules Δ u (.const propN))
    (spines : Algorithmic X.realRules X.realRoles (.spinesW Δ t u U))
    (compared : ∃ V, RedTy X.realRules X.realRoles Δ V U ∧ ArgumentsCompared X Δ t u V) :
    Algorithmic X.realRules X.realRoles
      (.terms Δ (.app (.const holdsN) t) (.app (.const holdsN) u) U0) := by
  have hu : X.realRules.isUniverse (.sort Tower.zero) := realRules_U0 X
  have isU0 : IsType X.realRules Δ U0 := universe_isType (S := realSetting X) hu
  have holdsT : ∀ {k : Nat} {Θ : Tower.Ctx k},
      Typed X.realRules Θ (.const holdsN) (.pi (.const propN) U0) :=
    Derivable.mono X.realSub holds_typedO
  have typeT : ∀ (type : HOL.Ty SetProfile.SetBase) {k : Nat} {Θ : Tower.Ctx k},
      Typed X.realRules Θ (FormationSensitiveHOLInterface.typeAt SetProfile.types k type) U0 :=
    fun type => realTypeAt_typed X type
  have typesU : ∀ {k : Nat} {Θ : Tower.Ctx k} {A B : Tower.Tm k},
      Algorithmic X.realRules X.realRoles (.terms Θ A B U0) →
        Algorithmic X.realRules X.realRoles (.types Θ A B) :=
    fun d => Algorithmic.types_of_universe (S := realSetting X) hu d
  have decoded : ∀ {c c' D D' : Tower.Tm m},
      X.realRules.computation.step (.app (.const holdsN) c) D →
      X.realRules.computation.step (.app (.const holdsN) c') D' →
      Typed X.realRules Δ c (.const propN) → Typed X.realRules Δ c' (.const propN) →
      IsTypeForm X.realRoles D → IsTypeForm X.realRoles D' →
      Algorithmic X.realRules X.realRoles (.typesW Δ D D') →
      Algorithmic X.realRules X.realRoles
        (.terms Δ (.app (.const holdsN) c) (.app (.const holdsN) c') U0) := by
    intro c c' D D' step step' tc tc' _ _ d
    have red := real_redTm X facts newPreserving formed (.single (.root step))
      (.appElim holdsT tc)
    have red' := real_redTm X facts newPreserving formed (.single (.root step'))
      (.appElim holdsT tc')
    exact .terms (RedTy.refl isU0) (.inl ⟨_, rfl⟩) red red' (.univ hu red.target red'.target d)
  obtain ⟨V, -, argsCompared⟩ := compared
  have sameHead := ArgumentsCompared.spineConst_eq X argsCompared
  rcases formT with neutralT | ⟨k, arity, args, role, rfl⟩
  · -- Neutral codes decode to neutral types.
    have neutralU : Neutral X.realRoles u := by
      rcases formU with neutralU | ⟨k, arity, args', role, rfl⟩
      · exact neutralU
      · exact absurd role (neutralT.spineConst_not_constructor
          (sameHead.trans (spineConst_appSpine args' _)))
    have holdsTT : Typed X.realRules Δ (.app (.const holdsN) t) U0 := .appElim holdsT typedT
    have holdsTU : Typed X.realRules Δ (.app (.const holdsN) u) U0 := .appElim holdsT typedU
    have isProp : IsType X.realRules Δ (.const propN) :=
      ⟨_, hu, Derivable.mono X.realSub prop_typedO⟩
    have codes : Algorithmic X.realRules X.realRoles (.terms Δ t u (.const propN)) :=
      .terms (RedTy.refl isProp) (.inr (.inr (.inr (.inr (.inl (prop_neutral X))))))
        (RedTm.refl typedT) (RedTm.refl typedU)
        (.spine (.inr (.inl (prop_neutral X))) (.inl neutralT) (.inl neutralU)
          typedT typedU spines)
    have neutral : ∀ {c : Tower.Tm m}, Neutral X.realRoles c →
        Neutral X.realRoles (.app (.const holdsN) c) :=
      fun n => Neutral.stuck_single (before := []) (after := []) (realRoles_holds X) rfl n
    exact .terms (RedTy.refl isU0) (.inl ⟨_, rfl⟩) (RedTm.refl holdsTT) (RedTm.refl holdsTU)
      (.univ hu holdsTT holdsTU (.neutralTypes (neutral neutralT) (neutral neutralU) hu
        (.spinesW (.app (.spinesW (.const (X.realSub.constantType declared_holds) holdsT)
          (RedTy.refl (Typed.isType (S := realSetting X) holdsT formed))
          (.inr (.inl ⟨_, _, rfl⟩))) codes) (RedTy.refl isU0) (.inl ⟨_, rfl⟩))))
  · -- Constructor spines decode by one root step.
    have saturated := ctorSpine_saturated X facts formed typedT role
    have role₀ := codeSpine_old X facts formed typedT role
    rcases objectRoles_constructor role₀ with ⟨rfl, rfl⟩ | ⟨type, found, rfl⟩ |
      ⟨type, found, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- Implication decodes to a dependent function type of decodings.
      match args, saturated, typedT, argsCompared with
      | [p, q], _, typedT, argsCompared =>
        obtain ⟨g, b, A, B, rfl, -, ⟨V₁, red₁, args₁⟩, dq, hq⟩ := argsCompared
        obtain ⟨g', b', A', B', rfl, rfl, ⟨V₂, red₂, args₂⟩, dp, hp⟩ := args₁
        obtain ⟨rfl, T, declared, rfl⟩ := args₂
        obtain rfl : T = programCodes.impType :=
          Option.some.inj (declared.symm.trans (X.realSub.constantType declared_imp))
        have e₂ : (Tm.pi A' B' : Tower.Tm m) =
            .pi (.const propN) (.pi (.const propN) (.const propN)) :=
          WhRed.eq_of_whnf (S := realSetting X) (pi_whnf X.realShape _ _) red₂.red
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₂
        have e₁ : (Tm.pi A B : Tower.Tm m) = .pi (.const propN) (.const propN) :=
          WhRed.eq_of_whnf (S := realSetting X) (pi_whnf X.realShape _ _) red₁.red
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₁
        have tp := dp.terms_typed.1
        exact decoded (X.realDecodes (DecoderStep.imp p q)) (X.realDecodes (DecoderStep.imp b' b))
          typedT typedU (.inr (.inl ⟨_, _, rfl⟩)) (.inr (.inl ⟨_, _, rfl⟩))
          (.pi ⟨_, hu, .appElim holdsT tp⟩ (typesU (hp.1 rfl formed))
            (Algorithmic.rename (typesU (hq.1 rfl formed)) (CtxRen.wk Δ _)))
    · -- A quantifier decodes to a dependent function type over its carrier.
      obtain rfl := SetProfile.allInstance?_eq_some found
      match args, saturated, typedT, argsCompared with
      | [f], _, typedT, argsCompared =>
        obtain ⟨g, b, A, B, rfl, -, ⟨V₁, red₁, args₁⟩, df, hf⟩ := argsCompared
        obtain ⟨rfl, T, declared, rfl⟩ := args₁
        obtain rfl : T = SetProfile.allType type :=
          Option.some.inj (declared.symm.trans (X.realSub.constantType (declared_allName type)))
        have e₁ : (Tm.pi A B : Tower.Tm m) =
            .pi (.pi (FormationSensitiveHOLInterface.typeAt SetProfile.types m type)
              (.const propN)) (.const propN) := by
          rw [WhRed.eq_of_whnf (S := realSetting X) (pi_whnf X.realShape _ _) red₁.red]
          exact congrArg₂ Tm.pi (FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ _)
            (FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ _)
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₁
        have carrier : programCodes.decoders.allCarrier (SetProfile.allName type) =
            some (typeTerm type) := by
          change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = _
          rw [found]
          rfl
        have isCarrier : IsType X.realRules Δ
            (FormationSensitiveHOLInterface.typeAt SetProfile.types m type) := ⟨_, hu, typeT type⟩
        have body := typesU (hf.2 _ rfl (.snoc formed isCarrier))
        have step := DecoderStep.all carrier f
        have step' := DecoderStep.all carrier b
        rw [typeTerm_lift] at step step'
        exact decoded (X.realDecodes step) (X.realDecodes step') typedT typedU
          (.inr (.inl ⟨_, _, rfl⟩)) (.inr (.inl ⟨_, _, rfl⟩))
          (.pi isCarrier (typeAt_types_refl X type formed) body)
    · -- An equation decodes to an identity type of its carrier.
      obtain rfl := SetProfile.eqInstance?_eq_some found
      match args, saturated, typedT, argsCompared with
      | [x, y], _, typedT, argsCompared =>
        obtain ⟨g, b, A, B, rfl, -, ⟨V₁, red₁, args₁⟩, dy, -⟩ := argsCompared
        obtain ⟨g', b', A', B', rfl, rfl, ⟨V₂, red₂, args₂⟩, dx, -⟩ := args₁
        obtain ⟨rfl, T, declared, rfl⟩ := args₂
        obtain rfl : T = SetProfile.eqType type :=
          Option.some.inj (declared.symm.trans (X.realSub.constantType (declared_eqName type)))
        have e₂ : (Tm.pi A' B' : Tower.Tm m) =
            .pi (FormationSensitiveHOLInterface.typeAt SetProfile.types m type)
              (.pi (FormationSensitiveHOLInterface.typeAt SetProfile.types (m + 1) type)
                (.const propN)) := by
          rw [WhRed.eq_of_whnf (S := realSetting X) (pi_whnf X.realShape _ _) red₂.red]
          exact congrArg₂ Tm.pi (FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ _)
            (FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ _)
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₂
        have e₁ : (Tm.pi A B : Tower.Tm m) =
            .pi (FormationSensitiveHOLInterface.typeAt SetProfile.types m type)
              (.const propN) := by
          rw [WhRed.eq_of_whnf (S := realSetting X) (pi_whnf X.realShape _ _) red₁.red]
          rw [FormationSensitiveHOLInterface.typeAt_subst]
          rfl
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₁
        have carrier : programCodes.decoders.eqCarrier (SetProfile.eqName type) =
            some (typeTerm type) := by
          change (if true = true then (SetProfile.eqInstance? (SetProfile.eqName type)).map typeTerm
            else none) = _
          rw [if_pos rfl, found]
          rfl
        have step := DecoderStep.eq carrier x y
        have step' := DecoderStep.eq carrier b' b
        rw [typeTerm_lift] at step step'
        exact decoded (X.realDecodes step) (X.realDecodes step') typedT typedU
          (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))
          (.id (typeAt_types_refl X type formed) dx dy)
    · -- `zero` has no typing at the type of codes.
      exact (inductiveSpine_not_prop X facts formed X.realRoles_num
        ⟨_, hu, Derivable.mono X.realSub num_typedO⟩ (ctorEntry numN []) (N := 0)
        (X.realSub.constantType declared_zero) typedT).elim
    · -- Nor has `suc` applied to an argument.
      exact (inductiveSpine_not_prop X facts formed X.realRoles_num
        ⟨_, hu, Derivable.mono X.realSub num_typedO⟩ (ctorEntry numN [.recursive]) (N := 1)
        (X.realSub.constantType declared_suc) typedT).elim

/-- **Every comparison of the algorithmic equality of the package of an extension gives
the decoder what it needs**, given the facts: compared codes have compared
decodings, compared families of codes have compared decodings at a fresh
variable, and compared spines have compared arguments. By induction on the
derivation: a comparison of terms reduces the codes, and reducing a code reduces
its decoding; a family is compared at a fresh variable, exactly where its
decoding needs it; codes in weak-head normal form are compared as spines. -/
theorem algorithmic_decodings {st : AlgorithmicStatement Tower.Head}
    (derivation : Algorithmic X.realRules X.realRoles st) : DecodingsAt X st := by
  induction derivation with
  | types => trivial
  | heads => trivial
  | pi => trivial
  | sigma => trivial
  | id => trivial
  | inductiveType => trivial
  | neutralTypes => trivial
  | terms rA _ rt ru _ ih =>
      refine ⟨fun e formed => ?_, fun D e formed => ?_⟩
      · subst e
        obtain rfl := WhRed.eq_of_whnf (S := realSetting X)
          ((prop_neutral X).whnf X.realShape) rA.red
        exact Algorithmic.terms_expand (holds_redTm X facts newPreserving formed rt.red rt.source)
          (holds_redTm X facts newPreserving formed ru.red ru.source) (ih.1 rfl formed)
      · subst e
        obtain rfl := WhRed.eq_of_whnf (S := realSetting X) (pi_whnf X.realShape _ _) rA.red
        have fresh : ∀ {f f' : Tower.Tm _},
            RedTm X.realRules X.realRoles _ f f' (.pi D (.const propN)) →
            RedTm X.realRules X.realRoles _
              (.app (.const holdsN) (.app (Presentation.rename wk f) (.var 0)))
              (.app (.const holdsN) (.app (Presentation.rename wk f') (.var 0))) U0 :=
          fun red => holds_redTm X facts newPreserving formed ((red.red.rename wk).app (.var 0))
            (.appElim (B := .const propN) (Typed.weaken red.source) (.var 0))
        exact Algorithmic.terms_expand (fresh rt) (fresh ru) (ih.2 D rfl formed)
  | univ => exact ⟨nofun, fun _ => nofun⟩
  | eta _ _ _ _ _ _ ih =>
      refine ⟨nofun, fun D e formed => ?_⟩
      cases e
      exact ih.1 rfl formed
  | sigmaEta => exact ⟨nofun, fun _ => nofun⟩
  | refl => exact ⟨nofun, fun _ => nofun⟩
  | spine sA formT formU typedT typedU spines ih =>
      refine ⟨fun e formed => ?_, fun D e => ?_⟩
      · subst e
        exact spine_decodings X facts newPreserving formed formT formU typedT typedU spines ih
      · subst e
        exact absurd sA SpineType.not_pi
  | var i => exact rfl
  | const declared _ => exact ⟨rfl, _, declared, rfl⟩
  | app _ da ihF iha => exact ⟨_, _, _, _, rfl, rfl, ihF, da, iha⟩
  | fst _ ih =>
      obtain ⟨V, -, compared⟩ := ih
      have sameHead := ArgumentsCompared.spineConst_eq X compared
      exact sameHead
  | snd _ ih =>
      obtain ⟨V, -, compared⟩ := ih
      have sameHead := ArgumentsCompared.spineConst_eq X compared
      exact sameHead
  | spinesW _ rU _ ih => exact ⟨_, rU, ih⟩

/-- **The decoder is a congruence of the algorithmic equality of the package of an
extension**, given the facts: codes it relates at the type of codes have decodings it relates
at the universe of proofs. -/
theorem real_holdsCongruence :
    HoldsCongruence (algorithmic X.realRules X.realRoles) programCodes := by
  intro n Γ c c' related
  exact ⟨realDeclarative_holdsCongruence X related.1, fun _ _ _ cr formed =>
    (algorithmic_decodings X facts newPreserving (related.2 cr formed)).1 rfl formed⟩

/-- **Conversion completeness for the package of an extension**, given the facts, that its
root steps at new names preserve typing, the lifting of spine comparisons, and that its new
names are sound for its conversion models: derivably equal terms of a formed context are
algorithmically equal. The conversion model over the algorithmic equality is sound for the
package, and escape into it is completeness. -/
theorem real_algorithmicComplete (lift : SpineLift (realSetting X))
    (new : ∀ {E : GenericEquality Tower.Head} (lawsE : E.Laws X.realRules X.realRoles)
      (reduceE : RespectsReduction X.realRules X.realRoles E),
      HoldsCongruence E programCodes →
        NewSoundN X (nmodel X (fun _ => 0) (realSideAt X facts E lawsE reduceE))) :
    AlgorithmicComplete X.realRules X.realRoles := by
  intro n Γ t u A formed equal
  have lawsA := real_algorithmic_laws X facts newPreserving lift
  have reduceA : RespectsReduction X.realRules X.realRoles (algorithmic X.realRules X.realRoles) :=
    algorithmic_convTm_reduce (S := realSetting X)
  have holdsA : HoldsCongruence (algorithmic X.realRules X.realRoles) programCodes :=
    real_holdsCongruence X facts newPreserving
  have related := real_equal_escapeN X facts lawsA reduceA holdsA (new lawsA reduceA holdsA)
    formed equal
  have d := related.2 (CtxRen.id Γ) formed
  rw [rename_id, rename_id, rename_id] at d
  exact d

end Decoder

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
