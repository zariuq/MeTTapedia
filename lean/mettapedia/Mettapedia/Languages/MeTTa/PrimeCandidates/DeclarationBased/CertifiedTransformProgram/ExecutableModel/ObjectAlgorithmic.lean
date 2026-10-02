import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Renaming
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.RigidHeads

/-!
# The algorithmic equality of the object package at the types of codes

The decoder is a congruence of the algorithmic equality of the object package,
given the facts about the weak-head forms of its types
(`object_holdsCongruence`). With the lifting of spine comparisons, the
conversion model over the algorithmic equality is then sound for the object
package, and escape into it is conversion completeness
(`object_algorithmicComplete`).

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
  type of codes or the numbers; none of these is usable at the type of codes.
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
open Mettapedia.Logic
open Package (U0 numT)

namespace CodeModel
namespace ConvRules

variable {m : Nat} {Δ : Tower.Ctx m}

/-! ## The carriers compared with themselves -/

/-- A rigid type constant of the lowest universe is algorithmically equal to
itself as a type, compared as a neutral type. -/
theorem rigid_types_refl {c : DeclName} (rigid : objectRoles c = .rigid)
    (declared : objectRules.constantType c = some U0) :
    Algorithmic objectRules objectRoles (.types Δ (.const c) (.const c)) := by
  have typing : Typed objectRules Δ (.const c) U0 := constU0 tower_sub_objectRules declared
  have isC : IsType objectRules Δ (.const c) := ⟨_, LevelTower.IsUniverse.sort _, typing⟩
  have isU : IsType objectRules Δ U0 :=
    ⟨_, LevelTower.IsUniverse.sort _, U0_typedU tower_sub_objectRules⟩
  have neutral : Neutral objectRoles (.const c : Tower.Tm m) := .rigid (args := []) rigid
  exact .types (RedTy.refl isC) (RedTy.refl isC) (.inr (.inr (.inr (.inr (.inl neutral)))))
    (.inr (.inr (.inr (.inr (.inl neutral)))))
    (.neutralTypes neutral neutral (LevelTower.IsUniverse.sort _)
      (.spinesW (.const declared typing) (RedTy.refl isU) (.inl ⟨_, rfl⟩)))

/-- **A simple type of the profile is algorithmically equal to itself as a type**
in every formed context of the object package. -/
theorem typeAt_types_refl : ∀ (type : HOL.Ty SetProfile.SetBase) {m : Nat} {Δ : Tower.Ctx m},
    CtxFormed objectRules Δ →
    Algorithmic objectRules objectRoles
      (.types Δ (FormationSensitiveHOLInterface.typeAt SetProfile.types m type)
        (FormationSensitiveHOLInterface.typeAt SetProfile.types m type))
  | .prop, _, _, _ => rigid_types_refl objectRoles_prop declared_prop
  | .base .set, _, _, _ => rigid_types_refl objectRoles_set rfl
  | .base .num, _, Δ, _ => by
      have isNum : IsType objectRules Δ numT := ⟨_, LevelTower.IsUniverse.sort _, num_typedO⟩
      exact .types (RedTy.refl isNum) (RedTy.refl isNum)
        (.inr (.inr (.inr (.inr (.inr ⟨_, _, objectRoles_num, rfl⟩)))))
        (.inr (.inr (.inr (.inr (.inr ⟨_, _, objectRoles_num, rfl⟩)))))
        (.inductiveType objectRoles_num isNum)
  | .arr a b, m, Δ, formed => by
      have typeT : ∀ (type : HOL.Ty SetProfile.SetBase) {k : Nat} {Θ : Tower.Ctx k},
          Typed objectRules Θ (FormationSensitiveHOLInterface.typeAt SetProfile.types k type) U0 :=
        fun type => typeAt_typed tower_sub_objectRules declared_prop declared_num rfl type
      have isA :
          IsType objectRules Δ (FormationSensitiveHOLInterface.typeAt SetProfile.types m a) :=
        ⟨_, LevelTower.IsUniverse.sort _, typeT a⟩
      have isArr : IsType objectRules Δ
          (FormationSensitiveHOLInterface.typeAt SetProfile.types m (.arr a b)) :=
        ⟨_, LevelTower.IsUniverse.sort _, piU0 tower_sub_objectRules (typeT a) (typeT b)⟩
      exact .types (RedTy.refl isArr) (RedTy.refl isArr) (.inr (.inl ⟨_, _, rfl⟩))
        (.inr (.inl ⟨_, _, rfl⟩))
        (.pi isA (typeAt_types_refl a formed) (typeAt_types_refl b (.snoc formed isA)))

/-! ## Saturated constructor spines -/

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
theorem prop_neutral : Neutral objectRoles (.const propN : Tower.Tm m) :=
  .rigid (args := []) objectRoles_prop

section Facts

variable (facts : FormFacts objectRules objectRoles)
include facts

/-- **A dependent function type is usable at no type of codes.** -/
theorem pi_not_below_prop (formed : CtxFormed objectRules Δ) {A : Tower.Tm m}
    {B : Tower.Tm (m + 1)} (isPi : IsType objectRules Δ (.pi A B))
    (le : TypeLe objectRules Δ (.pi A B) (.const propN)) : False := by
  have isProp : IsType objectRules Δ (.const propN) := ⟨_, LevelTower.IsUniverse.sort _, prop_typedO⟩
  obtain ⟨A', B', e, -, -⟩ := Below.pi_source (S := objectSetting) facts
    (TypeLe.toBelow le isProp) formed (IsType.refl isPi)
  have neutral := (facts.forms e formed (.inr (.inr (.inr (.inr (.inl prop_neutral)))))
    (.inr (.inl ⟨_, _, rfl⟩))).neutral_left prop_neutral
  exact neutral.not_former.2.1 A' B' rfl

/-- **The type of codes is usable at no dependent function type.** -/
theorem prop_not_below_pi (formed : CtxFormed objectRules Δ) {A : Tower.Tm m}
    {B : Tower.Tm (m + 1)} (isPi : IsType objectRules Δ (.pi A B))
    (le : TypeLe objectRules Δ (.const propN) (.pi A B)) : False := by
  obtain ⟨A₀, B₀, e, -, -⟩ := Below.pi_inv (S := objectSetting) facts (TypeLe.toBelow le isPi)
    formed (IsType.refl isPi)
  have neutral := (facts.forms e formed (.inr (.inr (.inr (.inr (.inl prop_neutral)))))
    (.inr (.inl ⟨_, _, rfl⟩))).neutral_left prop_neutral
  exact neutral.not_former.2.1 A₀ B₀ rfl

/-- **The numbers are usable at no dependent function type.** -/
theorem num_not_below_pi (formed : CtxFormed objectRules Δ) {A : Tower.Tm m}
    {B : Tower.Tm (m + 1)} (isPi : IsType objectRules Δ (.pi A B))
    (le : TypeLe objectRules Δ numT (.pi A B)) : False := by
  obtain ⟨A₀, B₀, e, -, -⟩ := Below.pi_inv (S := objectSetting) facts (TypeLe.toBelow le isPi)
    formed (IsType.refl isPi)
  exact TypeEq.inductive_ne_pi facts objectRoles_num formed e

/-- A spine whose function part has the type of codes as its least type has no
argument. -/
theorem over_prop (formed : CtxFormed objectRules Δ) {g x : Tower.Tm m} {rest : List (Tower.Tm m)}
    {T : Tower.Tm m}
    (least : ∀ {X}, Typed objectRules Δ g X → TypeLe objectRules Δ (.const propN) X)
    (typing : Typed objectRules Δ (appSpine g (x :: rest)) T) : False := by
  obtain ⟨A, B, tg⟩ := Typed.spine_function rest typing
  exact prop_not_below_pi facts formed (Typed.isType (S := objectSetting) tg formed) (least tg)

/-- A spine whose function part has the numbers as its least type has no
argument. -/
theorem over_num (formed : CtxFormed objectRules Δ) {g x : Tower.Tm m} {rest : List (Tower.Tm m)}
    {T : Tower.Tm m} (least : ∀ {X}, Typed objectRules Δ g X → TypeLe objectRules Δ numT X)
    (typing : Typed objectRules Δ (appSpine g (x :: rest)) T) : False := by
  obtain ⟨A, B, tg⟩ := Typed.spine_function rest typing
  exact num_not_below_pi facts formed (Typed.isType (S := objectSetting) tg formed) (least tg)

/-- **A typed constructor spine at the type of codes is saturated**: it applies
its constructor to exactly as many arguments as the constructor declares. -/
theorem ctorSpine_saturated (formed : CtxFormed objectRules Δ) {k : DeclName}
    {args : List (Tower.Tm m)} {a : Nat}
    (typing : Typed objectRules Δ (appSpine (.const k) args) (.const propN))
    (role : objectRoles k = .constructor a) : args.length = a := by
  have univ := tower_sub_objectRules
  have hu : objectRules.isUniverse (.sort Tower.zero) := LevelTower.IsUniverse.sort _
  have propT : ∀ {k : Nat} {Θ : Tower.Ctx k}, Typed objectRules Θ (.const propN) U0 :=
    prop_typedO
  have typeT : ∀ (type : HOL.Ty SetProfile.SetBase) {k : Nat} {Θ : Tower.Ctx k},
      Typed objectRules Θ (FormationSensitiveHOLInterface.typeAt SetProfile.types k type) U0 :=
    fun type => typeAt_typed univ declared_prop declared_num rfl type
  have piProp : ∀ {k : Nat} {Θ : Tower.Ctx k}, IsType objectRules Θ
      (.pi (.const propN) (.const propN)) := ⟨_, hu, piU0 univ propT propT⟩
  rcases objectRoles_constructor role with ⟨rfl, rfl⟩ | ⟨type, found, rfl⟩ |
    ⟨type, found, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Implication declares two arguments.
    match args, typing with
    | [], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed .nil
          (.pi (.const propN) (.pi (.const propN) (.const propN))) declared_imp
          (σ := fun i => Fin.elim0 i) typing
        exact (pi_not_below_prop facts formed ⟨_, hu, piU0 univ propT (piU0 univ propT propT)⟩
          le).elim
    | [p], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil (.const propN)) (.pi (.const propN) (.const propN)) declared_imp
          (σ := consSub p fun i => Fin.elim0 i) typing
        exact (pi_not_below_prop facts formed piProp le).elim
    | [_, _], _ => rfl
    | p :: q :: r :: rest, typing =>
        refine (over_prop facts formed (g := appSpine (.const impN) [p, q]) (fun tg => ?_)
          typing).elim
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc (.snoc .nil (.const propN)) (.const propN)) (.const propN) declared_imp
          (σ := consSub q (consSub p fun i => Fin.elim0 i)) tg
        exact le
  · -- A quantifier declares one argument.
    obtain rfl := SetProfile.allInstance?_eq_some found
    match args, typing with
    | [], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed .nil
          (SetProfile.allType type) (declared_allName type) (σ := fun i => Fin.elim0 i) typing
        rw [SetProfile.allType, FormationSensitiveHOLInterface.typeAt_subst] at le
        exact (pi_not_below_prop facts formed ⟨_, hu, typeT (.arr (.arr type .prop) .prop)⟩
          le).elim
    | [_], _ => rfl
    | f :: x :: rest, typing =>
        refine (over_prop facts formed (g := appSpine (.const (SetProfile.allName type)) [f])
          (fun tg => ?_) typing).elim
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil (.pi (typeTerm type) (.const propN))) (.const propN)
          (declared_allName type) (σ := consSub f fun i => Fin.elim0 i) tg
        exact le
  · -- An equation declares two arguments.
    obtain rfl := SetProfile.eqInstance?_eq_some found
    match args, typing with
    | [], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed .nil
          (SetProfile.eqType type) (declared_eqName type) (σ := fun i => Fin.elim0 i) typing
        rw [SetProfile.eqType, FormationSensitiveHOLInterface.typeAt_subst] at le
        exact (pi_not_below_prop facts formed ⟨_, hu, typeT (.arr type (.arr type .prop))⟩
          le).elim
    | [x], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
          (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 (.arr type .prop))
          (declared_eqName type) (σ := consSub x fun i => Fin.elim0 i) typing
        have isArr : IsType objectRules Δ
            (FormationSensitiveHOLInterface.typeAt SetProfile.types m (.arr type .prop)) :=
          ⟨_, hu, typeT (.arr type .prop)⟩
        rw [FormationSensitiveHOLInterface.typeAt_subst] at le
        exact (pi_not_below_prop facts formed isArr le).elim
    | [_, _], _ => rfl
    | x :: y :: z :: rest, typing =>
        refine (over_prop facts formed (g := appSpine (.const (SetProfile.eqName type)) [x, y])
          (fun tg => ?_) typing).elim
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
            (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))
          (.const propN) (declared_eqName type)
          (σ := consSub y (consSub x fun i => Fin.elim0 i)) tg
        exact le
  · -- `zero` declares no argument.
    match args, typing with
    | [], _ => rfl
    | x :: rest, typing =>
        refine (over_num facts formed (g := .const zeroN) (fun tg => ?_) typing).elim
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed .nil numT
          declared_zero (σ := fun i => Fin.elim0 i) tg
        exact le
  · -- `suc` declares one argument.
    match args, typing with
    | [], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed .nil
          (.pi numT numT) declared_suc (σ := fun i => Fin.elim0 i) typing
        exact (pi_not_below_prop facts formed ⟨_, hu, piU0 univ num_typedO num_typedO⟩ le).elim
    | [_], _ => rfl
    | a :: x :: rest, typing =>
        refine (over_num facts formed (g := appSpine (.const sucN) [a]) (fun tg => ?_)
          typing).elim
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil numT) numT declared_suc (σ := consSub a fun i => Fin.elim0 i) tg
        exact le

end Facts

/-! ## The decoder along comparisons -/

/-- What a comparison of terms gives the decoder: codes compared at the type of
codes have decodings compared at the universe of proofs, and families of codes
compared at a dependent function type into the type of codes have decodings at
a fresh variable compared in the extended context. -/
abbrev DecodingsCompared (Δ : Tower.Ctx m) (t u A : Tower.Tm m) : Prop :=
  (A = .const propN → CtxFormed objectRules Δ →
    Algorithmic objectRules objectRoles
      (.terms Δ (.app (.const holdsN) t) (.app (.const holdsN) u) U0)) ∧
  (∀ D : Tower.Tm m, A = .pi D (.const propN) → CtxFormed objectRules (.snoc Δ D) →
    Algorithmic objectRules objectRoles (.terms (.snoc Δ D)
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
      (∃ V, RedTy objectRules objectRoles Δ V (.pi A B) ∧ ArgumentsCompared Δ f g V) ∧
      Algorithmic objectRules objectRoles (.terms Δ a b A) ∧ DecodingsCompared Δ a b A
  | .const k, u, U => u = .const k ∧ ∃ T, objectRules.constantType k = some T ∧ U = liftClosed T
  | t, u, _ => spineConst t = spineConst u

/-- Spines whose arguments are compared are headed by the same constant, if any. -/
theorem ArgumentsCompared.spineConst_eq {Δ : Tower.Ctx m} {t : Tower.Tm m} :
    ∀ {u U : Tower.Tm m}, ArgumentsCompared Δ t u U → spineConst t = spineConst u := by
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
  | .terms Γ t u A => DecodingsCompared Γ t u A
  | .termsW Γ t u A => DecodingsCompared Γ t u A
  | .spines Γ t u U => ArgumentsCompared Γ t u U
  | .spinesW Γ t u U => ∃ V, RedTy objectRules objectRoles Γ V U ∧ ArgumentsCompared Γ t u V

section Decoder

variable (facts : FormFacts objectRules objectRoles)
include facts

/-- Weak-head reduction of a typed term of the object package is a typed
reduction, given the facts. -/
theorem object_redTm (formed : CtxFormed objectRules Δ) {t t' T : Tower.Tm m}
    (red : WhRed objectRules objectRoles t t') (typing : Typed objectRules Δ t T) :
    RedTm objectRules objectRoles Δ t t' T := by
  obtain ⟨target, equal⟩ := object_reduces_preserve facts formed (WhRed.reduces red) typing
  exact ⟨red, typing, target, equal⟩

/-- Reducing a code reduces its decoding. -/
theorem holds_redTm (formed : CtxFormed objectRules Δ) {c c' : Tower.Tm m}
    (red : WhRed objectRules objectRoles c c') (typing : Typed objectRules Δ c (.const propN)) :
    RedTm objectRules objectRoles Δ (.app (.const holdsN) c) (.app (.const holdsN) c') U0 :=
  object_redTm facts formed (WhRed.scrutinee (before := []) (after := []) objectRoles_holds rfl red)
    (.appElim holds_typedO typing)

/-- **Codes compared as spines have compared decodings**: two weak-head normal
codes, compared as spines with their arguments' decodings compared, have
decodings compared at the universe of proofs. Neutral codes decode to neutral
types compared as spines headed by the decoder; constructor spines, saturated by
their typing, decode by one root step to dependent function types and identity
types whose parts are compared by the arguments' comparisons, over carriers
compared with themselves. -/
theorem spine_decodings (formed : CtxFormed objectRules Δ) {t u U : Tower.Tm m}
    (formT : SpineForm objectRoles t) (formU : SpineForm objectRoles u)
    (typedT : Typed objectRules Δ t (.const propN)) (typedU : Typed objectRules Δ u (.const propN))
    (spines : Algorithmic objectRules objectRoles (.spinesW Δ t u U))
    (compared : ∃ V, RedTy objectRules objectRoles Δ V U ∧ ArgumentsCompared Δ t u V) :
    Algorithmic objectRules objectRoles
      (.terms Δ (.app (.const holdsN) t) (.app (.const holdsN) u) U0) := by
  have hu : objectRules.isUniverse (.sort Tower.zero) := LevelTower.IsUniverse.sort _
  have isU0 : IsType objectRules Δ U0 := universe_isType (S := objectSetting) hu
  have typeT : ∀ (type : HOL.Ty SetProfile.SetBase) {k : Nat} {Θ : Tower.Ctx k},
      Typed objectRules Θ (FormationSensitiveHOLInterface.typeAt SetProfile.types k type) U0 :=
    fun type => typeAt_typed tower_sub_objectRules declared_prop declared_num rfl type
  have typesU : ∀ {k : Nat} {Θ : Tower.Ctx k} {A B : Tower.Tm k},
      Algorithmic objectRules objectRoles (.terms Θ A B U0) →
        Algorithmic objectRules objectRoles (.types Θ A B) :=
    fun d => Algorithmic.types_of_universe (S := objectSetting) hu d
  have decoded : ∀ {c c' D D' : Tower.Tm m},
      objectRules.computation.step (.app (.const holdsN) c) D →
      objectRules.computation.step (.app (.const holdsN) c') D' →
      Typed objectRules Δ c (.const propN) → Typed objectRules Δ c' (.const propN) →
      IsTypeForm objectRoles D → IsTypeForm objectRoles D' →
      Algorithmic objectRules objectRoles (.typesW Δ D D') →
      Algorithmic objectRules objectRoles
        (.terms Δ (.app (.const holdsN) c) (.app (.const holdsN) c') U0) := by
    intro c c' D D' step step' tc tc' _ _ d
    have red := object_redTm facts formed (.single (.root step)) (.appElim holds_typedO tc)
    have red' := object_redTm facts formed (.single (.root step')) (.appElim holds_typedO tc')
    exact .terms (RedTy.refl isU0) (.inl ⟨_, rfl⟩) red red' (.univ hu red.target red'.target d)
  obtain ⟨V, -, argsCompared⟩ := compared
  have sameHead := ArgumentsCompared.spineConst_eq argsCompared
  rcases formT with neutralT | ⟨k, arity, args, role, rfl⟩
  · -- Neutral codes decode to neutral types.
    have neutralU : Neutral objectRoles u := by
      rcases formU with neutralU | ⟨k, arity, args', role, rfl⟩
      · exact neutralU
      · exact absurd role (neutralT.spineConst_not_constructor
          (sameHead.trans (spineConst_appSpine args' _)))
    have holdsT : Typed objectRules Δ (.app (.const holdsN) t) U0 := .appElim holds_typedO typedT
    have holdsU : Typed objectRules Δ (.app (.const holdsN) u) U0 := .appElim holds_typedO typedU
    have isProp : IsType objectRules Δ (.const propN) := ⟨_, hu, prop_typedO⟩
    have codes : Algorithmic objectRules objectRoles (.terms Δ t u (.const propN)) :=
      .terms (RedTy.refl isProp) (.inr (.inr (.inr (.inr (.inl prop_neutral))))) (RedTm.refl typedT)
        (RedTm.refl typedU) (.spine (.inr (.inl prop_neutral)) (.inl neutralT) (.inl neutralU)
          typedT typedU spines)
    have neutral : ∀ {c : Tower.Tm m}, Neutral objectRoles c →
        Neutral objectRoles (.app (.const holdsN) c) :=
      fun n => Neutral.stuck_single (before := []) (after := []) objectRoles_holds rfl n
    exact .terms (RedTy.refl isU0) (.inl ⟨_, rfl⟩) (RedTm.refl holdsT) (RedTm.refl holdsU)
      (.univ hu holdsT holdsU (.neutralTypes (neutral neutralT) (neutral neutralU) hu
        (.spinesW (.app (.spinesW (.const declared_holds holds_typedO)
          (RedTy.refl (Typed.isType (S := objectSetting) holds_typedO formed))
          (.inr (.inl ⟨_, _, rfl⟩))) codes) (RedTy.refl isU0) (.inl ⟨_, rfl⟩))))
  · -- Constructor spines decode by one root step.
    have saturated := ctorSpine_saturated facts formed typedT role
    rcases objectRoles_constructor role with ⟨rfl, rfl⟩ | ⟨type, found, rfl⟩ |
      ⟨type, found, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- Implication decodes to a dependent function type of decodings.
      match args, saturated, typedT, argsCompared with
      | [p, q], _, typedT, argsCompared =>
        obtain ⟨g, b, A, B, rfl, -, ⟨V₁, red₁, args₁⟩, dq, hq⟩ := argsCompared
        obtain ⟨g', b', A', B', rfl, rfl, ⟨V₂, red₂, args₂⟩, dp, hp⟩ := args₁
        obtain ⟨rfl, T, declared, rfl⟩ := args₂
        obtain rfl : T = programCodes.impType := Option.some.inj (declared.symm.trans declared_imp)
        have e₂ : (Tm.pi A' B' : Tower.Tm m) =
            .pi (.const propN) (.pi (.const propN) (.const propN)) :=
          WhRed.eq_of_whnf (S := objectSetting) (pi_whnf objectShape _ _) red₂.red
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₂
        have e₁ : (Tm.pi A B : Tower.Tm m) = .pi (.const propN) (.const propN) :=
          WhRed.eq_of_whnf (S := objectSetting) (pi_whnf objectShape _ _) red₁.red
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₁
        have tp := dp.terms_typed.1
        exact decoded (.inr (DecoderStep.imp p q)) (.inr (DecoderStep.imp b' b)) typedT typedU
          (.inr (.inl ⟨_, _, rfl⟩)) (.inr (.inl ⟨_, _, rfl⟩))
          (.pi ⟨_, hu, .appElim holds_typedO tp⟩ (typesU (hp.1 rfl formed))
            (Algorithmic.rename (typesU (hq.1 rfl formed)) (CtxRen.wk Δ _)))
    · -- A quantifier decodes to a dependent function type over its carrier.
      obtain rfl := SetProfile.allInstance?_eq_some found
      match args, saturated, typedT, argsCompared with
      | [f], _, typedT, argsCompared =>
        obtain ⟨g, b, A, B, rfl, -, ⟨V₁, red₁, args₁⟩, df, hf⟩ := argsCompared
        obtain ⟨rfl, T, declared, rfl⟩ := args₁
        obtain rfl : T = SetProfile.allType type :=
          Option.some.inj (declared.symm.trans (declared_allName type))
        have e₁ : (Tm.pi A B : Tower.Tm m) =
            .pi (.pi (FormationSensitiveHOLInterface.typeAt SetProfile.types m type)
              (.const propN)) (.const propN) := by
          rw [WhRed.eq_of_whnf (S := objectSetting) (pi_whnf objectShape _ _) red₁.red]
          exact congrArg₂ Tm.pi (FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ _)
            (FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ _)
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₁
        have carrier : programCodes.decoders.allCarrier (SetProfile.allName type) =
            some (typeTerm type) := by
          change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = _
          rw [found]
          rfl
        have isCarrier : IsType objectRules Δ
            (FormationSensitiveHOLInterface.typeAt SetProfile.types m type) := ⟨_, hu, typeT type⟩
        have body := typesU (hf.2 _ rfl (.snoc formed isCarrier))
        have step := DecoderStep.all carrier f
        have step' := DecoderStep.all carrier b
        rw [typeTerm_lift] at step step'
        exact decoded (.inr step) (.inr step') typedT typedU (.inr (.inl ⟨_, _, rfl⟩))
          (.inr (.inl ⟨_, _, rfl⟩)) (.pi isCarrier (typeAt_types_refl type formed) body)
    · -- An equation decodes to an identity type of its carrier.
      obtain rfl := SetProfile.eqInstance?_eq_some found
      match args, saturated, typedT, argsCompared with
      | [x, y], _, typedT, argsCompared =>
        obtain ⟨g, b, A, B, rfl, -, ⟨V₁, red₁, args₁⟩, dy, -⟩ := argsCompared
        obtain ⟨g', b', A', B', rfl, rfl, ⟨V₂, red₂, args₂⟩, dx, -⟩ := args₁
        obtain ⟨rfl, T, declared, rfl⟩ := args₂
        obtain rfl : T = SetProfile.eqType type :=
          Option.some.inj (declared.symm.trans (declared_eqName type))
        have e₂ : (Tm.pi A' B' : Tower.Tm m) =
            .pi (FormationSensitiveHOLInterface.typeAt SetProfile.types m type)
              (.pi (FormationSensitiveHOLInterface.typeAt SetProfile.types (m + 1) type)
                (.const propN)) := by
          rw [WhRed.eq_of_whnf (S := objectSetting) (pi_whnf objectShape _ _) red₂.red]
          exact congrArg₂ Tm.pi (FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ _)
            (FormationSensitiveHOLInterface.typeAt_rename SetProfile.types _ _)
        obtain ⟨rfl, rfl⟩ := Tm.pi.inj e₂
        have e₁ : (Tm.pi A B : Tower.Tm m) =
            .pi (FormationSensitiveHOLInterface.typeAt SetProfile.types m type) (.const propN) := by
          rw [WhRed.eq_of_whnf (S := objectSetting) (pi_whnf objectShape _ _) red₁.red]
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
        exact decoded (.inr step) (.inr step') typedT typedU
          (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩)))) (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))
          (.id (typeAt_types_refl type formed) dx dy)
    · -- `zero` has no typing at the type of codes.
      match args, saturated, typedT with
      | [], _, typedT =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed .nil numT
          declared_zero (σ := fun i => Fin.elim0 i) typedT
        exact (num_not_below_prop facts formed le).elim
    · -- Nor has `suc` applied to an argument.
      match args, saturated, typedT with
      | [a], _, typedT =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil numT) numT declared_suc (σ := consSub a fun i => Fin.elim0 i) typedT
        exact (num_not_below_prop facts formed le).elim

/-- **Every comparison of the algorithmic equality of the object package gives
the decoder what it needs**, given the facts: compared codes have compared
decodings, compared families of codes have compared decodings at a fresh
variable, and compared spines have compared arguments. By induction on the
derivation: a comparison of terms reduces the codes, and reducing a code reduces
its decoding; a family is compared at a fresh variable, exactly where its
decoding needs it; codes in weak-head normal form are compared as spines. -/
theorem algorithmic_decodings {st : AlgorithmicStatement Tower.Head}
    (derivation : Algorithmic objectRules objectRoles st) : DecodingsAt st := by
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
        obtain rfl := WhRed.eq_of_whnf (S := objectSetting) (prop_neutral.whnf objectShape) rA.red
        exact Algorithmic.terms_expand (holds_redTm facts formed rt.red rt.source)
          (holds_redTm facts formed ru.red ru.source) (ih.1 rfl formed)
      · subst e
        obtain rfl := WhRed.eq_of_whnf (S := objectSetting) (pi_whnf objectShape _ _) rA.red
        have fresh : ∀ {f f' : Tower.Tm _},
            RedTm objectRules objectRoles _ f f' (.pi D (.const propN)) →
            RedTm objectRules objectRoles _
              (.app (.const holdsN) (.app (Presentation.rename wk f) (.var 0)))
              (.app (.const holdsN) (.app (Presentation.rename wk f') (.var 0))) U0 :=
          fun red => holds_redTm facts formed ((red.red.rename wk).app (.var 0))
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
        exact spine_decodings facts formed formT formU typedT typedU spines ih
      · subst e
        exact absurd sA SpineType.not_pi
  | var i => exact rfl
  | const declared _ => exact ⟨rfl, _, declared, rfl⟩
  | app _ da ihF iha => exact ⟨_, _, _, _, rfl, rfl, ihF, da, iha⟩
  | fst _ ih =>
      obtain ⟨V, -, compared⟩ := ih
      have sameHead := ArgumentsCompared.spineConst_eq compared
      exact sameHead
  | snd _ ih =>
      obtain ⟨V, -, compared⟩ := ih
      have sameHead := ArgumentsCompared.spineConst_eq compared
      exact sameHead
  | spinesW _ rU _ ih => exact ⟨_, rU, ih⟩

/-- **The decoder is a congruence of the algorithmic equality of the object
package**, given the facts: codes it relates at the type of codes have decodings
it relates at the universe of proofs. -/
theorem object_holdsCongruence :
    HoldsCongruence (algorithmic objectRules objectRoles) programCodes := by
  intro n Γ c c' related
  exact ⟨objectDeclarative_holdsCongruence related.1, fun _ _ _ cr formed =>
    (algorithmic_decodings facts (related.2 cr formed)).1 rfl formed⟩

/-- **Conversion completeness for the object package**, given the facts and the
lifting of spine comparisons: derivably equal terms of a formed context are
algorithmically equal. The conversion model over the algorithmic equality is
sound for the object package, and escape into it is completeness. -/
theorem object_algorithmicComplete (lift : SpineLift objectSetting) :
    AlgorithmicComplete objectRules objectRoles := by
  intro n Γ t u A formed equal
  have related := object_equal_escapeN facts (object_algorithmic_laws facts lift)
    (algorithmic_convTm_reduce (S := objectSetting)) (object_holdsCongruence facts) formed equal
  have d := related.2 (CtxRen.id Γ) formed
  rw [rename_id, rename_id, rename_id] at d
  exact d

end Decoder

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
