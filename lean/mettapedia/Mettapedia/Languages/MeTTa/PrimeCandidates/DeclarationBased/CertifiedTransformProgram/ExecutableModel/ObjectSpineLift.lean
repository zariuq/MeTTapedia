import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectAlgorithmic
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelInstances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NormalizingLift

/-!
# Spine comparisons lift in the object package

Given the facts about the weak-head forms of its types, spine comparisons of
the object package lift to comparisons at the type (`object_spineLift`), so
derivably equal terms of a formed context are algorithmically equal
(`object_algorithmicComplete_of_facts`). The lifting is by strong normalization
of the types of the object package (`objectRules_sn`), with no reducibility
model, from three properties of the package:

* **substituting neutral terms creates no weak-head redex**
  (`object_neutralReflecting`): its computing constants, the decoder
  included, inspect only constructor forms, and its root computations, the
  equations, recursors, the identity eliminator and the decoding of codes,
  reflect substitutions of neutral terms;
* **liftable values have the shapes of their types** (`object_liftableForms`),
  given the facts: a constructor spine is typed at a dependent function type
  while it lacks arguments, and at the type of codes or at the numbers once
  saturated (`ctorSpine_types`), so it is never a value of a universe or of a
  dependent pair type; the numbers are a type of the lowest universe, so they
  are values only of universes;
* its types are strongly normalizing (`objectRules_type_sn`).

The substituted terms must be neutral: the decoder at a variable is weak-head
normal, while its instance at a code of implication decodes
(`holds_var_imp_step`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
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

/-! ## Substituting neutral terms creates no weak-head redex -/

/-- The root computations of the executable package reflect substitutions of
neutral terms under the roles of the object package. -/
theorem rules_reflectsNeutral : RootReflectsNeutral objectRoles rules.computation := by
  have filtered : computations.filter (fun entry => (fun _ => true) entry.1) = computations :=
    List.filter_eq_self.mpr fun _ _ => rfl
  change RootReflectsNeutral objectRoles
    (RootComputation.unionAll (computations.filter fun entry => (fun _ => true) entry.1))
  rw [filtered]
  refine RootReflectsNeutral.unionAll fun entry mem => ?_
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact iotaComputation_reflectsNeutral objectRoles_num objectConstructorsDeclared
  · exact recursionComputation_reflectsNeutral _ objectRoles_num objectConstructorsDeclared _ _ _ _
  · exact recursionComputation_reflectsNeutral _ objectRoles_num objectConstructorsDeclared _ _ _ _
  · exact eliminatorComputation_reflectsNeutral _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact recursionComputation_reflectsNeutral _ objectRoles_num objectConstructorsDeclared _ _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _

/-- The root computation of the object package reflects substitutions of
neutral terms. -/
theorem objectRules_reflectsNeutral : RootReflectsNeutral objectRoles objectRules.computation :=
  RootReflectsNeutral.union rules_reflectsNeutral
    (decoderComputation_reflectsNeutral objectDecoderRoles)

/-- **Substituting neutral terms creates no weak-head redex in the object
package.** -/
theorem object_neutralReflecting : NeutralReflecting objectRules objectRoles :=
  NeutralReflecting.of_constructors objectShape objectRoles_onlyConstructors
    objectRules_reflectsNeutral

/-! ## The types of constructor spines -/

section Facts

variable (facts : FormFacts objectRules objectRoles)
include facts

/-- **The types of a typed constructor spine of the object package**, given the
facts: a spine that applies its constructor to fewer arguments than it declares
is usable at a dependent function type, and a saturated one is usable at the
type of codes or at the numbers. -/
theorem ctorSpine_types (formed : CtxFormed objectRules Δ) {k : DeclName}
    {args : List (Tower.Tm m)} {a : Nat} {T : Tower.Tm m}
    (typing : Typed objectRules Δ (appSpine (.const k) args) T)
    (role : objectRoles k = .constructor a) :
    (args.length < a ∧ ∃ A B, TypeLe objectRules Δ (.pi A B) T) ∨
      TypeLe objectRules Δ (.const propN) T ∨ TypeLe objectRules Δ numT T := by
  rcases objectRoles_constructor role with ⟨rfl, rfl⟩ | ⟨type, found, rfl⟩ |
    ⟨type, found, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Implication declares two arguments.
    match args, typing with
    | [], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed .nil
          (.pi (.const propN) (.pi (.const propN) (.const propN))) declared_imp
          (σ := fun i => Fin.elim0 i) typing
        exact .inl ⟨Nat.zero_lt_two, _, _, le⟩
    | [p], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil (.const propN)) (.pi (.const propN) (.const propN)) declared_imp
          (σ := consSub p fun i => Fin.elim0 i) typing
        exact .inl ⟨Nat.one_lt_two, _, _, le⟩
    | [p, q], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc (.snoc .nil (.const propN)) (.const propN)) (.const propN) declared_imp
          (σ := consSub q (consSub p fun i => Fin.elim0 i)) typing
        exact .inr (.inl le)
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
        exact .inl ⟨Nat.zero_lt_one, _, _, le⟩
    | [f], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil (.pi (typeTerm type) (.const propN))) (.const propN)
          (declared_allName type) (σ := consSub f fun i => Fin.elim0 i) typing
        exact .inr (.inl le)
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
        exact .inl ⟨Nat.zero_lt_two, _, _, le⟩
    | [x], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
          (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 (.arr type .prop))
          (declared_eqName type) (σ := consSub x fun i => Fin.elim0 i) typing
        rw [FormationSensitiveHOLInterface.typeAt_subst] at le
        exact .inl ⟨Nat.one_lt_two, _, _, le⟩
    | [x, y], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
            (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))
          (.const propN) (declared_eqName type)
          (σ := consSub y (consSub x fun i => Fin.elim0 i)) typing
        exact .inr (.inl le)
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
    | [], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed .nil numT
          declared_zero (σ := fun i => Fin.elim0 i) typing
        exact .inr (.inr le)
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
        exact .inl ⟨Nat.zero_lt_one, _, _, le⟩
    | [x], typing =>
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil numT) numT declared_suc (σ := consSub x fun i => Fin.elim0 i) typing
        exact .inr (.inr le)
    | x :: y :: rest, typing =>
        refine (over_num facts formed (g := appSpine (.const sucN) [x]) (fun tg => ?_)
          typing).elim
        obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := objectSetting) facts formed
          (.snoc .nil numT) numT declared_suc (σ := consSub x fun i => Fin.elim0 i) tg
        exact le

/-- **Liftable values of the object package have the shapes of their types**,
given the facts. -/
theorem object_liftableForms : LiftableForms objectSetting where
  constructor_universe := by
    intro n Γ k arity args u formed role hu typing
    have isU : IsType objectRules Γ (.head u) := Typed.isType (S := objectSetting) typing formed
    have target := fun {X : Tower.Tm n} (le : TypeLe objectRules Γ X (.head u)) =>
      Below.universe_target (S := objectSetting) facts (TypeLe.toBelow le isU) formed hu
        (IsType.refl isU)
    rcases ctorSpine_types facts formed typing role with ⟨-, A, B, le⟩ | le | le
    · obtain ⟨v, -, e, -⟩ := target le
      exact TypeEq.pi_ne_head facts formed e
    · obtain ⟨v, -, e, -⟩ := target le
      exact ((facts.forms e formed (.inr (.inr (.inr (.inr (.inl prop_neutral)))))
        (.inl ⟨v, rfl⟩)).neutral_left prop_neutral).not_former.1 v rfl
    · obtain ⟨v, -, e, -⟩ := target le
      exact TypeEq.inductive_ne_head facts objectRoles_num formed e
  constructor_pi := by
    intro n Γ k arity args A B formed role typing
    have isPi : IsType objectRules Γ (.pi A B) := Typed.isType (S := objectSetting) typing formed
    rcases ctorSpine_types facts formed typing role with ⟨short, -⟩ | le | le
    · exact short
    · exact (prop_not_below_pi facts formed isPi le).elim
    · exact (num_not_below_pi facts formed isPi le).elim
  constructor_sigma := by
    intro n Γ k arity args A B formed role typing
    have isSigma : IsType objectRules Γ (.sigma A B) :=
      Typed.isType (S := objectSetting) typing formed
    have inv := fun {X : Tower.Tm n} (le : TypeLe objectRules Γ X (.sigma A B)) =>
      Below.sigma_inv (S := objectSetting) facts (TypeLe.toBelow le isSigma) formed
        (IsType.refl isSigma)
    rcases ctorSpine_types facts formed typing role with ⟨-, A', B', le⟩ | le | le
    · obtain ⟨A₀, B₀, e, -, -⟩ := inv le
      exact TypeEq.pi_ne_sigma facts formed e
    · obtain ⟨A₀, B₀, e, -, -⟩ := inv le
      exact ((facts.forms e formed (.inr (.inr (.inr (.inr (.inl prop_neutral)))))
        (.inr (.inr (.inl ⟨_, _, rfl⟩)))).neutral_left prop_neutral).not_former.2.2.1 _ _ rfl
    · obtain ⟨A₀, B₀, e, -, -⟩ := inv le
      exact TypeEq.inductive_ne_sigma facts objectRoles_num formed e
  inductive_universe := by
    intro n Γ T ctors A formed role typing form
    obtain ⟨rfl, -⟩ := objectRoles_inductive role
    obtain ⟨type, u, declared, -, -, le⟩ := Typed.generation typing
    obtain rfl : type = U0 := Option.some.inj (declared.symm.trans declared_num)
    have hu0 : objectRules.isUniverse (.sort Tower.zero) := Tower.IsUniverse.sort _
    have isA : IsType objectRules Γ A := Typed.isType (S := objectSetting) typing formed
    have isU0 : IsType objectRules Γ U0 := universe_isType (S := objectSetting) hu0
    obtain ⟨v, hv, eA, -⟩ := Below.universe_source (S := objectSetting) facts
      (TypeLe.toBelow le isA) formed hu0 (IsType.refl isU0)
    obtain ⟨h', rfl, same⟩ := (facts.forms eA.symm formed (.inl ⟨v, rfl⟩) form).head_left
    exact ⟨h', rfl, (HeadSame.level objectLevels same).1.mp hv⟩

end Facts

/-! ## The lifting and completeness -/

/-- The types of a formed context of the object package are strongly
normalizing. -/
theorem objectRules_type_sn {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}
    (formed : CtxFormed objectRules Γ) (isA : IsType objectRules Γ A) :
    StrongNormalization.SN objectRules A := by
  obtain ⟨u, -, typed⟩ := isA
  exact (objectRules_sn formed typed).1

/-- **Spine comparisons lift in the object package**, given the facts about the
weak-head forms of its types. -/
theorem object_spineLift (facts : FormFacts objectRules objectRoles) :
    SpineLift objectSetting :=
  SpineLift.ofNormalizing (S := objectSetting) facts (objectRules_roots facts) objectRules_heads
    objectRules_algebra (object_liftableForms facts) object_neutralReflecting
    fun formed isA => objectRules_type_sn formed isA

/-- **Conversion completeness for the object package**, given the facts about
the weak-head forms of its types: derivably equal terms of a formed context are
algorithmically equal. -/
theorem object_algorithmicComplete_of_facts (facts : FormFacts objectRules objectRoles) :
    AlgorithmicComplete objectRules objectRoles :=
  object_algorithmicComplete facts (object_spineLift facts)

/-! ## Controls: the substituted terms must be neutral -/

/-- The decoder at a variable is neutral. -/
theorem holds_var_neutral : Neutral objectRoles (.app (.const holdsN) (.var 0) : Tower.Tm 1) :=
  Neutral.stuck_single (before := []) (after := []) objectRoles_holds rfl (.var (0 : Fin 1))

/-- **Substituting a term that is not neutral can create a redex**: the decoder
at a variable is weak-head normal, while its instance at a code of implication
decodes. -/
theorem holds_var_imp_step (p q : Tower.Tm 0) :
    Whnf objectRules objectRoles (.app (.const holdsN) (.var 0) : Tower.Tm 1) ∧
      ¬ Neutral objectRoles (appSpine (.const impN) [p, q]) ∧
        WhStep objectRules objectRoles
          (Presentation.subst (fun _ : Fin 1 => appSpine (.const impN) [p, q])
            (.app (.const holdsN) (.var 0)))
          (.pi (.app (.const holdsN) p) (.app (.const holdsN) (Presentation.rename wk q))) :=
  ⟨holds_var_neutral.whnf objectShape,
    fun neutral => neutral.not_canonical (.inr ⟨impN, 2, [p, q], objectRoles_imp, rfl⟩),
    .root (.inr (DecoderStep.imp p q))⟩

end ConvRules
end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
