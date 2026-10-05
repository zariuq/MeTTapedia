import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectAlgorithmic
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SNValueSound
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LevelInstances
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.NormalizingLift

/-!
# Spine comparisons lift in the package of an extension

Given the facts about the weak-head forms of its types, spine comparisons of the package of an
extension of the transport value model (`TExtension`) lift to comparisons at the type
(`real_spineLift`), so derivably equal terms of a formed context are algorithmically equal
(`real_algorithmicComplete_of_facts`). The lifting is by strong normalization of the types of
the package, with no reducibility model, from three properties of the package:

* **substituting neutral terms creates no weak-head redex**
  (`real_neutralReflecting`): its computing constants, the decoder
  included, inspect only constructor forms, and its root computations, the
  equations, recursors, the identity eliminator and the decoding of codes,
  reflect substitutions of neutral terms; at the new names this is an input;
* **liftable values have the shapes of their types** (`real_liftableForms`),
  given the facts: a constructor spine is typed at a dependent function type
  while it lacks arguments, and at the type of codes or at an inductive type
  once saturated (`ctorSpine_types`), so it is never a value of a universe or of a
  dependent pair type; an inductive type is a type of a universe, so it is a value only of
  universes;
* its types are strongly normalizing: an input, which the object package has
  (`objectRules_type_sn`).

The object package is the extension by no name: its spine comparisons lift and it is complete
given the facts alone (`object_spineLift`, `object_algorithmicComplete_of_facts`).

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
neutral terms under roles with its numbers and their declared constructors. -/
theorem rules_reflectsNeutral {ρ : Roles Tower.Head}
    (num : ρ numN = .inductive ctors) (declared : ConstructorsDeclared ρ) :
    RootReflectsNeutral ρ rules.computation := by
  have filtered : computations.filter (fun entry => (fun _ => true) entry.1) = computations :=
    List.filter_eq_self.mpr fun _ _ => rfl
  change RootReflectsNeutral ρ
    (RootComputation.unionAll (computations.filter fun entry => (fun _ => true) entry.1))
  rw [filtered]
  refine RootReflectsNeutral.unionAll fun entry mem => ?_
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact iotaComputation_reflectsNeutral num declared
  · exact recursionComputation_reflectsNeutral _ num declared _ _ _ _
  · exact recursionComputation_reflectsNeutral _ num declared _ _ _ _
  · exact eliminatorComputation_reflectsNeutral _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact recursionComputation_reflectsNeutral _ num declared _ _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _
  · exact definitionComputation_reflectsNeutral _ _ _

section Extension

variable (X : TExtension)

/-- The root computation of the object package reflects substitutions of neutral terms under
the roles of the package of an extension. -/
theorem objectRules_reflectsNeutral :
    RootReflectsNeutral X.realRoles objectRules.computation :=
  RootReflectsNeutral.union (rules_reflectsNeutral X.realRoles_num X.realDeclared)
    (decoderComputation_reflectsNeutral X.realDecoderRoles)

/-- **Substituting neutral terms creates no weak-head redex in the package of an extension**,
when its computing new constants inspect only constructor forms and its root steps at new
names reflect substitutions of neutral terms. -/
theorem real_neutralReflecting
    (newOnly : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree}, c ∈ X.names →
      X.realRoles c = .computes arity inspect → inspect.OnlyConstructors)
    (newReflects : ∀ ⦃n k : Nat⦄ ⦃σ : Sub Tower.Head n k⦄, NeutralSub X.realRoles σ →
      ∀ ⦃c : DeclName⦄ ⦃args : List (Tower.Tm n)⦄ ⦃u : Tower.Tm k⦄, c ∈ X.names →
        X.realRules.computation.step (appSpine (.const c) (args.map (Presentation.subst σ))) u →
          ∃ t', X.realRules.computation.step (appSpine (.const c) args) t') :
    NeutralReflecting X.realRules X.realRoles := by
  refine NeutralReflecting.of_constructors X.realShape (fun {c arity inspect} role => ?_)
    (fun n k σ neutral c args u step => ?_)
  · by_cases new : c ∈ X.names
    · exact newOnly new role
    · exact objectRoles_onlyConstructors ((X.realOld new).symm.trans role)
  · by_cases new : c ∈ X.names
    · exact newReflects neutral new step
    · obtain ⟨t', step'⟩ := objectRules_reflectsNeutral X neutral (X.realStepOld new step)
      exact ⟨t', X.realSub.computation step'⟩

/-! ## The types of constructor spines -/

section Facts

variable (facts : FormFacts X.realRules X.realRoles)
include facts

/-- **The types of a typed constructor spine of the package of an extension**, given the
facts: a spine that applies its constructor to fewer arguments than it declares is usable at
a dependent function type, and a saturated one is usable at the type of codes or at an
inductive type. -/
theorem ctorSpine_types (formed : CtxFormed X.realRules Δ) {k : DeclName}
    {args : List (Tower.Tm m)} {a : Nat} {T : Tower.Tm m}
    (typing : Typed X.realRules Δ (appSpine (.const k) args) T)
    (role : X.realRoles k = .constructor a) :
    (args.length < a ∧ ∃ A B, TypeLe X.realRules Δ (.pi A B) T) ∨
      TypeLe X.realRules Δ (.const propN) T ∨
        ∃ I cs, X.realRoles I = .inductive cs ∧ TypeLe X.realRules Δ (.const I) T := by
  have inductiveCase : ∀ {I : DeclName}
      {cs : List (DeclName × List (Normalization.Field Tower.Head))}
      (roleI : X.realRoles I = .inductive cs) (e : (i : Nat) → Tower.Tm i) {N : Nat},
      N = a → X.realRules.constantType k =
        some (TelescopeAbstraction.closeType (ofEntries e N) (.const I)) →
      (args.length < a ∧ ∃ A B, TypeLe X.realRules Δ (.pi A B) T) ∨
        TypeLe X.realRules Δ (.const propN) T ∨
          ∃ I cs, X.realRoles I = .inductive cs ∧ TypeLe X.realRules Δ (.const I) T := by
    intro I cs roleI e N hN declared
    subst hN
    rcases inductiveSpine_types X facts formed roleI e declared typing with
      ⟨short, A, B, -, le⟩ | ⟨-, le⟩
    · exact .inl ⟨short, A, B, le⟩
    · exact .inr (.inr ⟨I, cs, roleI, le⟩)
  rcases realRoles_constructor X role with ⟨-, role⟩ | ⟨-, I, fs, declared, len, -, cs, roleI⟩
  · rcases objectRoles_constructor role with ⟨rfl, rfl⟩ | ⟨type, found, rfl⟩ |
      ⟨type, found, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- Implication declares two arguments.
      match args, typing with
      | [], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed .nil
            (.pi (.const propN) (.pi (.const propN) (.const propN)))
            (X.realSub.constantType declared_imp) (σ := fun i => Fin.elim0 i) typing
          exact .inl ⟨Nat.zero_lt_two, _, _, le⟩
      | [p], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc .nil (.const propN)) (.pi (.const propN) (.const propN))
            (X.realSub.constantType declared_imp) (σ := consSub p fun i => Fin.elim0 i) typing
          exact .inl ⟨Nat.one_lt_two, _, _, le⟩
      | [p, q], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc (.snoc .nil (.const propN)) (.const propN)) (.const propN)
            (X.realSub.constantType declared_imp)
            (σ := consSub q (consSub p fun i => Fin.elim0 i)) typing
          exact .inr (.inl le)
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
          exact .inl ⟨Nat.zero_lt_one, _, _, le⟩
      | [f], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc .nil (.pi (typeTerm type) (.const propN))) (.const propN)
            (X.realSub.constantType (declared_allName type)) (σ := consSub f fun i => Fin.elim0 i)
            typing
          exact .inr (.inl le)
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
          exact .inl ⟨Nat.zero_lt_two, _, _, le⟩
      | [x], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
            (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 (.arr type .prop))
            (X.realSub.constantType (declared_eqName type)) (σ := consSub x fun i => Fin.elim0 i)
            typing
          rw [FormationSensitiveHOLInterface.typeAt_subst] at le
          exact .inl ⟨Nat.one_lt_two, _, _, le⟩
      | [x, y], typing =>
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
              (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))
            (.const propN) (X.realSub.constantType (declared_eqName type))
            (σ := consSub y (consSub x fun i => Fin.elim0 i)) typing
          exact .inr (.inl le)
      | x :: y :: z :: rest, typing =>
          refine (over_prop X facts formed
            (g := appSpine (.const (SetProfile.eqName type)) [x, y]) (fun tg => ?_) typing).elim
          obtain ⟨-, -, le⟩ := Typed.telescope_inv (S := realSetting X) facts formed
            (.snoc (.snoc .nil (FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type))
              (FormationSensitiveHOLInterface.typeAt SetProfile.types 1 type))
            (.const propN) (X.realSub.constantType (declared_eqName type))
            (σ := consSub y (consSub x fun i => Fin.elim0 i)) tg
          exact le
    · -- `zero` declares no argument.
      exact inductiveCase X.realRoles_num (ctorEntry numN []) (N := 0) rfl
        (X.realSub.constantType declared_zero)
    · -- `suc` declares one argument.
      exact inductiveCase X.realRoles_num (ctorEntry numN [.recursive]) (N := 1) rfl
        (X.realSub.constantType declared_suc)
  · -- A new constructor declares its fields.
    exact inductiveCase roleI (ctorEntry I fs) len declared

/-- **Liftable values of the package of an extension have the shapes of their types**, given
the facts. -/
theorem real_liftableForms : LiftableForms (realSetting X) where
  constructor_universe := by
    intro n Γ k arity args u formed role hu typing
    have isU : IsType X.realRules Γ (.head u) := Typed.isType (S := realSetting X) typing formed
    have target := fun {Y : Tower.Tm n} (le : TypeLe X.realRules Γ Y (.head u)) =>
      Below.universe_target (S := realSetting X) facts (TypeLe.toBelow le isU) formed hu
        (IsType.refl isU)
    rcases ctorSpine_types X facts formed typing role with ⟨-, A, B, le⟩ | le | ⟨I, cs, roleI, le⟩
    · obtain ⟨v, -, e, -⟩ := target le
      exact TypeEq.pi_ne_head facts formed e
    · obtain ⟨v, -, e, -⟩ := target le
      exact ((facts.forms e formed (.inr (.inr (.inr (.inr (.inl (prop_neutral X))))))
        (.inl ⟨v, rfl⟩)).neutral_left (prop_neutral X)).not_former.1 v rfl
    · obtain ⟨v, -, e, -⟩ := target le
      exact TypeEq.inductive_ne_head facts roleI formed e
  constructor_pi := by
    intro n Γ k arity args A B formed role typing
    have isPi : IsType X.realRules Γ (.pi A B) := Typed.isType (S := realSetting X) typing formed
    rcases ctorSpine_types X facts formed typing role with ⟨short, -⟩ | le | ⟨I, cs, roleI, le⟩
    · exact short
    · exact (prop_not_below_pi X facts formed isPi le).elim
    · exact (inductive_not_below_pi X facts formed roleI isPi le).elim
  constructor_sigma := by
    intro n Γ k arity args A B formed role typing
    have isSigma : IsType X.realRules Γ (.sigma A B) :=
      Typed.isType (S := realSetting X) typing formed
    have inv := fun {Y : Tower.Tm n} (le : TypeLe X.realRules Γ Y (.sigma A B)) =>
      Below.sigma_inv (S := realSetting X) facts (TypeLe.toBelow le isSigma) formed
        (IsType.refl isSigma)
    rcases ctorSpine_types X facts formed typing role with
      ⟨-, A', B', le⟩ | le | ⟨I, cs, roleI, le⟩
    · obtain ⟨A₀, B₀, e, -, -⟩ := inv le
      exact TypeEq.pi_ne_sigma facts formed e
    · obtain ⟨A₀, B₀, e, -, -⟩ := inv le
      exact ((facts.forms e formed (.inr (.inr (.inr (.inr (.inl (prop_neutral X))))))
        (.inr (.inr (.inl ⟨_, _, rfl⟩)))).neutral_left (prop_neutral X)).not_former.2.2.1 _ _ rfl
    · obtain ⟨A₀, B₀, e, -, -⟩ := inv le
      exact TypeEq.inductive_ne_sigma facts roleI formed e
  inductive_universe := by
    intro n Γ T ctors A formed role typing form
    obtain ⟨type, u, declared, -, -, le⟩ := Typed.generation typing
    obtain ⟨w, hw, rfl⟩ : ∃ w, X.realRules.isUniverse w ∧ type = .head w := by
      by_cases new : T ∈ X.names
      · obtain ⟨w, hw, declaredW⟩ := X.realNewInductive new role
        exact ⟨w, X.realSub.isUniverse hw, Option.some.inj (declared.symm.trans declaredW)⟩
      · have role₀ := (X.realOld new).symm.trans role
        obtain ⟨rfl, -⟩ := objectRoles_inductive role₀
        exact ⟨_, realRules_U0 X, Option.some.inj
          (declared.symm.trans (X.realSub.constantType declared_num))⟩
    have isA : IsType X.realRules Γ A := Typed.isType (S := realSetting X) typing formed
    have isW : IsType X.realRules Γ (.head w) := universe_isType (S := realSetting X) hw
    obtain ⟨v, hv, eA, -⟩ := Below.universe_source (S := realSetting X) facts
      (TypeLe.toBelow le isA) formed hw (IsType.refl isW)
    obtain ⟨h', rfl, same⟩ := (facts.forms eA.symm formed (.inl ⟨v, rfl⟩) form).head_left
    exact ⟨h', rfl, (HeadSame.level X.realLevels same).1.mp hv⟩

end Facts

/-! ## The lifting and completeness -/

section Lift

variable (facts : FormFacts X.realRules X.realRoles)
  (newPreserving : ∀ {n : Nat} {Γ : Tower.Ctx n} {c : DeclName} {args : List (Tower.Tm n)}
    {r A : Tower.Tm n}, CtxFormed X.realRules Γ → c ∈ X.names →
      X.realRules.computation.step (appSpine (.const c) args) r →
      Typed X.realRules Γ (appSpine (.const c) args) A → Typed X.realRules Γ r A)
  (newOnly : ∀ {c : DeclName} {arity : Nat} {inspect : InspectTree}, c ∈ X.names →
    X.realRoles c = .computes arity inspect → inspect.OnlyConstructors)
  (newReflects : ∀ ⦃n k : Nat⦄ ⦃σ : Sub Tower.Head n k⦄, NeutralSub X.realRoles σ →
    ∀ ⦃c : DeclName⦄ ⦃args : List (Tower.Tm n)⦄ ⦃u : Tower.Tm k⦄, c ∈ X.names →
      X.realRules.computation.step (appSpine (.const c) (args.map (Presentation.subst σ))) u →
        ∃ t', X.realRules.computation.step (appSpine (.const c) args) t')
  (typeSN : ∀ {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}, CtxFormed X.realRules Γ →
    IsType X.realRules Γ A → StrongNormalization.SN X.realRules A)
include facts newPreserving newOnly newReflects typeSN

/-- **Spine comparisons lift in the package of an extension**, given the facts about the
weak-head forms of its types, that its root steps at new names preserve typing and reflect
substitutions of neutral terms, that its new computing constants inspect only constructor
forms, and that its types are strongly normalizing. -/
theorem real_spineLift : SpineLift (realSetting X) :=
  SpineLift.ofNormalizing (S := realSetting X) facts (realRules_roots X facts newPreserving)
    (realRules_heads X) (realRules_algebra X) (real_liftableForms X facts)
    (real_neutralReflecting X newOnly newReflects) fun formed isA => typeSN formed isA

/-- **Conversion completeness for the package of an extension**, given the facts and the
inputs at its new names: derivably equal terms of a formed context are algorithmically equal. -/
theorem real_algorithmicComplete_of_facts
    (new : ∀ {E : GenericEquality Tower.Head} (lawsE : E.Laws X.realRules X.realRoles)
      (reduceE : RespectsReduction X.realRules X.realRoles E),
      HoldsCongruence E programCodes →
        NewSoundN X (nmodel X (fun _ => 0) (realSideAt X facts E lawsE reduceE))) :
    AlgorithmicComplete X.realRules X.realRoles :=
  real_algorithmicComplete X facts newPreserving
    (real_spineLift X facts newPreserving newOnly newReflects typeSN) new

end Lift

end Extension

/-! ## The object package -/

/-- The types of a formed context of the object package are strongly
normalizing. -/
theorem objectRules_type_sn {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n}
    (formed : CtxFormed objectRules Γ) (isA : IsType objectRules Γ A) :
    StrongNormalization.SN objectRules A := by
  obtain ⟨u, -, typed⟩ := isA
  exact (objectRules_sn formed typed).1

/-- **Spine comparisons lift in the object package**, given the facts about the weak-head forms
of its types: it is the extension by no name. -/
theorem object_spineLift (facts : FormFacts objectRules objectRoles) :
    SpineLift (realSetting objectTExt) :=
  real_spineLift objectTExt facts (fun _ h => (nomatch h)) (fun h => (nomatch h))
    (fun _ _ _ _ _ _ _ h => (nomatch h)) objectRules_type_sn

/-- **Conversion completeness for the object package**, given the facts about
the weak-head forms of its types: derivably equal terms of a formed context are
algorithmically equal. -/
theorem object_algorithmicComplete_of_facts (facts : FormFacts objectRules objectRoles) :
    AlgorithmicComplete objectRules objectRoles :=
  real_algorithmicComplete objectTExt facts (fun _ h => (nomatch h)) (object_spineLift facts)
    fun _ _ _ => objectTExt_newSoundN _

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
