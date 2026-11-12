import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Comparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.AgreementCounterexample
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.DeclaredConfluence
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerConservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerCaseTreesTyped

/-!
# Equation sets qualified for the definitional reading

An equation set read **definitionally** joins conversion: types may compute with it. It is
qualified for that reading (`Qualified`) when three checks pass, each of which the tree already
knows how to discharge at declaration time:

* **Constructor system** (syntactic): every left side is a defined constant applied to linear
  constructor patterns, every variable of a right side occurs on its left, and two left sides with a
  common instance are one equation (decided by first-order unifiability of the left sides,
  `ConstructorSystem.determined_of_disjoint`). This gives **Church–Rosser** for β, both projections,
  the universe-head equality and the declared equations together (`Qualified.churchRosser`).
* **Typed right sides**: each right side is typed at the declared type in the context of its
  pattern, in the stage of the package before the constant (the `bodyTyped` and `LeavesTyped`
  fields of the declaration records). With the facts about weak-head forms this gives **subject
  reduction**: every reduction, under binders included, preserves typing and is a typed equality
  (`Qualified.subjectReduction`). Without it subject reduction fails (`untypedLeaf_not_qualified`).
* **Termination** (the normalization model): every declared constant is semantic, which structural
  recursion on a constructor argument discharges (`DeclaresRecursion.semantic`). This gives weak-head
  normal forms (`Qualified.whnf`) and, with the semantic constants of the algorithmic equality,
  **decidable conversion**: the type-directed algorithm, with η for functions and pairs, derives
  exactly the typed equalities (`Qualified.algorithm_iff`) and decides them (`Qualified.decide`).

**η.** Untyped confluence cannot carry η here. The typed equality has η for functions, which
untyped conversion lacks: `h` and `λ x. h x` are typed-equal and not convertible
(`eta_not_conversion`). And η as a reduction does not preserve typing in the cumulative tower:
`λ x. h x` is typed at `Π (x : U₀). U₁` and its η-reduct `h` is not (`eta_reduct_not_typed`).
So η is handled by type-directed comparison, and "confluence with β and η" is the statement that the
algorithm decides the typed βη-equality with the declared rules, which `Qualified.algorithm_iff` and
`Qualified.decide` are.

**Instance.** The executable package of the certified-transform program is qualified
(`executable_qualified`), with every hypothesis proved: addition by structural recursion
(`add n zero ⟶ n`, `add n (suc m) ⟶ suc (add n m)`), the iterated power set, the iterator over a
family, identity elimination at reflexivity, the recursor, and the definition
`eqAt n ⟶ Id num (add zero n) n`, a type family computed by an equation that itself computes with
addition: a function of the program used in a type.

**Negative instances.** A setting over the overlapping declaration `add 0 b ↦ b`, `add 0 b ↦ 0` is
not qualified (`overlapping_not_qualified`); neither is one over a tree whose leaf is not typed
(`untypedLeaf_not_qualified`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ConstructorSystem (ConstructorPresentation)
open ConversionCoherence (ChurchRosser StepStar)

/-! ## The qualified class -/

section Generic

variable {Head L : Type} [UniverseLevel.LevelOrder L]

/-- **An equation set qualified for the definitional reading**: a constructor system, whose root
steps preserve typing, whose declared constants are semantic for the typed and for the algorithmic
equality, over a package whose universe-head equality is decided. -/
structure Qualified (S : Setting Head L) : Prop where
  laws : S.E.Laws S.R S.roles
  constructors : Nonempty (ConstructorPresentation S.R)
  constants : SemanticConstants S
  roots : RootPreserving S.R
  heads : HeadPreserving S.R
  algebra : CumulativeAlgebra S.R
  algorithmicConstants : SemanticConstants (algorithmicSetting S)
  decideHeads : ∀ h h' : Head, HeadSame S.R h h' ∨ ¬ HeadSame S.R h h'

namespace Qualified

variable {S : Setting Head L} (q : Qualified S)
include q

/-- **Confluence with β**: conversion of a qualified package is Church–Rosser. -/
theorem churchRosser : ChurchRosser S.R :=
  q.constructors.elim fun presentation => presentation.churchRosser

/-- **Unique normal forms**: convertible terms without computation steps are equal. -/
theorem eq_of_normal {n : Nat} {a b : Tm Head n} (normalA : ConstructorSystem.Normal S.R a)
    (normalB : ConstructorSystem.Normal S.R b) (conversion : Conv S.R.headEq a b S.R.computation) :
    a = b :=
  q.constructors.elim fun presentation => presentation.eq_of_normal normalA normalB conversion

/-- The facts about weak-head forms: injectivity and discrimination of type formers. -/
theorem facts : FormFacts S.R S.roles :=
  FormFacts.ofSemantic (S := S) q.laws q.constants

/-- **Subject reduction**: every reduction of a qualified package preserves typing and is a typed
equality. -/
theorem subjectReduction {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t t' T : Tm Head n}
    (red : Reduces S.R t t') (typing : Typed S.R Γ t T) :
    Typed S.R Γ t' T ∧ Equal S.R Γ t t' T :=
  Reduces.preserve (S := S) q.facts q.roots q.heads formed red typing

/-- **Conservativity**: convertible typed terms of one type are typed-equal. -/
theorem conv_toEqual {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {a b T : Tm Head n}
    (conversion : Conv S.R.headEq a b S.R.computation) (typedA : Typed S.R Γ a T)
    (typedB : Typed S.R Γ b T) : Equal S.R Γ a b T :=
  Conv.toEqual (S := S) q.facts q.roots q.heads q.churchRosser formed conversion typedA typedB

/-- **Termination, weak-head form**: every typed term has a weak-head normal form. -/
theorem whnf {n : Nat} {Γ : Ctx Head n} {t A : Tm Head n} (typing : Typed S.R Γ t A)
    (formed : CtxFormed S.R Γ) : ∃ nf, WhRed S.R S.roles t nf ∧ Whnf S.R S.roles nf :=
  Typed.whnf_exists (S := S) q.laws q.constants typing formed

/-- The algorithmic equality is complete. -/
theorem complete : AlgorithmicComplete S.R S.roles :=
  AlgorithmicComplete.ofSemantic (S := S) q.laws q.constants q.roots q.heads q.algebra
    q.algorithmicConstants

/-- **Confluence with β and η, typed**: on typed terms the type-directed algorithm, with η for
functions and pairs, derives exactly the typed equalities. -/
theorem algorithm_iff {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t u A : Tm Head n}
    (typedT : Typed S.R Γ t A) (typedU : Typed S.R Γ u A) :
    Algorithm S.R (.compare Γ t u A) ↔ Equal S.R Γ t u A :=
  algorithm_iff_equal (S := S) q.facts q.roots q.heads q.algebra q.complete formed typedT typedU

/-- **Decidable conversion**: the typed equality between two terms of a type is decided. -/
theorem decide {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t u A : Tm Head n}
    (typedT : Typed S.R Γ t A) (typedU : Typed S.R Γ u A) :
    Equal S.R Γ t u A ∨ ¬ Equal S.R Γ t u A :=
  Equal.decide (S := S) q.facts q.roots q.heads q.algebra q.decideHeads q.complete formed typedT
    typedU

end Qualified

/-- A package that is not Church–Rosser is not qualified. -/
theorem not_qualified_of_not_churchRosser {S : Setting Head L} (failure : ¬ ChurchRosser S.R) :
    ¬ Qualified S :=
  fun q => failure q.churchRosser

/-- A package whose root steps do not preserve typing is not qualified. -/
theorem not_qualified_of_not_rootPreserving {S : Setting Head L} (failure : ¬ RootPreserving S.R) :
    ¬ Qualified S :=
  fun q => failure q.roots

end Generic

/-! ## The executable package is qualified -/

section Executable

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open CertifiedTransformProgram

/-- **Every hypothesis holds for the executable package**: constructor patterns, typed right sides,
structural recursion, for addition, the iterated power set, the iterator, identity elimination, the
recursor and the definitions. -/
theorem executable_qualified : Qualified (ExecutableModel.setting fun _ => 0) where
  laws := ExecutableModel.laws _
  constructors := ⟨ExecutableModel.constructors⟩
  constants := ExecutableModel.constants _
  roots := ExecutableModel.roots
  heads := ExecutableModel.heads
  algebra := ExecutableModel.algebra
  algorithmicConstants := ExecutableModel.algorithmicConstants
  decideHeads := ExecutableModel.decideHeads

/-- **Addition computes in types**: `eqAt n ⟶ Id num (add zero n) n` is a step of the qualified
package, so the type `eqAt n` is convertible with an identity type that mentions addition. -/
theorem eqAt_step {n : Nat} (number : Tower.Tm n) :
    ExecutableModel.rules.computation.step (.app (.const Package.eqAtName) number)
      (.id Package.numT (SetProfile.addNative SetProfile.zeroNative number) number) :=
  ExecutableModel.equation_sound (ExecutableModel.equation_listed 7 (by decide) rfl)
    (fun _ => number)

/-- **Types compute with addition, typed**: for every number `n` of a formed context,
`eqAt n ≡ Id num (add zero n) n` at the universe of small types. -/
theorem eqAt_equal {m : Nat} {Γ : Tower.Ctx m} (formed : CtxFormed ExecutableModel.rules Γ)
    {number : Tower.Tm m} (typed : Typed ExecutableModel.rules Γ number Package.numT) :
    Equal ExecutableModel.rules Γ (.app (.const Package.eqAtName) number)
      (.id Package.numT (SetProfile.addNative SetProfile.zeroNative number) number) Package.U0 :=
  (executable_qualified.subjectReduction formed (.single (.root (eqAt_step number)))
    (.appElim (Derivable.mono (ExecutableModel.stage_sub_rules _)
      (ExecutableModel.eqAt_typed (names := [ExecutableModel.numN, Package.eqAtName]) (by simp) (by simp)))
      typed)).2

end Executable

/-! ## Negative instances -/

section Negative

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- **The overlapping declaration is not qualified**: `add 0 b ↦ b` with `add 0 b ↦ 0` is not
Church–Rosser. -/
theorem overlapping_not_qualified (S : Setting Tower.Head L) (same : S.R = VectorAppend.brules) :
    ¬ Qualified S := by
  intro q
  apply DeclaredConfluence.bad_not_churchRosser
  rw [← same]
  exact q.churchRosser

/-- **A tree whose leaf is not typed is not qualified**: `bad zero = junk` steps a typed call to an
untyped constant. -/
theorem untypedLeaf_not_qualified (S : Setting Tower.Head L)
    (same : S.R = TowerCaseTreesModel.badRules) : ¬ Qualified S := by
  intro q
  apply TowerCaseTreesModel.bad_not_preserving
  rw [← same]
  exact q.roots

end Negative

/-! ## η: typed, not untyped -/

section Eta

/-- The η-redex `λ x. h x` reduces by η to `h`, the variable of the frame. -/
theorem etaCode_shape :
    Eta.etaCode = .lam (.app (Presentation.rename wk (.var 0 : Tower.Tm 1)) (.var 0)) :=
  rfl

/-- **η-reduction does not preserve typing in the cumulative tower**: `λ x. h x` is typed at
`Π (x : U₀). U₁` and its η-reduct `h` is not. -/
theorem eta_reduct_not_typed :
    Typed Tower.rules Eta.hFrame.raw Eta.etaCode (.pi Eta.u0 Eta.u1) ∧
      ¬ Typed Tower.rules Eta.hFrame.raw (.var 0) (.pi Eta.u0 Eta.u1) :=
  ⟨Eta.etaCode_typed_small, fun typed => Eta.etaRow_not_wellTyped typed⟩

/-- `h` is normal. -/
theorem var_normal : ConstructorSystem.Normal Tower.rules (.var 0 : Tower.Tm 1) := by
  intro target step
  cases step with
  | root h => exact (h : False).elim

/-- `λ x. h x` is normal: η is not a step of conversion. -/
theorem etaCode_normal : ConstructorSystem.Normal Tower.rules Eta.etaCode := by
  intro target step
  cases step with
  | root h => exact (h : False).elim
  | congLam inner =>
      cases inner with
      | root h => exact (h : False).elim
      | congAppFun inner' =>
          cases inner' with
          | root h => exact (h : False).elim
      | congAppArg inner' =>
          cases inner' with
          | root h => exact (h : False).elim

/-- `h` and `λ x. h x` are equal at `Π (x : U₁). U₁`, by η. -/
theorem eta_equal : Equal Tower.rules Eta.hFrame.raw (.var 0) Eta.etaCode (.pi Eta.u1 Eta.u1) := by
  have beta : Equal Tower.rules (.snoc Eta.hFrame.raw Eta.u1)
      (.app (.lam (.app (.var 2) (.var 0))) (.var 0)) (.app (.var 1) (.var 0)) Eta.u1 :=
    .betaPi (A := Eta.u1) (B := Eta.u1) (body := .app (.var 2) (.var 0)) (a := .var 0)
      (Eta.bigArrow_typed _) (.sort _) (.appElim (A := Eta.u1) (B := Eta.u1) (.var 2) (.var 0))
      (.var 0)
  exact .etaPi (.var 0) Eta.etaCode_typed_big (.symm beta)

/-- **The typed equality has η, untyped conversion does not**: `h` and `λ x. h x` are typed-equal and
not convertible, being distinct normal forms of a Church–Rosser conversion. -/
theorem eta_not_conversion :
    Equal Tower.rules Eta.hFrame.raw (.var 0) Eta.etaCode (.pi Eta.u1 Eta.u1) ∧
      ¬ Conv Tower.rules.headEq (.var 0 : Tower.Tm 1) Eta.etaCode Tower.rules.computation := by
  refine ⟨eta_equal, fun conversion => ?_⟩
  obtain ⟨common, left, right⟩ := Normalization.LevelTower.churchRosser conversion
  have fromVar := ConstructorSystem.Normal.stepStar var_normal left
  have fromEta := ConstructorSystem.Normal.stepStar etaCode_normal right
  have same : (.var 0 : Tower.Tm 1) = Eta.etaCode := fromVar.symm.trans fromEta
  cases same

end Eta

end NativeTypesOnTheStep.Computing

#print axioms NativeTypesOnTheStep.Computing.Qualified.churchRosser
#print axioms NativeTypesOnTheStep.Computing.Qualified.eq_of_normal
#print axioms NativeTypesOnTheStep.Computing.Qualified.facts
#print axioms NativeTypesOnTheStep.Computing.Qualified.subjectReduction
#print axioms NativeTypesOnTheStep.Computing.Qualified.conv_toEqual
#print axioms NativeTypesOnTheStep.Computing.Qualified.whnf
#print axioms NativeTypesOnTheStep.Computing.Qualified.complete
#print axioms NativeTypesOnTheStep.Computing.Qualified.algorithm_iff
#print axioms NativeTypesOnTheStep.Computing.Qualified.decide
#print axioms NativeTypesOnTheStep.Computing.not_qualified_of_not_churchRosser
#print axioms NativeTypesOnTheStep.Computing.not_qualified_of_not_rootPreserving
#print axioms NativeTypesOnTheStep.Computing.executable_qualified
#print axioms NativeTypesOnTheStep.Computing.eqAt_step
#print axioms NativeTypesOnTheStep.Computing.eqAt_equal
#print axioms NativeTypesOnTheStep.Computing.overlapping_not_qualified
#print axioms NativeTypesOnTheStep.Computing.untypedLeaf_not_qualified
#print axioms NativeTypesOnTheStep.Computing.etaCode_shape
#print axioms NativeTypesOnTheStep.Computing.eta_reduct_not_typed
#print axioms NativeTypesOnTheStep.Computing.var_normal
#print axioms NativeTypesOnTheStep.Computing.etaCode_normal
#print axioms NativeTypesOnTheStep.Computing.eta_equal
#print axioms NativeTypesOnTheStep.Computing.eta_not_conversion

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
