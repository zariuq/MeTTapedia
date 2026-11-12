import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.HostTables
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateInferenceControls

/-!
# Subject reduction of the operational reading: the step's check after the match restores it

A rule's answer must have the call's declared type. A system that types a rule's body without what
its match learned, and checks answers only at run time, admits rules whose answers have another type
(the measured failures of the reference implementation: a body that returns its argument at another
type is accepted at declaration, and its answer is not re-checked when it is an already evaluated
expression).

The step decides this at admission. Its templating rule types every made row **after the match**, at
every solution of what the firing learned:

* **Every answer has its declared type** at every solution (`templating_answers_typed`), for every
  settler. This is subject reduction of the operational reading, by construction.
* **A row not typed after the match is refused** by every settler (`templating_refuses`). The firing that
  answers `f a`, whose type after the match is `U₀`, at the declared type `Ground` is refused
  (`mistyped_answer_refused`); the same firing answering at `U₀` is admitted
  (`TemplateInference.Controls.gap_admitted`), and so is the dependent clause `vappend nil ys = ys` at
  `vec (add m k)` (`VectorAppend.vappend_typedAfterMatch`), which only the match types.

**A host operation in a type.** With a total, deterministic host table the knowledge computes types
through it: `vec (0 - 1) ≡ vec 0` under truncated subtraction (`host_in_type`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.AnswersTyped

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)

section Generic

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L) {O : Type} [DecidableEq O] (settler : Settler levels)

/-- **Every answer of an admitted firing has its declared type at every solution** of what the
firing learned: subject reduction of the operational reading, for every settler. -/
theorem templating_answers_typed {s : State rules O} {f : Firing levels s}
    (admitted : (templatingStep levels O settler).Admits f) :
    ∀ m ∈ f.makes, ∀ (Θ : Context rules) (τ : Θ ⟶ f.helpers.frame), (frames levels).Models τ f.information →
      Typed rules Θ.raw (subst τ.substitution m.2.code) (m.2.type.reindex τ).code :=
  fun m member => (typedAfterMatch_iff levels _ _).mp (templating_typedAfterMatch levels settler admitted m member)

/-- **A firing with a row not typed after the match is refused**, by every settler. -/
theorem templating_refuses {s : State rules O} {f : Firing levels s} {m : O × Make f.helpers.frame}
    (member : m ∈ f.makes) (notTyped : ¬ TypedAfterMatch levels f.information m.2) :
    ¬ (templatingStep levels O settler).Admits f :=
  fun admitted => notTyped (templating_typedAfterMatch levels settler admitted m member)

end Generic

/-- **The mistyped answer is refused by every settler**: `f a`, typed `U₀` after the match, made at the
declared type `Ground`. -/
theorem mistyped_answer_refused (settler : Settler Interface.DependentFull.Controls.setting.levels) :
    ¬ (templatingStep Interface.DependentFull.Controls.setting.levels Nat settler).Admits
      TemplateInference.Controls.gapGroundFiring :=
  templating_refuses _ settler (m := (1, TemplateInference.Controls.groundRow)) (List.mem_singleton_self _)
    TemplateInference.Controls.gapGround_not_typedAfterMatch

/-- **The positive controls**: the same call answered at its type after the match is admitted, and so
is the clause `vappend nil ys = ys` at `vec (add m k)`, which only the match types. -/
theorem typed_answers_admitted :
    (templatingStep Interface.DependentFull.Controls.setting.levels Nat OlderUnknown.olderSettler).Admits
        TemplateControls.gapFiring ∧
      TypedAfterMatch VectorAppend.vlevels [VectorAppend.matchNil] VectorAppend.vappendRow :=
  ⟨TemplateInference.Controls.gap_admitted, VectorAppend.vappend_typedAfterMatch⟩

/-! ## A host operation in a type -/

section Host

open ProgrammingOnTheStep.VectorPackage
open HostTables

/-- **Types compute through a total, deterministic host table**: `vec (0 - 1) ≡ vec 0` under truncated
subtraction. -/
theorem host_in_type :
    Equal (declare rules (hostComputation addN natSub)) .nil (vecC (hostCall addN 0 1)) (vecC (numeral 0))
      U0 := by
  have vecConst : Typed (declare rules (hostComputation addN natSub)) .nil (.const vecN) (.pi natC U0) :=
    typed_declare _ (.const declared_vec vecTy_typed (.sort _))
  have call : Typed (declare rules (hostComputation addN natSub)) .nil (hostCall addN 0 1) natC :=
    typed_declare _ (add_typed (HostTables.numeral_typed _ 0) (HostTables.numeral_typed _ 1))
  exact .appCong (.refl vecConst)
    (.root (declare_step ⟨0, 1, 0, rfl, rfl, rfl⟩) call (typed_declare _ (HostTables.numeral_typed _ 0)))

end Host

end NativeTypesOnTheStep.Computing.AnswersTyped

#print axioms NativeTypesOnTheStep.Computing.AnswersTyped.templating_answers_typed
#print axioms NativeTypesOnTheStep.Computing.AnswersTyped.templating_refuses
#print axioms NativeTypesOnTheStep.Computing.AnswersTyped.mistyped_answer_refused
#print axioms NativeTypesOnTheStep.Computing.AnswersTyped.typed_answers_admitted
#print axioms NativeTypesOnTheStep.Computing.AnswersTyped.host_in_type

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
