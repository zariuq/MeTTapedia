import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaLongExistence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableReduction

/-!
# Reflection on the η-long fragment, the normalizer, and answers in η-long form

**Reflection.** Two terms are equal in the typed βη equality exactly when they have a common
η-long normal form (`equal_iff_common`). The η-long normal form of a term is unique up to the
package's head equality (`normalForm_unique`); with discrete heads, two typed terms are equal
exactly when their η-long normal forms are the same term (`equal_iff_normalForms_eq`).

**The normalizer.** The executable β-normalizer and the η-long read-back agree where both apply:
when the normalizer's result is already η-long at the type, it is the η-long normal form
(`normalizer_normalForm`), and every η-long normal form of the input is that result up to heads
(`normalizer_agrees`). Where the result is not η-long (a neutral function, a neutral pair), the
normalizer stops and η-expansion is still owed; the controls show both cases.

**Answers.** A substitution is read in η-long form by replacing each component by an η-long
normal form at its type (`LongReading`). Such a reading exists (`longReading_exists`), is unique
up to heads (`longReading_unique`), and keeps every principal answer of the typed βη frame
principal (`principal_of_longReading`): pointwise equal substitutions act equally on judged terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaLong

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

section Reflection

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra complete

/-- **The η-long normal form of a term is unique** up to the package's head equality. -/
theorem normalForm_unique {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t v w A : Tm Head n}
    (first : NormalForm S.R S.roles Γ t v A) (second : NormalForm S.R S.roles Γ t w A) :
    SameUpToHeads S.R v w :=
  long_unique facts roots heads algebra complete formed first.1 second.1
    (.trans (.symm first.2) second.2)

/-- Equal terms have η-long normal forms that are the same up to heads. -/
theorem normalForms_same_of_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {t u v w A : Tm Head n} (equal : Equal S.R Γ t u A) (first : NormalForm S.R S.roles Γ t v A)
    (second : NormalForm S.R S.roles Γ u w A) : SameUpToHeads S.R v w :=
  long_unique facts roots heads algebra complete formed first.1 second.1
    (.trans (.symm first.2) (.trans equal second.2))

variable (rigid : ∀ name, S.roles name = .rigid)
include rigid

/-- **Reflection**: equality in the typed βη equality is having a common η-long normal form. -/
theorem equal_iff_common {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t u A : Tm Head n} :
    Equal S.R Γ t u A ↔
      ∃ v, NormalForm S.R S.roles Γ t v A ∧ NormalForm S.R S.roles Γ u v A :=
  ⟨long_common facts roots heads algebra rigid complete formed,
    fun ⟨_, first, second⟩ => .trans first.2 (.symm second.2)⟩

/-- **Reflection with discrete heads**: two typed terms are equal exactly when their η-long
normal forms are the same term. -/
theorem equal_iff_normalForms_eq (discrete : ∀ {h h' : Head}, S.R.headEq h h' → h = h') {n : Nat}
    {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {t u A : Tm Head n} (tt : Typed S.R Γ t A)
    (tu : Typed S.R Γ u A) :
    Equal S.R Γ t u A ↔
      ∀ v w, NormalForm S.R S.roles Γ t v A → NormalForm S.R S.roles Γ u w A → v = w := by
  constructor
  · intro equal v w first second
    exact (normalForms_same_of_equal facts roots heads algebra complete formed equal first second).eq_of_discrete
      discrete
  · intro same
    obtain ⟨v, first⟩ := long_exists facts roots heads algebra rigid complete formed tt
    obtain ⟨w, second⟩ := long_exists facts roots heads algebra rigid complete formed tu
    obtain rfl := same v w first second
    exact .trans first.2 (.symm second.2)

end Reflection

/-! ## The executable normalizer -/

section Normalizer

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
include facts roots heads

/-- **Where both apply, the normalizer's result is the η-long normal form**: a result of the
executable β-normalizer that is η-long at the type is a normal form of the input. -/
theorem normalizer_normalForm {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {root : ExecutableReduction.RootEvaluator S.R} {fuel : Nat} {t t₀ A : Tm Head n}
    (typed : Typed S.R Γ t A) (run : ExecutableReduction.normalizeTerm S.R root fuel t = some t₀)
    (long : Long S.R S.roles (.term Γ t₀ A)) : NormalForm S.R S.roles Γ t t₀ A :=
  ⟨long, (Reduces.preserve facts roots heads formed
    (ExecutableReduction.normalizeTerm_sound S.R root run) typed).2⟩

variable (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
include algebra complete

/-- Every η-long normal form of the input is the normalizer's η-long result, up to heads. -/
theorem normalizer_agrees {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {root : ExecutableReduction.RootEvaluator S.R} {fuel : Nat} {t t₀ v A : Tm Head n}
    (typed : Typed S.R Γ t A) (run : ExecutableReduction.normalizeTerm S.R root fuel t = some t₀)
    (long : Long S.R S.roles (.term Γ t₀ A)) (normal : NormalForm S.R S.roles Γ t v A) :
    SameUpToHeads S.R t₀ v :=
  normalForm_unique facts roots heads algebra complete formed
    (normalizer_normalForm facts roots heads formed typed run long) normal

end Normalizer

/-! ## Answers in η-long form -/

section Answers

open ContextualDependentEta

/-- Pointwise equal substitutions act equally on every judged term of the typed βη frame. -/
theorem act_equal_of_substEq {Γ Δ : Context S.R} {σ σ' : Δ ⟶ Γ}
    (equal : SubstEq S.R Γ.raw Δ.raw σ.substitution σ'.substitution) (t : TotalTerm Γ) :
    (frames S.levels).E ((frames S.levels).act σ t) ((frames S.levels).act σ' t) :=
  ⟨⟨t.1.level, t.1.universeWitness, t.1.formed.functional equal⟩, t.2.typed.functional equal⟩

/-- **Principal answers survive pointwise equal readings.** -/
theorem principal_of_substEq {a m : Context S.R} {K : EquationStore (TotalTerm a)}
    {σ σ' : m ⟶ a} (equal : SubstEq S.R a.raw m.raw σ.substitution σ'.substitution)
    (principal : (frames S.levels).Principal (a := a) (m := m) K σ) :
    (frames S.levels).Principal (a := a) (m := m) K σ' where
  sound := by
    intro e member
    have solved := principal.sound e member
    exact ((frames S.levels).equivalence m).trans
      (((frames S.levels).equivalence m).symm (act_equal_of_substEq equal e.1))
      (((frames S.levels).equivalence m).trans solved (act_equal_of_substEq equal e.2))
  factors := by
    intro b τ solved
    obtain ⟨residual, through⟩ := principal.factors b τ solved
    refine ⟨residual, fun t => ((frames S.levels).equivalence b).trans (through t) ?_⟩
    rw [(frames S.levels).act_comp, (frames S.levels).act_comp]
    exact (frames S.levels).preserves residual (act_equal_of_substEq equal t)

/-- `σ'` reads `σ` in η-long form: each component is an η-long normal form of `σ`'s component,
at its type. -/
def LongReading {a m : Context S.R} (σ σ' : m ⟶ a) : Prop :=
  ∀ i, NormalForm S.R S.roles m.raw (σ.substitution i) (σ'.substitution i)
    (subst σ.substitution (Ctx.lookup a.raw i))

theorem LongReading.substEq {a m : Context S.R} {σ σ' : m ⟶ a} (reading : LongReading σ σ') :
    SubstEq S.R a.raw m.raw σ.substitution σ'.substitution :=
  ⟨σ.typed, fun i => (reading i).2⟩

/-- **Reading an answer in η-long form keeps it principal.** -/
theorem principal_of_longReading {a m : Context S.R} {K : EquationStore (TotalTerm a)}
    {σ σ' : m ⟶ a} (reading : LongReading σ σ')
    (principal : (frames S.levels).Principal (a := a) (m := m) K σ) :
    (frames S.levels).Principal (a := a) (m := m) K σ' :=
  principal_of_substEq reading.substEq principal

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra complete

/-- The η-long reading of a substitution is unique up to heads, component by component. -/
theorem longReading_unique {a m : Context S.R} {σ σ' σ'' : m ⟶ a} (first : LongReading σ σ')
    (second : LongReading σ σ'') (i : Fin a.arity) :
    SameUpToHeads S.R (σ'.substitution i) (σ''.substitution i) :=
  normalForm_unique facts roots heads algebra complete m.formed (first i) (second i)

variable (rigid : ∀ name, S.roles name = .rigid)
include rigid

/-- **Every substitution has an η-long reading.** -/
theorem longReading_exists {a m : Context S.R} (σ : m ⟶ a) : ∃ σ' : m ⟶ a, LongReading σ σ' := by
  have each : ∀ i, ∃ v, NormalForm S.R S.roles m.raw (σ.substitution i) v
      (subst σ.substitution (Ctx.lookup a.raw i)) :=
    fun i => long_exists facts roots heads algebra rigid complete m.formed (σ.typed i)
  choose component normal using each
  have equal : SubstEq S.R a.raw m.raw σ.substitution component := ⟨σ.typed, fun i => (normal i).2⟩
  refine ⟨⟨component, fun i => ?_⟩, normal⟩
  obtain ⟨u, hu, tLookup⟩ := Typed.isType (Derivable.var (R := S.R) (Γ := a.raw) i) a.formed
  exact Typed.convType (normal i).1.typed ⟨u, hu, tLookup.functional equal⟩

/-- **Principal answers can be read in η-long form.** -/
theorem principal_long_exists {a m : Context S.R} {K : EquationStore (TotalTerm a)} {σ : m ⟶ a}
    (principal : (frames S.levels).Principal (a := a) (m := m) K σ) :
    ∃ σ' : m ⟶ a, LongReading σ σ' ∧ (frames S.levels).Principal (a := a) (m := m) K σ' := by
  obtain ⟨σ', reading⟩ := longReading_exists facts roots heads algebra complete rigid σ
  exact ⟨σ', reading, principal_of_longReading reading principal⟩

end Answers

end ContextualDependentEtaLong
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
