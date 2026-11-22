import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.CrossPostponed
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateSettling
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseInjective
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdateLifting

/-!
# The older-unknown family: a type unknown solved at its own prefix

In dependent matching a pattern variable `x : X` may have as its type an *earlier* unknown `X : U`,
fixed only by what the match supplies: `(x : X) ≐ (g : Ground)`. The equation is heterogeneous, so it
states two equations at once, a type equation `X ≐ Ground` at `U` and a term equation over it. The
tree's solvers see only homogeneous equations: the newest-unknown driver is stuck on such a store, and
so is the in-place solver, which can solve an older unknown but only from an equation about it.

**Type extraction** (`typeEquation?`, `extract`). A heterogeneous equation whose two types differ and
have a common universe `u` (`commonUniverse?`: one level, or the larger when one is below the other)
gives its type equation as an equation of the store: both types as judged terms of `u` (`typeAsTerm`,
`typed_at_above`). A store and its extraction have the same solutions (`extract_equivalent`): a
solution makes the two types equal at some universe, hence at `u`
(`ContextualDependentUniverseInjective.equal_at_universe`), and conversely nothing is added.

**Families on equivalent stores** (`Decision.ofEquivalent`, `Family.prepared`): initial solutions and
solvability depend on a store only through its solutions, so a decision on an equivalent preparation is
a decision on the store. An initial solution is an exact transition to no equation (`initial_exact`).

**The older-unknown transition** (`olderTransition`, `olderTransition_exact`). Over `Γ, X : A` followed by
a telescope `H`, a term `T : A` of the prefix `Γ` defines the unknown at its own prefix
(`ContextualDependentUpdate.definition`), and the definition is carried past `H`, each later declaration
instantiated (`Update.lift`, `liftThrough`). Every store that entails the carried definition makes an
exact transition along its answer to the store transported there (`updateAlong`): its solutions are
exactly the composites with the answer of the solutions of the transported store. A heterogeneous
equation whose left type is `X` carried past `H` and whose right type is `T` carried past `H`, both typed
at `A = U`, entails it (`entails_definition_of_twin`). This is the class: **a pattern
variable whose type is an earlier unknown, fixed by the match to a type formed before that unknown.**
The transition's answer is an epimorphism on terms (`instantiate_epi`, `lift_epi`,
`olderTransition_epi`), so on the class an initial solution of the transported store, composed with it,
is an initial solution of the store (`initial_along`, `olderTransition_initial`).

**The tower's older-unknown family** (`olderFamily`): extraction, then the tree's in-place solver
(`ContextualDependentInPlace`), which solves an unknown at its own depth and carries the answer past the
later declarations, read as the worklist driver; a solved run whose answer covers its frame settles
along it, a refuted run refutes. It joins the tower's families (`olderFamilies`, `olderSettler`), and on
the union of the decided fragments the computable settler agrees with the semantic one
(`older_agrees_ideal`), for the converting and the templating steps alike (`older_converting_iff_ideal`,
`older_templating_iff_ideal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax (rawLift)
open ContextualDependentEta ContextualDependentUpdate
open Interface.DependentFull (Make State Firing Helpers)
open UnificationWithLevels (Agree InitialSolution EpiOnTerms Exact)

/-! ## The type equation of a heterogeneous equation -/

section Extraction

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L) (choices : ExecutableChecking.HeadChoices rules)

/-- **A universe as a formed type**, typed by its head typing. -/
def universeOver {Γ : Context rules} (u : Head) (hu : rules.isUniverse u)
    (typing : {v : Head // rules.headTyping u v}) : TypeOver Γ :=
  ⟨.head u, typing.val, (levels.universe_typing hu typing.property).1, .headType typing.property⟩

/-- **A type typed at the universe `u`, as a judged term of `u`.** -/
def typeAsTerm {Γ : Context rules} (A : TypeOver Γ) {u : Head} (typedAt : Typed rules Γ.raw A.code (.head u))
    (hu : rules.isUniverse u) (typing : {v : Head // rules.headTyping u v}) : TotalTerm Γ :=
  ⟨universeOver levels u hu typing, ⟨A.code, typedAt⟩⟩

omit [UniverseLevel.LevelOrder L] in
/-- A formed type is typed at its level and at every universe above it. -/
theorem typed_at_above {Γ : Context rules} (A : TypeOver Γ) {w : Head}
    (up : A.level = w ∨ rules.cumulative A.level w) : Typed rules Γ.raw A.code (.head w) := by
  rcases up with same | below
  · rw [← same]
    exact A.formed
  · exact .cumul A.formed below

include levels in
/-- A universe at or above a universe is one. -/
theorem universe_above {u w : Head} (hu : rules.isUniverse u) (up : u = w ∨ rules.cumulative u w) :
    rules.isUniverse w := by
  rcases up with same | below
  · exact same ▸ hu
  · exact (levels.cumulative_universe below).2.1

variable [DecidableEq Head] [DecidableRel rules.cumulative]

omit [UniverseLevel.LevelOrder L] in
/-- **A common universe of two levels**: the level itself when they are equal, otherwise the larger one
when one is below the other. -/
def commonUniverse? (u v : Head) :
    Option {w : Head // (u = w ∨ rules.cumulative u w) ∧ (v = w ∨ rules.cumulative v w)} :=
  if same : v = u then some ⟨u, .inl rfl, .inl same⟩
  else if below : rules.cumulative v u then some ⟨u, .inl rfl, .inr below⟩
  else if above : rules.cumulative u v then some ⟨v, .inr above, .inl rfl⟩
  else none

/-- **The type equation of an equation**, when its two types differ and have a common universe: both
types, as judged terms of that universe. -/
def typeEquation? {Γ : Context rules} (e : Equation (TotalTerm Γ)) : Option (Equation (TotalTerm Γ)) :=
  if e.1.1.code = e.2.1.code then none
  else
    match commonUniverse? e.1.1.level e.2.1.level with
    | none => none
    | some w => (choices.typing w.val).map fun typing =>
        (typeAsTerm levels e.1.1 (typed_at_above e.1.1 w.property.1)
            (universe_above levels e.1.1.universeWitness w.property.1) typing,
          typeAsTerm levels e.2.1 (typed_at_above e.2.1 w.property.2)
            (universe_above levels e.1.1.universeWitness w.property.1) typing)

/-- **The type equations of a store.** -/
def typeEquations {Γ : Context rules} (I : EquationStore (TotalTerm Γ)) : EquationStore (TotalTerm Γ) :=
  I.filterMap (typeEquation? levels choices)

/-- **The extraction of a store**: its type equations first, then the store itself. -/
def extract {Γ : Context rules} (I : EquationStore (TotalTerm Γ)) : EquationStore (TotalTerm Γ) :=
  typeEquations levels choices I ++ I

/-- A found type equation compares the two types as codes of one universe. -/
theorem typeEquation?_codes {Γ : Context rules} {e t : Equation (TotalTerm Γ)}
    (found : typeEquation? levels choices e = some t) :
    t.1.1 = t.2.1 ∧ t.1.2.code = e.1.1.code ∧ t.2.2.code = e.2.1.code ∧ e.1.1.code ≠ e.2.1.code := by
  unfold typeEquation? at found
  split at found
  · cases found
  · rename_i differ
    split at found
    · cases found
    · obtain ⟨typing, -, rfl⟩ := Option.map_eq_some_iff.mp found
      exact ⟨rfl, rfl, rfl, differ⟩

end Extraction

/-! ## A store and its extraction have the same solutions -/

section ExtractionExact

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [DecidableEq Head]
  [DecidableRel S.R.cumulative]
variable (choices : ExecutableChecking.HeadChoices S.R)
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra rigid complete

/-- **A solution of an equation solves its type equation**: the two types are equal at some universe,
hence at their common universe, where both are typed. -/
theorem typeEquation?_solves {Γ Θ : Context S.R} (τ : Θ ⟶ Γ) {e t : Equation (TotalTerm Γ)}
    (found : typeEquation? S.levels choices e = some t) (solved : (frames S.levels).Solves τ e) :
    (frames S.levels).Solves τ t := by
  unfold typeEquation? at found
  split at found
  · cases found
  · split at found
    · cases found
    · rename_i w _
      obtain ⟨typing, -, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨agree, -⟩ := (ContextualDependentTwins.solves_iff S.levels τ e).mp solved
      have hw := universe_above S.levels e.1.1.universeWitness w.property.1
      refine (ContextualDependentTwins.solves_iff S.levels τ _).mpr ⟨?_, ?_⟩
      · exact IsType.refl ((universeOver S.levels (Γ := Γ) w.val hw typing).reindex τ).isType
      · exact ContextualDependentUniverseInjective.equal_at_universe (S := S) facts roots heads algebra
          rigid complete Θ.formed hw ((typed_at_above e.1.1 w.property.1).substitute τ.typed)
          ((typed_at_above e.2.1 w.property.2).substitute τ.typed) agree

/-- **A store and its extraction have the same solutions.** -/
theorem extract_equivalent {Γ : Context S.R} (I : EquationStore (TotalTerm Γ)) :
    (frames S.levels).Equivalent I (extract S.levels choices I) := by
  intro Θ τ
  constructor
  · intro solved
    refine (Frames.models_append (X := frames S.levels) τ _ _).mpr ⟨fun t member => ?_, solved⟩
    obtain ⟨e, inside, found⟩ := List.mem_filterMap.mp member
    exact typeEquation?_solves choices facts roots heads algebra rigid complete τ found (solved e inside)
  · intro solved
    exact ((Frames.models_append (X := frames S.levels) τ _ _).mp solved).2

end ExtractionExact

/-! ## Decisions on equivalent stores -/

section Prepared

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable {levels : LevelModel rules L}

/-- **A decision on an equivalent store is a decision on the store**: initial solutions and solvability
depend on a store only through its solutions. -/
def Decision.ofEquivalent {Δ : Context rules} {I J : EquationStore (TotalTerm Δ)}
    (same : (frames levels).Equivalent I J) : Decision levels J → Decision levels I
  | .settled M σ initial => .settled M σ ((initialSolution_congr levels same σ).mpr initial)
  | .refuted absent => .refuted fun ⟨b, f, solved⟩ => absent ⟨b, f, (same b f).mp solved⟩
  | .undecided => .undecided

theorem Decision.ofEquivalent_decisive {Δ : Context rules} {I J : EquationStore (TotalTerm Δ)}
    (same : (frames levels).Equivalent I J) (d : Decision levels J) :
    (d.ofEquivalent same).Decisive ↔ d.Decisive := by
  cases d <;> exact Iff.rfl

theorem Decision.ofEquivalent_isSettled {Δ : Context rules} {I J : EquationStore (TotalTerm Δ)}
    (same : (frames levels).Equivalent I J) (d : Decision levels J) :
    (d.ofEquivalent same).isSettled = d.isSettled := by
  cases d <;> rfl

theorem Decision.ofEquivalent_isRefuted {Δ : Context rules} {I J : EquationStore (TotalTerm Δ)}
    (same : (frames levels).Equivalent I J) (d : Decision levels J) :
    (d.ofEquivalent same).isRefuted = d.isRefuted := by
  cases d <;> rfl

variable (levels) in
/-- **A family run on an equivalent preparation of each store.** -/
def Family.prepared
    (prepare : ∀ {Δ : Context rules} (I : EquationStore (TotalTerm Δ)),
      {J : EquationStore (TotalTerm Δ) // (frames levels).Equivalent I J})
    (F : Family levels) : Family levels :=
  fun I => (F (prepare I).val).ofEquivalent (prepare I).property

/-- **An initial solution is an exact transition to no equation**: the solutions of the store are
exactly the composites with it, up to agreement. -/
theorem initial_exact {M Δ : Context rules} {I : EquationStore (TotalTerm Δ)} {σ : M ⟶ Δ}
    (initial : InitialSolution (frames levels) I σ) (Θ : Context rules) (τ : Θ ⟶ Δ) :
    (frames levels).Models τ I ↔ ∃ g : Θ ⟶ M, Agree (frames levels) τ (g ≫ σ) := by
  constructor
  · exact initial.factor Θ τ
  · rintro ⟨g, agree⟩
    exact (UnificationWithLevels.models_of_agree agree I).mpr
      (Frames.models_comp (X := frames levels) initial.solves g)

end Prepared

/-! ## The older-unknown transition -/

section Transition

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

/-- A store carried past a telescope, weakened along each declaration in turn. -/
def weakenStore : {Γ : Context rules} → (H : Helpers Γ) → EquationStore (TotalTerm Γ) →
    EquationStore (TotalTerm H.frame)
  | _, .nil _, I => I
  | Γ, .cons A rest, I => weakenStore rest ((frames levels).applyStore (projectionHom Γ A) I)

/-- **An update carried past a telescope**, one later declaration at a time, each instantiated by the
answer (`Update.lift`). -/
def liftThrough : {Γ : Context rules} → (H : Helpers Γ) → {I : EquationStore (TotalTerm Γ)} →
    Update levels I → Update levels (weakenStore levels H I)
  | _, .nil _, _, u => u
  | _, .cons A rest, _, u => liftThrough rest (u.lift A)

/-- Carrying a finished update past a telescope leaves it finished. -/
theorem liftThrough_remaining : ∀ {Γ : Context rules} (H : Helpers Γ) {I : EquationStore (TotalTerm Γ)}
    (u : Update levels I), u.remaining = [] → (liftThrough levels H u).remaining = []
  | _, .nil _, _, _, finished => finished
  | _, .cons A rest, _, u, finished => liftThrough_remaining rest (u.lift A) (by
      show (frames levels).applyStore _ u.remaining = []
      rw [finished]
      rfl)

/-- **An update of an entailed store transports every store that entails it.** The answer is kept, the
residual store is the store transported along it. -/
def updateAlong {Δ : Context rules} {J : EquationStore (TotalTerm Δ)} (u : Update levels J)
    (I : EquationStore (TotalTerm Δ))
    (entails : ∀ (Θ : Context rules) (τ : Θ ⟶ Δ), (frames levels).Models τ I → (frames levels).Models τ J) :
    Update levels I where
  target := u.target
  answer := u.answer
  remaining := (frames levels).applyStore u.answer I
  sound := fun _ ρ solved => (Frames.models_applyStore (X := frames levels) u.answer ρ I).mp solved
  complete := fun Θ τ solved => by
    obtain ⟨ρ, -, factor⟩ := u.complete Θ τ (entails Θ τ solved)
    exact ⟨ρ, (Frames.models_applyStore (X := frames levels) u.answer ρ I).mpr
      ((Elimination.models_pointwise levels factor I).mp solved), factor⟩

/-- **An update is an exact transition** from its store to its residual store, along its answer. -/
theorem update_exact {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} (u : Update levels I) :
    Exact (frames levels) I u.answer u.remaining := by
  intro Θ τ
  constructor
  · intro solved
    obtain ⟨ρ, remaining, factor⟩ := u.complete Θ τ solved
    exact ⟨ρ, factor, remaining⟩
  · rintro ⟨ρ, agree, remaining⟩
    exact (UnificationWithLevels.models_of_agree agree I).mpr (u.sound Θ ρ remaining)

/-- **The older-unknown transition**: over `Γ, X : A` followed by the telescope `H`, the unknown `X`
defined by a term `T : A` of its prefix `Γ`, solved there and carried past `H`. -/
def olderTransition (Γ : Context rules) {A : TypeOver Γ} (T : Term Γ A) (H : Helpers (extend Γ A)) :
    Update levels (weakenStore levels H [Elimination.definition Γ T]) :=
  liftThrough levels H (ContextualDependentUpdate.definition levels T [])

/-- The older-unknown transition leaves nothing of the definition. -/
theorem olderTransition_finished (Γ : Context rules) {A : TypeOver Γ} (T : Term Γ A)
    (H : Helpers (extend Γ A)) : (olderTransition levels Γ T H).remaining = [] :=
  liftThrough_remaining levels H _ rfl

/-- **The carried definition has a principal answer**: the older-unknown transition's. -/
theorem olderTransition_principal (Γ : Context rules) {A : TypeOver Γ} (T : Term Γ A)
    (H : Helpers (extend Γ A)) :
    (frames levels).Principal (weakenStore levels H [Elimination.definition Γ T])
      (olderTransition levels Γ T H).answer :=
  (olderTransition levels Γ T H).completed (olderTransition_finished levels Γ T H)

/-! ### The transition's answer is an epimorphism on terms -/

/-- **Solving at the newest declaration is an epimorphism on terms**: it is a section of the
projection. -/
theorem instantiate_epi (Γ : Context rules) {A : TypeOver Γ} (T : Term Γ A) :
    EpiOnTerms (frames levels) (Elimination.instantiate Γ T) := by
  intro Θ g h same t
  have key : (t.reindex (projectionHom Γ A)).reindex (Elimination.instantiate Γ T) = t := by
    rw [← reindex_comp, Elimination.instantiate_projection, reindex_id]
  have moved := same (t.reindex (projectionHom Γ A))
  change (frames levels).E (((t.reindex (projectionHom Γ A)).reindex (Elimination.instantiate Γ T)).reindex g)
    (((t.reindex (projectionHom Γ A)).reindex (Elimination.instantiate Γ T)).reindex h) at moved
  rw [key] at moved
  exact moved

/-- **Carrying an update past one declaration keeps its answer an epimorphism on terms**: two
substitutions that agree on the image of the carried answer agree on its frame (through the epimorphism)
and on the newest variable (the image of the old newest variable). -/
theorem lift_epi {Γ : Context rules} {I : EquationStore (TotalTerm Γ)} (u : Update levels I)
    (A : TypeOver Γ) (epi : EpiOnTerms (frames levels) u.answer) :
    EpiOnTerms (frames levels) (rawLift u.answer A) := by
  intro Θ (g : Θ ⟶ extend u.target (A.reindex u.answer)) (h : Θ ⟶ extend u.target (A.reindex u.answer)) same
  have prefixAgree : Agree (frames levels) (g ≫ projectionHom u.target (A.reindex u.answer))
      (h ≫ projectionHom u.target (A.reindex u.answer)) := by
    apply epi
    intro t
    have key : (t.reindex (projectionHom Γ A)).reindex (rawLift u.answer A) =
        (t.reindex u.answer).reindex (projectionHom u.target (A.reindex u.answer)) := by
      rw [← reindex_comp, ← reindex_comp, lift_projection]
    show (frames levels).E ((t.reindex u.answer).reindex (g ≫ projectionHom u.target (A.reindex u.answer)))
      ((t.reindex u.answer).reindex (h ≫ projectionHom u.target (A.reindex u.answer)))
    rw [reindex_comp (t.reindex u.answer) g, reindex_comp (t.reindex u.answer) h, ← key]
    exact same (t.reindex (projectionHom Γ A))
  have key : (Elimination.last Γ A).reindex (rawLift u.answer A) =
      Elimination.last u.target (A.reindex u.answer) := by
    apply totalTerm_ext
    · calc (A.reindex (projectionHom Γ A)).reindex (rawLift u.answer A)
          = A.reindex (rawLift u.answer A ≫ projectionHom Γ A) := (TypeOver.reindex_comp A _ _).symm
        _ = A.reindex (projectionHom u.target (A.reindex u.answer) ≫ u.answer) := by rw [lift_projection]
        _ = (A.reindex u.answer).reindex (projectionHom u.target (A.reindex u.answer)) :=
            TypeOver.reindex_comp A _ _
    · rfl
  have newestAgree : (frames levels).E ((Elimination.last u.target (A.reindex u.answer)).reindex g)
      ((Elimination.last u.target (A.reindex u.answer)).reindex h) := by
    have moved := same (Elimination.last Γ A)
    change (frames levels).E (((Elimination.last Γ A).reindex (rawLift u.answer A)).reindex g)
      (((Elimination.last Γ A).reindex (rawLift u.answer A)).reindex h) at moved
    rw [key] at moved
    exact moved
  have values : Equal rules Θ.raw (pulledNewest g).code (pulledNewest h).code
      ((A.reindex u.answer).reindex (g ≫ projectionHom u.target (A.reindex u.answer))).code := by
    rw [pulledNewest_code, pulledNewest_code, TypeOver.reindex_comp]
    exact newestAgree.2
  have paired := homTypedEquality_pair (type := A.reindex u.answer)
    (substEq_of_act_equal levels prefixAgree) values
  rw [pair_eta, pair_eta] at paired
  exact fun t => act_equal_of_substEq levels paired t

/-- Carrying past a telescope keeps an epimorphism on terms. -/
theorem liftThrough_epi : ∀ {Γ : Context rules} (H : Helpers Γ) {I : EquationStore (TotalTerm Γ)}
    (u : Update levels I), EpiOnTerms (frames levels) u.answer →
      EpiOnTerms (frames levels) (liftThrough levels H u).answer
  | _, .nil _, _, _, epi => epi
  | _, .cons A rest, _, u, epi => liftThrough_epi rest (u.lift A) (lift_epi levels u A epi)

/-- **The older-unknown transition's answer is an epimorphism on terms.** -/
theorem olderTransition_epi (Γ : Context rules) {A : TypeOver Γ} (T : Term Γ A)
    (H : Helpers (extend Γ A)) : EpiOnTerms (frames levels) (olderTransition levels Γ T H).answer :=
  liftThrough_epi levels H _ (instantiate_epi levels Γ T)

/-- **Initial solutions compose along an epimorphic update**: an initial solution of the residual store,
composed with the answer, is an initial solution of the store. -/
theorem initial_along {Δ : Context rules} {I : EquationStore (TotalTerm Δ)} (u : Update levels I)
    (epi : EpiOnTerms (frames levels) u.answer) {M : Context rules} {ρ : M ⟶ u.target}
    (initial : InitialSolution (frames levels) u.remaining ρ) :
    InitialSolution (frames levels) I (ρ ≫ u.answer) := by
  refine ⟨u.sound M ρ initial.solves, fun Θ τ solved => ?_, fun Θ τ g h first second => ?_⟩
  · obtain ⟨ρ', remaining, factor⟩ := u.complete Θ τ solved
    obtain ⟨g, through⟩ := initial.factor Θ ρ' remaining
    refine ⟨g, fun t => ?_⟩
    have eq2 : t.reindex (g ≫ (ρ ≫ u.answer)) = (t.reindex u.answer).reindex (g ≫ ρ) := by
      rw [← Category.assoc, reindex_comp]
    have one : (frames levels).E (t.reindex τ) ((t.reindex u.answer).reindex ρ') := by
      have f := factor t
      rw [reindex_comp t ρ' u.answer] at f
      exact f
    have two : (frames levels).E ((t.reindex u.answer).reindex ρ') ((t.reindex u.answer).reindex (g ≫ ρ)) :=
      through (t.reindex u.answer)
    show (frames levels).E (t.reindex τ) (t.reindex (g ≫ (ρ ≫ u.answer)))
    rw [eq2]
    exact ((frames levels).equivalence Θ).trans one two
  · have both : Agree (frames levels) (g ≫ (ρ ≫ u.answer)) (h ≫ (ρ ≫ u.answer)) :=
      UnificationWithLevels.Agree.trans (UnificationWithLevels.Agree.symm first) second
    have images : Agree (frames levels) (g ≫ ρ) (h ≫ ρ) := by
      apply epi
      intro t
      have moved := both t
      change (frames levels).E (t.reindex (g ≫ (ρ ≫ u.answer))) (t.reindex (h ≫ (ρ ≫ u.answer))) at moved
      rw [← Category.assoc, ← Category.assoc, reindex_comp t (g ≫ ρ), reindex_comp t (h ≫ ρ)] at moved
      exact moved
    exact initial.unique Θ (g ≫ ρ) g h (UnificationWithLevels.Agree.refl _) images

/-- **The older-unknown transition carries initial solutions**: on its class, an initial solution of the
transported store, composed with the transition's answer, is an initial solution of the store. -/
theorem olderTransition_initial (Γ : Context rules) {A : TypeOver Γ} (T : Term Γ A)
    (H : Helpers (extend Γ A)) (I : EquationStore (TotalTerm H.frame))
    (entails : ∀ (Θ : Context rules) (τ : Θ ⟶ H.frame), (frames levels).Models τ I →
      (frames levels).Models τ (weakenStore levels H [Elimination.definition Γ T]))
    {M : Context rules} {ρ : M ⟶ (olderTransition levels Γ T H).target}
    (initial : InitialSolution (frames levels)
      ((frames levels).applyStore (olderTransition levels Γ T H).answer I) ρ) :
    InitialSolution (frames levels) I (ρ ≫ (olderTransition levels Γ T H).answer) :=
  initial_along levels (updateAlong levels (olderTransition levels Γ T H) I entails)
    (olderTransition_epi levels Γ T H) initial

/-- **The older-unknown transition is exact on its class**: a store over `Γ, X : A, H` that entails the
definition of `X` by `T`, carried past `H`, has exactly the solutions that factor through the answer
by a solution of the store transported there. -/
theorem olderTransition_exact (Γ : Context rules) {A : TypeOver Γ} (T : Term Γ A)
    (H : Helpers (extend Γ A)) (I : EquationStore (TotalTerm H.frame))
    (entails : ∀ (Θ : Context rules) (τ : Θ ⟶ H.frame), (frames levels).Models τ I →
      (frames levels).Models τ (weakenStore levels H [Elimination.definition Γ T])) :
    Exact (frames levels) I (olderTransition levels Γ T H).answer
      ((frames levels).applyStore (olderTransition levels Γ T H).answer I) :=
  update_exact levels (updateAlong levels (olderTransition levels Γ T H) I entails)

end Transition

/-! ## The class: a heterogeneous equation whose left type is the older unknown -/

section Twin

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L} [DecidableEq Head]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)
include facts roots heads algebra rigid complete

omit [DecidableEq Head] in
/-- **A heterogeneous equation entails the carried definition of its older type unknown.** Let the
carried definition be `d`, comparing the unknown `X` with `T` at the universe `head u`. An equation `e`
whose left type has the code of `X` carried past `H`, whose right type has the code of `T` carried past
`H`, both typed at `u` (formed at `u`, or below it), entails `d`: a solution of `e` makes its two types
equal at some universe, hence at `u`. -/
theorem entails_definition_of_twin {Δ : Context S.R} (e d : Equation (TotalTerm Δ)) {u : Head}
    (hu : S.R.isUniverse u) (universeCode : d.1.1.code = .head u) (sameType : d.2.1.code = d.1.1.code)
    (leftCode : e.1.1.code = d.1.2.code) (rightCode : e.2.1.code = d.2.2.code)
    (leftAt : Typed S.R Δ.raw e.1.1.code (.head u)) (rightAt : Typed S.R Δ.raw e.2.1.code (.head u))
    {Θ : Context S.R} (τ : Θ ⟶ Δ) (solved : (frames S.levels).Solves τ e) : (frames S.levels).Solves τ d := by
  obtain ⟨agree, -⟩ := (ContextualDependentTwins.solves_iff S.levels τ e).mp solved
  have equal := ContextualDependentUniverseInjective.equal_at_universe (S := S) facts roots heads algebra
    rigid complete Θ.formed hu (leftAt.substitute τ.typed) (rightAt.substitute τ.typed) agree
  rw [leftCode, rightCode] at equal
  refine (ContextualDependentTwins.solves_iff S.levels τ d).mpr ⟨?_, ?_⟩
  · show TypeEq S.R Θ.raw (subst τ.substitution d.1.1.code) (subst τ.substitution d.2.1.code)
    rw [sameType]
    exact IsType.refl ((d.1.1.reindex τ).isType)
  · show Equal S.R Θ.raw (subst τ.substitution d.1.2.code) (subst τ.substitution d.2.2.code)
      (subst τ.substitution d.1.1.code)
    rw [universeCode]
    exact equal

end Twin

/-! ## The tower's older-unknown family -/

namespace OlderUnknown

open ComputableControls
open Interface.DependentFull.Controls (setting rigid)

/-- **The tower's type extraction**, with its equivalence. -/
def prepareTower {Δ : Context setting.R} (I : EquationStore (TotalTerm Δ)) :
    {J : EquationStore (TotalTerm Δ) // (frames setting.levels).Equivalent I J} :=
  ⟨extract setting.levels ExecutableTowerChoices.choices I,
    extract_equivalent (S := setting) ExecutableTowerChoices.choices TowerModel.facts TowerModel.roots
      TowerModel.heads TowerModel.algebra rigid TowerModel.complete I⟩

/-- The tree's in-place solver of the tower, at budget 16. -/
abbrev inPlace : ContextualDependentWorklist.Solver setting.levels :=
  ContextualDependentInPlace.Controls.inPlaceOnly

/-- **The older-unknown family**: type extraction, then the tree's in-place solver as the worklist
driver, settling along a covering answer. -/
def olderFamily (fuel : Nat) : Family setting.levels :=
  Family.prepared setting.levels (fun I => prepareTower I) (driverFamily setting.levels inPlace fuel)

/-- The rounds the settler gives the older-unknown family: each older unknown takes an in-place round and
each woken equation a round of its own. -/
abbrev olderFuel : Nat := 16

/-- **The tower's families with the older-unknown family.** -/
def olderFamilies : List (Family setting.levels) :=
  towerFamilies ++ ([olderFamily olderFuel] : List (Family setting.levels))

/-- **The computable settler with the older-unknown family.** -/
def olderSettler : Settler setting.levels := Settler.ofFamilies setting.levels olderFamilies

/-- The older-unknown family decides a store exactly when the in-place driver decides its extraction. -/
theorem olderFamily_decisive_iff (fuel : Nat) {Δ : Context setting.R} (I : EquationStore (TotalTerm Δ)) :
    (olderFamily fuel I).Decisive ↔
      (driverFamily setting.levels inPlace fuel (extract setting.levels ExecutableTowerChoices.choices I)).Decisive :=
  Decision.ofEquivalent_decisive (prepareTower I).property _

/-- **Exactness**: where the older-unknown family settles, its answer is an initial solution, and the
solutions of the store are exactly the composites with it. -/
theorem olderFamily_exact (fuel : Nat) {Δ M : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    {σ : M ⟶ Δ} {initial : InitialSolution (frames setting.levels) I σ}
    (_ : olderFamily fuel I = .settled M σ initial) (Θ : Context setting.R) (τ : Θ ⟶ Δ) :
    (frames setting.levels).Models τ I ↔ ∃ g : Θ ⟶ M, Agree (frames setting.levels) τ (g ≫ σ) :=
  initial_exact initial Θ τ

/-- **On the union of the decided fragments the computable settler agrees with the semantic one**:
both settle exactly the solvable stores, along answers inverse to each other up to agreement. -/
theorem older_agrees_ideal {Δ : Context setting.R} {I : EquationStore (TotalTerm Δ)}
    (decided : DecidedBy setting.levels olderFamilies I) :
    ((∃ (M : Context setting.R) (σ : M ⟶ Δ) (initial : InitialSolution (frames setting.levels) I σ),
        olderSettler I = .settled M σ initial) ↔ (frames setting.levels).Solvable I) ∧
      ((∃ (M : Context setting.R) (σ : M ⟶ Δ) (initial : InitialSolution (frames setting.levels) I σ),
        Settler.ideal setting.levels I = .settled M σ initial) ↔ (frames setting.levels).Solvable I) ∧
      ∀ (M M' : Context setting.R) (σ : M ⟶ Δ) (σ' : M' ⟶ Δ)
        (initial : InitialSolution (frames setting.levels) I σ)
        (initial' : InitialSolution (frames setting.levels) I σ'),
        olderSettler I = .settled M σ initial → Settler.ideal setting.levels I = .settled M' σ' initial' →
        ∃ (g : M ⟶ M') (g' : M' ⟶ M), Agree (frames setting.levels) σ (g ≫ σ') ∧
          Agree (frames setting.levels) σ' (g' ≫ σ) ∧ Agree (frames setting.levels) (g ≫ g') (𝟙 M) ∧
          Agree (frames setting.levels) (g' ≫ g) (𝟙 M') :=
  ofFamilies_agrees_ideal setting.levels decided

/-- **The converting step with the computable settler admits what the semantic one admits** on the union
of the decided fragments. -/
theorem older_converting_iff_ideal {s : State setting.R Nat} {f : Firing setting.levels s}
    (decided : DecidedBy setting.levels olderFamilies f.information) :
    (convertingStep setting.levels Nat olderSettler).Admits f ↔
      (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f :=
  ofFamilies_converting_iff_ideal setting.levels olderFamilies decided

/-- **The templating step with the computable settler admits what the semantic one admits** on the
union of the decided fragments. -/
theorem older_templating_iff_ideal {s : State setting.R Nat} {f : Firing setting.levels s}
    (decided : DecidedBy setting.levels olderFamilies f.information) :
    (templatingStep setting.levels Nat olderSettler).Admits f ↔
      (templatingStep setting.levels Nat (Settler.ideal setting.levels)).Admits f :=
  ofFamilies_templating_iff_ideal setting.levels olderFamilies decided

end OlderUnknown

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.typeEquation?_codes
#print axioms NativeTypesOnTheStep.typeEquation?_solves
#print axioms NativeTypesOnTheStep.extract_equivalent
#print axioms NativeTypesOnTheStep.Decision.ofEquivalent
#print axioms NativeTypesOnTheStep.Decision.ofEquivalent_decisive
#print axioms NativeTypesOnTheStep.Family.prepared
#print axioms NativeTypesOnTheStep.initial_exact
#print axioms NativeTypesOnTheStep.liftThrough_remaining
#print axioms NativeTypesOnTheStep.updateAlong
#print axioms NativeTypesOnTheStep.update_exact
#print axioms NativeTypesOnTheStep.instantiate_epi
#print axioms NativeTypesOnTheStep.lift_epi
#print axioms NativeTypesOnTheStep.liftThrough_epi
#print axioms NativeTypesOnTheStep.olderTransition_epi
#print axioms NativeTypesOnTheStep.initial_along
#print axioms NativeTypesOnTheStep.olderTransition_initial
#print axioms NativeTypesOnTheStep.olderTransition_principal
#print axioms NativeTypesOnTheStep.olderTransition_exact
#print axioms NativeTypesOnTheStep.entails_definition_of_twin
#print axioms NativeTypesOnTheStep.OlderUnknown.olderFamily
#print axioms NativeTypesOnTheStep.OlderUnknown.olderSettler
#print axioms NativeTypesOnTheStep.OlderUnknown.olderFamily_decisive_iff
#print axioms NativeTypesOnTheStep.OlderUnknown.olderFamily_exact
#print axioms NativeTypesOnTheStep.OlderUnknown.older_agrees_ideal
#print axioms NativeTypesOnTheStep.OlderUnknown.older_converting_iff_ideal
#print axioms NativeTypesOnTheStep.OlderUnknown.older_templating_iff_ideal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
