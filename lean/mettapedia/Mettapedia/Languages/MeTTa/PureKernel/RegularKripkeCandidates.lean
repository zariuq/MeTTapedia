import Mettapedia.Languages.MeTTa.PureKernel.RegularReducibility

/-!
# Scope-aware candidates for regular Pure normalization

This module lifts the fixed-scope reducibility algebra to renaming-stable
function candidates.  Membership of a function is tested in every future
scope and against every argument admitted by the domain candidate.  It then
adds an argument-indexed codomain with the reduction transport needed by the
dependent function construction.  The module still stops short of a full
candidate model for contexts: substitution naturality, semantic environments,
and the fundamental lemma are supplied by later layers.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing

/-! ## Accessibility and neutrality across worlds -/

/-- If a renamed term is strongly normalizing, the source term is strongly
normalizing.  Every source reduction maps to a reduction in the future scope;
injectivity of the renaming is unnecessary. -/
theorem reductionAccessible_of_rename (ρ : Ren n m) {term : PureTm n}
    (accessible : ReductionAccessible (rename ρ term)) :
    ReductionAccessible term := by
  have reflect : ∀ renamed : PureTm m, ReductionAccessible renamed →
      ∀ source : PureTm n, renamed = rename ρ source →
        ReductionAccessible source := by
    intro renamed renamedAccessible
    induction renamedAccessible with
    | intro renamed smaller ih =>
        intro source sourceEq
        constructor
        intro target step
        have mapped : Red (rename ρ source) (rename ρ target) :=
          red_rename step ρ
        have mappedFromRenamed : Red renamed (rename ρ target) := by
          rw [sourceEq]
          exact mapped
        exact ih (rename ρ target) mappedFromRenamed target rfl
  exact reflect (rename ρ term) accessible term rfl

/-- Renaming preserves the outer neutral form. -/
theorem IsNeutral.rename {term : PureTm n} (neutral : IsNeutral term)
    (ρ : Ren n m) : IsNeutral (rename ρ term) := by
  cases term with
  | var => trivial
  | const => trivial
  | u0 => cases neutral
  | u1 => cases neutral
  | pi => cases neutral
  | sigma => cases neutral
  | id => cases neutral
  | lam => cases neutral
  | app function argument =>
      cases function <;>
        simp_all [IsNeutral,
          Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename]
  | pair => cases neutral
  | fst pair =>
      cases pair <;>
        simp_all [IsNeutral,
          Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename]
  | snd pair =>
      cases pair <;>
        simp_all [IsNeutral,
          Mettapedia.Languages.MeTTa.PureKernel.Renaming.rename]
  | refl => cases neutral

namespace ReductionCandidate.RenamingStable

/-- Every reducibility candidate contains every variable: variables are
neutral and have no reducts. -/
theorem variable_mem (family : ReductionCandidate.RenamingStable)
    (index : Fin n) :
    (family.fibre n).pred (.var index) := by
  apply (family.fibre n).cr3 (neutral_var index)
  intro target step
  cases step

/-! ## Kripke function space -/

/-- The function candidate at one source scope.  A member must continue to map
domain members to codomain members after every renaming into a future scope. -/
def arrowFibre (domain codomain : ReductionCandidate.RenamingStable)
    (n : Nat) : ReductionCandidate n where
  pred := fun function =>
    ∀ {m : Nat} (ρ : Ren n m) (argument : PureTm m),
      (domain.fibre m).pred argument →
        (codomain.fibre m).pred (.app (rename ρ function) argument)
  cr1 := by
    intro function covered
    have argumentCovered :
        (domain.fibre (n + 1)).pred (.var (0 : Fin (n + 1))) :=
      domain.variable_mem 0
    have applicationCovered := covered wk (.var 0) argumentCovered
    have renamedAccessible := reductionAccessible_app_left
      ((codomain.fibre (n + 1)).cr1 applicationCovered)
    exact reductionAccessible_of_rename wk renamedAccessible
  cr2 := by
    intro source target covered sourceStep m ρ argument argumentCovered
    exact (codomain.fibre m).cr2
      (covered ρ argument argumentCovered)
      (.congAppFun (red_rename sourceStep ρ))
  cr3 := by
    intro function functionNeutral functionReducts m ρ argument argumentCovered
    have renamedNeutral := functionNeutral.rename ρ
    have argumentAccessible := (domain.fibre m).cr1 argumentCovered
    induction argumentAccessible with
    | intro argument smallerArgument ih =>
        apply (codomain.fibre m).cr3 (neutral_app renamedNeutral)
        intro target step
        rcases neutral_app_step renamedNeutral step with
          ⟨renamedFunction, functionStep, rfl⟩ |
            ⟨argument', argumentStep, rfl⟩
        · obtain ⟨sourceFunction, sourceStep, rfl⟩ :=
            red_rename_reflect ρ functionStep
          exact functionReducts sourceFunction sourceStep
            ρ argument argumentCovered
        · exact ih argument' argumentStep
            ((domain.fibre m).cr2 argumentCovered argumentStep)

/-- The Kripke function construction is itself stable under renaming. -/
def arrow (domain codomain : ReductionCandidate.RenamingStable) :
    ReductionCandidate.RenamingStable where
  fibre := arrowFibre domain codomain
  rename_mem := by
    intro n m ξ function covered k ρ argument argumentCovered
    have mapped := covered (fun index => ρ (ξ index)) argument argumentCovered
    simpa only [rename_comp] using mapped

theorem arrow_pred (domain codomain : ReductionCandidate.RenamingStable)
    (function : PureTm n) :
    ((arrow domain codomain).fibre n).pred function ↔
      ∀ {m : Nat} (ρ : Ren n m) (argument : PureTm m),
        (domain.fibre m).pred argument →
          (codomain.fibre m).pred (.app (rename ρ function) argument) :=
  Iff.rfl

/-! ## A second, strict candidate family

Strong normalization alone cannot witness genuine variation between argument
fibres.  The following saturated candidate additionally excludes terms that
can reduce to `U0`.  It remains closed under reduction and neutral expansion,
so it is a real reducibility candidate rather than an arbitrary predicate. -/

/-- A multi-step reduction starting from a renamed term can be reflected to a
multi-step reduction at the source scope. -/
theorem redStar_rename_reflect (ρ : Ren n m) {source : PureTm n}
    {renamedTarget : PureTm m}
    (steps : RedStar (rename ρ source) renamedTarget) :
    ∃ target : PureTm n,
      RedStar source target ∧ renamedTarget = rename ρ target := by
  induction steps with
  | refl => exact ⟨source, RedStar.refl source, rfl⟩
  | tail prefixSteps finalStep ih =>
      obtain ⟨middle, sourceSteps, rfl⟩ := ih
      obtain ⟨target, sourceStep, rfl⟩ :=
        red_rename_reflect ρ finalStep
      exact ⟨target, RedStar.tail sourceSteps sourceStep, rfl⟩

/-- Renaming cannot turn a different outer constructor into `U0`. -/
theorem eq_u0_of_rename_eq_u0 (ρ : Ren n m) {term : PureTm n}
    (equal : rename ρ term = (.u0 : PureTm m)) : term = .u0 := by
  cases term <;> simp_all [rename]

/-- The saturated candidate of strongly normalizing terms that never reduce
to `U0`. -/
def avoidingU0 (n : Nat) : ReductionCandidate n where
  pred := fun term =>
    ReductionAccessible term ∧ ¬ RedStar term (.u0 : PureTm n)
  cr1 := fun covered => covered.1
  cr2 := by
    intro source target covered step
    refine ⟨covered.1.of_red step, ?_⟩
    intro targetToU0
    exact covered.2 (RedStar.trans (red_to_redStar step) targetToU0)
  cr3 := by
    intro term neutral reducts
    constructor
    · constructor
      intro target step
      exact (reducts target step).1
    · intro reachesU0
      induction reachesU0 using Relation.ReflTransGen.head_induction_on with
      | refl => cases neutral
      | @head source target first rest ih =>
          exact (reducts target first).2 rest

theorem avoidingU0_pred (term : PureTm n) :
    (avoidingU0 n).pred term ↔
      ReductionAccessible term ∧ ¬ RedStar term (.u0 : PureTm n) :=
  Iff.rfl

/-- Avoidance of `U0` is stable under arbitrary variable renaming. -/
def avoidingU0Family : ReductionCandidate.RenamingStable where
  fibre := avoidingU0
  rename_mem := by
    intro n m ρ term covered
    constructor
    · exact reductionAccessible_rename ρ covered.1
    · intro renamedToU0
      obtain ⟨target, sourceSteps, targetRenamesToU0⟩ :=
        redStar_rename_reflect ρ renamedToU0
      have targetIsU0 : target = (.u0 : PureTm n) :=
        eq_u0_of_rename_eq_u0 ρ targetRenamesToU0.symm
      exact covered.2 (targetIsU0 ▸ sourceSteps)

/-- `U1` cannot reduce to `U0`; both are distinct normal forms. -/
theorem u1_not_redStar_u0 :
    ¬ RedStar (.u1 : PureTm n) (.u0 : PureTm n) := by
  intro steps
  rcases Relation.ReflTransGen.cases_head steps with equal | ⟨target, first, rest⟩
  · cases equal
  · cases first

theorem u0_not_in_avoidingU0 :
    ¬ (avoidingU0 n).pred (.u0 : PureTm n) := by
  intro covered
  exact covered.2 (RedStar.refl .u0)

theorem u1_in_avoidingU0 :
    (avoidingU0 n).pred (.u1 : PureTm n) :=
  ⟨reductionAccessible_u1, u1_not_redStar_u0⟩

/-! ## Argument-indexed codomains

The codomain of a dependent function varies with its argument.  Reduction of
that argument therefore changes the index of the candidate used by the
induction hypothesis.  The following structure records exactly the conversion
coherence needed to move the result back to the source fibre.  It deliberately
does not yet claim the full substitution naturality required of a semantic
type family. -/

/-- A family of reduction candidates indexed by terms, contravariantly stable
along one-step reduction of the index. -/
structure ReductionStableCodomain
    (domain : ReductionCandidate.RenamingStable) where
  fibre : {n : Nat} → PureTm n → ReductionCandidate n
  backward_of_red : ∀ {n : Nat} {source target result : PureTm n},
    Red source target →
      (fibre target).pred result → (fibre source).pred result

namespace ReductionStableCodomain

/-- Every scope-indexed candidate family gives a constant dependent
codomain.  This is the calibration embedding of nondependent arrows into the
argument-indexed construction. -/
def constant (domain codomain : ReductionCandidate.RenamingStable) :
    ReductionStableCodomain domain where
  fibre := fun _ => codomain.fibre _
  backward_of_red := fun _ covered => covered

/-- Candidate selected by whether its index can reduce to `U0`.  The positive
branch is the full normalizing candidate; the negative branch is the strict
`avoidingU0` candidate. -/
noncomputable def selectedByReachesU0 {n : Nat} (argument : PureTm n) :
    ReductionCandidate n := by
  classical
  exact if RedStar argument (.u0 : PureTm n) then
      ReductionCandidate.normalizing n
    else
      avoidingU0 n

/-- A genuinely argument-sensitive codomain.  Reduction of an index can only
move from the strict branch into the larger normalizing branch, so backward
transport is sound. -/
noncomputable def selected (domain : ReductionCandidate.RenamingStable) :
    ReductionStableCodomain domain where
  fibre := selectedByReachesU0
  backward_of_red := by
    intro n source target result sourceStep covered
    by_cases sourceReaches : RedStar source (.u0 : PureTm n)
    · rw [selectedByReachesU0, if_pos sourceReaches]
      exact (selectedByReachesU0 target).cr1 covered
    · have targetAvoids : ¬ RedStar target (.u0 : PureTm n) := by
        intro targetReaches
        exact sourceReaches
          (RedStar.trans (red_to_redStar sourceStep) targetReaches)
      simpa [selectedByReachesU0, sourceReaches, targetAvoids] using covered

/-- The selected family is nonconstant: `U0` belongs to the fibre indexed by
`U0`, but not to the fibre indexed by `U1`. -/
theorem selected_is_genuinely_argument_sensitive
    (domain : ReductionCandidate.RenamingStable) :
    ((selected domain).fibre (.u0 : PureTm n)).pred .u0 ∧
      ¬ ((selected domain).fibre (.u1 : PureTm n)).pred .u0 := by
  constructor
  · change (selectedByReachesU0 (.u0 : PureTm n)).pred .u0
    rw [selectedByReachesU0, if_pos (RedStar.refl .u0)]
    change ReductionAccessible (.u0 : PureTm n)
    exact reductionAccessible_u0
  · change ¬ (selectedByReachesU0 (.u1 : PureTm n)).pred .u0
    rw [selectedByReachesU0, if_neg u1_not_redStar_u0]
    exact u0_not_in_avoidingU0

end ReductionStableCodomain

/-- The dependent function candidate at one source scope.  In addition to
Kripke quantification over future scopes, the result candidate is selected by
the actual argument. -/
def dependentArrowFibre (domain : ReductionCandidate.RenamingStable)
    (codomain : ReductionStableCodomain domain) (n : Nat) :
    ReductionCandidate n where
  pred := fun function =>
    ∀ {m : Nat} (ρ : Ren n m) (argument : PureTm m),
      (domain.fibre m).pred argument →
        (codomain.fibre argument).pred (.app (rename ρ function) argument)
  cr1 := by
    intro function covered
    have argumentCovered :
        (domain.fibre (n + 1)).pred (.var (0 : Fin (n + 1))) :=
      domain.variable_mem 0
    have applicationCovered := covered wk (.var 0) argumentCovered
    have renamedAccessible := reductionAccessible_app_left
      ((codomain.fibre (.var (0 : Fin (n + 1)))).cr1 applicationCovered)
    exact reductionAccessible_of_rename wk renamedAccessible
  cr2 := by
    intro source target covered sourceStep m ρ argument argumentCovered
    exact (codomain.fibre argument).cr2
      (covered ρ argument argumentCovered)
      (.congAppFun (red_rename sourceStep ρ))
  cr3 := by
    intro function functionNeutral functionReducts m ρ argument argumentCovered
    have renamedNeutral := functionNeutral.rename ρ
    have argumentAccessible := (domain.fibre m).cr1 argumentCovered
    induction argumentAccessible with
    | intro argument smallerArgument ih =>
        apply (codomain.fibre argument).cr3 (neutral_app renamedNeutral)
        intro target step
        rcases neutral_app_step renamedNeutral step with
          ⟨renamedFunction, functionStep, rfl⟩ |
            ⟨argument', argumentStep, rfl⟩
        · obtain ⟨sourceFunction, sourceStep, rfl⟩ :=
            red_rename_reflect ρ functionStep
          exact functionReducts sourceFunction sourceStep
            ρ argument argumentCovered
        · exact codomain.backward_of_red argumentStep
            (ih argument' argumentStep
              ((domain.fibre m).cr2 argumentCovered argumentStep))

/-- Argument-indexed function candidates remain stable under renaming of the
function's source context. -/
def dependentArrow (domain : ReductionCandidate.RenamingStable)
    (codomain : ReductionStableCodomain domain) :
    ReductionCandidate.RenamingStable where
  fibre := dependentArrowFibre domain codomain
  rename_mem := by
    intro n m ξ function covered k ρ argument argumentCovered
    have mapped := covered (fun index => ρ (ξ index)) argument argumentCovered
    simpa only [rename_comp] using mapped

theorem dependentArrow_pred (domain : ReductionCandidate.RenamingStable)
    (codomain : ReductionStableCodomain domain) (function : PureTm n) :
    ((dependentArrow domain codomain).fibre n).pred function ↔
      ∀ {m : Nat} (ρ : Ren n m) (argument : PureTm m),
        (domain.fibre m).pred argument →
          (codomain.fibre argument).pred
            (.app (rename ρ function) argument) :=
  Iff.rfl

/-- The dependent construction conservatively extends the nondependent one:
constant codomains have exactly the old membership predicate. -/
theorem dependentArrow_constant_pred
    (domain codomain : ReductionCandidate.RenamingStable)
    (function : PureTm n) :
    ((dependentArrow domain (ReductionStableCodomain.constant domain codomain)).fibre n).pred
        function ↔
      ((arrow domain codomain).fibre n).pred function :=
  Iff.rfl

end ReductionCandidate.RenamingStable

/-! ## Positive and negative canaries -/

def normalizingKripkeArrow : ReductionCandidate.RenamingStable :=
  ReductionCandidate.RenamingStable.arrow
    ReductionCandidate.RenamingStable.normalizing
    ReductionCandidate.RenamingStable.normalizing

/-- The identity function behaves uniformly in every future scope. -/
theorem identity_in_normalizingKripkeArrow :
    (normalizingKripkeArrow.fibre 0).pred (.lam (.var 0)) := by
  intro m ρ argument argumentAccessible
  change ReductionAccessible argument at argumentAccessible
  change ReductionAccessible
    (.app (rename ρ (.lam (.var (0 : Fin 1)))) argument)
  simpa [rename, liftRen] using
    (reductionAccessible_identity_application
      (n := m) (argument := argument) argumentAccessible)

/-- The normal delta term is excluded because function membership observes
its looping self-application. -/
theorem delta_not_in_normalizingKripkeArrow :
    ¬ (normalizingKripkeArrow.fibre 0).pred regularDelta := by
  intro covered
  have omegaAccessible := covered idRen regularDelta
    regularDelta_reductionAccessible
  change ReductionAccessible regularOmega at omegaAccessible
  exact omega_not_in_normalizing_candidate omegaAccessible

/-! ## Axiom audit -/

#print axioms reductionAccessible_of_rename
#print axioms IsNeutral.rename
#print axioms ReductionCandidate.RenamingStable.variable_mem
#print axioms ReductionCandidate.RenamingStable.arrow_pred
#print axioms ReductionCandidate.RenamingStable.redStar_rename_reflect
#print axioms ReductionCandidate.RenamingStable.avoidingU0_pred
#print axioms ReductionCandidate.RenamingStable.u0_not_in_avoidingU0
#print axioms ReductionCandidate.RenamingStable.u1_in_avoidingU0
#print axioms ReductionCandidate.RenamingStable.ReductionStableCodomain.selected_is_genuinely_argument_sensitive
#print axioms ReductionCandidate.RenamingStable.dependentArrow_pred
#print axioms ReductionCandidate.RenamingStable.dependentArrow_constant_pred
#print axioms identity_in_normalizingKripkeArrow
#print axioms delta_not_in_normalizingKripkeArrow

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
