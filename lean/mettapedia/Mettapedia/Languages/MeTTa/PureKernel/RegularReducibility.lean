import Mettapedia.Languages.MeTTa.PureKernel.RegularNormalizationAlgorithm

/-!
# Reducibility infrastructure for regular Pure normalization

The executable normalizer is total on `ReductionAccessible`.  This module
develops the proof algebra needed to establish that accessibility for typed
terms.  It deliberately stops short of the fundamental theorem: constructor
closure alone cannot prove accessibility of application, as the self-
application counterexample demonstrates.  The remaining bridge therefore has
to be a genuinely type-indexed logical relation.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.Languages.MeTTa.PureKernel.Reduction

/-! ## Basic accessibility API -/

/-- Every immediate reduct of a strongly normalizing term is strongly
normalizing. -/
theorem ReductionAccessible.of_red {source target : PureTm n}
    (sourceAccessible : ReductionAccessible source)
    (step : Red source target) : ReductionAccessible target :=
  Acc.inv sourceAccessible step

/-! Renaming may identify variables, but it cannot create a beta or projection
redex.  Reflecting a step through renaming is the key fact needed to transport
accessibility between de Bruijn scopes. -/

private theorem rename_eq_lam (ρ : Ren n m) {term : PureTm n}
    {body : PureTm (m + 1)} (equal : rename ρ term = .lam body) :
    ∃ sourceBody : PureTm (n + 1),
      term = .lam sourceBody ∧ body = rename (liftRen ρ) sourceBody := by
  cases term <;> cases equal
  exact ⟨_, rfl, rfl⟩

private theorem rename_eq_pair (ρ : Ren n m) {term : PureTm n}
    {first second : PureTm m} (equal : rename ρ term = .pair first second) :
    ∃ sourceFirst sourceSecond : PureTm n,
      term = .pair sourceFirst sourceSecond ∧
        first = rename ρ sourceFirst ∧ second = rename ρ sourceSecond := by
  cases term <;> cases equal
  exact ⟨_, _, rfl, rfl, rfl⟩

private theorem red_app_cases {function argument target : PureTm n}
    (step : Red (.app function argument) target) :
    (∃ body, function = .lam body ∧ target = inst0 argument body) ∨
      (∃ function', Red function function' ∧
        target = .app function' argument) ∨
      (∃ argument', Red argument argument' ∧
        target = .app function argument') := by
  cases step with
  | betaPi body argument => exact .inl ⟨body, rfl, rfl⟩
  | congAppFun functionStep => exact .inr (.inl ⟨_, functionStep, rfl⟩)
  | congAppArg argumentStep => exact .inr (.inr ⟨_, argumentStep, rfl⟩)

private theorem red_fst_cases {pair target : PureTm n}
    (step : Red (.fst pair) target) :
    (∃ first second, pair = .pair first second ∧ target = first) ∨
      (∃ pair', Red pair pair' ∧ target = .fst pair') := by
  cases step with
  | betaSigmaFst => exact .inl ⟨_, _, rfl, rfl⟩
  | congFst pairStep => exact .inr ⟨_, pairStep, rfl⟩

private theorem red_snd_cases {pair target : PureTm n}
    (step : Red (.snd pair) target) :
    (∃ first second, pair = .pair first second ∧ target = second) ∨
      (∃ pair', Red pair pair' ∧ target = .snd pair') := by
  cases step with
  | betaSigmaSnd => exact .inl ⟨_, _, rfl, rfl⟩
  | congSnd pairStep => exact .inr ⟨_, pairStep, rfl⟩

theorem red_rename_reflect (ρ : Ren n m) {source : PureTm n}
    {target : PureTm m} (step : Red (rename ρ source) target) :
    ∃ reduct : PureTm n, Red source reduct ∧ target = rename ρ reduct := by
  induction source generalizing m target with
  | var i => cases step
  | const name => cases step
  | u0 => cases step
  | u1 => cases step
  | pi A B ihA ihB =>
      cases step with
      | congPiDom domainStep =>
          obtain ⟨A', sourceStep, rfl⟩ := ihA ρ domainStep
          exact ⟨.pi A' B, .congPiDom sourceStep, rfl⟩
      | congPiCod codomainStep =>
          obtain ⟨B', sourceStep, rfl⟩ := ihB (liftRen ρ) codomainStep
          exact ⟨.pi A B', .congPiCod sourceStep, rfl⟩
  | sigma A B ihA ihB =>
      cases step with
      | congSigmaDom domainStep =>
          obtain ⟨A', sourceStep, rfl⟩ := ihA ρ domainStep
          exact ⟨.sigma A' B, .congSigmaDom sourceStep, rfl⟩
      | congSigmaCod codomainStep =>
          obtain ⟨B', sourceStep, rfl⟩ := ihB (liftRen ρ) codomainStep
          exact ⟨.sigma A B', .congSigmaCod sourceStep, rfl⟩
  | id A left right ihA ihLeft ihRight =>
      cases step with
      | congIdTy typeStep =>
          obtain ⟨A', sourceStep, rfl⟩ := ihA ρ typeStep
          exact ⟨.id A' left right, .congIdTy sourceStep, rfl⟩
      | congIdLeft leftStep =>
          obtain ⟨left', sourceStep, rfl⟩ := ihLeft ρ leftStep
          exact ⟨.id A left' right, .congIdLeft sourceStep, rfl⟩
      | congIdRight rightStep =>
          obtain ⟨right', sourceStep, rfl⟩ := ihRight ρ rightStep
          exact ⟨.id A left right', .congIdRight sourceStep, rfl⟩
  | lam body ih =>
      cases step with
      | congLam bodyStep =>
          obtain ⟨body', sourceStep, rfl⟩ := ih (liftRen ρ) bodyStep
          exact ⟨.lam body', .congLam sourceStep, rfl⟩
  | app function argument ihFunction ihArgument =>
      rcases red_app_cases step with
        ⟨renamedBody, functionEq, rfl⟩ |
          ⟨renamedFunction, functionStep, rfl⟩ |
          ⟨renamedArgument, argumentStep, rfl⟩
      · obtain ⟨body, rfl, bodyEq⟩ := rename_eq_lam ρ functionEq
        subst bodyEq
        exact ⟨inst0 argument body, .betaPi body argument, by
          simp⟩
      · obtain ⟨function', sourceStep, rfl⟩ := ihFunction ρ functionStep
        exact ⟨.app function' argument, .congAppFun sourceStep, rfl⟩
      · obtain ⟨argument', sourceStep, rfl⟩ := ihArgument ρ argumentStep
        exact ⟨.app function argument', .congAppArg sourceStep, rfl⟩
  | pair first second ihFirst ihSecond =>
      cases step with
      | congPairFst firstStep =>
          obtain ⟨first', sourceStep, rfl⟩ := ihFirst ρ firstStep
          exact ⟨.pair first' second, .congPairFst sourceStep, rfl⟩
      | congPairSnd secondStep =>
          obtain ⟨second', sourceStep, rfl⟩ := ihSecond ρ secondStep
          exact ⟨.pair first second', .congPairSnd sourceStep, rfl⟩
  | fst pair ih =>
      rcases red_fst_cases step with
        ⟨renamedFirst, renamedSecond, pairEq, rfl⟩ |
          ⟨renamedPair, pairStep, rfl⟩
      · obtain ⟨first, second, rfl, firstEq, secondEq⟩ :=
          rename_eq_pair ρ pairEq
        subst firstEq
        subst secondEq
        exact ⟨first, .betaSigmaFst first second, rfl⟩
      · obtain ⟨pair', sourceStep, rfl⟩ := ih ρ pairStep
        exact ⟨.fst pair', .congFst sourceStep, rfl⟩
  | snd pair ih =>
      rcases red_snd_cases step with
        ⟨renamedFirst, renamedSecond, pairEq, rfl⟩ |
          ⟨renamedPair, pairStep, rfl⟩
      · obtain ⟨first, second, rfl, firstEq, secondEq⟩ :=
          rename_eq_pair ρ pairEq
        subst firstEq
        subst secondEq
        exact ⟨second, .betaSigmaSnd first second, rfl⟩
      · obtain ⟨pair', sourceStep, rfl⟩ := ih ρ pairStep
        exact ⟨.snd pair', .congSnd sourceStep, rfl⟩
  | refl term ih =>
      cases step with
      | congRefl termStep =>
          obtain ⟨term', sourceStep, rfl⟩ := ih ρ termStep
          exact ⟨.refl term', .congRefl sourceStep, rfl⟩

/-- Strong normalization is stable under arbitrary variable renaming.  The
proof reflects every target step back to the source rather than assuming that
the renaming is injective. -/
theorem reductionAccessible_rename (ρ : Ren n m) {term : PureTm n}
    (accessible : ReductionAccessible term) :
    ReductionAccessible (rename ρ term) := by
  induction accessible generalizing m with
  | intro term smaller ih =>
      constructor
      intro target step
      obtain ⟨reduct, sourceStep, rfl⟩ := red_rename_reflect ρ step
      exact ih reduct sourceStep ρ

theorem reductionAccessible_var (i : Fin n) :
    ReductionAccessible (.var i : PureTm n) := by
  constructor
  intro target step
  cases step

theorem reductionAccessible_const (name : DeclName) :
    ReductionAccessible (.const name : PureTm n) := by
  constructor
  intro target step
  cases step

theorem reductionAccessible_u0 : ReductionAccessible (.u0 : PureTm n) :=
  u0_reductionAccessible n

theorem reductionAccessible_u1 : ReductionAccessible (.u1 : PureTm n) :=
  u1_reductionAccessible n

/-- Accessibility is closed under dependent-function formation.  The nested
accessibility inductions account for arbitrary interleavings of reductions in
the domain and codomain. -/
theorem reductionAccessible_pi {A : PureTm n} {B : PureTm (n + 1)}
    (domainAccessible : ReductionAccessible A)
    (codomainAccessible : ReductionAccessible B) :
    ReductionAccessible (.pi A B) := by
  induction domainAccessible generalizing B with
  | intro A smallerA ihA =>
      induction codomainAccessible with
      | intro B smallerB ihB =>
          constructor
          intro target step
          cases step with
          | congPiDom domainStep =>
              exact ihA _ domainStep (Acc.intro B smallerB)
          | congPiCod codomainStep =>
              exact ihB _ codomainStep

/-- Accessibility is closed under dependent-pair formation. -/
theorem reductionAccessible_sigma {A : PureTm n} {B : PureTm (n + 1)}
    (domainAccessible : ReductionAccessible A)
    (codomainAccessible : ReductionAccessible B) :
    ReductionAccessible (.sigma A B) := by
  induction domainAccessible generalizing B with
  | intro A smallerA ihA =>
      induction codomainAccessible with
      | intro B smallerB ihB =>
          constructor
          intro target step
          cases step with
          | congSigmaDom domainStep =>
              exact ihA _ domainStep (Acc.intro B smallerB)
          | congSigmaCod codomainStep =>
              exact ihB _ codomainStep

/-- Accessibility is closed under identity-type formation. -/
theorem reductionAccessible_id {A a b : PureTm n}
    (typeAccessible : ReductionAccessible A)
    (leftAccessible : ReductionAccessible a)
    (rightAccessible : ReductionAccessible b) :
    ReductionAccessible (.id A a b) := by
  induction typeAccessible generalizing a b with
  | intro A smallerA ihA =>
      induction leftAccessible generalizing b with
      | intro a smallerLeft ihLeft =>
          induction rightAccessible with
          | intro b smallerRight ihRight =>
              constructor
              intro target step
              cases step with
              | congIdTy typeStep =>
                  exact ihA _ typeStep
                    (Acc.intro a smallerLeft) (Acc.intro b smallerRight)
              | congIdLeft leftStep =>
                  exact ihLeft _ leftStep (Acc.intro b smallerRight)
              | congIdRight rightStep =>
                  exact ihRight _ rightStep

theorem reductionAccessible_lam {body : PureTm (n + 1)}
    (bodyAccessible : ReductionAccessible body) :
    ReductionAccessible (.lam body) := by
  induction bodyAccessible with
  | intro body smaller ih =>
      constructor
      intro target step
      cases step with
      | congLam bodyStep => exact ih _ bodyStep

theorem reductionAccessible_pair {first second : PureTm n}
    (firstAccessible : ReductionAccessible first)
    (secondAccessible : ReductionAccessible second) :
    ReductionAccessible (.pair first second) := by
  induction firstAccessible generalizing second with
  | intro first smallerFirst ihFirst =>
      induction secondAccessible with
      | intro second smallerSecond ihSecond =>
          constructor
          intro target step
          cases step with
          | congPairFst firstStep =>
              exact ihFirst _ firstStep (Acc.intro second smallerSecond)
          | congPairSnd secondStep =>
              exact ihSecond _ secondStep

theorem reductionAccessible_refl {term : PureTm n}
    (termAccessible : ReductionAccessible term) :
    ReductionAccessible (.refl term) := by
  induction termAccessible with
  | intro term smaller ih =>
      constructor
      intro target step
      cases step with
      | congRefl termStep => exact ih _ termStep

/-! ## Inversion through evaluation contexts -/

/-- If an application is strongly normalizing, so is its function. -/
theorem reductionAccessible_app_left {function argument : PureTm n}
    (applicationAccessible : ReductionAccessible (.app function argument)) :
    ReductionAccessible function := by
  have inversion : ∀ (whole : PureTm n), ReductionAccessible whole →
      ∀ function argument, whole = .app function argument →
        ReductionAccessible function := by
    intro whole accessible
    induction accessible with
    | intro whole smaller ih =>
        intro function argument wholeEq
        subst wholeEq
        constructor
        intro target step
        exact ih (.app target argument) (.congAppFun step)
          target argument rfl
  exact inversion (.app function argument) applicationAccessible
    function argument rfl

/-- If an application is strongly normalizing, so is its argument. -/
theorem reductionAccessible_app_right {function argument : PureTm n}
    (applicationAccessible : ReductionAccessible (.app function argument)) :
    ReductionAccessible argument := by
  have inversion : ∀ (whole : PureTm n), ReductionAccessible whole →
      ∀ function argument, whole = .app function argument →
        ReductionAccessible argument := by
    intro whole accessible
    induction accessible with
    | intro whole smaller ih =>
        intro function argument wholeEq
        subst wholeEq
        constructor
        intro target step
        exact ih (.app function target) (.congAppArg step)
          function target rfl
  exact inversion (.app function argument) applicationAccessible
    function argument rfl

theorem reductionAccessible_fst_argument {pair : PureTm n}
    (projectionAccessible : ReductionAccessible (.fst pair)) :
    ReductionAccessible pair := by
  have inversion : ∀ (whole : PureTm n), ReductionAccessible whole →
      ∀ pair, whole = .fst pair → ReductionAccessible pair := by
    intro whole accessible
    induction accessible with
    | intro whole smaller ih =>
        intro pair wholeEq
        subst wholeEq
        constructor
        intro target step
        exact ih (.fst target) (.congFst step) target rfl
  exact inversion (.fst pair) projectionAccessible pair rfl

theorem reductionAccessible_snd_argument {pair : PureTm n}
    (projectionAccessible : ReductionAccessible (.snd pair)) :
    ReductionAccessible pair := by
  have inversion : ∀ (whole : PureTm n), ReductionAccessible whole →
      ∀ pair, whole = .snd pair → ReductionAccessible pair := by
    intro whole accessible
    induction accessible with
    | intro whole smaller ih =>
        intro pair wholeEq
        subst wholeEq
        constructor
        intro target step
        exact ih (.snd target) (.congSnd step) target rfl
  exact inversion (.snd pair) projectionAccessible pair rfl

/-! ## Reducibility candidates -/

/-- Neutral syntax is headed by a variable/declaration or an elimination.
Introduction forms and type constructors are kept separate. -/
def IsNeutral : PureTm n → Prop
  | .var _ => True
  | .const _ => True
  | .app (.lam _) _ => False
  | .app _ _ => True
  | .fst (.pair _ _) => False
  | .fst _ => True
  | .snd (.pair _ _) => False
  | .snd _ => True
  | _ => False

theorem neutral_var (i : Fin n) : IsNeutral (.var i : PureTm n) := trivial

theorem beta_application_not_neutral (body : PureTm (n + 1))
    (argument : PureTm n) :
    ¬ IsNeutral (.app (.lam body) argument) := by
  intro _
  trivial

theorem neutral_app {function argument : PureTm n}
    (neutral : IsNeutral function) : IsNeutral (.app function argument) := by
  cases function <;> simp_all [IsNeutral]

theorem neutral_fst {pair : PureTm n} (neutral : IsNeutral pair) :
    IsNeutral (.fst pair) := by
  cases pair <;> simp_all [IsNeutral]

theorem neutral_snd {pair : PureTm n} (neutral : IsNeutral pair) :
    IsNeutral (.snd pair) := by
  cases pair <;> simp_all [IsNeutral]

/-- A step from a neutral-headed application comes from exactly one of its
components; the beta case is excluded by neutrality of the function. -/
theorem neutral_app_step {function argument target : PureTm n}
    (neutral : IsNeutral function) (step : Red (.app function argument) target) :
    (∃ function', Red function function' ∧ target = .app function' argument) ∨
      (∃ argument', Red argument argument' ∧
        target = .app function argument') := by
  cases step with
  | betaPi body argument =>
      exact False.elim (beta_application_not_neutral body argument neutral)
  | congAppFun functionStep => exact .inl ⟨_, functionStep, rfl⟩
  | congAppArg argumentStep => exact .inr ⟨_, argumentStep, rfl⟩

theorem neutral_fst_step {pair target : PureTm n}
    (neutral : IsNeutral pair) (step : Red (.fst pair) target) :
    ∃ pair', Red pair pair' ∧ target = .fst pair' := by
  cases step with
  | betaSigmaFst first second =>
      cases neutral
  | congFst pairStep => exact ⟨_, pairStep, rfl⟩

theorem neutral_snd_step {pair target : PureTm n}
    (neutral : IsNeutral pair) (step : Red (.snd pair) target) :
    ∃ pair', Red pair pair' ∧ target = .snd pair' := by
  cases step with
  | betaSigmaSnd first second =>
      cases neutral
  | congSnd pairStep => exact ⟨_, pairStep, rfl⟩

/-- A reducibility candidate packages the three closure laws used by the
logical-relations proof.  It is scoped at one de Bruijn depth; the later
Kripke layer supplies coherent transport between depths. -/
structure ReductionCandidate (n : Nat) where
  pred : PureTm n → Prop
  cr1 : ∀ {term}, pred term → ReductionAccessible term
  cr2 : ∀ {source target}, pred source → Red source target → pred target
  cr3 : ∀ {term}, IsNeutral term →
    (∀ target, Red term target → pred target) → pred term

namespace ReductionCandidate

/-- Candidate intersection retains proof-relevant restrictions instead of
erasing them to strong normalization. -/
def inter (left right : ReductionCandidate n) : ReductionCandidate n where
  pred := fun term => left.pred term ∧ right.pred term
  cr1 := fun covered => left.cr1 covered.1
  cr2 := fun covered step =>
    ⟨left.cr2 covered.1 step, right.cr2 covered.2 step⟩
  cr3 := fun neutral reducts =>
    ⟨left.cr3 neutral (fun target step => (reducts target step).1),
      right.cr3 neutral (fun target step => (reducts target step).2)⟩

theorem inter_pred (left right : ReductionCandidate n) (term : PureTm n) :
    (left.inter right).pred term ↔ left.pred term ∧ right.pred term :=
  Iff.rfl

/-- Strong normalization itself is a nondegenerate reducibility candidate. -/
def normalizing (n : Nat) : ReductionCandidate n where
  pred := ReductionAccessible
  cr1 := fun covered => covered
  cr2 := fun covered step => covered.of_red step
  cr3 := fun _ reducts => Acc.intro _ reducts

theorem normalizing_pred (term : PureTm n) :
    (normalizing n).pred term ↔ ReductionAccessible term :=
  Iff.rfl

/-- A scope-indexed candidate whose membership is stable under every variable
renaming.  This is the presheaf-level structure actually established here;
substitution stability requires candidate-respecting environments and is a
strictly stronger later theorem. -/
structure RenamingStable where
  fibre : (n : Nat) → ReductionCandidate n
  rename_mem : ∀ {n m : Nat} (ρ : Ren n m) {term : PureTm n},
    (fibre n).pred term → (fibre m).pred (rename ρ term)

namespace RenamingStable

/-- Strong normalization across all scopes is a renaming-stable candidate. -/
def normalizing : RenamingStable where
  fibre := ReductionCandidate.normalizing
  rename_mem := by
    intro n m ρ term covered
    exact reductionAccessible_rename ρ covered

theorem normalizing_fibre_pred (term : PureTm n) :
    (normalizing.fibre n).pred term ↔ ReductionAccessible term :=
  Iff.rfl

end RenamingStable

/-- A pointed candidate supplies one reducible probe.  Pointedness is needed
only to derive CR1 for function-space candidates at a fixed scope; the later
Kripke construction obtains such probes from fresh variables. -/
structure Pointed (n : Nat) extends ReductionCandidate n where
  point : PureTm n
  point_mem : pred point

/-- The normalizing candidate can be pointed by any already accessible term. -/
def normalizingPointed (point : PureTm n)
    (accessible : ReductionAccessible point) : Pointed n where
  toReductionCandidate := normalizing n
  point := point
  point_mem := accessible

/-- Nondependent function-space construction.  This is the first genuine
type-indexed candidate operation.  Its CR3 proof performs accessibility
induction on the argument; component accessibility alone is insufficient. -/
def arrow (domain : Pointed n) (codomain : ReductionCandidate n) :
    ReductionCandidate n where
  pred := fun function => ∀ argument, domain.pred argument →
    codomain.pred (.app function argument)
  cr1 := by
    intro function covered
    exact reductionAccessible_app_left
      (codomain.cr1 (covered domain.point domain.point_mem))
  cr2 := by
    intro source target covered step argument argumentCovered
    exact codomain.cr2 (covered argument argumentCovered) (.congAppFun step)
  cr3 := by
    intro function functionNeutral functionReducts argument argumentCovered
    have argumentAccessible := domain.cr1 argumentCovered
    induction argumentAccessible with
    | intro argument smallerArgument ih =>
        apply codomain.cr3 (neutral_app functionNeutral)
        intro target step
        rcases neutral_app_step functionNeutral step with
          ⟨function', functionStep, rfl⟩ | ⟨argument', argumentStep, rfl⟩
        · exact functionReducts function' functionStep
            argument argumentCovered
        · exact ih argument' argumentStep (domain.cr2 argumentCovered argumentStep)

theorem arrow_pred (domain : Pointed n) (codomain : ReductionCandidate n)
    (function : PureTm n) :
    (arrow domain codomain).pred function ↔
      ∀ argument, domain.pred argument →
        codomain.pred (.app function argument) :=
  Iff.rfl

/-- Nondependent product candidates are observed through both projections. -/
def product (left right : ReductionCandidate n) : ReductionCandidate n where
  pred := fun pair => left.pred (.fst pair) ∧ right.pred (.snd pair)
  cr1 := fun covered =>
    reductionAccessible_fst_argument (left.cr1 covered.1)
  cr2 := fun covered step =>
    ⟨left.cr2 covered.1 (.congFst step),
      right.cr2 covered.2 (.congSnd step)⟩
  cr3 := by
    intro pair pairNeutral pairReducts
    constructor
    · apply left.cr3 (neutral_fst pairNeutral)
      intro target step
      obtain ⟨pair', pairStep, rfl⟩ := neutral_fst_step pairNeutral step
      exact (pairReducts pair' pairStep).1
    · apply right.cr3 (neutral_snd pairNeutral)
      intro target step
      obtain ⟨pair', pairStep, rfl⟩ := neutral_snd_step pairNeutral step
      exact (pairReducts pair' pairStep).2

theorem product_pred (left right : ReductionCandidate n) (pair : PureTm n) :
    (product left right).pred pair ↔
      left.pred (.fst pair) ∧ right.pred (.snd pair) :=
  Iff.rfl

end ReductionCandidate

/-! ## Positive and negative canaries -/

theorem identityU0_in_normalizing_candidate :
    (ReductionCandidate.normalizing 0).pred regularIdentityU0 :=
  regularIdentityU0_reductionAccessible

theorem weakened_u0_in_normalizing_family :
    (ReductionCandidate.RenamingStable.normalizing.fibre 1).pred
      (rename wk (.u0 : PureTm 0)) :=
  ReductionCandidate.RenamingStable.normalizing.rename_mem wk
    reductionAccessible_u0

theorem omega_not_in_normalizing_candidate :
    ¬ (ReductionCandidate.normalizing 0).pred regularOmega := by
  intro accessible
  exact accessibleNormalizationSpecification.omega_not_in_domain
    ⟨accessible, regularOmega_constantFree⟩

/-- Applying the identity lambda to any accessible argument remains
accessible.  This is the positive beta-expansion lemma used by the first
function-candidate canary. -/
theorem reductionAccessible_identity_application {n : Nat}
    {argument : PureTm n}
    (argumentAccessible : ReductionAccessible argument) :
    ReductionAccessible
      (.app (.lam (.var (0 : Fin (n + 1)))) argument) := by
  induction argumentAccessible with
  | intro argument smaller ih =>
      constructor
      intro target step
      cases step with
      | betaPi => exact Acc.intro argument smaller
      | congAppFun functionStep =>
          cases functionStep with
          | congLam bodyStep => cases bodyStep
      | congAppArg argumentStep => exact ih _ argumentStep

def normalizingPointedU0 : ReductionCandidate.Pointed 0 :=
  ReductionCandidate.normalizingPointed .u0 reductionAccessible_u0

def normalizingArrow0 : ReductionCandidate 0 :=
  ReductionCandidate.arrow normalizingPointedU0
    (ReductionCandidate.normalizing 0)

theorem identity_in_normalizingArrow0 :
    normalizingArrow0.pred (.lam (.var 0)) := by
  intro argument argumentAccessible
  exact reductionAccessible_identity_application argumentAccessible

theorem regularDelta_reductionAccessible :
    ReductionAccessible regularDelta := by
  constructor
  intro target step
  exact False.elim (regularDelta_normal target step)

theorem delta_not_in_normalizingArrow0 :
    ¬ normalizingArrow0.pred regularDelta := by
  intro deltaReducible
  exact omega_not_in_normalizing_candidate
    (deltaReducible regularDelta regularDelta_reductionAccessible)

/-- Strong normalization of the two parts does not imply strong normalization
of application.  This is the exact obstruction forcing a type-indexed logical
relation rather than a structural induction over terms. -/
theorem application_not_closed_by_component_accessibility :
    ReductionAccessible regularDelta ∧
      ReductionAccessible regularDelta ∧
      ¬ ReductionAccessible (.app regularDelta regularDelta) := by
  refine ⟨regularDelta_reductionAccessible,
    regularDelta_reductionAccessible, ?_⟩
  intro omegaAccessible
  exact omega_not_in_normalizing_candidate omegaAccessible

/-- The open self-application is accessible before its variable is
instantiated.  It is the smallest canary separating harmless open syntax from
arbitrary closing substitutions. -/
theorem regularOmegaBody_reductionAccessible :
    ReductionAccessible regularOmegaBody := by
  constructor
  intro target step
  cases step with
  | congAppFun variableStep => cases variableStep
  | congAppArg variableStep => cases variableStep

/-- The substitution sending the sole open variable to the looping delta
term. -/
def regularDeltaSubstitution : Sub 1 0 :=
  fun _ => regularDelta

/-- A deliberately weak environment condition: every substituted image lies
in one fixed candidate.  The following canary proves that this is insufficient
for dependent typing; the source context must assign candidates by type. -/
def PointwiseSatisfies (candidate : ReductionCandidate m)
    (substitution : Sub n m) : Prop :=
  ∀ i, candidate.pred (substitution i)

theorem regularDeltaSubstitution_pointwise_normalizing :
    PointwiseSatisfies (ReductionCandidate.normalizing 0)
      regularDeltaSubstitution := by
  intro i
  exact regularDelta_reductionAccessible

theorem substitute_regularOmegaBody_with_delta :
    subst regularDeltaSubstitution regularOmegaBody = regularOmega := by
  rfl

/-- Strong normalization is not preserved by arbitrary substitution.  A
fundamental lemma must therefore quantify over substitutions whose images
satisfy the candidates assigned by the source context; plain syntactic
substitutions are too broad. -/
theorem accessibility_not_preserved_by_arbitrary_substitution :
    ReductionAccessible regularOmegaBody ∧
      ¬ ReductionAccessible
        (subst regularDeltaSubstitution regularOmegaBody) := by
  refine ⟨regularOmegaBody_reductionAccessible, ?_⟩
  rw [substitute_regularOmegaBody_with_delta]
  exact application_not_closed_by_component_accessibility.2.2

/-- Even a substitution whose every image is strongly normalizing can turn an
accessible open term into a loop.  Candidate-respecting environments must be
indexed by the variables' types, not merely pointwise by normalization. -/
theorem pointwise_normalizing_environment_is_insufficient :
    ∃ substitution : Sub 1 0,
      PointwiseSatisfies (ReductionCandidate.normalizing 0) substitution ∧
        ReductionAccessible regularOmegaBody ∧
        ¬ ReductionAccessible (subst substitution regularOmegaBody) := by
  exact ⟨regularDeltaSubstitution,
    regularDeltaSubstitution_pointwise_normalizing,
    accessibility_not_preserved_by_arbitrary_substitution⟩

/-! ## Axiom audit -/

#print axioms reductionAccessible_pi
#print axioms red_rename_reflect
#print axioms reductionAccessible_rename
#print axioms reductionAccessible_sigma
#print axioms reductionAccessible_id
#print axioms reductionAccessible_lam
#print axioms reductionAccessible_pair
#print axioms reductionAccessible_refl
#print axioms reductionAccessible_app_left
#print axioms reductionAccessible_app_right
#print axioms ReductionCandidate.inter_pred
#print axioms ReductionCandidate.arrow_pred
#print axioms ReductionCandidate.product_pred
#print axioms identityU0_in_normalizing_candidate
#print axioms weakened_u0_in_normalizing_family
#print axioms omega_not_in_normalizing_candidate
#print axioms reductionAccessible_identity_application
#print axioms identity_in_normalizingArrow0
#print axioms regularDelta_reductionAccessible
#print axioms delta_not_in_normalizingArrow0
#print axioms application_not_closed_by_component_accessibility
#print axioms regularOmegaBody_reductionAccessible
#print axioms substitute_regularOmegaBody_with_delta
#print axioms accessibility_not_preserved_by_arbitrary_substitution
#print axioms pointwise_normalizing_environment_is_insufficient

end Mettapedia.Languages.MeTTa.PureKernel.PresentationBoundary
