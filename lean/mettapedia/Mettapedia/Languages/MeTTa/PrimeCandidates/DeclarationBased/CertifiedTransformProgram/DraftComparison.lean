import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Preservation

/-!
# The draft's identity elimination and the linearized one

The draft fires `id:eliminate A x P d y (refl z)` only when the point `x`, the
endpoint `y` and the witness `z` are one term.  The linearized program fires it
at every reflexivity path.  On typed terms the two computations reach the same
results:

* A typed term without a step of the draft has no step of the linearized
  program either.  At a typed elimination the reflexivity proof makes the
  witness convertible to the point and to the endpoint, and convertible terms
  without steps are equal.
* So a draft run of a typed term that stops has reached the term's normal form
  in the linearized program, and all such runs stop at the same term.
* Between typed terms whose draft runs stop, conversion in the linearized
  program is conversion in the draft.

The comparison is stated for every host and every program that differs from
it only in when identity elimination fires.  For terms whose draft runs do not
stop it says nothing: preservation of the draft's own judgments there still
needs its own proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.DraftComparison

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence Presentation.TelescopeAbstraction
open Presentation.ConstructorSystem (Normal)
open Presentation.AlgebraicSchema (SchemaTable)
open CertifiedTransformProgram.Package CertifiedTransformProgram.Confluence
open CertifiedTransformProgram.Preservation

theorem jApp_eq {n : Nat} (carrier point motive method endpoint path : Tower.Tm n) :
    jApp carrier point motive method endpoint path =
      .app (.app (.app (.app (.app (.app (.const jName) carrier) point) motive) method)
        endpoint) path :=
  rfl

/-- In a typed elimination at reflexivity the witness converts to the point and
to the endpoint. -/
theorem elimination_components (host : Host) {n : Nat} {Γ : Tower.Ctx n}
    (formed : ContextFormation host.rules Γ)
    {carrier point motive method endpoint witness displayed : Tower.Tm n}
    (observed : Typing host.rules Γ
      (jApp carrier point motive method endpoint (.refl witness)) displayed) :
    Conv host.rules.headEq witness point host.rules.computation ∧
      Conv host.rules.headEq witness endpoint host.rules.computation := by
  let σ : Sub Tower.Head 6 n :=
    Execution.patternValues ![carrier, point, motive, method, endpoint, witness]
  have instance_typed : Typing host.rules Γ
      (subst σ (jApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.refl (.var 0)))) displayed :=
    observed
  have spine := host.declaredSpine lookup_j jType_formed Γ
  rw [jType_close] at spine
  obtain ⟨morphism, _, _, _⟩ := DeclarationSpine.recoverTelescope host.universes
    host.piBoundary formed jDeclarationTelescope (.app (.app (.var 3) (.var 1)) (.var 0))
    (consSub (.refl (σ 0)) (fun index => σ index.succ)) spine instance_typed
  have pathTyped : Typing host.rules Γ (.refl (σ 0)) (.id (σ 5) (σ 4) (σ 1)) := morphism 0
  exact host.refl_endpoints pathTyped

/-! ## Drafts of a host -/

/-- A program that differs from a host only in identity elimination: every
other root step of the host is one of its own, and it eliminates a reflexivity
path at least when the witness is the point and the endpoint. -/
structure Draft (host : Host) where
  rules : Rules Tower.Head
  toHost : rules.Morphism host.rules (fun head => head)
  headEq : ∀ {left right : Tower.Head}, host.rules.headEq left right → rules.headEq left right
  cover : ∀ {n : Nat} {source target : Tower.Tm n}, host.rules.computation.step source target →
    rules.computation.step source target ∨
      ∃ carrier point motive method endpoint witness,
        source = jApp carrier point motive method endpoint (.refl witness)
  diagonal : ∀ {n : Nat} (carrier point motive method : Tower.Tm n),
    rules.computation.step (jApp carrier point motive method point (.refl point)) method

namespace Draft

variable {host : Host} (draft : Draft host)

theorem step_host {n : Nat} {source target : Tower.Tm n}
    (step : Step draft.rules.headEq source target draft.rules.computation) :
    Step host.rules.headEq source target host.rules.computation := by
  simpa only [Tm.mapHead_id] using
    StepCore.mapHead (fun head => head) draft.toHost.headEq draft.toHost.computation step

theorem runs_host {n : Nat} {source target : Tower.Tm n}
    (runs : StepStar draft.rules source target) : StepStar host.rules source target := by
  induction runs with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (draft.step_host step)

theorem normal_of_host {n : Nat} {term : Tower.Tm n} (normal : Normal host.rules term) :
    Normal draft.rules term :=
  fun step => normal (draft.step_host step)

/-- A root step of the host at a term that is no elimination at reflexivity is a
step of the draft. -/
theorem root_apart {n : Nat} {source target : Tower.Tm n}
    (step : host.rules.computation.step source target)
    (apart : ∀ carrier point motive method endpoint witness,
      source ≠ jApp carrier point motive method endpoint (.refl witness)) :
    draft.rules.computation.step source target := by
  rcases draft.cover step with drafted | ⟨carrier, point, motive, method, endpoint, witness, shape⟩
  · exact drafted
  · exact (apart carrier point motive method endpoint witness shape).elim

/-- Only applications are eliminations. -/
theorem apart_of_ne_app {n : Nat} {source : Tower.Tm n}
    (notApp : ∀ function argument, source ≠ .app function argument) :
    ∀ carrier point motive method endpoint witness,
      source ≠ jApp carrier point motive method endpoint (.refl witness) := by
  intro carrier point motive method endpoint witness shape
  rw [jApp_eq] at shape
  exact notApp _ _ shape

/-- A typed term with no step of the draft has no step of the host.  Where the
host eliminates `id:eliminate A x P d y (refl z)`, the typing makes `z`, `x`
and `y` convertible; they have no steps, so they are one term and the draft
eliminates too. -/
theorem normal_of_draftNormal
    (unique : ∀ {n : Nat} {first second : Tower.Tm n}, Normal host.rules first →
      Normal host.rules second → Conv host.rules.headEq first second host.rules.computation →
        first = second)
    {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n} (typing : Typing host.rules Γ term type) :
    ContextFormation host.rules Γ → Normal draft.rules term → Normal host.rules term := by
  induction typing with
  | headType headTyped =>
      intro _ normal target step
      cases step with
      | head equality => exact normal (.head (draft.headEq equality))
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
  | var index =>
      intro _ normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
  | const known formed universeWitness _ =>
      intro _ normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
  | piForm formedA universeA formedB universeB join ihA ihB =>
      intro context normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
      | congPiDom nested => exact ihA context (fun inner => normal (.congPiDom inner)) nested
      | congPiCod nested =>
          exact ihB (.snoc context formedA universeA) (fun inner => normal (.congPiCod inner)) nested
  | sigmaForm formedA universeA formedB universeB join ihA ihB =>
      intro context normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
      | congSigmaDom nested => exact ihA context (fun inner => normal (.congSigmaDom inner)) nested
      | congSigmaCod nested =>
          exact ihB (.snoc context formedA universeA) (fun inner => normal (.congSigmaCod inner))
            nested
  | lamIntro formed universeWitness bodyTyped _ ihBody =>
      intro context normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
      | congLam nested =>
          obtain ⟨u, v, w, formedA, universeA, formedB, universeB, join⟩ := formed.piFormation
          exact ihBody (.snoc context formedA universeA) (fun inner => normal (.congLam inner)) nested
  | @appElim n Γ function argument A B functionTyped argumentTyped ihFunction ihArgument =>
      intro context normal target step
      have functionNormal : Normal host.rules function :=
        ihFunction context (fun inner => normal (.congAppFun inner))
      have argumentNormal : Normal host.rules argument :=
        ihArgument context (fun inner => normal (.congAppArg inner))
      cases step with
      | betaPi body _ => exact normal (.betaPi body argument)
      | congAppFun nested => exact functionNormal nested
      | congAppArg nested => exact argumentNormal nested
      | root equation =>
          rcases draft.cover equation with drafted |
            ⟨carrier, point, motive, method, endpoint, witness, shape⟩
          · exact normal (.root drafted)
          · have observed : Typing host.rules Γ
                (jApp carrier point motive method endpoint (.refl witness)) (inst0 argument B) :=
              shape ▸ Typing.appElim functionTyped argumentTyped
            obtain ⟨toPoint, toEndpoint⟩ := elimination_components host context observed
            rw [jApp_eq] at shape
            injection shape with _ functionShape argumentShape
            subst functionShape argumentShape
            have witnessNormal : Normal host.rules witness :=
              fun inner => argumentNormal (.congRefl inner)
            have pointNormal : Normal host.rules point :=
              fun inner => functionNormal (.congAppFun (.congAppFun (.congAppFun (.congAppArg inner))))
            have endpointNormal : Normal host.rules endpoint :=
              fun inner => functionNormal (.congAppArg inner)
            have atPoint := unique witnessNormal pointNormal toPoint
            have atEndpoint := unique witnessNormal endpointNormal toEndpoint
            subst atPoint atEndpoint
            exact normal (.root (draft.diagonal carrier witness motive method))
  | @pairIntro n Γ first second A B u formed universeWitness firstTyped secondTyped
      _ ihFirst ihSecond =>
      intro context normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
      | congPairFst nested => exact ihFirst context (fun inner => normal (.congPairFst inner)) nested
      | congPairSnd nested =>
          exact ihSecond context (fun inner => normal (.congPairSnd inner)) nested
  | fstElim pairTyped ihPair =>
      intro context normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
      | betaSigmaFst => exact normal (.betaSigmaFst _ _)
      | congFst nested => exact ihPair context (fun inner => normal (.congFst inner)) nested
  | sndElim pairTyped ihPair =>
      intro context normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
      | betaSigmaSnd => exact normal (.betaSigmaSnd _ _)
      | congSnd nested => exact ihPair context (fun inner => normal (.congSnd inner)) nested
  | idForm formed universeWitness leftTyped rightTyped ihA ihLeft ihRight =>
      intro context normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
      | congIdTy nested => exact ihA context (fun inner => normal (.congIdTy inner)) nested
      | congIdLeft nested => exact ihLeft context (fun inner => normal (.congIdLeft inner)) nested
      | congIdRight nested => exact ihRight context (fun inner => normal (.congIdRight inner)) nested
  | reflIntro termTyped ihTerm =>
      intro context normal target step
      cases step with
      | root equation =>
          exact normal (.root (draft.root_apart equation
            (apart_of_ne_app (fun _ _ shape => by cases shape))))
      | congRefl nested => exact ihTerm context (fun inner => normal (.congRefl inner)) nested
  | cumul typed order ih =>
      intro context normal
      exact ih context normal
  | conv typed formed universeWitness conversion ih _ =>
      intro context normal
      exact ih context normal

variable (unique : ∀ {n : Nat} {first second : Tower.Tm n}, Normal host.rules first →
    Normal host.rules second → Conv host.rules.headEq first second host.rules.computation →
      first = second)
  (preserve : ∀ {n : Nat} {Γ : Tower.Ctx n} {source target type : Tower.Tm n},
    Judgment host.rules Γ source type → StepStar host.rules source target →
      Judgment host.rules Γ target type)

include unique preserve

/-- A draft run of a typed term that stops has reached a normal form of the host. -/
theorem normal_of_stopped {n : Nat} {Γ : Tower.Ctx n} {term type result : Tower.Tm n}
    (judgment : Judgment host.rules Γ term type) (runs : StepStar draft.rules term result)
    (stopped : Normal draft.rules result) : Normal host.rules result :=
  let final := preserve judgment (draft.runs_host runs)
  draft.normal_of_draftNormal unique final.typing final.context stopped

/-- Draft runs of a typed term that stop, stop at the same term. -/
theorem stopped_unique {n : Nat} {Γ : Tower.Ctx n} {term type first second : Tower.Tm n}
    (judgment : Judgment host.rules Γ term type)
    (firstRuns : StepStar draft.rules term first) (firstStopped : Normal draft.rules first)
    (secondRuns : StepStar draft.rules term second) (secondStopped : Normal draft.rules second) :
    first = second :=
  unique (draft.normal_of_stopped unique preserve judgment firstRuns firstStopped)
    (draft.normal_of_stopped unique preserve judgment secondRuns secondStopped)
    (.trans _ _ _ (.symm _ _ (stepStar_implies_conv (draft.runs_host firstRuns)))
      (stepStar_implies_conv (draft.runs_host secondRuns)))

/-- Between typed terms whose draft runs stop, conversion of the host is
conversion of the draft. -/
theorem conversion_reflects {n : Nat} {Γ : Tower.Ctx n}
    {left right leftType rightType leftResult rightResult : Tower.Tm n}
    (leftJudgment : Judgment host.rules Γ left leftType)
    (rightJudgment : Judgment host.rules Γ right rightType)
    (conversion : Conv host.rules.headEq left right host.rules.computation)
    (leftRuns : StepStar draft.rules left leftResult) (leftStopped : Normal draft.rules leftResult)
    (rightRuns : StepStar draft.rules right rightResult)
    (rightStopped : Normal draft.rules rightResult) :
    Conv draft.rules.headEq left right draft.rules.computation := by
  have same : leftResult = rightResult :=
    unique (draft.normal_of_stopped unique preserve leftJudgment leftRuns leftStopped)
      (draft.normal_of_stopped unique preserve rightJudgment rightRuns rightStopped)
      (.trans _ _ _ (.trans _ _ _ (.symm _ _ (stepStar_implies_conv (draft.runs_host leftRuns)))
        conversion) (stepStar_implies_conv (draft.runs_host rightRuns)))
  subst same
  exact .trans _ _ _ (stepStar_implies_conv leftRuns) (.symm _ _ (stepStar_implies_conv rightRuns))

end Draft

/-! ## The draft's program -/

/-- The draft's program is a draft of the linearized program. -/
noncomputable def packageDraft : Draft linearHost where
  rules := packageRules
  toHost := packageToLinear
  headEq := fun equality => equality
  cover := by
    intro n source target step
    change linearRules.computation.step source target at step
    cases step with
    | inherited targetStep => exact .inl (.inherited targetStep)
    | delta unfolding => rw [linear_valueOf] at unfolding; cases unfolding
    | declared declared =>
        cases declared with
        | instantiate listed substitution =>
            simp only [SchemaTable.family, linearEquations, List.mem_cons, List.not_mem_nil,
              or_false] at listed
            rcases listed with same | same | same | same | same | same | same | same | same |
              same | same | same | same | same | same
            · cases same
              exact .inr ⟨_, _, _, _, _, _, rfl⟩
            all_goals
              cases same
              exact .inl (.declared (SchemaTable.step_of_mem packageEquations
                (by simp [packageEquations]) substitution))
  diagonal := fun carrier point motive method =>
    RootStep.declared (SchemaTable.step_of_mem packageEquations listed_jIota
      (Execution.patternValues ![carrier, point, motive, method]))

theorem linear_unique {n : Nat} {first second : Tower.Tm n} (firstNormal : Normal linearRules first)
    (secondNormal : Normal linearRules second)
    (conversion : Conv linearRules.headEq first second linearRules.computation) :
    first = second :=
  linearConstructors.eq_of_normal firstNormal secondNormal conversion

/-- A typed term of the linearized program with no step of the draft has no
step of the linearized program. -/
theorem normal_of_draftNormal {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (judgment : Judgment linearRules Γ term type) (normal : Normal R term) :
    Normal linearRules term :=
  packageDraft.normal_of_draftNormal linear_unique judgment.typing judgment.context normal

/-- Runs of the draft's evaluator from a typed term that stop, stop at the same
term, the term's normal form in the linearized program. -/
theorem stopped_unique {n : Nat} {Γ : Tower.Ctx n} {term type first second : Tower.Tm n}
    (judgment : Judgment R Γ term type)
    (firstRuns : Execution.Runs term first) (firstStopped : Normal R first)
    (secondRuns : Execution.Runs term second) (secondStopped : Normal R second) :
    first = second :=
  packageDraft.stopped_unique linear_unique steps_preserve (judgment_linear judgment)
    firstRuns firstStopped secondRuns secondStopped

/-- Between typed terms whose runs stop, conversion of the linearized program is
conversion of the draft's program. -/
theorem conversion_reflects {n : Nat} {Γ : Tower.Ctx n}
    {left right leftType rightType leftResult rightResult : Tower.Tm n}
    (leftJudgment : Judgment R Γ left leftType) (rightJudgment : Judgment R Γ right rightType)
    (conversion : Conv linearRules.headEq left right linearRules.computation)
    (leftRuns : Execution.Runs left leftResult) (leftStopped : Normal R leftResult)
    (rightRuns : Execution.Runs right rightResult) (rightStopped : Normal R rightResult) :
    Conv R.headEq left right R.computation :=
  packageDraft.conversion_reflects linear_unique steps_preserve (judgment_linear leftJudgment)
    (judgment_linear rightJudgment) conversion leftRuns leftStopped rightRuns rightStopped

#print axioms elimination_components
#print axioms Draft.normal_of_draftNormal
#print axioms Draft.stopped_unique
#print axioms Draft.conversion_reflects
#print axioms packageDraft
#print axioms normal_of_draftNormal
#print axioms stopped_unique
#print axioms conversion_reflects

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.DraftComparison
