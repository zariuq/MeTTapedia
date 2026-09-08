import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveRegularity
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypingGeneration

/-!
# Formation and conversion are distinct admission obligations

The positive specimen checks a universe-polymorphic dependent identity
function in the formation-sensitive candidate over the real cumulative
syntax. Its two beta-conversion steps return the supplied argument. These
are steps of the proof-computation presentation. They do not select a runtime
evaluation strategy for Prime's planned CBPV foundation.

The negative specimen retains those formation and substitution laws but
licenses an extra equation identifying an opaque ground type with its own
function space. Both equation endpoints are formed. The resulting admitted
self-application loops, so formation alone does not qualify conversion or
prove normalization. This computation package is a counterexample, not an
extension installed into Prime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
namespace FormationSensitive.Examples

variable {n : Nat}

def polymorphicIdentity : Tower.Tm n := .lam (.lam (.var 0))

def polymorphicIdentityType (level : LevelExpr) : Tower.Tm n :=
  .pi (sortTm level) (.pi (.var 0) (.var 1))

def identityLevel (level : LevelExpr) : LevelExpr :=
  .max (.succ level) (.max level level)

theorem polymorphicIdentityType_formed (Γ : Tower.Ctx n) (level : LevelExpr) :
    Typing Tower.rules Γ (polymorphicIdentityType level)
      (sortTm (identityLevel level)) := by
  apply Typing.piForm (.headType (Tower.HeadTyping.sort level))
    (Tower.IsUniverse.sort _)
  · apply Typing.piForm (Typing.var 0) (Tower.IsUniverse.sort level)
    · exact Typing.var 1
    · exact .sort level
    · exact .sorts level level
  · exact .sort _
  · exact .sorts _ _

/-- Type-level dependency is used in the actual admitted term, not merely
described by a semantic family outside the syntax. -/
theorem polymorphicIdentity_typed (Γ : Tower.Ctx n) (level : LevelExpr) :
    Typing Tower.rules Γ polymorphicIdentity (polymorphicIdentityType level) := by
  apply Typing.lamIntro (polymorphicIdentityType_formed Γ level) (.sort _)
  apply Typing.lamIntro
  · exact .piForm (Typing.var 0) (.sort level) (Typing.var 1) (.sort level)
      (.sorts level level)
  · exact .sort _
  · exact .var 0

theorem polymorphicIdentity_specializes {Γ : Tower.Ctx n}
    {A argument : Tower.Tm n} {level : LevelExpr}
    (formed : Typing Tower.rules Γ A (sortTm level))
    (typed : Typing Tower.rules Γ argument A) :
    Typing Tower.rules Γ (.app (.app polymorphicIdentity A) argument) A := by
  have first := Typing.appElim (polymorphicIdentity_typed Γ level) formed
  have functionTyped : Typing Tower.rules Γ (.app polymorphicIdentity A)
      (.pi A (rename wk A)) := by
    exact first
  have result := Typing.appElim functionTyped typed
  simpa only [inst0_rename_wk] using result

/-- The specialized dependent function reduces by the existing beta rule;
there is no new proof-computation rule for its formation receipts. -/
theorem polymorphicIdentity_two_steps (A argument : Tower.Tm n) :
    ∃ middle,
      Step Tower.HeadEq (.app (.app polymorphicIdentity A) argument) middle ∧
      Step Tower.HeadEq middle argument := by
  refine ⟨.app (.lam (.var 0)) argument, ?_, ?_⟩
  · apply Step.congAppFun
    simpa [polymorphicIdentity, inst0, subst, subst0, liftSub] using
      (Step.betaPi (headEq := Tower.HeadEq) (.lam (.var 0)) A)
  · simpa [inst0, subst, subst0] using
      (Step.betaPi (headEq := Tower.HeadEq) (.var 0) argument)

namespace ConversionCollapse

def ground : Tower.Tm n := .head .legacyGround
def endomorphism : Tower.Tm n := .pi ground ground

/-- This deliberately unsafe equation is stable under both raw structural
operations; those laws alone do not make it a sound type conversion. -/
inductive Collapse : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop where
  | unfold {n : Nat} : Collapse (ground : Tower.Tm n) endomorphism

def root : RootComputation Tower.Head where
  step := Collapse
  rename := by
    intro n m ρ left right step
    cases step
    exact .unfold
  substitute := by
    intro n m σ left right step
    cases step
    exact .unfold

def rules : Rules Tower.Head := { Tower.rules with computation := root }

theorem universeRegularity : UniverseRegularity rules where
  head_target := towerUniverseRegularity.head_target
  join_target := towerUniverseRegularity.join_target
  cumulative_target := towerUniverseRegularity.cumulative_target
  universe_typed := towerUniverseRegularity.universe_typed

theorem ground_formed (Γ : Tower.Ctx n) :
    Typing rules Γ ground (sortTm Tower.zero) := .headType .legacyGround

theorem endomorphism_formed (Γ : Tower.Ctx n) :
    Typing rules Γ endomorphism (sortTm (.max Tower.zero Tower.zero)) :=
  .piForm (ground_formed Γ) (.sort _) (ground_formed (.snoc Γ ground))
    (.sort _) (.sorts _ _)

/-- Even a same-universe endpoint formation check accepts the unsafe law. -/
theorem root_endpoints_formed (Γ : Tower.Ctx n) :
    Typing rules Γ ground (sortTm (.max Tower.zero Tower.zero)) ∧
    Typing rules Γ endomorphism (sortTm (.max Tower.zero Tower.zero)) := by
  refine ⟨.cumul (ground_formed Γ) ?_, endomorphism_formed Γ⟩
  intro valuation
  simp [LevelExpr.eval]

theorem ground_converts_endomorphism :
    Conv rules.headEq (ground : Tower.Tm n) endomorphism rules.computation :=
  .rel _ _ (.root .unfold)

theorem no_pi_conversion_boundary : ¬ PiConversionBoundary rules :=
  noPiConversionBoundaryOfHeadCollapse
    (Relation.EqvGen.symm _ _ (ground_converts_endomorphism (n := 0)))

def delta : Tower.Tm n := .lam (.app (.var 0) (.var 0))
def omega : Tower.Tm n := .app delta delta

theorem delta_typed (Γ : Tower.Ctx n) :
    Typing rules Γ delta endomorphism := by
  apply Typing.lamIntro (endomorphism_formed Γ) (.sort _)
  have variableTyped : Typing rules (.snoc Γ ground) (.var 0) ground := .var 0
  have asFunction : Typing rules (.snoc Γ ground) (.var 0) endomorphism :=
    .conv variableTyped (endomorphism_formed _) (.sort _) ground_converts_endomorphism
  exact Typing.appElim asFunction variableTyped

theorem delta_typed_ground (Γ : Tower.Ctx n) :
    Typing rules Γ delta ground :=
  .conv (delta_typed Γ) (ground_formed Γ) (.sort _)
    (Relation.EqvGen.symm _ _ ground_converts_endomorphism)

/-- All additional formation premises are discharged, but the admitted
conversion still permits a closed looping inhabitant of the ground type. -/
theorem omega_typed_ground : Typing rules .nil (omega : Tower.Tm 0) ground :=
  .appElim (delta_typed .nil) (delta_typed_ground .nil)

/-- Requiring the ambient context to be formed does not remove the unsafe
conversion: the counterexample is already closed. -/
theorem omega_judgment_ground : Judgment rules .nil (omega : Tower.Tm 0) ground :=
  ⟨.nil, omega_typed_ground⟩

theorem omega_self_step :
    Step rules.headEq (omega : Tower.Tm 0) omega rules.computation := by
  simpa [omega, delta, inst0, subst, subst0] using
    (Step.betaPi (headEq := rules.headEq) (root := rules.computation)
      (.app (.var 0) (.var 0)) (delta : Tower.Tm 0))

theorem omega_not_accessible :
    ¬ Acc (fun reduct source : Tower.Tm 0 =>
      Step rules.headEq source reduct rules.computation) omega := by
  have noSelf : ∀ term : Tower.Tm 0,
      Acc (fun reduct source : Tower.Tm 0 =>
        Step rules.headEq source reduct rules.computation) term →
      ¬ Step rules.headEq term term rules.computation := by
    intro term accessible
    induction accessible with
    | intro term _ inductionHypothesis =>
        intro step
        exact inductionHypothesis term step step
  intro accessible
  exact noSelf _ accessible omega_self_step

end ConversionCollapse

#print axioms polymorphicIdentityType_formed
#print axioms polymorphicIdentity_typed
#print axioms polymorphicIdentity_specializes
#print axioms polymorphicIdentity_two_steps
#print axioms ConversionCollapse.universeRegularity
#print axioms ConversionCollapse.root_endpoints_formed
#print axioms ConversionCollapse.no_pi_conversion_boundary
#print axioms ConversionCollapse.omega_typed_ground
#print axioms ConversionCollapse.omega_judgment_ground
#print axioms ConversionCollapse.omega_self_step
#print axioms ConversionCollapse.omega_not_accessible

end FormationSensitive.Examples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
