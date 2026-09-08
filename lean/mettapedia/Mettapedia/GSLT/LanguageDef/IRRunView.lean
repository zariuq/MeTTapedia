import Mettapedia.GSLT.LanguageDef.IRPass

/-!
# The run view modulo equations of a representation

A machine-shaped representation takes many small steps to do what a coarser
language does in one.  Its run view is the GSLT whose terms and equations are
those of the representation and whose single step is one complete run: from
the entry state of a term to a result state, as designated by a run protocol.
As with every authored rewrite relation, the raw run relation is closed as
`E ; Run ; E`.  A run hidden behind a change of representative is therefore
visible, and the result may be read through any equivalent representative.

The run view is a derived semantic object, not another representation; it is
the honest target of a pass from a coarse language into a machine, because a
pass covers steps by steps and the machine's step is a run.  A term map whose
source steps are target runs, and under which every run from an image term
comes from a source step up to target equations, is a semantic cover into the
run view.  The equation-free case is a theorem about this one construction,
not a second run semantics.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IRRunView

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.IRPass
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A run protocol: where a term's run starts, and which states are results
of which terms. -/
structure RunProtocol where
  entry : Pattern → Pattern
  exit : Pattern → Option Pattern

/-- Finitely many steps of a representation. -/
def reaches (ir : IRLanguage) : Pattern → Pattern → Prop :=
  Relation.ReflTransGen ir.semantics.Step

/-- One complete raw run before closing the endpoints under equations. -/
def RawRun (ir : IRLanguage) (protocol : RunProtocol)
    (source target : Pattern) : Prop :=
  ∃ final, reaches ir (protocol.entry source) final ∧
    protocol.exit final = some target

/-- The least endpoint saturation needed to make complete runs act on the
representation's equation classes. -/
def RunModuloEquations (ir : IRLanguage) (protocol : RunProtocol)
    (source target : Pattern) : Prop :=
  ∃ redex contractum,
    ir.semantics.Equiv source redex ∧
      RawRun ir protocol redex contractum ∧
      ir.semantics.Equiv contractum target

/-- One modulo-equations complete run as one step. -/
def runView (ir : IRLanguage) (protocol : RunProtocol) : GSLT where
  Term := Pattern
  equations := ir.semantics.equations
  rewrites := RunModuloEquations ir protocol
  rewrites_resp_left := by
    intro source source' target equivalent step
    rcases step with ⟨redex, contractum, sourceRedex, run, contractumTarget⟩
    refine ⟨target, ⟨redex, contractum, ?_, run, contractumTarget⟩, ?_⟩
    · exact ir.semantics.equations.iseqv.trans
        (ir.semantics.equations.iseqv.symm equivalent) sourceRedex
    · exact ir.semantics.equations.iseqv.refl target
  rewrites_resp_right := by
    intro source target target' step equivalent
    rcases step with ⟨redex, contractum, sourceRedex, run, contractumTarget⟩
    exact ⟨redex, contractum, sourceRedex, run,
      ir.semantics.equations.iseqv.trans contractumTarget equivalent⟩

theorem runView_step_iff (ir : IRLanguage) (protocol : RunProtocol) (source target : Pattern) :
    (runView ir protocol).Step source target ↔
      RunModuloEquations ir protocol source target :=
  Iff.rfl

theorem runView_equiv_iff (ir : IRLanguage) (protocol : RunProtocol) (left right : Pattern) :
    (runView ir protocol).Equiv left right ↔ ir.semantics.Equiv left right :=
  Iff.rfl

/-- Every raw run is visible in the run view modulo equations. -/
theorem step_of_rawRun (ir : IRLanguage) (protocol : RunProtocol)
    {source target : Pattern} (run : RawRun ir protocol source target) :
    (runView ir protocol).Step source target :=
  ⟨source, target,
    ir.semantics.equations.iseqv.refl source, run,
    ir.semantics.equations.iseqv.refl target⟩

/-- If the represented language has only literal equality, the sole run view
reduces exactly to the raw complete-run relation. -/
theorem runView_step_iff_raw_of_equiv_eq
    (ir : IRLanguage) (protocol : RunProtocol)
    (equivEq : ∀ {left right : Pattern},
      ir.semantics.Equiv left right → left = right)
    (source target : Pattern) :
    (runView ir protocol).Step source target ↔
      RawRun ir protocol source target := by
  rw [runView_step_iff]
  constructor
  · rintro ⟨redex, contractum, sourceRedex, run, contractumTarget⟩
    have sourceEq : source = redex := equivEq sourceRedex
    have targetEq : contractum = target := equivEq contractumTarget
    subst redex
    subst target
    exact run
  · exact step_of_rawRun ir protocol

/-- A term map whose source steps are runs of the target and whose runs from
image terms come from source steps is a semantic cover into the run view. -/
def coverOfRuns (source target : IRLanguage) (protocol : RunProtocol)
    (mapTerm : Pattern → Pattern)
    (mapEquiv : ∀ {left right : Pattern}, source.semantics.Equiv left right →
      target.semantics.Equiv (mapTerm left) (mapTerm right))
    (forward : ∀ {sourceTerm sourceTarget : Pattern},
      source.semantics.Step sourceTerm sourceTarget →
        (runView target protocol).Step (mapTerm sourceTerm) (mapTerm sourceTarget))
    (backward : ∀ {sourceTerm : Pattern} {targetTerm : Pattern},
      (runView target protocol).Step (mapTerm sourceTerm) targetTerm →
        ∃ sourceTarget, source.semantics.Step sourceTerm sourceTarget ∧
          target.semantics.Equiv (mapTerm sourceTarget) targetTerm) :
    SemanticCoveredTranslation source.semantics (runView target protocol) where
  mapTerm := mapTerm
  mapEquiv := mapEquiv
  mapStep := forward
  liftStep := by
    intro sourceTerm targetTerm step
    exact backward step

@[simp]
theorem coverOfRuns_mapTerm (source target : IRLanguage) (protocol : RunProtocol)
    (mapTerm : Pattern → Pattern) (mapEquiv) (forward) (backward) :
    (coverOfRuns source target protocol mapTerm mapEquiv forward backward).mapTerm = mapTerm :=
  rfl

#print axioms step_of_rawRun
#print axioms runView_step_iff_raw_of_equiv_eq
#print axioms coverOfRuns

/-! ## Runs under the first-reduct strategy

A realization executes one invocation deterministically: it follows the
first authored reduct until no reduct remains or its step budget is spent.
The strategy run view records exactly those runs.  Every strategy run is a
run, so the identity is a forward pass from the strategy view into the run
view; the two coincide when reduction is deterministic and the exits are
normal forms, which is a separate obligation of each representation. -/

open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- The endpoint of the first-reduct strategy from the entry of a source
term, with one contextual bound and one step bound. -/
def strategyEndpoint (ir : IRLanguage) (protocol : RunProtocol)
    (contextFuel stepFuel : Nat) (source : Pattern) : Pattern :=
  normalizeFirstUsing ir.relations ir.definition.language contextFuel stepFuel
    (protocol.entry source)

/-- The first-reduct normalization of a term is reachable from it. -/
theorem reaches_normalizeFirst (ir : IRLanguage) (contextFuel : Nat) :
    ∀ (stepFuel : Nat) (term : Pattern),
      reaches ir term
        (normalizeFirstUsing ir.relations ir.definition.language contextFuel stepFuel term)
  | 0, _ => Relation.ReflTransGen.refl
  | stepFuel + 1, term => by
      unfold normalizeFirstUsing normalizeFirstAt
      cases reducts : rewriteAt (engineBasePremises ir.relations) ir.definition.language
          contextFuel term with
      | nil => exact Relation.ReflTransGen.refl
      | cons next _ =>
          have member : next ∈ rewriteAt (engineBasePremises ir.relations)
              ir.definition.language contextFuel term := by
            rw [reducts]
            exact List.mem_cons_self
          have reduces : langReducesUsing ir.relations ir.definition.language term next :=
            (langReducesUsing_iff_execUsing ir.relations ir.definition.language term next).2
              ⟨contextFuel, member⟩
          have step : ir.semantics.Step term next :=
            EquationSemantics.step_to_stepModuloEquations reduces
          exact Relation.ReflTransGen.head step
            (reaches_normalizeFirst ir contextFuel stepFuel next)

/-- One complete run under the strategy: the exit observation of the
strategy endpoint. -/
def StrategyRun (ir : IRLanguage) (protocol : RunProtocol) (contextFuel stepFuel : Nat)
    (source target : Pattern) : Prop :=
  protocol.exit (strategyEndpoint ir protocol contextFuel stepFuel source) = some target

/-- Every strategy run is a raw run. -/
theorem rawRun_of_strategyRun (ir : IRLanguage) (protocol : RunProtocol)
    {contextFuel stepFuel : Nat} {source target : Pattern}
    (run : StrategyRun ir protocol contextFuel stepFuel source target) :
    RawRun ir protocol source target :=
  ⟨_, reaches_normalizeFirst ir contextFuel stepFuel (protocol.entry source), run⟩

/-- Strategy runs closed under the representation's equations. -/
def StrategyRunModuloEquations (ir : IRLanguage) (protocol : RunProtocol)
    (contextFuel stepFuel : Nat) (source target : Pattern) : Prop :=
  ∃ redex contractum,
    ir.semantics.Equiv source redex ∧
      StrategyRun ir protocol contextFuel stepFuel redex contractum ∧
      ir.semantics.Equiv contractum target

/-- One modulo-equations strategy run as one step. -/
def strategyRunView (ir : IRLanguage) (protocol : RunProtocol)
    (contextFuel stepFuel : Nat) : GSLT where
  Term := Pattern
  equations := ir.semantics.equations
  rewrites := StrategyRunModuloEquations ir protocol contextFuel stepFuel
  rewrites_resp_left := by
    intro source source' target equivalent step
    rcases step with ⟨redex, contractum, sourceRedex, run, contractumTarget⟩
    refine ⟨target, ⟨redex, contractum, ?_, run, contractumTarget⟩, ?_⟩
    · exact ir.semantics.equations.iseqv.trans
        (ir.semantics.equations.iseqv.symm equivalent) sourceRedex
    · exact ir.semantics.equations.iseqv.refl target
  rewrites_resp_right := by
    intro source target target' step equivalent
    rcases step with ⟨redex, contractum, sourceRedex, run, contractumTarget⟩
    exact ⟨redex, contractum, sourceRedex, run,
      ir.semantics.equations.iseqv.trans contractumTarget equivalent⟩

theorem strategyRunView_step_iff (ir : IRLanguage) (protocol : RunProtocol)
    (contextFuel stepFuel : Nat) (source target : Pattern) :
    (strategyRunView ir protocol contextFuel stepFuel).Step source target ↔
      StrategyRunModuloEquations ir protocol contextFuel stepFuel source target :=
  Iff.rfl

theorem strategyRunView_equiv_iff (ir : IRLanguage) (protocol : RunProtocol)
    (contextFuel stepFuel : Nat) (left right : Pattern) :
    (strategyRunView ir protocol contextFuel stepFuel).Equiv left right ↔
      ir.semantics.Equiv left right :=
  Iff.rfl

/-- If the represented language has only literal equality, the strategy run
view reduces exactly to the strategy runs. -/
theorem strategyRunView_step_iff_strategy_of_equiv_eq
    (ir : IRLanguage) (protocol : RunProtocol) (contextFuel stepFuel : Nat)
    (equivEq : ∀ {left right : Pattern}, ir.semantics.Equiv left right → left = right)
    (source target : Pattern) :
    (strategyRunView ir protocol contextFuel stepFuel).Step source target ↔
      StrategyRun ir protocol contextFuel stepFuel source target := by
  rw [strategyRunView_step_iff]
  constructor
  · rintro ⟨redex, contractum, sourceRedex, run, contractumTarget⟩
    have sourceEq : source = redex := equivEq sourceRedex
    have targetEq : contractum = target := equivEq contractumTarget
    subst redex
    subst target
    exact run
  · intro run
    exact ⟨source, target, ir.semantics.equations.iseqv.refl source, run,
      ir.semantics.equations.iseqv.refl target⟩

/-- Strategy runs are runs: the identity is a forward pass from the strategy
view into the run view. -/
def strategyRunView_toRunView (ir : IRLanguage) (protocol : RunProtocol)
    (contextFuel stepFuel : Nat) :
    OperationalTranslation (strategyRunView ir protocol contextFuel stepFuel)
      (runView ir protocol) where
  mapTerm := id
  mapEquiv equivalent := equivalent
  mapStep := by
    rintro _ _ ⟨redex, contractum, sourceRedex, run, contractumTarget⟩
    exact ⟨redex, contractum, sourceRedex, rawRun_of_strategyRun ir protocol run,
      contractumTarget⟩


end Mettapedia.GSLT.LanguageDef.IRRunView
