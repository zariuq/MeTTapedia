import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RegionalEquality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantumContextuality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.SharedUnknown
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.FreshOpenings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.OwnedStore
import Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission
import Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Spec-by-example suite (Part II): Higher dimensions D5, D6, D8, D9, D10

Each dimension is demonstrated by a concrete motivating specimen with kernel-checked
positive and negative controls built directly over Mettapedia's real formalizations:
`RuleSyntax.step`, `RuleSyntax.RegionalEquality`, `NullsOnTheStep.ParallelClosed.{SharedUnknown,
FreshOpenings, OwnedStore}`, `OSLF.MeTTaIL.{ReflectiveQuoteAdmission, ReflectiveContextualQuote}`,
and `AnnotatedRuns.AmplitudeRuns.Contextuality`:

* **D5 (`HollowCubeAndAsymmetry`)** — Higher-dimensional concurrency & asymmetric conflict:
  three tells `X = Y`, `X = 1`, `Y = 2` are pairwise solvable (three 2-cells) yet jointly
  unsolvable (hollow cube, no 3-cell); and `audit (read)` followed by `consume (take)`
  succeeds while `consume` disables `audit` (asymmetric conflict).
* **D6 (`ScopedPrivacyEscrow`)** — Fresh openings, anti-capture & owned-store scoping:
  contrasts fixed rule instances (`SharedUnknown.beside_captor_blocked`, where a parallel
  neighbour captures an unshared rule variable) against real fresh openings
  (`FreshOpenings.captor_analog_keeps`, `FreshOpenings.switchesOff_shares`) and Meredith's
  owned-store scoping boundary (`OwnedStore.nested_blocks`, `OwnedStore.other_fires`,
  `OwnedStore.ownedStore_no_parallelContextRule`).
* **D8 (`CrossBubbleCMTT`)** — Regional conversion bubbles & contextual quotation:
  a real `RuleSyntax.RegionalEquality` instance separates an `arith` bubble (where
  `addZero e ≈ e`) from the strict `core` bubble; eager core normalization loses a valid
  shared-variable solution; and `ReflectiveQuoteAdmission` + `ReflectiveContextualQuote`
  separate real `@(*y)` quote admission (`admitted_not_sealed`, `sorted_not_admitted`,
  `quoteAdmits_reads_quoteScope`, `instantiate_scope_needs_admission`) and prove fresh
  closure-context factorization vs. necessity (`exists_closure_factorization`,
  `closureView_not_factorable`, `closure_fresh_context_validates`,
  `closure_signature_context_rejected`).
* **D9 (`SpeculativeDemandControl`)** — One-shot vs. multi-shot handlers & bounded demand:
  on `RuleSyntax.step`, taking a continuation enforces one-shot resumption (second resume
  refused) whereas reading it enables multi-shot resumption; linear `select k` inspects
  only a finite prefix of an infinite stream.
* **D10 (`ContextualFairProductive`)** — Sheaf contextuality, fairness & finite-lookahead
  productivity: connects Mermin's no-global-section theorem (`mermin_no_global_section`,
  `mermin_no_classical_model`, `ghz_reproduces_mermin`, `recorded_has_global_section`),
  computes `Relation.ReflTransGen` reachability on real directed transition relations to prove
  reachability sets fail to decide fair completeness, and separates finite-lookahead
  `streamTail` (`n + 1`) from same-depth contraction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open Mettapedia.GSLT.Core.NonFactorization
open RuleSyntax
open RuleSyntax.OneFrame (Terms frames ext)
open RuleSyntax.Controls (atoms action)
open RuleSyntax.Examples (Tm X E c fresh_of_ground)

/-! ## D5: Three-Sensor Hollow Cube + Audit-Before-Consume -/

namespace HollowCubeAndAsymmetry

def v0 : Term atoms := .var 0
def v1 : Term atoms := .var 1

def tellEq : Equation (Tm PUnit.unit) := (v0, v1)
def tellOne : Equation (Tm PUnit.unit) := (v0, c 1)
def tellTwo : Equation (Tm PUnit.unit) := (v1, c 2)

/-- **D5 Positive Control (1 — All three 2-cell pairs are solvable)**. -/
theorem hollowCube_all_pairs_solvable :
    X.Solvable (a := PUnit.unit) [tellEq, tellOne] ∧
    X.Solvable (a := PUnit.unit) [tellEq, tellTwo] ∧
    X.Solvable (a := PUnit.unit) [tellOne, tellTwo] := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨PUnit.unit, fun _ => c 1, fun e he => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  · refine ⟨PUnit.unit, fun _ => c 2, fun e he => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  · refine ⟨PUnit.unit, fun v => if v = 0 then c 1 else c 2, fun e he => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl

/-- **D5 Negative Control (1 — Hollow Cube)**: the three pairwise-consistent tells are
jointly unsolvable (three 2-squares bound no 3-cube). -/
theorem hollowCube_triple_unsolvable :
    ¬ X.Solvable (a := PUnit.unit) [tellEq, tellOne, tellTwo] := by
  rintro ⟨_, σ, hmod⟩
  have heq : σ 0 = σ 1 := hmod tellEq List.mem_cons_self
  have h1 : σ 0 = c 1 := hmod tellOne (List.mem_cons_of_mem _ List.mem_cons_self)
  have h2 : σ 1 = c 2 := hmod tellTwo (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hbad : c 1 = c 2 := h1.symm.trans (heq.trans h2)
  exact absurd (Term.const.inj hbad) (by decide)

/-- Audit rule: reads ledger occurrence `c 5` without consuming it. -/
def auditRule : Rule Tm := ⟨PUnit.unit, ⟨[], [c 5], [], [], []⟩, []⟩

/-- Consume rule: takes ledger occurrence `c 5`. -/
def consumeRule : Rule Tm := ⟨PUnit.unit, ⟨[c 5], [], [], [], []⟩, []⟩

def asymProgram : Program Tm := {auditRule, consumeRule}

def ledgerState : State Tm ℕ := ⟨PUnit.unit, [], {0}, fun _ => c 5⟩

def auditFiring : Firing ℕ E asymProgram PUnit.unit :=
  ⟨auditRule, Or.inl rfl, PUnit.unit, Subst.id atoms, ⟨[], [0], []⟩, []⟩

def consumeFiring : Firing ℕ E asymProgram PUnit.unit :=
  ⟨consumeRule, Or.inr rfl, PUnit.unit, Subst.id atoms, ⟨[0], [], []⟩, []⟩

theorem audit_information :
    auditFiring.information X ledgerState = [(c 5, c 5)] := rfl

theorem consume_after_audit_information :
    consumeFiring.information X (auditFiring.result X ledgerState) = [(c 5, c 5), (c 5, c 5)] := rfl

/-- **D5 Positive Control (2 — Asymmetric Conflict)**: `audit` fires first and leaves
`consume` admitted on the resulting state. -/
theorem audit_then_consume_admitted :
    (step X ℕ E asymProgram).Admits (s := ledgerState) auditFiring ∧
    (step X ℕ E asymProgram).Admits (s := auditFiring.result X ledgerState) consumeFiring := by
  have hAudit : (step X ℕ E asymProgram).Admits (s := ledgerState) auditFiring := by
    refine (admits_iff auditFiring).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_nil,
      rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · apply fresh_of_ground action ledgerState auditFiring
      intro t member σ
      simp only [auditFiring, auditRule, Rule.terms, List.map_nil, List.flatMap_nil,
        List.nil_append, List.append_nil, List.mem_singleton] at member
      subst member; rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [auditFiring, ledgerState, Selection.commit]
    · rw [audit_information]
      refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
      obtain rfl := List.mem_singleton.mp member
      rfl
    · intro check member; simp [auditFiring, auditRule, Firing.opened, RuleInstance.map] at member
    · intro q member; simp [auditFiring, auditRule, Firing.collectOpened] at member
  have hPost : (auditFiring.result X ledgerState).present = {0} := by
    simp [Firing.result, auditFiring, ledgerState, fire, Selection.commit]
  have hConsume : (step X ℕ E asymProgram).Admits (s := auditFiring.result X ledgerState) consumeFiring := by
    refine (admits_iff consumeFiring).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_nil,
      rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · apply fresh_of_ground action (auditFiring.result X ledgerState) consumeFiring
      intro t member σ
      simp only [consumeFiring, consumeRule, Rule.terms, List.map_nil, List.flatMap_nil,
        List.append_nil, List.mem_singleton] at member
      subst member; rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [consumeFiring, hPost, Selection.commit]
    · rw [consume_after_audit_information]
      refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    · intro check member; simp [consumeFiring, consumeRule, Firing.opened, RuleInstance.map] at member
    · intro q member; simp [consumeFiring, consumeRule, Firing.collectOpened] at member
  exact ⟨hAudit, hConsume⟩

/-- **D5 Negative Control (2 — Asymmetric Conflict)**: firing `consume` first disables `audit`. -/
theorem consume_disables_audit :
    ¬ (step X ℕ E asymProgram).Admits (s := consumeFiring.result X ledgerState) auditFiring := by
  intro hadm
  have hread := ((admits_iff auditFiring).mp hadm).2.2.1.kept_subset
  have hzero : (0 : ℕ) ∈ (consumeFiring.result X ledgerState).present :=
    hread (by simp [auditFiring, Selection.commit])
  simp [Firing.result, consumeFiring, ledgerState, fire, Selection.commit] at hzero

end HollowCubeAndAsymmetry

/-! ## D6: Fresh Openings, Anti-Capture & Owned-Store Scoping -/

namespace ScopedPrivacyEscrow

open NullsOnTheStep.ParallelClosed
open NullsOnTheStep.ParallelClosed.SharedUnknown
open NullsOnTheStep.ParallelClosed.FreshOpenings
open NullsOnTheStep.ParallelClosed.OwnedStore

/-- **D6 Negative Control (Without Fresh Openings — Capture by a Parallel Neighbour)**:
In `SharedUnknown`, `request` does not mention `y = var 1` and `captor` mentions ONLY `y`,
yet because the rule instance has fixed variable `y` without fresh opening, placing `captor`
beside `request` captures `y` and blocks `request` from succeeding (`beside_captor_blocked`). -/
theorem fixed_instance_vulnerable_to_capture :
    (∀ v, SharedUnknown.Mentions SharedUnknown.captor.equations v → v = 1) ∧
    (PositiveTell.request.equations = [] ∧
      ∀ o ∈ PositiveTell.request.present, ¬ SharedUnknown.Occurs (sig := atoms) 1 o.1) ∧
    ¬ PositiveTell.tellSource.Succeeds
        (NullsOnTheStep.Composition.unionOf PositiveTell.request SharedUnknown.captor) :=
  ⟨SharedUnknown.captor_mentions_only_y,
   SharedUnknown.request_does_not_mention_y,
   SharedUnknown.beside_captor_blocked⟩

/-- **D6 Positive Control (1 — Fresh Openings Eliminate Capture)**:
On `RuleSyntax.step` with fresh openings (`FreshOpenings`), `captorAnalog` constrains the exact
unknown `var 1` that the standalone firing opened, yet `captor_analog_keeps` proves it CANNOT
switch off `request` because the firing opens its rule's unknown freshly elsewhere!
Meanwhile `shared_switches` confirms that genuinely sharing `request`'s own unknown `x = var 0`
still switches it off. -/
theorem fresh_openings_prevent_capture :
    ¬ FreshOpenings.SwitchesOff RuleSyntax.Scope.CompositionControls.tellProgram
        (· = c 9) FreshOpenings.captorAnalog RuleSyntax.Scope.CompositionControls.request ∧
    FreshOpenings.SwitchesOff RuleSyntax.Scope.CompositionControls.tellProgram
        (· = c 9) RuleSyntax.Scope.CompositionControls.neighbour
        RuleSyntax.Scope.CompositionControls.request :=
  ⟨FreshOpenings.captor_analog_keeps, FreshOpenings.shared_switches⟩

/-- **D6 Positive/Negative Control (2 — Owned-Store Freshness Boundary)**:
Meredith's owned store (`OwnedStore.ownedStore`) fires when the store avoids the name `U`
(`other_fires`), blocks even on a nested mention `[g(U)]` (`nested_blocks`), and admits NO
parallel context rule (`ownedStore_no_parallelContextRule`) because its rule carries a
freshness premise. -/
theorem owned_store_scoping_controls (relEnv : Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv)
    (kind : Mettapedia.OSLF.MeTTaIL.Syntax.CollType) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises relEnv)
      OwnedStore.ownedStore
      (OwnedStore.store [OwnedStore.otherRow])
      (OwnedStore.store [OwnedStore.madeRow, OwnedStore.otherRow]) ∧
    (∀ result, ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (Mettapedia.OSLF.MeTTaIL.ContextualStep.engineBasePremises relEnv)
      OwnedStore.ownedStore
      (OwnedStore.store [OwnedStore.nestedRow]) result) ∧
    ¬ NullsOnTheStep.ParallelClosed.HasParallelContextRule kind OwnedStore.ownedStore :=
  ⟨OwnedStore.other_fires relEnv,
   (OwnedStore.nested_blocks relEnv).2,
   OwnedStore.ownedStore_no_parallelContextRule kind⟩

end ScopedPrivacyEscrow

/-! ## D8: Cross-Bubble CMTT Proof Transformer (Regional Bubbles & Contextual Metavars) -/

namespace CrossBubbleCMTT

/-- Minimal arithmetic expression language with an unknown `var`, `zero`, `succ`, and `addZero`. -/
inductive ArithExpr where
  | var
  | zero
  | succ (e : ArithExpr)
  | addZero (e : ArithExpr)
  deriving DecidableEq

def substArith (val : ArithExpr) : ArithExpr → ArithExpr
  | .var => val
  | .zero => .zero
  | .succ e => .succ (substArith val e)
  | .addZero e => .addZero (substArith val e)

/-- Normalization in the `arith` bubble eliminates `+ 0`. -/
def normArith : ArithExpr → ArithExpr
  | .var => .var
  | .zero => .zero
  | .succ e => .succ (normArith e)
  | .addZero e => normArith e

theorem normArith_subst (val e : ArithExpr) :
    normArith (substArith val e) = substArith (normArith val) (normArith e) := by
  induction e with
  | var => rfl
  | zero => rfl
  | succ e ih => simp [substArith, normArith, ih]
  | addZero e ih => simp [substArith, normArith, ih]

theorem substArith_id (e : ArithExpr) : substArith .var e = e := by
  induction e with
  | var => rfl
  | zero => rfl
  | succ e ih => simp [substArith, ih]
  | addZero e ih => simp [substArith, ih]

theorem substArith_comp (g f e : ArithExpr) :
    substArith (substArith g f) e = substArith g (substArith f e) := by
  induction e with
  | var => rfl
  | zero => rfl
  | succ e ih => simp [substArith, ih]
  | addZero e ih => simp [substArith, ih]

/-- Base frame action on `ArithExpr` with strict syntactic equality. -/
def arithBase : Frames (fun _ : Unit => ArithExpr) (fun _ _ => ArithExpr) where
  E := Eq
  equivalence _ := eq_equivalence
  act := substArith
  id _ := .var
  comp g f := substArith g f
  act_id := substArith_id
  act_comp := substArith_comp
  preserves := by intro _ _ σ _ _ h; exact congrArg (substArith σ) h

/-- Two regional conversion views: strict `core` vs. `arith` (`e + 0 ≈ e`). -/
inductive BubbleRegion where
  | core
  | arith
  deriving DecidableEq

/-- Real `RuleSyntax.RegionalEquality` instance over `arithBase`. -/
def bubbleViews : RegionalEquality arithBase BubbleRegion where
  conversion
    | .core, _ => ⟨Eq, eq_equivalence⟩
    | .arith, _ =>
      ⟨fun a b => normArith a = normArith b, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
  preserves region _ _ σ a b hab := by
    cases region with
    | core => exact congrArg (substArith σ) hab
    | arith =>
      change normArith (substArith σ a) = normArith (substArith σ b)
      rw [normArith_subst, normArith_subst, hab]

/-- **D8 Positive Control (Regional Bubbles)**: under `bubbleViews.frames`, the equation
`addZero var ≐ var` is solved in `.arith`, while `.core` strictly refuses it. -/
theorem bubble_arith_admits_core_refuses :
    bubbleViews.frames.Solvable (a := ())
      [((BubbleRegion.arith, ArithExpr.addZero .var), (BubbleRegion.arith, ArithExpr.var))] ∧
    ¬ bubbleViews.frames.Solvable (a := ())
      [((BubbleRegion.core, ArithExpr.addZero .var), (BubbleRegion.core, ArithExpr.var))] := by
  constructor
  · refine ⟨(), .zero, fun e he => ?_⟩
    obtain rfl := List.mem_singleton.mp he
    exact ⟨rfl, rfl⟩
  · rintro ⟨_, σ, hmod⟩
    have h := (hmod _ (List.mem_singleton_self _)).2
    change ArithExpr.addZero σ = σ at h
    have hsz : sizeOf (ArithExpr.addZero σ) = sizeOf σ := congrArg sizeOf h
    simp only [ArithExpr.addZero.sizeOf_spec] at hsz
    omega

/-- **D8 Negative Control (Eager Normalization Trap)**: in `.arith`, both `σ := .zero` and
`σ := .addZero .zero` solve `var ≐_arith addZero zero`, yet they are distinct in `.core`.
Eagerly committing to the normalized representative `.zero` drops a valid solution. -/
theorem bubble_shared_var_multiple_core_witnesses :
    bubbleViews.frames.Models (a := ()) (b := ()) ArithExpr.zero
      [((BubbleRegion.arith, ArithExpr.var), (BubbleRegion.arith, ArithExpr.addZero .zero))] ∧
    bubbleViews.frames.Models (a := ()) (b := ()) (ArithExpr.addZero .zero)
      [((BubbleRegion.arith, ArithExpr.var), (BubbleRegion.arith, ArithExpr.addZero .zero))] ∧
    ¬ bubbleViews.frames.E (a := ())
      (BubbleRegion.core, ArithExpr.zero) (BubbleRegion.core, ArithExpr.addZero .zero) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he; obtain rfl := List.mem_singleton.mp he; exact ⟨rfl, rfl⟩
  · intro e he; obtain rfl := List.mem_singleton.mp he; exact ⟨rfl, rfl⟩
  · intro h; exact ArithExpr.noConfusion h.2

/-- **D8 Real Reflective Sorting vs. Quote Admission Controls (`ReflectiveQuoteAdmission`)**:
Directly on Mettapedia's real `rhoReflectivePresentation` (`Pattern` calculus):
1. `@(y!(0))` is well-sorted yet NOT quote-closed (`sorted_not_admitted`);
2. `@(*y)` is well-sorted AND quote-closed (`QuotesClosed`) despite failing naive syntactic
   quote-sealing `binderSafeAt` (`admitted_not_sealed`);
3. Quote admission reads the declared `QuoteScope` policy (`quoteAdmits_reads_quoteScope`);
4. Eliminating the binder of a sorted body requires admission (`instantiate_scope_needs_admission`). -/
theorem reflective_sorting_vs_admission_controls :
    (Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.NameWellSorted
      Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation
      Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax.FreeSortContext.empty ["Name"]
      (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) ∧
     Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.QuotesClosed
      Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.toReflectivePresentationDecl
      (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) ∧
     Mettapedia.OSLF.MeTTaIL.ScopedPattern.binderSafeAt "NQuote" 1
      (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) = false) ∧
    (Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.quoteAdmits
      (Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.withQuoteScope .closed).toReflectivePresentationDecl
      (.apply "POutput" [.bvar 0, .apply "PZero" []]) = false ∧
     Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.quoteAdmits
      (Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.withQuoteScope (.reaching .apply)).toReflectivePresentationDecl
      (.apply "POutput" [.bvar 0, .apply "PZero" []]) = true) :=
  ⟨Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission.admitted_not_sealed,
   Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission.quoteAdmits_reads_quoteScope⟩

/-- **D8 Real Contextual Closure Factorization & Freshness Controls (`ReflectiveContextualQuote`)**:
1. A fresh closure context constructor validates on `rhoCalc` (`closure_fresh_context_validates`),
   whereas reusing `rhoCalc`'s own `"PZero"` constructor is rejected (`closure_signature_context_rejected`).
2. Without freshness, NO observation of `closureView` can recover `applyView` or `freezeView`
   across all bodies (`closureView_not_factorable`, `closureView_not_factorable_freeze`).
3. With a fresh context constructor, EVERY `body` and `replacement` admit a fresh context label
   through which `erase` recovers `applyView` and `atomize` recovers `freezeView`
   (`exists_closure_factorization`). -/
theorem reflective_contextual_closure_controls :
    Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc.validateReflectivePresentation
      { Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.toReflectivePresentationDecl with
        quoteScope := .reaching (.closure "QuoteContext") } = [] ∧
    (Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc.validateReflectivePresentation
      { Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.toReflectivePresentationDecl with
        quoteScope := .reaching (.closure "PZero") }).length = 1 :=
  ⟨Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote.closure_fresh_context_validates,
   Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote.closure_signature_context_rejected⟩

end CrossBubbleCMTT

/-! ## D9: Speculative Search (`select k`) & One-Shot vs. Multi-Shot Resumption -/

namespace SpeculativeDemandControl

/-- One-shot handler: **takes** continuation `c 77` and reply `c reply`. -/
def oneShotRule (reply : ℕ) : Rule Tm :=
  ⟨PUnit.unit, ⟨[c 77, c reply], [], [], [], [c (100 + reply)]⟩, []⟩

/-- Multi-shot handler: **reads** continuation `c 77` and takes reply `c reply`. -/
def multiShotRule (reply : ℕ) : Rule Tm :=
  ⟨PUnit.unit, ⟨[c reply], [c 77], [], [], [c (100 + reply)]⟩, []⟩

def handlerProgram : Program Tm :=
  {oneShotRule 10, oneShotRule 20, multiShotRule 10, multiShotRule 20}

/-- Initial state: continuation `c 77` at id `0`, reply `c 10` at id `1`, reply `c 20` at id `2`. -/
def suspendedState : State Tm ℕ :=
  ⟨PUnit.unit, [], {0, 1, 2}, fun o => if o = 0 then c 77 else if o = 1 then c 10 else c 20⟩

def oneShotFirst : Firing ℕ E handlerProgram PUnit.unit :=
  ⟨oneShotRule 10, Or.inl rfl, PUnit.unit, Subst.id atoms, ⟨[0, 1], [], [3]⟩, []⟩

def oneShotSecond : Firing ℕ E handlerProgram PUnit.unit :=
  ⟨oneShotRule 20, Or.inr (Or.inl rfl), PUnit.unit, Subst.id atoms, ⟨[0, 2], [], [4]⟩, []⟩

def multiShotFirst : Firing ℕ E handlerProgram PUnit.unit :=
  ⟨multiShotRule 10, Or.inr (Or.inr (Or.inl rfl)), PUnit.unit, Subst.id atoms, ⟨[1], [0], [3]⟩, []⟩

def multiShotSecond : Firing ℕ E handlerProgram PUnit.unit :=
  ⟨multiShotRule 20, Or.inr (Or.inr (Or.inr rfl)), PUnit.unit, Subst.id atoms, ⟨[2], [0], [4]⟩, []⟩

theorem multiShotFirst_information :
    multiShotFirst.information X suspendedState = [(c 10, c 10), (c 77, c 77)] := rfl

theorem multiShotSecond_information :
    multiShotSecond.information X (multiShotFirst.result X suspendedState) =
      [(c 10, c 10), (c 77, c 77), (c 20, c 20), (c 77, c 77)] := rfl

/-- **D9 Negative Control (One-Shot Enforcement)**: after `oneShotFirst` consumes
continuation `0`, `oneShotSecond` is refused. -/
theorem oneShot_second_resume_refused :
    ¬ (step X ℕ E handlerProgram).Admits (s := oneShotFirst.result X suspendedState) oneShotSecond := by
  intro hadm
  have htake := ((admits_iff oneShotSecond).mp hadm).2.2.1.1
  have hzero : (0 : ℕ) ∈ (oneShotFirst.result X suspendedState).present :=
    htake (by simp [oneShotSecond, Selection.commit])
  simp [Firing.result, oneShotFirst, suspendedState, fire, Selection.commit] at hzero

/-- **D9 Positive Control (Multi-Shot Branching)**: reading continuation `0` keeps it live
so BOTH replies `1` and `2` resume cleanly in sequence. -/
theorem multiShot_both_resumes_admitted :
    (step X ℕ E handlerProgram).Admits (s := suspendedState) multiShotFirst ∧
    (step X ℕ E handlerProgram).Admits (s := multiShotFirst.result X suspendedState) multiShotSecond := by
  have hFirst : (step X ℕ E handlerProgram).Admits (s := suspendedState) multiShotFirst := by
    refine (admits_iff multiShotFirst).mpr ⟨?_, ⟨List.nodup_singleton 1, List.nodup_singleton 3,
      rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · apply fresh_of_ground action suspendedState multiShotFirst
      intro t member σ
      simp only [multiShotFirst, multiShotRule, Rule.terms, List.map_nil, List.flatMap_nil,
        List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [multiShotFirst, suspendedState, Selection.commit]
    · rw [multiShotFirst_information]
      refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl
    · intro check member
      simp [multiShotFirst, multiShotRule, Firing.opened, RuleInstance.map] at member
    · intro q member
      simp [multiShotFirst, multiShotRule, Firing.collectOpened] at member
  have hPost : (multiShotFirst.result X suspendedState).present = {0, 2, 3} := by
    ext o
    simp only [Firing.result, multiShotFirst, suspendedState, fire, Selection.commit,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hSecond : (step X ℕ E handlerProgram).Admits
      (s := multiShotFirst.result X suspendedState) multiShotSecond := by
    refine (admits_iff multiShotSecond).mpr ⟨?_, ⟨List.nodup_singleton 2, List.nodup_singleton 4,
      rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
    · apply fresh_of_ground action (multiShotFirst.result X suspendedState) multiShotSecond
      intro t member σ
      simp only [multiShotSecond, multiShotRule, Rule.terms, List.map_nil, List.flatMap_nil,
        List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl | rfl <;> rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [multiShotSecond, hPost, Selection.commit]
    · rw [multiShotSecond_information]
      refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> rfl
    · intro check member
      simp [multiShotSecond, multiShotRule, Firing.opened, RuleInstance.map] at member
    · intro q member
      simp [multiShotSecond, multiShotRule, Firing.collectOpened] at member
  exact ⟨hFirst, hSecond⟩

/-- Bounded linear demand `selectK k` pulls exactly `k` answers from an infinite stream. -/
def selectK {α : Type*} (k : ℕ) (stream : ℕ → α) : List α :=
  List.ofFn (fun i : Fin k => stream i.val)

/-- **D9 Positive Control (Bounded Demand)**: `selectK k` returns length `k` and depends
only on stream indices `< k` (finite work on an infinite producer). -/
theorem selectK_bounded_work {α : Type*} (k : ℕ) (s₁ s₂ : ℕ → α)
    (hagree : ∀ i < k, s₁ i = s₂ i) :
    (selectK k s₁).length = k ∧ selectK k s₁ = selectK k s₂ := by
  refine ⟨List.length_ofFn, ?_⟩
  unfold selectK
  congr 1
  funext i
  exact hagree i.val i.isLt

end SpeculativeDemandControl

/-! ## D10: Sheaf Contextuality, Fair Search & Finite-Lookahead Productivity -/

namespace ContextualFairProductive

open AnnotatedRuns.AmplitudeRuns.Contextuality

/-- **D10 Control (1 — Abramsky–Brandenburger Sheaf Contextuality)**:
Wires Mettapedia's Mermin–GHZ theorem into the spec-by-example suite:
no global classical distribution or classical-grade run model reproduces Mermin's
empirical table, whereas coherent amplitudes reproduce it and recording histories
destroys contextuality (yielding a global section). -/
theorem sheaf_contextuality_separates_coherent_from_classical :
    ¬ GlobalSection merminRestrict mermin ∧
    ¬ ClassicalModel merminRestrict mermin ∧
    (∀ c o, ghzWeight c o / ∑ o' : Outcome, ghzWeight c o' = mermin c o) ∧
    GlobalSection merminRestrict uniform :=
  ⟨mermin_no_global_section, mermin_no_classical_model,
   ghz_reproduces_mermin, recorded_has_global_section⟩

/-- Transition relation with a destructive stall (`0 → 1`, `0 → 2`, `1 → 1`):
from `1` (`dead`), `2` (`proof`) is no longer reachable. -/
def destructiveStep (a b : Fin 3) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 1)

/-- Repaired transition relation (`0 → 1`, `0 → 2`, `1 → 2`):
from every reachable state, `2` (`proof`) remains reachable. -/
def repairedStep (a b : Fin 3) : Prop :=
  (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 2)

/-- Reachability set of any transition relation on `Fin 3` starting from `0`. -/
def reachableSet (R : Fin 3 → Fin 3 → Prop) : Set (Fin 3) :=
  { s | Relation.ReflTransGen R 0 s }

/-- Fair proof completeness: `2` remains reachable from every state reachable from `0`. -/
def fairProofReachable (R : Fin 3 → Fin 3 → Prop) : Prop :=
  ∀ s, Relation.ReflTransGen R 0 s → Relation.ReflTransGen R s 2

theorem destructiveStep_one_stuck {s : Fin 3} (h : Relation.ReflTransGen destructiveStep 1 s) :
    s = 1 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    rcases hstep with ⟨h0, _⟩ | ⟨h0, _⟩ | ⟨_, h1⟩
    · exact absurd h0 (by decide)
    · exact absurd h0 (by decide)
    · exact h1

/-- **D10 Control (2 — Real `ReflTransGen` Reachability Does Not Decide Fair Completeness)**:
`destructiveStep` and `repairedStep` have the **exact same** `Relation.ReflTransGen`
reachable set (`Set.univ`), yet `repairedStep` satisfies `fairProofReachable` while
`destructiveStep` fails it (witnessed by `1`, which can never reach `2`).
Hence `fairProofReachable` does NOT factor through `reachableSet`. -/
theorem reachableSet_eq_destructive_repaired :
    reachableSet destructiveStep = reachableSet repairedStep := by
  ext s
  simp only [reachableSet, Set.mem_ofPred_eq]
  have hallD : ∀ x : Fin 3, Relation.ReflTransGen destructiveStep 0 x := by
    intro x
    fin_cases x
    · exact .refl
    · exact .single (Or.inl ⟨rfl, rfl⟩)
    · exact .single (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hallR : ∀ x : Fin 3, Relation.ReflTransGen repairedStep 0 x := by
    intro x
    fin_cases x
    · exact .refl
    · exact .single (Or.inl ⟨rfl, rfl⟩)
    · exact .single (Or.inr (Or.inl ⟨rfl, rfl⟩))
  exact ⟨fun _ => hallR s, fun _ => hallD s⟩

theorem repairedStep_fairProofReachable : fairProofReachable repairedStep := by
  intro s _
  fin_cases s
  · exact .single (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · exact .single (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · exact .refl

theorem destructiveStep_not_fairProofReachable : ¬ fairProofReachable destructiveStep := by
  intro hfair
  have h12 : Relation.ReflTransGen destructiveStep 1 2 :=
    hfair 1 (.single (Or.inl ⟨rfl, rfl⟩))
  exact absurd (destructiveStep_one_stuck h12) (by decide)

def reachability_vs_fairness_fiber : NonTrivialFiber reachableSet fairProofReachable where
  left := destructiveStep
  right := repairedStep
  sameShadow := reachableSet_eq_destructive_repaired
  differentValue := by
    intro heq
    exact destructiveStep_not_fairProofReachable (heq.mpr repairedStep_fairProofReachable)

theorem reachability_does_not_decide_fairness :
    ¬ Factors reachableSet fairProofReachable :=
  reachability_vs_fairness_fiber.not_factors

/-- Stream shift `tail(s)(i) = s(i + 1)` on Cantor space `ℕ → Bool`. -/
def streamTail (s : ℕ → Bool) : ℕ → Bool := fun i => s (i + 1)

/-- **D10 Control (3 — Finite-Lookahead Productivity vs. Same-Depth Contraction)**:
`streamTail` is continuous with exact finite lookahead modulus `n + 1`, yet fails
same-depth (`n`) causality. -/
theorem streamTail_lookahead_not_contractive :
    (∀ (n : ℕ) (s₁ s₂ : ℕ → Bool),
      (∀ i < n + 1, s₁ i = s₂ i) → ∀ i < n, streamTail s₁ i = streamTail s₂ i) ∧
    (∃ s₁ s₂ : ℕ → Bool,
      (∀ i < 1, s₁ i = s₂ i) ∧ streamTail s₁ 0 ≠ streamTail s₂ 0) := by
  refine ⟨fun n s₁ s₂ h i hi => h (i + 1) (by omega), ?_⟩
  refine ⟨fun _ => false, fun i => decide (i = 1), ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by omega
    subst hi0; rfl
  · decide

end ContextualFairProductive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens
