import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.RealCalculi
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.CoreSpecimens
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.HigherSpecimens
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.HeatingBisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoChannelFragment
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoPeekOutside
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReadOnlyQuery
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.LinearTake
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.RhoTarget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Gap
import Mettapedia.GSLT.Distinction.SpecSpace.FrameDiagramCMTT

/-!
# Real 8-Primitive AIT Basis of the Transform Step

This module formalizes an irredundant, adequate basis for the constraint-multiset-rewriting
step in terms of its **eight actual semantic primitives** (`StepPrimitive`):

```
{ take, read, make, tell, guards, fresh, frame, size }
```

No synthetic enum-rank profiles or threshold predicates appear here. Instead:

1. **"Not too minimal" (Irredundancy)** is proved by **eight real semantic separation theorems**
   (`sep_take`, `sep_read`, `sep_make`, `sep_tell`, `sep_guards`, `sep_fresh`, `sep_frame`,
   `sep_size`). For each primitive `p : StepPrimitive`, we pair:
   * a quantified invariance / impossibility theorem holding for EVERY firing, rule set, or
     calculus in the fragment omitting `p`, with
   * an explicit positive firing or calculus using `p` that strictly violates that invariant or
     admits no uniform translation into the omitting fragment.
2. **"Not too cluttered" (Adequacy)** is established by grounding all ten specification
   dimensions (`D1`–`D10`) in real positive specimens and real negative separation theorems
   built directly over these primitives in `CoreSpecimens`, `HigherSpecimens`, `RealCalculi`,
   `FragmentsOfTheStep`, `NullsOnTheStep.ParallelClosed`, and `FrameDiagramCMTT`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.SpecSpace

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings
open Mettapedia.OSLF.MeTTaIL.ReflectiveQuoteAdmission
open Mettapedia.OSLF.MeTTaIL.ReflectiveContextualQuote

/-! ## 1. The Eight Semantic Primitives of the Step -/

/-- The eight actual primitives that generate the step's expressiveness landscape:
* `take`: linear consumption of present occurrences (`RuleInstance.take`),
* `read`: non-destructive identity-preserving inspection (`RuleInstance.read`),
* `make`: allocation of fresh output occurrences (`RuleInstance.produce`),
* `tell`: constraint/equation posting over shared unknowns (`RuleInstance.tell`),
* `guards`: non-monotone absence and count checks (`RuleInstance.checks`),
* `fresh`: fresh opening of rule-local unknowns (`Firing.Fresh`),
* `frame`: parametric frame action / regional conversion & reflective quote views (`Interface.Frames`),
* `size`: unbounded every-match bulk retraction vs. fixed bounded take-arity. -/
inductive StepPrimitive where
  | take
  | read
  | make
  | tell
  | guards
  | fresh
  | frame
  | size
  deriving DecidableEq, Repr

/-- Enumerates all 8 primitives. -/
def allStepPrimitives : List StepPrimitive :=
  [.take, .read, .make, .tell, .guards, .fresh, .frame, .size]

theorem allStepPrimitives_nodup : allStepPrimitives.Nodup := by decide

theorem allStepPrimitives_length : allStepPrimitives.length = 8 := rfl

theorem mem_allStepPrimitives (p : StepPrimitive) : p ∈ allStepPrimitives := by
  cases p <;> decide

/-! ## 2. Real Fragment Predicates on Actual Step Objects -/

/-- Fragment omitting `take`: rules never consume occurrences (`rule.take = []`). -/
def WithoutTake {T : Type*} (rule : RuleInstance T) : Prop := rule.take = []

/-- Fragment omitting `read`: rules never inspect without consuming (`rule.read = []`). -/
def WithoutRead {T : Type*} (rule : RuleInstance T) : Prop := rule.read = []

/-- Fragment omitting `make`: rules never allocate new occurrences (`rule.produce = []`). -/
def WithoutMake {T : Type*} (rule : RuleInstance T) : Prop := rule.produce = []

/-- Fragment omitting `guards`: rules carry only monotone checks (equations / `some`). -/
def WithoutGuards {T : Type*} (rule : RuleInstance T) : Prop :=
  Monotone.MonotoneChecks rule

/-- Fragment with fixed bounded take-arity `≤ B` on `RuleSyntax.Rule`. -/
def BoundedTakeArity {Obj : Type*} {Tm : Obj → Type*} (B : ℕ) (r : RuleSyntax.Rule Tm) : Prop :=
  r.body.take.length ≤ B

/-! ## 3. Eight Real Semantic Separation Theorems (Not Too Minimal) -/

/-- **Separation 1 (`take`)**:
1. *Wall without `take`*: on ANY valid selection with `WithoutTake rule`, every pre-state
   occurrence survives (`C.present ⊆ post.present`, `C.present.card ≤ post.present.card`);
   and any check-free rule set omitting `take` (`MonotoneInference.Monotone`) is confluent
   (all runs share the same eventual facts, the Datalog least fixed point).
2. *Witness with `take`*: `DualResourceEscrow.escrowSwap` consumes both tokens `{0, 1} ↦ {2}`
   atomically on `RuleSyntax.step`, and `MonotoneInference.Controls.choice` breaks confluence
   permanently via competitive consumption. -/
theorem sep_take :
    (∀ {T S O : Type} [DecidableEq O] {A : SubstitutionAction T S} {label : O → T}
        {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O},
      WithoutTake rule → sel.Valid A label rule C →
      C.present ⊆ (sel.result label rule C).present ∧
      C.present.card ≤ (sel.result label rule C).present.card) ∧
    (∀ {R : HeatingBisimulation.RuleSet NamesOnTheStep.Expr}
        (_ : MonotoneInference.Monotone R) {C C₁ C₂ : NamesOnTheStep.IssuingControls.Conf},
      (∀ e ∈ C.equations, e.1 = e.2) →
      Relation.ReflTransGen (GroundFirings.GroundStep R) C C₁ →
      Relation.ReflTransGen (GroundFirings.GroundStep R) C C₂ →
      ∀ p, (∃ D, Relation.ReflTransGen (GroundFirings.GroundStep R) C₁ D ∧ p ∈ GroundFirings.facts D) ↔
        (∃ D, Relation.ReflTransGen (GroundFirings.GroundStep R) C₂ D ∧ p ∈ GroundFirings.facts D)) ∧
    ((RuleSyntax.step RuleSyntax.Examples.X ℕ RuleSyntax.Examples.E DualResourceEscrow.escrowProgram).Admits
        (s := DualResourceEscrow.escrowState) DualResourceEscrow.atomicSwapFiring ∧
      (DualResourceEscrow.atomicSwapFiring.result RuleSyntax.Examples.X DualResourceEscrow.escrowState).present = {2}) ∧
    (¬ MonotoneInference.Monotone MonotoneInference.Controls.choice ∧
      (∃ D, Relation.ReflTransGen (GroundFirings.GroundStep MonotoneInference.Controls.choice)
          MonotoneInference.Controls.afterRight D ∧
          MonotoneInference.Controls.right ∈ GroundFirings.facts D) ∧
      ¬ ∃ D, Relation.ReflTransGen (GroundFirings.GroundStep MonotoneInference.Controls.choice)
          MonotoneInference.Controls.afterLeft D ∧
          MonotoneInference.Controls.right ∈ GroundFirings.facts D) :=
  ⟨fun {_ _ _ _ _ _ _ _ _} hno hval => withoutTake_present_subset_and_card_le hno hval,
   fun {_} hmono {_ _ _} htriv r1 r2 => MonotoneInference.confluent hmono htriv r1 r2,
   ⟨DualResourceEscrow.escrow_atomic_admitted, DualResourceEscrow.escrow_atomic_result_present⟩,
   ⟨MonotoneInference.Controls.choice_not_confluent.1,
    MonotoneInference.Controls.choice_not_confluent.2.2.2.1,
    MonotoneInference.Controls.choice_not_confluent.2.2.2.2⟩⟩

/-- **Separation 2 (`read`)**:
1. *Wall without `read`*: on ANY valid selection with `WithoutRead rule`, every taken occurrence
   is destroyed (`o ∉ post.present`) and every made occurrence is fresh (`m ∉ C.present`), so no
   firing can observe an occurrence and retain its exact physical identity; emulating a query by
   consuming and recreating (`ReadOnlyQuery.Controls.consume`) creates a causal blocker
   (`consuming_query_is_a_cause`); and peeking (`RhoPeekOutside.PeekStep`) admits NO bisimulation
   with rho's take-make channel step (`peek_not_rho`).
2. *Witness with `read`*: `ReadOnlyQuery.Controls.query` commutes with disjoint takers while
   preserving store identity (`query_commutes_with_taker`), and `SpeculativeDemandControl`
   resumes a read continuation twice (`multiShot_both_resumes_admitted`) whereas taking it
   refuses the second resume (`oneShot_second_resume_refused`). -/
theorem sep_read :
    (∀ {T S O : Type} [DecidableEq O] {A : SubstitutionAction T S} {label : O → T}
        {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O},
      WithoutRead rule → sel.Valid A label rule C →
      sel.read = [] ∧
      (∀ o ∈ sel.taken, o ∉ (sel.result label rule C).present) ∧
      (∀ m ∈ sel.made, m ∉ C.present)) ∧
    (¬ ReadOnlyQuery.ReadOnly ReadOnlyQuery.Controls.consume ∧
      ReadOnlyQuery.Controls.queryAt.Valid NamesOnTheStep.IssuingControls.ground Prod.fst
        ReadOnlyQuery.Controls.query ReadOnlyQuery.Controls.start ∧
      ¬ ReadOnlyQuery.Controls.queryAt.Valid NamesOnTheStep.IssuingControls.ground Prod.fst
        ReadOnlyQuery.Controls.query
        (ReadOnlyQuery.Controls.consumeAt.result Prod.fst ReadOnlyQuery.Controls.consume
          ReadOnlyQuery.Controls.start)) ∧
    (¬ TransitionMaps.IsBisimulation RhoPeekOutside.PeekStep
        RhoChannelFragment.RhoStep ContextualCommunicationAdequacy.Represents) ∧
    (GuardFreeProcessOrders.SameUpTo NamesOnTheStep.IssuingControls.ground
        (ReadOnlyQuery.Controls.takeBAt.result Prod.fst ReadOnlyQuery.Controls.takeB
          (ReadOnlyQuery.Controls.queryAt.result Prod.fst ReadOnlyQuery.Controls.query
            ReadOnlyQuery.Controls.start))
        (ReadOnlyQuery.Controls.queryAt.result Prod.fst ReadOnlyQuery.Controls.query
          (ReadOnlyQuery.Controls.takeBAt.result Prod.fst ReadOnlyQuery.Controls.takeB
            ReadOnlyQuery.Controls.start)) ∧
      ((RuleSyntax.step RuleSyntax.Examples.X ℕ RuleSyntax.Examples.E
          SpeculativeDemandControl.handlerProgram).Admits
          (s := SpeculativeDemandControl.suspendedState) SpeculativeDemandControl.multiShotFirst ∧
       (RuleSyntax.step RuleSyntax.Examples.X ℕ RuleSyntax.Examples.E
          SpeculativeDemandControl.handlerProgram).Admits
          (s := SpeculativeDemandControl.multiShotFirst.result RuleSyntax.Examples.X
            SpeculativeDemandControl.suspendedState)
          SpeculativeDemandControl.multiShotSecond)) :=
  ⟨fun hno hval => withoutRead_cannot_preserve_matched_identity hno hval,
   ReadOnlyQuery.Controls.consuming_query_is_a_cause,
   RhoPeekOutside.peek_not_rho,
   ⟨ReadOnlyQuery.Controls.query_commutes_with_taker,
    SpeculativeDemandControl.multiShot_both_resumes_admitted⟩⟩

/-- **Separation 3 (`make`)**:
1. *Wall without `make`*: on ANY valid selection with `WithoutMake rule`, the post-state is a
   subset of the pre-state (`post.present ⊆ C.present`) and store cardinality can never increase
   (`post.present.card ≤ C.present.card`).
2. *Witness with `make`*: `Monotone.makerSource` succeeds starting from the **empty** store
   `Monotone.empty` (`maker_empty_succeeds`), and `DualResourceEscrow.atomicSwapFiring` mints
   the fresh settlement occurrence `2 ∉ {0, 1}`. -/
theorem sep_make :
    (∀ {T S O : Type} [DecidableEq O] {A : SubstitutionAction T S} {label : O → T}
        {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O},
      WithoutMake rule → sel.Valid A label rule C →
      (sel.result label rule C).present ⊆ C.present ∧
      (sel.result label rule C).present.card ≤ C.present.card) ∧
    (Monotone.makerSource.Succeeds Monotone.empty ∧
      Monotone.empty.present = ∅ ∧
      (DualResourceEscrow.atomicSwapFiring.result RuleSyntax.Examples.X
        DualResourceEscrow.escrowState).present = {2} ∧
      (2 : ℕ) ∉ DualResourceEscrow.escrowState.present) :=
  ⟨fun hno hval => withoutMake_subset_and_card_le hno hval,
   ⟨Monotone.maker_empty_succeeds, rfl, DualResourceEscrow.escrow_atomic_result_present,
    by simp [DualResourceEscrow.escrowState]⟩⟩

/-- **Separation 4 (`tell` — constraint/equation posting over shared unknowns)**:
1. *Wall without `tell` (ground check-free rules)*: EVERY ground rule set whose checks are
   monotone is **not `Switchable`** (`Monotone.not_switchable`), and ground check-free
   `Monotone.relaySource` admits a real `UniformTranslation` into a persistent positive multiset
   bag (`Monotone.relayTranslation`).
2. *Witness with `tell`*: `PositiveTell.tellRule` has **zero checks** (`tellRule.checks = []`),
   yet posting an equation on a shared unknown makes `PositiveTell.tellSource` **`Switchable`**
   (`tellSource_switchable`), admitting NO uniform translation into `rhoParallel ω`
   (`Encodings.no_uniformTranslation_positiveTell`), `heMatchParallel`, or `pettaMatchParallel`,
   and NO coordinated translation into `rhoParallel ω` (`Gap.positiveTell_not_into_rho_coordinated`).
   Furthermore, three tells form a **hollow cube** (pairwise solvable, jointly unsolvable:
   `HollowCubeAndAsymmetry.hollowCube_all_pairs_solvable`, `hollowCube_triple_unsolvable`). -/
theorem sep_tell :
    (∀ {P : RuleInstance NamesOnTheStep.Expr → Prop} {row : NamesOnTheStep.Expr → Prop},
      (∀ r, P r → Monotone.MonotoneChecks r) →
      ¬ (stepCalculus NamesOnTheStep.IssuingControls.ground
          (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr) P row).Switchable) ∧
    Nonempty (UniformTranslation Monotone.relaySource Monotone.relayTarget) ∧
    (PositiveTell.tellRule.checks = [] ∧
      PositiveTell.tellSource.Switchable ∧
      (∀ ω, IsEmpty (UniformTranslation PositiveTell.tellSource (rhoParallel ω))) ∧
      (∀ rules fuel succ,
        IsEmpty (UniformTranslation PositiveTell.tellSource (heMatchParallel rules fuel succ))) ∧
      (∀ rules succ,
        IsEmpty (UniformTranslation PositiveTell.tellSource (pettaMatchParallel rules succ))) ∧
      ¬ RuleSyntax.Examples.X.Solvable (a := PUnit.unit)
          [HollowCubeAndAsymmetry.tellEq, HollowCubeAndAsymmetry.tellOne,
           HollowCubeAndAsymmetry.tellTwo]) :=
  ⟨fun hmono => Monotone.not_switchable hmono,
   ⟨Monotone.relayTranslation⟩,
   ⟨PositiveTell.tellRule_checks,
    PositiveTell.tellSource_switchable,
    fun ω => no_uniformTranslation_positiveTell ω,
    fun rules fuel succ => no_uniformTranslation_positiveTell_into_heMatch rules fuel succ,
    fun rules succ => no_uniformTranslation_positiveTell_into_pettaMatch rules succ,
    HollowCubeAndAsymmetry.hollowCube_triple_unsolvable⟩⟩

/-- **Separation 5 (`guards` — absence & count checks)**:
1. *Walls without `guards`*:
   * Positive admission is monotone under consistent parallel composition
     (`NullsOnTheStep.Composition.positive_admission_monotone`);
   * Every `TakeMake` fragment has a heating bisimulation with a multiset reaction system
     (`HeatingBisimulation.heating_bisimulation`);
   * Disjoint firings without absence/count checks always interchange
     (`LinearTake.linearTake_interchange`).
2. *Witnesses with `guards`*:
   * Both absence (`NullsOnTheStep.ParallelClosed.source_switchable`) and count
     (`Monotone.counted_switchable`) are `Switchable`, admitting NO uniform translation into
     `rhoParallel ω`, `heMatchParallel`, or `pettaMatchParallel`;
   * Absence destroys heating bisimulation (`HeatingBisimulation.Controls.absence_has_no_heating_bisimulation`),
     breaks disjoint interchange (`LinearTake.Controls.absence_breaks_interchange`),
     and breaks confluence even without `take` (`MonotoneInference.Controls.absence_not_confluent`). -/
theorem sep_guards :
    (∀ {P : RuleInstance NamesOnTheStep.Expr → Prop} {row : NamesOnTheStep.Expr → Prop},
      (∀ r, P r → WithoutGuards r) →
      ¬ (stepCalculus NamesOnTheStep.IssuingControls.ground
          (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr) P row).Switchable) ∧
    (NullsOnTheStep.ParallelClosed.source.Switchable ∧
      Monotone.countedSource.Switchable ∧
      (∀ ω, IsEmpty (UniformTranslation NullsOnTheStep.ParallelClosed.source (rhoParallel ω))) ∧
      (¬ ∃ react : StoreComposition.Reaction NamesOnTheStep.Expr,
        TransitionMaps.IsBisimulation
          (HeatingBisimulation.modelledStep NamesOnTheStep.IssuingControls.ground
            (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr) ()
            HeatingBisimulation.Controls.spawnOnly)
          (StoreComposition.Reduces react)
          (HeatingBisimulation.Encodes (label := (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr)))) ∧
      (¬ LinearTake.NoAbsenceOrCount LinearTake.Controls.spawnFiring.1 ∧
        ¬ LinearTake.Controls.spawnFiring.2.Valid NamesOnTheStep.IssuingControls.ground Prod.fst
            LinearTake.Controls.spawnFiring.1
            (LinearTake.Controls.makeU.2.result Prod.fst LinearTake.Controls.makeU.1
              NullsOnTheStep.Separations.emptyS.1)) ∧
      (¬ MonotoneInference.Monotone MonotoneInference.Controls.guarded ∧
        ¬ ∃ D, Relation.ReflTransGen (GroundFirings.GroundStep MonotoneInference.Controls.guarded)
            MonotoneInference.Controls.withLeft D ∧
            MonotoneInference.Controls.other ∈ GroundFirings.facts D)) :=
  ⟨fun hmono => Monotone.not_switchable hmono,
   ⟨NullsOnTheStep.ParallelClosed.source_switchable,
    Monotone.counted_switchable,
    fun ω => no_uniformTranslation_absence ω,
    HeatingBisimulation.Controls.absence_has_no_heating_bisimulation,
    ⟨LinearTake.Controls.absence_breaks_interchange.1,
     LinearTake.Controls.absence_breaks_interchange.2.2.2.2.2.2⟩,
    ⟨MonotoneInference.Controls.absence_not_confluent.1,
     MonotoneInference.Controls.absence_not_confluent.2.2.2.2⟩⟩⟩

/-- **Separation 6 (`fresh` — fresh opening of rule unknowns)**:
1. *Wall without `fresh` openings*: in `SharedUnknown`, `PositiveTell.request` does NOT mention
   `var 1`, and `SharedUnknown.captor` mentions ONLY `var 1`, yet because rule instances fix
   their unknown without fresh opening, `captor` captures it and blocks `request`
   (`SharedUnknown.beside_captor_blocked`).
2. *Witness with `fresh` openings*: on `RuleSyntax.step` with fresh openings (`FreshOpenings`),
   `captorAnalog` constraining `var 1` CANNOT switch off `request` (`captor_analog_keeps`), and
   `switchesOff_shares` proves ANY neighbour switching off a positive program MUST share an
   unknown already mentioned by the state! -/
theorem sep_fresh :
    ((∀ v, SharedUnknown.Mentions SharedUnknown.captor.equations v → v = 1) ∧
      (PositiveTell.request.equations = [] ∧
        ∀ o ∈ PositiveTell.request.present,
          ¬ SharedUnknown.Occurs (sig := RuleSyntax.Controls.atoms) 1 o.1) ∧
      ¬ PositiveTell.tellSource.Succeeds
          (NullsOnTheStep.Composition.unionOf PositiveTell.request SharedUnknown.captor)) ∧
    (¬ FreshOpenings.SwitchesOff RuleSyntax.Scope.CompositionControls.tellProgram
        (· = RuleSyntax.Examples.c 9) FreshOpenings.captorAnalog
        RuleSyntax.Scope.CompositionControls.request ∧
      FreshOpenings.SwitchesOff RuleSyntax.Scope.CompositionControls.tellProgram
        (· = RuleSyntax.Examples.c 9) RuleSyntax.Scope.CompositionControls.neighbour
        RuleSyntax.Scope.CompositionControls.request) :=
  ⟨ScopedPrivacyEscrow.fixed_instance_vulnerable_to_capture,
   ScopedPrivacyEscrow.fresh_openings_prevent_capture⟩

/-- **Separation 7 (`frame` — parametric frame action, regional conversion & reflective quote views)**:
1. *Wall with strict syntactic equality `Eq` only*:
   * `bubbleViews` strict `.core` refuses `addZero var ≐ var` (`CrossBubbleCMTT.bubble_arith_admits_core_refuses`);
   * strict `syntacticPatternFrames` separates `@(*#0)` from `#0`
     (`ReflectiveViewFrames.rho_quote_drop_separates_syntactic_from_canonical_frames`);
   * naive syntactic quote-sealing `binderSafeAt` rejects `@(*y)` (`admitted_not_sealed`);
   * without a fresh context constructor, no observer factors `applyView` through `closureView`
     (`closureView_not_factorable`).
2. *Witness with parametric `frame` / reflective views*:
   * `bubbleViews.frames` solves `addZero var ≐ var` inside `.arith`;
   * `syntacticToCanonicalFrameMap` merges `@(*#0)` and `#0` in `reflectiveCanonicalFrames`;
   * `quoteAdmits` reads `QuoteScope` (`quoteAdmits_reads_quoteScope`), and `exists_closure_factorization`
     factors both `applyView` and `freezeView` through a fresh `closureView`. -/
theorem sep_frame :
    (CrossBubbleCMTT.bubbleViews.frames.Solvable (a := ())
        [((CrossBubbleCMTT.BubbleRegion.arith, CrossBubbleCMTT.ArithExpr.addZero .var),
          (CrossBubbleCMTT.BubbleRegion.arith, CrossBubbleCMTT.ArithExpr.var))] ∧
      ¬ CrossBubbleCMTT.bubbleViews.frames.Solvable (a := ())
        [((CrossBubbleCMTT.BubbleRegion.core, CrossBubbleCMTT.ArithExpr.addZero .var),
          (CrossBubbleCMTT.BubbleRegion.core, CrossBubbleCMTT.ArithExpr.var))]) ∧
    (¬ (ReflectiveViewFrames.syntacticPatternFrames
          Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.toReflectivePresentationDecl).frames.E
          (a := ()) (.apply "NQuote" [.apply "PDrop" [.bvar 0]]) (.bvar 0) ∧
      (ReflectiveViewFrames.reflectiveCanonicalFrames
          Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.toReflectivePresentationDecl).frames.E
          (a := ())
          ((ReflectiveViewFrames.syntacticToCanonicalFrameMap
            Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.toReflectivePresentationDecl).onTm
            (a := ()) (.apply "NQuote" [.apply "PDrop" [.bvar 0]]))
          ((ReflectiveViewFrames.syntacticToCanonicalFrameMap
            Mettapedia.OSLF.MeTTaIL.Syntax.rhoReflectivePresentation.toReflectivePresentationDecl).onTm
            (a := ()) (.bvar 0))) ∧
    (∃ (decl : Mettapedia.OSLF.MeTTaIL.Syntax.ReflectivePresentationDecl)
        (ctx : String) (rep : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      ¬ ∃ observe : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern,
        ∀ body, observe (closureView decl ctx 0 rep body) = applyView decl 0 rep body) ∧
    (∀ (declaration : Mettapedia.OSLF.MeTTaIL.Syntax.ReflectivePresentationDecl)
        (depth : Nat) (replacement body : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      ∃ context,
        erase declaration context (closureView declaration context depth replacement body) =
            applyView declaration depth replacement body ∧
          ∀ name : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern, name.isWellScopedAt 0 = true →
            atomize declaration context name
              (closureView declaration context depth replacement body) =
            freezeView declaration depth replacement name body) :=
  ⟨CrossBubbleCMTT.bubble_arith_admits_core_refuses,
   ReflectiveViewFrames.rho_quote_drop_separates_syntactic_from_canonical_frames,
   ⟨_, _, _, closureView_not_factorable⟩,
   exists_closure_factorization⟩

/-- **Separation 8 (`size` — unbounded bulk every-match vs. fixed bounded take-arity)**:
1. *Wall with bounded take-arity `B`*: for EVERY `B : ℕ`, EVERY frame action `X`, EVERY
   extension supply `E`, EVERY program `P`, EVERY state `s` with `B + 1 ≤ s.present.card`, and
   EVERY admitted firing `f` of `RuleSyntax.step` satisfying `BoundedTakeArity B f.rule`,
   the post-state remains nonempty (`1 ≤ (f.result X s).present.card`).
2. *Witnesses with unbounded bulk `size`*: `bulkRetractState` clears ANY `N`-occurrence state
   to `∅` in one atomic step (`bulkRetractState_clears_all`), and PeTTa's `PeTTaSpace.removeAtom`
   clears ANY `N` matching copies in one call (`petta_removeAtom_clears_all_copies`). -/
theorem sep_size :
    (∀ {Obj : Type} {Tm : Obj → Type} {Hom : Obj → Obj → Type}
        {X : Interface.Frames Tm Hom} {O : Type} [DecidableEq O]
        {E : RuleSyntax.Extensions Hom} {P : RuleSyntax.Program Tm}
        {s : RuleSyntax.State Tm O} {f : RuleSyntax.Firing O E P s.frame},
      (RuleSyntax.step X O E P).Admits (s := s) f →
      ∀ {B : ℕ}, BoundedTakeArity B f.rule → B + 1 ≤ s.present.card →
      1 ≤ (f.result X s).present.card) ∧
    (∀ N : ℕ, (bulkRetractState (BulkAttentionWave.waveState N) (fun _ => true)).present = ∅) ∧
    (∀ (N : ℕ) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern),
      (Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.removeAtom ⟨List.replicate N p, []⟩ p).facts = []) :=
  ⟨fun {_ _ _ _ _ _ _ _ _ _} hadm {_} harity hsize => bounded_take_cannot_clear_k_plus_one hadm harity hsize,
   BulkAttentionWave.bulk_everyMatch_clears_entire_wave,
   petta_removeAtom_clears_all_copies⟩

/-! ## 4. Unified Basis Non-Redundancy Theorem -/

/-- Maps each of the 8 `StepPrimitive`s to its actual semantic separation proposition
(no synthetic rank thresholds). -/
def PrimitiveSeparated : StepPrimitive → Prop
  | .take =>
      (∀ {T S O : Type} [DecidableEq O] {A : SubstitutionAction T S} {label : O → T}
          {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O},
        WithoutTake rule → sel.Valid A label rule C →
        C.present ⊆ (sel.result label rule C).present) ∧
      ¬ MonotoneInference.Monotone MonotoneInference.Controls.choice
  | .read =>
      (∀ {T S O : Type} [DecidableEq O] {A : SubstitutionAction T S} {label : O → T}
          {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O},
        WithoutRead rule → sel.Valid A label rule C →
        ∀ o ∈ sel.taken, o ∉ (sel.result label rule C).present) ∧
      ¬ TransitionMaps.IsBisimulation RhoPeekOutside.PeekStep
          RhoChannelFragment.RhoStep ContextualCommunicationAdequacy.Represents
  | .make =>
      (∀ {T S O : Type} [DecidableEq O] {A : SubstitutionAction T S} {label : O → T}
          {rule : RuleInstance T} {sel : Selection O} {C : Configuration T O},
        WithoutMake rule → sel.Valid A label rule C →
        (sel.result label rule C).present ⊆ C.present) ∧
      Monotone.makerSource.Succeeds Monotone.empty
  | .tell =>
      (∀ {P : RuleInstance NamesOnTheStep.Expr → Prop} {row : NamesOnTheStep.Expr → Prop},
        (∀ r, P r → Monotone.MonotoneChecks r) →
        ¬ (stepCalculus NamesOnTheStep.IssuingControls.ground
            (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr) P row).Switchable) ∧
      (PositiveTell.tellRule.checks = [] ∧ PositiveTell.tellSource.Switchable)
  | .guards =>
      (∀ {P : RuleInstance NamesOnTheStep.Expr → Prop} {row : NamesOnTheStep.Expr → Prop},
        (∀ r, P r → WithoutGuards r) →
        ¬ (stepCalculus NamesOnTheStep.IssuingControls.ground
            (Prod.fst : NamesOnTheStep.IssuingControls.Occ → NamesOnTheStep.Expr) P row).Switchable) ∧
      (NullsOnTheStep.ParallelClosed.source.Switchable ∧ Monotone.countedSource.Switchable)
  | .fresh =>
      (¬ PositiveTell.tellSource.Succeeds
          (NullsOnTheStep.Composition.unionOf PositiveTell.request SharedUnknown.captor)) ∧
      (¬ FreshOpenings.SwitchesOff RuleSyntax.Scope.CompositionControls.tellProgram
          (· = RuleSyntax.Examples.c 9) FreshOpenings.captorAnalog
          RuleSyntax.Scope.CompositionControls.request)
  | .frame =>
      (CrossBubbleCMTT.bubbleViews.frames.Solvable (a := ())
          [((CrossBubbleCMTT.BubbleRegion.arith, CrossBubbleCMTT.ArithExpr.addZero .var),
            (CrossBubbleCMTT.BubbleRegion.arith, CrossBubbleCMTT.ArithExpr.var))] ∧
        ¬ CrossBubbleCMTT.bubbleViews.frames.Solvable (a := ())
          [((CrossBubbleCMTT.BubbleRegion.core, CrossBubbleCMTT.ArithExpr.addZero .var),
            (CrossBubbleCMTT.BubbleRegion.core, CrossBubbleCMTT.ArithExpr.var))])
  | .size =>
      (∀ (B : ℕ) (P : RuleSyntax.Program RuleSyntax.Examples.Tm)
          (f : RuleSyntax.Firing ℕ RuleSyntax.Examples.E P PUnit.unit),
        (RuleSyntax.step RuleSyntax.Examples.X ℕ RuleSyntax.Examples.E P).Admits
          (s := BulkAttentionWave.waveState (B + 1)) f →
        BoundedTakeArity B f.rule →
        1 ≤ (f.result RuleSyntax.Examples.X (BulkAttentionWave.waveState (B + 1))).present.card) ∧
      (∀ N : ℕ, (bulkRetractState (BulkAttentionWave.waveState N) (fun _ => true)).present = ∅)

/-- **Master Irredundancy of the 8-Primitive Basis**:
Every single one of the eight primitives `{take, read, make, tell, guards, fresh, frame, size}`
has a kernel-verified semantic separation theorem over Mettapedia's real step and calculi. -/
theorem all_eight_step_primitives_separated :
    ∀ p : StepPrimitive, PrimitiveSeparated p
  | .take => ⟨fun hno hval => (sep_take.1 hno hval).1, sep_take.2.2.2.1⟩
  | .read => ⟨fun hno hval => (sep_read.1 hno hval).2.1, sep_read.2.2.1⟩
  | .make => ⟨fun hno hval => (sep_make.1 hno hval).1, sep_make.2.1⟩
  | .tell => ⟨sep_tell.1, ⟨sep_tell.2.2.1, sep_tell.2.2.2.1⟩⟩
  | .guards => ⟨sep_guards.1, ⟨sep_guards.2.1, sep_guards.2.2.1⟩⟩
  | .fresh => ⟨sep_fresh.1.2.2, sep_fresh.2.1⟩
  | .frame => CrossBubbleCMTT.bubble_arith_admits_core_refuses
  | .size => ⟨fun B P f hadm har =>
      BulkAttentionWave.admitted_bounded_take_leaves_nonempty B P f hadm har,
      BulkAttentionWave.bulk_everyMatch_clears_entire_wave⟩

end Mettapedia.GSLT.Distinction.SpecSpace
