import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetPeTTaBindings

/-!
# A variant of HE's matching step with the ordinary syntactic merge, and the machine it gives

HE's model fixes the binding record of a matching row only up to its meaning: a row hit may carry any
record with the solutions and names of the row's match merged into the call's record
(`LogicalMergeRel`). `DeclaredBranchGap` shows that this admits a circular record at which HE's type
check fails, where HE's interpreter, which merges syntactically, succeeds.

The model defines the logical merge against one canonical record: the match's assignments and
equalities followed by the incoming ones. This module takes that record itself.

* `merge`, `SynRowResultsRel`, `SynFrontierRel`: **the variant matching step**: as the model's, with
  the hit's record the syntactic merge `merge matched incoming` (and it must be satisfiable).
* Agreement with the model's step:
  * `SynFrontierRel.sound`: every variant frontier is a frontier of the model;
  * `frontier_represented`: every frontier of the model is a variant frontier up to how each work's
    record is written (same rows, positions, patterns and bodies; records with the same solutions and
    names), so the variant exists wherever the model's step does;
  * `frontier_unambiguous`: **where the model's step is unambiguous** (one frontier), the variant's is
    that frontier; `frontier_empty_iff`: in particular they agree on "no row matches";
  * `syn_iff`: the variant frontiers are exactly the model's frontiers whose records are syntactic
    merges.
* `VStep`: **the variant machine**: HE's machine whose frontier steps carry syntactic merges;
  `vstep_call_iff`: its step from a call to its equations is the model's rule with `SynFrontierRel`
  in place of `EquationFrontierRel`. `vstep_total`: it steps wherever the model steps.
  `vstep_of_unambiguous`: where a call's frontier is unique, every step of the model from the call
  is a step of the variant machine.
* `GoodV`, `EveryRunV`, `GoodV.every_run`: every run of the variant machine finishes and publishes the
  given answers; a complete run exists.
* `goodV_of_finishes`, `every_run_of_model`: **wherever the model's answers are determined on every
  run and every run finishes, the variant machine has the same answers on every run and finishes**:
  all earlier every-run results hold for the variant machine as they stand
  (`Controls.let_five_variant`, `Controls.both_variant`).
* `goodv_det` and the continuation and task steps of the variant machine, for
  `DeclaredBranchVariant`.

## Controls

* `Controls.cycle_not_variant` (negative): the circular record of `DeclaredBranchGap` is not the
  variant's record for that match; the variant's is the record at which the cast succeeds
  (`Controls.variant_record`, positive).
* `Controls.native_merge_is_variant` (positive), `Controls.native_merge_not_cycle` (negative): on
  those two records HE's executable merge (`mergeBindings`) has exactly the variant's record as its
  output, in either argument order, and the circular record is not among its outputs.
* `Controls.let_five_variant`, `Controls.both_variant` (positive): `(let $x 5 (pair $x $x))` and
  `(both)` on every run of the variant machine.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace SyntacticMerge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel
  EquationRowResultsRel AlphaVariantRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (LogicalMergeRel)
open Mettapedia.Languages.MeTTa.HE (BindingSourceAgreement)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open ServiceFootprints EntryToQuery AnswerBags EveryRun EveryRunFinishes ScopedTransfer
open NestedEveryRun (forall₂_append)

/-! ## The variant matching step -/

/-- **The ordinary syntactic merge** of a match into the incoming record: the match's assignments and
equalities, followed by the incoming ones. It is the record against which the model defines its
logical merge. -/
def merge (matched incoming : Bindings) : Bindings :=
  ⟨matched.assignments ++ incoming.assignments, matched.equalities ++ incoming.equalities⟩

/-- The syntactic merge is a logical merge when it is satisfiable. -/
theorem merge_logical {matched incoming : Bindings}
    (satisfiable : ∃ v : String → Atom, TypeBindingSatisfied v (merge matched incoming)) :
    LogicalMergeRel matched incoming (merge matched incoming) :=
  ⟨BindingSourceAgreement.refl _, satisfiable⟩

/-- **A logical merge exists exactly when the syntactic merge is satisfiable.** -/
theorem logical_iff {matched incoming : Bindings} :
    (∃ output, LogicalMergeRel matched incoming output) ↔
      ∃ v : String → Atom, TypeBindingSatisfied v (merge matched incoming) := by
  constructor
  · rintro ⟨output, agreement, v, model⟩
    exact ⟨v, (agreement.solutions v).mp model⟩
  · intro satisfiable
    exact ⟨_, merge_logical satisfiable⟩

/-- **The variant of the model's matching step for one row**: an irrelevant row and a row with no
viable match contribute nothing; a hit contributes one work whose record is the syntactic merge of
its match into the incoming record. -/
inductive SynRowResultsRel (live : List Atom) (query : Atom) (incoming : Bindings) :
    Nat → Atom → List EquationWork → Prop where
  | irrelevant (position : Nat) (row : Atom) :
      (∀ left right, row ≠ .expression [.symbol "=", left, right]) →
      SynRowResultsRel live query incoming position row []
  | miss (position : Nat) (left right pattern body : Atom) :
      AlphaVariantRel live query incoming left right pattern body →
      (∀ otherPattern otherBody,
        AlphaVariantRel live query incoming left right otherPattern otherBody →
        ∀ matched, ¬(MatchRel equalityGroundedSemantic query otherPattern matched ∧
          ∃ v : String → Atom, TypeBindingSatisfied v (merge matched incoming))) →
      SynRowResultsRel live query incoming position (.expression [.symbol "=", left, right]) []
  | hit (position : Nat) (left right pattern body : Atom) (matched : Bindings) :
      AlphaVariantRel live query incoming left right pattern body →
      MatchRel equalityGroundedSemantic query pattern matched →
      (∃ v : String → Atom, TypeBindingSatisfied v (merge matched incoming)) →
      SynRowResultsRel live query incoming position (.expression [.symbol "=", left, right])
        [⟨position, left, right, pattern, body, merge matched incoming⟩]

/-- **The variant frontier**: every stored row, by the variant row step. -/
inductive SynFrontierRel (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings) :
    List EquationWork → Prop where
  | completed {blocks : List (List EquationWork)} :
      List.Forall₂ (fun row block => SynRowResultsRel live query incoming row.2 row.1 block)
        space.atoms.zipIdx blocks →
      SynFrontierRel space live query incoming blocks.flatten

/-- The works of a list are syntactic merges of matches of the query. -/
def SynWorksAt (query : Atom) (incoming : Bindings) (works : List EquationWork) : Prop :=
  ∀ w ∈ works, ∃ matched, MatchRel equalityGroundedSemantic query w.pattern matched ∧
    w.bindings = merge matched incoming

/-- Two works that differ only in how their record is written. -/
def SameWork (w w' : EquationWork) : Prop :=
  w'.position = w.position ∧ w'.left = w.left ∧ w'.right = w.right ∧ w'.pattern = w.pattern ∧
    w'.body = w.body ∧ BindingSourceAgreement w.bindings w'.bindings

/-! ## Agreement with the model's step -/

theorem SynRowResultsRel.sound {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {position : Nat} {row : Atom} {block : List EquationWork},
      SynRowResultsRel live query incoming position row block →
      EquationRowResultsRel live query incoming position row block
  | _, _, _, .irrelevant position row notEquation => .irrelevant position row notEquation
  | _, _, _, .miss position left right pattern body alpha absent =>
      .miss position left right pattern body alpha fun otherPattern otherBody other matched output
        both => absent otherPattern otherBody other matched
          ⟨both.1, logical_iff.mp ⟨output, both.2⟩⟩
  | _, _, _, .hit position left right pattern body matched alpha matching satisfiable =>
      .hit position left right pattern body matched _ alpha matching (merge_logical satisfiable)

theorem SynRowResultsRel.works {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {position : Nat} {row : Atom} {block : List EquationWork},
      SynRowResultsRel live query incoming position row block → SynWorksAt query incoming block
  | _, _, _, .irrelevant _ _ _ => fun w member => by cases member
  | _, _, _, .miss _ _ _ _ _ _ _ => fun w member => by cases member
  | _, _, _, .hit _ _ _ _ _ matched _ matching _ => fun w member => by
      rw [List.mem_singleton] at member
      subst member
      exact ⟨matched, matching, rfl⟩

/-- **A row result of the model whose works are syntactic merges is a variant row result.** -/
theorem row_syntactic {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {position : Nat} {row : Atom} {block : List EquationWork},
      EquationRowResultsRel live query incoming position row block →
      SynWorksAt query incoming block → SynRowResultsRel live query incoming position row block
  | _, _, _, .irrelevant position row notEquation, _ => .irrelevant position row notEquation
  | _, _, _, .miss position left right pattern body alpha absent, _ =>
      .miss position left right pattern body alpha fun otherPattern otherBody other matched both =>
        absent otherPattern otherBody other matched _ ⟨both.1, merge_logical both.2⟩
  | _, _, _, .hit position left right pattern body matched output alpha matching merged,
      syntactic => by
      obtain ⟨matched', matching', same⟩ := syntactic _ List.mem_cons_self
      simp only at same matching'
      subst same
      exact .hit position left right pattern body matched' alpha matching' merged.2

/-- **Every row result of the model is a variant row result up to how the record is written.** -/
theorem row_represented {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {position : Nat} {row : Atom} {block : List EquationWork},
      EquationRowResultsRel live query incoming position row block →
      ∃ block', SynRowResultsRel live query incoming position row block' ∧
        List.Forall₂ SameWork block block'
  | _, _, _, .irrelevant position row notEquation => ⟨[], .irrelevant position row notEquation, .nil⟩
  | _, _, _, .miss position left right pattern body alpha absent =>
      ⟨[], .miss position left right pattern body alpha fun otherPattern otherBody other matched
        both => absent otherPattern otherBody other matched _ ⟨both.1, merge_logical both.2⟩, .nil⟩
  | _, _, _, .hit position left right pattern body matched output alpha matching merged => by
      obtain ⟨v, model⟩ := merged.2
      exact ⟨_, .hit position left right pattern body matched alpha matching
          ⟨v, (merged.1.solutions v).mp model⟩,
        .cons ⟨rfl, rfl, rfl, rfl, rfl, merged.1⟩ .nil⟩

theorem forall₂_flatten {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List (List α)} {ys : List (List β)}, List.Forall₂ (List.Forall₂ R) xs ys →
      List.Forall₂ R xs.flatten ys.flatten
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons here rest => by
      simp only [List.flatten_cons]
      exact forall₂_append here (forall₂_flatten rest)

theorem rows_represented {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {rows : List (Atom × Nat)} {blocks : List (List EquationWork)},
      List.Forall₂ (fun row block => EquationRowResultsRel live query incoming row.2 row.1 block)
        rows blocks →
      ∃ blocks', List.Forall₂ (fun row block =>
          SynRowResultsRel live query incoming row.2 row.1 block) rows blocks' ∧
        List.Forall₂ (List.Forall₂ SameWork) blocks blocks'
  | [], [], .nil => ⟨[], .nil, .nil⟩
  | _ :: _, _ :: _, .cons here rest => by
      obtain ⟨block', syn, same⟩ := row_represented here
      obtain ⟨blocks', syns, sames⟩ := rows_represented rest
      exact ⟨block' :: blocks', .cons syn syns, .cons same sames⟩

theorem rows_syntactic {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {rows : List (Atom × Nat)} {blocks : List (List EquationWork)},
      List.Forall₂ (fun row block => EquationRowResultsRel live query incoming row.2 row.1 block)
        rows blocks →
      SynWorksAt query incoming blocks.flatten →
      List.Forall₂ (fun row block => SynRowResultsRel live query incoming row.2 row.1 block)
        rows blocks
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons here rest, syntactic => by
      refine .cons (row_syntactic here fun w member => syntactic w ?_)
        (rows_syntactic rest fun w member => syntactic w ?_)
      · simp only [List.flatten_cons, List.mem_append]
        exact Or.inl member
      · simp only [List.flatten_cons, List.mem_append]
        exact Or.inr member

theorem rows_sound {live : List Atom} {query : Atom} {incoming : Bindings} :
    ∀ {rows : List (Atom × Nat)} {blocks : List (List EquationWork)},
      List.Forall₂ (fun row block => SynRowResultsRel live query incoming row.2 row.1 block)
        rows blocks →
      List.Forall₂ (fun row block => EquationRowResultsRel live query incoming row.2 row.1 block)
        rows blocks ∧ SynWorksAt query incoming blocks.flatten
  | [], [], .nil => ⟨.nil, fun w member => by cases member⟩
  | _ :: _, _ :: _, .cons here rest => by
      obtain ⟨models, syntactic⟩ := rows_sound rest
      refine ⟨.cons here.sound models, fun w member => ?_⟩
      simp only [List.flatten_cons, List.mem_append] at member
      rcases member with inHere | inRest
      · exact here.works w inHere
      · exact syntactic w inRest

/-- **Every variant frontier is a frontier of the model.** -/
theorem SynFrontierRel.sound {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} (syn : SynFrontierRel space live query incoming works) :
    EquationFrontierRel space live query incoming works := by
  cases syn with
  | completed covered => exact .completed (rows_sound covered).1

/-- The works of a variant frontier are syntactic merges. -/
theorem SynFrontierRel.works {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} (syn : SynFrontierRel space live query incoming works) :
    SynWorksAt query incoming works := by
  cases syn with
  | completed covered => exact (rows_sound covered).2

/-- **The variant frontiers are exactly the model's frontiers whose records are syntactic merges.** -/
theorem syn_iff {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} :
    SynFrontierRel space live query incoming works ↔
      EquationFrontierRel space live query incoming works ∧ SynWorksAt query incoming works := by
  constructor
  · intro syn
    exact ⟨syn.sound, syn.works⟩
  · rintro ⟨model, syntactic⟩
    cases model with
    | completed covered => exact .completed (rows_syntactic covered syntactic)

/-- **Every frontier of the model is a variant frontier up to how each work's record is written**:
the variant step exists wherever the model's does, with the same rows, patterns and bodies. -/
theorem frontier_represented {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} (model : EquationFrontierRel space live query incoming works) :
    ∃ works', SynFrontierRel space live query incoming works' ∧ List.Forall₂ SameWork works works' := by
  cases model with
  | completed covered =>
      obtain ⟨blocks', syn, same⟩ := rows_represented covered
      exact ⟨_, .completed syn, forall₂_flatten same⟩

/-- **Where the model's step is unambiguous, the variant's step is the model's.** -/
theorem frontier_unambiguous {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings}
    {works : List EquationWork} (model : EquationFrontierRel space live query incoming works)
    (unique : ∀ works', EquationFrontierRel space live query incoming works' → works' = works) :
    SynFrontierRel space live query incoming works := by
  obtain ⟨works', syn, _⟩ := frontier_represented model
  rw [← unique works' syn.sound]
  exact syn

/-- **The model and the variant agree on "no row matches".** -/
theorem frontier_empty_iff {space : Space} {live : List Atom} {query : Atom} {incoming : Bindings} :
    EquationFrontierRel space live query incoming [] ↔ SynFrontierRel space live query incoming [] := by
  constructor
  · intro model
    exact syn_iff.mpr ⟨model, fun w member => by cases member⟩
  · exact fun syn => syn.sound

/-! ## The variant machine -/

/-- The works of a frontier step are syntactic merges of matches of the call into its activation. -/
def SynWorks (value : Entry.Value) (activation : Frame) (works : List EquationWork) : Prop :=
  SynWorksAt value.erase activation.bindings works

/-- A step from a call (or an explicit invocation) to its equations carries syntactic merges; every
other step is unconstrained. -/
def FrontierSyntactic (x y : HEConfig) : Prop :=
  match x.control, y.control with
  | .work (.call _ _ value _ activation), .work (.equations _ _ _ _ _ works) =>
      SynWorks value activation works
  | .work (.invocation _ _ _ value activation), .work (.invocationEquations _ _ _ _ works) =>
      SynWorks value activation works
  | _, _ => True

/-- **The variant machine**: HE's machine whose frontier steps carry the syntactic merge. -/
def VStep (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) (x y : HEConfig) :
    Prop :=
  HEStep dispatch lookup policy x y ∧ FrontierSyntactic x y

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

theorem VStep.model {x y : HEConfig} (step : VStep dispatch lookup policy x y) :
    HEStep dispatch lookup policy x y := step.1

theorem vsteps_model {x y : HEConfig}
    (run : Relation.ReflTransGen (VStep dispatch lookup policy) x y) :
    Relation.ReflTransGen (HEStep dispatch lookup policy) x y := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step.1

/-- **The variant machine's step from a call to its equations is the model's rule with the variant
frontier.** -/
theorem vstep_call_iff {space : Space} {live : List Atom} {scope : List String} {value : Entry.Value}
    {expected : Atom} {activation : Frame} {works : List EquationWork} {stack : List Continuation}
    {emitted : List Result} :
    VStep dispatch lookup policy
        ⟨space, .work (.call live scope value expected activation), stack, emitted⟩
        ⟨space, .work (.equations live scope value expected activation works), stack, emitted⟩ ↔
      ¬ IsErrorRel value.erase ∧ NonGroundedCallRel dispatch value.erase ∧
        SynFrontierRel space (expected :: live) value.erase activation.bindings works ∧
        works ≠ [] := by
  constructor
  · rintro ⟨step, syntactic⟩
    cases step with
    | internal l =>
        cases l with
        | callEquations notError nonGrounded frontier nonempty =>
            exact ⟨notError, nonGrounded, syn_iff.mpr ⟨frontier, syntactic⟩, nonempty⟩
  · rintro ⟨notError, nonGrounded, syn, nonempty⟩
    exact ⟨.internal (.callEquations notError nonGrounded syn.sound nonempty), syn.works⟩

/-- **Where the model's matching step is unambiguous, the variant machine's steps from the call are
the model's steps**: when the call's frontier is unique, every step of the model from the call is a
step of the variant machine. -/
theorem vstep_of_unambiguous {space : Space} {live : List Atom} {scope : List String}
    {value : Entry.Value} {expected : Atom} {activation : Frame} {stack : List Continuation}
    {emitted : List Result}
    (unique : ∀ works works', EquationFrontierRel space (expected :: live) value.erase
        activation.bindings works →
      EquationFrontierRel space (expected :: live) value.erase activation.bindings works' →
      works' = works)
    {y : HEConfig}
    (step : HEStep dispatch lookup policy
      ⟨space, .work (.call live scope value expected activation), stack, emitted⟩ y) :
    VStep dispatch lookup policy
      ⟨space, .work (.call live scope value expected activation), stack, emitted⟩ y := by
  refine ⟨step, ?_⟩
  cases step with
  | internal l =>
      cases l with
      | callError _ => exact True.intro
      | callEmbedded _ _ _ => exact True.intro
      | callAbsent _ _ _ => exact True.intro
      | callEquations _ _ frontier _ =>
          exact (frontier_unambiguous frontier fun works' other => unique _ works' frontier
            other).works

/-- Which steps are frontier steps. -/
theorem frontier_free_or {admission : Completed.ArgumentService} {space : Space}
    {before after : Control × List Continuation}
    (l : LocalStepWith admission space dispatch lookup policy before after)
    (emitted : List Result) :
    FrontierSyntactic ⟨space, before.1, before.2, emitted⟩ ⟨space, after.1, after.2, emitted⟩ ∨
      (∃ live scope value expected activation works,
        before.1 = .work (.call live scope value expected activation) ∧
        after = (.work (.equations live scope value expected activation works), before.2) ∧
        ¬ IsErrorRel value.erase ∧ NonGroundedCallRel dispatch value.erase ∧
        EquationFrontierRel space (expected :: live) value.erase activation.bindings works ∧
        works ≠ []) ∨
      (∃ live scope caller value activation works,
        before.1 = .work (.invocation live scope caller value activation) ∧
        after = (.work (.invocationEquations live scope value activation works), before.2) ∧
        NonGroundedCallRel dispatch value.erase ∧
        EquationFrontierRel space live value.erase activation.bindings works ∧ works ≠ []) := by
  cases l
  case callEquations =>
    exact Or.inr (Or.inl ⟨_, _, _, _, _, _, rfl, rfl, by assumption, by assumption, by assumption,
      by assumption⟩)
  case invocationEquations =>
    exact Or.inr (Or.inr ⟨_, _, _, _, _, _, rfl, rfl, by assumption, by assumption,
      by assumption⟩)
  all_goals exact Or.inl True.intro

theorem same_length {works works' : List EquationWork} (same : List.Forall₂ SameWork works works')
    (nonempty : works ≠ []) : works' ≠ [] := by
  intro none
  subst none
  cases same
  exact nonempty rfl

/-- **The variant machine steps wherever the model steps.** -/
theorem vstep_total {x y : HEConfig} (step : HEStep dispatch lookup policy x y) :
    ∃ y', VStep dispatch lookup policy x y' := by
  cases step with
  | publish => exact ⟨_, .publish, True.intro⟩
  | @internal space before stack after remaining emitted l =>
      rcases frontier_free_or l emitted with free |
        ⟨live, scope, value, expected, activation, works, isCall, _, notError, nonGrounded,
          frontier, nonempty⟩ |
        ⟨live, scope, caller, value, activation, works, isInvocation, _, nonGrounded, frontier,
          nonempty⟩
      · exact ⟨_, .internal l, free⟩
      · simp only at isCall
        subst isCall
        obtain ⟨works', syn, same⟩ := frontier_represented frontier
        exact ⟨_, .internal (.callEquations notError nonGrounded syn.sound
          (same_length same nonempty)), syn.works⟩
      · simp only at isInvocation
        subst isInvocation
        obtain ⟨works', syn, same⟩ := frontier_represented frontier
        exact ⟨_, .internal (.invocationEquations nonGrounded syn.sound
          (same_length same nonempty)), syn.works⟩

/-! ## Every run of the variant machine -/

/-- **Every run of the variant machine from `x` finishes and publishes `target`**: `x` is final with
`target` published, or `x` can step and every successor is such. -/
inductive GoodV (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (target : List Atom) : HEConfig → Prop
  | final {space : Space} {emitted : List Result} :
      emitted.map (fun r => r.1.erase) = target →
      GoodV dispatch lookup policy target ⟨space, .returning [], [], emitted⟩
  | step {x : HEConfig} : (∃ y, VStep dispatch lookup policy x y) →
      (∀ y, VStep dispatch lookup policy x y → GoodV dispatch lookup policy target y) →
      GoodV dispatch lookup policy target x

variable {target : List Atom}

theorem GoodV.next {x y : HEConfig} (good : GoodV dispatch lookup policy target x)
    (step : VStep dispatch lookup policy x y) : GoodV dispatch lookup policy target y := by
  cases good with
  | final => exact absurd step.1 final_no_step
  | step _ all => exact all y step

theorem GoodV.reaches {x y : HEConfig} (good : GoodV dispatch lookup policy target x)
    (run : Relation.ReflTransGen (VStep dispatch lookup policy) x y) :
    GoodV dispatch lookup policy target y := by
  induction run with
  | refl => exact good
  | tail _ step ih => exact ih.next step

theorem GoodV.acc {x : HEConfig} (good : GoodV dispatch lookup policy target x) :
    Acc (fun b a => VStep dispatch lookup policy a b) x := by
  induction good with
  | final => exact Acc.intro _ fun y step => absurd step.1 final_no_step
  | step _ _ ih => exact Acc.intro _ fun y step => ih y step

theorem GoodV.published {space : Space} {emitted : List Result}
    (good : GoodV dispatch lookup policy target ⟨space, .returning [], [], emitted⟩) :
    emitted.map (fun r => r.1.erase) = target := by
  cases good with
  | final same => exact same
  | step moves _ =>
      obtain ⟨y, step⟩ := moves
      exact absurd step.1 final_no_step

theorem GoodV.exists_final {x : HEConfig} (good : GoodV dispatch lookup policy target x) :
    ∃ (space : Space) (emitted : List Result),
      Relation.ReflTransGen (VStep dispatch lookup policy) x ⟨space, .returning [], [], emitted⟩ := by
  induction good with
  | final => exact ⟨_, _, .refl⟩
  | step moves _ ih =>
      obtain ⟨y, step⟩ := moves
      obtain ⟨space, emitted, run⟩ := ih y step
      exact ⟨space, emitted, .head step run⟩

/-- **Every run of the variant machine from the entry of `c` finishes with `L`, and one exists.** -/
def EveryRunV (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) (space : Space)
    (c : Atom) (L : List Atom) : Prop :=
  (∃ answers : List Result,
    Relation.ReflTransGen (VStep dispatch lookup policy) (load space c Atom.undefinedType)
      (final space answers)) ∧
  (∀ emitted : List Result,
    Relation.ReflTransGen (VStep dispatch lookup policy) (load space c Atom.undefinedType)
      (final space emitted) → emitted.map (fun r => r.1.erase) = L) ∧
  Acc (fun b a => VStep dispatch lookup policy a b) (load space c Atom.undefinedType) ∧
  ∀ y, Relation.ReflTransGen (VStep dispatch lookup policy) (load space c Atom.undefinedType) y →
    (∃ z, VStep dispatch lookup policy y z) ∨
      ∃ emitted : List Result, y = final space emitted ∧ emitted.map (fun r => r.1.erase) = L

theorem GoodV.every_run {space : Space} {c : Atom} {L : List Atom}
    (good : GoodV dispatch lookup policy L (load space c Atom.undefinedType)) :
    EveryRunV dispatch lookup policy space c L := by
  refine ⟨?_, fun emitted run => (good.reaches run).published, good.acc, fun y run => ?_⟩
  · obtain ⟨space', emitted, run⟩ := good.exists_final
    have same : space' = space := space_fixed (vsteps_model run)
    subst same
    exact ⟨emitted, run⟩
  · have here := good.reaches run
    cases here with
    | final same =>
        have fixed := space_fixed (vsteps_model run)
        simp only at fixed
        subst fixed
        exact Or.inr ⟨_, rfl, same⟩
    | step moves _ => exact Or.inl moves

/-- **Wherever every run of the model finishes with `L`, every run of the variant machine does.** -/
theorem goodV_of_finishes {space : Space} {c : Atom} {L : List Atom}
    (finishes : Finishes dispatch lookup policy space c L) :
    GoodV dispatch lookup policy L (load space c Atom.undefinedType) := by
  obtain ⟨acc, every⟩ := finishes
  have each : ∀ y, Acc (fun b a => HEStep dispatch lookup policy a b) y →
      Relation.ReflTransGen (HEStep dispatch lookup policy) (load space c Atom.undefinedType) y →
      GoodV dispatch lookup policy L y := by
    intro y accY
    induction accY with
    | intro y _ ih =>
        intro path
        rcases every y path with ⟨z, step⟩ | ⟨emitted, rfl, same⟩
        · exact .step (vstep_total step) fun z' step' => ih z' step'.1 (path.tail step'.1)
        · exact .final same
  exact each _ acc .refl

/-- **The model's every-run results hold for the variant machine as they stand.** -/
theorem every_run_of_model {space : Space} {c : Atom} {L : List Atom}
    (finishes : Finishes dispatch lookup policy space c L) :
    EveryRunV dispatch lookup policy space c L :=
  (goodV_of_finishes finishes).every_run

/-! ## Steps of the variant machine -/

/-- A unique step of the model that is not a constrained frontier step. -/
theorem goodv_det {x y : HEConfig} (moves : HEStep dispatch lookup policy x y)
    (only : ∀ z, HEStep dispatch lookup policy x z → z = y) (free : FrontierSyntactic x y)
    (next : GoodV dispatch lookup policy target y) : GoodV dispatch lookup policy target x :=
  .step ⟨y, moves, free⟩ fun z step => by rw [only z step.1]; exact next

section Frames

variable {space : Space} {stack : List Continuation} {emitted : List Result} {live : List Atom}
  {scope : List String}

theorem goodv_singleton {R : List Result}
    (next : GoodV dispatch lookup policy target ⟨space, .returning (R.map Completed.tupleSingleton),
      stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning R, .singleton :: stack, emitted⟩ :=
  goodv_det (.internal .singleton) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_branches_frame {tail : List Entry.Value} {heads : List Result}
    (next : GoodV dispatch lookup policy target ⟨space, .work (.branches live scope tail heads),
      stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning heads,
      .branches live scope tail :: stack, emitted⟩ :=
  goodv_det (.internal .branches) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_tupleTail {head : Entry.Value} {R : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .returning (R.map (Completed.tuplePrepend head)), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning R, .tupleTail head :: stack, emitted⟩ :=
  goodv_det (.internal .tupleTail) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_append {remaining : Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Task}
    {R : List Result}
    (next : GoodV dispatch lookup policy target ⟨space, .work remaining, .prepend R :: stack,
      emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning R, .append remaining :: stack, emitted⟩ :=
  goodv_det (.internal .append) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_prepend {selected R : List Result}
    (next : GoodV dispatch lookup policy target ⟨space, .returning (selected ++ R), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning R, .prepend selected :: stack, emitted⟩ :=
  goodv_det (.internal .prepend) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_calls_frame {expected : Atom} {rows : List Result}
    (next : GoodV dispatch lookup policy target ⟨space, .work (.calls live scope expected rows),
      stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning rows,
      .calls live scope expected :: stack, emitted⟩ :=
  goodv_det (.internal .calls) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_diagnostics {errors : List Atom} {activation : Frame} {R : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .returning (R ++ Completed.diagnosticResults errors activation), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning R,
      .diagnostics errors activation :: stack, emitted⟩ :=
  goodv_det (.internal .diagnostics) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_boundaryBatch_frame {caller : Option Atom} {site : Completed.Boundary}
    {rows : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.boundaryBatch live scope caller site rows), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning rows,
      .boundaryBatch live scope caller site :: stack, emitted⟩ :=
  goodv_det (.internal .boundaryBatch) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

/-- The publication frame: every answer is answerable, so all are kept. -/
theorem goodv_publish {R : List Result} {original : Atom} (clean : ∀ r ∈ R, Answerable r.1.erase)
    (next : GoodV dispatch lookup policy target ⟨space,
      .returning (R.map (Completed.publishResult policy original)), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning R, .publish original :: stack, emitted⟩ := by
  have unchanged : R.map (Completed.readResult policy) = R :=
    map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase) (R.map (Completed.readResult policy)) R := by
    rw [unchanged]
    exact HERuns.success_all R fun r member => (clean r member).notError
  refine goodv_det (.internal (.publish selected)) (fun z step => ?_) True.intro next
  cases step with
  | internal l =>
      cases l with
      | publish chosen =>
          rw [Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional chosen
            selected]

/-- **The top level drains its batch**: the publication rule moves the answers one by one. -/
theorem goodv_top : ∀ (R emitted : List Result),
    (emitted ++ R).map (fun r => r.1.erase) = target →
    GoodV dispatch lookup policy target ⟨space, .returning R, [], emitted⟩
  | [], emitted, same => .final (by simpa using same)
  | r :: rs, emitted, same => goodv_det .publish (fun z step => by
      cases step with
      | internal l => cases l
      | publish => rfl) True.intro (goodv_top rs (emitted ++ [r]) (by simpa using same))

theorem goodv_tuple_singleton {v : Entry.Value} {activation : Frame}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.atom live scope v Atom.undefinedType activation), .singleton :: stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .work (.tuple live scope [v] activation), stack,
      emitted⟩ :=
  goodv_det (.internal .tupleSingleton) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_tuple_cons {head second : Entry.Value} {remaining : List Entry.Value}
    {activation : Frame}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.atom (.expression ((second :: remaining).map Entry.Value.erase) :: live) scope head
        Atom.undefinedType activation), .branches live scope (second :: remaining) :: stack,
        emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.tuple live scope (head :: second :: remaining) activation), stack, emitted⟩ :=
  goodv_det (.internal .tupleCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_branches_nil {tail : List Entry.Value}
    (next : GoodV dispatch lookup policy target ⟨space, .returning [], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .work (.branches live scope tail []), stack,
      emitted⟩ :=
  goodv_det (.internal .branchesNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_branches_cons {tail : List Entry.Value} {head : Result} {heads : List Result}
    (clean : ¬ IsEmptyOrErrorRel head.1.erase)
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.tuple (head.1.erase :: live) scope tail head.2),
      .tupleTail head.1 :: .append (.branches live scope tail heads) :: stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .work (.branches live scope tail (head :: heads)),
      stack, emitted⟩ :=
  goodv_det (.internal (.branchesContinue clean)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | branchesStopped stopped => exact absurd stopped clean
        | branchesContinue _ => rfl) True.intro next

theorem goodv_calls_nil {expected : Atom}
    (next : GoodV dispatch lookup policy target ⟨space, .returning [], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .work (.calls live scope expected []), stack,
      emitted⟩ :=
  goodv_det (.internal .callsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_calls_cons {expected : Atom} {head : Result} {heads : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.call live scope head.1 expected head.2),
      .append (.calls live scope expected heads) :: stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .work (.calls live scope expected (head :: heads)),
      stack, emitted⟩ :=
  goodv_det (.internal .callsCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_equations_nil {original : Entry.Value} {expected : Atom} {activation : Frame}
    (next : GoodV dispatch lookup policy target ⟨space, .returning [], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.equations live scope original expected activation []), stack, emitted⟩ :=
  goodv_det (.internal .equationsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_boundary_producer {caller : Option Atom} {value : Entry.Value} {activation : Frame}
    (raw : ¬ Completed.FunctionPending policy value)
    (next : GoodV dispatch lookup policy target ⟨space, .returning [(value, activation)], stack,
      emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.boundary live scope caller .producer value activation), stack, emitted⟩ :=
  goodv_det (.internal (.boundaryProducerRaw raw)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | boundaryProducerRaw _ => rfl
        | boundaryProducerFunction pending => exact absurd pending raw) True.intro next

theorem goodv_boundaryBatch_nil {caller : Option Atom} {site : Completed.Boundary}
    (next : GoodV dispatch lookup policy target ⟨space, .returning [], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .work (.boundaryBatch live scope caller site []),
      stack, emitted⟩ :=
  goodv_det (.internal .boundaryBatchNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_boundaryBatch_cons {caller : Option Atom} {site : Completed.Boundary} {head : Result}
    {heads : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.boundary live scope caller site head.1 head.2),
      .append (.boundaryBatch live scope caller site heads) :: stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.boundaryBatch live scope caller site (head :: heads)), stack, emitted⟩ :=
  goodv_det (.internal .boundaryBatchCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_boundary_returned {caller : Option Atom} {original value : Entry.Value}
    {expected : Atom} {activation : Frame}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.returned live scope original expected value activation), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.boundary live scope caller (.returned original expected) value activation), stack,
        emitted⟩ :=
  goodv_det (.internal .boundaryReturned) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_returned_evaluate {original value : Entry.Value} {expected : Atom} {activation : Frame}
    (notRefused : value.erase ≠ Atom.notReducible) (notStopped : ¬ IsEmptyOrErrorRel value.erase)
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.atom live scope value expected activation), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.returned live scope original expected value activation), stack, emitted⟩ :=
  goodv_det (.internal (.returnEvaluate notRefused notStopped)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | returnRefused refused => exact absurd refused notRefused
        | returnStopped stopped => exact absurd stopped notStopped
        | returnEvaluate _ _ => rfl) True.intro next

theorem goodv_invocations_nil {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value}
    (next : GoodV dispatch lookup policy target ⟨space, .returning [], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.invocations live scope expected signature operator arguments []), stack, emitted⟩ :=
  goodv_det (.internal .invocationsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_invocations_cons {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value} {activation : Frame}
    {activations : List Frame}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.function (Completed.invocationReturnType signature :: live) scope expected signature
        operator arguments activation),
      .calls live scope (Completed.invocationReturnType signature) ::
        .append (.invocations live scope expected signature operator arguments activations) ::
          stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.invocations live scope expected signature operator arguments
        (activation :: activations)), stack, emitted⟩ :=
  goodv_det (.internal .invocationsCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_functionStart {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value} {activation : Frame}
    (arity : arguments.length = signature.argumentTypes.length)
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.atom (signature.functionType :: arguments.map Entry.Value.erase ++ live)
        (scope ++ expectedApplicationScope
          (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
        operator signature.functionType activation),
      .functionHeads live scope (arguments.zip signature.argumentTypes) :: stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.function live scope expected signature operator arguments activation), stack,
      emitted⟩ :=
  goodv_det (.internal (.functionStart arity)) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_functionHeads_frame {requests : List Completed.ArgumentRequest} {heads : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.functionBranches live scope requests heads), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning heads,
      .functionHeads live scope requests :: stack, emitted⟩ :=
  goodv_det (.internal .functionHeads) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_functionBranches_nil {requests : List Completed.ArgumentRequest}
    (next : GoodV dispatch lookup policy target ⟨space, .returning [], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .work (.functionBranches live scope requests []),
      stack, emitted⟩ :=
  goodv_det (.internal .functionBranchesNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_functionBranches_continue {requests : List Completed.ArgumentRequest}
    {head : Result} {heads : List Result} (notStopped : ¬ IsEmptyOrErrorRel head.1.erase)
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.arguments (head.1.erase :: live) scope requests head.2),
      .functionAssemble head.1 :: .append (.functionBranches live scope requests heads) :: stack,
      emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.functionBranches live scope requests (head :: heads)), stack, emitted⟩ :=
  goodv_det (.internal (.functionBranchesContinue notStopped)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | functionBranchesStopped stopped => exact absurd stopped notStopped
        | functionBranchesContinue _ => rfl) True.intro next

theorem goodv_functionAssemble {head : Entry.Value} {R : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .returning (R.map (Completed.functionAssemble head)), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning R, .functionAssemble head :: stack,
      emitted⟩ :=
  goodv_det (.internal .functionAssemble) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_argumentsNil {activation : Frame}
    (next : GoodV dispatch lookup policy target ⟨space,
      .returning [(Entry.Value.argumentPacket [], activation)], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .work (.arguments live scope [] activation), stack,
      emitted⟩ :=
  goodv_det (.internal .argumentsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_argumentsCons {request : Completed.ArgumentRequest}
    {requests : List Completed.ArgumentRequest} {activation : Frame}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.atom (Completed.argumentScope requests ++ live) scope request.1 request.2 activation),
      .arguments live scope request.1 requests :: stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.arguments live scope (request :: requests) activation), stack, emitted⟩ :=
  goodv_det (.internal .argumentsCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_arguments_frame {original : Entry.Value} {requests : List Completed.ArgumentRequest}
    {heads : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.argumentBranches live scope original requests heads), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning heads,
      .arguments live scope original requests :: stack, emitted⟩ :=
  goodv_det (.internal .arguments) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_argumentBranches_nil {original : Entry.Value}
    {requests : List Completed.ArgumentRequest}
    (next : GoodV dispatch lookup policy target ⟨space, .returning [], stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.argumentBranches live scope original requests []), stack, emitted⟩ :=
  goodv_det (.internal .argumentBranchesNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

theorem goodv_argumentBranches_continue {original : Entry.Value}
    {requests : List Completed.ArgumentRequest} {head : Result} {heads : List Result}
    (notStopped : ¬ Completed.ArgumentStopped original head)
    (next : GoodV dispatch lookup policy target ⟨space,
      .work (.arguments (head.1.erase :: live) scope requests head.2),
      .argumentTail head.1 :: .append (.argumentBranches live scope original requests heads) ::
        stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space,
      .work (.argumentBranches live scope original requests (head :: heads)), stack, emitted⟩ :=
  goodv_det (.internal (.argumentBranchesContinue notStopped)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | argumentBranchesStopped stopped => exact absurd stopped notStopped
        | argumentBranchesContinue _ => rfl) True.intro next

theorem goodv_argumentTail {head : Entry.Value} {R : List Result}
    (next : GoodV dispatch lookup policy target ⟨space,
      .returning (R.map (Completed.argumentPrepend head)), stack, emitted⟩) :
    GoodV dispatch lookup policy target ⟨space, .returning R, .argumentTail head :: stack, emitted⟩ :=
  goodv_det (.internal .argumentTail) (fun z step => by
    cases step with
    | internal l => cases l; rfl) True.intro next

/-- Pending work under an `Atom` demand: delivery is the only step. -/
theorem goodv_atom_demand {value : Entry.Value} {activation : Frame}
    (next : GoodV dispatch lookup policy target
      ⟨space, .returning [(activation.read policy value, activation)], stack, emitted⟩) :
    GoodV dispatch lookup policy target
      ⟨space, .work (.atom live scope value Atom.atomType activation), stack, emitted⟩ :=
  goodv_det (.internal (.delivered (AtomDemands.atom_demand_deliver _)))
    (fun _ step => AtomDemands.atom_demand_step step) True.intro next

end Frames

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app)

/-- **Positive control**: for the row match and the call's record of `DeclaredBranchGap`, the
variant's record is the syntactic record, at which the cast of `1` against `$t` succeeds
(`DeclaredBranchGap.syntactic_cast_succeeds`). -/
theorem variant_record :
    merge DeclaredBranchGap.rowMatch DeclaredBranchGap.callFrame = DeclaredBranchGap.syntacticFrame :=
  rfl

/-- **Negative control**: the circular record the model admits
(`DeclaredBranchGap.cycle_admitted`) is not the variant's record. -/
theorem cycle_not_variant :
    DeclaredBranchGap.cycleFrame ≠ merge DeclaredBranchGap.rowMatch DeclaredBranchGap.callFrame := by
  decide

/-- **Positive control, the model's executable merge**: for the row match and the call's record of
`DeclaredBranchGap`, HE's executable merge (`mergeBindings`) has one output, in either argument
order, and it is the variant's record. -/
theorem native_merge_is_variant :
    Mettapedia.Languages.MeTTa.HE.mergeBindings DeclaredBranchGap.rowMatch
        DeclaredBranchGap.callFrame 10 =
      [merge DeclaredBranchGap.rowMatch DeclaredBranchGap.callFrame] ∧
    Mettapedia.Languages.MeTTa.HE.mergeBindings DeclaredBranchGap.callFrame
        DeclaredBranchGap.rowMatch 10 =
      [merge DeclaredBranchGap.rowMatch DeclaredBranchGap.callFrame] := by
  constructor <;> decide +kernel

/-- **Negative control, the model's executable merge**: the circular record is not an output of the
executable merge; it comes from the relation's freedom alone. -/
theorem native_merge_not_cycle :
    DeclaredBranchGap.cycleFrame ∉ Mettapedia.Languages.MeTTa.HE.mergeBindings
      DeclaredBranchGap.rowMatch DeclaredBranchGap.callFrame 10 := by
  decide +kernel

/-- **Positive control**: `(let $x 5 (pair $x $x))` on every run of the variant machine. -/
theorem let_five_variant (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList LetEveryRun.Controls.letIfRows)
      LetEveryRun.Controls.fiveCall [app "pair" [.grounded (.int 5), .grounded (.int 5)]] :=
  every_run_of_model (LetEveryRun.Controls.five_every_run policy).2.1

/-- **Positive control**: `(both)`, the polymorphic `if` twice in one body, on every run of the
variant machine. -/
theorem both_variant (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList IfInBodies.Controls.bothRows)
      (app "both" []) [app "pair" [sym "yes", sym "no"]] :=
  every_run_of_model (IfInBodies.Controls.both_every_run policy).2.1

end Controls

#print axioms logical_iff
#print axioms SynFrontierRel.sound
#print axioms syn_iff
#print axioms frontier_represented
#print axioms frontier_unambiguous
#print axioms frontier_empty_iff
#print axioms vstep_call_iff
#print axioms vstep_of_unambiguous
#print axioms vstep_total
#print axioms GoodV.every_run
#print axioms goodV_of_finishes
#print axioms every_run_of_model
#print axioms goodv_publish
#print axioms goodv_top
#print axioms Controls.variant_record
#print axioms Controls.cycle_not_variant
#print axioms Controls.native_merge_is_variant
#print axioms Controls.native_merge_not_cycle
#print axioms Controls.let_five_variant
#print axioms Controls.both_variant

end SyntacticMerge

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
