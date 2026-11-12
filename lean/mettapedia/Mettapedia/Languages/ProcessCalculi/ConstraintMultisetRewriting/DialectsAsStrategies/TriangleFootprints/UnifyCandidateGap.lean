import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.SyntacticMerge

/-!
# The same freedom at `unify`: its candidate record is also fixed only up to meaning

`DeclaredBranchGap` shows that HE's model lets a row hit carry a circular record. HE's model takes a
logical merge at a second place: the candidate of primitive `unify` (`UnifyCandidateRel`), which the
rule for `unify` uses for the bindings of its result frame. So a `unify` (and `let`, which reduces to
it) executed at a frame that records `t = t1` may return the same circular record, and a later cast
of a declared value against `$t` fails there. HE's interpreter answers `(if True (let $x 1 $x) 2)`
with `[1]`.

* `pattern_match`: `(P 1 2)` matches `(P $then1 $else1)` by `{then1 := 1, else1 := 2}`.
* `unify_cycle_admitted`: at the record `{t = t1}`, the circular record
  `{t := $t1, t1 := $t, then1 := 1, else1 := 2}` is a candidate of that `unify`.
* `unify_cycle_cast_error`: at that candidate the cast of the declared `1` against `$t` publishes a
  `BadType` error, under either matching policy.
* `unify_syntactic_admitted`, `unify_syntactic_cast` (positive controls): the syntactic merge is a
  candidate too, and there the cast keeps `1`.

So the change proposed in `DeclaredBranchVariant` for the row hit is needed at the rule for `unify`
as well: the result frame's bindings as the syntactic merge of the match into the frame's bindings.
The candidate relation itself also carries the records of typed renewals, which the type match
merges in the other order (`Frame.TypeRenewRel.of_modelled_match`); the restriction therefore
belongs in the rule, not in the relation.

* `candidate_syntactic`, `unify_step_syntactic`: the rule with the syntactic record fires wherever
  the model's rule fires (every candidate has the syntactic candidate of the same match beside it,
  with a result frame), and each such step is a step of the model's rule.

The variant machine of `SyntacticMerge` does not restrict this step; no every-run statement of this
development about the variant machine passes through a `unify` after a declared `if`.

## Controls

* `Controls.cycle_is_not_syntactic` (negative): the circular candidate is not the syntactic merge.
* `Controls.no_candidate_on_clash` (negative): `(P 1 2)` against `(Q $then1 $else1)` has no match, so
  no candidate of either kind.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace UnifyCandidateGap

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (UnifyCandidateRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs MatchRel MatchListAccRel MergeRel
  MergeConstraintsRel AddVarBindingRel equalityGroundedSemantic SemanticLoopFree ClassDepends
  semanticLoopFree_empty semanticLoopFree_single_assignment)
open DeclaredBranchGap (rowMatch callFrame cycleFrame syntacticFrame)
open AnswerBags.Controls (sym app)

/-- `1` and `2`. -/
abbrev one : Atom := .grounded (.int 1)
abbrev two : Atom := .grounded (.int 2)

/-- `(P 1 2)` and `(P $then1 $else1)`. -/
abbrev target : Atom := app "P" [one, two]
abbrev pattern : Atom := app "P" [.var "then1", .var "else1"]

theorem rowMatch_eq : (Bindings.empty.assign "then1" one).assign "else1" two = rowMatch := by
  decide

/-- The row's match has no dependency between names: both values are numbers. -/
theorem rowMatch_loopFree : SemanticLoopFree rowMatch := by
  have noStep : ∀ source goal, ¬ ClassDepends rowMatch source goal := by
    rintro source goal ⟨key, value, dependency, member, _, occurs, _⟩
    simp only [rowMatch, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> cases occurs
  have noPath : ∀ source goal, ¬ Relation.TransGen (ClassDepends rowMatch) source goal := by
    intro source goal reach
    induction reach with
    | single step => exact noStep _ _ step
    | tail _ step _ => exact noStep _ _ step
  intro name
  exact noPath name name

/-- Two symbols match only when they are the same symbol. -/
theorem symbols_equal {a b : String} {m : Bindings}
    (matched : MatchRel equalityGroundedSemantic (.symbol a) (.symbol b) m) : a = b := by
  cases matched with
  | symSym => rfl

theorem pattern_match_raw : MatchRel equalityGroundedSemantic target pattern
    ((Bindings.empty.assign "then1" one).assign "else1" two) :=
  .expression
    (.cons (.symSym "P" semanticLoopFree_empty)
      (MergeRel.mk (order := []) (List.Perm.refl _) .nil)
      (.cons (.nonVarVar rfl (semanticLoopFree_single_assignment (by intro occurs; cases occurs)))
        (MergeRel.mk (order := [.value "then1" one]) (List.Perm.refl _)
          (.value (.fresh (by decide)) .nil))
        (.cons (.nonVarVar rfl (semanticLoopFree_single_assignment (by intro occurs; cases occurs)))
          (MergeRel.mk (order := [.value "else1" two]) (List.Perm.refl _)
            (.value (.fresh (by decide)) .nil))
          .nil)))
    (by rw [rowMatch_eq]; exact rowMatch_loopFree)

/-- **`(P 1 2)` matches `(P $then1 $else1)` by `{then1 := 1, else1 := 2}`.** -/
theorem pattern_match : MatchRel equalityGroundedSemantic target pattern rowMatch := by
  rw [← rowMatch_eq]
  exact pattern_match_raw

/-- **`unify` may present `t = t1` as a cycle**: at the record `{t = t1}`, the circular record is a
candidate of the `unify` of `(P 1 2)` with `(P $then1 $else1)`. -/
theorem unify_cycle_admitted : UnifyCandidateRel target pattern callFrame cycleFrame :=
  ⟨rowMatch, pattern_match, DeclaredBranchGap.cycle_admitted⟩

/-- **At that candidate the cast of the declared `1` against `$t` publishes a `BadType` error**,
under either matching policy (`DeclaredBranchGap.cycle_cast_error`). -/
theorem unify_cycle_cast_error (policy : Policy) :
    Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeCastBatchRel
      (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram) one (.var "t") cycleFrame
      [(Mettapedia.Languages.MeTTa.HE.mkError one (.badType (.var "t") (sym "Number")), cycleFrame)]
      (lookup := Mettapedia.Languages.MeTTa.HE.Spec.Type.rawTypeLookupRel
        (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram))
      (matching := policy.matching.Rel) :=
  DeclaredBranchGap.cycle_cast_error policy

theorem syntactic_model : ∃ v : String → Atom,
    TypeBindingSatisfied v (SyntacticMerge.merge rowMatch callFrame) := by
  obtain ⟨v, sat⟩ := DeclaredBranchGap.cycle_admitted.2
  exact ⟨v, (DeclaredBranchGap.cycle_solutions v).mp sat⟩

/-- **Positive control**: the syntactic merge of the match into `{t = t1}` is a candidate too. -/
theorem unify_syntactic_admitted :
    UnifyCandidateRel target pattern callFrame (SyntacticMerge.merge rowMatch callFrame) :=
  ⟨rowMatch, pattern_match, SyntacticMerge.merge_logical syntactic_model⟩

/-- **Positive control**: at the syntactic candidate the cast of `1` against `$t` keeps `1`. -/
theorem unify_syntactic_cast : ∃ out,
    Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeCastBatchRel
      (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram) one (.var "t")
      (SyntacticMerge.merge rowMatch callFrame) [(one, out)]
      (lookup := Mettapedia.Languages.MeTTa.HE.Spec.Type.rawTypeLookupRel
        (Mettapedia.Languages.MeTTa.HE.Space.ofList IfEveryRun.ifProgram)) :=
  DeclaredBranchGap.syntactic_cast_succeeds

/-! ## The rule for `unify` with the syntactic record -/

section Rule

open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open ServiceFootprints EntryToQuery AnswerBags EveryRun

/-- **Every candidate of `unify` has the syntactic candidate of the same match beside it.** -/
theorem candidate_syntactic {left right : Atom} {incoming output : Bindings}
    (candidate : UnifyCandidateRel left right incoming output) :
    ∃ matched, MatchRel equalityGroundedSemantic left right matched ∧
      UnifyCandidateRel left right incoming (SyntacticMerge.merge matched incoming) := by
  obtain ⟨matched, matching, merged⟩ := candidate
  obtain ⟨v, model⟩ := merged.2
  exact ⟨matched, matching, matched, matching,
    SyntacticMerge.merge_logical ⟨v, (merged.1.solutions v).mp model⟩⟩

/-- **The rule for `unify` with the syntactic record fires wherever the model's rule fires**: for
every candidate at a frame there is a result frame whose bindings are the syntactic merge of a match
into the frame's bindings, and HE's step to it. Every such step is a step of the model's rule. -/
theorem unify_step_syntactic {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}
    {space : Space} {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Entry.Status} {left right yes no : Entry.Value} {activation : Frame}
    {stack : List Continuation} {emitted : List Result} {output : Bindings}
    (candidate : UnifyCandidateRel left.erase right.erase activation.bindings output) :
    ∃ (matched : Bindings) (frame : Frame),
      MatchRel equalityGroundedSemantic left.erase right.erase matched ∧
      frame.bindings = SyntacticMerge.merge matched activation.bindings ∧
      HEStep dispatch lookup policy
        ⟨space, .work (.minimal live scope caller
          (.expression readiness [.symbol "unify", left, right, yes, no]) activation), stack,
          emitted⟩
        ⟨space, .returning [(frame.read policy yes, frame)], stack, emitted⟩ := by
  obtain ⟨matched, matching, syntactic⟩ := candidate_syntactic candidate
  obtain ⟨after, unified, certificate⟩ := Entry.Value.UnifyRel.of_source_candidate
    (policy := policy.rebuilding) activation.certified syntactic
  exact ⟨matched, ⟨_, after, certificate⟩, matching, rfl,
    .internal (.minimalUnifyYes (output := ⟨_, after, certificate⟩) syntactic unified)⟩

end Rule

namespace Controls

/-- **Negative control**: the circular candidate is not the syntactic merge. -/
theorem cycle_is_not_syntactic : cycleFrame ≠ SyntacticMerge.merge rowMatch callFrame :=
  SyntacticMerge.Controls.cycle_not_variant

/-- **Negative control**: against a pattern with another head there is no match, so no candidate of
either kind. -/
theorem no_candidate_on_clash (incoming output : Bindings) :
    ¬ UnifyCandidateRel target (app "Q" [.var "then1", .var "else1"]) incoming output := by
  rintro ⟨matched, matching, _⟩
  cases matching with
  | expression items _ =>
      cases items with
      | cons head _ _ => exact absurd (symbols_equal head) (by decide)

end Controls

#print axioms pattern_match
#print axioms unify_cycle_admitted
#print axioms unify_cycle_cast_error
#print axioms unify_syntactic_admitted
#print axioms unify_syntactic_cast
#print axioms candidate_syntactic
#print axioms unify_step_syntactic
#print axioms Controls.cycle_is_not_syntactic
#print axioms Controls.no_candidate_on_clash

end UnifyCandidateGap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
