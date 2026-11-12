import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemo
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedSaturation

/-!
# Recursive retained-reply memoization agrees with fresh source reads

The operational memoizer performs every miss through the existing adaptive
inference body. Children may hit or miss independently. Cache validity is
preserved by those executions, not supplied as a postcondition of each child.
A historical completed read justifies a hit at every saturated recursion
depth and every private allocation history. Open replies are never reused.

The comparison retains a single growing correspondence for caller-visible
names. It preserves ordered replies and missing observations, not identical
allocation counters, primitive read traces, or physical work budgets. The
authority stamp is fixed during the comparison; native invalidation and
address-key correspondence remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemoRefinement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypeCallGraph NativeTypeSourcePorts TypeReadQueryWorlds
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

abbrev MemoState := TypeReadQueryMemo.State

theorem fixed_empty (world : Coordinates) : Fixed world [] := by
  constructor <;> simp

theorem empty_protected (first second : Supply) :
    Protected (⟨Equiv.refl String, []⟩ : Coordinates) first second := by
  constructor <;> simp

/-- Historical evidence is transported by the actual source-coordinate and
structural saturation theorems. It is not a supplied cache-answer oracle. -/
theorem recorded_at (source : Source) (external : ExternalView)
    (safe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (normalize : Atom → Atom)
    (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (completionDepth : Call → Nat)
    (saturated : ∀ call, NativeTypeCallRank.rank call < completionDepth call)
    (call : Call) (types : List Atom)
    (recorded : TypeReadQueryMemo.Recorded (TypeScopeMatcher.currentOps external normalize subtypes)
      source external completionDepth call types)
    (depth : Nat) (enough : NativeTypeCallRank.rank call < depth) (supply : Supply) :
    (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
      source external depth call supply).1 = some (.types types) := by
  obtain ⟨historical, returned⟩ := recorded.history
  have fixed : Fixed (⟨Equiv.refl String, []⟩ : Coordinates) (questionNames (.inr call)) := by
    rw [TypeReadQueryMemo.eligible_names call recorded.key]
    exact fixed_empty _
  have same := TypeReadQueryRecursive.retained_evaluate_equal source external safe alpha
    normalize normalize normalizer subtypes subtypes (completionDepth call)
    ⟨Equiv.refl String, []⟩ call historical supply fixed (empty_protected _ _)
    types returned recorded.retained
  rw [NativeTypeScopedSaturation.evaluate_eq_of_rank _ source external call depth
    (completionDepth call) enough (saturated call) supply]
  exact same

def States (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (completionDepth : Call → Nat)
    (authority : Nat) (world : Coordinates) (first : Supply) (second : MemoState) : Prop :=
  Protected world first second.supply ∧
    TypeReadQueryMemo.Valid ops source external completionDepth authority second.cache

/-- A right-hand retained family determines its related left family literally. -/
theorem completed_right_retained {world : Coordinates} {first second : Option Reply}
    (related : Option.Rel (RepliesRelated world) first second)
    (types : List Atom) (returned : second = some (.types types))
    (retained : RetainedTypePayloads.admittedList types = true) : first = some (.types types) := by
  rw [returned] at related
  cases found : first with
  | none => simp only [found, Option.not_rel_none_some] at related
  | some reply =>
      simp only [found, Option.rel_some_some] at related
      cases related with
      | types typesRelated =>
          rw [TypeReadQueryMemo.retained_right_equal typesRelated retained]

/-- Complete recursive source/memo correspondence, with arbitrary admitted hit
patterns and a preserved historical-evidence cache invariant. -/
theorem evaluate_related (source : Source) (external : ExternalView)
    (safe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (normalize : Atom → Atom)
    (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (completionDepth : Call → Nat)
    (saturated : ∀ call, NativeTypeCallRank.rank call < completionDepth call)
    (authority : Nat) (allow : Call → Bool) :
    ∀ (call : Call) (firstDepth secondDepth : Nat),
      NativeTypeCallRank.rank call < firstDepth → NativeTypeCallRank.rank call < secondDepth →
      ∀ (world : Coordinates) (first : Supply) (second : MemoState),
        Fixed world (questionNames (.inr call)) →
        States (TypeScopeMatcher.currentOps external normalize subtypes)
          source external completionDepth authority world first second →
        ∃ after, Grows world after ∧
          States (TypeScopeMatcher.currentOps external normalize subtypes)
            source external completionDepth authority after
            (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
              source external firstDepth call first).2
            (TypeReadQueryMemo.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
              source external authority allow secondDepth call second).2 ∧
          Option.Rel (RepliesRelated after)
            (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
              source external firstDepth call first).1
            (TypeReadQueryMemo.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
              source external authority allow secondDepth call second).1 := by
  let ops := TypeScopeMatcher.currentOps external normalize subtypes
  intro call
  induction call using (measure NativeTypeCallRank.rank).wf.induction with
  | h call ih =>
      intro firstDepth secondDepth firstEnough secondEnough world first second fixed states
      cases firstDepth with
      | zero => omega
      | succ firstDepth =>
          cases secondDepth with
          | zero => omega
          | succ secondDepth =>
              cases cached : (if allow call && TypeReadQueryMemo.eligible call then
                  RevisionedQueryFacts.lookup authority call second.cache else none) with
              | some types =>
                  have found : RevisionedQueryFacts.lookup authority call second.cache = some types := by
                    split at cached
                    · exact cached
                    · cases cached
                  have recorded := TypeReadQueryMemo.lookup_recorded ops source external
                    completionDepth authority second.cache states.2 call types found
                  have returned := recorded_at source external safe alpha normalize normalizer subtypes
                    completionDepth saturated call types recorded (firstDepth + 1) firstEnough first
                  have keeps := NativeTypeScopedReads.evaluate_remembers ops source external
                    (firstDepth + 1) call first
                  refine ⟨world, grows_refl world, ?_, ?_⟩
                  · simpa only [TypeReadQueryMemo.evaluate, cached] using
                      (show States ops source external completionDepth authority world
                        (NativeTypeScopedReads.evaluate ops source external (firstDepth + 1) call first).2 second from
                        ⟨⟨fun _ member => keeps (states.1.1 member), states.1.2⟩, states.2⟩)
                  · simp only [TypeReadQueryMemo.evaluate, cached, returned]
                    exact .some (.types (TypeReadQueryMemo.retained_reflexive world types recorded.retained))
              | none =>
                  let firstService : Supply → Question → Option Reply × Supply := fun current => fun
                    | .inl key => NativeTypeScopedReads.primitive source external current key
                    | .inr child => NativeTypeScopedReads.evaluate ops source external firstDepth child current
                  let secondService : MemoState → Question → Option Reply × MemoState := fun current => fun
                    | .inl key =>
                        let result := NativeTypeScopedReads.primitive source external current.supply key
                        (result.1, { current with supply := result.2 })
                    | .inr child => TypeReadQueryMemo.evaluate ops source external authority allow secondDepth child current
                  let limited := ReadOnlyQueryWorldRelation.restrictKeys worlds
                    (NativeTypeCallRank.KeyBelow (NativeTypeCallRank.rank call))
                  have services : ReadOnlyQueryWorldRelation.ServicesRelated limited
                      (States ops source external completionDepth authority) firstService secondService := by
                    intro before left right kept firstKey secondKey keys
                    rcases keys with ⟨keys, bounded⟩
                    cases firstKey with
                    | inl primitive =>
                        cases secondKey with
                        | inr other =>
                            cases primitive with
                            | closure seeds => obtain ⟨_, impossible, _⟩ := keys; cases impossible
                            | annotations _ | intrinsic _ | kind _ | classify _ _ => cases keys.1
                        | inl other =>
                            obtain ⟨after, grown, supplies, replies⟩ :=
                              TypeReadQueryServices.primitive source external safe alpha
                                before left right.supply kept.1 primitive other keys
                            exact ⟨after, grown, ⟨supplies, kept.2⟩, replies⟩
                    | inr child =>
                        obtain ⟨same, childFixed⟩ := keys
                        subst secondKey
                        have smaller : NativeTypeCallRank.rank child < NativeTypeCallRank.rank call := bounded
                        exact ih child smaller firstDepth secondDepth (by omega) (by omega)
                          before left right childFixed kept
                  have bodyRelated := ReadOnlyQueryWorldRelation.restrict_related worlds
                    (NativeTypeCallRank.KeyBelow (NativeTypeCallRank.rank call))
                    TypeReadQueryCallGraph.ReplyAnswers
                    (TypeReadQueryCallGraph.body external normalize normalize normalizer subtypes subtypes
                      world call fixed)
                    (NativeTypeCallRank.body_keys_below ops call)
                  obtain ⟨after, grown, kept, answers, _reads⟩ :=
                    ReadOnlyQueryWorldRelation.demand_run_related limited TypeReadQueryCallGraph.ReplyAnswers
                      (States ops source external completionDepth authority) firstService secondService services
                      bodyRelated first second states
                  let firstRun := QueryState.run firstService (ReadOnlyQueryDemand.demand (body ops call)) first
                  let secondRun := QueryState.run secondService (ReadOnlyQueryDemand.demand (body ops call)) second
                  have completed : Option.Rel (RepliesRelated after)
                      (NativeTypeRecursiveDriver.completed firstRun.answer)
                      (NativeTypeRecursiveDriver.completed secondRun.answer) :=
                    TypeReadQueryRecursive.completed_related answers
                  let finalSupply := NativeTypeScopedReads.retain secondRun.state.supply
                    (NativeTypeRecursiveDriver.completed secondRun.answer)
                  let retainedState : MemoState := ⟨finalSupply, secondRun.state.cache⟩
                  have valid := TypeReadQueryMemo.publish_valid ops source external completionDepth
                    authority allow call (NativeTypeRecursiveDriver.completed secondRun.answer)
                    retainedState
                    kept.2 (by
                      intro types returned retained
                      have sourceReturned := completed_right_retained completed types returned retained
                      refine ⟨first, ?_⟩
                      rw [NativeTypeScopedSaturation.evaluate_eq_of_rank ops source external call
                        (completionDepth call) (firstDepth + 1) (saturated call) firstEnough first]
                      exact sourceReturned)
                  refine ⟨after, grown, ?_, ?_⟩
                  · change States ops source external completionDepth authority after
                      (NativeTypeScopedReads.evaluate ops source external (firstDepth + 1) call first).2
                      (TypeReadQueryMemo.evaluate ops source external authority allow (secondDepth + 1) call second).2
                    rw [TypeReadQueryMemo.evaluate, cached]
                    dsimp only [TypeReadQueryMemo.finish]
                    refine ⟨?_, valid⟩
                    rw [TypeReadQueryMemo.publish_supply]
                    exact TypeReadQueryRecursive.retain_protected kept.1
                      (NativeTypeRecursiveDriver.completed firstRun.answer)
                      (NativeTypeRecursiveDriver.completed secondRun.answer)
                  · change Option.Rel (RepliesRelated after)
                      (NativeTypeScopedReads.evaluate ops source external (firstDepth + 1) call first).1
                      (TypeReadQueryMemo.evaluate ops source external authority allow (secondDepth + 1) call second).1
                    rw [TypeReadQueryMemo.evaluate, cached]
                    exact completed

/-! ## Literal retained answers and derived completion evidence -/

/-- A structural depth witness is proof metadata, not part of an operational
cache key and not a replacement for the subtype service's own budget. -/
noncomputable def completionDepth (call : Call) : Nat := NativeTypeCallRank.rank call + 1

theorem completion_saturated (call : Call) : NativeTypeCallRank.rank call < completionDepth call := by
  simp [completionDepth]

theorem empty_valid (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (authority : Nat) :
    TypeReadQueryMemo.Valid ops source external completionDepth authority [] := by
  intro entry member
  cases member

/-- The coordinate relation collapses to literal ordered equality precisely
for a retained immutable answer family. Duplicate occurrences are retained. -/
theorem retained_evaluate_equal (source : Source) (external : ExternalView)
    (safe : NativeTypeSourcePorts.Safe source)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant source.alpha)
    (normalize : Atom → Atom)
    (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (authority : Nat) (allow : Call → Bool)
    (call : Call) (firstDepth secondDepth : Nat)
    (firstEnough : NativeTypeCallRank.rank call < firstDepth)
    (secondEnough : NativeTypeCallRank.rank call < secondDepth)
    (world : Coordinates) (first : Supply) (second : MemoState)
    (fixed : Fixed world (questionNames (.inr call)))
    (states : States (TypeScopeMatcher.currentOps external normalize subtypes)
      source external completionDepth authority world first second)
    (types : List Atom)
    (returned : (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
      source external firstDepth call first).1 = some (.types types))
    (retained : RetainedTypePayloads.admittedList types = true) :
    (TypeReadQueryMemo.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
      source external authority allow secondDepth call second).1 = some (.types types) := by
  obtain ⟨after, _, _, related⟩ := evaluate_related source external safe alpha normalize normalizer subtypes
    completionDepth completion_saturated authority allow call firstDepth secondDepth firstEnough secondEnough
    world first second fixed states
  rw [returned] at related
  cases found : (TypeReadQueryMemo.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
      source external authority allow secondDepth call second).1 with
  | none => simp only [found, Option.not_rel_some_none] at related
  | some reply =>
      simp only [found, Option.rel_some_some] at related
      cases related with
      | types typesRelated => rw [TypeReadQueryRecursive.retained_types_equal typesRelated retained]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemoRefinement
