import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PublicInvariant

/-!
# Actual public source answers are exactly reached done payloads

The forward construction transports an existing binder execution under the
public continuation, returns the reached reply and performs the fresh pattern
bind and final return. Reflection follows every branch of the actual public
source execution. It does not select only successful internal search paths.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicAnswers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open PublicQuery (rows keys result site query frame)

local instance msigClosed : ProgramBinders.ClosedTerms MSig where
  closed := fun | () => csym "unused"

variable (helpers authored : List ProgramLayout.Rule) (D : Discipline MSig [] ()) (supply : Nat → MClosed)
  (separated : HeadSeparated (rows helpers authored) activeTag doneTag)

include separated

theorem public_answer_of_reached {call value : MClosed}
    (initialHead : closedHead call = some activeTag ∨ closedHead call = some doneTag)
    (rewritten : PublicInvariant.Reach helpers authored call (doneC value)) :
    ∃ after, Runs D (BinderCore.program (rows helpers authored)) supply
      (Config.initial (fun _ => 0) (query helpers authored call)) after ∧
      HasAnswer (D := D) (rows helpers authored) after value := by
  obtain ⟨configuration, path, before, member, term, focus, frames, pending, fresh, read⟩ :=
    BinderCore.runs_forward (rows helpers authored) D supply rewritten
  have head := heads_runs (rows helpers authored) separated supply initialHead path before member
  rw [focus] at head
  change literalHead term = some activeTag ∨ literalHead term = some doneTag at head
  have doneHead : literalHead term = some doneTag := by
    rcases head with activeHead | doneHead
    · have wrong := literalHead_of_reads activeHead read
      have impossible : activeTag = doneTag := Option.some.inj wrong.symm
      exact (active_done_distinct impossible).elim
    · exact doneHead
  have live : Solvable before.store := by
    obtain ⟨X, family, assignment, solved, _⟩ := read
    exact ⟨X, family, assignment, solved⟩
  obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
  rcases configuration with ⟨world, all⟩
  rcases before with ⟨store, oldFocus, oldFrames, oldPending⟩
  simp only at focus frames pending fresh read split live doneHead
  subst oldFocus oldFrames oldPending
  let framedRest := rest.map (ContinuationLift.branch (frame helpers authored (Ty := D.Ty)))
  let replied : Branch (keys helpers authored) [] () D.Ty :=
    ⟨store, .value term, [frame helpers authored], []⟩
  have beforeSplit :
      (ContinuationLift.configuration (frame helpers authored (Ty := D.Ty))
        (⟨world, all⟩ : Config (keys helpers authored) [] () D.Ty)).branches =
      (⟨store, .eval (.apply term), [frame helpers authored], []⟩ :
        Branch (keys helpers authored) [] () D.Ty) ::ₘ framedRest := by
    simp only [ContinuationLift.configuration, split, Multiset.map_cons, ContinuationLift.branch,
      List.nil_append, framedRest]
  have replyStep : SourceLanguage.Step D (BinderCore.program (rows helpers authored)) supply
      (ContinuationLift.configuration (frame helpers authored) (⟨world, all⟩ : Config (keys helpers authored) [] () D.Ty))
      ⟨world, replied ::ₘ framedRest⟩ := by
    exact SourceLanguage.Step.of_eq beforeSplit rfl live
      (.unmatched world store term [frame helpers authored] []
        (none_at_done (D := D) (rows helpers authored) separated doneHead))
  let opened := openAt (keys helpers authored) (site helpers authored) world.scope
  let output := instantiate opened (result helpers authored)
  let finalStore := store ++ [(instantiate opened (PublicReadout.pattern (result helpers authored)), term)]
  have resultRead : Reads finalStore output value := PublicQuery.bind_has_result helpers authored fresh read
  have boundLive : Solvable finalStore := by
    obtain ⟨X, family, assignment, solved, _⟩ := resultRead
    exact ⟨X, family, assignment, solved⟩
  let returning : Branch (keys helpers authored) [] () D.Ty := ⟨finalStore, .eval (.ret output), [], []⟩
  let finished : Branch (keys helpers authored) [] () D.Ty := ⟨finalStore, .value output, [], []⟩
  have bindStep : SourceLanguage.Step D (BinderCore.program (rows helpers authored)) supply
      ⟨world, replied ::ₘ framedRest⟩ ⟨world.fresh, returning ::ₘ framedRest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl live
      (.letBind world store term (site helpers authored)
        (PublicReadout.pattern (result helpers authored)) (.ret (result helpers authored)) [] [])
  have returnStep : SourceLanguage.Step D (BinderCore.program (rows helpers authored)) supply
      ⟨world.fresh, returning ::ₘ framedRest⟩ ⟨world.fresh, finished ::ₘ framedRest⟩ :=
    SourceLanguage.Step.of_eq rfl rfl boundLive (.ret world.fresh finalStore output [] [])
  exact ⟨⟨world.fresh, finished ::ₘ framedRest⟩,
    (((PublicQuery.runs_inside helpers authored D supply path).tail replyStep).tail bindStep).tail returnStep,
    finished, Multiset.mem_cons_self _ _, ⟨rfl, output, rfl⟩, output, rfl, resultRead⟩

/-- The observation is the actual public result set, rather than a filter
applied to arbitrary internal helper answers after execution. -/
theorem public_answers_iff (call value : MClosed)
    (initialHead : closedHead call = some activeTag ∨ closedHead call = some doneTag) :
    PublicInvariant.Reach helpers authored call (doneC value) ↔
      ∃ after, Runs D (BinderCore.program (rows helpers authored)) supply
        (Config.initial (fun _ => 0) (query helpers authored call)) after ∧
        HasAnswer (D := D) (rows helpers authored) after value := by
  constructor
  · exact public_answer_of_reached helpers authored D supply separated initialHead
  · rintro ⟨after, executed, answered⟩
    exact PublicInvariant.public_answer_reflected helpers authored D supply executed answered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicAnswers

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.PublicAnswers.public_answers_iff
