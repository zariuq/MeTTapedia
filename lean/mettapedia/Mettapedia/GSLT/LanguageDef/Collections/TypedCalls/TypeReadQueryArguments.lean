import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMatcher

/-!
# Adaptive argument-type inference under extended private coordinates

The actual argument plan is related continuation by continuation. Its
metatype cut and first-local successful unifier are retained. This models
inference applicability; it does not replace a source call's separate
argument-evaluation demand with the substituted formal.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryArguments

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines.ReadOnlyQueryWorldRelation (Related)
open TypeReadQueryWorlds TypeReadQueryMatcher
open RetainedTypePayloads (ExternalView)

theorem argsPlan (external : ExternalView) (firstNormalize secondNormalize : Atom → Atom)
    (firstSubtypes secondSubtypes : List Atom → List Atom) (formals : List Atom) :
    ∀ (world : Coordinates) (otherFormals values : List Atom)
      (firstState secondState : TypeScopeMatcher.State),
      TypesRelated world formals otherFormals → Fixed world (atomListVariables values) →
      BindingRelated world firstState secondState →
      Related viewWorlds BindingAnswers world
        (NativeTypeDemand.argsPlan (TypeScopeMatcher.ops external firstNormalize firstSubtypes)
          formals values firstState)
        (NativeTypeDemand.argsPlan (TypeScopeMatcher.ops external secondNormalize secondSubtypes)
          otherFormals values secondState) := by
  induction formals with
  | nil =>
      intro world otherFormals values firstState secondState forms _ states
      rw [forms.2.2]
      cases values with
      | nil => exact .pure (.ok (.some states))
      | cons _ _ => exact .pure (.ok .none)
  | cons formal formals ih =>
      intro world otherFormals values firstState secondState forms fixed states
      have formalRelated := types_member forms (List.mem_cons_self : formal ∈ formal :: formals)
      have restRelated := types_tail forms
      rw [forms.2.2]
      cases values with
      | nil => exact .pure (.ok .none)
      | cons value values =>
          have valueFixed := fixed_head fixed
          have tailFixed := fixed_tail fixed
          simp only [List.map_cons, NativeTypeDemand.argsPlan]
          apply Related.read
          · exact ⟨rfl, valueFixed⟩
          · intro next grown firstReply secondReply replies
            cases replies with
            | types _ => exact .pure .error
            | class_ _ => exact .pure .error
            | kind kind =>
                have nextStates := binding_mono grown states
                have nextFormal := atom_mono grown formalRelated
                have expected := apply_related nextStates nextFormal
                have sameMeta := metaCheck_related expected kind
                simp only [TypeScopeMatcher.ops]
                rw [sameMeta]
                cases metatype : TypeScopeMatcher.metaCheckAtom (substA firstState formal) kind with
                | some answer =>
                    cases answer with
                    | false => exact .pure (.ok .none)
                    | true =>
                        exact ih next _ values firstState secondState
                          (types_mono grown restRelated) (fixed_mono grown tailFixed) nextStates
                | none =>
                    apply Related.read
                    · exact ⟨rfl, fixed_mono grown valueFixed⟩
                    · intro last extended firstActual secondActual actualReplies
                      cases actualReplies with
                      | class_ _ | kind _ => exact .pure .error
                      | types actuals =>
                          rename_i firstTypes secondTypes
                          have allGrowth := grows_trans grown extended
                          have lastStates := binding_mono allGrowth states
                          have lastExpected := apply_related lastStates (atom_mono allGrowth formalRelated)
                          have selected := firstChoice_related external last firstState secondState lastStates
                            _ _ lastExpected _ _ actuals
                          dsimp only
                          cases firstChosen : StampInference.firstResult
                              (fun actual => TypeScopeMatcher.unify external firstState actual
                                (substA firstState formal)) firstTypes with
                          | none =>
                              cases secondChosen : StampInference.firstResult
                                  (fun actual => TypeScopeMatcher.unify external secondState actual
                                    (substA secondState (renameAtom world.names formal))) secondTypes with
                              | none => exact .pure (.ok .none)
                              | some result =>
                                  simp only [firstChosen, secondChosen, Option.not_rel_none_some] at selected
                          | some firstSelected =>
                              cases secondChosen : StampInference.firstResult
                                  (fun actual => TypeScopeMatcher.unify external secondState actual
                                    (substA secondState (renameAtom world.names formal))) secondTypes with
                              | none =>
                                  simp only [firstChosen, secondChosen, Option.not_rel_some_none] at selected
                              | some secondSelected =>
                                  have selection : BindingRelated last firstSelected secondSelected := by
                                    simpa only [firstChosen, secondChosen, Option.rel_some_some] using selected
                                  exact ih last _ values firstSelected secondSelected (types_mono allGrowth restRelated)
                                    (fixed_mono allGrowth tailFixed) selection

/-- Lifting changes inquiry labels only; it does not execute or duplicate a
recursive child query. -/
theorem liftViews {Answer : Type} (answers : Coordinates → Answer → Answer → Prop)
    {world : Coordinates} {first second : Mettapedia.Machines.ReadOnlyQuery.Program
      (NativeTypeDemand.Question Atom) NativeTypeCallGraph.Reply Answer}
    (related : Related viewWorlds answers world first second) :
    Related worlds answers world (NativeTypeCallGraph.liftViews first) (NativeTypeCallGraph.liftViews second) := by
  induction related with
  | pure good => exact .pure good
  | read keys children ih => exact .read keys ih

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryArguments
