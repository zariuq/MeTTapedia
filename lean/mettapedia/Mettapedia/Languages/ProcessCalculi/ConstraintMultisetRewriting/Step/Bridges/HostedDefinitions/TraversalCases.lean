import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextRules

/-!
# Exhaustive field readback of the actual context traversal clauses

Cases classify the existing finite source equations. They are proof views of
actual equation instances, with no separate source grammar or evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.TraversalCases

open SourceLanguage.Elaboration
open RuleBuilder

inductive Case : MClosed → MClosed → Prop
  | routeRoot (term context continuation : MClosed) : Case (seekC term context continuation) (rootC term (nodeC "hd-main-plug" [context, continuation]))
  | routePlug (term context continuation : MClosed) : Case (resumeC term (nodeC "hd-main-plug" [context, continuation])) (plugC term context continuation)
  | empty (term continuation : MClosed) : Case (plugC term emptyContext continuation) (resumeC term continuation)
  | piSeekLeft (a b context continuation : MClosed) : Case (seekC (nodeC "prime-tm-pi" [a, b]) context continuation) (seekC a (nodeC "hd-context-pi-domain" [b, context]) continuation)
  | piSeekRight (a b context continuation : MClosed) : Case (seekC (nodeC "prime-tm-pi" [a, b]) context continuation) (seekC b (nodeC "hd-context-pi-codomain" [a, context]) continuation)
  | piPlugLeft (a b context continuation : MClosed) : Case (plugC a (nodeC "hd-context-pi-domain" [b, context]) continuation) (plugC (nodeC "prime-tm-pi" [a, b]) context continuation)
  | piPlugRight (b a context continuation : MClosed) : Case (plugC b (nodeC "hd-context-pi-codomain" [a, context]) continuation) (plugC (nodeC "prime-tm-pi" [a, b]) context continuation)
  | sigmaSeekLeft (a b context continuation : MClosed) : Case (seekC (nodeC "prime-tm-sigma" [a, b]) context continuation) (seekC a (nodeC "hd-context-sigma-domain" [b, context]) continuation)
  | sigmaSeekRight (a b context continuation : MClosed) : Case (seekC (nodeC "prime-tm-sigma" [a, b]) context continuation) (seekC b (nodeC "hd-context-sigma-codomain" [a, context]) continuation)
  | sigmaPlugLeft (a b context continuation : MClosed) : Case (plugC a (nodeC "hd-context-sigma-domain" [b, context]) continuation) (plugC (nodeC "prime-tm-sigma" [a, b]) context continuation)
  | sigmaPlugRight (b a context continuation : MClosed) : Case (plugC b (nodeC "hd-context-sigma-codomain" [a, context]) continuation) (plugC (nodeC "prime-tm-sigma" [a, b]) context continuation)
  | idSeekType (carrier left right context continuation : MClosed) : Case (seekC (nodeC "prime-tm-id" [carrier, left, right]) context continuation) (seekC carrier (nodeC "hd-context-id-type" [left, right, context]) continuation)
  | idSeekLeft (carrier left right context continuation : MClosed) : Case (seekC (nodeC "prime-tm-id" [carrier, left, right]) context continuation) (seekC left (nodeC "hd-context-id-left" [carrier, right, context]) continuation)
  | idSeekRight (carrier left right context continuation : MClosed) : Case (seekC (nodeC "prime-tm-id" [carrier, left, right]) context continuation) (seekC right (nodeC "hd-context-id-right" [carrier, left, context]) continuation)
  | idPlugType (carrier left right context continuation : MClosed) : Case (plugC carrier (nodeC "hd-context-id-type" [left, right, context]) continuation) (plugC (nodeC "prime-tm-id" [carrier, left, right]) context continuation)
  | idPlugLeft (left carrier right context continuation : MClosed) : Case (plugC left (nodeC "hd-context-id-left" [carrier, right, context]) continuation) (plugC (nodeC "prime-tm-id" [carrier, left, right]) context continuation)
  | idPlugRight (right carrier left context continuation : MClosed) : Case (plugC right (nodeC "hd-context-id-right" [carrier, left, context]) continuation) (plugC (nodeC "prime-tm-id" [carrier, left, right]) context continuation)
  | lamSeek (term context continuation : MClosed) : Case (seekC (nodeC "prime-tm-lam" [term]) context continuation) (seekC term (nodeC "hd-context-lam" [context]) continuation)
  | lamPlug (term context continuation : MClosed) : Case (plugC term (nodeC "hd-context-lam" [context]) continuation) (plugC (nodeC "prime-tm-lam" [term]) context continuation)
  | appSeekLeft (a b context continuation : MClosed) : Case (seekC (nodeC "prime-tm-app" [a, b]) context continuation) (seekC a (nodeC "hd-context-app-function" [b, context]) continuation)
  | appSeekRight (a b context continuation : MClosed) : Case (seekC (nodeC "prime-tm-app" [a, b]) context continuation) (seekC b (nodeC "hd-context-app-argument" [a, context]) continuation)
  | appPlugLeft (a b context continuation : MClosed) : Case (plugC a (nodeC "hd-context-app-function" [b, context]) continuation) (plugC (nodeC "prime-tm-app" [a, b]) context continuation)
  | appPlugRight (b a context continuation : MClosed) : Case (plugC b (nodeC "hd-context-app-argument" [a, context]) continuation) (plugC (nodeC "prime-tm-app" [a, b]) context continuation)
  | pairSeekLeft (a b context continuation : MClosed) : Case (seekC (nodeC "prime-tm-pair" [a, b]) context continuation) (seekC a (nodeC "hd-context-pair-first" [b, context]) continuation)
  | pairSeekRight (a b context continuation : MClosed) : Case (seekC (nodeC "prime-tm-pair" [a, b]) context continuation) (seekC b (nodeC "hd-context-pair-second" [a, context]) continuation)
  | pairPlugLeft (a b context continuation : MClosed) : Case (plugC a (nodeC "hd-context-pair-first" [b, context]) continuation) (plugC (nodeC "prime-tm-pair" [a, b]) context continuation)
  | pairPlugRight (b a context continuation : MClosed) : Case (plugC b (nodeC "hd-context-pair-second" [a, context]) continuation) (plugC (nodeC "prime-tm-pair" [a, b]) context continuation)
  | fstSeek (term context continuation : MClosed) : Case (seekC (nodeC "prime-tm-fst" [term]) context continuation) (seekC term (nodeC "hd-context-first" [context]) continuation)
  | fstPlug (term context continuation : MClosed) : Case (plugC term (nodeC "hd-context-first" [context]) continuation) (plugC (nodeC "prime-tm-fst" [term]) context continuation)
  | sndSeek (term context continuation : MClosed) : Case (seekC (nodeC "prime-tm-snd" [term]) context continuation) (seekC term (nodeC "hd-context-second" [context]) continuation)
  | sndPlug (term context continuation : MClosed) : Case (plugC term (nodeC "hd-context-second" [context]) continuation) (plugC (nodeC "prime-tm-snd" [term]) context continuation)
  | reflSeek (term context continuation : MClosed) : Case (seekC (nodeC "prime-tm-refl" [term]) context continuation) (seekC term (nodeC "hd-context-refl" [context]) continuation)
  | reflPlug (term context continuation : MClosed) : Case (plugC term (nodeC "hd-context-refl" [context]) continuation) (plugC (nodeC "prime-tm-refl" [term]) context continuation)

theorem of_step {before after : MClosed}
    (step : ProgramBinders.Rewrites ContextRules.traversal.get before after) : Case before after := by
  obtain ⟨index, answered⟩ := step
  fin_cases index
  all_goals obtain ⟨environment, lhs, rhs⟩ := (answers_iff _ _ before after).mp answered
  all_goals simp only [ContextRules.active, materialize_node, materialize_slot,
    List.map_cons, List.map_nil] at lhs rhs
  all_goals rw [← lhs, ← rhs]
  · exact .routeRoot (environment 0) (environment 1) (environment 2)
  · exact .routePlug (environment 0) (environment 1) (environment 2)
  · exact .empty (environment 0) (environment 1)
  · exact .piSeekLeft (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .piSeekRight (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .piPlugLeft (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .piPlugRight (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .sigmaSeekLeft (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .sigmaSeekRight (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .sigmaPlugLeft (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .sigmaPlugRight (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .idSeekType (environment 0) (environment 1) (environment 2) (environment 3) (environment 4)
  · exact .idSeekLeft (environment 0) (environment 1) (environment 2) (environment 3) (environment 4)
  · exact .idSeekRight (environment 0) (environment 1) (environment 2) (environment 3) (environment 4)
  · exact .idPlugType (environment 0) (environment 1) (environment 2) (environment 3) (environment 4)
  · exact .idPlugLeft (environment 0) (environment 1) (environment 2) (environment 3) (environment 4)
  · exact .idPlugRight (environment 0) (environment 1) (environment 2) (environment 3) (environment 4)
  · exact .lamSeek (environment 0) (environment 1) (environment 2)
  · exact .lamPlug (environment 0) (environment 1) (environment 2)
  · exact .appSeekLeft (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .appSeekRight (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .appPlugLeft (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .appPlugRight (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .pairSeekLeft (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .pairSeekRight (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .pairPlugLeft (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .pairPlugRight (environment 0) (environment 1) (environment 2) (environment 3)
  · exact .fstSeek (environment 0) (environment 1) (environment 2)
  · exact .fstPlug (environment 0) (environment 1) (environment 2)
  · exact .sndSeek (environment 0) (environment 1) (environment 2)
  · exact .sndPlug (environment 0) (environment 1) (environment 2)
  · exact .reflSeek (environment 0) (environment 1) (environment 2)
  · exact .reflPlug (environment 0) (environment 1) (environment 2)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.TraversalCases
