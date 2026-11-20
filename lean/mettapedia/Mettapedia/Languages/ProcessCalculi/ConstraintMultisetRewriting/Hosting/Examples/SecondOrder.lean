import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ExampleChoice

/-!
# The step's own knowledge solves the second-order unknown: a body with its binder

At the start of the query `(app (lam x. (s x)) zero)` over the program
`(= (app (lam x. $F x) $a) ($F $a))`, the canonical firing of the equation's schema is admitted
(`admitted`), and **every** solution of its information, in every frame, sends the opened `$F` to the
body `(s x)` with the bound variable (`step_solves_F`), never to a term that ignores it
(`not_constant`), and the opened `$a` to `zero`. The second-order work is done by the step's knowledge
(syntactic equality at the contextual frames), not by a matcher outside it.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.SecondOrder

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open SourceLanguage.ExampleBeta (betaEq program call1 lamD)
open Hosting

abbrev N := mettaNodes

/-- The query `(app (lam x. (s x)) zero)`. -/
def betaQ : Comp mkeys [] () MTy := .apply call1

theorem betaQ_unopened : ∀ t ∈ betaQ.data, ∀ x ∈ support t, x.scopes = [] := by
  intro t member x inside
  simp only [betaQ, Comp.data, List.mem_singleton] at member
  subst member
  simp [call1, tuple, tupleArgs, sym, lamD, lamAt, tupleAt, tupleArgsAt, symAt, bv, support, supportArgs] at inside

abbrev s1 : HostState MSig := Hosting.start N program betaQ

abbrev f1 : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations MSig) (translate N program) s1.frame :=
  canonicalAt s1 (schema N betaEq) (schema_mem N program (List.mem_singleton_self _)) program.equations.length

/-- **The firing is admitted**: its information has a solution. -/
theorem admitted : f1.Admits (Interface.Frames.contextual MSig) s1 :=
  (schema_admitted_iff N (start_represents N program betaQ betaQ_unopened) (List.mem_singleton_self _)).mpr
    ExampleChoice.live0

/-- **Every solution of the step's information reads `$F` as the body `(s x)`, with its binder, and `$a`
as `zero`.** -/
theorem step_solves_F {B : Interface.Frames.Frame MSig}
    (u : Assignment ((RuleSyntax.Contextual.declarations MSig).target f1.ext).arity B.arity)
    (solved : (Interface.Frames.contextual MSig).Models u (f1.information (Interface.Frames.contextual MSig) s1)) :
    instantiate u (f1.opening (.inl (ho [] [100] 0))) = tupleAt [symAt "s", bv] ∧
      instantiate u (f1.opening (.inl (fo [] [100] 1))) = symAt "zero" := by
  have rep := start_represents N program betaQ betaQ_unopened
  have simple := canonical_simple (s := s1) (r := schema N betaEq)
    (member := schema_mem N program (List.mem_singleton_self _)) (a := program.equations.length)
    (pat := observe (altN N (evalN N (applyN N (instantiate asUnknowns betaEq.lhs))) schemaStack))
    (out := observe (altN N (evalN N (encComp N (instantiate asUnknowns) betaEq.rhs)) schemaStack)) rfl rfl rfl
  obtain ⟨known, _, matched⟩ := simple_restrict simple u solved
  have reads := (rep.reads B _).mp ⟨_, known, matched.symm⟩
  change branchReads N _ B (observe (instantiate _ _)) at reads
  rw [instantiate_altN, instantiate_evalN, instantiate_applyN, instantiate_asUnknowns] at reads
  obtain ⟨t, σ, focus, _, onCall⟩ := shape_apply N reads
  simp only [initialBranch, betaQ, Focus.eval.injEq, Comp.apply.injEq] at focus
  subst focus
  have rhs : instantiate (fun y => Assignment.compose u f1.opening (.inl y)) betaEq.lhs =
      tupleAt [symAt "app", lamAt (instantiate u (f1.opening (.inl (ho [] [100] 0)))),
        instantiate u (f1.opening (.inl (fo [] [100] 1)))] := by
    show tupleAt [symAt "app", lamAt (instantiate (fun y => Assignment.compose u f1.opening (.inl y))
        (hoD [] [100] 0 bv)), instantiate (fun y => Assignment.compose u f1.opening (.inl y)) (foD [] [100] 1)] = _
    rw [instantiate_hoD_bv, instantiate_foD]
  have lhs : instantiate σ call1 = tupleAt [symAt "app", lamAt (tupleAt [symAt "s", bv]), symAt "zero"] := rfl
  obtain ⟨_, onF, onA⟩ := tuple3_inj (lhs.symm.trans (onCall.trans rhs))
  exact ⟨(lamAt_inj onF).symm, onA.symm⟩

/-- **Not a term that happens to work**: no solution reads `$F` as a body that ignores its binder. -/
theorem not_constant {B : Interface.Frames.Frame MSig}
    (u : Assignment ((RuleSyntax.Contextual.declarations MSig).target f1.ext).arity B.arity)
    (solved : (Interface.Frames.contextual MSig).Models u (f1.information (Interface.Frames.contextual MSig) s1)) :
    instantiate u (f1.opening (.inl (ho [] [100] 0))) ≠ tupleAt [symAt "s", symAt "zero"] := by
  rw [(step_solves_F u solved).1]
  intro same
  obtain ⟨_, rest⟩ := Args.cons.inj (op_inj same)
  obtain ⟨body, _⟩ := Args.cons.inj rest
  cases body

#print axioms admitted
#print axioms step_solves_F
#print axioms not_constant

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Examples.SecondOrder
