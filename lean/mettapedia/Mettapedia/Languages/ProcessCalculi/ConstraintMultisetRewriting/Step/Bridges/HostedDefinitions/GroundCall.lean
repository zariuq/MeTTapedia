import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.GroundRead

/-!
# A live selected equation preserves a determined ground call

The selected branch's real constraint store supplies a matching environment.
A checked dependency law then proves that every solution determines the same
right side. No inference from equality of closed readings to determination
is used, and no fresh-opening premise is invented for this backward law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundCall

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage SourceLanguage.Elaboration
open ProgramBinders

local instance closedTerms : ClosedTerms MSig where
  closed := fun | () => csym "closed-hole"

variable (rows : List (ProgramBinders.Equation MSig [] ()))

theorem selected_determines (index : Fin rows.length) (scope : Nat)
    (K : List (Constraint (BinderCore.keys rows) [] ()))
    (term : Data (BinderCore.keys rows) [] ()) (call : MClosed)
    (determined : Determines K term call) (grounding : GroundRead.Grounding (rows.get index))
    (live : Solvable (K ++ [(instantiate (BinderCore.stamp rows scope index) (rows.get index).lhs, term)])) :
    ∃ answer, ProgramBinders.Answers (rows.get index) call answer ∧
      Determines (K ++ [(instantiate (BinderCore.stamp rows scope index) (rows.get index).lhs, term)])
        (instantiate (BinderCore.stamp rows scope index) (rows.get index).rhs) answer := by
  let equation := rows.get index
  obtain ⟨X, target, model, solved⟩ := live
  obtain ⟨old, added⟩ := (models_append _ _ _).mp solved
  have matched := (models_singleton _ _).mp added
  dsimp only at matched
  let atRule : Assignment equation.arity target := fun hole => model ⟨[scope], ⟨index, hole⟩⟩
  have matchedAt : instantiate atRule equation.lhs = Rigid.includeTerm target call := by
    exact (BinderCore.instantiate_stamp rows model scope index equation.lhs).symm.trans
      (matched.trans (determined.2 target model old))
  let grounded : Assignment equation.arity (ground MSig) := Assignment.compose (close target) atRule
  let environment : equation.Ground := fun hole => decode (grounded hole)
  have restored : equation.assign environment (ground MSig) = grounded :=
    equation.ground_assignment grounded
  have matchedGround : instantiate (equation.assign environment (ground MSig)) equation.lhs =
      Rigid.includeTerm (ground MSig) call := by
    rw [restored, Assignment.instantiate_compose, matchedAt, Rigid.instantiate_include]
  let answer : MClosed := decode (instantiate (equation.assign environment (ground MSig)) equation.rhs)
  have answeredGround : instantiate (equation.assign environment (ground MSig)) equation.rhs =
      Rigid.includeTerm (ground MSig) answer := (include_decode _).symm
  refine ⟨answer, ⟨environment, matchedGround, answeredGround⟩, ⟨X, target, model, solved⟩, ?_⟩
  intro Y next candidate candidateSolved
  obtain ⟨before, new⟩ := (models_append _ _ _).mp candidateSolved
  have candidateMatch := (models_singleton _ _).mp new
  dsimp only at candidateMatch
  let candidateAt : Assignment equation.arity next := fun hole => candidate ⟨[scope], ⟨index, hole⟩⟩
  have leftGround : instantiate candidateAt equation.lhs = Rigid.includeTerm next call := by
    exact (BinderCore.instantiate_stamp rows candidate scope index equation.lhs).symm.trans
      (candidateMatch.trans (determined.2 next candidate before))
  have expectedLeft : instantiate (equation.assign environment next) equation.lhs =
      Rigid.includeTerm next call :=
    (equation.reads_in_frame environment equation.lhs call next).mp matchedGround
  have sameRight := grounding next candidateAt environment (leftGround.trans expectedLeft.symm)
  rw [BinderCore.instantiate_stamp]
  exact sameRight.trans ((equation.reads_in_frame environment equation.rhs answer next).mp answeredGround)

theorem live_callBranch_determines (D : Discipline MSig [] ())
    (index : Fin rows.length) (scope : Nat)
    (K : List (Constraint (BinderCore.keys rows) [] ()))
    (term : Data (BinderCore.keys rows) [] ()) (call : MClosed)
    (frames : List (Frame (BinderCore.keys rows) [] () D.Ty))
    (pending : List (Data (BinderCore.keys rows) [] () × Comp (BinderCore.keys rows) [] () D.Ty))
    (determined : Determines K term call) (grounding : GroundRead.Grounding (rows.get index))
    (live : Solvable (callBranch D scope K term frames pending (BinderCore.embedEquation rows index)).store) :
    ∃ answer datum,
      (callBranch D scope K term frames pending (BinderCore.embedEquation rows index)).focus = .eval (.apply datum) ∧
      ProgramBinders.Answers (rows.get index) call answer ∧
      Determines (callBranch D scope K term frames pending (BinderCore.embedEquation rows index)).store datum answer := by
  have storeEq :
      (callBranch D scope K term frames pending (BinderCore.embedEquation rows index)).store =
        K ++ [(instantiate (BinderCore.stamp rows scope index) (rows.get index).lhs, term)] := by
    simp only [callBranch, BinderCore.embedEquation, BinderCore.copy_embed]
  rw [storeEq] at live
  obtain ⟨answer, answered, output⟩ := selected_determines rows index scope K term call determined grounding live
  refine ⟨answer, instantiate (BinderCore.stamp rows scope index) (rows.get index).rhs, ?_, answered, ?_⟩
  · simp only [callBranch, BinderCore.embedEquation, Comp.inst, Comp.mapData, BinderCore.copy_embed]
  · rw [storeEq]
    exact output

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundCall

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.GroundCall.selected_determines
