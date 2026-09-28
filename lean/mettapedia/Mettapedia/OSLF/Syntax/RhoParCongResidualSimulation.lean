import Mettapedia.OSLF.Syntax.RhoQuoteSafeCommComparison

/-!
# Parallel congruence of a rho firing comparison

The authored parallel context is a hash bag with a distinguished selected
component and a rest collection. Intrinsic rho uses a binary parallel former.
The comparison below carries a child source congruence, an actual authored
child step, and a child target residual equivalence through this frame. It
also retains the intrinsic ParCong constructor and its recursive child tree.
It does not identify authored and intrinsic firing histories.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoParCongResidualSimulation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.IntrinsicEncoding
open Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial
open Mettapedia.OSLF.Binding.RhoRulePolynomialMorphism
open Mettapedia.OSLF.Binding.RhoAuthoredCommRuleCover
open Mettapedia.OSLF.Binding.RhoQuoteSafeCommComparison
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax

private abbrev raw := BindingCloneAlgebra.terms sig

/-- The authored ParCong rule acts on a selected child step. Its canonical
hash-bag endpoints retain the same rest component. -/
theorem authored_parallel_step {source target : Pattern}
    (rest : Pattern) (step : RhoStep source target) :
    RhoStep
      (.collection .hashBag [source, rest] none)
      (.collection .hashBag [target, rest] none) := by
  exact RhoStep.par [rest] step

/-- Structural comparison of child sources survives the selected-component
parallel frame, without quotienting the selected occurrence. -/
theorem parallel_source_congruence {intrinsic authored rest : Pattern}
    (comparison : StructuralCongruence intrinsic authored) :
    StructuralCongruence
      (.collection .hashBag [intrinsic, rest] none)
      (.collection .hashBag [authored, rest] none) := by
  refine StructuralCongruence.par_cong _ _ rfl ?_
  intro index leftBound rightBound
  cases index with
  | zero => simpa using comparison
  | succ index =>
      cases index with
      | zero => exact StructuralCongruence.refl rest
      | succ later =>
          simp at leftBound

/-- Residual comparison of child targets is compatible with the same
parallel frame. This remains weaker than structural congruence. -/
theorem parallel_target_residual {authored intrinsic rest : Pattern}
    (comparison : ProcResidualEquiv authored intrinsic) :
    ProcResidualEquiv
      (.collection .hashBag [authored, rest] none)
      (.collection .hashBag [intrinsic, rest] none) := by
  refine ProcResidualEquiv.collection_cong .hashBag
    [authored, rest] [intrinsic, rest] none rfl ?_
  intro index leftBound rightBound
  cases index with
  | zero => simpa using comparison
  | succ index =>
      cases index with
      | zero => exact ProcResidualEquiv.refl rest
      | succ later =>
          simp at leftBound

/-- A child simulation span lifts through actual authored ParCong. The
source and target comparisons have different relations for a reason: COMM
can contract a quoted Drop in the authored immediate reduct. -/
theorem parallel_simulation {intrinsicSource intrinsicTarget authoredSource
    authoredTarget rest : Pattern}
    (sourceComparison : StructuralCongruence intrinsicSource authoredSource)
    (authoredChild : RhoStep authoredSource authoredTarget)
    (targetComparison : ProcResidualEquiv authoredTarget intrinsicTarget) :
    RhoStep
      (.collection .hashBag [authoredSource, rest] none)
      (.collection .hashBag [authoredTarget, rest] none) ∧
    StructuralCongruence
      (.collection .hashBag [intrinsicSource, rest] none)
      (.collection .hashBag [authoredSource, rest] none) ∧
    ProcResidualEquiv
      (.collection .hashBag [authoredTarget, rest] none)
      (.collection .hashBag [intrinsicTarget, rest] none) :=
  ⟨authored_parallel_step rest authoredChild,
    parallel_source_congruence sourceComparison,
    parallel_target_residual targetComparison⟩

/-- The authored closed-process carrier is stable under the declared
parallel-bag constructor. The proof uses both its process sort and sealed
quotation check. -/
theorem closed_parallel (left right : Pattern)
    (leftClosed : RhoClosedTermWellSorted rhoProc left)
    (rightClosed : RhoClosedTermWellSorted rhoProc right) :
    RhoClosedTermWellSorted rhoProc
      (.collection .hashBag [left, right] none) := by
  have leftParts := (rhoClosedTermWellSorted_process_iff left).mp leftClosed
  have rightParts := (rhoClosedTermWellSorted_process_iff right).mp rightClosed
  apply (rhoClosedTermWellSorted_process_iff _).mpr
  constructor
  · exact ProcWellSorted.parallel
      (.cons leftParts.1 (.cons rightParts.1 .nil))
  · simpa [binderSafeAt, binderSafeListAt] using
      And.intro leftParts.2 rightParts.2

/-- The actual authored COMM step supplies ParCong's recursive premise.
The intrinsic binary source and result compare to its canonical hash-bag
source and result by their respective justified relations. -/
theorem comm_under_par_simulation
    (channel : Term sig [] Srt.nm)
    (payload rest : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true) :
    RhoStep
      (.collection .hashBag
        [authoredInputFirst channel payload body, encodeTerm rest] none)
      (.collection .hashBag
        [authoredResult payload body, encodeTerm rest] none) ∧
    StructuralCongruence
      (encodeTerm (par raw (intrinsicSource channel payload body) rest))
      (.collection .hashBag
        [authoredInputFirst channel payload body, encodeTerm rest] none) ∧
    ProcResidualEquiv
      (.collection .hashBag
        [authoredResult payload body, encodeTerm rest] none)
      (encodeTerm (par raw (commTarget raw payload body) rest)) := by
  have child := authored_comm_residual_simulation channel payload body
    channelSafe payloadSafe bodySafe
  have lifted := parallel_simulation
    (rest := encodeTerm rest) child.2.2.1 child.2.1 child.2.2.2
  exact lifted

/-- For quote-safe data, both sides of the ParCong comparison remain in the
same declaration-derived closed process carrier, at source and target. -/
theorem comm_under_par_closed
    (channel : Term sig [] Srt.nm)
    (payload rest : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr)
    (channelSafe : intrinsicQuoteSafe 0 channel = true)
    (payloadSafe : intrinsicQuoteSafe 0 payload = true)
    (bodySafe : intrinsicQuoteSafe 1 body = true)
    (restSafe : intrinsicQuoteSafe 0 rest = true) :
    RhoClosedTermWellSorted rhoProc
      (encodeTerm (par raw (intrinsicSource channel payload body) rest)) ∧
    RhoClosedTermWellSorted rhoProc
      (.collection .hashBag
        [authoredInputFirst channel payload body, encodeTerm rest] none) ∧
    RhoClosedTermWellSorted rhoProc
      (.collection .hashBag
        [authoredResult payload body, encodeTerm rest] none) ∧
    RhoClosedTermWellSorted rhoProc
      (encodeTerm (par raw (commTarget raw payload body) rest)) := by
  have child := comm_closed_source_and_rule_cover channel payload body
    channelSafe payloadSafe bodySafe
  have restClosed := (encoded_process_admitted_iff_quoteSafe rest).mpr restSafe
  have targetClosed := intrinsic_comm_target_admitted_of_safe
    payload body payloadSafe bodySafe
  exact ⟨closed_parallel _ _ child.1 restClosed,
    closed_parallel _ _ child.2.1 restClosed,
    closed_parallel _ _ child.2.2.1 restClosed,
    closed_parallel _ _ targetClosed restClosed⟩

/-- One intrinsic ParCong node retains its supplied recursive child tree
at the exact premise judgment, rather than merely asserting that an endpoint
relation is inhabited. -/
def parCongTree {source target rest : Term sig [] Srt.pr}
    (child : (rules raw).Fix () (judgment raw source target)) :
    (rules raw).Fix ()
      (judgment raw (par raw source rest) (par raw target rest)) :=
  .roll (RuleShape.parCong (A := raw) (Γ := []) source target rest)
    (fun _ => child)

/-- At the raw intrinsic presentation, a ParCong constructor retains its
specific child derivation: two parent trees at the same judgment are equal
only if their recursive children are equal. No injectivity through the
equation-model interpretation is assumed. -/
theorem parCongTree_injective {source target rest : Term sig [] Srt.pr} :
    Function.Injective
      (fun child : (rules raw).Fix () (judgment raw source target) =>
        parCongTree (rest := rest) child) := by
  intro first second equal
  unfold parCongTree at equal
  injection equal with indexEqual shapeEqual childrenEqual
  exact congrFun childrenEqual ()

/-- The already established COMM constructor can be used as ParCong's
recursive child at every closed intrinsic channel, payload and body. -/
def parCommTree (channel : Term sig [] Srt.nm)
    (payload rest : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) :
    (rules raw).Fix ()
      (judgment raw
        (par raw (intrinsicSource channel payload body) rest)
        (par raw (commTarget raw payload body) rest)) :=
  parCongTree (intrinsicCommTree channel payload body)

private noncomputable abbrev sourceAlgebra :=
  (FreeBindingEquationModel.presented rhoSourceE).algebra

/-- The full source-equation model retains the ParCong node and its COMM
child after interpreting the intrinsic terms into equation classes. -/
noncomputable def sourceEquationParCommTree
    (channel : Term sig [] Srt.nm)
    (payload rest : Term sig [] Srt.pr)
    (body : Term sig [Srt.nm] Srt.pr) :
    (rules sourceAlgebra).Fix ()
      (mapJudgment (FreeBindingClone.interpretHom sourceAlgebra)
        (judgment raw
          (par raw (intrinsicSource channel payload body) rest)
          (par raw (commTarget raw payload body) rest))) :=
  interpretTree (FreeBindingClone.interpretHom sourceAlgebra) _
    (parCommTree channel payload rest body)

/-- The selected unquote result remains only residually equivalent after
ParCong with a closed nil rest. Structural congruence of the parent results
would imply the already-refuted structural congruence of their children. -/
theorem unquote_parallel_residual_but_not_structural :
    ProcResidualEquiv
      (.collection .hashBag
        [authoredCommReduct, encodeTerm nilP] none)
      (.collection .hashBag
        [encodeTerm RhoSchema.commTarget, encodeTerm nilP] none) ∧
    ¬ StructuralCongruence
      (.collection .hashBag
        [authoredCommReduct, encodeTerm nilP] none)
      (.collection .hashBag
        [encodeTerm RhoSchema.commTarget, encodeTerm nilP] none) := by
  have selected := unquote_result_residual_but_not_structural
  constructor
  · exact parallel_target_residual selected.1
  · intro parent
    have leftUnit : StructuralCongruence
        (.collection .hashBag
          [authoredCommReduct, encodeTerm nilP] none)
        authoredCommReduct := by
      simpa [nilP, encodeTerm] using
        (StructuralCongruence.par_nil_right authoredCommReduct)
    have rightUnit : StructuralCongruence
        (.collection .hashBag
          [encodeTerm RhoSchema.commTarget, encodeTerm nilP] none)
        (encodeTerm RhoSchema.commTarget) := by
      simpa [nilP, encodeTerm] using
        (StructuralCongruence.par_nil_right
          (encodeTerm RhoSchema.commTarget))
    have child : StructuralCongruence authoredCommReduct
        (encodeTerm RhoSchema.commTarget) :=
      StructuralCongruence.trans _ _ _
        (StructuralCongruence.symm _ _ leftUnit)
        (StructuralCongruence.trans _ _ _ parent rightUnit)
    exact selected.2 child

#print axioms parallel_simulation
#print axioms closed_parallel
#print axioms comm_under_par_simulation
#print axioms comm_under_par_closed
#print axioms parCongTree
#print axioms parCongTree_injective
#print axioms parCommTree
#print axioms sourceEquationParCommTree
#print axioms unquote_parallel_residual_but_not_structural

end Mettapedia.OSLF.Binding.RhoParCongResidualSimulation
