import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLineControls

/-!
# Union of programs is idempotent, parallel composition of processes cancels: every uniform
# translation into the reflective calculus with its equations forgets the program

Systems compose by the union of their programs, so `⟨P, ∅⟩ ∥ ⟨P, t⟩` and `⟨P, ∅⟩ ∥ ⟨∅, t⟩` are the
same system (`P ∪ P = P ∪ ∅`). The equations of the reflective calculus are equality of canonical
bags, and the bag of `A | B` is the sum of the bags (`fromProcess_par_bag`), which cancels. So a
translation homomorphic up to the equations sends `⟨P, t⟩` and `⟨∅, t⟩` to equal processes, for
every program `P` and every state `t` with solvable knowledge (`program_blind`). Success sensitivity
then fails at one rule: take `*@0`, make `ω!(0)`, with the row `*@0` (`withRule_succeeds`,
`blockerOnly_never`).

* `step_not_into_rho_by_idempotence`: the negative half of `strict_separation_solvable`, with no
  none check and a finite program.
* `positive_not_into_rho_by_idempotence`: the positive step does not embed either, with finite
  programs.
* The argument needs the target's equivalence to cancel a common parallel component; it does not
  apply to barbed bisimilarity, for which only the counting argument is available.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Idempotence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag (fromProcess fromProcess_eq_iff append_inventory)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
  (ParallelCalculus UniformTranslation)
open ByInstantiation (sig G Similar ObsSimilar Grounding knowledge groundFrame someGrounding zeroT dropqT)
open Interface.Frames (Frame)

/-! ## Cancellation in the reflective calculus -/

/-- **The equations cancel a common parallel component.** -/
theorem cancel_par {A B B' : RhoProcess}
    (same : rhoProcessEquations.r (par A B) (par A B')) : rhoProcessEquations.r B B' := by
  rw [← fromProcess_eq_iff] at same ⊢
  rw [fromProcess_par_bag, fromProcess_par_bag] at same
  apply Subtype.ext
  have inventories := congrArg Subtype.val same
  rw [append_inventory, append_inventory] at inventories
  exact add_left_cancel inventories

/-- Reachable success is invariant under the equations. -/
theorem succeeds_congr (ω : G [] .nm) {P P' : RhoProcess} (same : rhoProcessEquations.r P P') :
    (rhoParallel ω).Succeeds P ↔ (rhoParallel ω).Succeeds P' :=
  ⟨(rhoParallel_persistent ω).respects P' P (rhoProcessEquations.iseqv.symm same),
    (rhoParallel_persistent ω).respects P P' same⟩

/-! ## Every uniform translation forgets the program -/

theorem empty_solvable : knowledge.Solvable emptyState.knowledge :=
  (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, fun _ inside => absurd inside List.not_mem_nil⟩

/-- `⟨P, ∅⟩ ∥ ⟨P, t⟩` and `⟨P, ∅⟩ ∥ ⟨∅, t⟩` are the same system. -/
theorem par_absorbs (ω : G [] .nm) (P : Prog) (t : ByInstantiation.State) :
    (stepParallelSolvable ω).par ⟨P, emptyState⟩ ⟨P, t⟩ = (stepParallelSolvable ω).par ⟨P, emptyState⟩ ⟨∅, t⟩ := by
  show (⟨P ∪ P, tensor emptyState t⟩ : System) = ⟨P ∪ ∅, tensor emptyState t⟩
  rw [Set.union_self, Set.union_empty]

/-- **Every uniform translation of the step into the reflective calculus forgets the program**: up to
the equations, `⟨P, t⟩` and `⟨∅, t⟩` have the same image whenever `t`'s knowledge is solvable. -/
theorem program_blind {ω : G [] .nm} (τ : UniformTranslation (stepParallelSolvable ω) (rhoParallel ω))
    (P : Prog) (t : ByInstantiation.State) (solvable : knowledge.Solvable t.knowledge) :
    rhoProcessEquations.r (τ.map ⟨P, t⟩) (τ.map ⟨∅, t⟩) := by
  have one := τ.homomorphic ⟨P, emptyState⟩ ⟨P, t⟩ ((tensor_solvable_iff _ _).mpr ⟨empty_solvable, solvable⟩)
  have two := τ.homomorphic ⟨P, emptyState⟩ ⟨∅, t⟩ ((tensor_solvable_iff _ _).mpr ⟨empty_solvable, solvable⟩)
  rw [par_absorbs] at one
  exact cancel_par (rhoProcessEquations.iseqv.trans (rhoProcessEquations.iseqv.symm one) two)

/-! ## One rule tells the difference -/

/-- **Take `*@0`, make `ω!(0)`**: positive, and finite. -/
abbrev takeBlocker (ω : G [] .nm) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [ByInstantiation.obs blockerRow], read := [], tell := [], checks := [],
            produce := [ByInstantiation.obs (successRow ω)] }
  collect := []

theorem takeBlocker_positive (ω : G [] .nm) : RuleSyntax.Scope.Positive (takeBlocker ω) :=
  ⟨fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- The row `*@0` with the rule. -/
def withRule (ω : G [] .nm) : System := ⟨{takeBlocker ω}, single blockerRow⟩

/-- The row `*@0` with no rule. -/
def blockerOnly : System := ⟨∅, single blockerRow⟩

abbrev takeFiring (ω : G [] .nm) :
    RuleSyntax.Firing ℕ decl ({takeBlocker ω} : Prog) (single blockerRow).frame :=
  RuleSyntax.Contextual.canonical (F := (single blockerRow).frame) (takeBlocker ω) (Set.mem_singleton _)
    ⟨[0], [], [1]⟩ []

theorem takeFiring_information (ω : G [] .nm) :
    (takeFiring ω).information knowledge (single blockerRow) =
      [(knowledge.act (takeFiring ω).opening (ByInstantiation.obs blockerRow),
        knowledge.act (decl.weaken (takeFiring ω).ext) (ByInstantiation.obs blockerRow))] := rfl

theorem take_equation (ω : G [] .nm) :
    knowledge.E
      (knowledge.act (b := groundFrame) (someGrounding _)
        (knowledge.act (takeFiring ω).opening (ByInstantiation.obs blockerRow)))
      (knowledge.act (b := groundFrame) (someGrounding _)
        (knowledge.act (decl.weaken (takeFiring ω).ext) (ByInstantiation.obs blockerRow))) :=
  equal_of_grounds (o := ByInstantiation.obs blockerRow)
    (fun g => ground_back₃ (takeFiring ω).opening (someGrounding _) g (ByInstantiation.obs blockerRow))
    (fun g => ground_back₃ (decl.weaken (takeFiring ω).ext) (someGrounding _) g (ByInstantiation.obs blockerRow))

theorem takeFiring_admitted (ω : G [] .nm) : (takeFiring ω).Admits knowledge (single blockerRow) := by
  refine ⟨⟨canonical_fresh_knowledge _ (takeBlocker ω) _ _ _, List.nodup_singleton 0, List.nodup_singleton 1,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ()) ({0} : Finset ℕ) ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [takeFiring_information]
    intro e inside
    obtain rfl := List.mem_singleton.mp inside
    exact take_equation ω
  · intro b σ _
    exact ⟨fun c inside => (nomatch inside), fun q inside => (nomatch inside)⟩

/-- **With the rule, the row `*@0` leads to success.** -/
theorem withRule_succeeds (ω : G [] .nm) : (stepParallelSolvable ω).Succeeds (withRule ω) := by
  refine ⟨⟨{takeBlocker ω}, (takeFiring ω).result knowledge (single blockerRow)⟩,
    .single ⟨rfl, takeFiring ω, takeFiring_admitted ω, rfl⟩, ?_⟩
  refine outBarb_of_ground (o := 1) ?_ ?_ ?_
  · change 1 ∈ fire ({0} : Finset ℕ) ((⟨[0], [], [1]⟩ : Selection ℕ).commit (T := Unit))
    rw [mem_fire]
    exact .inr (by simp [Selection.commit])
  · intro e inside
    change e ∈ (takeFiring ω).information knowledge (single blockerRow) at inside
    rw [takeFiring_information] at inside
    obtain rfl := List.mem_singleton.mp inside
    exact take_equation ω
  · show instantiateObservation (someGrounding _)
      (instantiateObservation (takeFiring ω).opening (ByInstantiation.obs (successRow ω))) = _
    exact ground_back _ _ _

/-- The row `*@0` shows no output barb. -/
theorem single_blocker_no_barb (ω : G [] .nm) : ¬ OutBarb ω (single blockerRow) := by
  rintro ⟨o, _, B, σ, h, _, equal⟩
  have similar := equal (someGrounding B)
  change ObsSimilar
      (instantiateObservation (someGrounding B) (instantiateObservation σ (ByInstantiation.obs blockerRow)))
      (instantiateObservation (someGrounding B)
        (instantiateObservation h ⟨[], .pr, ByInstantiation.outputT (embed ω) payloadUnknown⟩)) at similar
  have left : instantiateObservation (someGrounding B)
      (instantiateObservation σ (ByInstantiation.obs blockerRow)) = ByInstantiation.obs blockerRow :=
    ground_back _ _ _
  rw [left] at similar
  have closed := ByInstantiation.obsSimilar_closed.mp similar
  change Similar (dropqT zeroT) (ByInstantiation.outputT _ _) at closed
  cases closed

/-- **Without the rule, it never does.** -/
theorem blockerOnly_never (ω : G [] .nm) : ¬ (stepParallelSolvable ω).Succeeds blockerOnly :=
  never_succeeds_of_stuck (fun f => absurd f.member (Set.notMem_empty _)) (single_blocker_no_barb ω)

theorem single_solvable : knowledge.Solvable (single blockerRow).knowledge :=
  (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, fun _ inside => absurd inside List.not_mem_nil⟩

/-! ## The separations -/

/-- **The negative half of the separation, by idempotence**: no uniform translation of the step with
restricted composition into the reflective calculus, with no none check and a one-rule program. -/
theorem step_not_into_rho_by_idempotence (ω : G [] .nm) :
    IsEmpty (UniformTranslation (stepParallelSolvable ω) (rhoParallel ω)) :=
  ⟨fun τ => blockerOnly_never ω (τ.reflects _ ((succeeds_congr ω
    (program_blind τ {takeBlocker ω} (single blockerRow) single_solvable)).mp
      (τ.preserves _ (withRule_succeeds ω))))⟩

/-- **The positive step, finite programs included, does not embed into the reflective calculus with
its equations.** -/
theorem positive_not_into_rho_by_idempotence (ω : G [] .nm) :
    IsEmpty (UniformTranslation (positiveParallel ω) (rhoParallel ω)) := by
  refine ⟨fun τ => ?_⟩
  let P : Prog := {takeBlocker ω}
  have positive : ∀ r ∈ P, RuleSyntax.Scope.Positive r := fun r member => by
    rw [Set.mem_singleton_iff.mp member]
    exact takeBlocker_positive ω
  have none : ∀ r ∈ (∅ : Prog), RuleSyntax.Scope.Positive r := fun r member => absurd member (Set.notMem_empty r)
  let S : (positiveParallel ω).Term := ⟨⟨P, emptyState⟩, positive⟩
  let T : (positiveParallel ω).Term := ⟨⟨P, single blockerRow⟩, positive⟩
  let T' : (positiveParallel ω).Term := ⟨⟨∅, single blockerRow⟩, none⟩
  have composable : ∀ U : (positiveParallel ω).Term, U.1.state = single blockerRow →
      (positiveParallel ω).composable S U := fun U state => by
    change knowledge.Solvable (tensor emptyState U.1.state).knowledge
    rw [state]
    exact (tensor_solvable_iff _ _).mpr ⟨empty_solvable, single_solvable⟩
  have one := τ.homomorphic S T (composable T rfl)
  have two := τ.homomorphic S T' (composable T' rfl)
  have same : (positiveParallel ω).par S T = (positiveParallel ω).par S T' :=
    Subtype.ext (par_absorbs ω P (single blockerRow))
  rw [same] at one
  have blind := cancel_par (rhoProcessEquations.iseqv.trans (rhoProcessEquations.iseqv.symm one) two)
  have succeedsT : (positiveParallel ω).Succeeds T := (positive_succeeds_iff ω T).mpr (withRule_succeeds ω)
  exact blockerOnly_never ω ((positive_succeeds_iff ω T').mp
    (τ.reflects T' ((succeeds_congr ω blind).mp (τ.preserves T succeedsT))))

#print axioms cancel_par
#print axioms succeeds_congr
#print axioms par_absorbs
#print axioms program_blind
#print axioms takeFiring_admitted
#print axioms withRule_succeeds
#print axioms single_blocker_no_barb
#print axioms blockerOnly_never
#print axioms step_not_into_rho_by_idempotence
#print axioms positive_not_into_rho_by_idempotence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Idempotence
