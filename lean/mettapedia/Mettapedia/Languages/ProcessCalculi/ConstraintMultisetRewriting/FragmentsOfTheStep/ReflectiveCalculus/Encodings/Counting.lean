import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.DividingLineControls
import Mettapedia.OSLF.MeTTaIL.PatternCountability

/-!
# Counting: the positive step does not embed into the reflective calculus, for a reason that is not
# a feature

A program is a set of rules (`RuleSyntax.Program := Set (Rule …)`), so there are as many positive
systems as sets of natural numbers, while closed processes of the reflective calculus are countable
(`Pattern` is countable). The criterion asks a translation to be homomorphic on parallel composition
up to the target's static equivalence and to preserve and reflect reachable success. When that
equivalence respects reachable success in both directions (the equations of the reflective calculus;
its barbed bisimilarity over names that include the success channel), a translation must keep apart
any two systems that some test tells apart, and countably many tests tell apart uncountably many
positive systems. So no such translation exists, and no none check, count check or collect pattern
is involved.

* `nest`: `0`, `*@0`, `*@*@0`, …; similar only at equal depth (`nest_similar`). The row of `n` is
  `nest (n + 1)`, a drop, never an output.
* `takeRule ω n`: take the row of `n`, make `ω!(0)`; positive (`takeRule_positive`).
* `systemOf ω A`: the rules `takeRule ω m` for `m ∈ A`, and no row. `testOf ω n`: no rule, the row
  of `n`. Side by side they succeed exactly when `n ∈ A` (`succeeds_iff_mem`).
* `no_faithful_map`: no map of positive systems to processes is success-faithful on systems and on
  composites read through the reflective calculus's parallel composition.
* Instances: `positive_not_into_rho` (the reflective calculus with its equations, the target of the
  separation), `positive_not_into_symmetric` (any symmetric relation that respects success, hence
  `positive_not_into_bisimilar`), and `step_not_into_rho_by_counting` (the negative half of the
  separation, with no none check).
* The hypothesis that the relation respects success both ways is needed: the total relation does not
  respect success, and with it the characteristic function of success is uniform
  (`oracle_with_total`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Counting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
  (ParallelCalculus UniformTranslation)
open ByInstantiation (sig G Similar ObsSimilar Grounding knowledge groundFrame someGrounding zeroT dropqT)
open Interface.Frames (Frame)

/-! ## Rows told apart by depth -/

/-- Nested drops: `0`, `*@0`, `*@*@0`, … -/
def nest : ℕ → G [] .pr
  | 0 => zeroT
  | n + 1 => dropqT (nest n)

/-- **Nested drops are similar only at equal depth.** -/
theorem nest_similar : ∀ m n : ℕ, Similar (nest m) (nest n) → m = n
  | 0, 0, _ => rfl
  | 0, n + 1, similar => by
      change Similar (zeroT : G [] .pr) (dropqT (nest n)) at similar
      cases similar
  | m + 1, 0, similar => by
      change Similar (dropqT (nest m)) (zeroT : G [] .pr) at similar
      cases similar
  | m + 1, n + 1, similar => by
      change Similar (dropqT (nest m)) (dropqT (nest n)) at similar
      cases similar with
      | dropq inner => exact congrArg (· + 1) (nest_similar m n inner)

/-- The row of `n`. -/
abbrev rowOf (n : ℕ) : G [] .pr := nest (n + 1)

/-! ## The systems and the tests -/

/-- **Take the row of `n`, make `ω!(0)`**: one take, no check, no tell, no collect pattern. -/
abbrev takeRule (ω : G [] .nm) (n : ℕ) : RuleSyntax.Rule (RuleSyntax.Contextual.Terms sig) where
  locals := groundFrame
  body := { take := [ByInstantiation.obs (rowOf n)], read := [], tell := [], checks := [],
            produce := [ByInstantiation.obs (successRow ω)] }
  collect := []

theorem takeRule_positive (ω : G [] .nm) (n : ℕ) : RuleSyntax.Scope.Positive (takeRule ω n) :=
  ⟨fun _ inside => absurd inside List.not_mem_nil, rfl⟩

/-- The rules `takeRule ω m` for `m ∈ A`. -/
def programOf (ω : G [] .nm) (A : Set ℕ) : Prog := takeRule ω '' A

/-- **The system of `A`**: the rules of `A`, and no row. -/
def systemOf (ω : G [] .nm) (A : Set ℕ) : (positiveParallel ω).Term :=
  ⟨⟨programOf ω A, emptyState⟩, fun r member => by
    obtain ⟨m, _, rfl⟩ := member
    exact takeRule_positive ω m⟩

/-- **The test of `n`**: no rule, and the row of `n`. -/
def testOf (ω : G [] .nm) (n : ℕ) : (positiveParallel ω).Term :=
  ⟨⟨∅, single (rowOf n)⟩, fun r member => absurd member (Set.notMem_empty r)⟩

/-- The state of the composite. -/
abbrev besideState (n : ℕ) : ByInstantiation.State := tensor emptyState (single (rowOf n))

theorem composable_test (ω : G [] .nm) (A : Set ℕ) (n : ℕ) :
    (positiveParallel ω).composable (systemOf ω A) (testOf ω n) := by
  refine (ByInstantiation.solvable_iff _).mpr ⟨someGrounding _, ?_⟩
  intro e member
  change e ∈ knowledge.applyStore _ ([] : List _) ++ knowledge.applyStore _ ([] : List _) at member
  simp [Interface.Frames.applyStore] at member

theorem besideState_label (n : ℕ) :
    (besideState n).label 1 =
      instantiateObservation (rightIn emptyState.frame (single (rowOf n)).frame)
        (ByInstantiation.obs (rowOf n)) :=
  tensor_label_odd emptyState (single (rowOf n)) 0

/-! ## When `n ∈ A`, the composite succeeds -/

/-- The firing of `takeRule ω n` at the composite: it takes the test's row (identity `1`) and makes
identity `0`. -/
abbrev takeFiring (ω : G [] .nm) (A : Set ℕ) (n : ℕ) (inside : n ∈ A) :
    RuleSyntax.Firing ℕ decl (programOf ω A ∪ ∅) (besideState n).frame :=
  RuleSyntax.Contextual.canonical (F := (besideState n).frame) (takeRule ω n)
    (Set.mem_union_left _ ⟨n, inside, rfl⟩) ⟨[1], [], [0]⟩ []

theorem takeFiring_information (ω : G [] .nm) (A : Set ℕ) (n : ℕ) (inside : n ∈ A) :
    (takeFiring ω A n inside).information knowledge (besideState n) =
      [(knowledge.act (takeFiring ω A n inside).opening (ByInstantiation.obs (rowOf n)),
        knowledge.act (decl.weaken (takeFiring ω A n inside).ext) ((besideState n).label 1))] := rfl

/-- The take equation is solved by every grounding. -/
theorem take_equation_grounded (ω : G [] .nm) (A : Set ℕ) (n : ℕ) (inside : n ∈ A) :
    knowledge.E
      (knowledge.act (b := groundFrame) (someGrounding _)
        (knowledge.act (takeFiring ω A n inside).opening (ByInstantiation.obs (rowOf n))))
      (knowledge.act (b := groundFrame) (someGrounding _)
        (knowledge.act (decl.weaken (takeFiring ω A n inside).ext) ((besideState n).label 1))) := by
  rw [besideState_label]
  exact equal_of_grounds (o := ByInstantiation.obs (rowOf n))
    (fun g => ground_back₃ (takeFiring ω A n inside).opening (someGrounding _) g
      (ByInstantiation.obs (rowOf n)))
    (fun g => ground_back₄ (rightIn emptyState.frame (single (rowOf n)).frame)
      (decl.weaken (takeFiring ω A n inside).ext) (someGrounding _) g (ByInstantiation.obs (rowOf n)))

theorem takeFiring_admitted (ω : G [] .nm) (A : Set ℕ) (n : ℕ) (inside : n ∈ A) :
    (takeFiring ω A n inside).Admits knowledge (besideState n) := by
  refine ⟨⟨canonical_fresh_knowledge _ (takeRule ω n) _ _ _, List.nodup_singleton 1,
    List.nodup_singleton 0, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : ℕ => ())
      ((∅ : Finset ℕ).map evenEmbedding ∪ ({0} : Finset ℕ).map oddEmbedding)
      ((⟨[1], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    decide
  · refine ⟨groundFrame, someGrounding _, ?_⟩
    rw [takeFiring_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact take_equation_grounded ω A n inside
  · intro b σ _
    exact ⟨fun c member => (nomatch member), fun q member => (nomatch member)⟩

/-- **When `n ∈ A`, the system of `A` beside the test of `n` succeeds.** -/
theorem beside_succeeds (ω : G [] .nm) (A : Set ℕ) (n : ℕ) (inside : n ∈ A) :
    (positiveParallel ω).Succeeds ((positiveParallel ω).par (systemOf ω A) (testOf ω n)) := by
  refine (positive_succeeds_iff ω _).mpr ?_
  refine ⟨⟨programOf ω A ∪ ∅, (takeFiring ω A n inside).result knowledge (besideState n)⟩,
    .single ⟨rfl, takeFiring ω A n inside, takeFiring_admitted ω A n inside, rfl⟩, ?_⟩
  refine outBarb_of_ground (o := 0) ?_ ?_ ?_
  · change 0 ∈ fire ((∅ : Finset ℕ).map evenEmbedding ∪ ({0} : Finset ℕ).map oddEmbedding)
      ((⟨[1], [], [0]⟩ : Selection ℕ).commit (T := Unit))
    rw [mem_fire]
    exact .inr (by simp [Selection.commit])
  · intro e member
    change e ∈ (takeFiring ω A n inside).information knowledge (besideState n) at member
    rw [takeFiring_information] at member
    obtain rfl := List.mem_singleton.mp member
    exact take_equation_grounded ω A n inside
  · show instantiateObservation (someGrounding _)
      (instantiateObservation (takeFiring ω A n inside).opening (ByInstantiation.obs (successRow ω))) = _
    exact ground_back _ _ _

/-! ## When `n ∉ A`, the composite never succeeds -/

/-- **The row of `n` shows no output barb**: it is a drop. -/
theorem row_no_barb (ω : G [] .nm) (n : ℕ) : ¬ OutBarb ω (besideState n) := by
  rintro ⟨o, present, B, σ, h, _, equal⟩
  have isOne : o = 1 := by
    rcases mem_tensor.mp present with ⟨k, inside, _⟩ | ⟨k, inside, rfl⟩
    · exact absurd inside (Finset.notMem_empty k)
    · rw [Finset.mem_singleton.mp inside]
  subst isOne
  have similar := equal (someGrounding B)
  change ObsSimilar
      (instantiateObservation (someGrounding B) (instantiateObservation σ ((besideState n).label 1)))
      (instantiateObservation (someGrounding B)
        (instantiateObservation h ⟨[], .pr, ByInstantiation.outputT (embed ω) payloadUnknown⟩)) at similar
  have left : instantiateObservation (someGrounding B)
      (instantiateObservation σ ((besideState n).label 1)) = ByInstantiation.obs (rowOf n) := by
    rw [besideState_label]
    exact ground_back₃ _ _ _ _
  rw [left] at similar
  have closed := ByInstantiation.obsSimilar_closed.mp similar
  change Similar (dropqT (nest n)) (ByInstantiation.outputT _ _) at closed
  cases closed

/-- **When `n ∉ A`, no firing is admitted at the composite**: a rule `takeRule ω m` with `m ≠ n` would
equate the row of `m` with the row of `n`. -/
theorem beside_stuck (ω : G [] .nm) (A : Set ℕ) (n : ℕ) (outside : n ∉ A)
    (f : RuleSyntax.Firing ℕ decl (programOf ω A ∪ ∅) (besideState n).frame) :
    ¬ f.Admits knowledge (besideState n) := by
  obtain ⟨rule, member, ext, opening, ⟨taken, read, made⟩, seen⟩ := f
  obtain ⟨m, inA, rfl⟩ : ∃ m ∈ A, takeRule ω m = rule := by
    rcases member with inside | inside
    · exact inside
    · exact inside.elim
  rintro ⟨⟨_, _, _, takeLength, _, _, _⟩, enabled, solvable, _⟩
  obtain ⟨o, rfl⟩ : ∃ o, taken = [o] := by
    match taken, takeLength with
    | [o], _ => exact ⟨o, rfl⟩
  have present : o ∈ (besideState n).present :=
    enabled.taken_subset (List.mem_toFinset.mpr (List.mem_singleton_self o))
  have isOne : o = 1 := by
    rcases mem_tensor.mp present with ⟨k, inside, _⟩ | ⟨k, inside, rfl⟩
    · exact absurd inside (Finset.notMem_empty k)
    · rw [Finset.mem_singleton.mp inside]
  subst isOne
  obtain ⟨g, solves⟩ := (ByInstantiation.solvable_iff _).mp solvable
  have equated := RuleSyntax.Firing.take_solved (X := knowledge)
    (⟨takeRule ω m, member, ext, opening, ⟨[1], read, made⟩, seen⟩ :
      RuleSyntax.Firing ℕ decl (programOf ω A ∪ ∅) (besideState n).frame)
    (ByInstantiation.models_of_groundSolves solves)
    (p := knowledge.act opening (ByInstantiation.obs (rowOf m))) (o := 1) (List.mem_singleton_self _)
  have similar := equated (someGrounding groundFrame)
  change ObsSimilar
      (instantiateObservation (someGrounding groundFrame)
        (instantiateObservation g (instantiateObservation opening (ByInstantiation.obs (rowOf m)))))
      (instantiateObservation (someGrounding groundFrame)
        (instantiateObservation g (instantiateObservation
          (RuleSyntax.Contextual.weakenNames sig (besideState n).frame ext) ((besideState n).label 1))))
    at similar
  have left : instantiateObservation (someGrounding groundFrame)
      (instantiateObservation g (instantiateObservation opening (ByInstantiation.obs (rowOf m)))) =
        ByInstantiation.obs (rowOf m) :=
    ground_back₃ _ _ _ _
  have right : instantiateObservation (someGrounding groundFrame)
      (instantiateObservation g (instantiateObservation
        (RuleSyntax.Contextual.weakenNames sig (besideState n).frame ext) ((besideState n).label 1))) =
        ByInstantiation.obs (rowOf n) := by
    rw [besideState_label]
    exact ground_back₄ _ _ _ _ _
  rw [left, right] at similar
  have same : m + 1 = n + 1 := nest_similar (m + 1) (n + 1) (ByInstantiation.obsSimilar_closed.mp similar)
  obtain rfl : m = n := by omega
  exact outside inA

/-- **When `n ∉ A`, the composite never succeeds.** -/
theorem beside_never (ω : G [] .nm) (A : Set ℕ) (n : ℕ) (outside : n ∉ A) :
    ¬ (positiveParallel ω).Succeeds ((positiveParallel ω).par (systemOf ω A) (testOf ω n)) := by
  rw [positive_succeeds_iff]
  exact never_succeeds_of_stuck (S := ⟨programOf ω A ∪ ∅, besideState n⟩) (beside_stuck ω A n outside)
    (row_no_barb ω n)

/-- **The test of `n` reads off membership of `n` in `A`.** -/
theorem succeeds_iff_mem (ω : G [] .nm) (A : Set ℕ) (n : ℕ) :
    (positiveParallel ω).Succeeds ((positiveParallel ω).par (systemOf ω A) (testOf ω n)) ↔ n ∈ A :=
  ⟨fun succeeds => Classical.byContradiction fun outside => beside_never ω A n outside succeeds,
    beside_succeeds ω A n⟩

/-! ## No success-faithful map into a countable calculus -/

/-- The sets of natural numbers are not countable. -/
theorem not_countable_sets : ¬ Countable (Set ℕ) := by
  intro countable
  obtain ⟨f, onto⟩ := exists_surjective_nat (Set ℕ)
  exact Function.cantor_surjective f onto

/-- **No map of positive systems to closed processes is success-faithful**: on every system, and on
every composable pair, read through the reflective calculus's parallel composition. -/
theorem no_faithful_map (ω : G [] .nm) (map : (positiveParallel ω).Term → RhoProcess)
    (onPairs : ∀ S T, (positiveParallel ω).composable S T →
      ((rhoParallel ω).Succeeds (map ((positiveParallel ω).par S T)) ↔
        (rhoParallel ω).Succeeds (par (map S) (map T))))
    (sensitive : ∀ S, (positiveParallel ω).Succeeds S ↔ (rhoParallel ω).Succeeds (map S)) : False := by
  have decides : ∀ A n, n ∈ A ↔ (rhoParallel ω).Succeeds (par (map (systemOf ω A)) (map (testOf ω n))) := by
    intro A n
    rw [← succeeds_iff_mem ω A n, sensitive, onPairs _ _ (composable_test ω A n)]
  have injective : Function.Injective fun A : Set ℕ => map (systemOf ω A) := by
    intro A B same
    ext n
    rw [decides A n, decides B n]
    exact iff_of_eq (congrArg (fun P => (rhoParallel ω).Succeeds (par P (map (testOf ω n)))) same)
  exact not_countable_sets (Function.Injective.countable (β := RhoProcess) injective)

/-- Reachable success is invariant under a symmetric relation that respects it. -/
theorem succeeds_congr_of_symmetric (ω : G [] .nm) {E : RhoProcess → RhoProcess → Prop}
    (symmetric : ∀ t t', E t t' → E t' t) (respects : RespectsSuccess ω E) {t t' : RhoProcess}
    (related : E t t') : (rhoParallel ω).Succeeds t ↔ (rhoParallel ω).Succeeds t' :=
  ⟨respects t' t (symmetric t t' related), respects t t' related⟩

/-- **With any symmetric relation that respects reachable success, the positive step has no uniform
translation into the reflective calculus.** -/
theorem positive_not_into_symmetric (ω : G [] .nm) {E : RhoProcess → RhoProcess → Prop}
    (symmetric : ∀ t t', E t t' → E t' t) (respects : RespectsSuccess ω E) :
    IsEmpty (UniformTranslation (positiveParallel ω) (rhoWith ω E)) :=
  ⟨fun τ => no_faithful_map ω τ.map
    (fun S T composable => succeeds_congr_of_symmetric ω symmetric respects (τ.homomorphic S T composable))
    (fun S => ⟨τ.preserves S, τ.reflects S⟩)⟩

/-- **The target of the separation**: with the equations of the reflective calculus. -/
theorem positive_not_into_rho (ω : G [] .nm) :
    IsEmpty (UniformTranslation (positiveParallel ω) (rhoParallel ω)) :=
  ⟨fun τ => no_faithful_map ω τ.map
    (fun S T composable => succeeds_congr_of_symmetric ω (fun _ _ same => rhoProcessEquations.iseqv.symm same)
      (rhoParallel_persistent ω).respects (τ.homomorphic S T composable))
    (fun S => ⟨τ.preserves S, τ.reflects S⟩)⟩

/-- **With barbed bisimilarity over names that include `ω`.** -/
theorem positive_not_into_bisimilar (ω : G [] .nm) {N : G [] .nm → Prop} (observed : N ω) :
    IsEmpty (UniformTranslation (positiveParallel ω) (rhoWith ω (SourceBisimilar N))) :=
  positive_not_into_symmetric ω
    (fun _ _ ⟨R, bisimulation, related⟩ => ⟨R, bisimulation, bisimulation.symm related⟩)
    (bisimilar_respects ω observed)

/-- **The negative half of the separation, with no none check**: no uniform translation of the
step with restricted composition into the reflective calculus, because its positive systems already
have none. -/
theorem step_not_into_rho_by_counting (ω : G [] .nm) :
    IsEmpty (UniformTranslation (stepParallelSolvable ω) (rhoParallel ω)) :=
  ⟨fun τ => (positive_not_into_rho ω).false
    { map := fun S => τ.map S.1
      homomorphic := fun S T composable => τ.homomorphic S.1 T.1 composable
      preserves := fun S succeeds => τ.preserves S.1 ((positive_succeeds_iff ω S).mp succeeds)
      reflects := fun S succeeds => (positive_succeeds_iff ω S).mpr (τ.reflects S.1 succeeds) }⟩

#print axioms nest_similar
#print axioms takeFiring_admitted
#print axioms beside_succeeds
#print axioms row_no_barb
#print axioms beside_stuck
#print axioms beside_never
#print axioms succeeds_iff_mem
#print axioms not_countable_sets
#print axioms no_faithful_map
#print axioms positive_not_into_symmetric
#print axioms positive_not_into_rho
#print axioms positive_not_into_bisimilar
#print axioms step_not_into_rho_by_counting

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.Counting
