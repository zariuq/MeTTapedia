import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeConcurrentInterface

/-!
# The native concurrent step respects agreement up to dead names

`Step/NativeConcurrentInterface` matches a native concurrent step at an agreeing state by a multi-firing
step of the interface. This module matches it by a native concurrent step: clear families carry along
dead-name extensions, in both directions.

## Carrying solutions

* **Lifts of agreeing solutions agree** (`lift_captured`): the fresh-generator lift of a solution along a
  dead-name extension (`ContextualGuardMatching.Extension.liftModel`) sends the dead names to fresh
  names, whatever the solution (`liftModel_congr`).
* **Joint solutions restrict and lift** along a dead-name extension (`restrictJointAlong`,
  `liftJointAlong`), and so does joint solvability of a family (`jointly_along`).
* **What a guard sees is carried** (`matches_along`, `guardSees_along`), and fresh names in the solution
  frame are not seen (`matches_inclusion`, `guardSees_inclusion`).

## Clear families carry

* `clear_along`: a live firing leaves an admitted one clear exactly when their carryings do.
* `familyClear_along`: a family is clear exactly when its carrying is.
* `concurrent_along`: a concurrent step carries along a dead-name extension to a concurrent step of the
  carried family, and back, with final states that agree up to dead names.
* **Agreement up to dead names is a bisimulation of the native concurrent step**
  (`concurrent_bisimulation`): at two agreeing states, for a program that does not see dead names, a
  concurrent step of an offered clear word at one is matched at the other by a concurrent step of an
  offered clear word with the same labels, and the two results agree up to dead names.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual NativeDead NativeIterated NativeUpToDead
open ContextualGuardMatching (Extension)
open ContextualPrefixModels (inclusion extended)

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeConcurrent

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **The lift of a solution sends the dead names to fresh names, whatever the solution**: two lifts
agree at a name whenever the solutions agree at its preimages. -/
theorem liftModel_congr {V W : Type} {source : V → MetaArity S} {next : W → MetaArity S} (E : Extension source)
    {σ τ : Assignment source next} (x : E.Names) (same : ∀ v, E.name v = x → σ v = τ v) :
    E.liftModel σ x = E.liftModel τ x := by
  have inner : ContextualStoredRows.liftCaptures E.complementDeclarations σ (E.splitNames.symm x) =
      ContextualStoredRows.liftCaptures E.complementDeclarations τ (E.splitNames.symm x) := by
    rcases h : E.splitNames.symm x with c | v
    · rfl
    · have named : E.name v = x := by
        rw [← Extension.splitNames_source, ← h, Equiv.apply_symm_apply]
      show instantiate _ (σ v) = instantiate _ (τ v)
      rw [same v named]
  show instantiate (ContextualStoredRows.liftCaptures E.complementDeclarations σ) (E.unsplitAssignment x) =
    instantiate (ContextualStoredRows.liftCaptures E.complementDeclarations τ) (E.unsplitAssignment x)
  unfold Extension.unsplitAssignment
  rw [instantiate_reindex, instantiate_reindex, inner]

variable {s u : NativeState S O Γ sort} (e : DeadExtension s u)

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Lifts of agreeing solutions agree** on the larger state's names. -/
theorem lift_captured {W : Type} {next : W → MetaArity S}
    (σ τ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next)
    (agree : Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
      Assignment.compose τ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)) :
    Assignment.compose (e.targetExtension.liftModel σ) (ContextualSelectionViews.capturedTarget u.locals u.state.declarations) =
      Assignment.compose (e.targetExtension.liftModel τ) (ContextualSelectionViews.capturedTarget u.locals u.state.declarations) := by
  funext n
  refine (instantiate_generator (e.targetExtension.liftModel σ) (.inr n)).trans
    ((liftModel_congr e.targetExtension (.inr n) fun v named => ?_).trans
      (instantiate_generator (e.targetExtension.liftModel τ) (.inr n)).symm)
  rcases v with v | m
  · simp [Inclusion.targetExtension] at named
  · exact (instantiate_generator σ (.inr m)).symm.trans ((congrFun agree m).trans (instantiate_generator τ (.inr m)))

/-- **A joint solution at the larger state restricts to one at the smaller.** -/
def restrictJointAlong {f g : LiveFiring s} {b : Frames.Frame S}
    (J : Joint u (e.firing f).toNative.information (problemOf u (e.firing g).selection (e.firing g).rule) b) :
    Joint s f.toNative.information (problemOf s g.selection g.rule) b where
  left := Assignment.compose J.left e.target
  right := Assignment.compose J.right e.target
  left_models := (ContextualResidual.models_mapProblem _ _ _).mp ((models_perm _ (e.information_firing f)).mp J.left_models)
  right_models := (ContextualResidual.models_mapProblem _ _ _).mp ((models_perm _ (e.information_firing g)).mp J.right_models)
  agree := by
    rw [← Assignment.compose_associative, ← Assignment.compose_associative, Inclusion.target_captured,
      Assignment.compose_associative, Assignment.compose_associative, J.agree]

/-- **A joint solution at the smaller state lifts to one at the larger**, with fresh names for the dead
names. -/
noncomputable def liftJointAlong {f g : LiveFiring s} {b : Frames.Frame S}
    (J : Joint s f.toNative.information (problemOf s g.selection g.rule) b) :
    Joint u (e.firing f).toNative.information (problemOf u (e.firing g).selection (e.firing g).rule)
      ⟨e.targetExtension.Complement ⊕ b.Names, extended e.targetExtension.complementDeclarations b.arity⟩ where
  left := e.targetExtension.liftModel J.left
  right := e.targetExtension.liftModel J.right
  left_models := (models_perm _ (e.information_firing f)).mpr
    ((ContextualConditionalNaturality.models_liftModel_iff e.targetExtension J.left _).mpr J.left_models)
  right_models := (models_perm _ (e.information_firing g)).mpr
    ((ContextualConditionalNaturality.models_liftModel_iff e.targetExtension J.right _).mpr J.right_models)
  agree := lift_captured e J.left J.right J.agree

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **What a carried pattern matches is what the pattern matches at the restriction**, at a present
occurrence. -/
theorem matches_along {W : Type} {next : W → MetaArity S}
    (ρ : Assignment (ContextualActivatedStep.target u.locals u.state.declarations) next) {o : O}
    (present : o ∈ s.state.present)
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) :
    ContextualConditionalRows.Matches u.locals (ContextualActivatedStep.target u.locals u.state.declarations) ρ
        (instantiate ρ (instantiate e.target pattern))
        (ContextualConditionalExecution.guardRows u.locals u.state.declarations u.state.rows o) ↔
      ContextualConditionalRows.Matches s.locals (ContextualActivatedStep.target s.locals s.state.declarations)
        (Assignment.compose ρ e.target) (instantiate (Assignment.compose ρ e.target) pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows o) := by
  have mem := Finset.ext_iff.mp (e.region_carried s.state.rows u.state.rows e.rows s.state.present ρ pattern) o
  rw [ContextualConditionalGuards.mem_region, ContextualConditionalGuards.mem_region] at mem
  exact ⟨fun seen => (mem.mp ⟨present, seen⟩).2, fun seen => (mem.mpr ⟨present, seen⟩).2⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **What a carried guard sees is what the guard sees at the restriction**, at a present occurrence. -/
theorem guardSees_along {W : Type} {next : W → MetaArity S}
    (ρ : Assignment (ContextualActivatedStep.target u.locals u.state.declarations) next) {o : O}
    (present : o ∈ s.state.present)
    (check : Check (Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)) :
    GuardSees u.locals ρ (ContextualConditionalExecution.guardRows u.locals u.state.declarations u.state.rows)
        (check.map (instantiate e.target)) o ↔
      GuardSees s.locals (Assignment.compose ρ e.target)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) check o := by
  cases check with
  | equal first second => exact Iff.rfl
  | absent pattern => exact matches_along e ρ present pattern
  | count pattern cardinality => exact matches_along e ρ present pattern

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Fresh names in the solution frame are not seen.** -/
theorem matches_inclusion {Extra : Type} (unused : Extra → MetaArity S) {W : Type} {next : W → MetaArity S}
    (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next) {o : O}
    (present : o ∈ s.state.present)
    (pattern : Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort) :
    ContextualConditionalRows.Matches s.locals (ContextualActivatedStep.target s.locals s.state.declarations)
        (Assignment.compose (inclusion unused next) σ) (instantiate (Assignment.compose (inclusion unused next) σ) pattern)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows o) ↔
      ContextualConditionalRows.Matches s.locals (ContextualActivatedStep.target s.locals s.state.declarations) σ
        (instantiate σ pattern) (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows o) := by
  have mem := Finset.ext_iff.mp (ContextualConditionalNaturality.region_inclusion s.locals unused σ
    (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) s.state.present pattern) o
  rw [ContextualConditionalGuards.mem_region, ContextualConditionalGuards.mem_region] at mem
  exact ⟨fun seen => (mem.mp ⟨present, seen⟩).2, fun seen => (mem.mpr ⟨present, seen⟩).2⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem guardSees_inclusion {Extra : Type} (unused : Extra → MetaArity S) {W : Type} {next : W → MetaArity S}
    (σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) next) {o : O}
    (present : o ∈ s.state.present)
    (check : Check (Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)) :
    GuardSees s.locals (Assignment.compose (inclusion unused next) σ)
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) check o ↔
      GuardSees s.locals σ (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) check o := by
  cases check with
  | equal first second => exact Iff.rfl
  | absent pattern => exact matches_inclusion unused σ present pattern
  | count pattern cardinality => exact matches_inclusion unused σ present pattern

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Fresh names in the solution frame do not change what a guard sees among outputs.** -/
theorem seesOutput_inclusion {V Extra : Type} {declaration : V → MetaArity S} (unused : Extra → MetaArity S)
    {W : Type} {next : W → MetaArity S} (left right : Assignment declaration next)
    (output : Term (signature S declaration) Γ sort) (check : Check (Term (signature S declaration) Γ sort)) :
    SeesOutput (Assignment.compose (inclusion unused next) left) (Assignment.compose (inclusion unused next) right)
        output check ↔ SeesOutput left right output check := by
  have equal : ∀ p : Term (signature S declaration) Γ sort,
      instantiate (Assignment.compose (inclusion unused next) left) p =
          instantiate (Assignment.compose (inclusion unused next) right) output ↔
        instantiate left p = instantiate right output := fun p => by
    rw [Assignment.instantiate_compose, Assignment.instantiate_compose]
    exact ⟨ContextualPrefixModels.inclusion_injective unused next _ _, congrArg _⟩
  cases check with
  | equal first second => exact Iff.rfl
  | absent pattern => exact equal pattern
  | count pattern cardinality => exact equal pattern

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- The rule views of a carried firing are the carried views. -/
theorem checks_along (f : LiveFiring s) :
    (e.firing f).toNative.prepared.rule.checks = f.toNative.prepared.rule.checks.map (Check.map (instantiate e.target)) := by
  rw [e.prepared_firing]
  rfl

/-- **Clearness carries along a dead-name extension**, in both directions. -/
theorem clear_along {f g : LiveFiring s} (admitted : g.toNative.Realized) :
    Clear f g.selection g.rule g.outputs ↔
      Clear (e.firing f) (e.firing g).selection (e.firing g).rule (e.firing g).outputs := by
  obtain ⟨_, enabled, _, _⟩ := (native_admits_iff g.toNative).mp admitted
  have present : ∀ o ∈ g.selection.taken, o ∈ s.state.present := fun o taken =>
    enabled.taken_subset (List.mem_toFinset.mpr taken)
  constructor
  · intro clear
    refine ⟨clear.takes, clear.ports, clear.keeps, ?_, ?_, ?_⟩
    · obtain ⟨b, ⟨J⟩⟩ := clear.consistent
      exact ⟨_, ⟨liftJointAlong e J⟩⟩
    · intro b J o taken
      obtain ⟨checks, patterns⟩ := clear.blindTakes b (restrictJointAlong e J) o taken
      refine ⟨fun check member sees => ?_, fun pattern member seen => ?_⟩
      · rw [checks_along] at member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact checks original inside ((guardSees_along e J.left (present o taken) original).mp sees)
      · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact patterns original inside ((matches_along e J.left (present o taken) original.1).mp seen)
    · intro b J o made
      obtain ⟨checks, patterns⟩ := clear.blindOutputs b (restrictJointAlong e J) o made
      refine ⟨fun check member sees => ?_, fun pattern member equal => ?_⟩
      · rw [checks_along] at member
        obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact checks original inside ((seesOutput_map e.target J.left J.right (g.outputs o) original).mp sees)
      · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
        exact patterns original inside ((Assignment.instantiate_compose J.left e.target original.1).trans
          (equal.trans (Assignment.instantiate_compose J.right e.target (g.outputs o)).symm))
  · intro clear
    refine ⟨clear.takes, clear.ports, clear.keeps, ?_, ?_, ?_⟩
    · obtain ⟨b, ⟨J⟩⟩ := clear.consistent
      exact ⟨b, ⟨restrictJointAlong e J⟩⟩
    · intro b J o taken
      obtain ⟨checks, patterns⟩ := clear.blindTakes _ (liftJointAlong e J) o taken
      have leftSquare := e.targetExtension.liftModel_square J.left
      refine ⟨fun check member sees => ?_, fun pattern member seen => ?_⟩
      · have carried : check.map (instantiate e.target) ∈ (e.firing f).toNative.prepared.rule.checks := by
          rw [checks_along]
          exact List.mem_map_of_mem member
        apply checks _ carried
        refine (guardSees_along e _ (present o taken) check).mpr ?_
        change GuardSees s.locals (Assignment.compose (e.targetExtension.liftModel J.left) e.target) _ check o
        rw [Inclusion.targetExtension_assignment] at leftSquare
        rw [leftSquare]
        exact (guardSees_inclusion _ J.left (present o taken) check).mpr sees
      · have carried : (instantiate e.target pattern.1, pattern.2) ∈ (e.firing f).patterns :=
          List.mem_map_of_mem (f := fun pattern => (instantiate e.target pattern.1, pattern.2)) member
        apply patterns _ carried
        refine (matches_along e _ (present o taken) pattern.1).mpr ?_
        change ContextualConditionalRows.Matches s.locals _ (Assignment.compose (e.targetExtension.liftModel J.left) e.target)
          (instantiate (Assignment.compose (e.targetExtension.liftModel J.left) e.target) pattern.1) _
        rw [Inclusion.targetExtension_assignment] at leftSquare
        rw [leftSquare]
        exact (matches_inclusion _ J.left (present o taken) pattern.1).mpr seen
    · intro b J o made
      obtain ⟨checks, patterns⟩ := clear.blindOutputs _ (liftJointAlong e J) o made
      have leftSquare := e.targetExtension.liftModel_square J.left
      have rightSquare := e.targetExtension.liftModel_square J.right
      rw [Inclusion.targetExtension_assignment] at leftSquare rightSquare
      refine ⟨fun check member sees => ?_, fun pattern member equal => ?_⟩
      · have carried : check.map (instantiate e.target) ∈ (e.firing f).toNative.prepared.rule.checks := by
          rw [checks_along]
          exact List.mem_map_of_mem member
        apply checks _ carried
        refine (seesOutput_map e.target _ _ (g.outputs o) check).mpr ?_
        change SeesOutput (Assignment.compose (e.targetExtension.liftModel J.left) e.target)
          (Assignment.compose (e.targetExtension.liftModel J.right) e.target) (g.outputs o) check
        rw [leftSquare, rightSquare]
        exact (seesOutput_inclusion _ J.left J.right (g.outputs o) check).mpr sees
      · have carried : (instantiate e.target pattern.1, pattern.2) ∈ (e.firing f).patterns :=
          List.mem_map_of_mem (f := fun pattern => (instantiate e.target pattern.1, pattern.2)) member
        apply patterns _ carried
        show instantiate (e.targetExtension.liftModel J.left) (instantiate e.target pattern.1) =
          instantiate (e.targetExtension.liftModel J.right) (instantiate e.target (g.outputs o))
        rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose, leftSquare, rightSquare,
          Assignment.instantiate_compose, Assignment.instantiate_compose, equal]

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Joint solvability carries along a dead-name extension**, in both directions. -/
theorem jointly_along (fs : List (LiveFiring s)) : Jointly s fs ↔ Jointly u (fs.map e.firing) := by
  constructor
  · rintro ⟨b, shared, each⟩
    rcases fs with _ | ⟨f₀, rest⟩
    · exact ⟨⟨u.state.Names, u.state.declarations⟩, generator _, fun _ member => absurd member List.not_mem_nil⟩
    · obtain ⟨σ₀, _, agree₀⟩ := each f₀ List.mem_cons_self
      refine ⟨⟨e.targetExtension.Complement ⊕ b.Names, extended e.targetExtension.complementDeclarations b.arity⟩,
        Assignment.compose (e.targetExtension.liftModel σ₀) (ContextualSelectionViews.capturedTarget u.locals u.state.declarations),
        fun f' member => ?_⟩
      obtain ⟨f, inFs, rfl⟩ := List.mem_map.mp member
      obtain ⟨σ, models, agree⟩ := each f inFs
      exact ⟨e.targetExtension.liftModel σ, (models_perm _ (e.information_firing f)).mpr
        ((ContextualConditionalNaturality.models_liftModel_iff e.targetExtension σ _).mpr models),
        lift_captured e σ σ₀ (agree.trans agree₀.symm)⟩
  · rintro ⟨b, shared, each⟩
    refine ⟨b, Assignment.compose shared e.frame, fun f member => ?_⟩
    obtain ⟨σ, models, agree⟩ := each (e.firing f) (List.mem_map_of_mem member)
    refine ⟨Assignment.compose σ e.target,
      (ContextualResidual.models_mapProblem _ _ _).mp ((models_perm _ (e.information_firing f)).mp models), ?_⟩
    rw [← Assignment.compose_associative, Inclusion.target_captured, Assignment.compose_associative, agree]

/-- **A family is clear exactly when its carrying is.** -/
theorem familyClear_along (fs : List (LiveFiring s)) : FamilyClear s fs ↔ FamilyClear u (fs.map e.firing) := by
  constructor
  · intro clear
    refine ⟨fun f' member => ?_, ?_, (jointly_along e fs).mp clear.jointly⟩
    · obtain ⟨f, inFs, rfl⟩ := List.mem_map.mp member
      exact (e.admits_iff f).mp (clear.admitted f inFs)
    · refine List.pairwise_map.mpr (clear.pairwise.imp_of_mem fun {f g} inF inG clears => ?_)
      exact ⟨(clear_along e (clear.admitted g inG)).mp clears.1, (clear_along e (clear.admitted f inF)).mp clears.2⟩
  · intro clear
    have admitted : ∀ f ∈ fs, f.toNative.Realized := fun f member =>
      (e.admits_iff f).mpr (clear.admitted (e.firing f) (List.mem_map_of_mem member))
    refine ⟨admitted, ?_, (jointly_along e fs).mpr clear.jointly⟩
    refine (List.pairwise_map.mp clear.pairwise).imp_of_mem fun {f g} inF inG clears => ?_
    exact ⟨(clear_along e (admitted g inG)).mpr clears.1, (clear_along e (admitted f inF)).mpr clears.2⟩

/-- **A concurrent step carries along a dead-name extension**, in both directions, with results that
agree up to dead names. -/
theorem concurrent_along (fs : List (LiveFiring s)) :
    (∀ {t : NativeState S O Γ sort}, Concurrent s (fs : Multiset (LiveFiring s)) t →
        ∃ t', Concurrent u ((fs.map e.firing : List (LiveFiring u)) : Multiset (LiveFiring u)) t' ∧ DeadEquiv t t') ∧
      ∀ {t' : NativeState S O Γ sort}, Concurrent u ((fs.map e.firing : List (LiveFiring u)) : Multiset (LiveFiring u)) t' →
        ∃ t, Concurrent s (fs : Multiset (LiveFiring s)) t ∧ DeadEquiv t t' := by
  constructor
  · intro t step
    obtain ⟨l, same, clear, run⟩ := step
    obtain ⟨t', run', agree⟩ := (NativeIterated.sequential_along _ e l rfl).1 run
    refine ⟨t', ⟨l.map e.firing, ?_, (familyClear_along e l).mp clear, run'⟩, agree⟩
    exact Multiset.coe_eq_coe.mpr ((Multiset.coe_eq_coe.mp same).map _)
  · intro t' step
    obtain ⟨t'', run, agree⟩ := step.agrees rfl
    obtain ⟨_, same, clear, _⟩ := step
    have clearMapped : FamilyClear u (fs.map e.firing) := clear.perm (Multiset.coe_eq_coe.mp same).symm
    obtain ⟨t, run', agree'⟩ := (NativeIterated.sequential_along _ e fs rfl).2 run
    exact ⟨t, ⟨fs, rfl, (familyClear_along e fs).mpr clearMapped, run'⟩, agree'.trans agree.symm⟩

variable {L : Type}

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- An offered word at the larger state is carried from an offered word with the same labels. -/
theorem pull_offered {program : L → (v : NativeState S O Γ sort) → LiveFiring v → Prop}
    (invariant : DeadInvariant program) :
    ∀ (w : List (L × LiveFiring u)), (∀ x ∈ w, program x.1 u x.2) →
      ∃ w' : List (L × LiveFiring s), (∀ x ∈ w', program x.1 s x.2) ∧ w'.map Prod.fst = w.map Prod.fst ∧
        (w'.map Prod.snd).map e.firing = w.map Prod.snd
  | [], _ => ⟨[], fun _ member => absurd member List.not_mem_nil, rfl, rfl⟩
  | x :: rest, offered => by
      obtain ⟨f, offeredF, carried⟩ := (invariant e x.1).2 x.2 (offered x List.mem_cons_self)
      obtain ⟨w', offered', labels, carries⟩ :=
        pull_offered invariant rest fun y member => offered y (List.mem_cons_of_mem _ member)
      refine ⟨(x.1, f) :: w', ?_, by rw [List.map_cons, List.map_cons, labels], ?_⟩
      · intro y member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact offeredF
        · exact offered' y inRest
      · rw [List.map_cons, List.map_cons, List.map_cons, carries, carried]

end NativeConcurrent

/-- **Agreement up to dead names is a bisimulation of the native concurrent step.** At two states that
agree up to dead names, for a program that does not see dead names, a concurrent step of an offered
clear word at the first is matched at the second by a concurrent step of an offered clear word with the
same labels, and the two results agree up to dead names. -/
theorem NativeConcurrent.concurrent_bisimulation {L : Type}
    {program : L → (v : NativeState S O Γ sort) → LiveFiring v → Prop} (invariant : DeadInvariant program)
    {s s' : NativeState S O Γ sort} (same : DeadEquiv s s') {w : List (L × LiveFiring s)}
    (offered : ∀ x ∈ w, program x.1 s x.2) {t : NativeState S O Γ sort}
    (step : NativeConcurrent.Concurrent s ((w.map Prod.snd : List (LiveFiring s)) : Multiset (LiveFiring s)) t) :
    ∃ w' : List (L × LiveFiring s'), (∀ x ∈ w', program x.1 s' x.2) ∧ w'.map Prod.fst = w.map Prod.fst ∧
      ∃ t', NativeConcurrent.Concurrent s' ((w'.map Prod.snd : List (LiveFiring s')) : Multiset (LiveFiring s')) t' ∧
        DeadEquiv t t' := by
  obtain ⟨u, ⟨e⟩, ⟨e'⟩⟩ := same
  obtain ⟨t₁, step₁, agree₁⟩ := (NativeConcurrent.concurrent_along e (w.map Prod.snd)).1 step
  have offeredU : ∀ x ∈ w.map (fun x => (x.1, e.firing x.2)), program x.1 u x.2 := by
    intro x member
    obtain ⟨y, inW, rfl⟩ := List.mem_map.mp member
    exact (invariant e y.1).1 y.2 (offered y inW)
  obtain ⟨w', offered', labels, carries⟩ := NativeConcurrent.pull_offered e' invariant _ offeredU
  have carried : (w'.map Prod.snd).map e'.firing = (w.map Prod.snd).map e.firing := by
    rw [carries, List.map_map, List.map_map]
    rfl
  rw [← carried] at step₁
  obtain ⟨t', step', agree'⟩ := (NativeConcurrent.concurrent_along e' (w'.map Prod.snd)).2 step₁
  refine ⟨w', offered', ?_, t', step', agree₁.trans agree'.symm⟩
  rw [labels, List.map_map]
  rfl

#print axioms NativeConcurrent.liftModel_congr
#print axioms NativeConcurrent.lift_captured
#print axioms NativeConcurrent.matches_along
#print axioms NativeConcurrent.matches_inclusion
#print axioms NativeConcurrent.clear_along
#print axioms NativeConcurrent.jointly_along
#print axioms NativeConcurrent.familyClear_along
#print axioms NativeConcurrent.concurrent_along
#print axioms NativeConcurrent.concurrent_bisimulation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
