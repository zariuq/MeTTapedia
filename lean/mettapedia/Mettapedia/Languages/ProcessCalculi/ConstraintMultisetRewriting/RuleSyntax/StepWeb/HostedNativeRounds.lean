import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketRounds

/-!
# Hosted firings at the entry of the native round construction

The round construction of `Step/Bridges/Concurrency/NativePacketRounds` starts from one native state and
a finite family of live firings at it. With the adapter of `HostedNative`, a family of canonical
hosted firings at one presented hosted state is such a family. The constructions compared are those
of `HostedNative`: the contextual rule-syntax step (a bag store of labelled occurrences; one match per
step; guards asked after the firing's own tells; the program a fixed set of rules beside the store; one
knowledge store) and the native step on live firings (a bag store of conditional rows; one match per
step, opened at reserved scopes; guards and queries asked after the firing's own tells; the rule carried
by the firing, its unknowns in the private family; one knowledge store).

* `packet_admission_iff`: a member of the packet family that is the live firing of an unguarded
  canonical hosted firing is admitted at the family's packet source exactly when the hosted firing is
  admitted (`NativePacketRounds.member_admission_iff`, composed with `HostedNative.admits_iff`).
* `HostedJointly`: one solution of the hosted state's names extends to a solution of each hosted
  firing's information; `jointly_iff`: it is `NativeIterated.Jointly` of the live firings. Each member
  keeps its own solution of its own unknowns; only the state's names are shared.
* `packet_consistent_iff`: so the packet family's joint problem is consistent exactly when the hosted
  firings are jointly solvable (`NativePacketRounds.consistent_iff_jointly`, composed).

## Runs

* `HostedRun`: the members' canonical firings in order, each at the hosted result of the one before,
  the presentation carried by `resultPresented` and the scope ledger advanced as the native step
  advances it (`nextLedger`).
* `sequential_iff`: **hosted runs are native sequential runs up to dead names**: a family runs in the
  native step from the adapted state (`NativeIterated.Sequential`) exactly when it runs in the hosted
  step, and the final native state agrees with the adapted final hosted state up to dead names
  (`NativeDead.DeadEquiv`). The proof composes the result law, the residual law
  (`residuals_eq`) and `NativeIterated.sequential_along`.
* `every_order_hosted`: every order of a clear family runs in the hosted step, all ending in states that
  agree up to dead names (`NativeIterated.every_order_agrees`, read back). Clearness is the native
  condition on the live firings.
* `familyClear_of_hosted`, `every_order_of_apart`: for unguarded rules clearness is hosted: each member
  admitted, the selections pairwise physically apart (`Apart`), and the family jointly solvable
  (`HostedJointly`). So execution in every order follows from these hosted conditions. Guarded rules
  (`unmatched`) need the native blindness conditions of `Clear`, which are not restated here.
* `no_order_hosted`: a family with no inner causal dependence that is not jointly solvable in the hosted
  reading has no hosted run in any order (`NativeIterated.no_order_of_not_jointly`, read back).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative.Rounds

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open Interface (NativeState LiveFiring native)
open Interface.Frames (Frame)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open SourceLanguage Hosting Hosting.Alternatives

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} {κ : Keys S}

/-! ## Members -/

variable (Γ star κ) in
/-- **A member of a hosted family**: a rule of the program, placed, with its selection and budget. -/
structure Member (P : CProgram S) where
  rule : CRule S
  member : rule ∈ P
  placed : Placed Γ star κ rule
  selection : Selection ℕ
  fuel : ℕ

/-- The member's canonical hosted firing. -/
def Member.hosted {P : CProgram S} (m : Member Γ star κ P) (s : HostState S) :
    RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) P s.frame :=
  RuleSyntax.Contextual.canonical (F := s.frame) m.rule m.member m.selection []

/-- The member's live firing. -/
noncomputable def Member.live {P : CProgram S} (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s)
    (occupied : Finset ℕ) (m : Member Γ star κ P) : LiveFiring (state κ s p occupied) :=
  HostedNative.live N s p occupied m.placed m.selection m.fuel

/-! ## Joint solvability -/

/-- **The hosted reading of joint solvability**: one solution of the state's names extends to a
solution of each firing's information. -/
def HostedJointly {P : CProgram S} (s : HostState S)
    (fs : List (RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) P s.frame)) : Prop :=
  ∃ (b : Frame S) (shared : Assignment s.frame.arity b.arity), ∀ f ∈ fs,
    ∃ σ : Assignment ((RuleSyntax.Contextual.declarations S).target f.ext).arity b.arity,
      (Interface.Frames.contextual S).Models σ (f.information (Interface.Frames.contextual S) s) ∧
        Assignment.compose σ ((RuleSyntax.Contextual.declarations S).weaken f.ext) = shared

/-- The complement of an extension's image, widened to all of its names. -/
def widen {V : Type} {source : V → MetaArity S} (extension : ContextualGuardMatching.Extension source)
    {W : Type} (next : W → MetaArity S) :
    Assignment (ContextualPrefixModels.extended extension.complementDeclarations next)
      (ContextualPrefixModels.extended extension.declarations next) :=
  reindex (Sum.map Subtype.val id) fun name => by cases name <;> rfl

theorem widen_inclusion {V : Type} {source : V → MetaArity S} (extension : ContextualGuardMatching.Extension source)
    {W : Type} (next : W → MetaArity S) :
    Assignment.compose (widen extension next) (ContextualPrefixModels.inclusion extension.complementDeclarations next) =
      ContextualPrefixModels.inclusion extension.declarations next := by
  funext name
  change instantiate (widen extension next) (generator _ (Sum.inr name)) = generator _ (Sum.inr name)
  rw [instantiate_generator]
  rfl

section Joint

variable [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Joint solvability of the live firings is joint solvability of the hosted firings.** -/
theorem jointly_iff {P : CProgram S} (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s)
    (occupied : Finset ℕ) (ms : List (Member Γ star κ P)) :
    Interface.NativeIterated.Jointly (state κ s p occupied) (ms.map (Member.live N s p occupied)) ↔
      HostedJointly s (ms.map (Member.hosted · s)) := by
  constructor
  · rintro ⟨b, shared, each⟩
    refine ⟨b, shared, fun f inside => ?_⟩
    obtain ⟨m, insideM, rfl⟩ := List.mem_map.mp inside
    obtain ⟨σ, solved, agrees⟩ := each _ (List.mem_map_of_mem insideM)
    change ContextualResidual.Models σ (live N s p occupied m.placed m.selection m.fuel).toNative.information at solved
    rw [information_eq N s p occupied m.member m.placed m.selection m.fuel] at solved
    refine ⟨Assignment.compose σ (infoExtension m.placed s.frame (ruleScope occupied m.selection)).assignment,
      (ContextualResidual.models_mapProblem _ _ _).mp solved, ?_⟩
    change Assignment.compose (Assignment.compose σ _) (RuleSyntax.Contextual.weakenNames S s.frame m.rule.locals) = shared
    rw [← Assignment.compose_associative, info_weaken]
    exact agrees
  · rintro ⟨b, shared, each⟩
    refine ⟨⟨_, ContextualPrefixModels.extended (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity)
      b.arity⟩, Assignment.compose (ContextualPrefixModels.inclusion
        (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity) b.arity) shared, fun f inside => ?_⟩
    obtain ⟨m, insideM, rfl⟩ := List.mem_map.mp inside
    obtain ⟨σ, solved, agrees⟩ := each _ (List.mem_map_of_mem insideM)
    refine ⟨Assignment.compose (widen (infoExtension m.placed s.frame (ruleScope occupied m.selection)) b.arity)
      ((infoExtension m.placed s.frame (ruleScope occupied m.selection)).liftModel σ), ?_, ?_⟩
    · change ContextualResidual.Models _ (live N s p occupied m.placed m.selection m.fuel).toNative.information
      rw [information_eq N s p occupied m.member m.placed m.selection m.fuel]
      exact ContextualResidual.models_compose
        ((ContextualConditionalNaturality.models_liftModel_iff
          (infoExtension m.placed s.frame (ruleScope occupied m.selection)) σ _).mpr solved) _
    · change Assignment.compose σ (RuleSyntax.Contextual.weakenNames S s.frame m.rule.locals) = shared at agrees
      show Assignment.compose
          (Assignment.compose (widen (infoExtension m.placed s.frame (ruleScope occupied m.selection)) b.arity)
            ((infoExtension m.placed s.frame (ruleScope occupied m.selection)).liftModel σ))
          (ContextualSelectionViews.capturedTarget (ruleLocals Γ star κ) s.frame.arity) =
        Assignment.compose (ContextualPrefixModels.inclusion
          (ContextualActivatedStep.target (ruleLocals Γ star κ) s.frame.arity) b.arity) shared
      rw [← info_weaken m.placed s.frame (ruleScope occupied m.selection), Assignment.compose_associative,
        ← Assignment.compose_associative _ _ (widen _ b.arity), ContextualGuardMatching.Extension.liftModel_square,
        Assignment.compose_associative, ← Assignment.compose_associative, agrees]
      exact congrArg (fun first => Assignment.compose first shared)
        (widen_inclusion (infoExtension m.placed s.frame (ruleScope occupied m.selection)) b.arity)

/-! ## Round entry -/

/-- **Round entry, admission.** A member of the packet family that is the live firing of an unguarded
canonical hosted firing is admitted at the family's packet source exactly when the hosted firing is
admitted. `shapes` is the native shape condition of the packet theorem. -/
theorem packet_admission_iff (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ)
    {P : CProgram S} {r : CRule S} (member : r ∈ P) (pl : Placed Γ star κ r) (selection : Selection ℕ) (fuel : ℕ)
    (members : List (LiveFiring (state κ s p occupied))) (index : Fin members.length)
    (adapted : members[index] = live N s p occupied pl selection fuel)
    (shapes : native.Shapes (live N s p occupied pl selection fuel).toNative)
    (unguarded : pl.body.checks = []) :
    (Interface.Bridges.Concurrency.NativePacketRounds.member members index).firing.Admits
        (RuleSyntax.OneFrame.frames
          (Interface.Bridges.Concurrency.NativePacketStep.packetAction (S := S) (O := ℕ) (Γ := Γ) (sort := star)))
        (Interface.Bridges.Concurrency.NativePacketRounds.source members) ↔
      (RuleSyntax.Contextual.canonical (F := s.frame) r member selection []).Admits (Interface.Frames.contextual S) s := by
  have noChecks : members[index].rule.checks = [] := by
    rw [adapted]
    change pl.body.checks.map _ = []
    rw [unguarded]
    rfl
  have noQueries : members[index].patterns = [] := by
    rw [adapted]
    rfl
  have shaped : native.Shapes members[index].toNative := by
    rw [adapted]
    exact shapes
  rw [Interface.Bridges.Concurrency.NativePacketRounds.member_admission_iff members index shaped noChecks noQueries,
    adapted]
  exact (admits_iff N s p occupied member pl selection fuel).symm

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Round entry, joint consistency.** The packet family of a nonempty hosted family, every member
physically enabled, has a consistent joint problem exactly when the hosted firings are jointly
solvable. -/
theorem packet_consistent_iff {P : CProgram S} (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s)
    (occupied : Finset ℕ) (ms : List (Member Γ star κ P)) (nonempty : ms ≠ [])
    (enabled : ∀ index : Fin (ms.map (Member.live N s p occupied)).length,
      Enabled (fun _ : ℕ => ()) s.present
        ((ms.map (Member.live N s p occupied))[index].selection.commit (T := Unit))) :
    (Interface.Bridges.Concurrency.NativePacketStep.packetAction (S := S) (O := ℕ) (Γ := Γ) (sort := star)).Consistent
        (Interface.Bridges.Concurrency.NativePacketRounds.jointProblem (ms.map (Member.live N s p occupied))) ↔
      HostedJointly s (ms.map (Member.hosted · s)) :=
  (Interface.Bridges.Concurrency.NativePacketRounds.consistent_iff_jointly _
    (fun empty => nonempty (List.map_eq_nil_iff.mp empty)) enabled).trans (jointly_iff N s p occupied ms)

/-! ## Runs -/

/-- The scope ledger after a step with a selection: the native step's reservation and helper scope. -/
abbrev nextLedger (occupied : Finset ℕ) (selection : Selection ℕ) : Finset ℕ :=
  ContextualFreshFrameScopeLedger.helperLedger (ContextualActivationScopes.after occupied selection)

/-- **A hosted run of a family**: the members' canonical firings in order, each admitted at the hosted
result of the one before, with the presentation carried along and the ledger advanced as the native
step advances it. -/
inductive HostedRun {P : CProgram S} :
    (s : HostState S) → Presented Γ star s → Finset ℕ → List (Member Γ star κ P) →
      (t : HostState S) → Presented Γ star t → Finset ℕ → Prop
  | nil (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ) : HostedRun s p occupied [] s p occupied
  | cons {s : HostState S} {p : Presented Γ star s} {occupied : Finset ℕ} (m : Member Γ star κ P)
      (rest : List (Member Γ star κ P)) (admitted : (m.hosted s).Admits (Interface.Frames.contextual S) s)
      {t : HostState S} {q : Presented Γ star t} {final : Finset ℕ}
      (later : HostedRun ((m.hosted s).result (Interface.Frames.contextual S) s)
        (resultPresented s p m.member m.placed m.selection) (nextLedger occupied m.selection) rest t q final) :
      HostedRun s p occupied (m :: rest) t q final

/-- The residuals after a member's step are the rest's live firings at the hosted result, carried. -/
theorem residuals_eq {P : CProgram S} (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s)
    (occupied : Finset ℕ) (m : Member Γ star κ P) (rest : List (Member Γ star κ P))
    (realized : (Member.live N s p occupied m).toNative.Realized) :
    (rest.map (Member.live N s p occupied)).map (Interface.NativeIterated.residualAfter realized) =
      (rest.map (Member.live N ((m.hosted s).result (Interface.Frames.contextual S) s)
          (resultPresented s p m.member m.placed m.selection)
          (native.result (Member.live N s p occupied m).toNative realized).state.occupied)).map
        (resultExtension N s p occupied m.member m.placed m.selection m.fuel realized).firing := by
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun m₂ _ =>
    residual_eq N s p occupied m.member m.placed m.selection m.fuel realized m₂.placed m₂.selection m₂.fuel

/-- **Hosted runs are native sequential runs, up to dead names.** A family of members at a presented
hosted state runs sequentially in the native step from the adapted state exactly when it runs in the
hosted step, and the final native state agrees up to dead names with the adapted final hosted state. -/
theorem sequential_iff {P : CProgram S} (N : Nodes S Γ star) (ms : List (Member Γ star κ P)) :
    ∀ (s : HostState S) (p : Presented Γ star s) (occupied : Finset ℕ),
      (∀ {u : NativeState S ℕ Γ star},
        Interface.NativeIterated.Sequential (state κ s p occupied) (ms.map (Member.live N s p occupied)) u →
          ∃ (t : HostState S) (q : Presented Γ star t) (final : Finset ℕ), HostedRun s p occupied ms t q final ∧
            Interface.NativeDead.DeadEquiv (state κ t q final) u) ∧
      (∀ {t : HostState S} {q : Presented Γ star t} {final : Finset ℕ}, HostedRun s p occupied ms t q final →
        ∃ u : NativeState S ℕ Γ star,
          Interface.NativeIterated.Sequential (state κ s p occupied) (ms.map (Member.live N s p occupied)) u ∧
            Interface.NativeDead.DeadEquiv (state κ t q final) u) := by
  induction ms with
  | nil =>
      intro s p occupied
      refine ⟨fun {u} run => ⟨s, p, occupied, .nil s p occupied, ?_⟩, fun {t q final} run => ?_⟩
      · rw [Interface.NativeIterated.sequential_nil_iff.mp run]
        exact Interface.NativeDead.DeadEquiv.refl _
      · cases run
        exact ⟨_, .nil _, Interface.NativeDead.DeadEquiv.refl _⟩
  | cons m rest ih =>
      intro s p occupied
      constructor
      · intro u run
        obtain ⟨realized, later⟩ := Interface.NativeIterated.sequential_cons_iff.mp run
        rw [residuals_eq N s p occupied m rest realized] at later
        obtain ⟨u₀, run₀, agree₀⟩ := (Interface.NativeIterated.sequential_along _
          (resultExtension N s p occupied m.member m.placed m.selection m.fuel realized) _ rfl).2 later
        obtain ⟨t, q, final, hosted, agree⟩ := (ih _ _ _).1 run₀
        exact ⟨t, q, final,
          .cons m rest ((admits_iff N s p occupied m.member m.placed m.selection m.fuel).mpr realized) hosted,
          agree.trans agree₀⟩
      · intro t q final run
        cases run with
        | cons _ _ admitted later =>
            have realized : (Member.live N s p occupied m).toNative.Realized :=
              (admits_iff N s p occupied m.member m.placed m.selection m.fuel).mp admitted
            obtain ⟨u₀, run₀, agree₀⟩ := (ih _ _ _).2 later
            obtain ⟨u, runCarried, agree⟩ := (Interface.NativeIterated.sequential_along _
              (resultExtension N s p occupied m.member m.placed m.selection m.fuel realized) _ rfl).1 run₀
            have runResiduals : Interface.NativeIterated.Sequential
                (native.result (Member.live N s p occupied m).toNative realized)
                ((rest.map (Member.live N s p occupied)).map (Interface.NativeIterated.residualAfter realized)) u := by
              rw [residuals_eq N s p occupied m rest realized]
              exact runCarried
            exact ⟨u, .cons _ _ realized runResiduals, agree₀.trans agree⟩

/-- **Every order of a clear family runs in the hosted step**, and all orders end in states that agree up to
dead names: `NativeIterated.every_order_agrees` on the live firings, read back through `sequential_iff`.
Clearness is the native condition on the live firings; its joint-solvability part is `HostedJointly`
(`jointly_iff`). -/
theorem every_order_hosted {P : CProgram S} (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s)
    (occupied : Finset ℕ) (ms : List (Member Γ star κ P))
    (clear : Interface.NativeIterated.FamilyClear (state κ s p occupied) (ms.map (Member.live N s p occupied))) :
    ∃ (t : HostState S) (q : Presented Γ star t) (final : Finset ℕ), HostedRun s p occupied ms t q final ∧
      ∀ order : List (Member Γ star κ P), order.Perm ms →
        ∃ (t' : HostState S) (q' : Presented Γ star t') (final' : Finset ℕ), HostedRun s p occupied order t' q' final' ∧
          Interface.NativeDead.DeadEquiv (state κ t q final) (state κ t' q' final') := by
  obtain ⟨u₀, run₀, every⟩ := Interface.NativeIterated.every_order_agrees clear
  obtain ⟨t, q, final, hosted, agree⟩ := (sequential_iff N ms s p occupied).1 run₀
  refine ⟨t, q, final, hosted, fun order perm => ?_⟩
  obtain ⟨u, run, agreeOrder⟩ := every _ (perm.map _)
  obtain ⟨t', q', final', hosted', agree'⟩ := (sequential_iff N order s p occupied).1 run
  exact ⟨t', q', final', hosted', (agree.trans agreeOrder).trans agree'.symm⟩

/-- **Two selections are physically apart**: disjoint takes, disjoint made identities, and neither takes
what the other reads. -/
def Apart (first second : Selection ℕ) : Prop :=
  Disjoint first.taken.toFinset second.taken.toFinset ∧ Disjoint first.made.toFinset second.made.toFinset ∧
    Disjoint second.taken.toFinset first.read.toFinset ∧ Disjoint first.taken.toFinset second.read.toFinset

/-- **An unguarded hosted family is clear** when each member's canonical firing is admitted, the members'
selections are pairwise apart, and the family is jointly solvable in the hosted reading. The live firings
of unguarded rules carry no guard and no query, so blindness holds vacuously. -/
theorem familyClear_of_hosted {P : CProgram S} (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s)
    (occupied : Finset ℕ) (ms : List (Member Γ star κ P))
    (unguarded : ∀ m ∈ ms, m.placed.body.checks = [])
    (admitted : ∀ m ∈ ms, (m.hosted s).Admits (Interface.Frames.contextual S) s)
    (apart : ms.Pairwise fun m m' => Apart m.selection m'.selection)
    (jointly : HostedJointly s (ms.map (Member.hosted · s))) :
    Interface.NativeIterated.FamilyClear (state κ s p occupied) (ms.map (Member.live N s p occupied)) := by
  have native := (jointly_iff N s p occupied ms).mpr jointly
  have noChecks : ∀ m ∈ ms, (Member.live N s p occupied m).toNative.prepared.rule.checks = [] := by
    intro m inside
    change (m.placed.body.checks.map _).map _ = []
    rw [unguarded m inside]
    rfl
  refine ⟨fun f inside => ?_, ?_, native⟩
  · obtain ⟨m, insideM, rfl⟩ := List.mem_map.mp inside
    exact (admits_iff N s p occupied m.member m.placed m.selection m.fuel).mp (admitted m insideM)
  · refine List.pairwise_map.mpr (List.Pairwise.imp_of_mem ?_ apart)
    intro m m' insideM insideM' separated
    obtain ⟨takes, ports, keeps, keeps'⟩ := separated
    have inF := List.mem_map_of_mem (f := Member.live N s p occupied) insideM
    have inG := List.mem_map_of_mem (f := Member.live N s p occupied) insideM'
    have jointFG := Interface.NativeIterated.Jointly.joint native inF inG
    have jointGF := Interface.NativeIterated.Jointly.joint native inG inF
    constructor
    · constructor
      · exact takes
      · exact ports
      · exact keeps
      · exact jointFG
      · intro b J o _
        refine ⟨fun check inside => ?_, fun pattern inside => by cases inside⟩
        rw [noChecks m insideM] at inside
        cases inside
      · intro b J o _
        refine ⟨fun check inside => ?_, fun pattern inside => by cases inside⟩
        rw [noChecks m insideM] at inside
        cases inside
    · constructor
      · exact takes.symm
      · exact ports.symm
      · exact keeps'
      · exact jointGF
      · intro b J o _
        refine ⟨fun check inside => ?_, fun pattern inside => by cases inside⟩
        rw [noChecks m' insideM'] at inside
        cases inside
      · intro b J o _
        refine ⟨fun check inside => ?_, fun pattern inside => by cases inside⟩
        rw [noChecks m' insideM'] at inside
        cases inside

/-- **Execution in every order from compatibility and joint solvability, in hosted terms.** For an
unguarded hosted family whose members are admitted, physically apart and jointly solvable, every order
of the family is a hosted run, and all orders end in states that agree up to dead names. -/
theorem every_order_of_apart {P : CProgram S} (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s)
    (occupied : Finset ℕ) (ms : List (Member Γ star κ P))
    (unguarded : ∀ m ∈ ms, m.placed.body.checks = [])
    (admitted : ∀ m ∈ ms, (m.hosted s).Admits (Interface.Frames.contextual S) s)
    (apart : ms.Pairwise fun m m' => Apart m.selection m'.selection)
    (jointly : HostedJointly s (ms.map (Member.hosted · s))) :
    ∃ (t : HostState S) (q : Presented Γ star t) (final : Finset ℕ), HostedRun s p occupied ms t q final ∧
      ∀ order : List (Member Γ star κ P), order.Perm ms →
        ∃ (t' : HostState S) (q' : Presented Γ star t') (final' : Finset ℕ), HostedRun s p occupied order t' q' final' ∧
          Interface.NativeDead.DeadEquiv (state κ t q final) (state κ t' q' final') :=
  every_order_hosted N s p occupied ms (familyClear_of_hosted N s p occupied ms unguarded admitted apart jointly)

/-- **Without joint solvability no order runs**: a family whose live firings take and read nothing any
of them makes, and that is not jointly solvable in the hosted reading, has no hosted run in any order. -/
theorem no_order_hosted {P : CProgram S} (N : Nodes S Γ star) (s : HostState S) (p : Presented Γ star s)
    (occupied : Finset ℕ) (ms : List (Member Γ star κ P))
    (unmade : Interface.NativeIterated.Unmade (ms.map (Member.live N s p occupied)))
    (notJointly : ¬ HostedJointly s (ms.map (Member.hosted · s))) {order : List (Member Γ star κ P)}
    (perm : order.Perm ms) {t : HostState S} {q : Presented Γ star t} {final : Finset ℕ} :
    ¬ HostedRun s p occupied order t q final := by
  intro hosted
  obtain ⟨u, run, _⟩ := (sequential_iff N order s p occupied).2 hosted
  exact Interface.NativeIterated.no_order_of_not_jointly unmade
    (fun jointly => notJointly ((jointly_iff N s p occupied ms).mp jointly)) (perm.map _) run

end Joint

#print axioms every_order_hosted
#print axioms familyClear_of_hosted
#print axioms every_order_of_apart
#print axioms no_order_hosted
#print axioms residuals_eq
#print axioms sequential_iff
#print axioms widen_inclusion
#print axioms jointly_iff
#print axioms packet_admission_iff
#print axioms packet_consistent_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.HostedNative.Rounds
