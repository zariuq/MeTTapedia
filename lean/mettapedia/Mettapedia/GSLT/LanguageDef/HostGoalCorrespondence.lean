import Mettapedia.GSLT.LanguageDef.HostGoalMachine

/-!
# The two runs of a host goal

`DestinationPassingRefinement` relates the output-at-return and output-first
runs of a query that has no destination and no context: `FramesRel` ends in
`FramesRel.nil`, with no destination and every valuation allowed.  A host goal
starts at a call site of the tier.  On the output-first side it carries a
destination `goalDest`, the instance of the call's pattern, and its store `σF`
is the reference store `σA` refined by a context `Q`: the solutions of `σF`
are those of `σA` intersected with `Q`, the equations the output-first side
has made ahead.  This module relates the two runs of such a goal.

**The correspondence.**  `GoalFrames goalDest Q` is `FramesRel` whose last
level is the goal itself, owing its destination and its context
(`GoalFrames.base`).  `GoalRelated` and `GoalDoomed` are `Related` and `Doomed`
over it.  With no destination and no context they are the existing relations
(`goalFrames_of_framesRel`, `goalRelated_of_related`, `goalDoomed_of_doomed`).
The local work of a task is related as before, by `inspect_related` and
`inspect_doomed`.  What changes is the base.  A return there is an answer of
the goal: both runs deliver it, the output-first store being the reference's
intersected with the destination meeting the value and with `Q`
(`AnswerRel`), or the reference delivers an answer with no solution there,
which the output-first run never delivers (`AnswerOmitted`).  A doomed
reference task may therefore deliver an answer, and every answer it delivers
is omitted.

**Expansion laws.**  `goal_expand_related`: corresponding tasks, the reference
task moded, expand to corresponding tasks (`Embeds GoalRelated GoalDoomed`) and
to answers related by `Embeds AnswerRel AnswerOmitted`.  `goal_expand_doomed`:
a doomed task yields doomed tasks and omitted answers only.  They rest on
`goal_activations_embed`, `goal_activations_doomed`, `goal_successors_related`
and `goal_successors_doomed`.  These are `activations_embed`,
`activations_doomed`, `successors_related` and `successors_doomed`, whose
statements fix `FramesRel`, proved again for the goal's base; only the base
cases differ.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals

open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.HostCalls

section Correspondence

variable {Term Store Rel Op : Type}
variable (L : TemplateLanguage Term) {S : StoreAlgebra Term Store Op} (X : ExactStore S)
variable [Inhabited Term]

/-- The return stacks of a host goal's two runs: `FramesRel` over the goal's
destination `goalDest` and context `Q`, where `FramesRel` has no destination
and no context.  The index is the destination of the code running above, and
the set the equations that the frames' levels and the goal still owe. -/
inductive GoalFrames (goalDest : Option Term) (Q : Set X.Valuation) :
    Option Term → List (ReturnFrame L Rel Op) → List (DestFrame L Rel Op) →
      Set X.Valuation → Prop
  | base : GoalFrames goalDest Q goalDest [] [] Q
  | cons {k : Nat} (p : L.Tmpl k) {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
      (captured : Fin k → Option Term) (origin : Fin k → Term) (dest : Option Term)
      {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
      (ahead : BindsAhead L E late early)
      (agrees : ∀ i ∈ late.support L, reconstruct captured i = origin i)
      (rest : GoalFrames goalDest Q dest fs gs P) :
      GoalFrames goalDest Q (some (L.inst p (reconstruct captured)))
        (⟨k, p, late, captured⟩ :: fs) (⟨⟨k, p, early, captured⟩, dest⟩ :: gs)
        (pending L X E origin late (reconstruct captured) dest ∩ P)

/-- Corresponding tasks of a host goal's two runs: `Related`, over the goal's
return stacks. -/
inductive GoalRelated (goalDest : Option Term) (Q : Set X.Valuation) :
    Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) →
      Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op) → Prop
  | mk {k : Nat} {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
      (frame origin : Fin k → Term) (σA σF : Store) (dest : Option Term)
      {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
      (ahead : BindsAhead L E late early) (agrees : ∀ i ∈ late.support L, frame i = origin i)
      (frames : GoalFrames L X goalDest Q dest fs gs P) (goodA : X.WellFormed σA)
      (goodF : X.WellFormed σF)
      (sols : X.solutions σF = X.solutions σA ∩ pending L X E origin late frame dest ∩ P)
      (keys : X.supply σF = X.supply σA) :
      GoalRelated goalDest Q ⟨(), ⟨k, late, frame, σA⟩, fs⟩
        ⟨(), ⟨⟨k, early, frame, σF⟩, dest⟩, gs⟩

/-- A reference task of a host goal that can deliver no answer with a solution
in the goal's context and against its destination: `Doomed`, over the goal's
return stacks. -/
inductive GoalDoomed (goalDest : Option Term) (Q : Set X.Valuation) :
    Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op) → Prop
  | failing {k : Nat} (frame : Fin k → Term) (σ : Store) (fs : List (ReturnFrame L Rel Op)) :
      GoalDoomed goalDest Q ⟨(), ⟨k, .fail, frame, σ⟩, fs⟩
  | unsatisfiable {k : Nat} {E : List (L.Tmpl k × L.Tmpl k)} {late early : Code L Rel Op k}
      (frame origin : Fin k → Term) (σ : Store) (dest : Option Term)
      {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
      (ahead : BindsAhead L E late early) (agrees : ∀ i ∈ late.support L, frame i = origin i)
      (frames : GoalFrames L X goalDest Q dest fs gs P) (good : X.WellFormed σ)
      (empty : X.solutions σ ∩ pending L X E origin late frame dest ∩ P = ∅) :
      GoalDoomed goalDest Q ⟨(), ⟨k, late, frame, σ⟩, fs⟩

variable {L X}

/-- `FramesRel` is the goal's return stacks for no destination and no context. -/
theorem goalFrames_of_framesRel {dest : Option Term} {fs : List (ReturnFrame L Rel Op)}
    {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation} (frames : FramesRel L X dest fs gs P) :
    GoalFrames L X none Set.univ dest fs gs P := by
  induction frames with
  | nil => exact .base
  | cons p captured origin dest ahead agrees _ ih =>
      exact .cons p captured origin dest ahead agrees ih

theorem goalRelated_of_related
    {tA : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    {tF : Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op)}
    (related : Related L X tA tF) : GoalRelated L X none Set.univ tA tF := by
  cases related with
  | mk frame origin σA σF dest ahead agrees frames goodA goodF sols keys =>
      exact .mk frame origin σA σF dest ahead agrees (goalFrames_of_framesRel frames) goodA goodF
        sols keys

theorem goalDoomed_of_doomed {t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    (doomed : Doomed L X t) : GoalDoomed L X none Set.univ t := by
  cases doomed with
  | failing frame σ fs => exact .failing frame σ fs
  | unsatisfiable frame origin σ dest ahead agrees frames good empty =>
      exact .unsatisfiable frame origin σ dest ahead agrees (goalFrames_of_framesRel frames) good
        empty

end Correspondence

/-! ## Expansion laws -/

section Expansion

variable {Term Store Rel Op : Type}
variable {L : TemplateLanguage Term} {S : StoreAlgebra Term Store Op} {X : ExactStore S}
variable [Inhabited Term] [DecidableEq Rel] {PA PF : EqProgram L Rel Op}
  {goalDest : Option Term} {Q : Set X.Valuation}

/-- The activations of one call on the two sides of a goal's runs: an equation
the reference activates is activated on the output-first side and the tasks
correspond, or it is not and the reference task is doomed.  This is
`activations_embed` over the goal's return stacks. -/
theorem goal_activations_embed (aligned : ProgramBindsAhead L PA PF)
    (rel : Rel) (args : List Term) (σA σF : Store) (goodA : X.WellFormed σA)
    (goodF : X.WellFormed σF) (keys : X.supply σF = X.supply σA) (dest : Option Term)
    {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
    (frames : GoalFrames L X goalDest Q dest fs gs P)
    (sols : X.solutions σF = X.solutions σA ∩ P) :
    Embeds (GoalRelated L X goalDest Q) (GoalDoomed L X goalDest Q)
      ((activate L S PA (rel, args, σA)).map fun a =>
        (⟨(), ⟨a.slots, a.code, a.frame, a.store⟩, fs⟩ :
          Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)))
      ((activateOut L S PF (rel, args, σF, dest)).map fun a =>
        (⟨(), a, gs⟩ : Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op))) := by
  simp only [activate, activateOut, List.map_filterMap]
  refine embeds_filterMap _ _ ?_ (aligned.equations rel)
  intro eA eF related
  cases related with
  | @mk k params late early ahead =>
  obtain ⟨sameFrame, sameKey⟩ := X.fresh_supply k keys.symm
  obtain ⟨acceptA, rejectA⟩ :=
    unifyAll_exact X (instArgs L params (S.fresh σA k).1) args (S.fresh σA k).2
      (X.fresh_wellFormed k goodA)
  obtain ⟨acceptF, rejectF⟩ :=
    unifyAll_exact X (instArgs L params (S.fresh σA k).1) args (S.fresh σF k).2
      (X.fresh_wellFormed k goodF)
  simp only [← sameFrame, Option.map_map]
  refine ⟨fun noneA => ?_, fun task someA => ?_⟩
  · -- the output-first head fails too
    rw [Option.map_eq_none_iff] at noneA
    have empty := rejectA noneA
    have noneF :
        unifyAll S (instArgs L params (S.fresh σA k).1) args (S.fresh σF k).2 = none := by
      cases unified : unifyAll S (instArgs L params (S.fresh σA k).1) args (S.fresh σF k).2 with
      | none => rfl
      | some σ' =>
          obtain ⟨sols', good', _⟩ := acceptF σ' unified
          obtain ⟨w, member⟩ := X.wellFormed_nonempty good'
          rw [sols', X.fresh_solutions, sols] at member
          have : w ∈ X.solutions (S.fresh σA k).2 ∩
              solvesAll X (instArgs L params (S.fresh σA k).1) args := by
            rw [X.fresh_solutions]
            exact ⟨member.1.1, member.2⟩
          rw [empty] at this
          exact absurd this (Set.notMem_empty w)
    simp [noneF]
  · rw [Option.map_eq_some_iff] at someA
    obtain ⟨σA', unifiedA, rfl⟩ := someA
    obtain ⟨solsA, goodA', keyA⟩ := acceptA σA' unifiedA
    rw [X.fresh_solutions] at solsA
    have doomedA :
        X.solutions σA' ∩ pending L X [] (S.fresh σA k).1 late (S.fresh σA k).1 dest ∩ P =
          ∅ →
        GoalDoomed L X goalDest Q ⟨(), ⟨k, late, (S.fresh σA k).1, σA'⟩, fs⟩ :=
      GoalDoomed.unsatisfiable _ _ σA' dest ahead (fun _ _ => rfl) frames goodA'
    have shape :
        X.solutions (S.fresh σF k).2 ∩ solvesAll X (instArgs L params (S.fresh σA k).1) args =
        X.solutions σA' ∩ P := by
      rw [X.fresh_solutions, sols, solsA]
      ext w
      simp only [Set.mem_inter_iff]
      tauto
    cases unifiedF : unifyAll S (instArgs L params (S.fresh σA k).1) args (S.fresh σF k).2 with
    | none =>
        refine .inl ⟨by simp, doomedA ?_⟩
        refine Set.subset_eq_empty ?_ ((shape ▸ rejectF unifiedF))
        rintro w ⟨⟨inSol, _⟩, inP⟩
        exact ⟨inSol, inP⟩
    | some σF' =>
        obtain ⟨solsF, goodF', keyF⟩ := acceptF σF' unifiedF
        obtain ⟨acceptM, rejectM⟩ :=
          meet_exact (L := L) (X := X) (S.fresh σA k).1 early dest σF' goodF'
        rw [ahead.exposed_eq] at acceptM rejectM
        cases met : meet L S (S.fresh σA k).1 early dest σF' with
        | none =>
            refine .inl ⟨by simp [met], doomedA ?_⟩
            have empty := rejectM met
            rw [solsF, shape] at empty
            refine Set.subset_eq_empty ?_ empty
            rintro w ⟨⟨inSol, _, inMeets⟩, inP⟩
            exact ⟨⟨inSol, inP⟩, inMeets⟩
        | some σF'' =>
            obtain ⟨solsM, goodM, keyM⟩ := acceptM σF'' met
            refine .inr ⟨⟨(), ⟨⟨k, early, (S.fresh σA k).1, σF''⟩, dest⟩, gs⟩,
              by simp [met], ?_⟩
            refine GoalRelated.mk _ _ σA' σF'' dest ahead (fun _ _ => rfl) frames goodA' goodM
              ?_ ?_
            · rw [solsM, solsF, shape]
              ext w
              simp only [pending, binds_nil, Set.mem_inter_iff, Set.mem_univ, true_and]
              tauto
            · rw [keyM, keyF, keyA]
              exact sameKey.symm

/-- The activations of a call whose owed equations have no solution are all
doomed. -/
theorem goal_activations_doomed (aligned : ProgramBindsAhead L PA PF)
    (rel : Rel) (args : List Term) (σ : Store) (good : X.WellFormed σ) (dest : Option Term)
    {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)} {P : Set X.Valuation}
    (frames : GoalFrames L X goalDest Q dest fs gs P) (empty : X.solutions σ ∩ P = ∅) :
    ∀ t ∈ (activate L S PA (rel, args, σ)).map (fun a =>
        (⟨(), ⟨a.slots, a.code, a.frame, a.store⟩, fs⟩ :
          Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op))),
      GoalDoomed L X goalDest Q t := by
  intro t member
  simp only [List.mem_map, activate, List.mem_filterMap, Option.map_eq_some_iff] at member
  obtain ⟨_, ⟨e, eMember, σ', unified, rfl⟩, rfl⟩ := member
  obtain ⟨e', _, related⟩ := exists_of_forall₂_mem (aligned.equations rel) eMember
  cases related with
  | @mk k params late early ahead =>
  obtain ⟨sols', good', _⟩ :=
    (unifyAll_exact X _ args (S.fresh σ k).2 (X.fresh_wellFormed k good)).1 σ' unified
  rw [X.fresh_solutions] at sols'
  refine GoalDoomed.unsatisfiable _ _ σ' dest ahead (fun _ _ => rfl) frames good' ?_
  refine Set.subset_eq_empty ?_ empty
  rintro w ⟨⟨inSol, _⟩, inP⟩
  rw [sols'] at inSol
  exact ⟨inSol.1, inP⟩

/-- A doomed instruction yields only doomed tasks, and every answer it delivers
has no solution in the goal's context against the goal's destination. -/
theorem goal_successors_doomed (aligned : ProgramBindsAhead L PA PF)
    {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
    {P : Set X.Valuation} (frames : GoalFrames L X goalDest Q dest fs gs P)
    {instruction : Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store)}
    (doomed : DoomedInstruction L X dest P instruction) :
    (∀ t ∈ (expandWith (compiled L S PA) () fs instruction).1, GoalDoomed L X goalDest Q t) ∧
      ∀ x ∈ (expandWith (compiled L S PA) () fs instruction).2,
        AnswerOmitted X Q goalDest x.2 := by
  cases doomed with
  | ret v σ good empty =>
      cases frames with
      | base =>
          refine ⟨fun t member => by simp [expandWith] at member, fun x member => ?_⟩
          simp only [expandWith, List.mem_singleton] at member
          subst member
          exact ⟨good, empty⟩
      | @cons k p E late early captured origin dest' fs' gs' P' ahead agrees rest =>
          refine ⟨fun t member => ?_, fun x member => by simp [expandWith] at member⟩
          simp only [expandWith, List.mem_singleton] at member
          subst member
          change GoalDoomed L X goalDest Q
            ⟨(), resumeControl L S ⟨k, p, late, captured⟩ (v, σ), fs'⟩
          simp only [resumeControl]
          cases unified : S.unify (L.inst p (reconstruct captured)) v σ with
          | none => exact .failing _ _ _
          | some σ' =>
              refine GoalDoomed.unsatisfiable _ origin σ' dest' ahead agrees rest
                (X.unify_wellFormed good unified) ?_
              refine Set.subset_eq_empty ?_ empty
              rintro w ⟨⟨inSol, inPending⟩, inP⟩
              rw [X.unify_some good unified] at inSol
              refine ⟨⟨inSol.1, ?_⟩, inPending, inP⟩
              intro a d hA hD
              simp only [Option.some.injEq] at hA hD
              subst hA hD
              exact (X.solves_comm _ _ _).mp inSol.2
  | fail => exact ⟨fun _ member => by simp [expandWith] at member,
      fun _ member => by simp [expandWith] at member⟩
  | call rel args σ p captured origin ahead agrees good empty =>
      refine ⟨fun t member => ?_, fun _ member => by simp [expandWith] at member⟩
      simp only [expandWith, compiled, List.map_map] at member
      exact goal_activations_doomed aligned rel args σ good _
        (.cons p captured origin dest ahead agrees frames)
        (by rw [← Set.inter_assoc]; exact empty)
        t (by simpa [Function.comp_def] using member)
  | tail rel args σ good empty =>
      refine ⟨fun t member => ?_, fun _ member => by simp [expandWith] at member⟩
      simp only [expandWith, compiled, List.map_map] at member
      exact goal_activations_doomed aligned rel args σ good _ frames empty t
        (by simpa [Function.comp_def] using member)

/-- Corresponding instructions yield corresponding tasks; a return at the
goal's base delivers corresponding answers, the output-first store being the
reference's intersected with the goal's destination meeting the value and with
the goal's context. -/
theorem goal_successors_related (aligned : ProgramBindsAhead L PA PF)
    {dest : Option Term} {fs : List (ReturnFrame L Rel Op)} {gs : List (DestFrame L Rel Op)}
    {P : Set X.Valuation} (frames : GoalFrames L X goalDest Q dest fs gs P)
    {iA : Instruction (Call Term Store Rel) (ReturnFrame L Rel Op) (Answer Term Store)}
    {iF : Instruction (DestCall Term Store Rel) (DestFrame L Rel Op) (Answer Term Store)}
    (related : InspectRelated L X dest P iA iF) :
    Embeds (GoalRelated L X goalDest Q) (GoalDoomed L X goalDest Q)
        (expandWith (compiled L S PA) () fs iA).1 (expandWith (outputFirst L S PF) () gs iF).1 ∧
      Embeds (fun a b : Unit × Answer Term Store => AnswerRel X Q goalDest a.2 b.2)
        (fun a => AnswerOmitted X Q goalDest a.2)
        (expandWith (compiled L S PA) () fs iA).2 (expandWith (outputFirst L S PF) () gs iF).2 := by
  cases related with
  | ret v σA σF goodA goodF sols keys =>
      cases frames with
      | base => exact ⟨.nil, .keep ⟨goodA, goodF, rfl, sols, keys⟩ .nil⟩
      | @cons k p E late early captured origin dest' fs' gs' P' ahead agrees rest =>
          refine ⟨?_, .nil⟩
          simp only [expandWith]
          change Embeds (GoalRelated L X goalDest Q) (GoalDoomed L X goalDest Q)
            [⟨(), resumeControl L S ⟨k, p, late, captured⟩ (v, σA), fs'⟩]
            [⟨(), ⟨⟨k, early, reconstruct captured, σF⟩, dest'⟩, gs'⟩]
          simp only [resumeControl]
          have solved : X.solutions σF ⊆
              X.solutions σA ∩ {w | X.solves w (L.inst p (reconstruct captured)) v} := by
            rw [sols]
            rintro w ⟨⟨inSol, inMeets⟩, _⟩
            exact ⟨inSol, (X.solves_comm _ _ _).mp (inMeets v _ rfl rfl)⟩
          cases unified : S.unify (L.inst p (reconstruct captured)) v σA with
          | none =>
              have empty := X.unify_none goodA unified
              exact absurd (Set.subset_eq_empty solved empty)
                (X.wellFormed_nonempty goodF).ne_empty
          | some σA' =>
              refine .keep (GoalRelated.mk _ origin σA' σF dest' ahead agrees rest
                (X.unify_wellFormed goodA unified) goodF ?_
                (keys.trans (X.unify_supply unified).symm)) .nil
              rw [sols, X.unify_some goodA unified]
              ext w
              simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
              constructor
              · rintro ⟨⟨inSol, inMeets⟩, inPending, inP⟩
                exact
                  ⟨⟨⟨inSol, (X.solves_comm _ _ _).mp (inMeets v _ rfl rfl)⟩, inPending⟩, inP⟩
              · rintro ⟨⟨⟨inSol, inSat⟩, inPending⟩, inP⟩
                refine ⟨⟨inSol, ?_⟩, inPending, inP⟩
                intro a d hA hD
                simp only [Option.some.injEq] at hA hD
                subst hA hD
                exact (X.solves_comm _ _ _).mp inSat
  | fail => exact ⟨.nil, .nil⟩
  | call rel args σA σF p captured origin ahead agrees goodA goodF sols keys =>
      refine ⟨?_, .nil⟩
      simp only [expandWith, compiled, outputFirst, List.map_map]
      have embeds := goal_activations_embed aligned rel args σA σF goodA goodF keys _
        (.cons p captured origin dest ahead agrees frames) (by rw [sols, Set.inter_assoc])
      simpa [Function.comp_def] using embeds
  | tail rel args σA σF goodA goodF sols keys =>
      refine ⟨?_, .nil⟩
      simp only [expandWith, compiled, outputFirst, List.map_map]
      have embeds := goal_activations_embed aligned rel args σA σF goodA goodF keys _ frames sols
      simpa [Function.comp_def] using embeds
  | doomed d =>
      obtain ⟨all, omitted⟩ := goal_successors_doomed aligned frames d
      exact ⟨Embeds.of_forall all, Embeds.of_forall omitted⟩

/-- **Corresponding tasks of a goal's runs expand to corresponding tasks and
answers**, for a moded reference task. -/
theorem goal_expand_related (aligned : ProgramBindsAhead L PA PF)
    {tA : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    {tF : Task Unit (DestControl L Rel Op Store) (DestFrame L Rel Op)}
    (related : GoalRelated L X goalDest Q tA tF) (moded : Moded L X tA) :
    Embeds (GoalRelated L X goalDest Q) (GoalDoomed L X goalDest Q)
        (expand (compiled L S PA) tA).1 (expand (outputFirst L S PF) tF).1 ∧
      Embeds (fun a b : Unit × Answer Term Store => AnswerRel X Q goalDest a.2 b.2)
        (fun a => AnswerOmitted X Q goalDest a.2)
        (expand (compiled L S PA) tA).2 (expand (outputFirst L S PF) tF).2 := by
  cases related with
  | mk frame origin σA σF dest ahead agrees frames goodA goodF sols keys =>
      exact goal_successors_related aligned frames
        (inspect_related ahead frame origin dest _ σA σF goodA goodF agrees sols keys moded)

/-- **A doomed task of a goal's reference run** yields only doomed tasks, and
every answer it delivers is omitted: it has no solution in the goal's context
against the goal's destination. -/
theorem goal_expand_doomed (aligned : ProgramBindsAhead L PA PF)
    {t : Task Unit (Control L Rel Op Store) (ReturnFrame L Rel Op)}
    (doomed : GoalDoomed L X goalDest Q t) :
    (∀ t' ∈ (expand (compiled L S PA) t).1, GoalDoomed L X goalDest Q t') ∧
      ∀ x ∈ (expand (compiled L S PA) t).2, AnswerOmitted X Q goalDest x.2 := by
  cases doomed with
  | failing frame σ fs =>
      exact ⟨fun _ member => by simp [expand, compiled, inspectCode, expandWith] at member,
        fun _ member => by simp [expand, compiled, inspectCode, expandWith] at member⟩
  | unsatisfiable frame origin σ dest ahead agrees frames good empty =>
      exact goal_successors_doomed aligned frames
        (inspect_doomed ahead frame origin dest _ σ good agrees empty)

end Expansion

end Mettapedia.GSLT.LanguageDef.HostGoals
