import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeDeadDiamond

/-!
# Iterated native residuals: every order of a clear family is admitted

`Step/NativeResidual` reads a live firing at the published result of one other live firing's step
(`LiveFiring.residualAt`) and shows that a firing the other leaves clear stays admitted there. This
module iterates the residual over words of live firings.

## Sequential runs

A **sequential run** of a word of live firings (`Sequential`) fires the first, reads the rest as
residuals after its step (`residualAfter`), and runs them from its published result. A word has at
most one final state (`Sequential.unique`): the solver's return is a function of the data.

## The family condition

Pairwise clearness does not survive residuals. Three tellers `X = true`, `Y = false` and `X = Y` are
pairwise jointly solvable, and no order of the three is admitted (`Step/NativeIteratedControls`). The
right condition is **joint solvability of the whole family** (`Jointly`): one solution of the state's
names, extended by a solution of each firing's information. A **clear family** (`FamilyClear`) is
admitted firing by firing, pairwise clear in both directions, and jointly solvable.

* **Clearness is preserved by residuals** (`residual_clear`): two firings that one execution leaves
  clear, and that are jointly solvable with it, leave each other's residuals clear. Their takes,
  produced ports and reads are unchanged; the residuals' joint solution is the amalgamation of the triple's
  (`amalgam`); and every joint solution of the residuals restricts, along the carrying, to a joint
  solution of the two firings (`restrictJoint`), where the blindness of the pair applies.
* **A clear family stays clear after each of its firings** (`familyClear_residual`).
* **Every order is admitted** (`every_order_admitted`): every permutation of a clear family is a
  sequential run.
* **Joint solvability is necessary** (`Sequential.jointly`): a sequential run of a word in which no
  firing takes or reads what another makes (`Unmade`) has a joint solution of the whole word; so without
  one, no order runs (`no_order_of_not_jointly`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeIterated

/-! ## Residuals after a step, and sequential runs -/

section Runs

variable {s : NativeState S O Γ sort}

/-- **The residual after a step**: a live firing read at the published result of an admitted live
firing's step, along the step's pinned execution. -/
noncomputable abbrev residualAfter {g : LiveFiring s} (admitted : g.toNative.Realized) (f : LiveFiring s) :
    LiveFiring (native.result g.toNative admitted) :=
  f.residualAt (LiveFiring.execution admitted)

theorem residualAfter_toNative {g : LiveFiring s} (admitted : g.toNative.Realized) (f : LiveFiring s) :
    (residualAfter admitted f).toNative = LiveFiring.residual admitted f :=
  rfl

/-- **A sequential native run of a word of live firings**: the first firing is admitted, and the rest,
read as residuals after its step, run from its published result to `t`. -/
inductive Sequential : (s : NativeState S O Γ sort) → List (LiveFiring s) → NativeState S O Γ sort → Prop
  | nil (s : NativeState S O Γ sort) : Sequential s [] s
  | cons {s : NativeState S O Γ sort} (f : LiveFiring s) (rest : List (LiveFiring s))
      (admitted : f.toNative.Realized) {t : NativeState S O Γ sort}
      (later : Sequential (native.result f.toNative admitted) (rest.map (residualAfter admitted)) t) :
      Sequential s (f :: rest) t

theorem sequential_nil_iff {t : NativeState S O Γ sort} : Sequential s [] t ↔ t = s := by
  constructor
  · intro run
    cases run
    rfl
  · intro same
    subst same
    exact .nil _

theorem sequential_cons_iff {f : LiveFiring s} {rest : List (LiveFiring s)} {t : NativeState S O Γ sort} :
    Sequential s (f :: rest) t ↔ ∃ admitted : f.toNative.Realized,
      Sequential (native.result f.toNative admitted) (rest.map (residualAfter admitted)) t := by
  constructor
  · intro run
    cases run with
    | cons _ _ admitted later => exact ⟨admitted, later⟩
  · rintro ⟨admitted, later⟩
    exact .cons f rest admitted later

/-- **A word has at most one final state**: the solver's return is computed from the data. -/
theorem Sequential.unique {fs : List (LiveFiring s)} {t t' : NativeState S O Γ sort}
    (first : Sequential s fs t) (second : Sequential s fs t') : t = t' := by
  induction first generalizing t' with
  | nil s =>
      cases second
      rfl
  | cons f rest admitted later ih =>
      cases second with
      | cons _ _ admitted' later' => exact ih later'

/-- A run of one firing is its step. -/
theorem sequential_singleton_iff {f : LiveFiring s} {t : NativeState S O Γ sort} :
    Sequential s [f] t ↔ ∃ admitted : f.toNative.Realized, t = native.result f.toNative admitted := by
  rw [sequential_cons_iff]
  refine exists_congr fun admitted => ?_
  rw [List.map_nil, sequential_nil_iff]

end Runs

/-! ## Joint solvability of a family -/

section Jointly

variable {s : NativeState S O Γ sort}

/-- **A family is jointly solvable**: one solution of the state's names extends to a solution of each
firing's information. -/
def Jointly (s : NativeState S O Γ sort) (fs : List (LiveFiring s)) : Prop :=
  ∃ (b : Frames.Frame S) (shared : Assignment s.state.declarations b.arity),
    ∀ f ∈ fs, ∃ σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity,
      ContextualResidual.Models σ f.toNative.information ∧
        Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) = shared

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem Jointly.mono {fs fs' : List (LiveFiring s)} (jointly : Jointly s fs) (inside : ∀ f ∈ fs', f ∈ fs) :
    Jointly s fs' := by
  obtain ⟨b, shared, each⟩ := jointly
  exact ⟨b, shared, fun f member => each f (inside f member)⟩

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **Two members of a jointly solvable family have a joint solution.** -/
theorem Jointly.joint {fs : List (LiveFiring s)} (jointly : Jointly s fs) {f g : LiveFiring s}
    (inF : f ∈ fs) (inG : g ∈ fs) :
    ∃ b : Frames.Frame S, Nonempty (Joint s f.toNative.information g.toNative.information b) := by
  obtain ⟨b, shared, each⟩ := jointly
  obtain ⟨σ, modelsF, agreeF⟩ := each f inF
  obtain ⟨τ, modelsG, agreeG⟩ := each g inG
  exact ⟨b, ⟨⟨σ, τ, modelsF, modelsG, agreeF.trans agreeG.symm⟩⟩⟩

end Jointly

/-- Two live firings leave each other clear. -/
def Clears {s : NativeState S O Γ sort} (f g : LiveFiring s) : Prop :=
  Clear f g.selection g.rule g.outputs ∧ Clear g f.selection f.rule f.outputs

omit [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem Clears.symm {s : NativeState S O Γ sort} {f g : LiveFiring s} (clears : Clears f g) : Clears g f :=
  ⟨clears.2, clears.1⟩

/-- **A clear family** of live firings: each is admitted, every two leave each other clear, and the
family is jointly solvable. -/
structure FamilyClear (s : NativeState S O Γ sort) (fs : List (LiveFiring s)) : Prop where
  admitted : ∀ f ∈ fs, f.toNative.Realized
  pairwise : fs.Pairwise Clears
  jointly : Jointly s fs

/-- **Clear families are closed under permutation.** -/
theorem FamilyClear.perm {s : NativeState S O Γ sort} {fs fs' : List (LiveFiring s)} (clear : FamilyClear s fs)
    (perm : fs'.Perm fs) : FamilyClear s fs' where
  admitted f member := clear.admitted f (perm.subset member)
  pairwise := (perm.pairwise_iff Clears.symm).mpr clear.pairwise
  jointly := clear.jointly.mono fun _ member => perm.subset member

/-! ## Clearness is preserved by residuals -/

section Preserved

variable {s : NativeState S O Γ sort} (G : ContextualConditionalExecution.Firing s.locals s.state)

/-- **Whatever a firing takes or reads is not made by another execution**: it is present, and the
execution's makes are fresh. -/
theorem unmade_of {x : LiveFiring s} (admitted : x.toNative.Realized) :
    ∀ o ∈ x.selection.taken ++ x.selection.read, o ∉ G.selection.made := by
  intro o member made
  obtain ⟨_, enabled, _, _⟩ := (native_admits_iff x.toNative).mp admitted
  have inP : o ∈ s.state.present := by
    rcases List.mem_append.mp member with taken | read
    · exact enabled.taken_subset (List.mem_toFinset.mpr taken)
    · exact enabled.kept_subset (List.mem_toFinset.mpr read)
  exact Finset.disjoint_left.mp G.admitted.fresh (List.mem_toFinset.mpr made) inP

/-- The published frame of an amalgamated solution depends on the second solution only. -/
def sharedAmalgam {b : Frames.Frame S}
    (right : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity) :
    Assignment G.target.declarations (Frames.firstOrderFrame S).arity
  | .inl name => instantiate (Frames.toFirstOrder b) (right name)
  | .inr helper => Frames.toFirstOrder ⟨_, laterTarget G⟩ (.inr (.inr helper))

theorem amalgam_captured {first second : ContextualResidual.Problem
      (ContextualActivatedStep.target s.locals s.state.declarations)} {b : Frames.Frame S}
    (J : Joint s first second b) :
    Assignment.compose (amalgam G J) (laterCaptured G) = sharedAmalgam G J.right := by
  funext name
  refine (instantiate_generator (amalgam G J) (.inr name)).trans ?_
  cases name <;> rfl

/-- **A joint solution of two residuals restricts to a joint solution of the two firings**, along
the carrying. -/
def restrictJoint {f h : LiveFiring s}
    (unmadeF : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made)
    (unmadeH : ∀ o ∈ h.selection.taken ++ h.selection.read, o ∉ G.selection.made) {b : Frames.Frame S}
    (J : Joint (rawTarget G) (f.residualAt G).toNative.information
      (problemOf (rawTarget G) (h.residualAt G).selection (h.residualAt G).rule) b) :
    Joint s f.toNative.information (problemOf s h.selection h.rule) b where
  left := Assignment.compose J.left (carry G)
  right := Assignment.compose J.right (carry G)
  left_models := (Joint.ofResidual G f unmadeF J.left J.left_models).left_models
  right_models := (Joint.ofResidual G h unmadeH J.right J.right_models).left_models
  agree := (restrictions_agree G J.left).trans
    ((congrArg (fun assignment => Assignment.compose (Assignment.compose assignment
        (ContextualComputedFreshFrame.includeSource G.update))
        (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)) J.agree).trans
      (restrictions_agree G J.right).symm)

/-- **A carried guard sees a retained occurrence at the published result exactly when the guard sees
it at the state**, read at the restriction. -/
theorem guardSees_retained {W : Type} {next : W → MetaArity S} (ρ : Assignment (laterTarget G) next) {o : O}
    (notMade : o ∉ G.selection.made)
    (check : Check (Term (signature S (ContextualActivatedStep.target s.locals s.state.declarations)) Γ sort)) :
    GuardSees (ContextualPublication.privateFamily s.locals G.update.declaration) ρ
        (ContextualConditionalExecution.guardRows (ContextualPublication.privateFamily s.locals G.update.declaration)
          G.target.declarations G.target.rows) (check.map (instantiate (carry G))) o ↔
      GuardSees s.locals (Assignment.compose ρ (carry G))
        (ContextualConditionalExecution.guardRows s.locals s.state.declarations s.state.rows) check o := by
  cases check with
  | equal first second => exact Iff.rfl
  | absent pattern =>
      show ContextualConditionalRows.Matches _ _ ρ (instantiate ρ (instantiate (carry G) pattern)) _ ↔
        ContextualConditionalRows.Matches _ _ (Assignment.compose ρ (carry G))
          (instantiate (Assignment.compose ρ (carry G)) pattern) _
      rw [← Assignment.instantiate_compose]
      exact matches_retained G ρ notMade _
  | count pattern cardinality =>
      show ContextualConditionalRows.Matches _ _ ρ (instantiate ρ (instantiate (carry G) pattern)) _ ↔
        ContextualConditionalRows.Matches _ _ (Assignment.compose ρ (carry G))
          (instantiate (Assignment.compose ρ (carry G)) pattern) _
      rw [← Assignment.instantiate_compose]
      exact matches_retained G ρ notMade _

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
/-- **What a carried guard sees among carried outputs** is what the guard sees, read at the
restrictions. -/
theorem seesOutput_map {V W X : Type} {declaration : V → MetaArity S} {middle : W → MetaArity S}
    {next : X → MetaArity S} (φ : Assignment declaration middle) (left right : Assignment middle next)
    (output : Term (signature S declaration) Γ sort) (check : Check (Term (signature S declaration) Γ sort)) :
    SeesOutput left right (instantiate φ output) (check.map (instantiate φ)) ↔
      SeesOutput (Assignment.compose left φ) (Assignment.compose right φ) output check := by
  cases check with
  | equal first second => exact Iff.rfl
  | absent pattern =>
      show instantiate left (instantiate φ pattern) = instantiate right (instantiate φ output) ↔ _
      rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
      rfl
  | count pattern cardinality =>
      show instantiate left (instantiate φ pattern) = instantiate right (instantiate φ output) ↔ _
      rw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
      rfl

/-- The rule views of a residual are the firing's, carried. -/
theorem residual_prepared (f : LiveFiring s) :
    (f.residualAt G).toNative.prepared.rule = f.toNative.prepared.rule.map (instantiate (carry G)) :=
  (prepared_rule_carried G f.selection f.rule (fun o => (s.state.rows o).value)
    (fun o => (G.target.rows o).value)).symm

/-- **Clearness is preserved by residuals.** Two live firings that an execution's published result
receives, the first leaving the second clear, leave each other's residuals clear when the three are
jointly solvable: given by a joint solution of each with the execution, with one solution of the
execution. -/
theorem residual_clear {f h : LiveFiring s}
    (unmadeF : ∀ o ∈ f.selection.taken ++ f.selection.read, o ∉ G.selection.made)
    (unmadeH : ∀ o ∈ h.selection.taken ++ h.selection.read, o ∉ G.selection.made)
    (clear : Clear f h.selection h.rule h.outputs)
    (consistent : ∃ (b : Frames.Frame S) (Jf : Joint s f.toNative.information (problemOf s G.selection G.rule) b)
      (Jh : Joint s h.toNative.information (problemOf s G.selection G.rule) b), Jf.right = Jh.right) :
    Clear (f.residualAt G) (h.residualAt G).selection (h.residualAt G).rule (h.residualAt G).outputs where
  takes := clear.takes
  ports := clear.ports
  keeps := clear.keeps
  consistent := by
    obtain ⟨b, Jf, Jh, same⟩ := consistent
    refine ⟨Frames.firstOrderFrame S, ⟨⟨amalgam G Jf, amalgam G Jh, models_amalgam G f unmadeF Jf,
      models_amalgam G h unmadeH Jh, ?_⟩⟩⟩
    show Assignment.compose (amalgam G Jf) (laterCaptured G) = Assignment.compose (amalgam G Jh) (laterCaptured G)
    rw [amalgam_captured, amalgam_captured, same]
  blindTakes b J o taken := by
    have notMade : o ∉ G.selection.made := unmadeH o (List.mem_append_left _ taken)
    obtain ⟨checks, patterns⟩ := clear.blindTakes b (restrictJoint G unmadeF unmadeH J) o taken
    refine ⟨fun check member sees => ?_, fun pattern member matched => ?_⟩
    · have member' : check ∈ (f.toNative.prepared.rule.map (instantiate (carry G))).checks :=
        (congrArg (fun checks => check ∈ checks) (congrArg RuleInstance.checks (residual_prepared G f))).mp member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member'
      exact checks original inside ((guardSees_retained G J.left notMade original).mp sees)
    · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      have seen := (matches_retained G J.left notMade _).mp matched
      have term : instantiate J.left (instantiate (carry G) original.1) =
          instantiate (Assignment.compose J.left (carry G)) original.1 :=
        (Assignment.instantiate_compose _ _ _).symm
      rw [term] at seen
      exact patterns original inside seen
  blindOutputs b J o made := by
    obtain ⟨checks, patterns⟩ := clear.blindOutputs b (restrictJoint G unmadeF unmadeH J) o made
    refine ⟨fun check member sees => ?_, fun pattern member equal => ?_⟩
    · have member' : check ∈ (f.toNative.prepared.rule.map (instantiate (carry G))).checks :=
        (congrArg (fun checks => check ∈ checks) (congrArg RuleInstance.checks (residual_prepared G f))).mp member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member'
      exact checks original inside ((seesOutput_map (carry G) J.left J.right (h.outputs o) original).mp sees)
    · obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      exact patterns original inside ((Assignment.instantiate_compose J.left (carry G) original.1).trans
        (equal.trans (Assignment.instantiate_compose J.right (carry G) (h.outputs o)).symm))

end Preserved

/-! ## A clear family stays clear, and every order is admitted -/

section Families

variable {s : NativeState S O Γ sort}

/-- The pinned execution's information is the firing's. -/
theorem problemOf_execution {g : LiveFiring s} (admitted : g.toNative.Realized) :
    problemOf s (LiveFiring.execution admitted).selection (LiveFiring.execution admitted).rule =
      g.toNative.information := by
  rw [(LiveFiring.execution_data admitted).1, (LiveFiring.execution_data admitted).2.1]
  rfl

/-- **A clear family stays clear after each of its firings**: the rest, read as residuals after the
step of its first firing, is again a clear family. -/
theorem familyClear_residual {g : LiveFiring s} {rest : List (LiveFiring s)} (clear : FamilyClear s (g :: rest))
    (admitted : g.toNative.Realized) :
    FamilyClear (native.result g.toNative admitted) (rest.map (residualAfter admitted)) := by
  have problem := problemOf_execution admitted
  obtain ⟨b, shared, each⟩ := clear.jointly
  obtain ⟨σg, modelsG, agreeG⟩ := each g List.mem_cons_self
  have modelsG' : ContextualResidual.Models σg
      (problemOf s (LiveFiring.execution admitted).selection (LiveFiring.execution admitted).rule) := by
    rw [problem]
    exact modelsG
  have withG : ∀ f ∈ rest, ∃ J : Joint s f.toNative.information
      (problemOf s (LiveFiring.execution admitted).selection (LiveFiring.execution admitted).rule) b, J.right = σg := by
    intro f inRest
    obtain ⟨σ, models, agree⟩ := each f (List.mem_cons_of_mem _ inRest)
    exact ⟨⟨σ, σg, models, modelsG', agree.trans agreeG.symm⟩, rfl⟩
  have pairwiseG := List.pairwise_cons.mp clear.pairwise
  have admittedRest : ∀ f ∈ rest, f.toNative.Realized := fun f inRest =>
    clear.admitted f (List.mem_cons_of_mem _ inRest)
  refine ⟨?_, ?_, ?_⟩
  · intro f' member
    obtain ⟨f, inRest, rfl⟩ := List.mem_map.mp member
    exact LiveFiring.after (admittedRest f inRest) admitted (pairwiseG.1 f inRest).2
  · refine List.pairwise_map.mpr (pairwiseG.2.imp_of_mem fun {f h} inF inH clears => ?_)
    obtain ⟨Jf, sameF⟩ := withG f inF
    obtain ⟨Jh, sameH⟩ := withG h inH
    have unmadeF := unmade_of (LiveFiring.execution admitted) (admittedRest f inF)
    have unmadeH := unmade_of (LiveFiring.execution admitted) (admittedRest h inH)
    exact ⟨residual_clear (LiveFiring.execution admitted) unmadeF unmadeH clears.1
        ⟨b, Jf, Jh, sameF.trans sameH.symm⟩,
      residual_clear (LiveFiring.execution admitted) unmadeH unmadeF clears.2
        ⟨b, Jh, Jf, sameH.trans sameF.symm⟩⟩
  · refine ⟨Frames.firstOrderFrame S, sharedAmalgam (LiveFiring.execution admitted) σg, fun f' member => ?_⟩
    obtain ⟨f, inRest, rfl⟩ := List.mem_map.mp member
    obtain ⟨J, same⟩ := withG f inRest
    refine ⟨amalgam (LiveFiring.execution admitted) J,
      models_amalgam (LiveFiring.execution admitted) f
        (unmade_of (LiveFiring.execution admitted) (admittedRest f inRest)) J, ?_⟩
    rw [← same]
    exact amalgam_captured (LiveFiring.execution admitted) J

/-- **A clear family is a sequential run.** -/
theorem sequential_of_familyClear : ∀ (n : ℕ) {s : NativeState S O Γ sort} (fs : List (LiveFiring s)),
    fs.length = n → FamilyClear s fs → ∃ t, Sequential s fs t
  | _, s, [], _, _ => ⟨s, .nil s⟩
  | n + 1, _, g :: rest, length, clear => by
      have admitted := clear.admitted g List.mem_cons_self
      obtain ⟨t, later⟩ := sequential_of_familyClear n (rest.map (residualAfter admitted))
        (by rw [List.length_map]; exact Nat.succ.inj length) (familyClear_residual clear admitted)
      exact ⟨t, .cons g rest admitted later⟩

/-- **Every order of a clear family is admitted**: every permutation of the family is a sequential
run. -/
theorem every_order_admitted {fs : List (LiveFiring s)} (clear : FamilyClear s fs) {order : List (LiveFiring s)}
    (perm : order.Perm fs) : ∃ t, Sequential s order t :=
  sequential_of_familyClear _ order rfl (clear.perm perm)


/-! ## Joint solvability is necessary -/

/-- **No firing of a word takes or reads what a firing of the word makes**: the word has no causal
dependence inside it. -/
def Unmade (fs : List (LiveFiring s)) : Prop :=
  ∀ x ∈ fs, ∀ y ∈ fs, ∀ o ∈ x.selection.taken ++ x.selection.read, o ∉ y.selection.made

theorem Unmade.residual {g : LiveFiring s} (admitted : g.toNative.Realized) {rest : List (LiveFiring s)}
    (unmade : Unmade (g :: rest)) : Unmade (rest.map (residualAfter admitted)) := by
  intro x' inX y' inY o member
  obtain ⟨x, restX, rfl⟩ := List.mem_map.mp inX
  obtain ⟨y, restY, rfl⟩ := List.mem_map.mp inY
  exact unmade x (List.mem_cons_of_mem _ restX) y (List.mem_cons_of_mem _ restY) o member

omit [DecidableEq O] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] in
theorem Unmade.perm {fs fs' : List (LiveFiring s)} (unmade : Unmade fs) (perm : fs'.Perm fs) : Unmade fs' :=
  fun x inX y inY => unmade x (perm.subset inX) y (perm.subset inY)

/-- **Joint solvability is necessary**: a sequential run of a word without inner causal dependence
has a joint solution of the whole word. Every solution of the last firing's information restricts,
along the carryings, to solutions of all the earlier ones that agree on the state's names. -/
theorem Sequential.jointly {fs : List (LiveFiring s)} {t : NativeState S O Γ sort} (run : Sequential s fs t) :
    Unmade fs → Jointly s fs := by
  induction run with
  | nil s => exact fun _ => ⟨⟨s.state.Names, s.state.declarations⟩, generator _,
      fun f member => absurd member List.not_mem_nil⟩
  | @cons s f rest admitted t later ih =>
      intro unmade
      by_cases empty : rest = []
      · subst empty
        obtain ⟨_, _, ⟨b, σ, models⟩, _⟩ := (native_admits_iff f.toNative).mp admitted
        refine ⟨b, Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations),
          fun x member => ?_⟩
        rw [List.mem_singleton.mp member]
        exact ⟨σ, models, rfl⟩
      · obtain ⟨b, shared, each⟩ := ih (Unmade.residual admitted unmade)
        have selection := (LiveFiring.execution_data admitted).2.1
        have unmadeOf : ∀ x ∈ rest, ∀ o ∈ x.selection.taken ++ x.selection.read,
            o ∉ (LiveFiring.execution admitted).selection.made := by
          intro x inRest o member
          rw [selection]
          exact unmade x (List.mem_cons_of_mem _ inRest) f List.mem_cons_self o member
        have restricted : ∀ x ∈ rest, ∃ σ : Assignment (ContextualActivatedStep.target s.locals s.state.declarations) b.arity,
            ContextualResidual.Models σ x.toNative.information ∧
              Assignment.compose σ (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) =
                Assignment.compose (Assignment.compose shared
                  (ContextualComputedFreshFrame.includeSource (LiveFiring.execution admitted).update))
                  (ContextualSelectionViews.capturedTarget s.locals s.state.declarations) ∧
              ContextualResidual.Models (Assignment.compose shared
                  (ContextualComputedFreshFrame.includeSource (LiveFiring.execution admitted).update))
                (problemOf s (LiveFiring.execution admitted).selection (LiveFiring.execution admitted).rule) := by
          intro x inRest
          obtain ⟨σ', models', agree'⟩ := each (residualAfter admitted x) (List.mem_map_of_mem inRest)
          have through : Assignment.compose (Assignment.compose σ' (laterCaptured (LiveFiring.execution admitted)))
              (ContextualComputedFreshFrame.includeSource (LiveFiring.execution admitted).update) =
              Assignment.compose shared
                (ContextualComputedFreshFrame.includeSource (LiveFiring.execution admitted).update) :=
            congrArg (fun assignment => Assignment.compose assignment
              (ContextualComputedFreshFrame.includeSource (LiveFiring.execution admitted).update)) agree'
          refine ⟨Assignment.compose σ' (carry (LiveFiring.execution admitted)),
            (Joint.ofResidual (LiveFiring.execution admitted) x (unmadeOf x inRest) σ' models').left_models,
            (restrictions_agree (LiveFiring.execution admitted) σ').trans ?_, ?_⟩
          · exact congrArg (fun assignment => Assignment.compose assignment
              (ContextualSelectionViews.capturedTarget s.locals s.state.declarations)) through
          · rw [← through]
            exact (Joint.ofResidual (LiveFiring.execution admitted) x (unmadeOf x inRest) σ' models').right_models
        obtain ⟨h₀, inRest⟩ := List.exists_mem_of_ne_nil rest empty
        refine ⟨b, Assignment.compose (Assignment.compose shared
            (ContextualComputedFreshFrame.includeSource (LiveFiring.execution admitted).update))
            (ContextualSelectionViews.capturedTarget s.locals s.state.declarations), fun x member => ?_⟩
        rcases List.mem_cons.mp member with same | inRest'
        · subst same
          refine ⟨_, ?_, rfl⟩
          obtain ⟨_, _, _, models⟩ := restricted h₀ inRest
          rw [problemOf_execution admitted] at models
          exact models
        · obtain ⟨σ, models, agree, -⟩ := restricted x inRest'
          exact ⟨σ, models, agree⟩

/-- **No order of a word without inner causal dependence runs unless the word is jointly
solvable.** -/
theorem no_order_of_not_jointly {fs : List (LiveFiring s)} (unmade : Unmade fs) (notJointly : ¬ Jointly s fs)
    {order : List (LiveFiring s)} (perm : order.Perm fs) {t : NativeState S O Γ sort} : ¬ Sequential s order t :=
  fun run => notJointly ((run.jointly (unmade.perm perm)).mono fun _ member => perm.symm.subset member)

end Families

end NativeIterated

#print axioms NativeIterated.Sequential.unique
#print axioms NativeIterated.FamilyClear.perm
#print axioms NativeIterated.restrictJoint
#print axioms NativeIterated.guardSees_retained
#print axioms NativeIterated.seesOutput_map
#print axioms NativeIterated.residual_clear
#print axioms NativeIterated.familyClear_residual
#print axioms NativeIterated.sequential_of_familyClear
#print axioms NativeIterated.every_order_admitted
#print axioms NativeIterated.Sequential.jointly
#print axioms NativeIterated.no_order_of_not_jointly

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
