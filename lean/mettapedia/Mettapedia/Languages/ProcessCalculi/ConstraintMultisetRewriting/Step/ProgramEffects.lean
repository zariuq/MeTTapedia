import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramChoice
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects

/-!
# Effects and suspension

## Immediate effects
`add` and `remove` act on fact rows at once. **Control** (`immediate_effects_leave_a_trace`): in
`amb (let _ = add a in remove z) b`, the left branch adds `a`, then waits forever for a fact `z`: it
fails, and its fact `a` stays.

## Deferred effects (w9's deferred-effect blocks, `StagedSourceEffects`, on the step)
A deferred block is a list of translated firings at consecutive scopes (`block`), executed privately
and compiled by `StagedSourceEffects.compile`.
* `block_run`: an executable block is a run of translated firings.
* `deferred_block`: the compiled block either commits, and its result is the end of that run, or it
  leaves the configuration exactly as it was.
* `deferred_one_firing`: a committed block is one actual firing at its cut, with the knowledge and the
  rows of the run in code order: the order is the block's, not a scheduler's.
* **Control** (`deferred_failed_branch_leaves_no_trace`): the same two effects as the immediate
  control, an addition and a removal that cannot happen. Immediately, the addition fires and its fact
  stays while the removal never fires; deferred, no block of them is executable, and the compiled
  result is the starting configuration.

## Obstruction: atomic commits need computed rules
`firing_changes_bounded`: one translated firing of the core removes at most two occurrences and makes
at most two. So a block whose commit makes more than two rows is not one firing of any fixed rule of
the core; the block compiler's commit is a rule computed from the block (`deferred_one_firing`).
Prime must choose computed block rules, not a fixed schema family, for atomic deferred effects.

## Suspension
`await k` parks the continuation as `susp k κ`; `demandE k e` makes a demand row `demand k v`; the
resumption **takes the demand and reads the suspended continuation**.
* `demand_balance`: along every run, demands remaining plus resumptions equal initial demands plus
  demands made. Each resumption consumes exactly one demand, and nothing else consumes one.
* `taken_never_again`: on the step, an occurrence a firing takes is never present again, so one
  demand occurrence fuels at most one resumption.
* `exactly_once_per_demand`: one suspended continuation and two demands: every halted run resumed it
  exactly once per demand.
* **Control** (`replay_unbounded`): a resumption that only reads the demand replays it without
  bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-! ## Immediate effects -/

/-- `amb (let _ = add a in remove z) b`. -/
def failingBranch : Sx := ev (amb (let_ (add (atom ka)) (remove (atom kz))) (atom kb)) nil nil

/-- The failed branch: the removal of `z` waits, and the fact `a` stays. -/
def failedWithTrace : List Sx := [ret (atom kz) (cons removeK nil), fact (atom ka)]

theorem failingBranch_closed : SuccessorClosed (reach 12 [[failingBranch]]) = true := by decide

theorem failedWithTrace_halted :
    ∃ H ∈ halted (reach 12 [[failingBranch]]), H.isPerm failedWithTrace = true := by
  have : (halted (reach 12 [[failingBranch]])).any (fun H => H.isPerm failedWithTrace) = true := by decide
  exact List.any_eq_true.mp this

/-- **Control: an immediate effect of a failed branch leaves a trace.** -/
theorem immediate_effects_leave_a_trace :
    Relation.ReflTransGen Step ({failingBranch} : Multiset Sx) (failedWithTrace : Multiset Sx) ∧
      (∀ W', ¬ Step (failedWithTrace : Multiset Sx) W') ∧ fact (atom ka) ∈ failedWithTrace := by
  obtain ⟨H, mem, perm⟩ := failedWithTrace_halted
  have same : (H : Multiset Sx) = (failedWithTrace : Multiset Sx) :=
    Multiset.coe_eq_coe.mpr (List.isPerm_iff.mp perm)
  obtain ⟨reached, stuck⟩ := (halted_runs failingBranch_closed).1 H mem
  rw [same] at reached stuck
  exact ⟨reached, stuck, by decide⟩

/-! ## Deferred effects -/

/-- A translated firing as a prepared instruction of a deferred block. -/
def instruction (i : RuleName) (n : ℕ) (taken read : List Occ) :
    StagedSourceEffects.Instruction Tm (Mettapedia.Logic.LP.Subst rows) Occ :=
  ⟨(schema i).rule n, ⟨taken, read, madeAt n 0 (schema i).make⟩, []⟩

/-- A deferred block of translated firings at consecutive scopes from `n`. -/
def block : ℕ → List (RuleName × List Occ × List Occ) →
    List (StagedSourceEffects.Instruction Tm (Mettapedia.Logic.LP.Subst rows) Occ)
  | _, [] => []
  | n, (i, taken, read) :: rest => instruction i n taken read :: block (n + 1) rest

/-- The sequential end of a block, in code order. -/
noncomputable def blockEnd (C : Config) (n : ℕ) (b : List (RuleName × List Occ × List Occ)) : Config :=
  ConditionalSchedule.follow Occ.label C ((block n b).map StagedSourceEffects.Instruction.raw)

/-- **An executable deferred block is a run of translated firings.** -/
theorem block_run : ∀ (n : ℕ) (b : List (RuleName × List Occ × List Occ)) (C : Config),
    StagedSourceEffects.Executable A Occ.label C (block n b) →
      Relation.ReflTransGen (Translated schema) (C, n) (blockEnd C n b, n + b.length)
  | n, [], C, _ => by
      show Relation.ReflTransGen (Translated schema) (C, n) (C, n + 0)
      exact .refl
  | n, (i, taken, read) :: rest, C, ⟨valid, later⟩ => by
      have first : Translated schema (C, n) (((schema i).firing n taken read).result Occ.label C, n + 1) :=
        .fire i taken read valid
      have tail := block_run (n + 1) rest _ later
      have index : n + 1 + rest.length = n + ((i, taken, read) :: rest).length := by
        simp only [List.length_cons]; omega
      rw [index] at tail
      exact Relation.ReflTransGen.head first tail

/-- **Deferred effects commit at their cut, all or nothing**: the compiled block either is executable
and its result is the end of the block's translated run, or it is not and the configuration stays
exactly as it was. -/
theorem deferred_block (n : ℕ) (b : List (RuleName × List Occ × List Occ)) (C after : Config)
    (result : StagedSourceEffects.CompiledResult A Occ.label (StagedSourceEffects.compile Occ.label (block n b))
      C after) :
    (StagedSourceEffects.Executable A Occ.label C (block n b) ∧ after = blockEnd C n b ∧
        Relation.ReflTransGen (Translated schema) (C, n) (after, n + b.length)) ∨
      (¬ StagedSourceEffects.Executable A Occ.label C (block n b) ∧ after = C) := by
  rcases (StagedSourceEffects.compiled_result_iff_source A Occ.label (block n b) C after).mp result with
    ⟨ready, rfl⟩ | ⟨refused, rfl⟩
  · exact .inl ⟨ready, rfl, block_run n b C ready⟩
  · exact .inr ⟨refused, rfl⟩

/-- **A committed block is one actual firing at its cut**, with the knowledge (up to equivalence) and
the rows of the block's translated run in code order. -/
theorem deferred_one_firing (n : ℕ) (b : List (RuleName × List Occ × List Occ)) (C : Config)
    (ready : StagedSourceEffects.Executable A Occ.label C (block n b)) :
    let plan := (StagedSourceEffects.compile Occ.label (block n b)).raw
    let selected := CensusSourceCompilation.selection plan.effect
    let rule := CensusSourceCompilation.rule Occ.label plan.effect plan.equations
    PredicateQueryAdmission.Valid A Occ.label rule (plan.effect.queries.map PredicateQueryAdmission.Query.fixed)
        C selected ∧
      A.Equivalent (selected.result Occ.label rule C).equations (blockEnd C n b).equations ∧
      (selected.result Occ.label rule C).present = (blockEnd C n b).present ∧
      Relation.ReflTransGen (Translated schema) (C, n) (blockEnd C n b, n + b.length) :=
  let net := StagedSourceEffects.realize_net_under_retained_admission A Occ.label (block n b) C
    ((StagedSourceEffects.compile_exact A Occ.label (block n b) C).mpr ready)
  ⟨net.1, net.2.1, net.2.2, block_run n b C ready⟩

/-- Two threads: one adds `a`, one removes `z`; there is no fact `z`. -/
def twoEffects : List Sx := [ret (atom ka) (cons addK nil), ret (atom kz) (cons removeK nil)]
/-- After the addition. -/
def afterAddition : List Sx := [ret (atom ka) nil, fact (atom ka), ret (atom kz) (cons removeK nil)]

theorem afterAddition_successor : afterAddition ∈ ruleSuccessors .addK twoEffects := by decide
theorem no_removal_after_addition : ruleSuccessors .removeK afterAddition = [] := by decide

/-- **Control: deferred, the failed effects leave no trace; immediate, the addition stays.** From the
two threads, the addition fires as one translated firing whose result represents the fact `a`, and no
removal can fire there. Deferred, a block of that addition and any removal is not executable, and
its compiled result is the starting configuration. -/
theorem deferred_failed_branch_leaves_no_trace :
    ∃ taken read : List Occ, ((schema .addK).firing 1 taken read).Valid A Occ.label (initial twoEffects) ∧
      Represents (((schema .addK).firing 1 taken read).result Occ.label (initial twoEffects))
        (afterAddition : Multiset Sx) 2 ∧
      (∀ taken' read', ¬ ((schema .removeK).firing 2 taken' read').Valid A Occ.label
        (((schema .addK).firing 1 taken read).result Occ.label (initial twoEffects))) ∧
      ∀ taken' read' after,
        StagedSourceEffects.CompiledResult A Occ.label
          (StagedSourceEffects.compile Occ.label (block 1 [(.addK, taken, read), (.removeK, taken', read')]))
          (initial twoEffects) after → after = initial twoEffects := by
  have fires : (schema .addK).Fires (twoEffects : Multiset Sx) (afterAddition : Multiset Sx) :=
    (fires_iff_ruleSuccessors .addK twoEffects _).mpr ⟨afterAddition, afterAddition_successor, rfl⟩
  obtain ⟨taken, read, valid, rep⟩ := sound (schema_wellFormed .addK) (initial_represents twoEffects) fires
  have noRemoval : ∀ taken' read', ¬ ((schema .removeK).firing 2 taken' read').Valid A Occ.label
      (((schema .addK).firing 1 taken read).result Occ.label (initial twoEffects)) := by
    intro taken' read' valid'
    obtain ⟨W', removal, -⟩ := complete (schema_wellFormed .removeK) rep valid'
    obtain ⟨l, mem, -⟩ := (fires_iff_ruleSuccessors .removeK afterAddition W').mp removal
    rw [no_removal_after_addition] at mem
    cases mem
  refine ⟨taken, read, valid, rep, noRemoval, fun taken' read' after result => ?_⟩
  refine StagedSourceEffects.refused_has_no_residue ?_ result
  rintro ⟨-, valid', -⟩
  exact noRemoval taken' read' valid'

/-! ## Obstruction: atomic commits need computed rules -/

/-- **One translated firing changes few occurrences**: it removes at most its take patterns and makes
at most its made terms. -/
theorem firing_changes_bounded {C : Config} {n : ℕ} {i : RuleName} {taken read : List Occ}
    (valid : ((schema i).firing n taken read).Valid A Occ.label C) :
    (C.present \ (((schema i).firing n taken read).result Occ.label C).present).card ≤ (schema i).take.length ∧
      ((((schema i).firing n taken read).result Occ.label C).present \ C.present).card ≤ (schema i).make.length := by
  have present : (((schema i).firing n taken read).result Occ.label C).present =
      (C.present \ taken.toFinset) ∪ (madeAt n 0 (schema i).make).toFinset := rfl
  have takeLength : ((schema i).take.map (Pat.at n)).length = taken.length := valid.firing.take_length
  rw [List.length_map] at takeLength
  constructor
  · calc (C.present \ (((schema i).firing n taken read).result Occ.label C).present).card
        ≤ taken.toFinset.card := by
          refine Finset.card_le_card fun o ho => ?_
          rw [present, Finset.mem_sdiff, Finset.mem_union, Finset.mem_sdiff] at ho
          by_contra h
          exact ho.2 (.inl ⟨ho.1, h⟩)
      _ ≤ taken.length := List.toFinset_card_le taken
      _ = (schema i).take.length := takeLength.symm
  · calc ((((schema i).firing n taken read).result Occ.label C).present \ C.present).card
        ≤ (madeAt n 0 (schema i).make).toFinset.card := by
          refine Finset.card_le_card fun o ho => ?_
          rw [present, Finset.mem_sdiff, Finset.mem_union, Finset.mem_sdiff] at ho
          rcases ho.1 with old | made
          · exact absurd old.1 ho.2
          · exact made
      _ ≤ (madeAt n 0 (schema i).make).length := List.toFinset_card_le _
      _ = (schema i).make.length := by rw [← List.length_map Occ.label, madeAt_label, List.length_map]

/-- Every rule of the core takes at most two rows and makes at most two. -/
theorem schema_small (i : RuleName) : (schema i).take.length ≤ 2 ∧ (schema i).make.length ≤ 2 := by
  cases i <;> decide

/-- **No fixed rule of the core commits more than two new rows at once.** -/
theorem no_fixed_atomic_commit {C : Config} {n : ℕ} {i : RuleName} {taken read : List Occ}
    (valid : ((schema i).firing n taken read).Valid A Occ.label C) :
    ((((schema i).firing n taken read).result Occ.label C).present \ C.present).card ≤ 2 :=
  le_trans (firing_changes_bounded valid).2 (schema_small i).2

/-! ## Suspension -/

/-- A demand row. -/
def isDemand : Sx → Bool
  | .cell (.sym 33) _ => true
  | _ => false

def isDemandPat : Pat → Bool
  | .cell (.sym 33) _ => true
  | _ => false

/-- A pattern whose head is a rigid tag. -/
def rigidHead : Pat → Bool
  | .cell (.sym _) _ => true
  | _ => false

theorem isDemand_inst : ∀ (p : Pat), rigidHead p = true → ∀ θ : ℕ → Sx, isDemand (p.inst θ) = isDemandPat p
  | .cell (.sym k) _, _, _ => by
      by_cases h : k = 33
      · subst h; rfl
      · simp [Pat.inst, isDemand, isDemandPat, h]
  | .var _, h, _ => by simp [rigidHead] at h
  | .sym _, h, _ => by simp [rigidHead] at h
  | .cell (.var _) _, h, _ => by simp [rigidHead] at h
  | .cell (.cell _ _) _, h, _ => by simp [rigidHead] at h

/-- The number of demand rows. -/
def demands (W : Multiset Sx) : ℕ := W.countP fun s => isDemand s = true

theorem demands_push (l : List Sx) (F : Multiset Sx) :
    demands (push l F) = l.countP (fun s => isDemand s) + demands F := by
  rw [push_eq, demands, Multiset.countP_add, Multiset.coe_countP]
  simp [demands]

theorem countP_inst (ps : List Pat) (rigid : ∀ p ∈ ps, rigidHead p = true) (θ : ℕ → Sx) :
    (ps.map (Pat.inst θ)).countP (fun s => isDemand s) = ps.countP (fun p => isDemandPat p) := by
  rw [List.countP_map]
  exact List.countP_congr fun p hp => by
    simp only [Function.comp, isDemand_inst p (rigid p hp) θ]

theorem schema_rigid (i : RuleName) :
    (∀ p ∈ (schema i).take, rigidHead p = true) ∧ (∀ p ∈ (schema i).read, rigidHead p = true) ∧
      ∀ p ∈ (schema i).make, rigidHead p = true := by
  cases i <;> decide

/-- Demands made and consumed by each rule: only `demandK` makes one, only `resume` takes one. -/
theorem schema_demands (i : RuleName) :
    (schema i).make.countP (fun p => isDemandPat p) + (if i = .resume then 1 else 0) =
      (schema i).take.countP (fun p => isDemandPat p) + (if i = .demandK then 1 else 0) := by
  cases i <;> decide

/-- **Each rule's effect on demands.** -/
theorem demands_fires {i : RuleName} {W W' : Multiset Sx} (fires : (schema i).Fires W W') :
    demands W' + (if i = .resume then 1 else 0) = demands W + (if i = .demandK then 1 else 0) := by
  obtain ⟨θ, F, rfl, rfl⟩ := fires
  obtain ⟨takeRigid, readRigid, makeRigid⟩ := schema_rigid i
  rw [demands_push, demands_push, demands_push, demands_push, countP_inst _ takeRigid,
    countP_inst _ readRigid, countP_inst _ makeRigid]
  have := schema_demands i
  omega

/-- Runs labelled by their rules. -/
inductive Labeled : Multiset Sx → List RuleName → Multiset Sx → Prop
  | nil (W : Multiset Sx) : Labeled W [] W
  | cons {W W' W'' : Multiset Sx} {ls : List RuleName} (i : RuleName) (fires : (schema i).Fires W W')
      (rest : Labeled W' ls W'') : Labeled W (i :: ls) W''

theorem labeled_of_path {W W' : Multiset Sx} (path : Relation.ReflTransGen Step W W') :
    ∃ ls, Labeled W ls W' := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], .nil _⟩
  | head step _ ih =>
      obtain ⟨ls, rest⟩ := ih
      obtain ⟨i, fires⟩ := (step_iff_rewrites _ _).mp step
      exact ⟨i :: ls, .cons i fires rest⟩

/-- **The demand balance**: along every labelled run, the demands remaining plus the resumptions
equal the initial demands plus the demands made. -/
theorem demand_balance : ∀ {W W' : Multiset Sx} {ls : List RuleName}, Labeled W ls W' →
    demands W' + ls.count .resume = demands W + ls.count .demandK
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons i fires rest => by
      have step := demands_fires fires
      have later := demand_balance rest
      simp only [List.count_cons, beq_iff_eq]
      by_cases h₁ : i = .resume
      · subst h₁; simp at step ⊢; omega
      · by_cases h₂ : i = .demandK
        · subst h₂; simp at step ⊢; omega
        · simp [h₁, h₂] at step ⊢; omega

/-- **On the step, a taken occurrence never returns**: after a firing takes `o` from a represented
configuration, no configuration of any later translated run has `o` present. -/
theorem taken_never_again {C : Config} {W : Multiset Sx} {n : ℕ} (rep : Represents C W n)
    {i : RuleName} {taken read : List Occ} (valid : ((schema i).firing n taken read).Valid A Occ.label C)
    {o : Occ} (ho : o ∈ taken) {q : Config × ℕ}
    (run : Relation.ReflTransGen (Translated schema) (((schema i).firing n taken read).result Occ.label C, n + 1) q) :
    o ∉ q.1.present := by
  obtain ⟨-, -, pres, -⟩ := rep
  have scope : o.scope < n := (pres o (valid.firing.occurrences.taken_subset (List.mem_toFinset.mpr ho))).1
  suffices ∀ p : Config × ℕ, Relation.ReflTransGen (Translated schema)
      (((schema i).firing n taken read).result Occ.label C, n + 1) p → o ∉ p.1.present ∧ o.scope < p.2 from
    (this q run).1
  intro p path
  induction path with
  | refl =>
      refine ⟨fun present => ?_, Nat.lt_succ_of_lt scope⟩
      have := valid.firing.consumed_removed ho
      exact this present
  | tail _ step ih =>
      cases step with
      | @fire C' m j taken' read' valid' =>
          refine ⟨fun present => ?_, Nat.lt_succ_of_lt ih.2⟩
          have present' : (((schema j).firing m taken' read').result Occ.label C').present =
              (C'.present \ taken'.toFinset) ∪ (madeAt m 0 (schema j).make).toFinset := rfl
          rw [present', Finset.mem_union, Finset.mem_sdiff] at present
          rcases present with ⟨old, -⟩ | made
          · exact ih.1 old
          · have := (madeAt_mem (List.mem_toFinset.mp made)).1
            omega

/-- A thread about to suspend its continuation, and two demands of it. -/
def suspension : List Sx :=
  [ev (await ku) nil nil, demand ku (atom ka), demand ku (atom kb)]

/-- The end of every run: the continuation stays suspended, and it was resumed once with each
demanded value. -/
def resumedOnce : List Sx := [susp ku nil, ret (atom ka) nil, ret (atom kb) nil]

theorem suspension_closed : SuccessorClosed (reach 4 [suspension]) = true := by decide

theorem suspension_halted : (halted (reach 4 [suspension])).all (fun H => H.isPerm resumedOnce) = true ∧
    halted (reach 4 [suspension]) ≠ [] := by decide

/-- **Exactly once per demand**: every halted run resumed the suspended continuation once for each
demand, and one run does halt. -/
theorem exactly_once_per_demand :
    (∀ W, Relation.ReflTransGen Step (suspension : Multiset Sx) W → (∀ W', ¬ Step W W') →
        W = (resumedOnce : Multiset Sx)) ∧
      Relation.ReflTransGen Step (suspension : Multiset Sx) (resumedOnce : Multiset Sx) := by
  obtain ⟨all, nonempty⟩ := suspension_halted
  obtain ⟨reached, every⟩ := halted_runs suspension_closed
  refine ⟨fun W path stuck => ?_, ?_⟩
  · obtain ⟨H, mem, rfl⟩ := every W path stuck
    exact Multiset.coe_eq_coe.mpr (List.isPerm_iff.mp (List.all_eq_true.mp all H mem))
  · obtain ⟨H, rest, eq⟩ := List.exists_cons_of_ne_nil nonempty
    have mem : H ∈ halted (reach 4 [suspension]) := by rw [eq]; exact List.mem_cons_self
    have := (reached H mem).1
    rwa [Multiset.coe_eq_coe.mpr (List.isPerm_iff.mp (List.all_eq_true.mp all H mem))] at this

/-- A resumption that reads its demand instead of taking it. -/
def replaySchema : Schema := ⟨[], [p2 33 (.var 0) (.var 1), p2 32 (.var 0) (.var 2)], [p2 30 (.var 1) (.var 2)]⟩

/-- **Control: a resumption that reads its demand replays it without bound.** -/
theorem replay_unbounded (k v κ : Sx) (m : ℕ) :
    Relation.ReflTransGen replaySchema.Fires ({demand k v, susp k κ} : Multiset Sx)
      (Multiset.replicate m (ret v κ) + {demand k v, susp k κ}) := by
  induction m with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ m ih =>
      refine ih.tail ⟨args [k, v, κ], Multiset.replicate m (ret v κ), ?_, ?_⟩
      · show Multiset.replicate m (ret v κ) + {demand k v, susp k κ} =
          demand k v ::ₘ susp k κ ::ₘ Multiset.replicate m (ret v κ)
        rw [add_comm]
        rfl
      · show Multiset.replicate (m + 1) (ret v κ) + {demand k v, susp k κ} =
          ret v κ ::ₘ demand k v ::ₘ susp k κ ::ₘ Multiset.replicate m (ret v κ)
        rw [Multiset.replicate_succ, add_comm]
        show demand k v ::ₘ susp k κ ::ₘ ret v κ ::ₘ Multiset.replicate m (ret v κ) = _
        rw [Multiset.cons_swap (susp k κ), Multiset.cons_swap (demand k v)]

/-- The replaying schema is not a rule of the core's form: it takes nothing. -/
theorem replay_not_wellFormed : ¬ replaySchema.WellFormed := fun wf => by
  have := wf.single_read
  simp [replaySchema] at this

#print axioms immediate_effects_leave_a_trace
#print axioms block_run
#print axioms deferred_block
#print axioms deferred_one_firing
#print axioms deferred_failed_branch_leaves_no_trace
#print axioms firing_changes_bounded
#print axioms no_fixed_atomic_commit
#print axioms demands_fires
#print axioms labeled_of_path
#print axioms demand_balance
#print axioms taken_never_again
#print axioms exactly_once_per_demand
#print axioms replay_unbounded
#print axioms replay_not_wellFormed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
