import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEffects

/-!
# `defer` as a source construct, compiled per block

A thread `defer B` runs a block `B` of fact effects, additions and removals, in order, and commits
them at once: either the whole block happens, or nothing does (`DeferStep`, over the sequential
effects `Effects`). R82's obstruction (`Program.no_fixed_atomic_commit`) says that a fixed family of
rules cannot commit unboundedly many rows in one firing, so the construct is compiled **per block**:

* **The block's schemas** (`blockSchemas`): one that takes the `defer` row and makes the finished
  row, then one ground schema per effect. Run in order they present the reference semantics
  (`defer_chain`, `chain_defer`).
* **Staged on the step** (`blockCode`): the schemas' firings at consecutive scopes, as instructions
  of `StagedSourceEffects`, compiled by `StagedSourceEffects.compile` into one plan.
* **Adequacy** (`defer_sound`, `defer_complete`): a reference commit from represented rows is an
  executable block whose compiled result represents the committed rows; and an executable block is
  a reference commit. The compiled result is the block's sequential end or the unchanged
  configuration (`defer_compiled_result`), and a committed block is one actual firing at its cut
  (`defer_one_firing`).
* **No partial effects** (`no_partial_effects`): `defer [add b, remove a]` without a fact `a` has
  no reference step, no executable block for any selection, and its compiled result leaves the
  configuration exactly as it was: the addition of `b` does not happen.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramSourceDefer

open ProgramRows ProgramTranslation Program

/-! ## Ground patterns -/

/-- A row as a pattern without variables. -/
def lit : Sx → Pat
  | .sym k => .sym k
  | .cell a b => .cell (lit a) (lit b)

theorem lit_inst (θ : ℕ → Sx) : ∀ s : Sx, (lit s).inst θ = s
  | .sym _ => rfl
  | .cell a b => by
      show Sx.cell ((lit a).inst θ) ((lit b).inst θ) = _
      rw [lit_inst θ a, lit_inst θ b]

theorem lit_vars : ∀ s : Sx, (lit s).vars = []
  | .sym _ => rfl
  | .cell a b => by simp [lit, Pat.vars, lit_vars a, lit_vars b]

/-! ## The construct and its reference semantics -/

/-- A fact effect. -/
inductive Effect where
  | add (v : Sx)
  | remove (v : Sx)

/-- A block of effects, in order. -/
abbrev Block := List Effect

def effectCode : Effect → Sx
  | .add v => t1 115 v
  | .remove v => t1 116 v

def codeOfBlock : Block → Sx
  | [] => nil
  | e :: B => cons (effectCode e) (codeOfBlock B)

/-- The thread running `defer B`. -/
def deferRow (B : Block) : Sx := t1 117 (codeOfBlock B)

/-- The finished thread. -/
def doneRow : Sx := t0 118

/-- **The block's effects in order**: an addition makes a fact, a removal takes one. -/
inductive Effects : Block → Multiset Sx → Multiset Sx → Prop
  | nil (W : Multiset Sx) : Effects [] W W
  | add (v : Sx) {B : Block} {W W' : Multiset Sx} : Effects B (fact v ::ₘ W) W' → Effects (.add v :: B) W W'
  | remove (v : Sx) {B : Block} {W W' : Multiset Sx} :
      Effects B W W' → Effects (.remove v :: B) (fact v ::ₘ W) W'

/-- **The reference semantics of `defer`**: the block's effects, committed at once with the thread
finishing. A block whose effects cannot all happen has no step. -/
inductive DeferStep : Multiset Sx → Multiset Sx → Prop
  | commit (B : Block) {W W' : Multiset Sx} (effects : Effects B W W') :
      DeferStep (deferRow B ::ₘ W) (doneRow ::ₘ W')

/-! ## The block's schemas -/

def startSchema (B : Block) : Schema := ⟨[lit (deferRow B)], [], [lit doneRow]⟩

def effectSchema : Effect → Schema
  | .add v => ⟨[], [], [lit (fact v)]⟩
  | .remove v => ⟨[lit (fact v)], [], []⟩

/-- **The schemas computed from a block.** -/
def blockSchemas (B : Block) : List Schema := startSchema B :: B.map effectSchema

theorem schema_wellFormed_of_lit {r : Schema} (ground : ∀ q ∈ r.make, q.vars = []) (noRead : r.read = []) :
    r.WellFormed :=
  ⟨fun q hq x hx => by rw [ground q hq] at hx; exact absurd hx List.not_mem_nil,
    by rw [noRead]; exact Nat.zero_le 1⟩

theorem blockSchemas_wellFormed (B : Block) : ∀ r ∈ blockSchemas B, r.WellFormed ∧ r.read = [] := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact ⟨schema_wellFormed_of_lit (by simp [startSchema, lit_vars]) rfl, rfl⟩
  · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hr
    cases e with
    | add v => exact ⟨schema_wellFormed_of_lit (by simp [effectSchema, lit_vars]) rfl, rfl⟩
    | remove v => exact ⟨schema_wellFormed_of_lit (by simp [effectSchema]) rfl, rfl⟩

/-- Schemas fired in order. -/
inductive Chain : List Schema → Multiset Sx → Multiset Sx → Prop
  | nil (W : Multiset Sx) : Chain [] W W
  | cons {r : Schema} {rs : List Schema} {W W₁ W₂ : Multiset Sx} :
      r.Fires W W₁ → Chain rs W₁ W₂ → Chain (r :: rs) W W₂

theorem fires_add (v : Sx) (W : Multiset Sx) : (effectSchema (.add v)).Fires W (fact v ::ₘ W) :=
  ⟨fun _ => .sym 0, W, rfl, by simp [effectSchema, push, lit_inst]⟩

theorem fires_remove (v : Sx) (W : Multiset Sx) : (effectSchema (.remove v)).Fires (fact v ::ₘ W) W :=
  ⟨fun _ => .sym 0, W, by simp [effectSchema, push, lit_inst], rfl⟩

theorem fires_start (B : Block) (W : Multiset Sx) :
    (startSchema B).Fires (deferRow B ::ₘ W) (doneRow ::ₘ W) :=
  ⟨fun _ => .sym 0, W, by simp [startSchema, push, lit_inst], by simp [startSchema, push, lit_inst]⟩

theorem effects_chain {B : Block} {W W' : Multiset Sx} (effects : Effects B W W') (x : Sx) :
    Chain (B.map effectSchema) (x ::ₘ W) (x ::ₘ W') := by
  induction effects with
  | nil W => exact .nil _
  | @add v B W W' _ ih =>
      have step := fires_add v (x ::ₘ W)
      rw [Multiset.cons_swap] at step
      exact .cons step ih
  | @remove v B W W' _ ih =>
      have step := fires_remove v (x ::ₘ W)
      rw [Multiset.cons_swap] at step
      exact .cons step ih

theorem fact_ne_done (v : Sx) : fact v ≠ doneRow := by simp [fact, doneRow, t1, t0]

theorem chain_effects : ∀ (B : Block) {W X : Multiset Sx}, Chain (B.map effectSchema) (doneRow ::ₘ W) X →
    ∃ W', X = doneRow ::ₘ W' ∧ Effects B W W'
  | [], W, X, chain => by
      cases chain
      exact ⟨W, rfl, .nil W⟩
  | .add v :: B, W, X, chain => by
      cases chain with
      | cons fires rest =>
          obtain ⟨θ, F, hW, rfl⟩ := fires
          simp only [effectSchema, List.map_nil, push, List.foldr_nil] at hW
          subst hW
          simp only [effectSchema, List.map_cons, List.map_nil, push, List.foldr_cons, List.foldr_nil,
            lit_inst] at rest
          rw [Multiset.cons_swap] at rest
          obtain ⟨W', rfl, effects⟩ := chain_effects B rest
          exact ⟨W', rfl, .add v effects⟩
  | .remove v :: B, W, X, chain => by
      cases chain with
      | cons fires rest =>
          obtain ⟨θ, F, hW, rfl⟩ := fires
          simp only [effectSchema, List.map_cons, List.map_nil, push, List.foldr_cons, List.foldr_nil,
            lit_inst] at hW
          rcases Multiset.cons_eq_cons.mp hW with ⟨same, -⟩ | ⟨-, cs, hcs, hF⟩
          · exact absurd same.symm (fact_ne_done v)
          · rw [hF] at rest
            obtain ⟨W', rfl, effects⟩ := chain_effects B rest
            rw [hcs]
            exact ⟨W', rfl, .remove v effects⟩

/-- **A reference commit is the block's schemas fired in order.** -/
theorem defer_chain {V V' : Multiset Sx} (step : DeferStep V V') :
    ∃ B W, V = deferRow B ::ₘ W ∧ Chain (blockSchemas B) V V' := by
  cases step with
  | commit B effects =>
      exact ⟨B, _, rfl, .cons (fires_start B _) (effects_chain effects doneRow)⟩

theorem chain_effects_of_block (B : Block) {W V' : Multiset Sx}
    (chain : Chain (blockSchemas B) (deferRow B ::ₘ W) V') :
    ∃ W', V' = doneRow ::ₘ W' ∧ Effects B W W' := by
  cases chain with
  | cons fires rest =>
      obtain ⟨θ, F, hW, rfl⟩ := fires
      simp only [startSchema, List.map_cons, List.map_nil, push, List.foldr_cons, List.foldr_nil,
        lit_inst] at hW
      have hF : W = F := (Multiset.cons_inj_right _).mp hW
      subst hF
      simp only [startSchema, List.map_cons, List.map_nil, push, List.foldr_cons, List.foldr_nil,
        lit_inst] at rest
      exact chain_effects B rest

/-- **The block's schemas fired in order are a reference commit.** -/
theorem chain_defer (B : Block) {W V' : Multiset Sx} (chain : Chain (blockSchemas B) (deferRow B ::ₘ W) V') :
    DeferStep (deferRow B ::ₘ W) V' := by
  obtain ⟨W', rfl, effects⟩ := chain_effects_of_block B chain
  exact .commit B effects

/-! ## Staged on the step -/

/-- The firing of a schema at scope `n` on taken occurrences, as an instruction. -/
def instruction (r : Schema) (n : ℕ) (taken : List Occ) :
    StagedSourceEffects.Instruction Tm (Mettapedia.Logic.LP.Subst rows) Occ :=
  ⟨r.rule n, ⟨taken, [], madeAt n 0 r.make⟩, []⟩

/-- Schemas with their selections, as instructions at consecutive scopes. -/
def codeOn : ℕ → List (Schema × List Occ) →
    List (StagedSourceEffects.Instruction Tm (Mettapedia.Logic.LP.Subst rows) Occ)
  | _, [] => []
  | n, (r, taken) :: rest => instruction r n taken :: codeOn (n + 1) rest

/-- The sequential end of a staged code. -/
noncomputable def codeEnd (C : Config) (code : List (StagedSourceEffects.Instruction Tm
    (Mettapedia.Logic.LP.Subst rows) Occ)) : Config :=
  ConditionalSchedule.follow Occ.label C (code.map StagedSourceEffects.Instruction.raw)

theorem chain_sound : ∀ (rs : List Schema), (∀ r ∈ rs, r.WellFormed ∧ r.read = []) →
    ∀ {W W' : Multiset Sx}, Chain rs W W' → ∀ {C : Config} {n : ℕ}, Represents C W n →
      ∃ sel : List (List Occ), sel.length = rs.length ∧
        StagedSourceEffects.Executable A Occ.label C (codeOn n (rs.zip sel)) ∧
        Represents (codeEnd C (codeOn n (rs.zip sel))) W' (n + rs.length)
  | [], _, W, W', chain, C, n, rep => by
      cases chain
      exact ⟨[], rfl, rep.1, rep⟩
  | r :: rs, wf, W, W', chain, C, n, rep => by
      cases chain with
      | cons fires rest =>
          obtain ⟨wfr, noRead⟩ := wf r List.mem_cons_self
          obtain ⟨taken, read, valid, rep₁⟩ := sound wfr rep fires
          have readNil : read = [] := List.length_eq_zero_iff.mp (by
            have h : (r.read.map (Pat.at n)).length = read.length := valid.firing.read_length
            rw [List.length_map, noRead] at h
            exact h.symm)
          subst readNil
          obtain ⟨sel, len, exec, rep'⟩ :=
            chain_sound rs (fun r' h => wf r' (List.mem_cons_of_mem _ h)) rest rep₁
          refine ⟨taken :: sel, by simp [len], show PredicateQueryAdmission.Valid _ _ _ _ _ _ ∧
            StagedSourceEffects.Executable _ _ _ _ from ⟨valid, exec⟩, ?_⟩
          have index : n + (r :: rs).length = n + 1 + rs.length := by
            simp only [List.length_cons]; omega
          rw [index]
          exact rep'

theorem chain_complete : ∀ (rs : List Schema), (∀ r ∈ rs, r.WellFormed ∧ r.read = []) →
    ∀ (sel : List (List Occ)), sel.length = rs.length → ∀ {W : Multiset Sx} {C : Config} {n : ℕ},
      Represents C W n → StagedSourceEffects.Executable A Occ.label C (codeOn n (rs.zip sel)) →
        ∃ W', Chain rs W W' ∧ Represents (codeEnd C (codeOn n (rs.zip sel))) W' (n + rs.length)
  | [], _, [], _, W, C, n, rep, _ => ⟨W, .nil W, rep⟩
  | [], _, _ :: _, len, _, _, _, _, _ => by simp at len
  | _ :: _, _, [], len, _, _, _, _, _ => by simp at len
  | r :: rs, wf, taken :: sel, len, W, C, n, rep, ready => by
      obtain ⟨valid, exec⟩ := ready
      obtain ⟨wfr, -⟩ := wf r List.mem_cons_self
      obtain ⟨W₁, fires, rep₁⟩ := complete (read := []) wfr rep valid
      obtain ⟨W', rest, rep'⟩ := chain_complete rs (fun r' h => wf r' (List.mem_cons_of_mem _ h)) sel
        (by simpa using len) rep₁ exec
      refine ⟨W', .cons fires rest, ?_⟩
      have index : n + (r :: rs).length = n + 1 + rs.length := by
        simp only [List.length_cons]; omega
      rw [index]
      exact rep'

/-! ## Adequacy -/

/-- **Soundness**: a reference commit from represented rows is an executable staged block of the
committed block's schemas, whose end represents the committed rows. -/
theorem defer_sound {V V' : Multiset Sx} (step : DeferStep V V') {C : Config} {n : ℕ}
    (rep : Represents C V n) :
    ∃ (B : Block) (sel : List (List Occ)), sel.length = (blockSchemas B).length ∧
      StagedSourceEffects.Executable A Occ.label C (codeOn n ((blockSchemas B).zip sel)) ∧
      Represents (codeEnd C (codeOn n ((blockSchemas B).zip sel))) V' (n + (blockSchemas B).length) := by
  obtain ⟨B, W, -, chain⟩ := defer_chain step
  obtain ⟨sel, len, exec, rep'⟩ := chain_sound _ (blockSchemas_wellFormed B) chain rep
  exact ⟨B, sel, len, exec, rep'⟩

/-- The rows of the block's code are injective in the block. -/
theorem codeOfBlock_inj : ∀ {B B' : Block}, codeOfBlock B = codeOfBlock B' → B = B'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [codeOfBlock, nil, cons, t0, t2] at h
  | _ :: _, [], h => by simp [codeOfBlock, nil, cons, t0, t2] at h
  | e :: B, e' :: B', h => by
      simp only [codeOfBlock, cons, t2, Sx.cell.injEq, true_and] at h
      obtain ⟨he, hB⟩ := h
      have : e = e' := by
        cases e <;> cases e' <;> simp_all [effectCode, t1]
      rw [this, codeOfBlock_inj hB]

/-- **Completeness**: an executable staged block of a `defer` row's schemas, from represented rows,
is a reference commit, and its end represents the committed rows. -/
theorem defer_complete (B : Block) (sel : List (List Occ)) (len : sel.length = (blockSchemas B).length)
    {W : Multiset Sx} {C : Config} {n : ℕ} (rep : Represents C (deferRow B ::ₘ W) n)
    (exec : StagedSourceEffects.Executable A Occ.label C (codeOn n ((blockSchemas B).zip sel))) :
    ∃ V', DeferStep (deferRow B ::ₘ W) V' ∧
      Represents (codeEnd C (codeOn n ((blockSchemas B).zip sel))) V' (n + (blockSchemas B).length) := by
  obtain ⟨V', chain, rep'⟩ := chain_complete _ (blockSchemas_wellFormed B) sel len rep exec
  exact ⟨V', chain_defer B chain, rep'⟩

/-- **The compiled block commits all or nothing**: its result is the block's sequential end when the
block is executable, and the unchanged configuration when it is not. -/
theorem defer_compiled_result (code : List (StagedSourceEffects.Instruction Tm
    (Mettapedia.Logic.LP.Subst rows) Occ)) (C after : Config) :
    StagedSourceEffects.CompiledResult A Occ.label (StagedSourceEffects.compile Occ.label code) C after ↔
      (StagedSourceEffects.Executable A Occ.label C code ∧ after = codeEnd C code) ∨
        (¬ StagedSourceEffects.Executable A Occ.label C code ∧ after = C) :=
  StagedSourceEffects.compiled_result_iff_source A Occ.label code C after

/-- **A committed block is one actual firing at its cut**, with the knowledge (up to equivalence)
and the rows of the block's sequential end. -/
theorem defer_one_firing (code : List (StagedSourceEffects.Instruction Tm
    (Mettapedia.Logic.LP.Subst rows) Occ)) (C : Config)
    (ready : StagedSourceEffects.Executable A Occ.label C code) :
    let plan := (StagedSourceEffects.compile Occ.label code).raw
    let selected := CensusSourceCompilation.selection plan.effect
    let rule := CensusSourceCompilation.rule Occ.label plan.effect plan.equations
    PredicateQueryAdmission.Valid A Occ.label rule (plan.effect.queries.map PredicateQueryAdmission.Query.fixed)
        C selected ∧
      A.Equivalent (selected.result Occ.label rule C).equations (codeEnd C code).equations ∧
      (selected.result Occ.label rule C).present = (codeEnd C code).present :=
  StagedSourceEffects.realize_net_under_retained_admission A Occ.label code C
    ((StagedSourceEffects.compile_exact A Occ.label code C).mpr ready)

/-! ## No partial effects -/

def kb : Sx := atom (.sym 120)
def ka' : Sx := atom (.sym 121)

/-- `defer [add b, remove a]`. -/
def addThenRemove : Block := [.add kb, .remove ka']

theorem no_effects (W' : Multiset Sx) : ¬ Effects addThenRemove 0 W' := by
  intro effects
  cases effects with
  | add _ rest =>
      generalize hW : (fact kb ::ₘ (0 : Multiset Sx)) = W₀ at rest
      cases rest with
      | @remove v B W₁ W'' _ =>
          have member : fact ka' ∈ fact kb ::ₘ (0 : Multiset Sx) := by
            rw [hW]; exact Multiset.mem_cons_self _ _
          simp [fact, kb, ka', atom, t1] at member

/-- **No partial effects**: without a fact `a`, `defer [add b, remove a]` has no reference step, no
staged block of its schemas is executable for any selection, and the compiled result is the
unchanged configuration: the fact `b` is never added. -/
theorem no_partial_effects {C : Config} {n : ℕ} (rep : Represents C {deferRow addThenRemove} n) :
    (∀ V', ¬ DeferStep {deferRow addThenRemove} V') ∧
      ∀ (sel : List (List Occ)), sel.length = (blockSchemas addThenRemove).length →
        ¬ StagedSourceEffects.Executable A Occ.label C (codeOn n ((blockSchemas addThenRemove).zip sel)) ∧
        ∀ after, StagedSourceEffects.CompiledResult A Occ.label
          (StagedSourceEffects.compile Occ.label (codeOn n ((blockSchemas addThenRemove).zip sel))) C after →
            after = C := by
  have noStep : ∀ V', ¬ DeferStep {deferRow addThenRemove} V' := by
    intro V' step
    obtain ⟨B, W, same, chain⟩ := defer_chain step
    obtain ⟨hB, rfl⟩ := (Multiset.singleton_eq_cons_iff _).mp same
    have : addThenRemove = B := codeOfBlock_inj (by simpa [deferRow, t1] using hB)
    subst this
    obtain ⟨W', -, effects⟩ := chain_effects_of_block addThenRemove (W := 0) chain
    exact no_effects W' effects
  have rep' : Represents C (deferRow addThenRemove ::ₘ 0) n := rep
  refine ⟨noStep, fun sel len => ?_⟩
  have refused : ¬ StagedSourceEffects.Executable A Occ.label C
      (codeOn n ((blockSchemas addThenRemove).zip sel)) := fun exec => by
    obtain ⟨V', step, -⟩ := defer_complete addThenRemove sel len rep' exec
    exact noStep V' step
  exact ⟨refused, fun after result => StagedSourceEffects.refused_has_no_residue refused result⟩

#print axioms lit_inst
#print axioms blockSchemas_wellFormed
#print axioms defer_chain
#print axioms chain_defer
#print axioms chain_sound
#print axioms chain_complete
#print axioms defer_sound
#print axioms defer_complete
#print axioms defer_compiled_result
#print axioms defer_one_firing
#print axioms no_partial_effects

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramSourceDefer
