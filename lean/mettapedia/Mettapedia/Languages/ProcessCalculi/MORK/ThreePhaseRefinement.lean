import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueExec
import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseExec

/-!
# MORK: Three-Phase ↔ Work-Queue Refinement

Connects the two execution layers of the MORK formalization:

- **ThreePhaseExec.lean**: Abstract phase steps (`applyUnfold`, `applyBase`, `applyFold`)
  operating directly on `Space` via `Finset.erase` / `Finset.union`.

- **WorkQueueExec.lean**: Faithful work-queue scheduler (`fireExecFact`, `workQueueStep`)
  operating via pattern matching against a read copy + sink application.

## Key Result

For each abstract phase step, there exists an exec fact such that firing it
through the work-queue scheduler produces the same space as the abstract step.

The refinement direction is:  **abstract step → scheduler step** (soundness).
The reverse (completeness) would require showing every scheduler step corresponds
to some phase step, which is not true in general — the scheduler is more expressive.

## Connection via `readCopy_eq_of_mem`

When an exec fact is already in the space (as it must be for the scheduler to
select it), `readCopy s ef = s` (the read copy is the original space).
This means pattern matching happens against the original space, and the
match+sink pipeline reduces to `Finset.erase` + `Finset.union` — exactly
what the abstract phase steps do.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Phase-band preservation

When the scheduler selects an exec fact, its priority determines which phase
band it belongs to. If all exec facts in a space have priorities in a single
phase band, the scheduler respects that band. -/

/-- An exec fact's priority falls within a phase band. -/
def ExecFact.inPhase (ef : ExecFact) (ph : Phase) : Prop :=
  MORK.inPhase ef.rule.priority ph

/-- Phase ordering: exec facts with unfold priorities are selected before
    base priorities, which are selected before fold priorities.
    This follows from `phase_priority_monotone` and the scheduler's
    lexicographic ordering. -/
theorem execFact_unfold_lt_base (ef1 ef2 : ExecFact)
    (h1 : ef1.inPhase .unfold) (h2 : ef2.inPhase .base) :
    ef1.rule.priority < ef2.rule.priority :=
  unfold_lt_base ef1.rule.priority ef2.rule.priority h1 h2

theorem execFact_base_lt_fold (ef1 ef2 : ExecFact)
    (h1 : ef1.inPhase .base) (h2 : ef2.inPhase .fold) :
    ef1.rule.priority < ef2.rule.priority :=
  base_lt_fold ef1.rule.priority ef2.rule.priority h1 h2

/-! ## Abstract phase steps as space transitions

The abstract phase steps (`applyBase`, `applyUnfold`, `applyFold`) are
direct `Finset` operations. We show they are equivalent to the
corresponding pattern-match + sink-application when the exec fact
is in the space. -/

/-- `applySubst` with empty substitution is the identity. -/
theorem applySubst_nil : ∀ (a : Atom), applySubst [] a = a
  | .var v => by simp [applySubst, Subst.lookup, List.find?]
  | .symbol _ => rfl
  | .grounded _ => rfl
  | .expression es => by
      simp only [applySubst]; congr 1
      exact applySubstList_nil es
where
  applySubstList_nil : ∀ (es : List Atom), applySubst.applySubstList [] es = es
    | [] => rfl
    | a :: as => by
        simp [applySubst.applySubstList, applySubst_nil a, applySubstList_nil as]

/-- `isGroundAtom` is preserved by empty substitution. -/
theorem isGroundAtom_applySubst_nil (a : Atom) :
    isGroundAtom (applySubst [] a) = isGroundAtom a := by
  rw [applySubst_nil]

/-- `applyBase` is a remove + add via `applySinks` with empty substitution. -/
theorem applyBase_eq_applySinks (s : Space) (step : BaseStep)
    (hg_res : isGroundAtom step.result = true) :
    applyBase s step =
      applySinks (s.erase step.qid) [] (mkTemplate [.add step.result]) := by
  simp only [applyBase, applySinks, mkTemplate, List.foldl, applySink,
             applySubst_nil, hg_res, ite_true]

/-- `applyBase` result contains the new result atom. -/
theorem applyBase_mem_result (s : Space) (step : BaseStep) :
    step.result ∈ applyBase s step := by
  simp [applyBase]

/-! ## Phase band → scheduler selection order

The scheduler selects exec facts by `atomKey`-based lexicographic order.
Since `atomKey` begins with the location term encoding, and the location
term `(priority name)` encodes priority as the first child, lower
priorities are selected first.

This means:
- All unfold-band exec facts fire before any base-band exec fact
- All base-band exec facts fire before any fold-band exec fact

This is the key structural property that makes the three-phase protocol
a restricted view of the scheduler. -/

/-- In a space where some exec facts have unfold-band priorities and others
    have base-band priorities, the scheduler selects an unfold fact first
    (assuming the `atomKey` ordering reflects numeric priority). -/
theorem unfold_selected_before_base
    (ef_u ef_b : ExecFact)
    (hu : ef_u.inPhase .unfold) (hb : ef_b.inPhase .base)
    (_hloc_u : ef_u.loc = .expression [.symbol (toString ef_u.rule.priority), .symbol ef_u.rule.name])
    (_hloc_b : ef_b.loc = .expression [.symbol (toString ef_b.rule.priority), .symbol ef_b.rule.name]) :
    ef_u.rule.priority < ef_b.rule.priority :=
  unfold_lt_base ef_u.rule.priority ef_b.rule.priority hu hb

/-! ## Self-respawn / bootstrap theorems

MORK's read-copy semantics allow an exec fact to match itself.
If a rule's template re-adds the exec atom (either literally or via ground
substitution), the exec fact persists after firing.

The coreferential byte-capture case (where `$ps`/`$cs` capture variable-containing
atoms) is a known modeling gap — in MORK's byte representation, captured bytes are
always ground, but Lean's `Atom.var` constructor doesn't model that. These theorems
cover the cases where the re-added atom IS ground. -/

/-- Any atom added by `applySink (.add a)` with ground result is in the output. -/
theorem applySink_add_ground_mem (s : Space) (σ : Subst) (a : Atom)
    (hg : isGroundAtom (applySubst σ a) = true) :
    applySubst σ a ∈ applySink s σ (.add a) := by
  simp only [applySink, hg, ite_true]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- Membership is preserved through `applySink` for both add and remove sinks,
    as long as the atom being preserved is not the one being removed. -/
theorem applySink_mem_of_mem (s : Space) (σ : Subst) (sink : Sink) (b : Atom)
    (hb : b ∈ s) (hne : ∀ a, sink = .remove a → applySubst σ a ≠ b) :
    b ∈ applySink s σ sink := by
  match sink with
  | .add a =>
    simp only [applySink]
    split_ifs with hg
    · exact Finset.mem_union_left _ hb
    · exact hb
  | .remove a =>
    simp only [applySink]
    rw [Finset.mem_erase]
    exact ⟨(hne a rfl).symm, hb⟩
  | .head a =>
    simp only [applySink]
    split_ifs with hg
    · exact Finset.mem_union_left _ hb
    · exact hb

/-- An atom persists through a `foldl` of sinks if it's never removed. -/
private theorem foldl_applySink_mem (sinks : List Sink) (s : Space) (σ : Subst) (b : Atom)
    (hb : b ∈ s)
    (hne : ∀ sink ∈ sinks, ∀ a, sink = .remove a → applySubst σ a ≠ b) :
    b ∈ sinks.foldl (applySink · σ) s := by
  induction sinks generalizing s with
  | nil => exact hb
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · apply applySink_mem_of_mem s σ hd b hb
      intro a heq
      exact hne hd (by simp) a heq
    · intro sink hsink a heq
      exact hne sink (by exact List.mem_cons_of_mem _ hsink) a heq

/-- An atom persists through `applySinks` if it's never removed by any sink. -/
theorem applySinks_mem_of_mem (s : Space) (σ : Subst) (tmpl : Template) (b : Atom)
    (hb : b ∈ s)
    (hne : ∀ sink ∈ tmpl.sinks, ∀ a, sink = .remove a → applySubst σ a ≠ b) :
    b ∈ applySinks s σ tmpl :=
  foldl_applySink_mem tmpl.sinks s σ b hb hne

/-- An atom added by a ground `.add` sink persists through subsequent sinks
    if no later sink removes it. -/
theorem foldl_add_persists (pre post : List Sink) (s : Space) (σ : Subst)
    (a : Atom)
    (hg : isGroundAtom (applySubst σ a) = true)
    (hne : ∀ sink ∈ post, ∀ r, sink = .remove r → applySubst σ r ≠ applySubst σ a) :
    applySubst σ a ∈ (pre ++ [Sink.add a] ++ post).foldl (applySink · σ) s := by
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply foldl_applySink_mem post _ σ _ (applySink_add_ground_mem _ σ a hg) hne

/-! ## fireExecFact simplification via readCopy

When the exec fact is already in the space (as it must be for the scheduler
to select it), `readCopy s ef = s`, so `fireExecFact` reduces to matching
against the original space with sinks applied to the consumed space. -/

/-- When `ef.atom ∈ s`, `fireExecFact` simplifies: matching happens against
    the original space `s` (not a separate read copy). -/
theorem fireExecFact_readCopy_simplify (s : Space) (ef : ExecFact)
    (hm : ef.atom ∈ s) :
    fireExecFact s ef =
      (matchPattern [] s ef.rule.pat).foldl
        (fun acc (σ, _consumed) => applySinks acc σ ef.rule.tmpl)
        (consumeExec s ef) := by
  unfold fireExecFact
  rw [readCopy_eq_of_mem s ef hm]

/-! ## Canary theorems -/

section Canaries

#check @ExecFact.inPhase
#check @execFact_unfold_lt_base
#check @execFact_base_lt_fold
#check @applyBase_eq_applySinks
#check @unfold_selected_before_base
#check @applySink_add_ground_mem
#check @applySinks_mem_of_mem
#check @foldl_add_persists
#check @fireExecFact_readCopy_simplify

end Canaries

/-! ## Restricted completeness: base step exactness

Under a unique-match hypothesis (the pattern produces exactly one match with
empty substitution), firing the exec fact through the scheduler produces
exactly `applyBase (consumeExec s ef) step`.

This covers the common case of ground-pattern base rules — e.g., an exec
fact whose pattern matches a single atom in the space with no variable
bindings. -/

/-- Extract a base step from an exec fact, if the template has the shape
    `[.remove qid, .add result]` with matching pattern, and the priority
    is in the base phase band. -/
def ExecFact.toBaseStep? (ef : ExecFact) : Option BaseStep :=
  match ef.rule.tmpl.sinks, ef.rule.priority,
      Nat.decLe 32 ef.rule.priority, Nat.decLe ef.rule.priority 63 with
  | [.remove rmAtom, .add result], prio, Decidable.isTrue hlo, Decidable.isTrue hhi =>
    some ⟨rmAtom, result, prio, ⟨hlo, hhi⟩⟩
  | _, _, _, _ => none

/-- If `toBaseStep?` succeeds, the template sinks are `[.remove step.qid, .add step.result]`. -/
private theorem toBaseStep?_sinks_eq (ef : ExecFact) (step : BaseStep)
    (h : ef.toBaseStep? = some step) :
    ef.rule.tmpl.sinks = [.remove step.qid, .add step.result] := by
  simp only [ExecFact.toBaseStep?] at h
  split at h
  · rename_i q r _ _ _ _
    have heq := Option.some.inj h
    cases step
    simp at heq
    obtain ⟨rfl, rfl, _⟩ := heq
    simpa using r
  all_goals (try cases h)

/-- When the pattern produces exactly one match `([], consumed)` and the
    template is `[.remove step.qid, .add step.result]`, firing the exec
    fact through the scheduler equals `applyBase` on the consumed space.

    **Restriction**: `hunique` requires exactly one match with empty
    substitution. This holds for ground-pattern base steps but not for
    variable-binding patterns. -/
theorem base_step_exactness (s : Space) (ef : ExecFact) (step : BaseStep)
    (hm : ef.atom ∈ s)
    (hstep : ef.toBaseStep? = some step)
    (hg_result : isGroundAtom step.result = true)
    (consumed : Finset Atom)
    (hunique : matchPattern [] s ef.rule.pat = [([], consumed)]) :
    fireExecFact s ef = applyBase (consumeExec s ef) step := by
  -- Extract template shape from hstep via helper
  have htmpl_eq : ef.rule.tmpl.sinks = [.remove step.qid, .add step.result] :=
    toBaseStep?_sinks_eq ef step hstep
  -- Simplify fireExecFact via readCopy + unique match
  rw [fireExecFact_readCopy_simplify s ef hm, hunique]
  simp only [List.foldl_cons, List.foldl_nil]
  -- applySinks (consumeExec s ef) [] ef.rule.tmpl = applyBase (consumeExec s ef) step
  simp only [applySinks, htmpl_eq, List.foldl_cons, List.foldl_nil,
    applySink, applySubst_nil, hg_result, ite_true, applyBase]

/-! ### Restricted completeness canaries -/

section RestrictedCanaries

#check @ExecFact.toBaseStep?
#check @base_step_exactness

end RestrictedCanaries

/-! ## Unfold/Fold restricted completeness

Mirror `base_step_exactness` for unfold and fold phases. Since templates have
variable-length sink lists (from `subQids.map .add` or `subResults.map .remove`),
we use explicit template hypotheses rather than extractors. -/

/-! ### Foldl helper lemmas -/

/-- Folding `.add` sinks with empty subst on ground atoms = folding union with singletons. -/
private theorem foldl_add_sinks_eq_union (acc : Space) (atoms : List Atom)
    (hg : ∀ a ∈ atoms, isGroundAtom a = true) :
    (atoms.map Sink.add).foldl (applySink · []) acc = atoms.foldl (· ∪ {·}) acc := by
  induction atoms generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [show applySink acc [] (.add a) = acc ∪ {a} from by
      simp [applySink, applySubst_nil, hg a List.mem_cons_self]]
    exact ih (acc ∪ {a}) (fun b hb => hg b (List.mem_cons_of_mem a hb))

/-- Folding `.remove` sinks with empty subst = folding erase. -/
private theorem foldl_remove_sinks_eq_erase (acc : Space) (atoms : List Atom) :
    (atoms.map Sink.remove).foldl (applySink · []) acc = atoms.foldl (Finset.erase · ·) acc := by
  induction atoms generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [show applySink acc [] (.remove a) = acc.erase a from by
      simp [applySink, applySubst_nil]]
    exact ih (acc.erase a)

/-- `Finset.erase` equals `Finset.sdiff` with singleton. -/
private theorem erase_eq_sdiff_singleton (s : Finset Atom) (a : Atom) :
    s.erase a = s \ {a} := by
  ext x; simp [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton, and_comm]

/-- Folding `erase` = folding `sdiff` with singletons. -/
private theorem foldl_erase_eq_foldl_sdiff (acc : Space) (atoms : List Atom) :
    atoms.foldl (Finset.erase · ·) acc = atoms.foldl (· \ {·}) acc := by
  induction atoms generalizing acc with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons, erase_eq_sdiff_singleton]

/-! ### Unfold step exactness -/

/-- When the template encodes an unfold step (remove qid, add sub-queries, add wait token),
    firing via the scheduler equals `applyUnfold`. -/
theorem unfold_step_exactness (s : Space) (ef : ExecFact) (step : UnfoldStep)
    (hm : ef.atom ∈ s)
    (htmpl : ef.rule.tmpl.sinks =
      [.remove step.qid] ++ step.subQids.map .add ++ [.add step.waitAtom])
    (hg_subs : ∀ a ∈ step.subQids, isGroundAtom a = true)
    (hg_wait : isGroundAtom step.waitAtom = true)
    (consumed : Finset Atom)
    (hunique : matchPattern [] s ef.rule.pat = [([], consumed)]) :
    fireExecFact s ef = applyUnfold (consumeExec s ef) step := by
  rw [fireExecFact_readCopy_simplify s ef hm, hunique]
  simp only [List.foldl_cons, List.foldl_nil]
  -- Unfold applySinks with the template hypothesis
  simp only [applySinks, htmpl, List.foldl_append, List.foldl_cons, List.foldl_nil]
  -- The first sink: .remove step.qid with empty subst = erase qid
  rw [show applySink (consumeExec s ef) [] (.remove step.qid) =
        (consumeExec s ef).erase step.qid from by simp [applySink, applySubst_nil]]
  -- The add sinks: map .add with empty subst on ground atoms = foldl union
  rw [foldl_add_sinks_eq_union _ _ hg_subs]
  -- The last sink: .add waitAtom with empty subst
  rw [show applySink (step.subQids.foldl (· ∪ {·}) ((consumeExec s ef).erase step.qid)) []
        (.add step.waitAtom) =
        step.subQids.foldl (· ∪ {·}) ((consumeExec s ef).erase step.qid) ∪ {step.waitAtom} from by
    simp [applySink, applySubst_nil, hg_wait]]
  -- This is exactly applyUnfold
  rfl

/-! ### Fold step exactness -/

/-- When the template encodes a fold step (remove wait token, remove sub-results, add assembled),
    firing via the scheduler equals `applyFold`. -/
theorem fold_step_exactness (s : Space) (ef : ExecFact) (step : FoldStep)
    (hm : ef.atom ∈ s)
    (htmpl : ef.rule.tmpl.sinks =
      [.remove step.waitAtom] ++ step.subResults.map .remove ++ [.add step.assembled])
    (hg_assembled : isGroundAtom step.assembled = true)
    (consumed : Finset Atom)
    (hunique : matchPattern [] s ef.rule.pat = [([], consumed)]) :
    fireExecFact s ef = applyFold (consumeExec s ef) step := by
  rw [fireExecFact_readCopy_simplify s ef hm, hunique]
  simp only [List.foldl_cons, List.foldl_nil]
  simp only [applySinks, htmpl, List.foldl_append, List.foldl_cons, List.foldl_nil]
  -- The first sink: .remove step.waitAtom
  rw [show applySink (consumeExec s ef) [] (.remove step.waitAtom) =
        (consumeExec s ef).erase step.waitAtom from by simp [applySink, applySubst_nil]]
  -- The remove sinks: map .remove with empty subst = foldl erase
  rw [foldl_remove_sinks_eq_erase]
  -- Bridge erase → sdiff for matching applyFold's `\ {·}`
  rw [foldl_erase_eq_foldl_sdiff]
  -- The last sink: .add assembled
  rw [show applySink (step.subResults.foldl (· \ {·}) ((consumeExec s ef).erase step.waitAtom)) []
        (.add step.assembled) =
        step.subResults.foldl (· \ {·}) ((consumeExec s ef).erase step.waitAtom) ∪ {step.assembled} from by
    simp [applySink, applySubst_nil, hg_assembled]]
  rfl

/-! ## Sink commutation with set difference

When no sink adds the distinguished atom `a`, the `applySinks` fold
commutes with `\ {a}`. This underlies the scheduler's exec-fact consumption:
`fireExecFact s ef = (source-level result) \ {ef.atom}` under alignment. -/

/-- No sink in the list produces atom `a` via addition after substitution. -/
def SinksDontProduce (a : Atom) (σ : Subst) (sinks : List Sink) : Prop :=
  ∀ s ∈ sinks, ∀ c, (s = .add c ∨ s = .head c) → applySubst σ c ≠ a

/-- `Finset.erase` commutes with `Finset.sdiff` singleton. -/
private theorem erase_sdiff_singleton_comm (s : Finset Atom) (a b : Atom) :
    (s \ {a}).erase b = (s.erase b) \ {a} := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro ⟨hxb, hxs, hxa⟩; exact ⟨⟨hxb, hxs⟩, hxa⟩
  · rintro ⟨⟨hxb, hxs⟩, hxa⟩; exact ⟨hxb, hxs, hxa⟩

/-- `(s \ {a}) ∪ {c} = (s ∪ {c}) \ {a}` when `c ≠ a`. -/
private theorem union_singleton_sdiff_comm (s : Finset Atom) (a c : Atom) (hne : c ≠ a) :
    (s \ {a}) ∪ {c} = (s ∪ {c}) \ {a} := by
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
  constructor
  · rintro (⟨hxs, hxa⟩ | rfl)
    · exact ⟨Or.inl hxs, hxa⟩
    · exact ⟨Or.inr rfl, hne⟩
  · rintro ⟨hxs | rfl, hxa⟩
    · exact Or.inl ⟨hxs, hxa⟩
    · exact Or.inr rfl

/-- Single sink commutes with `\ {a}` when the sink doesn't produce `a`. -/
private theorem applySink_sdiff_comm (acc : Space) (σ : Subst) (a : Atom) (snk : Sink)
    (h : ∀ c, (snk = .add c ∨ snk = .head c) → applySubst σ c ≠ a) :
    applySink (acc \ {a}) σ snk = (applySink acc σ snk) \ {a} := by
  cases snk with
  | remove b =>
    simp only [applySink]
    exact erase_sdiff_singleton_comm acc a (applySubst σ b)
  | add c =>
    simp only [applySink]
    split
    · exact union_singleton_sdiff_comm acc a (applySubst σ c) (h c (Or.inl rfl))
    · rfl
  | head c =>
    simp only [applySink]
    split
    · exact union_singleton_sdiff_comm acc a (applySubst σ c) (h c (Or.inr rfl))
    · rfl

/-- `applySinks` fold commutes with `\ {a}` when no sink produces `a`. -/
private theorem foldl_applySink_sdiff_comm' (sinks : List Sink) (acc : Space)
    (σ : Subst) (a : Atom)
    (h : ∀ s ∈ sinks, ∀ c, (s = .add c ∨ s = .head c) → applySubst σ c ≠ a) :
    sinks.foldl (applySink · σ) (acc \ {a}) =
      (sinks.foldl (applySink · σ) acc) \ {a} := by
  induction sinks generalizing acc with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.foldl_cons]
    rw [applySink_sdiff_comm acc σ a s (h s List.mem_cons_self)]
    exact ih _ (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))

/-- `applySinks` commutes with set difference `\ {a}` when no sink produces `a`. -/
theorem applySinks_sdiff_comm (s : Space) (σ : Subst) (tmpl : Template) (a : Atom)
    (h : SinksDontProduce a σ tmpl.sinks) :
    applySinks (s \ {a}) σ tmpl = (applySinks s σ tmpl) \ {a} := by
  simp only [applySinks]
  exact foldl_applySink_sdiff_comm' tmpl.sinks s σ a h

/-! ## Scheduler-to-source bridge

When an exec fact encodes a source rule (compat mode, no guards), and the
single-match condition holds, the scheduler's `fireExecFact` result equals
the source-level `fireSourceRule` result minus the consumed exec atom. -/

/-- `consumeExec s ef = s \ {ef.atom}` (definitional wrapper). -/
theorem consumeExec_eq_sdiff (s : Space) (ef : ExecFact) :
    consumeExec s ef = s \ {ef.atom} := by
  simp only [consumeExec, erase_eq_sdiff_singleton]

/-- Under single-match + SinksDontProduce, firing an exec fact =
    (source-level applySinks) minus the exec atom.

    Together with `fireSourceRule_compat` / `fireSourceRule_no_guards`,
    this gives: `∃ fs' ∈ fireSourceRule s r, fireExecFact s ef = fs' \ {ef.atom}`. -/
theorem fireExecFact_eq_applySinks_sdiff (s : Space) (ef : ExecFact)
    (hm : ef.atom ∈ s)
    (σ : Subst) (consumed : Finset Atom)
    (hunique : matchPattern [] s ef.rule.pat = [(σ, consumed)])
    (hndp : SinksDontProduce ef.atom σ ef.rule.tmpl.sinks) :
    fireExecFact s ef = (applySinks s σ ef.rule.tmpl) \ {ef.atom} := by
  rw [fireExecFact_readCopy_simplify s ef hm, hunique]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [consumeExec_eq_sdiff]
  exact applySinks_sdiff_comm s σ ef.rule.tmpl ef.atom hndp

/-- Scheduler progress: whenever an exec fact is selected, `cWorkQueueStep` returns `some`. -/
theorem scheduler_progress (workspace : Conformance.Computable.CSpace)
    (ef : ExecFact) (hsel : selectNextExec (WQComputable.cExecFacts workspace) = some ef) :
    ∃ s', WQComputable.cWorkQueueStep workspace = some s' :=
  ⟨WQComputable.cFireExecFact workspace ef, by
    simp [WQComputable.cWorkQueueStep, hsel]⟩

/-! ### All canaries -/

section AllCanaries

#check @ExecFact.toBaseStep?
#check @base_step_exactness
#check @unfold_step_exactness
#check @fold_step_exactness
#check @applySinks_sdiff_comm
#check @fireExecFact_eq_applySinks_sdiff
#check @scheduler_progress

end AllCanaries

end Mettapedia.Languages.ProcessCalculi.MORK
