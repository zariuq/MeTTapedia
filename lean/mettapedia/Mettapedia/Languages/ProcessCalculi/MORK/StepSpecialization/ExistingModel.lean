import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorWrites

/-!
# The existing GSLT model of MM2 publishes the step's `every`, on supports

`cFireRuleScopedSourceExecFact` (`MM2RuleScopedExecution`) is the firing of the GSLT
programmable-space language of MM2 (`ProgrammableSpaceMM2`, the sink-major profile that `MM2Batch`
observes). It runs on duplicate-free lists of atoms identified by their compact keys. Read on
**supports**, the sets of keys of a space (`ProgrammableSpaceMM2RowMajorWrites.support`):

* `support_stage`: a sink's stage over the rows is the set of keys of its instances
  (`stagedKeys`), a union over the rows;
* `support_sinkBatch`: with add and remove sinks, the firing publishes the sinks in their
  written order, an add joining its staged keys and a removal subtracting them (`publishKeys`):
  the step's `every` published left to right;
* `sinkBatch_support_of_mem_iff`: so the firing cannot see the order or the repetitions of its
  rows, and a streaming implementation that stages rows as the query finds them publishes the
  same support;
* `support_fire`: the firing takes the exec out of the space it writes (`support_remove`) and
  matches the space with the exec put back (`support_readCopy`).

Example: over `(edge a b)` and `(edge b c)`, the sinks `(O (+ $x) (- $y))` stage the keys `{a, b}`
for the add and `{b, c}` for the removal, so the support left is `({a, b} ∪ S) \ {b, c}` whatever
the order of the two rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization.ExistingModel

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorWrites
  (support support_insert support_remove Allowed)

/-- **The keys of a sink's instances over the rows.** -/
def stagedKeys (input : InputSpec) (rows : List Subst) (sink : Sink) : Finset MorkSupportKey :=
  ((rows.filterMap fun σ => instantiateRuleTemplateAtom? input σ sink.atom).map
    morkSupportKey).toFinset

theorem mem_stagedKeys {input : InputSpec} {rows : List Subst} {sink : Sink}
    {key : MorkSupportKey} :
    key ∈ stagedKeys input rows sink ↔
      ∃ σ ∈ rows, ∃ a, instantiateRuleTemplateAtom? input σ sink.atom = some a ∧
        morkSupportKey a = key := by
  simp only [stagedKeys, List.mem_toFinset, List.mem_map, List.mem_filterMap]
  constructor
  · rintro ⟨a, ⟨σ, m, h⟩, rfl⟩
    exact ⟨σ, m, a, h, rfl⟩
  · rintro ⟨σ, m, a, h, rfl⟩
    exact ⟨a, ⟨σ, m, h⟩, rfl⟩

@[simp] theorem support_nil : support ([] : List Atom) = ∅ := rfl

theorem support_cons (a : Atom) (l : List Atom) :
    support (a :: l) = insert (morkSupportKey a) (support l) := by
  simp [support]

/-- Staging from a list already staged adds the keys of the rows' instances. -/
theorem support_stage_from (input : InputSpec) (sink : Sink) :
    ∀ (rows : List Subst) (acc : List Atom),
      support (rows.foldl (stageRuleScopedSink input sink) acc) =
        support acc ∪ stagedKeys input rows sink
  | [], acc => by
      ext key
      simp [mem_stagedKeys]
  | σ :: rows, acc => by
      rw [List.foldl_cons, support_stage_from input sink rows]
      ext key
      rw [Finset.mem_union, Finset.mem_union, mem_stagedKeys, mem_stagedKeys]
      unfold stageRuleScopedSink
      cases h : instantiateRuleTemplateAtom? input σ sink.atom with
      | none =>
          simp only
          constructor
          · rintro (k | ⟨τ, m, a, ha, rfl⟩)
            · exact Or.inl k
            · exact Or.inr ⟨τ, List.mem_cons_of_mem σ m, a, ha, rfl⟩
          · rintro (k | ⟨τ, m, a, ha, rfl⟩)
            · exact Or.inl k
            · rcases List.mem_cons.mp m with rfl | m
              · rw [h] at ha; cases ha
              · exact Or.inr ⟨τ, m, a, ha, rfl⟩
      | some b =>
          simp only
          rw [support_insert, Finset.mem_insert]
          constructor
          · rintro ((rfl | k) | ⟨τ, m, a, ha, rfl⟩)
            · exact Or.inr ⟨σ, List.mem_cons_self, b, h, rfl⟩
            · exact Or.inl k
            · exact Or.inr ⟨τ, List.mem_cons_of_mem σ m, a, ha, rfl⟩
          · rintro (k | ⟨τ, m, a, ha, rfl⟩)
            · exact Or.inl (Or.inr k)
            · rcases List.mem_cons.mp m with rfl | m
              · rw [h] at ha; cases ha; exact Or.inl (Or.inl rfl)
              · exact Or.inr ⟨τ, m, a, ha, rfl⟩

/-- **A sink's stage over the rows is the set of keys of its instances.** -/
theorem support_stage (input : InputSpec) (sink : Sink) (rows : List Subst) :
    support (rows.foldl (stageRuleScopedSink input sink) []) = stagedKeys input rows sink := by
  rw [support_stage_from, support_nil, Finset.empty_union]

theorem support_union (space : List Atom) :
    ∀ staged : List Atom, support (morkUnionSupport space staged) = support space ∪ support staged
  | [] => by simp [morkUnionSupport]
  | a :: rest => by
      have ih := support_union (morkInsertSupport space a) rest
      simp only [morkUnionSupport, List.foldl_cons] at ih ⊢
      rw [ih, support_insert, support_cons, Finset.insert_union, Finset.union_insert]

theorem support_subtract (space : List Atom) :
    ∀ staged : List Atom, support (morkSubtractSupport space staged) = support space \ support staged
  | [] => by simp [morkSubtractSupport]
  | a :: rest => by
      have ih := support_subtract (morkEraseSupport space a) rest
      simp only [morkSubtractSupport, List.foldl_cons] at ih ⊢
      rw [ih, support_remove, support_cons, Finset.sdiff_insert, Finset.erase_sdiff_comm]

/-- **Left-to-right publication on supports**: an add joins its staged keys, a removal subtracts
them, in the sinks' written order. -/
def publishKeys (input : InputSpec) (rows : List Subst) :
    List Sink → Finset MorkSupportKey → Finset MorkSupportKey
  | [], s => s
  | .add a :: rest, s => publishKeys input rows rest (s ∪ stagedKeys input rows (.add a))
  | .remove a :: rest, s => publishKeys input rows rest (s \ stagedKeys input rows (.remove a))
  | .head _ _ :: rest, s => publishKeys input rows rest s
  | .tail _ _ :: rest, s => publishKeys input rows rest s

/-- **The existing sink-major firing publishes the step's `every` left to right**, on supports,
for add and remove sinks. -/
theorem support_sinkBatch (input : InputSpec) (rows : List Subst) :
    ∀ (sinks : List Sink) (space : List Atom), (∀ k ∈ sinks, Allowed k) →
      support (cApplyRuleScopedSinkBatch input rows space sinks) =
        publishKeys input rows sinks (support space)
  | [], space, _ => rfl
  | sink :: rest, space, allowed => by
      have restAllowed : ∀ k ∈ rest, Allowed k := fun k m => allowed k (List.mem_cons_of_mem _ m)
      simp only [cApplyRuleScopedSinkBatch]
      rw [support_sinkBatch input rows rest _ restAllowed]
      cases sink with
      | add a =>
          simp only [finalizeRuleScopedSink, publishKeys]
          rw [support_union, support_stage]
      | remove a =>
          simp only [finalizeRuleScopedSink, publishKeys]
          rw [support_subtract, support_stage]
      | head n a => exact absurd (allowed _ List.mem_cons_self) (by simp [Allowed])
      | tail n a => exact absurd (allowed _ List.mem_cons_self) (by simp [Allowed])

theorem stagedKeys_of_mem_iff {input : InputSpec} {rows rows' : List Subst}
    (same : ∀ σ, σ ∈ rows ↔ σ ∈ rows') (sink : Sink) :
    stagedKeys input rows sink = stagedKeys input rows' sink := by
  ext key
  rw [mem_stagedKeys, mem_stagedKeys]
  exact ⟨fun ⟨σ, m, a, h, e⟩ => ⟨σ, (same σ).mp m, a, h, e⟩,
    fun ⟨σ, m, a, h, e⟩ => ⟨σ, (same σ).mpr m, a, h, e⟩⟩

theorem publishKeys_of_mem_iff {input : InputSpec} {rows rows' : List Subst}
    (same : ∀ σ, σ ∈ rows ↔ σ ∈ rows') :
    ∀ (sinks : List Sink) (s : Finset MorkSupportKey),
      publishKeys input rows sinks s = publishKeys input rows' sinks s
  | [], s => rfl
  | .add a :: rest, s => by
      simp only [publishKeys]
      rw [stagedKeys_of_mem_iff same, publishKeys_of_mem_iff same rest]
  | .remove a :: rest, s => by
      simp only [publishKeys]
      rw [stagedKeys_of_mem_iff same, publishKeys_of_mem_iff same rest]
  | .head _ _ :: rest, s => by simp only [publishKeys]; exact publishKeys_of_mem_iff same rest s
  | .tail _ _ :: rest, s => by simp only [publishKeys]; exact publishKeys_of_mem_iff same rest s

/-- **The existing firing cannot see the order or the repetitions of its rows.** -/
theorem sinkBatch_support_of_mem_iff {input : InputSpec} {rows rows' : List Subst}
    (same : ∀ σ, σ ∈ rows ↔ σ ∈ rows') {sinks : List Sink} (allowed : ∀ k ∈ sinks, Allowed k)
    (space : List Atom) :
    support (cApplyRuleScopedSinkBatch input rows space sinks) =
      support (cApplyRuleScopedSinkBatch input rows' space sinks) := by
  rw [support_sinkBatch input rows sinks space allowed, support_sinkBatch input rows' sinks space allowed,
    publishKeys_of_mem_iff same]

/-- The rows of a directive's firing: its matches over the read copy, through its guards. -/
def fireRows (space : List Atom) (directive : SourceExecFact) : List Subst :=
  ((cMatchInputSpecMork [] (morkInsertSupport (morkEraseSupport space directive.atom)
      directive.atom) directive.rule.input).filter fun (substitution, _) =>
        matchSourceGuards substitution directive.rule.guards).map Prod.fst

/-- **The existing firing, on supports**: the exec leaves the space written, and the sinks
publish the rows' staged keys left to right. -/
theorem support_fire (space : List Atom) (directive : SourceExecFact)
    (allowed : ∀ k ∈ directive.rule.tmpl.sinks, Allowed k) :
    support (cFireRuleScopedSourceExecFact space directive) =
      publishKeys directive.rule.input (fireRows space directive) directive.rule.tmpl.sinks
        ((support space).erase (morkSupportKey directive.atom)) := by
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  rw [support_sinkBatch _ _ _ _ allowed, support_remove]
  rfl

/-- **The read copy is the space with the exec**: on supports, matching sees the snapshot, the
exec included. -/
theorem support_readCopy (space : List Atom) (atom : Atom)
    (selected : morkSupportKey atom ∈ support space) :
    support (morkInsertSupport (morkEraseSupport space atom) atom) = support space := by
  rw [support_insert, support_remove, Finset.insert_erase selected]

end Mettapedia.Languages.ProcessCalculi.MORK.StepSpecialization.ExistingModel
