import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNeedSource

/-!
# Call by need: a thunk is evaluated at most once, and every later demand reads its value

The machine keeps one update marker per forced thunk, whose cell is busy while the thunk runs
(`Wf`). From this invariant:

- `value_persists`, `value_read_later`: a value written into a cell stays there for the rest of the
  run.
- `forced_stays`: a forced cell (busy or valued) is never a thunk again.
- `later_demand_reads`: **after a thunk is forced, every later demand of its location that takes a
  step reads the written value**; a demand while the thunk runs has no step (a black hole). So each
  thunk is evaluated at most once, and its value is shared by every later demand.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed

open ProgramRows

variable {prog : Program}

/-- The locations of the update markers on a stack. -/
def updates : List Frame → List ℕ
  | [] => []
  | .update ℓ :: K => ℓ :: updates K
  | .left _ :: K => updates K
  | .right _ :: K => updates K
  | .arg :: K => updates K

/-- **The machine's invariant**: the update markers are for distinct locations, each busy. -/
def Wf (c : Conf) : Prop := (updates c.2.1).Nodup ∧ ∀ ℓ ∈ updates c.2.1, c.2.2 ℓ = .busy

theorem wf_initial (e : NEx) (H : Heap) : Wf (.ev e, [], H) :=
  ⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil⟩

theorem wf_step {c c' : Conf} (step : NStep prog c c') (wf : Wf c) : Wf c' := by
  obtain ⟨nodup, busy⟩ := wf
  cases step with
  | val => exact ⟨nodup, busy⟩
  | pair => exact ⟨nodup, busy⟩
  | call => exact ⟨nodup, busy⟩
  | bind ℓ' a b K H fresh =>
      dsimp only at nodup busy ⊢
      refine ⟨nodup, fun ℓ member => ?_⟩
      have isBusy := busy ℓ member
      have ne : ℓ ≠ ℓ' := fun same => by rw [same, fresh] at isBusy; cases isBusy
      change H.set ℓ' (.thunk a) ℓ = .busy
      rw [Heap.set_other _ _ ne, isBusy]
  | read => exact ⟨nodup, busy⟩
  | force ℓ' K H e stored =>
      dsimp only [updates] at nodup busy ⊢
      have out : ℓ' ∉ updates K := fun member => by
        have isBusy := busy ℓ' member
        rw [stored] at isBusy
        cases isBusy
      refine ⟨List.nodup_cons.mpr ⟨out, nodup⟩, fun ℓ member => ?_⟩
      change H.set ℓ' .busy ℓ = .busy
      by_cases same : ℓ = ℓ'
      · rw [same, Heap.set_same]
      · rw [Heap.set_other _ _ same]
        rcases List.mem_cons.mp member with rfl | member
        · exact absurd rfl same
        · exact busy ℓ member
  | left => exact ⟨nodup, busy⟩
  | right => exact ⟨nodup, busy⟩
  | arg => exact ⟨nodup, busy⟩
  | update ℓ' v K H =>
      dsimp only [updates] at nodup busy ⊢
      obtain ⟨out, nodup'⟩ := List.nodup_cons.mp nodup
      refine ⟨nodup', fun ℓ member => ?_⟩
      have ne : ℓ ≠ ℓ' := fun same => out (same ▸ member)
      change H.set ℓ' (.value v) ℓ = .busy
      rw [Heap.set_other _ _ ne]
      exact busy ℓ (List.mem_cons_of_mem _ member)
  | apply => exact ⟨nodup, busy⟩

theorem wf_run {c c' : Conf} (run : Relation.ReflTransGen (NStep prog) c c') (wf : Wf c) : Wf c' := by
  induction run with
  | refl => exact wf
  | tail _ step ih => exact wf_step step ih

/-- **A written value stays.** -/
theorem value_persists {c c' : Conf} (step : NStep prog c c') (wf : Wf c) {ℓ : ℕ} {v : Sx}
    (stored : c.2.2 ℓ = .value v) : c'.2.2 ℓ = .value v := by
  cases step with
  | val => exact stored
  | pair => exact stored
  | call => exact stored
  | bind ℓ' a b K H fresh =>
      dsimp only at stored
      have ne : ℓ ≠ ℓ' := fun same => by rw [same, fresh] at stored; cases stored
      change H.set ℓ' (.thunk a) ℓ = _
      rw [Heap.set_other _ _ ne]
      exact stored
  | read => exact stored
  | force ℓ' K H e thunk =>
      dsimp only at stored
      have ne : ℓ ≠ ℓ' := fun same => by rw [same, thunk] at stored; cases stored
      change H.set ℓ' .busy ℓ = _
      rw [Heap.set_other _ _ ne]
      exact stored
  | left => exact stored
  | right => exact stored
  | arg => exact stored
  | update ℓ' w K H =>
      have isBusy := wf.2 ℓ' (List.mem_cons_self)
      have ne : ℓ ≠ ℓ' := fun same => by
        change H ℓ = _ at stored
        rw [same] at stored
        change H ℓ' = _ at isBusy
        rw [stored] at isBusy
        cases isBusy
      change H.set ℓ' (.value w) ℓ = _
      rw [Heap.set_other _ _ ne]
      exact stored
  | apply => exact stored

theorem value_read_later {c c' : Conf} (run : Relation.ReflTransGen (NStep prog) c c') (wf : Wf c) {ℓ : ℕ}
    {v : Sx} (stored : c.2.2 ℓ = .value v) : c'.2.2 ℓ = .value v := by
  induction run with
  | refl => exact stored
  | tail before step ih => exact value_persists step (wf_run before wf) ih

/-- A forced cell: busy or valued. -/
def Forced (H : Heap) (ℓ : ℕ) : Prop := H ℓ = .busy ∨ ∃ v, H ℓ = .value v

/-- **A forced cell stays forced**: it is never a thunk again. -/
theorem forced_stays {c c' : Conf} (step : NStep prog c c') {ℓ : ℕ} (forced : Forced c.2.2 ℓ) :
    Forced c'.2.2 ℓ := by
  have notThunk : ∀ e, c.2.2 ℓ ≠ .thunk e := by
    intro e same
    rcases forced with busy | ⟨v, value⟩
    · rw [busy] at same; cases same
    · rw [value] at same; cases same
  have notEmpty : c.2.2 ℓ ≠ .empty := by
    intro same
    rcases forced with busy | ⟨v, value⟩
    · rw [busy] at same; cases same
    · rw [value] at same; cases same
  cases step with
  | val => exact forced
  | pair => exact forced
  | call => exact forced
  | bind ℓ' a b K H fresh =>
      dsimp only at forced notEmpty
      have ne : ℓ ≠ ℓ' := fun same => notEmpty (by rw [same]; exact fresh)
      change Forced (H.set ℓ' (.thunk a)) ℓ
      unfold Forced
      rw [Heap.set_other _ _ ne]
      exact forced
  | read => exact forced
  | force ℓ' K H e thunk =>
      dsimp only at forced
      change Forced (H.set ℓ' .busy) ℓ
      unfold Forced
      by_cases same : ℓ = ℓ'
      · rw [same, Heap.set_same]
        exact .inl rfl
      · rw [Heap.set_other _ _ same]
        exact forced
  | left => exact forced
  | right => exact forced
  | arg => exact forced
  | update ℓ' w K H =>
      dsimp only at forced
      change Forced (H.set ℓ' (.value w)) ℓ
      unfold Forced
      by_cases same : ℓ = ℓ'
      · rw [same, Heap.set_same]
        exact .inr ⟨w, rfl⟩
      · rw [Heap.set_other _ _ same]
        exact forced
  | apply => exact forced

theorem forced_run {c c' : Conf} (run : Relation.ReflTransGen (NStep prog) c c') {ℓ : ℕ}
    (forced : Forced c.2.2 ℓ) : Forced c'.2.2 ℓ := by
  induction run with
  | refl => exact forced
  | tail _ step ih => exact forced_stays step ih

/-- **The demand of a written value reads it.** -/
theorem demand_reads {ℓ : ℕ} {K : List Frame} {H : Heap} {v : Sx} (stored : H ℓ = .value v) {c : Conf}
    (step : NStep prog (.ev (.loc ℓ), K, H) c) : c = (.ret v, K, H) := by
  cases step with
  | read _ _ _ w read =>
      rw [stored] at read
      cases read
      rfl
  | force _ _ _ e thunk =>
      rw [stored] at thunk
      cases thunk

/-- A demand while the thunk runs has no step: a black hole. -/
theorem busy_blocks {ℓ : ℕ} {K : List Frame} {H : Heap} (busy : H ℓ = .busy) {c : Conf} :
    ¬ NStep prog (.ev (.loc ℓ), K, H) c := by
  intro step
  cases step with
  | read _ _ _ w read =>
      rw [busy] at read
      cases read
  | force _ _ _ e thunk =>
      rw [busy] at thunk
      cases thunk

/-- **A thunk is evaluated at most once, and its value is read by every later demand.** After the
demand that forces the thunk at `ℓ`, every later demand of `ℓ` that takes a step reads the value
written into the cell. -/
theorem later_demand_reads {ℓ : ℕ} {K K' : List Frame} {H H' : Heap} {e : NEx} {c₁ c₂ : Conf}
    (thunk : H ℓ = .thunk e) (forcing : NStep prog (.ev (.loc ℓ), K, H) c₁)
    (after : Relation.ReflTransGen (NStep prog) c₁ (.ev (.loc ℓ), K', H'))
    (demand : NStep prog (.ev (.loc ℓ), K', H') c₂) : ∃ v, H' ℓ = .value v ∧ c₂ = (.ret v, K', H') := by
  have forced₁ : Forced c₁.2.2 ℓ := by
    cases forcing with
    | read _ _ _ w read =>
        rw [thunk] at read
        cases read
    | force _ _ _ e' stored =>
        exact .inl (Heap.set_same _ _ _)
  rcases forced_run after forced₁ with busy | ⟨v, value⟩
  · exact (busy_blocks busy demand).elim
  · exact ⟨v, value, demand_reads value demand⟩

#print axioms wf_step
#print axioms wf_run
#print axioms value_persists
#print axioms value_read_later
#print axioms forced_stays
#print axioms demand_reads
#print axioms busy_blocks
#print axioms later_demand_reads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed
