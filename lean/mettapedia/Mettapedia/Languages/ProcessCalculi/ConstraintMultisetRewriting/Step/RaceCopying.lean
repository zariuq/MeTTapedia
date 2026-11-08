import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceExperiments

/-!
# What the experimenter cannot see without copying

The experimenter of `RaceExperiments` adds atoms at the ports and watches one run. Its readout is
sound for open bisimilarity, and it separates the race pair. It is strictly coarser than open
bisimilarity: some branching is visible only to an experimenter that copies a state and runs
several experiments from it (Abramsky 1987).

* **Covers** (`Cover`): a relation from configurations to nonempty lists of configurations that
  follows interventions, matches every firing by some member, and keeps a quiet member for every
  quiet configuration. A cover proves readout inclusion (`readout_subset_of_cover`): the experiment
  on the left is replayed on one member on the right, chosen after the whole experiment is known.
* **The copying pair** (`Copying`): `a.(b.c + b.d)` against `a.b.c + a.b.d`, with every firing taking
  a trigger of its action at the ports. In the first, `b` races between the two continuations; in the
  second, the race is at `a`.
  * **Equal readouts** (`readout_eq`): each is covered by the other (`cover₁₂`, `cover₂₁`).
  * **Not open bisimilar** (`not_openBisimilar`): after `a`, the first can, from one state, go on
    with `b` and then either `c` or `d`; the second has committed. Telling these apart takes two
    experiments from the state reached after `a`, that is, a copy of it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-! ## Covers -/

section Cover

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)
  (ports : O → Prop)

/-- **A cover**: each configuration on the left is related to a nonempty list on the right, the
relation follows interventions, every firing on the left is matched by a firing of some member,
and a quiet configuration keeps a quiet sublist. -/
structure Cover (ρ : Configuration T O → List (Configuration T O) → Prop) : Prop where
  nonempty : ∀ C 𝒟, ρ C 𝒟 → 𝒟 ≠ []
  add : ∀ C 𝒟 o, ports o → ρ C 𝒟 → ρ (addAtom C o) (𝒟.map fun D => addAtom D o)
  fired : ∀ C 𝒟 ℓ C', ρ C 𝒟 → Moves A label offers C ℓ C' →
    ∃ 𝒟', ρ C' 𝒟' ∧ ∀ D' ∈ 𝒟', ∃ D ∈ 𝒟, Moves A label offers D ℓ D'
  quiet : ∀ C 𝒟, ρ C 𝒟 → (∀ ℓ C', ¬ Moves A label offers C ℓ C') →
    ∃ 𝒟', ρ C 𝒟' ∧ ∀ D ∈ 𝒟', D ∈ 𝒟 ∧ ∀ ℓ D', ¬ Moves A label offers D ℓ D'

variable {A label offers ports}

/-- **A cover replays experiments**: every experiment on the left is an experiment of some member. -/
theorem Cover.experiment {ρ : Configuration T O → List (Configuration T O) → Prop}
    (cover : Cover A label offers ports ρ) :
    ∀ {C : Configuration T O} {e : List (Obs L O)}, Experiment A label offers ports C e →
      ∀ {𝒟 : List (Configuration T O)}, ρ C 𝒟 → ∃ D ∈ 𝒟, Experiment A label offers ports D e := by
  intro C e experiment
  induction experiment with
  | nil C =>
      intro 𝒟 related
      obtain ⟨D, member⟩ := List.exists_mem_of_ne_nil 𝒟 (cover.nonempty C 𝒟 related)
      exact ⟨D, member, .nil D⟩
  | add C o rest port _ ih =>
      intro 𝒟 related
      obtain ⟨D', member, experiment⟩ := ih (cover.add C 𝒟 o port related)
      obtain ⟨D, inD, rfl⟩ := List.mem_map.mp member
      exact ⟨D, inD, .add D o rest port experiment⟩
  | fired C C' ℓ rest moved _ ih =>
      intro 𝒟 related
      obtain ⟨𝒟', related', back⟩ := cover.fired C 𝒟 ℓ C' related moved
      obtain ⟨D', member, experiment⟩ := ih related'
      obtain ⟨D, inD, movedD⟩ := back D' member
      exact ⟨D, inD, .fired D D' ℓ rest movedD experiment⟩
  | quiet C rest still _ ih =>
      intro 𝒟 related
      obtain ⟨𝒟', related', inside⟩ := cover.quiet C 𝒟 related still
      obtain ⟨D, member, experiment⟩ := ih related'
      obtain ⟨inD, stillD⟩ := inside D member
      exact ⟨D, inD, .quiet D rest stillD experiment⟩

/-- **A cover by one configuration proves readout inclusion.** -/
theorem readout_subset_of_cover {ρ : Configuration T O → List (Configuration T O) → Prop}
    (cover : Cover A label offers ports ρ) {C D : Configuration T O} (related : ρ C [D]) :
    Readout A label offers ports C ⊆ Readout A label offers ports D := by
  intro e experiment
  obtain ⟨D', member, experiment'⟩ := cover.experiment experiment related
  rw [List.mem_singleton.mp member] at experiment'
  exact experiment'

end Cover

/-! ## The copying pair -/

namespace Copying

/-- Occurrence identities: two starts, the internal tokens, and one trigger per action. -/
inductive Site
  | s | s' | m | n₁ | n₂ | mc | md | ta | tb | tc | td
  deriving DecidableEq

/-- Action names. -/
inductive Act
  | a | b | c | d
  deriving DecidableEq

/-- The ports: the triggers. -/
def trigger (o : Site) : Prop := o = .ta ∨ o = .tb ∨ o = .tc ∨ o = .td

instance : DecidablePred trigger := fun o => by
  unfold trigger
  infer_instance

variable (τ : T)

/-- Every occurrence carries `τ`. -/
def label : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes `made`. -/
def firing (taken made : List Site) : Firing T S Site :=
  ⟨⟨taken.map (label τ), [], [], [], made.map (label τ)⟩, [], ⟨taken, [], made⟩⟩

/-- `a.(b.c + b.d)` from `s`, and `a.b.c + a.b.d` from `s'`; `c` and `d` are shared. -/
def alphabet : List (Act × Firing T S Site) :=
  [(.a, firing τ [.s, .ta] [.m]), (.b, firing τ [.m, .tb] [.mc]), (.b, firing τ [.m, .tb] [.md]),
    (.a, firing τ [.s', .ta] [.n₁]), (.a, firing τ [.s', .ta] [.n₂]),
    (.b, firing τ [.n₁, .tb] [.mc]), (.b, firing τ [.n₂, .tb] [.md]),
    (.c, firing τ [.mc, .tc] []), (.d, firing τ [.md, .td] [])]

def offers (ℓ : Act) (f : Firing T S Site) : Prop := (ℓ, f) ∈ alphabet (S := S) τ

/-- `a.(b.c + b.d)`, waiting for triggers. -/
def R₁ : Configuration T Site := ⟨[], {.s}⟩
/-- `a.b.c + a.b.d`, waiting for triggers. -/
def R₂ : Configuration T Site := ⟨[], {.s'}⟩

theorem ground : ∀ x ∈ alphabet (S := S) τ, Ground (label τ) x.2 := by
  intro x member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

/-- The internal occurrence a firing takes. -/
def internalOf (f : Firing T S Site) : Site := f.selection.taken.headD .s
/-- The trigger a firing takes. -/
def triggerOf (f : Firing T S Site) : Site := f.selection.taken.getD 1 .ta

theorem enabled_iff {i t x : Site} {made : List Site} {G : Finset Site} (hi : ¬ trigger i)
    (ht : trigger t) (hx : ¬ trigger x) (hG : ∀ y ∈ G, trigger y) (hm : ∀ y ∈ made, ¬ trigger y ∧ y ≠ i) :
    Enabled (label τ) (insert x G) ((firing (S := S) τ [i, t] made).selection.commit (T := T)) ↔
      i = x ∧ t ∈ G := by
  constructor
  · intro enabled
    have iIn := enabled.taken_subset (show i ∈ ([i, t] : List Site).toFinset by simp)
    have tIn := enabled.taken_subset (show t ∈ ([i, t] : List Site).toFinset by simp)
    rcases Finset.mem_insert.mp iIn with same | inG
    · rcases Finset.mem_insert.mp tIn with tx | tG
      · exact absurd (tx ▸ ht) hx
      · exact ⟨same, tG⟩
    · exact absurd (hG i inG) hi
  · rintro ⟨rfl, tG⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro y member
      simp only [Selection.commit, firing, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem tG
    · intro y member
      simp [Selection.commit, firing] at member
    · simp [Selection.commit, firing]
    · refine Finset.disjoint_left.mpr fun y member inside => ?_
      simp only [Selection.commit, firing, List.mem_toFinset] at member
      obtain ⟨notTrigger, notI⟩ := hm y member
      rcases Finset.mem_insert.mp inside with same | inG
      · exact notI same
      · exact notTrigger (hG y inG)
    · intro query member
      simp [Selection.commit] at member

theorem fire_eq {i t y : Site} {G : Finset Site} (hi : ¬ trigger i) (hG : ∀ z ∈ G, trigger z) :
    fire (insert i G) ((firing (S := S) τ [i, t] [y]).selection.commit (T := T)) = insert y (G.erase t) := by
  have iG : i ∉ G := fun h => hi (hG i h)
  ext z
  have hzi : z ∈ G → ¬ z = i := fun h e => iG (e ▸ h)
  simp only [MeTTaCalculus.OccurrenceCommits.mem_fire, Selection.commit, firing, Finset.mem_insert,
    Finset.mem_erase, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨inside, notTaken⟩ | made)
    · rcases inside with same | inG
      · exact absurd (.inl same) notTaken
      · exact .inr ⟨fun same => notTaken (.inr same), inG⟩
    · exact .inl made
  · rintro (made | ⟨notT, inG⟩)
    · exact .inr made
    · exact .inl ⟨.inr inG, fun taken => taken.elim (hzi inG) notT⟩

variable (A : SubstitutionAction T S)

/-- **Admission at an internal token beside triggers**: a member of the alphabet is admitted exactly
when it takes that token and its trigger is present. -/
theorem valid_iff_at {ℓ : Act} {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet τ)
    {C : Configuration T Site} (refl : Reflexive C.equations) {x : Site} {G : Finset Site}
    (hx : ¬ trigger x) (hG : ∀ y ∈ G, trigger y) (present : C.present = insert x G) :
    f.Valid A (label τ) C ↔ internalOf f = x ∧ triggerOf f ∈ G := by
  rw [(ground τ (ℓ, f) member).valid_iff A refl, present]
  simp only [alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact enabled_iff τ (of_decide_eq_true rfl) (of_decide_eq_true rfl) hx hG (of_decide_eq_true rfl)

theorem valid_of_same_present {ℓ : Act} {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet τ)
    {C D : Configuration T Site} (reflC : Reflexive C.equations) (reflD : Reflexive D.equations)
    (same : D.present = C.present) (valid : f.Valid A (label τ) C) : f.Valid A (label τ) D := by
  rw [(ground τ (ℓ, f) member).valid_iff A reflD, same]
  exact ((ground τ (ℓ, f) member).valid_iff A reflC).mp valid

theorem present_addAtom (C : Configuration T Site) (o : Site) : (addAtom C o).present = insert o C.present :=
  rfl

theorem insert_triggers {G : Finset Site} (hG : ∀ y ∈ G, trigger y) {o : Site} (port : trigger o) :
    ∀ y ∈ insert o G, trigger y := by
  intro y member
  rcases Finset.mem_insert.mp member with rfl | inG
  · exact port
  · exact hG y inG

theorem erase_triggers {G : Finset Site} (hG : ∀ y ∈ G, trigger y) (t : Site) :
    ∀ y ∈ G.erase t, trigger y := fun y member => hG y (Finset.mem_of_mem_erase member)

/-! ### The left readout is in the right one -/

/-- The cover of `a.(b.c + b.d)` by `a.b.c + a.b.d`. -/
def ρ₁₂ (C : Configuration T Site) (𝒟 : List (Configuration T Site)) : Prop :=
  Reflexive C.equations ∧ (∀ D ∈ 𝒟, Reflexive D.equations) ∧
    ((∃ G : Finset Site, (∀ y ∈ G, trigger y) ∧ C.present = insert .s G ∧
        ∃ D, 𝒟 = [D] ∧ D.present = insert .s' G) ∨
      (∃ G : Finset Site, (∀ y ∈ G, trigger y) ∧ C.present = insert .m G ∧
        ∃ D₁ D₂, 𝒟 = [D₁, D₂] ∧ D₁.present = insert .n₁ G ∧ D₂.present = insert .n₂ G) ∨
      (∃ D, 𝒟 = [D] ∧ D.present = C.present))

theorem moves_same {C D : Configuration T Site} (reflC : Reflexive C.equations)
    (reflD : Reflexive D.equations) (same : D.present = C.present) {ℓ : Act} {f : Firing T S Site}
    (member : offers τ ℓ f) (valid : f.Valid A (label τ) C) :
    Moves A (label τ) (offers τ) D ℓ (f.result (label τ) D) ∧
      (f.result (label τ) D).present = (f.result (label τ) C).present ∧
      Reflexive (f.result (label τ) D).equations ∧ Reflexive (f.result (label τ) C).equations := by
  refine ⟨⟨_, member, valid_of_same_present τ A member reflC reflD same valid, rfl⟩, ?_,
    (ground τ _ member).reflexive_result reflD, (ground τ _ member).reflexive_result reflC⟩
  show fire D.present _ = fire C.present _
  rw [same]

theorem quiet_same {C D : Configuration T Site} (reflC : Reflexive C.equations)
    (reflD : Reflexive D.equations) (same : D.present = C.present)
    (still : ∀ ℓ C', ¬ Moves A (label τ) (offers τ) C ℓ C') :
    ∀ ℓ D', ¬ Moves A (label τ) (offers τ) D ℓ D' := by
  rintro ℓ D' ⟨f, member, valid, _⟩
  exact still ℓ _ ⟨f, member, valid_of_same_present τ A member reflD reflC same.symm valid, rfl⟩

theorem cover₁₂ : Cover A (label τ) (offers τ) trigger (ρ₁₂ (T := T)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro C 𝒟 ⟨_, _, ⟨_, _, _, D, rfl, _⟩ | ⟨_, _, _, D₁, D₂, rfl, _⟩ | ⟨D, rfl, _⟩⟩ <;> simp
  · rintro C 𝒟 o port ⟨reflC, reflD, ⟨G, hG, present, D, rfl, presentD⟩ |
      ⟨G, hG, present, D₁, D₂, rfl, present₁, present₂⟩ | ⟨D, rfl, presentD⟩⟩
    · refine ⟨reflC, fun D' member => ?_, .inl ⟨insert o G, insert_triggers hG port, ?_, addAtom D o,
        rfl, ?_⟩⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
        rw [member]
        exact reflD D (List.mem_singleton_self _)
      · rw [present_addAtom, present, Finset.insert_comm]
      · rw [present_addAtom, presentD, Finset.insert_comm]
    · refine ⟨reflC, fun D' member => ?_, .inr (.inl ⟨insert o G, insert_triggers hG port, ?_,
        addAtom D₁ o, addAtom D₂ o, rfl, ?_, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact reflD D₁ (by simp)
        · exact reflD D₂ (by simp)
      · rw [present_addAtom, present, Finset.insert_comm]
      · rw [present_addAtom, present₁, Finset.insert_comm]
      · rw [present_addAtom, present₂, Finset.insert_comm]
    · refine ⟨reflC, fun D' member => ?_, .inr (.inr ⟨addAtom D o, rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
        rw [member]
        exact reflD D (List.mem_singleton_self _)
      · rw [present_addAtom, present_addAtom, presentD]
  · rintro C 𝒟 ℓ C' ⟨reflC, reflD, ⟨G, hG, present, D, rfl, presentD⟩ |
      ⟨G, hG, present, D₁, D₂, rfl, present₁, present₂⟩ | ⟨D, rfl, presentD⟩⟩ moved
    · obtain ⟨f, member, valid, rfl⟩ := moved
      have reflD' := reflD D (List.mem_singleton_self _)
      rw [valid_iff_at τ A member reflC (of_decide_eq_true rfl) hG present] at valid
      simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have ta : Site.ta ∈ G := valid.2
        have m₂ : ((Act.a, firing τ [.s', .ta] [.n₁]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        have m₃ : ((Act.a, firing τ [.s', .ta] [.n₂]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        refine ⟨[(firing (S := S) τ [.s', .ta] [.n₁]).result (label τ) D,
          (firing (S := S) τ [.s', .ta] [.n₂]).result (label τ) D], ⟨?_, ?_, .inr (.inl ⟨G.erase .ta,
            erase_triggers hG _, ?_, _, _, rfl, ?_, ?_⟩)⟩, ?_⟩
        · exact (ground τ (Act.a, firing (S := S) τ [.s, .ta] [.m]) (by simp [alphabet])).reflexive_result reflC
        · intro D' member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact (ground τ _ m₂).reflexive_result reflD'
          · exact (ground τ _ m₃).reflexive_result reflD'
        · show fire C.present _ = _
          rw [present]
          exact fire_eq τ (of_decide_eq_true rfl) hG
        · show fire D.present _ = _
          rw [presentD]
          exact fire_eq τ (of_decide_eq_true rfl) hG
        · show fire D.present _ = _
          rw [presentD]
          exact fire_eq τ (of_decide_eq_true rfl) hG
        · intro D' member
          refine ⟨D, List.mem_singleton_self _, ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl
          · exact ⟨_, m₂, (valid_iff_at τ A m₂ reflD' (of_decide_eq_true rfl) hG presentD).mpr
              ⟨rfl, ta⟩, rfl⟩
          · exact ⟨_, m₃, (valid_iff_at τ A m₃ reflD' (of_decide_eq_true rfl) hG presentD).mpr
              ⟨rfl, ta⟩, rfl⟩
      all_goals exact absurd valid.1 (of_decide_eq_false rfl)
    · obtain ⟨f, member, valid, rfl⟩ := moved
      have reflD₁ := reflD D₁ (by simp)
      have reflD₂ := reflD D₂ (by simp)
      rw [valid_iff_at τ A member reflC (of_decide_eq_true rfl) hG present] at valid
      simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd valid.1 (of_decide_eq_false rfl)
      · have tb : Site.tb ∈ G := valid.2
        have m₆ : ((Act.b, firing τ [.n₁, .tb] [.mc]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        refine ⟨[(firing (S := S) τ [.n₁, .tb] [.mc]).result (label τ) D₁], ⟨?_, ?_, .inr (.inr ⟨_, rfl, ?_⟩)⟩, ?_⟩
        · exact (ground τ (Act.b, firing (S := S) τ [.m, .tb] [.mc]) (by simp [alphabet])).reflexive_result reflC
        · intro D' member
          rw [List.mem_singleton.mp member]
          exact (ground τ _ m₆).reflexive_result reflD₁
        · show fire D₁.present _ = fire C.present _
          rw [present₁, present, fire_eq τ (of_decide_eq_true rfl) hG,
            fire_eq τ (of_decide_eq_true rfl) hG]
        · intro D' member
          refine ⟨D₁, by simp, ?_⟩
          rw [List.mem_singleton.mp member]
          exact ⟨_, m₆, (valid_iff_at τ A m₆ reflD₁ (of_decide_eq_true rfl) hG present₁).mpr ⟨rfl, tb⟩, rfl⟩
      · have tb : Site.tb ∈ G := valid.2
        have m₇ : ((Act.b, firing τ [.n₂, .tb] [.md]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        refine ⟨[(firing (S := S) τ [.n₂, .tb] [.md]).result (label τ) D₂], ⟨?_, ?_, .inr (.inr ⟨_, rfl, ?_⟩)⟩, ?_⟩
        · exact (ground τ (Act.b, firing (S := S) τ [.m, .tb] [.md]) (by simp [alphabet])).reflexive_result reflC
        · intro D' member
          rw [List.mem_singleton.mp member]
          exact (ground τ _ m₇).reflexive_result reflD₂
        · show fire D₂.present _ = fire C.present _
          rw [present₂, present, fire_eq τ (of_decide_eq_true rfl) hG,
            fire_eq τ (of_decide_eq_true rfl) hG]
        · intro D' member
          refine ⟨D₂, by simp, ?_⟩
          rw [List.mem_singleton.mp member]
          exact ⟨_, m₇, (valid_iff_at τ A m₇ reflD₂ (of_decide_eq_true rfl) hG present₂).mpr ⟨rfl, tb⟩, rfl⟩
      all_goals exact absurd valid.1 (of_decide_eq_false rfl)
    · have reflD' := reflD D (List.mem_singleton_self _)
      obtain ⟨f, member, valid, rfl⟩ := moved
      obtain ⟨movedD, same, reflResult, reflC'⟩ := moves_same τ A reflC reflD' presentD member valid
      exact ⟨[f.result (label τ) D], ⟨reflC', fun D'' member => by
          rw [List.mem_singleton.mp member]
          exact reflResult, .inr (.inr ⟨_, rfl, same⟩)⟩,
        fun D'' member => ⟨D, List.mem_singleton_self _, by rw [List.mem_singleton.mp member]; exact movedD⟩⟩
  · rintro C 𝒟 ⟨reflC, reflD, ⟨G, hG, present, D, rfl, presentD⟩ |
      ⟨G, hG, present, D₁, D₂, rfl, present₁, present₂⟩ | ⟨D, rfl, presentD⟩⟩ still
    · have noTa : Site.ta ∉ G := fun ta => by
        have m₁ : ((Act.a, firing τ [.s, .ta] [.m]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        exact still _ _ ⟨_, m₁, (valid_iff_at τ A m₁ reflC (of_decide_eq_true rfl) hG present).mpr
          ⟨rfl, ta⟩, rfl⟩
      refine ⟨[D], ⟨reflC, reflD, .inl ⟨G, hG, present, D, rfl, presentD⟩⟩, fun D' member => ?_⟩
      rw [List.mem_singleton.mp member]
      refine ⟨List.mem_singleton_self _, ?_⟩
      rintro ℓ D'' ⟨f, member', valid, _⟩
      rw [valid_iff_at τ A member' (reflD D (List.mem_singleton_self _)) (of_decide_eq_true rfl) hG
        presentD] at valid
      simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member'
      rcases member' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd valid.1 (of_decide_eq_false rfl)
      · exact absurd valid.1 (of_decide_eq_false rfl)
      · exact absurd valid.1 (of_decide_eq_false rfl)
      · exact noTa valid.2
      · exact noTa valid.2
      all_goals exact absurd valid.1 (of_decide_eq_false rfl)
    · have noTb : Site.tb ∉ G := fun tb => by
        have m₂ : ((Act.b, firing τ [.m, .tb] [.mc]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        exact still _ _ ⟨_, m₂, (valid_iff_at τ A m₂ reflC (of_decide_eq_true rfl) hG present).mpr
          ⟨rfl, tb⟩, rfl⟩
      refine ⟨[D₁, D₂], ⟨reflC, reflD, .inr (.inl ⟨G, hG, present, D₁, D₂, rfl, present₁, present₂⟩)⟩,
        fun D' member => ⟨member, ?_⟩⟩
      have reflD' := reflD D' member
      have presentD' : D'.present = insert .n₁ G ∨ D'.present = insert .n₂ G := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .inl present₁
        · exact .inr present₂
      rintro ℓ D'' ⟨f, member', valid, _⟩
      rcases presentD' with presentD' | presentD' <;>
        rw [valid_iff_at τ A member' reflD' (of_decide_eq_true rfl) hG presentD'] at valid <;>
        simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member' <;>
        rcases member' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        first
          | exact absurd valid.1 (of_decide_eq_false rfl)
          | exact noTb valid.2
    · refine ⟨[D], ⟨reflC, reflD, .inr (.inr ⟨D, rfl, presentD⟩)⟩, fun D' member => ?_⟩
      rw [List.mem_singleton.mp member]
      exact ⟨List.mem_singleton_self _, quiet_same τ A reflC (reflD D (List.mem_singleton_self _))
        presentD still⟩


/-! ### The right readout is in the left one -/

/-- The cover of `a.b.c + a.b.d` by `a.(b.c + b.d)`. -/
def ρ₂₁ (C : Configuration T Site) (𝒟 : List (Configuration T Site)) : Prop :=
  Reflexive C.equations ∧ (∀ D ∈ 𝒟, Reflexive D.equations) ∧
    ((∃ G : Finset Site, (∀ y ∈ G, trigger y) ∧ C.present = insert .s' G ∧
        ∃ D, 𝒟 = [D] ∧ D.present = insert .s G) ∨
      (∃ G : Finset Site, (∀ y ∈ G, trigger y) ∧
        (C.present = insert .n₁ G ∨ C.present = insert .n₂ G) ∧ ∃ D, 𝒟 = [D] ∧ D.present = insert .m G) ∨
      (∃ D, 𝒟 = [D] ∧ D.present = C.present))

theorem cover₂₁ : Cover A (label τ) (offers τ) trigger (ρ₂₁ (T := T)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro C 𝒟 ⟨_, _, ⟨_, _, _, D, rfl, _⟩ | ⟨_, _, _, D, rfl, _⟩ | ⟨D, rfl, _⟩⟩ <;> simp
  · rintro C 𝒟 o port ⟨reflC, reflD, ⟨G, hG, present, D, rfl, presentD⟩ |
      ⟨G, hG, present, D, rfl, presentD⟩ | ⟨D, rfl, presentD⟩⟩
    · refine ⟨reflC, fun D' member => ?_, .inl ⟨insert o G, insert_triggers hG port, ?_, addAtom D o,
        rfl, ?_⟩⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
        rw [member]
        exact reflD D (List.mem_singleton_self _)
      · rw [present_addAtom, present, Finset.insert_comm]
      · rw [present_addAtom, presentD, Finset.insert_comm]
    · refine ⟨reflC, fun D' member => ?_, .inr (.inl ⟨insert o G, insert_triggers hG port, ?_, addAtom D o,
        rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
        rw [member]
        exact reflD D (List.mem_singleton_self _)
      · rcases present with present | present
        · exact .inl (by rw [present_addAtom, present, Finset.insert_comm])
        · exact .inr (by rw [present_addAtom, present, Finset.insert_comm])
      · rw [present_addAtom, presentD, Finset.insert_comm]
    · refine ⟨reflC, fun D' member => ?_, .inr (.inr ⟨addAtom D o, rfl, ?_⟩)⟩
      · simp only [List.map_cons, List.map_nil, List.mem_singleton] at member
        rw [member]
        exact reflD D (List.mem_singleton_self _)
      · rw [present_addAtom, present_addAtom, presentD]
  · rintro C 𝒟 ℓ C' ⟨reflC, reflD, ⟨G, hG, present, D, rfl, presentD⟩ |
      ⟨G, hG, present, D, rfl, presentD⟩ | ⟨D, rfl, presentD⟩⟩ moved
    · obtain ⟨f, member, valid, rfl⟩ := moved
      have reflD' := reflD D (List.mem_singleton_self _)
      rw [valid_iff_at τ A member reflC (of_decide_eq_true rfl) hG present] at valid
      have m₁ : ((Act.a, firing (S := S) τ [.s, .ta] [.m]) : Act × Firing T S Site) ∈ alphabet τ := by
        simp [alphabet]
      have back : Site.ta ∈ G → ∀ D' ∈ [(firing (S := S) τ [.s, .ta] [.m]).result (label τ) D],
          ∃ D'' ∈ [D], Moves A (label τ) (offers τ) D'' Act.a D' := fun ta D' member' => by
        refine ⟨D, List.mem_singleton_self _, ?_⟩
        rw [List.mem_singleton.mp member']
        exact ⟨_, m₁, (valid_iff_at τ A m₁ reflD' (of_decide_eq_true rfl) hG presentD).mpr
          ⟨rfl, ta⟩, rfl⟩
      have presentM : ((firing (S := S) τ [.s, .ta] [.m]).result (label τ) D).present =
          insert .m (G.erase .ta) := by
        show fire D.present _ = _
        rw [presentD]
        exact fire_eq τ (of_decide_eq_true rfl) hG
      have reflM := (ground τ _ m₁).reflexive_result reflD'
      simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd valid.1 (of_decide_eq_false rfl)
      · exact absurd valid.1 (of_decide_eq_false rfl)
      · exact absurd valid.1 (of_decide_eq_false rfl)
      · refine ⟨_, ⟨(ground τ (Act.a, firing (S := S) τ [.s', .ta] [.n₁]) (by simp [alphabet])).reflexive_result
          reflC, fun D'' member' => by rw [List.mem_singleton.mp member']; exact reflM,
          .inr (.inl ⟨G.erase .ta, erase_triggers hG _, .inl ?_, _, rfl, presentM⟩)⟩, back valid.2⟩
        show fire C.present _ = _
        rw [present]
        exact fire_eq τ (of_decide_eq_true rfl) hG
      · refine ⟨_, ⟨(ground τ (Act.a, firing (S := S) τ [.s', .ta] [.n₂]) (by simp [alphabet])).reflexive_result
          reflC, fun D'' member' => by rw [List.mem_singleton.mp member']; exact reflM,
          .inr (.inl ⟨G.erase .ta, erase_triggers hG _, .inr ?_, _, rfl, presentM⟩)⟩, back valid.2⟩
        show fire C.present _ = _
        rw [present]
        exact fire_eq τ (of_decide_eq_true rfl) hG
      all_goals exact absurd valid.1 (of_decide_eq_false rfl)
    · obtain ⟨f, member, valid, rfl⟩ := moved
      have reflD' := reflD D (List.mem_singleton_self _)
      rcases present with present | present
      · rw [valid_iff_at τ A member reflC (of_decide_eq_true rfl) hG present] at valid
        have m₂ : ((Act.b, firing (S := S) τ [.m, .tb] [.mc]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · refine ⟨[(firing (S := S) τ [.m, .tb] [.mc]).result (label τ) D],
            ⟨(ground τ (Act.b, firing (S := S) τ [.n₁, .tb] [.mc]) (by simp [alphabet])).reflexive_result reflC,
              fun D'' member' => by
                rw [List.mem_singleton.mp member']
                exact (ground τ _ m₂).reflexive_result reflD',
              .inr (.inr ⟨_, rfl, ?_⟩)⟩, fun D'' member' => ⟨D, List.mem_singleton_self _, ?_⟩⟩
          · show fire D.present _ = fire C.present _
            rw [presentD, present, fire_eq τ (of_decide_eq_true rfl) hG, fire_eq τ (of_decide_eq_true rfl) hG]
          · rw [List.mem_singleton.mp member']
            exact ⟨_, m₂, (valid_iff_at τ A m₂ reflD' (of_decide_eq_true rfl) hG presentD).mpr
              ⟨rfl, valid.2⟩, rfl⟩
        all_goals exact absurd valid.1 (of_decide_eq_false rfl)
      · rw [valid_iff_at τ A member reflC (of_decide_eq_true rfl) hG present] at valid
        have m₃ : ((Act.b, firing (S := S) τ [.m, .tb] [.md]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
        rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · exact absurd valid.1 (of_decide_eq_false rfl)
        · refine ⟨[(firing (S := S) τ [.m, .tb] [.md]).result (label τ) D],
            ⟨(ground τ (Act.b, firing (S := S) τ [.n₂, .tb] [.md]) (by simp [alphabet])).reflexive_result reflC,
              fun D'' member' => by
                rw [List.mem_singleton.mp member']
                exact (ground τ _ m₃).reflexive_result reflD',
              .inr (.inr ⟨_, rfl, ?_⟩)⟩, fun D'' member' => ⟨D, List.mem_singleton_self _, ?_⟩⟩
          · show fire D.present _ = fire C.present _
            rw [presentD, present, fire_eq τ (of_decide_eq_true rfl) hG, fire_eq τ (of_decide_eq_true rfl) hG]
          · rw [List.mem_singleton.mp member']
            exact ⟨_, m₃, (valid_iff_at τ A m₃ reflD' (of_decide_eq_true rfl) hG presentD).mpr
              ⟨rfl, valid.2⟩, rfl⟩
        all_goals exact absurd valid.1 (of_decide_eq_false rfl)
    · have reflD' := reflD D (List.mem_singleton_self _)
      obtain ⟨f, member, valid, rfl⟩ := moved
      obtain ⟨movedD, same, reflResult, reflC'⟩ := moves_same τ A reflC reflD' presentD member valid
      exact ⟨[f.result (label τ) D], ⟨reflC', fun D'' member => by
          rw [List.mem_singleton.mp member]
          exact reflResult, .inr (.inr ⟨_, rfl, same⟩)⟩,
        fun D'' member => ⟨D, List.mem_singleton_self _, by rw [List.mem_singleton.mp member]; exact movedD⟩⟩
  · rintro C 𝒟 ⟨reflC, reflD, ⟨G, hG, present, D, rfl, presentD⟩ |
      ⟨G, hG, present, D, rfl, presentD⟩ | ⟨D, rfl, presentD⟩⟩ still
    · have noTa : Site.ta ∉ G := fun ta => by
        have m₄ : ((Act.a, firing (S := S) τ [.s', .ta] [.n₁]) : Act × Firing T S Site) ∈ alphabet τ := by
          simp [alphabet]
        exact still _ _ ⟨_, m₄, (valid_iff_at τ A m₄ reflC (of_decide_eq_true rfl) hG present).mpr
          ⟨rfl, ta⟩, rfl⟩
      refine ⟨[D], ⟨reflC, reflD, .inl ⟨G, hG, present, D, rfl, presentD⟩⟩, fun D' member => ?_⟩
      rw [List.mem_singleton.mp member]
      refine ⟨List.mem_singleton_self _, ?_⟩
      rintro ℓ D'' ⟨f, member', valid, _⟩
      rw [valid_iff_at τ A member' (reflD D (List.mem_singleton_self _)) (of_decide_eq_true rfl) hG
        presentD] at valid
      simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member'
      rcases member' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact noTa valid.2
      all_goals exact absurd valid.1 (of_decide_eq_false rfl)
    · have noTb : Site.tb ∉ G := fun tb => by
        rcases present with present | present
        · have m₆ : ((Act.b, firing (S := S) τ [.n₁, .tb] [.mc]) : Act × Firing T S Site) ∈ alphabet τ := by
            simp [alphabet]
          exact still _ _ ⟨_, m₆, (valid_iff_at τ A m₆ reflC (of_decide_eq_true rfl) hG present).mpr
            ⟨rfl, tb⟩, rfl⟩
        · have m₇ : ((Act.b, firing (S := S) τ [.n₂, .tb] [.md]) : Act × Firing T S Site) ∈ alphabet τ := by
            simp [alphabet]
          exact still _ _ ⟨_, m₇, (valid_iff_at τ A m₇ reflC (of_decide_eq_true rfl) hG present).mpr
            ⟨rfl, tb⟩, rfl⟩
      refine ⟨[D], ⟨reflC, reflD, .inr (.inl ⟨G, hG, present, D, rfl, presentD⟩)⟩, fun D' member => ?_⟩
      rw [List.mem_singleton.mp member]
      refine ⟨List.mem_singleton_self _, ?_⟩
      rintro ℓ D'' ⟨f, member', valid, _⟩
      rw [valid_iff_at τ A member' (reflD D (List.mem_singleton_self _)) (of_decide_eq_true rfl) hG
        presentD] at valid
      simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member'
      rcases member' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd valid.1 (of_decide_eq_false rfl)
      · exact noTb valid.2
      · exact noTb valid.2
      all_goals exact absurd valid.1 (of_decide_eq_false rfl)
    · refine ⟨[D], ⟨reflC, reflD, .inr (.inr ⟨D, rfl, presentD⟩)⟩, fun D' member => ?_⟩
      rw [List.mem_singleton.mp member]
      exact ⟨List.mem_singleton_self _, quiet_same τ A reflC (reflD D (List.mem_singleton_self _))
        presentD still⟩

theorem no_triggers : ∀ y ∈ (∅ : Finset Site), trigger y := fun y member =>
  absurd member (Finset.notMem_empty y)

/-- **The copying pair has equal readouts.** -/
theorem readout_eq :
    Readout A (label τ) (offers τ) trigger R₁ = Readout A (label τ) (offers τ) trigger R₂ := by
  apply Set.Subset.antisymm
  · exact readout_subset_of_cover (cover₁₂ τ A) ⟨reflexive_nil, fun D member => by
      rw [List.mem_singleton.mp member]
      exact reflexive_nil, .inl ⟨∅, no_triggers, of_decide_eq_true rfl, R₂, rfl, of_decide_eq_true rfl⟩⟩
  · exact readout_subset_of_cover (cover₂₁ τ A) ⟨reflexive_nil, fun D member => by
      rw [List.mem_singleton.mp member]
      exact reflexive_nil, .inl ⟨∅, no_triggers, of_decide_eq_true rfl, R₁, rfl, of_decide_eq_true rfl⟩⟩

/-- **The copying pair is not open bisimilar.** After `a`, the first is in one state from which `b`
may lead on to `c` or to `d`; when the second commits to `c`, the first answers with the state that
still races, takes the `b` that leads to `d`, and the second cannot follow with `d`. -/
theorem not_openBisimilar : ¬ OpenBisimilar A (label τ) (offers τ) trigger R₁ R₂ := by
  rintro ⟨R, bisimulation, related⟩
  have mα₁ : ((Act.a, firing (S := S) τ [.s, .ta] [.m]) : Act × Firing T S Site) ∈ alphabet τ := by
    simp [alphabet]
  have mα₂ : ((Act.a, firing (S := S) τ [.s', .ta] [.n₁]) : Act × Firing T S Site) ∈ alphabet τ := by
    simp [alphabet]
  have mβ₁' : ((Act.b, firing (S := S) τ [.m, .tb] [.md]) : Act × Firing T S Site) ∈ alphabet τ := by
    simp [alphabet]
  have mβ₂ : ((Act.b, firing (S := S) τ [.n₁, .tb] [.mc]) : Act × Firing T S Site) ∈ alphabet τ := by
    simp [alphabet]
  have mδ : ((Act.d, firing (S := S) τ [.md, .td] []) : Act × Firing T S Site) ∈ alphabet τ := by
    simp [alphabet]
  have onlyTa : ∀ y ∈ ({.ta} : Finset Site), trigger y := fun y member => by
    rw [Finset.mem_singleton.mp member]
    exact .inl rfl
  have reflM : Reflexive ((firing (S := S) τ [.s, .ta] [.m]).result (label τ) (addAtom R₁ .ta)).equations :=
    (ground τ _ mα₁).reflexive_result reflexive_nil
  have reflX : Reflexive ((firing (S := S) τ [.s', .ta] [.n₁]).result (label τ)
      (addAtom R₂ .ta)).equations :=
    (ground τ _ mα₂).reflexive_result reflexive_nil
  -- The experimenter adds the trigger of `a` on both sides.
  obtain ⟨Y, addedY, related₁⟩ := bisimulation.1 related (.inr .ta)
    (show OpenMoves A (label τ) (offers τ) trigger R₁ (.inr .ta) (addAtom R₁ .ta) from ⟨.inl rfl, rfl⟩)
  obtain ⟨_, rfl⟩ : trigger Site.ta ∧ Y = addAtom R₂ .ta := addedY
  -- The second fires the `a` that commits to `c`; the first must fire its only `a`.
  obtain ⟨M, movedM, related₂⟩ := bisimulation.2.1 related₁ (.inl .a)
    (show OpenMoves A (label τ) (offers τ) trigger (addAtom R₂ .ta) (.inl .a)
      ((firing (S := S) τ [.s', .ta] [.n₁]).result (label τ) (addAtom R₂ .ta)) from
      ⟨_, mα₂, (valid_iff_at τ A mα₂ reflexive_nil (x := .s') (G := {.ta}) (of_decide_eq_true rfl)
        onlyTa (of_decide_eq_true rfl)).mpr ⟨rfl, Finset.mem_singleton_self _⟩, rfl⟩)
  obtain ⟨f, member, valid, rfl⟩ := movedM
  rw [valid_iff_at τ A member reflexive_nil (x := .s) (G := {.ta}) (of_decide_eq_true rfl) onlyTa
    (of_decide_eq_true rfl)] at valid
  simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨-, rfl⟩
  rotate_left
  all_goals try exact absurd valid.1 (of_decide_eq_false rfl)
  -- The experimenter adds the trigger of `b` on both sides.
  obtain ⟨X, addedX, related₃⟩ := bisimulation.1 related₂ (.inr .tb)
    (show OpenMoves A (label τ) (offers τ) trigger _ (.inr .tb) _ from ⟨.inr (.inl rfl), rfl⟩)
  obtain ⟨_, rfl⟩ : trigger Site.tb ∧ X = addAtom ((firing (S := S) τ [.s', .ta] [.n₁]).result (label τ)
    (addAtom R₂ .ta)) .tb := addedX
  -- The first fires the `b` that leads to `d`; the second can only fire its `b` that leads to `c`.
  obtain ⟨X₂, movedX, related₄⟩ := bisimulation.1 related₃ (.inl .b)
    (show OpenMoves A (label τ) (offers τ) trigger _ (.inl .b) _ from
      ⟨_, mβ₁', (Ground.valid_iff A (ground τ _ mβ₁')
        (C := addAtom ((firing (S := S) τ [.s, .ta] [.m]).result (label τ) (addAtom R₁ .ta)) .tb)
        reflM).mpr (of_decide_eq_true rfl), rfl⟩)
  obtain ⟨g, member', valid', rfl⟩ := movedX
  rw [(ground τ _ member').valid_iff A
    (C := addAtom ((firing (S := S) τ [.s', .ta] [.n₁]).result (label τ) (addAtom R₂ .ta)) .tb) reflX]
    at valid'
  simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member'
  rcases member' with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨-, rfl⟩
  all_goals try exact absurd valid' (of_decide_eq_false rfl)
  -- The experimenter adds the trigger of `d`; the first fires `d`, the second cannot.
  obtain ⟨Z, addedZ, related₅⟩ := bisimulation.1 related₄ (.inr .td)
    (show OpenMoves A (label τ) (offers τ) trigger _ (.inr .td) _ from ⟨.inr (.inr (.inr rfl)), rfl⟩)
  obtain ⟨_, rfl⟩ := addedZ
  obtain ⟨W, movedW, _⟩ := bisimulation.1 related₅ (.inl .d)
    (show OpenMoves A (label τ) (offers τ) trigger _ (.inl .d) _ from
      ⟨_, mδ, (Ground.valid_iff A (ground τ _ mδ) (C := addAtom ((firing (S := S) τ [.m, .tb] [.md]).result
        (label τ) (addAtom ((firing (S := S) τ [.s, .ta] [.m]).result (label τ) (addAtom R₁ .ta)) .tb)) .td)
        ((ground τ _ mβ₁').reflexive_result
          (C := addAtom ((firing (S := S) τ [.s, .ta] [.m]).result (label τ) (addAtom R₁ .ta)) .tb) reflM)).mpr
        (of_decide_eq_true rfl), rfl⟩)
  obtain ⟨h, member'', valid'', _⟩ := movedW
  rw [(ground τ _ member'').valid_iff A (C := addAtom ((firing (S := S) τ [.n₁, .tb] [.mc]).result
    (label τ) (addAtom ((firing (S := S) τ [.s', .ta] [.n₁]).result (label τ) (addAtom R₂ .ta)) .tb)) .td)
    ((ground τ _ mβ₂).reflexive_result
      (C := addAtom ((firing (S := S) τ [.s', .ta] [.n₁]).result (label τ) (addAtom R₂ .ta)) .tb) reflX)]
    at valid''
  simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member''
  rcases member'' with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
    ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact absurd valid'' (of_decide_eq_false rfl)

/-- **The experimenter's readout is strictly coarser than open bisimilarity**: the copying pair has
equal readouts and is not open bisimilar. -/
theorem readout_strictly_coarser :
    Readout A (label τ) (offers τ) trigger R₁ = Readout A (label τ) (offers τ) trigger R₂ ∧
      ¬ OpenBisimilar A (label τ) (offers τ) trigger R₁ R₂ :=
  ⟨readout_eq τ A, not_openBisimilar τ A⟩

end Copying

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race in
#print axioms Cover.experiment
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race in
#print axioms readout_subset_of_cover
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race in
#print axioms Copying.readout_eq
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race in
#print axioms Copying.not_openBisimilar
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race in
#print axioms Copying.readout_strictly_coarser
