import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization.Atoms

/-!
# The static part of the congruence, at one frame: exactly the static equivalence of states

At the one-frame first-order instance (`Equivalence.AtOneFrame`: atoms as terms, identities `ℕ`,
may-barbs):

**The static equivalence** (`Static s t`): both knowledges are unsolvable, or some renaming of the
identities of `s` makes it equivalent to `t` modulo the knowledge with the same support (`Modulo` of
`renameState π s` and `t`). Unfolded, the second case says: the present rows correspond one to one;
the knowledges have the same solutions; each label equals the label of its image at every solution;
and the two states mention the same unknowns.

* **Sound for every program** (`congruent_of_static`): Laws 1 and 2, and all systems with unsolvable
  knowledge are congruent (`unsolvable_cong`).
* **Necessary, beside programs that leave a constant unused** (`static_of_congruent`): if
  `⟨P, s⟩` and `⟨P', t⟩` are congruent and `P`, `P'` are `Bounded` (their constants lie below a
  bound), then `Static s t`. The programs may be different, and may ask none queries and count queries.
  - *Solutions* (`models_of_congruent`): a solution of the one knowledge that fails an equation of the
    other is grounded and told; then the one side is solvable and the other not, and the rule that does
    nothing moves at the one side only.
  - *Rows* (`rows_of_congruent`): the knowledge has a principal solution (first-order unification); it
    is grounded generically (`generic_solution`: it equates two listed terms only when the knowledge
    does) and told. At such a pinned state the **probe** `probe k n z` (when exactly `n` rows equal
    `k`, make a row `z`, with `z` a constant no program or state uses) fires at the left; the answer at
    the right must show the barb `z` and not the barb `z'` of another unused constant, which no firing
    of the right's own program can do (`mayBarb_swap`, `result_avoids`), so the probe fires at the
    right: the rows equal to `k` are as many at both sides, for every `k`. Equal counts give a renaming
    (`exists_perm_of_map_eq`), and genericity turns equality at the grounded solution into equality at
    every solution.
  - *Support* (`mentions_of_congruent`): if the right mentions an unknown `w` that the left does not,
    the left opens the unknown of the rule that tells `x = 5` as `w`, which the right cannot; a context
    that then tells `w = 6` makes the left unsolvable and leaves the right solvable.
* **The characterization** (`congruent_iff_static`, and for the empty program `static_iff`):
  for a bounded program `P`, `⟨P, s⟩` and `⟨P, t⟩` are congruent exactly when `Static s t`.

A program that mentions every constant could answer the probe by itself; `Absorption` shows that the
bound is then needed, even for positive programs. The clauses are spelled out in `static_iff_clauses`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Mettapedia.Logic.LP
open RuleSyntax.Examples (Tm X E x c fresh_of_ground)
open RuleSyntax.Controls (atoms action)
open AtOneFrame (Sys Cong Moves pat idle information_of_empty fresh_identity tellX)

/-! ## The static equivalence -/

/-- **The static equivalence of states**: both knowledges unsolvable, or the identities of the one
renamed so that the two are equivalent modulo the knowledge, with the same support. -/
def Static (s t : State Tm ℕ) : Prop :=
  (¬ X.Solvable s.knowledge ∧ ¬ X.Solvable t.knowledge) ∨
    ∃ π : Equiv.Perm ℕ, Modulo X (renameState π s) t

/-- **A program leaves the constants from a bound on unused.** -/
def Bounded (P : Program Tm) : Prop :=
  ∃ B : ℕ, ∀ r ∈ P, ∀ t ∈ r.terms, ∀ k : ℕ, t = .const k → k < B

theorem bounded_empty : Bounded (∅ : Program Tm) :=
  ⟨0, fun r member => absurd member (Set.notMem_empty r)⟩

/-- **Statically equivalent states are congruent with every program.** -/
theorem congruent_of_static (P : Program Tm) {s t : State Tm ℕ} (static : Static s t) :
    Cong ⟨P, s⟩ ⟨P, t⟩ := by
  rcases static with ⟨unsolvableS, unsolvableT⟩ | ⟨π, modulo⟩
  · exact unsolvable_cong unsolvableS unsolvableT
  · exact (rename_congruent_mayBarb π P s).trans (modulo_congruent_mayBarb P modulo)

/-! ## Updating a solution at an unknown -/

theorem applyTerm_update_of_ne (σ : Subst atoms) {w : ℕ} (g : Term atoms) {t : Term atoms}
    (other : t ≠ .var w) : Subst.applyTerm (Function.update σ w g) t = Subst.applyTerm σ t := by
  cases t with
  | var v =>
      have different : v ≠ w := fun same => other (congrArg Term.var same)
      exact Function.update_of_ne different g σ
  | const _ => rfl
  | app fn _ => exact nomatch fn

/-- **An unknown a state does not mention is free in its knowledge.** -/
theorem models_update {s : State Tm ℕ} {w : ℕ} (unmentioned : ¬ s.Mentions (.var w))
    {σ : Subst atoms} (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) σ s.knowledge)
    (g : Term atoms) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) (Function.update σ w g) s.knowledge := by
  intro e member
  have left : e.1 ≠ .var w := by
    intro same
    apply unmentioned
    rw [← same]
    exact Or.inl (List.mem_map_of_mem member)
  have right : e.2 ≠ .var w := by
    intro same
    apply unmentioned
    rw [← same]
    exact Or.inr (Or.inl (List.mem_map_of_mem member))
  show Subst.applyTerm (Function.update σ w g) e.1 = Subst.applyTerm (Function.update σ w g) e.2
  rw [applyTerm_update_of_ne σ g left, applyTerm_update_of_ne σ g right]
  exact solved e member

/-! ## The solutions are observed -/

/-- **A solution of the left knowledge solves the right one**, beside any programs. -/
theorem models_of_congruent {P P' : Program Tm} {s t : State Tm ℕ} (related : Cong ⟨P, s⟩ ⟨P', t⟩)
    {σ : Subst atoms} (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) σ s.knowledge) :
    X.Models (a := PUnit.unit) (b := PUnit.unit) σ t.knowledge := by
  by_contra failing
  obtain ⟨e, member, unsolved⟩ : ∃ e ∈ t.knowledge,
      Subst.applyTerm σ e.1 ≠ Subst.applyTerm σ e.2 := by
    by_contra none
    exact failing fun e member =>
      Classical.byContradiction fun unsolved => none ⟨e, member, unsolved⟩
  -- Ground `σ` above its values at that equation.
  let M := sizeBound [Subst.applyTerm σ e.1, Subst.applyTerm σ e.2]
  let σ' : Subst atoms := Subst.comp (groundAt M) σ
  have constant : ∀ u, IsConst (Subst.applyTerm σ' u) := isConst_applyTerm_grounded M σ
  have separated : Subst.applyTerm σ' e.1 ≠ Subst.applyTerm σ' e.2 := by
    intro same
    have same' : Subst.applyTerm (groundAt M) (Subst.applyTerm σ e.1) =
        Subst.applyTerm (groundAt M) (Subst.applyTerm σ e.2) := by
      rw [← Subst.applyTerm_comp, ← Subst.applyTerm_comp]
      exact same
    exact unsolved (groundAt_injective (size_le_sizeBound (by simp)) (size_le_sizeBound (by simp))
      same')
  have solvedS : X.Models (a := PUnit.unit) (b := PUnit.unit) σ' s.knowledge :=
    Frames.models_comp solved (groundAt M)
  -- Tell every term of the right side its grounded value.
  let T := pin σ' (mentioned t)
  have left : X.Solvable (a := PUnit.unit) (tellState s T).knowledge :=
    ⟨PUnit.unit, σ', (Frames.models_append _ _ _).mpr
      ⟨solvedS, models_pin_self fun u _ => constant u⟩⟩
  have right : ¬ X.Solvable (a := PUnit.unit) (tellState t T).knowledge := by
    rintro ⟨b, τ, solvedT⟩
    obtain ⟨knownT, pinned⟩ := (Frames.models_append _ _ _).mp solvedT
    have agree := (models_pin_iff (fun u _ => constant u) τ).mp pinned
    have one := agree e.1 (mem_mentioned.mpr (Or.inl (List.mem_map_of_mem member)))
    have two := agree e.2 (mem_mentioned.mpr (Or.inr (Or.inl (List.mem_map_of_mem member))))
    have equated : Subst.applyTerm τ e.1 = Subst.applyTerm τ e.2 := knownT e member
    exact separated (one.symm.trans (equated.trans two))
  have told : Cong ⟨P ∪ {idle}, tellState s T⟩ ⟨P' ∪ {idle}, tellState t T⟩ :=
    (related.tell fun _ => T).addRules {idle}
  exact stuck_of_unsolvable (S := ⟨P' ∪ {idle}, tellState t T⟩) right
    (told.moves (idle_moves (Set.mem_union_right _ (Set.mem_singleton _)) _ left))

/-- **Congruent states have knowledges with the same solutions**, beside any programs. -/
theorem equivalent_of_congruent {P P' : Program Tm} {s t : State Tm ℕ}
    (related : Cong ⟨P, s⟩ ⟨P', t⟩) : X.Equivalent (a := PUnit.unit) s.knowledge t.knowledge :=
  fun _ _ => ⟨models_of_congruent related, models_of_congruent related.symm⟩

/-! ## A generic ground solution -/

/-- **A generic ground solution**: a solution of a solvable knowledge whose values are constants and
which equates two listed terms only when every solution does. -/
theorem generic_solution {K : EquationStore (Term atoms)}
    (solvable : X.Solvable (a := PUnit.unit) K) (L : List (Term atoms)) :
    ∃ σ₀ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) σ₀ K ∧
      (∀ u, IsConst (Subst.applyTerm σ₀ u)) ∧
      ∀ a ∈ L, ∀ b ∈ L, Subst.applyTerm σ₀ a = Subst.applyTerm σ₀ b →
        ∀ δ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) δ K →
          Subst.applyTerm δ a = Subst.applyTerm δ b := by
  have consistent : action.Consistent K := (Frames.ofSubstitution_solvable_iff action K).mp solvable
  obtain ⟨θ, accepted⟩ := (FirstOrder.accepted_iff_consistent K).mpr consistent
  have principal := FirstOrder.accepted_principal K θ accepted
  let N := sizeBound (L.map (Subst.applyTerm θ))
  refine ⟨Subst.comp (groundAt N) θ,
    Frames.models_comp (X := X) (b := PUnit.unit) principal.sound (groundAt N),
    isConst_applyTerm_grounded N θ, fun a inA b inB same δ solved => ?_⟩
  rw [Subst.applyTerm_comp, Subst.applyTerm_comp] at same
  have equal : Subst.applyTerm θ a = Subst.applyTerm θ b :=
    groundAt_injective (size_le_sizeBound (List.mem_map_of_mem inA))
      (size_le_sizeBound (List.mem_map_of_mem inB)) same
  obtain ⟨ρ, through⟩ := principal.factors δ solved
  have throughA : Subst.applyTerm δ a = Subst.applyTerm ρ (Subst.applyTerm θ a) := by
    have h : Subst.applyTerm δ a = Subst.applyTerm (Subst.comp ρ θ) a := through a
    rw [Subst.applyTerm_comp] at h
    exact h
  have throughB : Subst.applyTerm δ b = Subst.applyTerm ρ (Subst.applyTerm θ b) := by
    have h : Subst.applyTerm δ b = Subst.applyTerm (Subst.comp ρ θ) b := through b
    rw [Subst.applyTerm_comp] at h
    exact h
  rw [throughA, throughB, equal]

/-! ## Equal multisets of values give a renaming -/

/-- **Equal multisets of values give a renaming**: when two finite sets of identities carry the same
multiset of values, some permutation sends the one onto the other, value for value. -/
theorem exists_perm_of_map_eq {α : Type*} (f g : ℕ → α) :
    ∀ (A B : Finset ℕ), A.val.map f = B.val.map g →
      ∃ π : Equiv.Perm ℕ, A.map π.toEmbedding = B ∧ ∀ o ∈ A, g (π o) = f o := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
      intro B same
      have none : B.val.map g = 0 := by
        rw [← same]
        simp
      have empty : B = ∅ := by
        apply Finset.val_eq_zero.mp
        exact Multiset.map_eq_zero.mp none
      subst empty
      exact ⟨1, Finset.map_empty _, fun o inside => absurd inside (Finset.notMem_empty o)⟩
  | @insert a A' notMem ih =>
      intro B same
      rw [Finset.insert_val_of_notMem notMem, Multiset.map_cons] at same
      have inB : f a ∈ B.val.map g := by
        rw [← same]
        simp
      obtain ⟨b, member, valued⟩ := Multiset.mem_map.mp inB
      have memberB : b ∈ B := member
      have rest : A'.val.map f = (B.erase b).val.map g := by
        have split : B.val = b ::ₘ (B.erase b).val := by
          rw [Finset.erase_val, Multiset.cons_erase member]
        rw [split, Multiset.map_cons, valued] at same
        exact (Multiset.cons_inj_right _).mp same
      obtain ⟨π', image, labels⟩ := ih (B.erase b) rest
      have imageIn : ∀ o ∈ A', π' o ∈ B.erase b := fun o inside => by
        rw [← image]
        exact Finset.mem_map_of_mem _ inside
      refine ⟨Equiv.swap b (π' a) * π', ?_, ?_⟩
      · have fixes : ∀ o ∈ A', (Equiv.swap b (π' a) * π') o = π' o := by
          intro o inside
          rw [Equiv.Perm.mul_apply]
          apply Equiv.swap_apply_of_ne_of_ne
          · exact (Finset.mem_erase.mp (imageIn o inside)).1
          · intro sameImage
            exact notMem (π'.injective sameImage ▸ inside)
        have rest' : A'.map (Equiv.swap b (π' a) * π').toEmbedding = B.erase b := by
          rw [← image]
          ext o
          simp only [Finset.mem_map, Equiv.toEmbedding_apply]
          constructor
          · rintro ⟨o', inside, rfl⟩
            exact ⟨o', inside, (fixes o' inside).symm⟩
          · rintro ⟨o', inside, rfl⟩
            exact ⟨o', inside, fixes o' inside⟩
        rw [Finset.map_insert, rest', Equiv.toEmbedding_apply, Equiv.Perm.mul_apply,
          Equiv.swap_apply_right, Finset.insert_erase memberB]
      · intro o inside
        rcases Finset.mem_insert.mp inside with rfl | later
        · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
          exact valued
        · have fixed : (Equiv.swap b (π' a) * π') o = π' o := by
            rw [Equiv.Perm.mul_apply]
            apply Equiv.swap_apply_of_ne_of_ne
            · exact (Finset.mem_erase.mp (imageIn o later)).1
            · intro sameImage
              exact notMem (π'.injective sameImage ▸ later)
          rw [fixed]
          exact labels o later

/-! ## The probe -/

/-- **The probe**: when exactly `n` present rows equal `k`, make a row `z`. -/
def probe (k n z : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [.count (c k) n], [c z]⟩, []⟩

/-- How many present rows a substitution equates with the constant `k`. -/
noncomputable def countAt (σ : Subst atoms) (s : State Tm ℕ) (k : ℕ) : ℕ :=
  (matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ s.label s.present (c k)).card

/-- The rows a solution equates with a constant, at a state whose rows that solution pins. -/
theorem matchesAt_pinned {s : State Tm ℕ} {σ₀ τ : Subst atoms}
    (pinned : ∀ o ∈ s.present, Subst.applyTerm τ (s.label o) = Subst.applyTerm σ₀ (s.label o))
    (k : ℕ) :
    matchesAt X (a := PUnit.unit) (b := PUnit.unit) τ
      (fun o => Subst.applyTerm (Subst.id atoms) (s.label o)) s.present (c k) =
      matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ₀ s.label s.present (c k) := by
  ext o
  rw [mem_matchesAt, mem_matchesAt]
  constructor
  · rintro ⟨present, equated⟩
    refine ⟨present, ?_⟩
    have h : Subst.applyTerm τ (c k) =
        Subst.applyTerm τ (Subst.applyTerm (Subst.id atoms) (s.label o)) := equated
    rw [Subst.applyTerm_id, pinned o present] at h
    exact h
  · rintro ⟨present, equated⟩
    refine ⟨present, ?_⟩
    have h : Subst.applyTerm σ₀ (c k) = Subst.applyTerm σ₀ (s.label o) := equated
    show Subst.applyTerm τ (c k) = Subst.applyTerm τ (Subst.applyTerm (Subst.id atoms) (s.label o))
    rw [Subst.applyTerm_id, pinned o present]
    exact h

/-- **The probe fires** at a state whose rows a solution pins, with the count at that solution. -/
theorem probe_admitted {P : Program Tm} {k z : ℕ} {u : State Tm ℕ} {σ₀ : Subst atoms}
    (member : probe k (countAt σ₀ u k) z ∈ P) (solvable : X.Solvable (a := PUnit.unit) u.knowledge)
    (pinned : ∀ τ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) τ u.knowledge →
      ∀ o ∈ u.present, Subst.applyTerm τ (u.label o) = Subst.applyTerm σ₀ (u.label o))
    {m : ℕ} (fresh : m ∉ u.present) :
    (⟨probe k (countAt σ₀ u k) z, member, PUnit.unit, Subst.id atoms, ⟨[], [], [m]⟩, []⟩ :
      Firing ℕ E P u.frame).Admits X u := by
  let f : Firing ℕ E P u.frame :=
    ⟨probe k (countAt σ₀ u k) z, member, PUnit.unit, Subst.id atoms, ⟨[], [], [m]⟩, []⟩
  have info : f.information X u = X.applyStore (a := PUnit.unit) (b := PUnit.unit)
      (E.weaken f.ext) u.knowledge := information_of_empty f rfl rfl rfl
  have known : ∀ τ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) τ (f.information X u) →
      X.Models (a := PUnit.unit) (b := PUnit.unit) τ u.knowledge := by
    intro τ solved
    rw [info] at solved
    have composite := (Frames.models_applyStore (X := X) (E.weaken f.ext) τ u.knowledge).mp solved
    exact (Frames.models_congr (fun t => (Frames.act_comp_id (X := X) τ t).symm) u.knowledge).mp
      composite
  refine (admits_iff f).mpr ⟨?_, ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, ?_, fun q inside => absurd inside List.not_mem_nil⟩
  · apply fresh_of_ground action u f
    intro t inside τ
    simp [f, probe, Rule.terms, checkTerms] at inside
    rcases inside with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [f, Selection.commit]
    · simp [f, Selection.commit]
    · simp [f, Selection.commit]
    · simpa [f, Selection.commit] using fresh
    · intro q inside
      simp [f, Selection.commit] at inside
  · rw [info]
    obtain ⟨b, σ, solved⟩ := solvable
    refine ⟨b, σ, (Frames.models_applyStore _ _ _).mpr ?_⟩
    exact (Frames.models_congr (fun t => Frames.act_comp_id (X := X) σ t) u.knowledge).mp solved
  · intro check inside b τ solved
    have isCount : check = .count (c k) (countAt σ₀ u k) := List.mem_singleton.mp inside
    subst isCount
    show (matchesAt X τ (fun o => Subst.applyTerm (Subst.id atoms) (u.label o)) u.present
      (c k)).card = countAt σ₀ u k
    rw [matchesAt_pinned (pinned τ (known τ solved)) k]
    rfl

/-- **A firing of the probe admitted at a state counts its rows at every solution of its
knowledge.** -/
theorem count_of_probe {P : Program Tm} {k n z : ℕ} {v : State Tm ℕ}
    (h : Firing ℕ E P v.frame) (rule : h.rule = probe k n z) (admitted : h.Admits X v)
    {σ₀ : Subst atoms} (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) σ₀ v.knowledge) :
    countAt σ₀ v k = n := by
  obtain ⟨r, member, ext, ι, selection, seen⟩ := h
  simp only at rule
  subst rule
  obtain ⟨-, -, -, -, checks, -⟩ := (admits_iff _).mp admitted
  have info : (⟨probe k n z, member, ext, ι, selection, seen⟩ : Firing ℕ E P v.frame).information X v =
      X.applyStore (a := PUnit.unit) (b := PUnit.unit) (E.weaken ext) v.knowledge :=
    information_of_empty _ rfl rfl rfl
  have solvedInfo : X.Models (a := PUnit.unit) (b := PUnit.unit) σ₀
      ((⟨probe k n z, member, ext, ι, selection, seen⟩ : Firing ℕ E P v.frame).information X v) := by
    rw [info]
    refine (Frames.models_applyStore _ _ _).mpr ?_
    exact (Frames.models_congr (fun t => Frames.act_comp_id (X := X) σ₀ t) v.knowledge).mp solved
  have holds := checks (.count (c k) n) (List.mem_singleton_self _) PUnit.unit σ₀ solvedInfo
  have counted : (matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ₀
      (fun o => Subst.applyTerm (Subst.id atoms) (v.label o)) v.present (c k)).card = n := holds
  rw [matchesAt_pinned (σ₀ := σ₀) (fun _ _ => rfl) k] at counted
  exact counted

/-! ## The rows are observed -/

/-- The left result of the probe shows the barb of its row. -/
theorem probe_barb {P : Program Tm} {k z : ℕ} {u : State Tm ℕ} {σ₀ : Subst atoms}
    (member : probe k (countAt σ₀ u k) z ∈ P) {m : ℕ}
    (admitted : (⟨probe k (countAt σ₀ u k) z, member, PUnit.unit, Subst.id atoms, ⟨[], [], [m]⟩, []⟩ :
      Firing ℕ E P u.frame).Admits X u) :
    MayBarb X (pat (c z)) ((⟨probe k (countAt σ₀ u k) z, member, PUnit.unit, Subst.id atoms,
      ⟨[], [], [m]⟩, []⟩ : Firing ℕ E P u.frame).result X u) := by
  obtain ⟨b, σ, solved⟩ := admitted.2.2.1
  refine ⟨m, ?_, b, σ, Subst.id atoms, solved, ?_⟩
  · show m ∈ fire u.present ((⟨[], [], [m]⟩ : Selection ℕ).commit (T := Unit))
    rw [mem_fire]
    exact Or.inr (by simp [Selection.commit])
  · show Subst.applyTerm σ (relabel (fun o => Subst.applyTerm (Subst.id atoms) (u.label o)) [m]
      [Subst.applyTerm (Subst.id atoms) (c z)] m) = Subst.applyTerm (Subst.id atoms) (c z)
    simp [relabel, c]

/-- The left result of the probe shows no barb of a constant above every pinned value. -/
theorem probe_no_barb {P : Program Tm} {k z z' : ℕ} {u : State Tm ℕ} {σ₀ : Subst atoms}
    (member : probe k (countAt σ₀ u k) z ∈ P) {m : ℕ}
    (pinned : ∀ τ : Subst atoms, X.Models (a := PUnit.unit) (b := PUnit.unit) τ u.knowledge →
      ∀ o ∈ u.present, Subst.applyTerm τ (u.label o) = Subst.applyTerm σ₀ (u.label o))
    (below : ∀ o ∈ u.present, Subst.applyTerm σ₀ (u.label o) ≠ c z') (different : z ≠ z') :
    ¬ MayBarb X (pat (c z')) ((⟨probe k (countAt σ₀ u k) z, member, PUnit.unit, Subst.id atoms,
      ⟨[], [], [m]⟩, []⟩ : Firing ℕ E P u.frame).result X u) := by
  rintro ⟨o, present, b, τ, h, solved, equated⟩
  let f : Firing ℕ E P u.frame :=
    ⟨probe k (countAt σ₀ u k) z, member, PUnit.unit, Subst.id atoms, ⟨[], [], [m]⟩, []⟩
  have known : X.Models (a := PUnit.unit) (b := PUnit.unit) τ u.knowledge := by
    have info : f.information X u = X.applyStore (a := PUnit.unit) (b := PUnit.unit)
        (E.weaken f.ext) u.knowledge := information_of_empty f rfl rfl rfl
    have solved' : X.Models (a := PUnit.unit) (b := PUnit.unit) τ (f.information X u) := solved
    rw [info] at solved'
    have composite := (Frames.models_applyStore (X := X) (E.weaken f.ext) τ u.knowledge).mp solved'
    exact (Frames.models_congr (fun t => (Frames.act_comp_id (X := X) τ t).symm) u.knowledge).mp
      composite
  have value : Subst.applyTerm τ (relabel (fun o => Subst.applyTerm (Subst.id atoms) (u.label o)) [m]
      [Subst.applyTerm (Subst.id atoms) (c z)] o) = c z' := equated
  by_cases isM : o = m
  · subst isM
    simp [relabel, c] at value
    exact different value
  · have old : o ∈ u.present := by
      rcases mem_fire.mp present with ⟨old, -⟩ | made
      · exact old
      · exact absurd (by simpa [Selection.commit] using made) isM
    simp only [relabel, if_neg isM, Subst.applyTerm_id] at value
    exact below o old ((pinned τ known o old).symm.trans value)

#print axioms bounded_empty
#print axioms congruent_of_static
#print axioms applyTerm_update_of_ne
#print axioms models_update
#print axioms models_of_congruent
#print axioms equivalent_of_congruent
#print axioms generic_solution
#print axioms exists_perm_of_map_eq
#print axioms matchesAt_pinned
#print axioms probe_admitted
#print axioms count_of_probe
#print axioms probe_barb
#print axioms probe_no_barb

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Characterization
