import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchPolicy
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Independence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects

/-!
# Bounded search over the candidate step, and the three outcomes of a check

## Runs of the step are a search space (`Alternatives.space`)

Given finitely many admitted firings at each state (`Alternatives`), the step is a search space: a
state unfolds into the results of those firings, and a halted state (no admitted firing) is an
answer: a complete run ends there. An **enumeration** lists every admitted firing, each once
(`Enumeration`; it exists wherever firings are finitely many and admission is decided,
`Enumeration.ofFintype`). Where firings are infinitely many but finitely many up to alikeness, the
search explores representatives instead (`SearchClasses`).

* Positions of states are runs: an address is the list of indices of a run's firings among the
  alternatives (`Alternatives.Path`); it determines the run, and for an enumeration it is
  determined by it (`Path.unique_run`, `Path.unique_address`, `exists_path`, `item_state_iff`).
* Positions of answers are complete runs (`item_answer_iff`). Hence **a budgeted run of the step is
  a search**: budget `n` reports exactly the complete runs shorter than `n`, by their final states
  (`mem_run_space`); it is finished exactly when every run is shorter than `n` (`status_run_space`);
  and the multiplicity of a final state is the number of complete runs ending there
  (`multiplicity_space`). Collecting a finished budget gives the final states of all complete runs
  with those multiplicities (`collect_space`); collecting a cut-off budget gives nothing.

## The three outcomes (`Certifies`)

A search whose answers certify a proposition, and which has an answer whenever the proposition
holds, gives a three-way readout at every budget: **commit** (a certificate: the proposition holds),
**refuted** (finished with no answers: it fails), **suspended** (cut off with no answers: nothing
is known). Suspended occurs only when cut off, never at a budget where the search finished
(`Certifies.commit`, `Certifies.refuted`, `Certifies.suspended_of`), and definite readouts are
stable as the budget grows.

* **The check of independence** (`checkOfSearch`): a certificate search for `Transport.Independent`
  gives a sound three-valued `Transport.Check` at every budget, answering unknown exactly when the
  search is suspended (`checkOfSearch_unknown_iff`); its definite verdicts persist at larger budgets
  (`checkOfSearch_mono`).
* **Staged effects** (`staged_commit`, `staged_refuted`): a commit publishes the source result and a
  refutation leaves the configuration with a proof of nonadmission, both as `SourceResult` states.
  A suspended search proves nothing: at budget zero every search is suspended, and for an
  executable block with a visible effect, reading suspension as refusal contradicts the source
  contract (`staged_suspended_not_refusal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search

open Interface

universe uO uT uH uOcc uS uF uI u v

section StepSearch

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- **Alternatives of a search over runs**: finitely many admitted firings at each state. -/
structure Alternatives where
  next : (s : State) → List {f : Firing s // P.Admits f}

/-- **A finite enumeration of the admitted firings** at each state, each once. -/
structure Enumeration extends Alternatives P where
  complete : ∀ (s : State) (f : Firing s) (admitted : P.Admits f), ⟨f, admitted⟩ ∈ next s
  nodup : ∀ s : State, (next s).Nodup

/-- Where firings are finitely many and admission is decided, an enumeration exists. -/
noncomputable def Enumeration.ofFintype [∀ s, Fintype (Firing s)]
    [∀ (s : State) (f : Firing s), Decidable (P.Admits f)] : Enumeration P where
  next s := (Finset.univ : Finset {f : Firing s // P.Admits f}).toList
  complete _ _ _ := Finset.mem_toList.mpr (Finset.mem_univ _)
  nodup _ := Finset.nodup_toList _

/-- A state with no admitted firing: a run ending there is complete. -/
def Halted (s : State) : Prop := ∀ f : Firing s, ¬ P.Admits f

variable {P}

namespace Enumeration

variable (E : Enumeration P)

theorem halted_iff (s : State) : Halted P s ↔ E.next s = [] := by
  constructor
  · intro halted
    cases h : E.next s with
    | nil => rfl
    | cons g gs => exact absurd g.2 (halted g.1)
  · intro empty f admitted
    have := E.complete s f admitted
    rw [empty] at this
    exact List.not_mem_nil this

end Enumeration

namespace Alternatives

variable (A : Alternatives P)

/-- **The run space of the step**: a state unfolds into the results of its admitted firings; a
halted state is an answer. -/
def space : Space State State where
  unfold s := match A.next s with
    | [] => [.inl s]
    | g :: gs => (g :: gs).map fun g => .inr (P.result g.1 g.2)

theorem space_unfold_of_halted {s : State} (h : A.next s = []) : A.space.unfold s = [.inl s] := by
  simp [space, h]

theorem space_unfold_of_ne {s : State} (h : A.next s ≠ []) :
    A.space.unfold s = (A.next s).map fun g => .inr (P.result g.1 g.2) := by
  obtain ⟨g, gs, same⟩ := List.exists_cons_of_ne_nil h
  simp [space, same]

/-- **The address of a run**: the index of each of its firings among the alternatives. -/
inductive Path : {s : State} → P.Run s → List ℕ → Prop
  | nil (s : State) : Path (.nil s) []
  | cons {s : State} {i : ℕ} {f : Firing s} {admitted : P.Admits f}
      {rest : P.Run (P.result f admitted)} {w : List ℕ}
      (get : (A.next s)[i]? = some ⟨f, admitted⟩) (tail : Path rest w) :
      Path (.cons f admitted rest) (i :: w)

variable {A}

theorem Path.length_eq : ∀ {s : State} {r : P.Run s} {w : List ℕ}, A.Path r w → w.length = r.word.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ tail => by simp [Interface.Step.Run.word, tail.length_eq]

/-- **An address determines its run.** -/
theorem Path.unique_run : ∀ {s : State} {r r' : P.Run s} {w : List ℕ}, A.Path r w → A.Path r' w → r = r'
  | _, _, _, _, .nil _, .nil _ => rfl
  | _, _, _, _, .cons get tail, .cons get' tail' => by
      have same := get.symm.trans get'
      simp only [Option.some.injEq, Subtype.mk.injEq] at same
      subst same
      rw [tail.unique_run tail']

/-- **A run determines its address.** -/
theorem Path.unique_address (nodup : ∀ s : State, (A.next s).Nodup) :
    ∀ {s : State} {r : P.Run s} {w w' : List ℕ},
    A.Path r w → A.Path r w' → w = w'
  | _, _, _, _, .nil _, .nil _ => rfl
  | _, _, _, _, .cons (i := i) get tail, .cons (i := i') get' tail' => by
      have bound : i < (A.next _).length := (List.getElem?_eq_some_iff.mp get).1
      have index : i = i' := ((List.getElem?_inj bound (nodup _)).mp (get.trans get'.symm))
      rw [index, tail.unique_address nodup tail']

variable (A)

/-- **Positions of states are runs.** -/
theorem item_state_iff : ∀ (s : State) (w : List ℕ) (t : State),
    A.space.item (.inr s) w = some (.inr t) ↔ ∃ r : P.Run s, A.Path r w ∧ r.last = t
  | s, [], t => by
      simp only [Space.item_nil, Option.some.injEq, Sum.inr.injEq]
      constructor
      · rintro rfl
        exact ⟨.nil s, .nil s, rfl⟩
      · rintro ⟨r, path, rfl⟩
        cases path
        rfl
  | s, i :: w, t => by
      rw [Space.item_inr_cons]
      by_cases halted : A.next s = []
      · rw [A.space_unfold_of_halted halted]
        constructor
        · intro h
          cases i with
          | zero => cases w <;> simp at h
          | succ j => simp at h
        · rintro ⟨r, path, _⟩
          cases path with
          | cons get tail =>
              rw [halted] at get
              simp at get
      · rw [A.space_unfold_of_ne halted, List.getElem?_map, Option.bind_map]
        simp only [Option.bind_eq_some_iff, Function.comp_apply]
        constructor
        · rintro ⟨g, get, h⟩
          obtain ⟨r, path, last⟩ := (item_state_iff _ w t).mp h
          exact ⟨.cons g.1 g.2 r, .cons get path, last⟩
        · rintro ⟨r, path, rfl⟩
          cases path with
          | cons get tail => exact ⟨_, get, (item_state_iff _ w _).mpr ⟨_, tail, rfl⟩⟩

/-- **Positions of answers are complete runs.** -/
theorem item_answer_iff : ∀ (s : State) (w : List ℕ) (t : State),
    A.space.item (.inr s) w = some (.inl t) ↔
      ∃ (r : P.Run s) (w' : List ℕ), A.Path r w' ∧ w = w' ++ [0] ∧ r.last = t ∧ A.next t = []
  | s, [], t => by
      simp only [Space.item_nil, Option.some.injEq, reduceCtorEq, false_iff, not_exists, not_and]
      intro r w' _ empty
      have := congrArg List.length empty
      simp at this
  | s, i :: w, t => by
      rw [Space.item_inr_cons]
      by_cases halted : A.next s = []
      · rw [A.space_unfold_of_halted halted]
        constructor
        · intro h
          cases i with
          | zero =>
              cases w with
              | nil =>
                  simp only [List.length_cons, List.length_nil, Nat.lt_add_one, getElem?_pos,
                    List.getElem_cons_zero, Option.bind_some, Space.item_nil, Option.some.injEq,
                    Sum.inl.injEq] at h
                  subst h
                  exact ⟨.nil s, [], .nil s, rfl, rfl, halted⟩
              | cons j w => simp at h
          | succ j => simp at h
        · rintro ⟨r, w', path, address, rfl, _⟩
          cases path with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at address
              obtain ⟨rfl, rfl⟩ := address
              exact rfl
          | cons get tail =>
              rw [halted] at get
              simp at get
      · rw [A.space_unfold_of_ne halted, List.getElem?_map, Option.bind_map]
        simp only [Option.bind_eq_some_iff, Function.comp_apply]
        constructor
        · rintro ⟨g, get, h⟩
          obtain ⟨r, w', path, rfl, last, empty⟩ := (item_answer_iff _ w t).mp h
          exact ⟨.cons g.1 g.2 r, i :: w', .cons get path, rfl, last, empty⟩
        · rintro ⟨r, w', path, address, rfl, empty⟩
          cases path with
          | nil =>
              exact absurd empty halted
          | cons get tail =>
              simp only [List.cons_append, List.cons.injEq] at address
              obtain ⟨rfl, rfl⟩ := address
              exact ⟨_, get, (item_answer_iff _ _ _).mpr ⟨_, _, tail, rfl, rfl, empty⟩⟩

end Alternatives

namespace Enumeration

variable (E : Enumeration P)

/-- **Every run has an address.** -/
theorem exists_path : ∀ {s : State} (r : P.Run s), ∃ w, E.Path r w
  | _, .nil s => ⟨[], .nil s⟩
  | s, .cons f admitted rest => by
      obtain ⟨i, get⟩ := List.mem_iff_getElem?.mp (E.complete s f admitted)
      obtain ⟨w, tail⟩ := exists_path rest
      exact ⟨i :: w, .cons get tail⟩

/-- **A budgeted run of the step is a search**: budget `n` reports exactly the complete runs
shorter than `n`, by their final states, each once at its address. -/
theorem mem_run_space (n : ℕ) (s : State) (w : List ℕ) (t : State) :
    (w, t) ∈ (E.space.run n (.inr s)).answers ↔
      ∃ (r : P.Run s) (w' : List ℕ), E.Path r w' ∧ w = w' ++ [0] ∧ r.last = t ∧ Halted P t ∧
        r.word.length < n := by
  rw [Space.mem_run, E.item_answer_iff]
  constructor
  · rintro ⟨⟨r, w', path, rfl, last, empty⟩, short⟩
    refine ⟨r, w', path, rfl, last, (E.halted_iff t).mpr empty, ?_⟩
    rw [List.length_append, path.length_eq] at short
    simp only [List.length_singleton] at short
    omega
  · rintro ⟨r, w', path, rfl, last, halted, short⟩
    refine ⟨⟨r, w', path, rfl, last, (E.halted_iff t).mp halted⟩, ?_⟩
    rw [List.length_append, path.length_eq]
    simp only [List.length_singleton]
    omega

/-- **A budget finishes exactly when every run is shorter than it.** -/
theorem status_run_space (n : ℕ) (s : State) :
    (E.space.run n (.inr s)).status = .finished ↔ ∀ r : P.Run s, r.word.length < n := by
  rw [Space.status_run_eq_finished_iff]
  constructor
  · intro shallow r
    obtain ⟨w, path⟩ := E.exists_path r
    have := shallow w r.last ((E.item_state_iff s w r.last).mpr ⟨r, path, rfl⟩)
    rwa [path.length_eq] at this
  · intro short w t state
    obtain ⟨r, path, _⟩ := (E.item_state_iff s w t).mp state
    rw [path.length_eq]
    exact short r

/-- **Multiplicity is the number of complete runs ending at a state.** -/
theorem multiplicity_space (s t : State) :
    E.space.multiplicity (.inr s) t = {r : P.Run s | Halted P r.last ∧ r.last = t}.encard := by
  classical
  unfold Space.multiplicity
  apply Set.encard_congr
  refine
    { toFun := fun w => ⟨((E.item_answer_iff s w.1 t).mp w.2).choose,
        by
          obtain ⟨w', _, _, last, empty⟩ := ((E.item_answer_iff s w.1 t).mp w.2).choose_spec
          exact ⟨by rw [last]; exact (E.halted_iff t).mpr empty, last⟩⟩
      invFun := fun r => ⟨(E.exists_path r.1).choose ++ [0],
        by
          show E.space.item (.inr s) _ = some (.inl t)
          rw [E.item_answer_iff]
          obtain ⟨halted, last⟩ := r.2
          exact ⟨r.1, _, (E.exists_path r.1).choose_spec, rfl, last,
            (E.halted_iff t).mp (last ▸ halted)⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨w, h⟩
    apply Subtype.ext
    change (E.exists_path (Exists.choose _)).choose ++ [0] = w
    generalize_proofs found
    obtain ⟨w', path, address, _, _⟩ := found.choose_spec
    rw [(E.exists_path _).choose_spec.unique_address E.nodup path, ← address]
  · rintro ⟨r, ⟨halted, last⟩⟩
    apply Subtype.ext
    have found : ∃ (r' : P.Run s) (w' : List ℕ), E.Path r' w' ∧
        (E.exists_path r).choose ++ [0] = w' ++ [0] ∧ r'.last = t ∧ E.next t = [] :=
      ⟨r, _, (E.exists_path r).choose_spec, rfl, last, (E.halted_iff t).mp (by rw [← last]; exact halted)⟩
    change found.choose = r
    obtain ⟨w', path, address, _, _⟩ := found.choose_spec
    have := List.append_cancel_right address
    rw [← this] at path
    exact path.unique_run (E.exists_path r).choose_spec

/-- **Collecting complete runs**: a finished budget collects the final states of all complete
runs, each with the number of complete runs ending there; a cut-off budget collects nothing. -/
theorem collect_space [DecidableEq State] (n : ℕ) (s : State) :
    ((E.space.run n (.inr s)).status = .finished →
      ∃ A : Multiset State, Outcome.collect (E.space.approx n (.inr s)) = Outcome.pure A ∧
        ∀ t, (A.count t : ℕ∞) = {r : P.Run s | Halted P r.last ∧ r.last = t}.encard) ∧
    ((E.space.run n (.inr s)).status = .cutOff →
      Outcome.collect (E.space.approx n (.inr s)) = Outcome.unknown) := by
  constructor
  · intro finished
    refine ⟨(E.space.approx n (.inr s)).answers, ?_, fun t => ?_⟩
    · have : (E.space.approx n (.inr s)).status = .finished := finished
      generalize E.space.approx n (.inr s) = o at this ⊢
      obtain ⟨A, st⟩ := o
      change st = _ at this
      subst this
      rfl
    · rw [E.space.count_approx_eq_of_finished finished, multiplicity_space]
  · intro cut
    have : (E.space.approx n (.inr s)).status = .cutOff := cut
    generalize E.space.approx n (.inr s) = o at this ⊢
    obtain ⟨A, st⟩ := o
    change st = _ at this
    subst this
    rfl

end Enumeration

end StepSearch

/-! ## The three outcomes of a certificate search -/

section Certificates

variable {σ : Type u} {α : Type v}

/-- **A certificate search for a proposition**: every answer certifies it, and it has an answer
whenever the proposition holds. -/
structure Certifies (S : Space σ α) (x : α ⊕ σ) (Q : Prop) : Prop where
  sound : ∀ p ∈ S.Answers x, Q
  complete : Q → ∃ p, p ∈ S.Answers x

namespace Certifies

variable {S : Space σ α} {x : α ⊕ σ} {Q : Prop}

/-- **Commit is sound**, at every status. -/
theorem commit (c : Certifies S x Q) {n : ℕ} (h : (S.approx n x).verdict = .commit) : Q := by
  obtain ⟨w, a, answer, _⟩ := S.commit_sound h
  exact c.sound (w, a) answer

/-- **Refuted is sound**: the proposition fails. -/
theorem refuted (c : Certifies S x Q) {n : ℕ} (h : (S.approx n x).verdict = .refuted) : ¬ Q := by
  intro holds
  obtain ⟨⟨w, a⟩, answer⟩ := c.complete holds
  exact S.refuted_sound h w a answer

/-- **Suspended means cut off without a certificate.** -/
theorem suspended_of {n : ℕ} (h : (S.approx n x).verdict = .suspended) :
    (S.run n x).status = .cutOff ∧ (S.approx n x).answers = 0 := by
  rw [Outcome.verdict_eq_suspended_iff] at h
  exact ⟨congrArg Outcome.status h, congrArg Outcome.answers h⟩

/-- A finished budget is never suspended. -/
theorem not_suspended_of_finished {n : ℕ} (finished : (S.run n x).status = .finished) :
    (S.approx n x).verdict ≠ .suspended :=
  Outcome.verdict_ne_suspended_of_finished finished

/-- **Zero budget is always suspended**, whatever holds. -/
theorem zero_suspended (s : σ) : (S.approx 0 (.inr s)).verdict = .suspended := by
  rw [Space.approx_zero]
  rfl

end Certifies

end Certificates

/-! ## The check of independence from a certificate search -/

section IndependenceCheck

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Interface.Step X O State Firing} (T : Interface.Transport.{uO, uT, uH, uOcc, uS, uF, uI} P)
  {σ : Type u} {α : Type v}

/-- The verdict of independence read from a certificate search. -/
def independenceVerdict : Outcome.Verdict → Interface.Transport.Verdict
  | .commit => .independent
  | .refuted => .dependent
  | .suspended => .unknown

/-- **A certificate search for independence gives a sound three-valued check at every budget.** -/
def checkOfSearch (s : State) (space : Firing s → Firing s → Space σ α)
    (root : Firing s → Firing s → α ⊕ σ)
    (certifies : ∀ f g, Certifies (space f g) (root f g) (T.Independent s f g)) (n : ℕ) :
    T.Check s where
  verdict f g := independenceVerdict ((space f g).approx n (root f g)).verdict
  sound_independent f g answered := by
    cases h : ((space f g).approx n (root f g)).verdict
    · exact (certifies f g).commit h
    · rw [h] at answered; cases answered
    · rw [h] at answered; cases answered
  sound_dependent f g answered := by
    cases h : ((space f g).approx n (root f g)).verdict
    · rw [h] at answered; cases answered
    · exact (certifies f g).refuted h
    · rw [h] at answered; cases answered

variable {T}

/-- **Unknown exactly when the search is suspended**: cut off without a certificate. -/
theorem checkOfSearch_unknown_iff {s : State} {space : Firing s → Firing s → Space σ α}
    {root : Firing s → Firing s → α ⊕ σ}
    {certifies : ∀ f g, Certifies (space f g) (root f g) (T.Independent s f g)} {n : ℕ}
    (f g : Firing s) :
    (checkOfSearch T s space root certifies n).verdict f g = .unknown ↔
      ((space f g).run n (root f g)).status = .cutOff ∧ ((space f g).approx n (root f g)).answers = 0 := by
  dsimp only [checkOfSearch]
  constructor
  · intro h
    apply Certifies.suspended_of
    cases hv : ((space f g).approx n (root f g)).verdict <;> rw [hv] at h <;> first | rfl | cases h
  · rintro ⟨cut, empty⟩
    have : ((space f g).approx n (root f g)).verdict = .suspended := by
      rw [Outcome.verdict_eq_suspended_iff]
      exact Outcome.ext empty cut
    rw [this]
    rfl

/-- **Definite verdicts persist at larger budgets.** -/
theorem checkOfSearch_mono {s : State} {space : Firing s → Firing s → Space σ α}
    {root : Firing s → Firing s → α ⊕ σ}
    {certifies : ∀ f g, Certifies (space f g) (root f g) (T.Independent s f g)} {n m : ℕ}
    (le : n ≤ m) (f g : Firing s)
    (definite : (checkOfSearch T s space root certifies n).verdict f g ≠ .unknown) :
    (checkOfSearch T s space root certifies m).verdict f g =
      (checkOfSearch T s space root certifies n).verdict f g := by
  dsimp only [checkOfSearch]
  have notSuspended : ((space f g).approx n (root f g)).verdict ≠ .suspended := by
    intro h
    apply definite
    dsimp only [checkOfSearch]
    rw [h]
    rfl
  rw [(space f g).verdict_run_eq_of_le le notSuspended]

/-- **At a finished budget the check never answers unknown.** -/
theorem checkOfSearch_ne_unknown {s : State} {space : Firing s → Firing s → Space σ α}
    {root : Firing s → Firing s → α ⊕ σ}
    {certifies : ∀ f g, Certifies (space f g) (root f g) (T.Independent s f g)} {n : ℕ}
    (f g : Firing s) (finished : ((space f g).run n (root f g)).status = .finished) :
    (checkOfSearch T s space root certifies n).verdict f g ≠ .unknown := by
  rw [Ne, checkOfSearch_unknown_iff, finished]
  rintro ⟨cut, _⟩
  cases cut

end IndependenceCheck

/-! ## Staged effects: three outcomes, not two -/

section Staged

open StagedSourceEffects

variable {T : Type u} {S : Type v} {O : Type uOcc} [DecidableEq O]
  {action : SubstitutionAction T S} {label : O → T} {code : List (Instruction T S O)}
  {before : Configuration T O} {σ : Type uS} {α : Type uF} {space : Space σ α} {x : α ⊕ σ}

/-- **A commit publishes the source result.** -/
theorem staged_commit (c : Certifies space x (Executable action label before code)) {n : ℕ}
    (h : (space.approx n x).verdict = .commit) :
    SourceResult action label code before
      (ConditionalSchedule.follow label before (code.map Instruction.raw)) :=
  .inl ⟨c.commit h, rfl⟩

/-- **A refutation leaves the configuration, with a proof of nonadmission.** -/
theorem staged_refuted (c : Certifies space x (Executable action label before code)) {n : ℕ}
    (h : (space.approx n x).verdict = .refuted) : SourceResult action label code before before :=
  .inr ⟨c.refuted h, rfl⟩

/-- **Failure to obtain a certificate is not a proof of nonadmission**: at budget zero every
search is suspended; for an executable block with a visible effect, reading that suspension as the
refusal branch contradicts the source contract. -/
theorem staged_suspended_not_refusal (s : σ) (ready : Executable action label before code)
    (visible : ConditionalSchedule.follow label before (code.map Instruction.raw) ≠ before) :
    (space.approx 0 (.inr s)).verdict = .suspended ∧ ¬ SourceResult action label code before before := by
  refine ⟨Certifies.zero_suspended s, ?_⟩
  rintro (⟨_, same⟩ | ⟨refused, _⟩)
  · exact visible same.symm
  · exact refused ready

end Staged

#print axioms Enumeration.halted_iff
#print axioms Alternatives.Path.unique_run
#print axioms Alternatives.Path.unique_address
#print axioms Enumeration.exists_path
#print axioms Alternatives.item_state_iff
#print axioms Alternatives.item_answer_iff
#print axioms Enumeration.mem_run_space
#print axioms Enumeration.status_run_space
#print axioms Enumeration.multiplicity_space
#print axioms Enumeration.collect_space
#print axioms Certifies.commit
#print axioms Certifies.refuted
#print axioms Certifies.suspended_of
#print axioms Certifies.zero_suspended
#print axioms checkOfSearch
#print axioms checkOfSearch_unknown_iff
#print axioms checkOfSearch_mono
#print axioms checkOfSearch_ne_unknown
#print axioms staged_commit
#print axioms staged_refuted
#print axioms staged_suspended_not_refusal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Search
