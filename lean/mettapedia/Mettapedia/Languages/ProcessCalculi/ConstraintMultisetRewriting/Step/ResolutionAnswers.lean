import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResolutionFiring

/-!
# Answers of resolution runs: soundness, completeness, and the choice of goal

## The declarative semantics (`Derives`, `Holds`)

A **proof forest** `Derives prog goals n` derives every atom of `goals` from instances of clauses of
`prog`, with `n` clause instances in all. An atom **holds** (`Holds`) when it has a proof forest.
`Holds` is the least set of atoms closed under the instances of the clauses (`Holds.rule`,
`Holds.least`): for ground atoms it is the least Herbrand model, and it is closed under
instantiation (`Holds.subst`).

## The run-level correspondence

A **resolution run** is a run of the one-frame step all of whose firings are resolution firings of
clauses of the program (`IsResolution`). A run is **complete** when no goal occurrence is left.

* **Soundness** (`sound`, `sound_complete`): every solution of the final knowledge of a complete
  resolution run solves the initial knowledge and makes every initial goal hold. No freshness is
  needed: a renaming that is not apart loses answers, it never invents them.
* **Completeness for every selection rule** (`complete`): given any rule that selects a present
  goal at every configuration, every solution of the initial knowledge at which every initial goal
  holds is extended by a solution of the final knowledge of a complete resolution run that resolves,
  at each step, the selected goal. The run renames each clause apart (`exists_fresh`) and makes fresh
  occurrences for the body goals.

**The step realizes every selection rule at once.** In the step the choice of goal is the choice of
firing: a run is the SLD derivation whose selection rule is "the goal of the next firing". Fairness
of the goal choice is therefore not needed for success, and the completeness theorem holds for
every rule, fair or not.

## Independence of goal selection is trace equivalence

* **Independence of two resolution firings** (`resolve_independent_iff`): two admitted resolution
  firings with distinct made occurrences are independent exactly when they resolve different goals
  and their two unifications are jointly consistent with the knowledge. Two firings that resolve
  one goal, against two clauses, are admitted and dependent (`resolve_same_goal_dependent`).
* **The switching lemma** (`resolve_switch`): when a resolution firing runs after another, on a
  goal that was present before it and with no identity reused, the two are independent; the run
  with the two swapped is trace equivalent (`resolve_switch_traceEquiv`), so it ends in the same
  configuration class and has the same answers (`traceEquiv_same_answers`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open Interface (Transport)

universe uO

variable {sig : LPSignature}

/-! ## The declarative semantics -/

/-- **Proof forests**: every atom of the list is derived from an instance of a clause of the
program, with `n` clause instances in all. -/
inductive Derives (prog : Program sig) : List (Term sig) → ℕ → Prop
  | nil : Derives prog [] 0
  | cons {c : Clause sig} (γ : Subst sig) {rest : List (Term sig)} {n m : ℕ} :
      c ∈ prog → Derives prog (c.body.map γ.applyTerm) n → Derives prog rest m →
      Derives prog (γ.applyTerm c.head :: rest) (n + m + 1)

/-- **An atom holds** when it has a proof forest. -/
def Holds (prog : Program sig) (t : Term sig) : Prop := ∃ n, Derives prog [t] n

namespace Derives

variable {prog : Program sig}

theorem nil_size {n : ℕ} (derived : Derives prog [] n) : n = 0 := by
  cases derived
  rfl

/-- The first atom of a forest is an instance of a clause head. -/
theorem head_inv {l : List (Term sig)} {n : ℕ} (derived : Derives prog l n) {t : Term sig}
    {rest : List (Term sig)} (shape : l = t :: rest) :
    ∃ c ∈ prog, ∃ (γ : Subst sig) (k m : ℕ), γ.applyTerm c.head = t ∧
      Derives prog (c.body.map γ.applyTerm) k ∧ Derives prog rest m ∧ n = k + m + 1 := by
  cases derived with
  | nil => cases shape
  | cons γ member body more =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      exact ⟨_, member, γ, _, _, rfl, body, more, rfl⟩

/-- A forest splits at its first atom. -/
theorem split {t : Term sig} {rest : List (Term sig)} {n : ℕ} (derived : Derives prog (t :: rest) n) :
    ∃ a b, Derives prog [t] a ∧ Derives prog rest b ∧ n = a + b := by
  obtain ⟨c, member, γ, k, m, rfl, body, more, rfl⟩ := derived.head_inv rfl
  exact ⟨k + 0 + 1, m, .cons γ member body .nil, more, by omega⟩

/-- Forests join. -/
theorem join {t : Term sig} {rest : List (Term sig)} {a b : ℕ} (single : Derives prog [t] a)
    (more : Derives prog rest b) : Derives prog (t :: rest) (a + b) := by
  obtain ⟨c, member, γ, k, m, rfl, body, nothing, rfl⟩ := single.head_inv rfl
  rw [nothing.nil_size]
  have joined := Derives.cons γ member body more
  rwa [show k + b + 1 = k + 0 + 1 + b by omega] at joined

/-- A forest derives each of its atoms. -/
theorem holds : ∀ {l : List (Term sig)} {n : ℕ}, Derives prog l n → ∀ t ∈ l, Holds prog t
  | [], _, _, t, member => absurd member List.not_mem_nil
  | _ :: _, _, derived, t, member => by
      obtain ⟨a, b, single, more, -⟩ := derived.split
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨a, single⟩
      · exact holds more t inRest

end Derives

/-- Atoms that each hold have a forest. -/
theorem derives_of_holds {prog : Program sig} :
    ∀ {l : List (Term sig)}, (∀ t ∈ l, Holds prog t) → ∃ n, Derives prog l n
  | [], _ => ⟨0, .nil⟩
  | t :: rest, each => by
      obtain ⟨a, single⟩ := each t List.mem_cons_self
      obtain ⟨b, more⟩ := derives_of_holds fun u member => each u (List.mem_cons_of_mem t member)
      exact ⟨a + b, single.join more⟩

/-- **The clauses hold**: an instance of a clause whose body holds has a head that holds. -/
theorem Holds.rule {prog : Program sig} {c : Clause sig} (member : c ∈ prog) (γ : Subst sig)
    (body : ∀ b ∈ c.body, Holds prog (γ.applyTerm b)) : Holds prog (γ.applyTerm c.head) := by
  obtain ⟨n, forest⟩ := derives_of_holds (l := c.body.map γ.applyTerm) fun t inBody => by
    obtain ⟨b, inC, rfl⟩ := List.mem_map.mp inBody
    exact body b inC
  exact ⟨n + 0 + 1, .cons γ member forest .nil⟩

/-- **`Holds` is the least set closed under the clauses.** -/
theorem Holds.least {prog : Program sig} (M : Term sig → Prop)
    (closed : ∀ c ∈ prog, ∀ γ : Subst sig, (∀ b ∈ c.body, M (γ.applyTerm b)) → M (γ.applyTerm c.head))
    {t : Term sig} (holds : Holds prog t) : M t := by
  obtain ⟨n, forest⟩ := holds
  suffices each : ∀ {l : List (Term sig)} {n : ℕ}, Derives prog l n → ∀ u ∈ l, M u from
    each forest t List.mem_cons_self
  intro l n derived
  induction derived with
  | nil => exact fun u member => absurd member List.not_mem_nil
  | cons γ member _ _ bodyM restM =>
      intro u inList
      rcases List.mem_cons.mp inList with rfl | inRest
      · exact closed _ member γ fun b inBody => bodyM _ (List.mem_map.mpr ⟨b, inBody, rfl⟩)
      · exact restM u inRest

/-- `Holds` is closed under instantiation. -/
theorem Holds.subst {prog : Program sig} (τ : Subst sig) {t : Term sig} (holds : Holds prog t) :
    Holds prog (τ.applyTerm t) := by
  refine Holds.least (fun u => Holds prog (τ.applyTerm u)) (fun c member γ body => ?_) holds
  rw [← Subst.applyTerm_comp]
  exact Holds.rule member (τ ∘ₛ γ) fun b inBody => by
    rw [Subst.applyTerm_comp]
    exact body b inBody

/-! ## Sizes of derivations -/

open Classical in
/-- The fewest clause instances that derive an atom (zero when it does not hold). -/
noncomputable def size (prog : Program sig) (t : Term sig) : ℕ :=
  if h : Holds prog t then Nat.find h else 0

theorem size_spec {prog : Program sig} {t : Term sig} (holds : Holds prog t) :
    Derives prog [t] (size prog t) := by
  classical
  unfold size
  rw [dif_pos holds]
  exact Nat.find_spec holds

theorem size_le {prog : Program sig} {t : Term sig} {n : ℕ} (derived : Derives prog [t] n) :
    size prog t ≤ n := by
  classical
  unfold size
  rw [dif_pos ⟨n, derived⟩]
  exact Nat.find_min' _ derived

/-- The fewest derivations of the atoms of a forest add up to at most its size. -/
theorem sum_size_le {prog : Program sig} :
    ∀ {l : List (Term sig)} {n : ℕ}, Derives prog l n → (l.map (size prog)).sum ≤ n
  | [], _, _ => by simp
  | _ :: _, _, derived => by
      obtain ⟨a, b, single, more, rfl⟩ := derived.split
      rw [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (size_le single) (sum_size_le more)

/-! ## Resolution runs -/

variable [DecidableEq sig.vars] {O : Type uO} [DecidableEq O] {label : O → Term sig}

/-- **A resolution firing of the program.** -/
def IsResolution (prog : Program sig) (f : Firing (Term sig) (Subst sig) O) : Prop :=
  ∃ (o : O) (c : Clause sig) (ρ : Equiv.Perm sig.vars) (made : List O), c ∈ prog ∧ f = resolve o c ρ made

omit [DecidableEq sig.vars] in
/-- **Soundness, along any resolution run**: a solution of the last knowledge at which the last goals
hold solves the first knowledge, and the first goals hold there. -/
theorem sound (prog : Program sig) {C : Configuration (Term sig) O}
    (r : (firstOrder (A sig) label).Run C) (resolving : ∀ x ∈ r.word, IsResolution prog x.2)
    {τ : Subst sig} (solved : (A sig).Models τ r.last.equations)
    (proved : ∀ o ∈ r.last.present, Holds prog (τ.applyTerm (label o))) :
    (A sig).Models τ C.equations ∧ ∀ o ∈ C.present, Holds prog (τ.applyTerm (label o)) := by
  induction r with
  | nil C => exact ⟨solved, proved⟩
  | @cons C f admitted rest ih =>
      have later := ih (fun x member => resolving x (List.mem_cons_of_mem _ member)) solved proved
      obtain ⟨o, c, ρ, made, member, rfl⟩ := resolving ⟨C, f⟩ List.mem_cons_self
      obtain ⟨-, outputs, -, -, -⟩ := (resolve_valid_iff label C o c ρ made).mp admitted
      have result := resolve_result label C o c ρ made
      change (A sig).Models τ ((resolve o c ρ made).result label C).equations ∧
        ∀ x ∈ ((resolve o c ρ made).result label C).present, Holds prog (τ.applyTerm (label x)) at later
      rw [result] at later
      obtain ⟨equations, goals⟩ := later
      obtain ⟨knowledge, pair⟩ := ((A sig).models_append _ _ _).mp equations
      have unified : τ.applyTerm (rename ρ c.head) = τ.applyTerm (label o) :=
        (((A sig).models_cons _ _ _).mp pair).1
      refine ⟨knowledge, fun x present => ?_⟩
      by_cases selected : x = o
      · subst selected
        rw [← unified, rename, ← Subst.applyTerm_comp]
        refine Holds.rule member _ fun b inBody => ?_
        have inLabels : rename ρ b ∈ made.map label := by
          rw [outputs]
          exact List.mem_map.mpr ⟨b, inBody, rfl⟩
        obtain ⟨r, inMade, labelled⟩ := List.mem_map.mp inLabels
        have holds := goals r (Finset.mem_union_right _ (List.mem_toFinset.mpr inMade))
        rw [labelled, rename, ← Subst.applyTerm_comp] at holds
        exact holds
      · exact goals x (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨present, by simpa using selected⟩))

omit [DecidableEq sig.vars] in
/-- **Soundness of complete resolution runs.** -/
theorem sound_complete (prog : Program sig) {C : Configuration (Term sig) O}
    (r : (firstOrder (A sig) label).Run C) (resolving : ∀ x ∈ r.word, IsResolution prog x.2)
    (complete : r.last.present = ∅) {τ : Subst sig} (solved : (A sig).Models τ r.last.equations) :
    (A sig).Models τ C.equations ∧ ∀ o ∈ C.present, Holds prog (τ.applyTerm (label o)) :=
  sound prog r resolving solved fun o member => absurd (complete ▸ member) (Finset.notMem_empty o)

/-! ## Completeness -/

omit [DecidableEq O] in
/-- Substitutions that agree on the variables of a store have the same models there. -/
theorem models_congr_vars {K : EquationStore (Term sig)} {τ τ' : Subst sig}
    (agree : ∀ v ∈ eqVars K, τ v = τ' v) : (A sig).Models τ K ↔ (A sig).Models τ' K := by
  have terms : ∀ e ∈ K, τ.applyTerm e.1 = τ'.applyTerm e.1 ∧ τ.applyTerm e.2 = τ'.applyTerm e.2 :=
    fun e member => ⟨Subst.applyTerm_congr fun v occurs => agree v (mem_eqVars.mpr ⟨e, member, .inl occurs⟩),
      Subst.applyTerm_congr fun v occurs => agree v (mem_eqVars.mpr ⟨e, member, .inr occurs⟩)⟩
  constructor
  · intro solved e member
    have here : τ.applyTerm e.1 = τ.applyTerm e.2 := solved e member
    show τ'.applyTerm e.1 = τ'.applyTerm e.2
    rw [← (terms e member).1, ← (terms e member).2]
    exact here
  · intro solved e member
    have here : τ'.applyTerm e.1 = τ'.applyTerm e.2 := solved e member
    show τ.applyTerm e.1 = τ.applyTerm e.2
    rw [(terms e member).1, (terms e member).2]
    exact here

omit [DecidableEq O] in
theorem eqVars_append_left (K L : EquationStore (Term sig)) : eqVars K ⊆ eqVars (K ++ L) := by
  intro v member
  obtain ⟨e, inK, occurs⟩ := mem_eqVars.mp member
  exact mem_eqVars.mpr ⟨e, List.mem_append_left _ inK, occurs⟩

omit [DecidableEq O] in
theorem eqVars_append_right (K L : EquationStore (Term sig)) : eqVars L ⊆ eqVars (K ++ L) := by
  intro v member
  obtain ⟨e, inL, occurs⟩ := mem_eqVars.mp member
  exact mem_eqVars.mpr ⟨e, List.mem_append_right _ inL, occurs⟩

variable (label) in
/-- **Fresh identities for the body goals**: every renamed body atom of a clause of the program
labels identities outside every finite set. -/
def BodySupply (prog : Program sig) : Prop :=
  ∀ c ∈ prog, ∀ b ∈ c.body, ∀ (ρ : Equiv.Perm sig.vars) (G : Finset O), ∃ o, o ∉ G ∧ label o = rename ρ b

omit [DecidableEq sig.vars] [DecidableEq O] in
/-- Fresh identities for every label give fresh identities for the body goals. -/
theorem BodySupply.of_supply (prog : Program sig)
    (supply : ∀ (t : Term sig) (G : Finset O), ∃ o, o ∉ G ∧ label o = t) : BodySupply label prog :=
  fun _ _ b _ ρ G => supply (rename ρ b) G

omit [DecidableEq sig.vars] in
/-- **Fresh occurrences for a list of labels**, when each of its labels has fresh identities. -/
theorem exists_made :
    ∀ (ts : List (Term sig)), (∀ t ∈ ts, ∀ G : Finset O, ∃ o, o ∉ G ∧ label o = t) → ∀ G : Finset O,
      ∃ made : List O, made.Nodup ∧ made.map label = ts ∧ ∀ r ∈ made, r ∉ G
  | [], _, _ => ⟨[], List.nodup_nil, rfl, fun _ member => absurd member List.not_mem_nil⟩
  | t :: ts, supply, G => by
      obtain ⟨made, nodup, labels, fresh⟩ :=
        exists_made ts (fun u member => supply u (List.mem_cons_of_mem t member)) G
      obtain ⟨r, outside, labelled⟩ := supply t List.mem_cons_self (G ∪ made.toFinset)
      refine ⟨r :: made, List.nodup_cons.mpr ⟨fun inMade => outside
          (Finset.mem_union_right _ (List.mem_toFinset.mpr inMade)), nodup⟩, by
        rw [List.map_cons, labelled, labels], fun x member => ?_⟩
      rcases List.mem_cons.mp member with rfl | inMade
      · exact fun inG => outside (Finset.mem_union_left _ inG)
      · exact fresh x inMade

variable (label) in
/-- The size of the goals of a configuration at a solution: the fewest clause instances that
derive them. -/
noncomputable def measure (prog : Program sig) (C : Configuration (Term sig) O) (σ : Subst sig) : ℕ :=
  ∑ o ∈ C.present, size prog (σ.applyTerm (label o))

/-- **Completeness for every selection rule.** Given a rule that selects a present goal at every
configuration with goals, an infinite supply of variables, and fresh identities for the body goals:
every solution of the initial knowledge at which every initial goal holds agrees, on the variables
of the initial configuration, with a solution of the final knowledge of a complete resolution run
that resolves the selected goal at every step. -/
theorem complete [Infinite sig.vars] (prog : Program sig) (supply : BodySupply label prog)
    (select : Configuration (Term sig) O → O)
    (selects : ∀ C : Configuration (Term sig) O, C.present.Nonempty → select C ∈ C.present)
    (C : Configuration (Term sig) O) (σ : Subst sig) (solved : (A sig).Models σ C.equations)
    (proved : ∀ o ∈ C.present, Holds prog (σ.applyTerm (label o))) :
    ∃ r : (firstOrder (A sig) label).Run C,
      (∀ x ∈ r.word, IsResolution prog x.2 ∧ x.2.selection.taken = [select x.1]) ∧
        r.last.present = ∅ ∧
        ∃ τ : Subst sig, (A sig).Models τ r.last.equations ∧ ∀ v ∈ configVars label C, τ v = σ v := by
  classical
  suffices key : ∀ (N : ℕ) (C : Configuration (Term sig) O) (σ : Subst sig),
      measure label prog C σ = N → (A sig).Models σ C.equations →
      (∀ o ∈ C.present, Holds prog (σ.applyTerm (label o))) →
      ∃ r : (firstOrder (A sig) label).Run C,
        (∀ x ∈ r.word, IsResolution prog x.2 ∧ x.2.selection.taken = [select x.1]) ∧
          r.last.present = ∅ ∧
          ∃ τ : Subst sig, (A sig).Models τ r.last.equations ∧ ∀ v ∈ configVars label C, τ v = σ v from
    key _ C σ rfl solved proved
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C σ sized solved proved
  by_cases empty : C.present = ∅
  · exact ⟨.nil C, fun x member => absurd member List.not_mem_nil, empty, σ, solved, fun _ _ => rfl⟩
  have present : select C ∈ C.present := selects C (Finset.nonempty_iff_ne_empty.mpr empty)
  set o := select C with oDef
  obtain ⟨c, member, γ, k, m, headIs, body, nothing, sizeIs⟩ :=
    (size_spec (proved o present)).head_inv rfl
  rw [nothing.nil_size] at sizeIs
  obtain ⟨ρ, fresh, -⟩ := exists_fresh (configVars label C) c
  let σ' : Subst sig := fun v => if ρ.symm v ∈ c.vars then γ (ρ.symm v) else σ v
  have agree : ∀ v ∈ configVars label C, σ' v = σ v := by
    intro v inC
    have outside : ρ.symm v ∉ c.vars := fun inClause => fresh _ inClause (by simpa using inC)
    simp only [σ', if_neg outside]
  have onClause : ∀ t : Term sig, t.freeVars ⊆ c.vars → σ'.applyTerm (rename ρ t) = γ.applyTerm t := by
    intro t inside
    rw [rename, ← Subst.applyTerm_comp]
    refine Subst.applyTerm_congr fun v occurs => ?_
    show σ' (ρ v) = γ v
    simp only [σ', Equiv.symm_apply_apply, if_pos (inside occurs)]
  have onConfig : ∀ t : Term sig, t.freeVars ⊆ configVars label C → σ'.applyTerm t = σ.applyTerm t :=
    fun t inside => Subst.applyTerm_congr fun v occurs => agree v (inside occurs)
  obtain ⟨made, nodup, outputs, freshMade⟩ := exists_made (c.body.map (rename ρ))
    (fun t inBody G => by
      obtain ⟨b, inC, rfl⟩ := List.mem_map.mp inBody
      exact supply c member b inC ρ G) C.present
  have knowledge : (A sig).Models σ' C.equations :=
    (models_congr_vars fun v inK => agree v (eqVars_subset_configVars C inK)).mpr solved
  have goalVars := label_vars_subset_configVars (label := label) present
  have unified : σ'.applyTerm (rename ρ c.head) = σ'.applyTerm (label o) := by
    rw [onClause _ c.head_vars, headIs, onConfig _ goalVars]
  have valid : (resolve o c ρ made).Valid (A sig) label C :=
    (resolve_valid_iff label C o c ρ made).mpr ⟨nodup, outputs, present, freshMade, σ', knowledge, unified⟩
  have result := resolve_result label C o c ρ made
  have solved' : (A sig).Models σ' ((resolve o c ρ made).result label C).equations := by
    rw [result]
    exact ((A sig).models_append _ _ _).mpr
      ⟨knowledge, ((A sig).models_cons _ _ _).mpr ⟨unified, (A sig).models_nil _⟩⟩
  have bodyHolds : ∀ b ∈ c.body, Holds prog (γ.applyTerm b) := fun b inBody =>
    body.holds _ (List.mem_map.mpr ⟨b, inBody, rfl⟩)
  have madeLabel : ∀ r ∈ made, ∃ b ∈ c.body, label r = rename ρ b := by
    intro r inMade
    have inLabels : label r ∈ c.body.map (rename ρ) := by
      rw [← outputs]
      exact List.mem_map.mpr ⟨r, inMade, rfl⟩
    obtain ⟨b, inBody, same⟩ := List.mem_map.mp inLabels
    exact ⟨b, inBody, same.symm⟩
  have proved' : ∀ x ∈ ((resolve o c ρ made).result label C).present,
      Holds prog (σ'.applyTerm (label x)) := by
    rw [result]
    intro x inResult
    rcases Finset.mem_union.mp inResult with old | new
    · have inC := (Finset.mem_sdiff.mp old).1
      rw [onConfig _ (label_vars_subset_configVars inC)]
      exact proved x inC
    · obtain ⟨b, inBody, labelled⟩ := madeLabel x (List.mem_toFinset.mp new)
      rw [labelled, onClause _ (c.body_vars inBody)]
      exact bodyHolds b inBody
  have apart : Disjoint (C.present.erase o) made.toFinset :=
    Finset.disjoint_left.mpr fun {x} inOld inMade =>
      freshMade x (List.mem_toFinset.mp inMade) (Finset.mem_of_mem_erase inOld)
  have smaller : measure label prog ((resolve o c ρ made).result label C) σ' < N := by
    rw [← sized]
    unfold measure
    rw [result]
    show ∑ x ∈ (C.present \ {o}) ∪ made.toFinset, size prog (σ'.applyTerm (label x)) <
      ∑ x ∈ C.present, size prog (σ.applyTerm (label x))
    rw [Finset.sdiff_singleton_eq_erase, Finset.sum_union apart, List.sum_toFinset _ nodup,
      ← Finset.add_sum_erase _ _ present]
    have old : ∑ x ∈ C.present.erase o, size prog (σ'.applyTerm (label x)) =
        ∑ x ∈ C.present.erase o, size prog (σ.applyTerm (label x)) :=
      Finset.sum_congr rfl fun x inOld =>
        by rw [onConfig _ (label_vars_subset_configVars (Finset.mem_of_mem_erase inOld))]
    have new : (made.map fun x => size prog (σ'.applyTerm (label x))).sum ≤ k := by
      have rewritten : (made.map fun x => size prog (σ'.applyTerm (label x))) =
          ((c.body.map γ.applyTerm).map (size prog)) := by
        have viaLabels : (made.map fun x => size prog (σ'.applyTerm (label x))) =
            (made.map label).map (fun t => size prog (σ'.applyTerm t)) := by
          rw [List.map_map]
          rfl
        rw [viaLabels, outputs, List.map_map, List.map_map]
        refine List.map_congr_left fun b inBody => ?_
        show size prog (σ'.applyTerm (rename ρ b)) = size prog (γ.applyTerm b)
        rw [onClause _ (c.body_vars inBody)]
      rw [rewritten]
      exact sum_size_le body
    have total : size prog (σ.applyTerm (label o)) = k + 1 := by
      rw [sizeIs]
    rw [old, total]
    omega
  obtain ⟨r, steps, complete, τ, final, extends'⟩ :=
    ih _ smaller _ σ' rfl solved' proved'
  refine ⟨.cons (resolve o c ρ made) valid r, ?_, complete, τ, final, ?_⟩
  · intro x inWord
    rcases List.mem_cons.mp inWord with rfl | later
    · exact ⟨⟨o, c, ρ, made, member, rfl⟩, rfl⟩
    · exact steps x later
  · intro v inC
    rw [← agree v inC]
    refine extends' v ?_
    rw [result]
    rcases Finset.mem_union.mp inC with inK | inGoals
    · exact Finset.mem_union_left _ (eqVars_append_left _ _ inK)
    · obtain ⟨x, inPresent, occurs⟩ := Finset.mem_biUnion.mp inGoals
      by_cases selected : x = o
      · subst selected
        refine Finset.mem_union_left _ (eqVars_append_right _ _ ?_)
        exact mem_eqVars.mpr ⟨_, List.mem_cons_self, .inr occurs⟩
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x, Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨inPresent, by simpa using selected⟩), occurs⟩)

/-! ## Independence of goal selection -/

omit [DecidableEq sig.vars] in
/-- Two equations join a store in either order with the same solutions. -/
theorem consistent_swap (K : EquationStore (Term sig)) (e e' : Equation (Term sig)) :
    (A sig).Consistent (K ++ [e] ++ [e']) ↔ (A sig).Consistent (K ++ [e'] ++ [e]) := by
  refine (A sig).equivalent_consistent fun τ => ?_
  simp only [SubstitutionAction.models_append]
  exact ⟨fun ⟨⟨k, a⟩, b⟩ => ⟨⟨k, b⟩, a⟩, fun ⟨⟨k, b⟩, a⟩ => ⟨⟨k, a⟩, b⟩⟩

omit [DecidableEq sig.vars] in
/-- **Independence of two resolution firings**: two admitted resolution firings with distinct made
occurrences are independent exactly when they resolve different goals and their unifications are
jointly consistent with the knowledge. -/
theorem resolve_independent_iff {C : Configuration (Term sig) O} {o o' : O} {c c' : Clause sig}
    {ρ ρ' : Equiv.Perm sig.vars} {made made' : List O}
    (first : (resolve o c ρ made).Valid (A sig) label C)
    (second : (resolve o' c' ρ' made').Valid (A sig) label C)
    (apart : ∀ r ∈ made, r ∉ made') :
    (firstOrderTransport (A sig) label).Independent C (resolve o c ρ made) (resolve o' c' ρ' made') ↔
      o ≠ o' ∧ (A sig).Consistent
        (C.equations ++ [(rename ρ c.head, label o)] ++ [(rename ρ' c'.head, label o')]) := by
  obtain ⟨nodup, outputs, present, freshMade, -⟩ := (resolve_valid_iff label C o c ρ made).mp first
  obtain ⟨nodup', outputs', present', freshMade', -⟩ := (resolve_valid_iff label C o' c' ρ' made').mp second
  rw [AnnotatedRuns.firstOrder_independent_iff]
  constructor
  · rintro ⟨-, -, afterFirst, -⟩
    obtain ⟨-, -, inResult, -, unifiable⟩ := (resolve_valid_iff label _ o' c' ρ' made').mp afterFirst
    rw [resolve_result] at inResult unifiable
    refine ⟨fun same => ?_, (unifiable_iff_consistent _ _ _).mp unifiable⟩
    subst same
    rcases Finset.mem_union.mp inResult with old | new
    · simp at old
    · exact freshMade _ (List.mem_toFinset.mp new) present
  · rintro ⟨distinct, consistent⟩
    refine ⟨first, second, ?_, ?_⟩
    · refine (resolve_valid_iff label _ o' c' ρ' made').mpr ⟨nodup', outputs', ?_, ?_, ?_⟩
      · rw [resolve_result]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨present', by simpa [eq_comm] using distinct⟩)
      · intro r inMade' inResult
        rw [resolve_result] at inResult
        rcases Finset.mem_union.mp inResult with old | new
        · exact freshMade' r inMade' (Finset.mem_sdiff.mp old).1
        · exact apart r (List.mem_toFinset.mp new) inMade'
      · rw [resolve_result, unifiable_iff_consistent]
        exact consistent
    · refine (resolve_valid_iff label _ o c ρ made).mpr ⟨nodup, outputs, ?_, ?_, ?_⟩
      · rw [resolve_result]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨present, by simpa using distinct⟩)
      · intro r inMade inResult
        rw [resolve_result] at inResult
        rcases Finset.mem_union.mp inResult with old | new
        · exact freshMade r inMade (Finset.mem_sdiff.mp old).1
        · exact apart r inMade (List.mem_toFinset.mp new)
      · rw [resolve_result, unifiable_iff_consistent]
        exact (consistent_swap _ _ _).mp consistent

omit [DecidableEq sig.vars] in
/-- **Two firings that compete for one goal are dependent**, though both are admitted. -/
theorem resolve_same_goal_dependent {C : Configuration (Term sig) O} {o : O} {c c' : Clause sig}
    {ρ ρ' : Equiv.Perm sig.vars} {made made' : List O}
    (first : (resolve o c ρ made).Valid (A sig) label C)
    (second : (resolve o c' ρ' made').Valid (A sig) label C)
    (apart : ∀ r ∈ made, r ∉ made') :
    ¬ (firstOrderTransport (A sig) label).Independent C (resolve o c ρ made) (resolve o c' ρ' made') :=
  fun independent => ((resolve_independent_iff first second apart).mp independent).1 rfl

omit [DecidableEq sig.vars] in
/-- **The switching lemma**: a resolution firing that runs after another, on a goal present before
it and with no identity reused, is independent of it. -/
theorem resolve_switch {C : Configuration (Term sig) O} {o o' : O} {c c' : Clause sig}
    {ρ ρ' : Equiv.Perm sig.vars} {made made' : List O}
    (first : (resolve o c ρ made).Valid (A sig) label C)
    (after : (resolve o' c' ρ' made').Valid (A sig) label ((resolve o c ρ made).result label C))
    (wasPresent : o' ∈ C.present) (notReused : o ∉ made') :
    (firstOrderTransport (A sig) label).Independent C (resolve o c ρ made) (resolve o' c' ρ' made') := by
  obtain ⟨-, -, present, freshMade, -⟩ := (resolve_valid_iff label C o c ρ made).mp first
  obtain ⟨nodup', outputs', inResult, freshAfter, unifiable⟩ :=
    (resolve_valid_iff label _ o' c' ρ' made').mp after
  rw [resolve_result] at inResult freshAfter unifiable
  have consistent := (unifiable_iff_consistent _ _ _).mp unifiable
  have apart : ∀ r ∈ made, r ∉ made' := fun r inMade inMade' =>
    freshAfter r inMade' (Finset.mem_union_right _ (List.mem_toFinset.mpr inMade))
  have second : (resolve o' c' ρ' made').Valid (A sig) label C := by
    refine (resolve_valid_iff label C o' c' ρ' made').mpr ⟨nodup', outputs', wasPresent, ?_, ?_⟩
    · intro r inMade' inC
      have ne : r ≠ o := fun same => notReused (same ▸ inMade')
      exact freshAfter r inMade' (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨inC, by simpa using ne⟩))
    · rw [unifiable_iff_consistent]
      obtain ⟨τ, solved⟩ := consistent
      obtain ⟨⟨knowledge, -⟩, pair⟩ := by simpa only [SubstitutionAction.models_append] using solved
      exact ⟨τ, ((A sig).models_append _ _ _).mpr ⟨knowledge, pair⟩⟩
  refine (resolve_independent_iff first second apart).mpr ⟨fun same => ?_, consistent⟩
  subst same
  rcases Finset.mem_union.mp inResult with old | new
  · simp at old
  · exact freshMade _ (List.mem_toFinset.mp new) present

omit [DecidableEq sig.vars] in
/-- **Swapping the choice of goal is a trace equivalence**: the two orders of an independent pair of
resolution firings, followed by a continuation carried along the closing isomorphism, are trace
equivalent runs. -/
theorem resolve_switch_traceEquiv {C : Configuration (Term sig) O} {f g : Firing (Term sig) (Subst sig) O}
    (independent : (firstOrderTransport (A sig) label).Independent C f g) :
    ∃ (first : f.Valid (A sig) label C) (second : g.Valid (A sig) label C)
      (afterFirst : g.Valid (A sig) label (f.result label C))
      (afterSecond : f.Valid (A sig) label (g.result label C))
      (close : (firstOrderTransport (A sig) label).Iso (g.result label (f.result label C))
        (f.result label (g.result label C))),
      ∀ rest : (firstOrder (A sig) label).Run (g.result label (f.result label C)),
        (firstOrderTransport (A sig) label).TraceEquiv C
          (.cons f first (.cons g afterFirst rest))
          (.cons g second (.cons f afterSecond ((firstOrderTransport (A sig) label).moveRun close rest))) := by
  obtain ⟨first, second, afterFirst, afterSecond, close, swaps⟩ := independent.swap
  exact ⟨first, second, afterFirst, afterSecond, close, fun rest => .rel _ _ (.inl (swaps rest))⟩

omit [DecidableEq sig.vars] in
/-- **Trace-equivalent runs have the same answers**: their last configurations have the same
solutions and the same goals. -/
theorem traceEquiv_same_answers {C : Configuration (Term sig) O} {r r' : (firstOrder (A sig) label).Run C}
    (equivalent : (firstOrderTransport (A sig) label).TraceEquiv C r r') :
    (∀ τ : Subst sig, (A sig).Models τ r.last.equations ↔ (A sig).Models τ r'.last.equations) ∧
      r.last.present = r'.last.present := by
  obtain ⟨⟨same⟩⟩ := Transport.TraceEquiv.same_last equivalent
  exact ⟨same.1, same.2⟩

#print axioms Derives.head_inv
#print axioms Derives.split
#print axioms Derives.join
#print axioms Derives.holds
#print axioms derives_of_holds
#print axioms Holds.rule
#print axioms Holds.least
#print axioms Holds.subst
#print axioms size_spec
#print axioms size_le
#print axioms sum_size_le
#print axioms sound
#print axioms sound_complete
#print axioms models_congr_vars
#print axioms BodySupply.of_supply
#print axioms exists_made
#print axioms complete
#print axioms consistent_swap
#print axioms resolve_independent_iff
#print axioms resolve_same_goal_dependent
#print axioms resolve_switch
#print axioms resolve_switch_traceEquiv
#print axioms traceEquiv_same_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution
