import Mettapedia.Logic.ASP.Solver

/-!
# Unfounded sets by source pointers

The solver's unfounded-set propagation (`Program.Step.unfounded`) applies to any
set unfounded with respect to the trail. This module gives the executable check a
solver runs, in the style of the source pointers of smodels and clasp, and proves
that it computes exactly the greatest unfounded set.

## Data and operation

* A source list (`Sourced`) pairs atoms with their source rules, newest first: the
  rule's head is the atom, its body is not assigned false (the complement of the
  body's literal, `Body.lit`, is not assigned: `F a` for a unit body `a`, `T b` for a
  unit body `not b`, `F B` otherwise), and its positive body atoms are sourced by
  older entries. Atoms appear once.
* `keepSources` keeps the sources of an earlier list that are still valid under the
  current assignment, oldest first; a source is lost when its body is assigned
  false or a positive body atom lost its source.
* `sourcePass` makes one pass over the rules and sources the head of every rule
  whose body is not assigned false and whose positive atoms are sourced;
  `sourceIter` repeats passes until nothing changes, at most one pass more than
  the program has rules.
* `unfoundedCheck` returns the new sources and the program atoms left without a
  source.

## Results

* An atom is founded (`Founded`) when some rule for it has a body not assigned
  false and founded positive atoms. Every sourced atom is founded
  (`Sourced.founded`).
* The source list after the check is closed (`unfoundedCheck_closed`), so the
  sourced atoms are exactly the founded atoms (`mem_sources_iff_founded`).
* **The atoms the check marks form an unfounded set** of the current assignment
  (`unfoundedCheck_unfounded`), and **every unfounded set of program atoms is
  among them** (`unfoundedCheck_greatest`): the check computes exactly the greatest
  unfounded set (`mem_unfoundedCheck_iff`).
* **Their loop nogoods are what the solver adds**: for an unassigned marked atom,
  pushing its negation with the loop nogood of the marked set as reason is a
  step of the solver when no marked atom is a falsum atom (`unfoundedCheck_step`);
  for a true marked atom that loop nogood is falsified (`unfoundedCheck_conflict`).

The input source list may be anything, such as the sources of an earlier call:
`keepSources` re-validates it, so correctness does not depend on it, and work is
saved on the atoms whose sources stay valid.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

universe u

variable {A : Type u}

section SourcePointers

variable [DecidableEq A]

namespace Program

variable (P : Program A)

/-- Atoms founded with respect to the assigned literals: the least set closed under the rules
whose body is not assigned false. -/
inductive Founded (assigned : List (Lit A)) : A → Prop
  | rule {r : Rule A} : r ∈ P → r.body.lit.compl ∉ assigned → (∀ b ∈ r.pos, Founded assigned b) →
      Founded assigned r.head

/-- A source list, newest first: each atom once, with a rule for it whose body is not assigned
false and whose positive atoms are sourced by older entries. -/
inductive Sourced (assigned : List (Lit A)) : List (A × Rule A) → Prop
  | nil : Sourced assigned []
  | cons {a : A} {r : Rule A} {src : List (A × Rule A)} : Sourced assigned src → a ∉ src.map Prod.fst →
      r ∈ P → r.head = a → r.body.lit.compl ∉ assigned → (∀ b ∈ r.pos, b ∈ src.map Prod.fst) →
      Sourced assigned ((a, r) :: src)

omit [DecidableEq A] in
/-- **Sourced atoms are founded.** -/
theorem Sourced.founded {assigned : List (Lit A)} : ∀ {src : List (A × Rule A)}, P.Sourced assigned src →
    ∀ a ∈ src.map Prod.fst, P.Founded assigned a
  | [], _, a, h => absurd h List.not_mem_nil
  | _ :: _, .cons rest _ hr head notFalse pos, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · rw [← head]
      exact .rule hr notFalse fun b hb => Sourced.founded rest b (pos b hb)
    · exact Sourced.founded rest a h

omit [DecidableEq A] in
theorem Sourced.nodup {assigned : List (Lit A)} : ∀ {src : List (A × Rule A)}, P.Sourced assigned src →
    (src.map Prod.fst).Nodup
  | [], _ => List.nodup_nil
  | _ :: _, .cons rest fresh _ _ _ _ => List.nodup_cons.mpr ⟨fresh, Sourced.nodup rest⟩

omit [DecidableEq A] in
theorem Sourced.head_mem {assigned : List (Lit A)} : ∀ {src : List (A × Rule A)}, P.Sourced assigned src →
    ∀ a ∈ src.map Prod.fst, a ∈ P.map Rule.head
  | [], _, a, h => absurd h List.not_mem_nil
  | _ :: _, .cons rest _ hr head _ _, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_map.mpr ⟨_, hr, head⟩
    · exact Sourced.head_mem rest a h

theorem Sourced.length_le {assigned : List (Lit A)} {src : List (A × Rule A)} (h : P.Sourced assigned src) :
    src.length ≤ P.length := by
  have card := List.toFinset_card_of_nodup (Sourced.nodup P h)
  rw [List.length_map] at card
  rw [← card]
  calc (src.map Prod.fst).toFinset.card ≤ (P.map Rule.head).toFinset.card :=
        Finset.card_le_card fun a ha => List.mem_toFinset.mpr
          (Sourced.head_mem P h a (List.mem_toFinset.mp ha))
    _ ≤ (P.map Rule.head).length := List.toFinset_card_le _
    _ = P.length := List.length_map _

/-! ## The operations -/

/-- **Keep the sources still valid**, oldest first. -/
def keepSources (assigned : List (Lit A)) : List (A × Rule A) → List (A × Rule A)
  | [] => []
  | (a, r) :: src =>
    if a ∉ (keepSources assigned src).map Prod.fst ∧ r ∈ P ∧ r.head = a ∧ r.body.lit.compl ∉ assigned ∧
        ∀ b ∈ r.pos, b ∈ (keepSources assigned src).map Prod.fst then
      (a, r) :: keepSources assigned src
    else keepSources assigned src

/-- Source the head of a rule, if its body is not assigned false and its positive atoms are
sourced. -/
def sourceRule (assigned : List (Lit A)) (acc : List (A × Rule A)) (r : Rule A) : List (A × Rule A) :=
  if r.head ∉ acc.map Prod.fst ∧ r.body.lit.compl ∉ assigned ∧ ∀ b ∈ r.pos, b ∈ acc.map Prod.fst then
    (r.head, r) :: acc
  else acc

/-- **One pass over the rules.** -/
def sourcePass (assigned : List (Lit A)) (src : List (A × Rule A)) : List (A × Rule A) :=
  P.foldl (sourceRule assigned) src

/-- **Passes until nothing changes**, at most `n`. -/
def sourceIter (assigned : List (Lit A)) : ℕ → List (A × Rule A) → List (A × Rule A)
  | 0, src => src
  | n + 1, src =>
    if (P.sourcePass assigned src).length = src.length then src
    else sourceIter assigned n (P.sourcePass assigned src)

/-- The sources after the check. -/
def sources (assigned : List (Lit A)) (src : List (A × Rule A)) : List (A × Rule A) :=
  P.sourceIter assigned (P.length + 1) (P.keepSources assigned src)

/-- The program atoms left without a source. -/
def marked (assigned : List (Lit A)) (src : List (A × Rule A)) : List A :=
  P.allAtoms.filter fun a => a ∉ (P.sources assigned src).map Prod.fst

/-- **The source-pointer unfounded-set check**: the new sources, and the program atoms left
without a source. -/
def unfoundedCheck (assigned : List (Lit A)) (src : List (A × Rule A)) : List (A × Rule A) × List A :=
  (P.sources assigned src, P.marked assigned src)

/-! ## Correctness -/

theorem keepSources_sourced (assigned : List (Lit A)) :
    ∀ src : List (A × Rule A), P.Sourced assigned (P.keepSources assigned src)
  | [] => .nil
  | (a, r) :: src => by
    unfold keepSources
    split
    · rename_i h
      exact .cons (keepSources_sourced assigned src) h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    · exact keepSources_sourced assigned src

theorem sourceRule_sourced {assigned : List (Lit A)} {acc : List (A × Rule A)} (h : P.Sourced assigned acc)
    {r : Rule A} (hr : r ∈ P) : P.Sourced assigned (sourceRule assigned acc r) := by
  unfold sourceRule
  split
  · rename_i c
    exact .cons h c.1 hr rfl c.2.1 c.2.2
  · exact h

theorem sourceRule_sub (assigned : List (Lit A)) (acc : List (A × Rule A)) (r : Rule A) :
    ∃ pre, sourceRule assigned acc r = pre ++ acc := by
  unfold sourceRule
  split
  · exact ⟨[_], rfl⟩
  · exact ⟨[], rfl⟩

theorem foldl_sourceRule_sourced {assigned : List (Lit A)} :
    ∀ (rules : List (Rule A)), (∀ r ∈ rules, r ∈ P) → ∀ {acc : List (A × Rule A)}, P.Sourced assigned acc →
      P.Sourced assigned (rules.foldl (sourceRule assigned) acc)
  | [], _, _, h => h
  | r :: rules, within, acc, h => by
    rw [List.foldl_cons]
    exact foldl_sourceRule_sourced rules (fun r' h' => within r' (List.mem_cons_of_mem _ h'))
      (P.sourceRule_sourced h (within r List.mem_cons_self))

theorem foldl_sourceRule_sub (assigned : List (Lit A)) :
    ∀ (rules : List (Rule A)) (acc : List (A × Rule A)), ∃ pre, rules.foldl (sourceRule assigned) acc = pre ++ acc
  | [], acc => ⟨[], rfl⟩
  | r :: rules, acc => by
    rw [List.foldl_cons]
    obtain ⟨pre, h⟩ := sourceRule_sub assigned acc r
    obtain ⟨pre', h'⟩ := foldl_sourceRule_sub assigned rules (sourceRule assigned acc r)
    exact ⟨pre' ++ pre, by rw [h', h, List.append_assoc]⟩

/-- A pass that adds nothing leaves a closed list. -/
theorem foldl_sourceRule_closed {assigned : List (Lit A)} :
    ∀ (rules : List (Rule A)) (acc : List (A × Rule A)),
      (rules.foldl (sourceRule assigned) acc).length = acc.length →
      ∀ r ∈ rules, r.body.lit.compl ∉ assigned → (∀ b ∈ r.pos, b ∈ acc.map Prod.fst) → r.head ∈ acc.map Prod.fst
  | [], _, _, r, hr => absurd hr List.not_mem_nil
  | r :: rules, acc, same, r', hr' => by
    rw [List.foldl_cons] at same
    obtain ⟨pre, hpre⟩ := foldl_sourceRule_sub assigned rules (sourceRule assigned acc r)
    have unchanged : sourceRule assigned acc r = acc := by
      obtain ⟨pre', hpre'⟩ := sourceRule_sub assigned acc r
      rw [hpre, hpre'] at same
      simp only [List.length_append] at same
      have : pre' = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [hpre', this, List.nil_append]
    rcases List.mem_cons.mp hr' with rfl | hr'
    · intro notFalse pos
      by_contra absent
      have : sourceRule assigned acc r' = (r'.head, r') :: acc := by
        unfold sourceRule
        rw [if_pos ⟨absent, notFalse, pos⟩]
      rw [unchanged] at this
      exact absurd (congrArg List.length this) (by simp)
    · rw [unchanged] at same
      exact foldl_sourceRule_closed rules acc same r' hr'

/-- The source list is closed: every rule with a body not assigned false and sourced positive
atoms has a sourced head. -/
def Closed (assigned : List (Lit A)) (src : List (A × Rule A)) : Prop :=
  ∀ r ∈ P, r.body.lit.compl ∉ assigned → (∀ b ∈ r.pos, b ∈ src.map Prod.fst) → r.head ∈ src.map Prod.fst

theorem sourceIter_spec {assigned : List (Lit A)} :
    ∀ (n : ℕ) {src : List (A × Rule A)}, P.Sourced assigned src → P.length + 1 ≤ n + src.length →
      P.Sourced assigned (P.sourceIter assigned n src) ∧ P.Closed assigned (P.sourceIter assigned n src)
  | 0, src, h, bound => by
    have := Sourced.length_le P h
    omega
  | n + 1, src, h, bound => by
    unfold sourceIter
    split
    · rename_i same
      exact ⟨h, foldl_sourceRule_closed P src same⟩
    · rename_i grew
      have next := P.foldl_sourceRule_sourced P (fun _ h => h) h
      obtain ⟨pre, hpre⟩ := foldl_sourceRule_sub assigned P src
      have longer : src.length < (P.sourcePass assigned src).length := by
        unfold sourcePass at grew ⊢
        rw [hpre, List.length_append] at grew ⊢
        omega
      exact sourceIter_spec n next (by omega)

theorem unfoundedCheck_sourced (assigned : List (Lit A)) (src : List (A × Rule A)) :
    P.Sourced assigned (P.sources assigned src) :=
  (P.sourceIter_spec (P.length + 1) (P.keepSources_sourced assigned src) (by omega)).1

theorem unfoundedCheck_closed (assigned : List (Lit A)) (src : List (A × Rule A)) :
    P.Closed assigned (P.sources assigned src) :=
  (P.sourceIter_spec (P.length + 1) (P.keepSources_sourced assigned src) (by omega)).2

/-- **The sourced atoms are exactly the founded atoms.** -/
theorem mem_sources_iff_founded (assigned : List (Lit A)) (src : List (A × Rule A)) (a : A) :
    a ∈ (P.sources assigned src).map Prod.fst ↔ P.Founded assigned a := by
  constructor
  · exact Sourced.founded P (P.unfoundedCheck_sourced assigned src) a
  · intro founded
    induction founded with
    | rule hr notFalse _ ih => exact P.unfoundedCheck_closed assigned src _ hr notFalse ih

/-- A founded atom is in no unfounded set. -/
theorem Founded.not_mem {assigned : List (Lit A)} {U : Finset A} (unfounded : P.UnfoundedBy assigned U)
    {a : A} (h : P.Founded assigned a) : a ∉ U := by
  induction h with
  | @rule r hr notFalse _ ih =>
    intro member
    rcases unfounded r hr member with assignedFalse | ⟨b, hb, inside⟩
    · exact notFalse assignedFalse
    · exact ih b hb inside

/-- **The marked atoms form an unfounded set** of the current assignment. -/
theorem unfoundedCheck_unfounded (assigned : List (Lit A)) (src : List (A × Rule A)) :
    P.UnfoundedBy assigned (P.marked assigned src).toFinset := by
  intro r hr head
  rw [List.mem_toFinset] at head
  have notSourced : r.head ∉ (P.sources assigned src).map Prod.fst :=
    of_decide_eq_true (List.mem_filter.mp head).2
  by_cases notFalse : r.body.lit.compl ∈ assigned
  · exact Or.inl notFalse
  · right
    by_contra all
    push Not at all
    apply notSourced
    refine P.unfoundedCheck_closed assigned src r hr notFalse fun b hb => ?_
    by_contra absent
    apply all b hb
    rw [List.mem_toFinset]
    exact List.mem_filter.mpr ⟨(P.mem_allAtoms).mpr ⟨r, hr, Or.inr (Or.inl hb)⟩, decide_eq_true absent⟩

/-- **Every unfounded set of program atoms is among the marked atoms.** -/
theorem unfoundedCheck_greatest (assigned : List (Lit A)) (src : List (A × Rule A)) {U : Finset A}
    (unfounded : P.UnfoundedBy assigned U) {a : A} (member : a ∈ U) (program : a ∈ P.atomSet) :
    a ∈ (P.marked assigned src) := by
  refine List.mem_filter.mpr ⟨(P.mem_allAtoms).mpr program, decide_eq_true fun sourced => ?_⟩
  exact Founded.not_mem P unfounded ((P.mem_sources_iff_founded assigned src a).mp sourced) member

/-- **The check computes exactly the greatest unfounded set.** -/
theorem mem_unfoundedCheck_iff (assigned : List (Lit A)) (src : List (A × Rule A)) (a : A) :
    a ∈ (P.marked assigned src) ↔ a ∈ P.atomSet ∧ ∃ U : Finset A, P.UnfoundedBy assigned U ∧ a ∈ U := by
  constructor
  · intro h
    exact ⟨(P.mem_allAtoms).mp (List.mem_filter.mp h).1, _, P.unfoundedCheck_unfounded assigned src,
      List.mem_toFinset.mpr h⟩
  · rintro ⟨program, U, unfounded, member⟩
    exact P.unfoundedCheck_greatest assigned src unfounded member program

/-! ## Refinement of the solver -/

/-- **The loop nogood of the marked set is the reason the solver adds**: when no marked atom is a
falsum atom, pushing the negation of an unassigned marked atom is a solver step. The driver leaves
the falsum atoms out of the set (`Program.loopMarked`). -/
theorem unfoundedCheck_step {s : State A} (src : List (A × Rule A)) {a : A}
    (noFalsum : ∀ x ∈ P.marked s.lits src, ¬ P.Falsum x)
    (marked : a ∈ (P.marked s.lits src)) (unassigned : ¬ s.Assigned (.atom a)) :
    P.Step (.running s)
      (.running (s.push ⟨fAtom a, levelOf s.trail, some (P.loopNogood (P.marked s.lits src).toFinset a)⟩)) :=
  Step.unfounded P (P.unfoundedCheck_unfounded s.lits src) (fun x hx => noFalsum x (List.mem_toFinset.mp hx))
    (List.mem_toFinset.mpr marked) unassigned
    ((P.mem_allAtoms).mp (List.mem_filter.mp marked).1)

/-- For a true marked atom, the loop nogood of the marked set is falsified: a conflict. -/
theorem unfoundedCheck_conflict {s : State A} (src : List (A × Rule A)) {a : A} (isTrue : tAtom a ∈ s.lits) :
    s.Falsifies (P.loopNogood (P.marked s.lits src).toFinset a) := by
  intro l hl
  by_cases same : l = tAtom a
  · exact same ▸ isTrue
  · exact P.loopNogood_unit_of_unfounded (P.unfoundedCheck_unfounded s.lits src) a l hl same

end Program

end SourcePointers

end Mettapedia.Logic.ASP
