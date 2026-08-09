import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mettapedia.Machines.ConeDuality

/-!
# Sequential binding discipline: the algebra that decides repeated-variable
semantics

A sequential binding form — `let*`, a chain of `let`s, a conjunction of
patterns processed left to right — must choose what a *repeated variable
spelling* means across its steps.  Three candidate semantics exist:

* **refine** (relational): one store for the whole form; a repeated name is
  an equality constraint; a ground conflict fails.
* **shadow** (lexical): each step rebinds; a repeated name silently
  replaces the earlier binding.
* **observed refine**: the ordinary refine result, accompanied when requested
  by a conflict witness `(name, old, new)`.  The witness is evidence about a
  failed branch, not a different evaluator result or an exception.

This module proves the theorems that decide among them, over ground stores.
The ground fragment already separates the candidate designs.  Extending the
result to non-ground terms requires a separately formalized substitution
lattice and residuated equality; this module does not claim that extension.

The laws:

* `refineRun_mono` / `futureCone_preserves_binding` — **the cone law**:
  refinement only grows
  the store along the information order, and a binding made by an earlier
  fragment is seen unchanged by every later-composed fragment ("compose
  new code in, and `$x` is what it already was").
* `shadowStep_not_information_mono` — shadowing rewrites the observable past.
* `refineRun_empty_eq_solveConj` — **compositionality**: sequential
  refinement from the empty store equals solving the steps as one
  simultaneous conjunction.  Therefore any design requiring sequencing to
  present conjunction must retain the within-pattern equality meaning across
  patterns.  `shadow_breaks_conj` exhibits the disagreement of shadowing with
  that law.
* `solveConj_perm` — the refine meaning is order-independent (bag-level,
  as specifications require); `shadow_order_sensitive` shows shadowing is
  essentially order-dependent.
* `observeRun_outcome_eq` / `observeRun_conflict_spec` — optional conflict
  observation projects to exactly the ordinary refine result and carries a
  genuine witness with `old ≠ new`.  Observation policy does not alter the
  answer semantics.
* `rename_store_name_breaks` — for store names, spelling **is** identity:
  renaming can destroy solvability.  Lambda binders, alpha-quotiented in
  an ABT, have no analogous phenomenon: their spellings are presentation.
  This is the two-sorted principle — `$`-names are store names (semantic,
  single-assignment, monotone); λ-binders are alpha-classes (shadowing
  harmless because spelling is meaningless there).
-/

namespace Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline

variable {N V : Type*}

/-- A ground binding store. -/
abbrev Store (N V : Type*) := N → Option V

/-- Information order on stores: everything the smaller store knows, the
larger knows identically. -/
def Store.LE (s s' : Store N V) : Prop :=
  ∀ n v, s n = some v → s' n = some v

@[inherit_doc] scoped infix:50 " ⊑ " => Store.LE

theorem Store.LE.refl (s : Store N V) : s ⊑ s := fun _ _ h => h

theorem Store.LE.trans {a b c : Store N V} (hab : a ⊑ b) (hbc : b ⊑ c) :
    a ⊑ c := fun n v h => hbc n v (hab n v h)

/-- The empty store. -/
def Store.empty : Store N V := fun _ => none

/-- Ground binding steps: this name takes this value. -/
abbrev Steps (N V : Type*) := List (N × V)

variable [DecidableEq N] [DecidableEq V]

/-! ## The refine semantics -/

/-- One refinement step: bind if unbound; accept a repeated binding of the
same value; fail on a ground conflict. -/
def refineStep (s : Store N V) (p : N × V) : Option (Store N V) :=
  match s p.1 with
  | none => some (fun n => if n = p.1 then some p.2 else s n)
  | some w => if w = p.2 then some s else none

/-- Sequential refinement over a step list. -/
def refineRun (s : Store N V) : Steps N V → Option (Store N V)
  | [] => some s
  | p :: rest =>
    match refineStep s p with
    | none => none
    | some s' => refineRun s' rest

theorem refineStep_mono {s s' : Store N V} {p : N × V}
    (h : refineStep s p = some s') : s ⊑ s' := by
  unfold refineStep at h
  cases hs : s p.1 with
  | none =>
    rw [hs] at h
    injection h with h
    subst h
    intro n v hn
    by_cases hne : n = p.1
    · rw [hne] at hn
      rw [hn] at hs
      cases hs
    · simp [hne, hn]
  | some w =>
    rw [hs] at h
    by_cases hw : w = p.2
    · simp only [hw] at h
      injection h with h
      subst h
      exact fun _ _ hn => hn
    · simp [hw] at h

/-- A successful step establishes its own assertion. -/
theorem refineStep_binds {s s' : Store N V} {p : N × V}
    (h : refineStep s p = some s') : s' p.1 = some p.2 := by
  unfold refineStep at h
  cases hs : s p.1 with
  | none =>
    rw [hs] at h
    injection h with h
    subst h
    simp
  | some w =>
    rw [hs] at h
    by_cases hw : w = p.2
    · simp only [hw] at h
      injection h with h
      subst h
      rw [hs, hw]
    · simp [hw] at h

/-- **The cone law, pointwise**: refinement only grows the store. -/
theorem refineRun_mono {s t : Store N V} {steps : Steps N V}
    (h : refineRun s steps = some t) : s ⊑ t := by
  induction steps generalizing s with
  | nil =>
    unfold refineRun at h
    injection h with h
    subst h
    exact Store.LE.refl s
  | cons p rest ih =>
    unfold refineRun at h
    cases hstep : refineStep s p with
    | none => rw [hstep] at h; cases h
    | some s' =>
      rw [hstep] at h
      exact (refineStep_mono hstep).trans (ih h)

/-! ## Refinement as a causal/lightcone relation -/

/-- A successful single refinement is one causal production step on stores. -/
def RefinesOne (s t : Store N V) : Prop :=
  ∃ p : N × V, refineStep s p = some t

/-- Every causal refinement step preserves all information already known. -/
theorem refinesOne_mono {s t : Store N V} (h : RefinesOne s t) : s ⊑ t := by
  obtain ⟨p, hp⟩ := h
  exact refineStep_mono hp

/-- Every finite path in the refinement relation preserves prior bindings. -/
theorem reaches_refines_mono {s t : Store N V}
    (h : Mettapedia.Machines.Reaches RefinesOne s t) : s ⊑ t := by
  induction h with
  | refl => exact Store.LE.refl s
  | tail _ hstep ih => exact ih.trans (refinesOne_mono hstep)

/-- **Forward-lightcone persistence**: once a store knows `n = v`, every
store in its refinement future knows the same fact. -/
theorem futureCone_preserves_binding {s t : Store N V} {n : N} {v : V}
    (ht : t ∈ Mettapedia.Machines.forwardCone RefinesOne ({s} : Set (Store N V)))
    (hbound : s n = some v) : t n = some v := by
  obtain ⟨s₀, hs₀, hreach⟩ := ht
  simp only [Set.mem_singleton_iff] at hs₀
  subst s₀
  exact reaches_refines_mono hreach n v hbound

/-- The dual reading: a possible refinement-past is information-compatible
with the demanded future store. -/
theorem backwardCone_past_le_future {s t : Store N V}
    (hs : s ∈ Mettapedia.Machines.backwardCone RefinesOne ({t} : Set (Store N V))) :
    s ⊑ t := by
  obtain ⟨t₀, ht₀, hreach⟩ := hs
  simp only [Set.mem_singleton_iff] at ht₀
  subst t₀
  exact reaches_refines_mono hreach

/-- A successful run establishes every assertion of its step list. -/
theorem refineRun_asserts {s t : Store N V} {steps : Steps N V}
    (h : refineRun s steps = some t) :
    ∀ p ∈ steps, t p.1 = some p.2 := by
  induction steps generalizing s with
  | nil => intro p hp; cases hp
  | cons q rest ih =>
    unfold refineRun at h
    cases hstep : refineStep s q with
    | none => rw [hstep] at h; cases h
    | some s' =>
      rw [hstep] at h
      intro p hp
      rcases List.mem_cons.mp hp with hq | hrest
      · subst hq
        exact refineRun_mono h p.1 p.2 (refineStep_binds hstep)
      · exact ih h p hrest

theorem refineRun_nil (s : Store N V) : refineRun s [] = some s := rfl

theorem refineRun_cons (s : Store N V) (p : N × V) (rest : Steps N V) :
    refineRun s (p :: rest) =
      match refineStep s p with
      | none => none
      | some s' => refineRun s' rest := rfl

/-- Sequential composition factors through the intermediate store. -/
theorem refineRun_append (s : Store N V) (l₁ l₂ : Steps N V) :
    refineRun s (l₁ ++ l₂) =
      match refineRun s l₁ with
      | none => none
      | some t => refineRun t l₂ := by
  induction l₁ generalizing s with
  | nil => simp [refineRun_nil]
  | cons p rest ih =>
    rw [List.cons_append, refineRun_cons, refineRun_cons]
    cases hstep : refineStep s p with
    | none => rfl
    | some s' => exact ih s'

/-- **Append persistence**: whatever an earlier fragment bound is
seen unchanged by every later-composed fragment. -/
theorem refineRun_append_preserves_prior_binding
    {s t u : Store N V} {l₁ l₂ : Steps N V} {n : N} {v : V}
    (h₁ : refineRun s l₁ = some t) (hbound : t n = some v)
    (h₂ : refineRun s (l₁ ++ l₂) = some u) : u n = some v := by
  rw [refineRun_append, h₁] at h₂
  exact refineRun_mono h₂ n v hbound

/-! ## The shadow semantics, and how it breaks the laws -/

/-- One right-biased lexical overwrite step. -/
def shadowStep (s : Store N V) (p : N × V) : Store N V :=
  fun n => if n = p.1 then some p.2 else s n

/-- Lexical rebinding: every step overwrites. -/
def shadowRun (s : Store N V) : Steps N V → Store N V
  | [] => s
  | p :: rest => shadowRun (shadowStep s p) rest

/-- Shadowing is not monotone in the store information order. -/
theorem shadowStep_not_information_mono :
    ¬ Store.LE
        (shadowStep (Store.empty : Store String String) ("x", "a"))
        (shadowStep
          (shadowStep (Store.empty : Store String String) ("x", "a"))
          ("x", "b")) := by
  intro h
  have hbad := h "x" "a" (by simp [shadowStep])
  simp [shadowStep] at hbad

/-- Shadowing rewrites the observable past: after `x := a` then `x := b`,
composed code sees `b` where the cone law demands `a` (or a failure). -/
theorem shadow_breaks_cone :
    shadowRun (Store.empty : Store String String)
      [("x", "a"), ("x", "b")] "x" = some "b" := by
  rfl

/-- The same two steps under refine: honest ground-conflict failure. -/
theorem refine_rejects_conflict :
    refineRun (Store.empty : Store String String)
      [("x", "a"), ("x", "b")] = none := by
  rfl

/-- At most one ground store is produced here; `none` denotes the empty
answer bag. -/
def answerBag {α : Type*} : Option α → List α
  | none => []
  | some a => [a]

theorem refine_conflict_has_empty_answer_bag :
    answerBag
      (refineRun (Store.empty : Store String String)
        [("x", "a"), ("x", "b")]) = [] := by
  rfl

/-- Positive control: a consistent repeat is accepted and refines to the
shared value. -/
theorem refine_accepts_repeat :
    (refineRun (Store.empty : Store String String)
      [("x", "a"), ("x", "a")]).map (fun s => s "x") =
      some (some "a") := by
  rfl

/-! ## Compositionality: sequencing is a presentation of conjunction -/

/-- The simultaneous reading: consistent iff no name is asserted at two
distinct values. -/
def Consistent (steps : Steps N V) : Prop :=
  ∀ p ∈ steps, ∀ q ∈ steps, p.1 = q.1 → p.2 = q.2

instance (steps : Steps N V) : Decidable (Consistent steps) := by
  unfold Consistent
  infer_instance

/-- Canonical solution of a conjunction: the first asserted value per name
(under consistency, the only asserted value). -/
def lookupFirst (steps : Steps N V) (n : N) : Option V :=
  (steps.find? (fun p => p.1 = n)).map (·.2)

/-- The conjunction semantics of a step list. -/
def solveConj (steps : Steps N V) : Option (Store N V) :=
  if Consistent steps then some (lookupFirst steps) else none

omit [DecidableEq V] in
theorem lookupFirst_nil (n : N) :
    lookupFirst ([] : Steps N V) n = none := rfl

omit [DecidableEq V] in
theorem lookupFirst_cons (p : N × V) (rest : Steps N V) (n : N) :
    lookupFirst (p :: rest) n =
      if p.1 = n then some p.2 else lookupFirst rest n := by
  unfold lookupFirst
  by_cases h : p.1 = n
  · simp [List.find?, h]
  · simp [List.find?, h]

omit [DecidableEq N] [DecidableEq V] in
theorem Consistent.tail {p : N × V} {rest : Steps N V}
    (hc : Consistent (p :: rest)) : Consistent rest := fun a ha b hb hab =>
  hc a (List.mem_cons_of_mem p ha) b (List.mem_cons_of_mem p hb) hab

omit [DecidableEq V] in
/-- Under consistency, `lookupFirst` returns exactly the asserted
values. -/
theorem lookupFirst_eq_some_iff {steps : Steps N V} :
    Consistent steps → ∀ {n : N} {v : V},
      (lookupFirst steps n = some v ↔ (n, v) ∈ steps) := by
  induction steps with
  | nil =>
    intro _ n v
    simp [lookupFirst_nil]
  | cons p rest ih =>
    intro hc n v
    rw [lookupFirst_cons]
    by_cases hpn : p.1 = n
    · rw [if_pos hpn]
      constructor
      · intro h
        injection h with h
        exact List.mem_cons.mpr (Or.inl (Prod.ext hpn.symm h.symm))
      · intro hmem
        rcases List.mem_cons.mp hmem with hh | ht
        · rw [← hh]
        · have hval := hc p (List.mem_cons_self) (n, v)
            (List.mem_cons_of_mem p ht) hpn
          simp [hval]
    · rw [if_neg hpn, ih hc.tail]
      constructor
      · exact fun h => List.mem_cons_of_mem p h
      · intro hmem
        rcases List.mem_cons.mp hmem with hh | ht
        · exact absurd (congrArg Prod.fst hh).symm hpn
        · exact ht

/-- A refine run from a compatible store succeeds on a consistent step
list, and its result is characterized pointwise: asserted names take
their asserted values, untouched names keep the incoming store's view. -/
theorem refineRun_of_consistent {steps : Steps N V} (hc : Consistent steps) :
    ∀ (s : Store N V),
      (∀ p ∈ steps, ∀ w, s p.1 = some w → w = p.2) →
      ∃ t, refineRun s steps = some t ∧
        (∀ n v, lookupFirst steps n = some v → t n = some v) ∧
        (∀ n, lookupFirst steps n = none → t n = s n) := by
  induction steps with
  | nil =>
    intro s _
    refine ⟨s, rfl, ?_, fun n _ => rfl⟩
    intro n v h
    rw [lookupFirst_nil] at h
    cases h
  | cons p rest ih =>
    intro s hs
    -- the head step succeeds and is pointwise characterized
    have hstep : ∃ s', refineStep s p = some s' ∧
        (∀ n, s' n = if n = p.1 then some p.2 else s n) := by
      unfold refineStep
      cases hsp : s p.1 with
      | none => exact ⟨_, rfl, fun n => rfl⟩
      | some w =>
        have hw : w = p.2 := hs p (List.mem_cons_self) w hsp
        refine ⟨s, by simp [hw], fun n => ?_⟩
        by_cases hn : n = p.1
        · rw [if_pos hn, hn, hsp, hw]
        · rw [if_neg hn]
    obtain ⟨s', hstepEq, hs'⟩ := hstep
    have hs'ok : ∀ q ∈ rest, ∀ w, s' q.1 = some w → w = q.2 := by
      intro q hq w hw
      rw [hs' q.1] at hw
      by_cases hqp : q.1 = p.1
      · rw [if_pos hqp] at hw
        injection hw with hw
        have hpq : p.2 = q.2 := hc p (List.mem_cons_self) q
          (List.mem_cons_of_mem p hq) hqp.symm
        rw [← hw]
        exact hpq
      · rw [if_neg hqp] at hw
        exact hs q (List.mem_cons_of_mem p hq) w hw
    obtain ⟨t, hrun, hsome, hnone⟩ := ih hc.tail s' hs'ok
    refine ⟨t, ?_, ?_, ?_⟩
    · unfold refineRun
      rw [hstepEq]
      exact hrun
    · intro n v hlook
      rw [lookupFirst_cons] at hlook
      by_cases hpn : p.1 = n
      · rw [if_pos hpn] at hlook
        injection hlook with hlook
        have hbind : s' n = some v := by
          rw [hs' n, if_pos hpn.symm, hlook]
        exact refineRun_mono hrun n v hbind
      · rw [if_neg hpn] at hlook
        exact hsome n v hlook
    · intro n hlook
      rw [lookupFirst_cons] at hlook
      by_cases hpn : p.1 = n
      · rw [if_pos hpn] at hlook
        cases hlook
      · rw [if_neg hpn] at hlook
        rw [hnone n hlook, hs' n, if_neg (fun h => hpn h.symm)]

/-- Refine rejects exactly the inconsistent step lists (from the empty
store). -/
theorem refineRun_none_of_inconsistent {steps : Steps N V}
    (hc : ¬ Consistent steps) :
    refineRun (Store.empty : Store N V) steps = none := by
  cases h : refineRun (Store.empty : Store N V) steps with
  | none => rfl
  | some t =>
    exfalso
    apply hc
    intro p hp q hq hpq
    have h1 := refineRun_asserts h p hp
    have h2 := refineRun_asserts h q hq
    rw [hpq] at h1
    rw [h1] at h2
    injection h2

/-- **Compositionality**: sequential refinement from the empty store *is*
the conjunction semantics.  The meaning of repeated spelling inside one
pattern (equality) extends uniquely to sequences of patterns. -/
theorem refineRun_empty_eq_solveConj (steps : Steps N V) :
    refineRun (Store.empty : Store N V) steps = solveConj steps := by
  unfold solveConj
  by_cases hc : Consistent steps
  · rw [if_pos hc]
    obtain ⟨t, hrun, hsome, hnone⟩ :=
      refineRun_of_consistent hc Store.empty (fun p _ w hw => by cases hw)
    rw [hrun]
    congr 1
    funext n
    cases hl : lookupFirst steps n with
    | none => rw [hnone n hl]; rfl
    | some v => rw [hsome n v hl]
  · rw [if_neg hc]
    exact refineRun_none_of_inconsistent hc

/-- The shadow semantics disagrees with the conjunction reading on the
canonical two-step example: the conjunction fails, shadowing "succeeds". -/
theorem shadow_breaks_conj :
    solveConj ([("x", "a"), ("x", "b")] : Steps String String) = none ∧
    shadowRun Store.empty [("x", "a"), ("x", "b")] "x" = some "b" := by
  constructor
  · rw [← refineRun_empty_eq_solveConj]
    exact refine_rejects_conflict
  · rfl

/-! ## Order-independence -/

omit [DecidableEq N] [DecidableEq V] in
/-- Consistency is invariant under permutation. -/
theorem Consistent.perm {l l' : Steps N V} (hp : l.Perm l')
    (hc : Consistent l) : Consistent l' := fun p hpmem q hqmem hpq =>
  hc p (hp.symm.subset hpmem) q (hp.symm.subset hqmem) hpq

/-- The refine/conjunction meaning is order-independent: permuting the
steps permutes nothing observable. -/
theorem solveConj_perm {l l' : Steps N V} (hp : l.Perm l') :
    solveConj l = solveConj l' := by
  unfold solveConj
  by_cases hc : Consistent l
  · have hc' : Consistent l' := hc.perm hp
    rw [if_pos hc, if_pos hc']
    congr 1
    funext n
    cases hl : lookupFirst l n with
    | some v =>
      have hmem := (lookupFirst_eq_some_iff hc).mp hl
      exact ((lookupFirst_eq_some_iff hc').mpr (hp.subset hmem)).symm
    | none =>
      cases hl' : lookupFirst l' n with
      | none => rfl
      | some v =>
        exfalso
        have hmem := (lookupFirst_eq_some_iff hc').mp hl'
        have := (lookupFirst_eq_some_iff hc).mpr (hp.symm.subset hmem)
        rw [hl] at this
        cases this
  · have hc' : ¬ Consistent l' := fun h => hc (h.perm hp.symm)
    rw [if_neg hc, if_neg hc']

/-- Shadowing is essentially order-dependent: reversing the two steps
changes the observable answer. -/
theorem shadow_order_sensitive :
    shadowRun (Store.empty : Store String String)
        [("x", "a"), ("x", "b")] "x" ≠
      shadowRun (Store.empty : Store String String)
        [("x", "b"), ("x", "a")] "x" := by
  intro h
  have hba : (some "b" : Option String) = some "a" := h
  simp at hba

/-! ## Optional conflict observation -/

/-- An observation of a refinement run.  Its projection back to `Option`
is the ordinary evaluator result. -/
inductive RunObservation (N V : Type*) where
  | ok (s : Store N V)
  | conflict (n : N) (old new : V)

/-- Observe one refinement step. -/
def observeStep (s : Store N V) (p : N × V) : RunObservation N V :=
  match s p.1 with
  | none => .ok (fun n => if n = p.1 then some p.2 else s n)
  | some w => if w = p.2 then .ok s else .conflict p.1 w p.2

/-- Observe a sequential refinement run. -/
def observeRun (s : Store N V) : Steps N V → RunObservation N V
  | [] => .ok s
  | p :: rest =>
    match observeStep s p with
    | .ok s' => observeRun s' rest
    | .conflict n old new => .conflict n old new

theorem observeStep_ok_iff {s s' : Store N V} {p : N × V} :
    observeStep s p = .ok s' ↔ refineStep s p = some s' := by
  unfold observeStep refineStep
  cases hs : s p.1 with
  | none => simp
  | some w =>
    by_cases hw : w = p.2 <;> simp [hw]

theorem observeStep_conflict_iff {s : Store N V} {p : N × V} {n : N}
    {old new : V} :
    observeStep s p = .conflict n old new ↔
      refineStep s p = none ∧ n = p.1 ∧ s p.1 = some old ∧ new = p.2 ∧
        old ≠ new := by
  unfold observeStep refineStep
  cases hs : s p.1 with
  | none => simp
  | some w =>
    by_cases hw : w = p.2
    · simp [hw]
    · simp only [if_neg hw]
      constructor
      · intro h
        injection h with h1 h2 h3
        subst h1
        subst h2
        subst h3
        exact ⟨trivial, rfl, rfl, rfl, hw⟩
      · rintro ⟨-, rfl, hsw, rfl, -⟩
        injection hsw with hsw
        rw [hsw]

/-- Optional observation succeeds on exactly the programs ordinary refine
accepts, with the same store. -/
theorem observeRun_ok_iff {s t : Store N V} {steps : Steps N V} :
    observeRun s steps = .ok t ↔ refineRun s steps = some t := by
  induction steps generalizing s with
  | nil =>
    unfold observeRun refineRun
    constructor
    · intro h; injection h with h; rw [h]
    · intro h; injection h with h; rw [h]
  | cons p rest ih =>
    unfold observeRun refineRun
    cases hl : observeStep s p with
    | ok s' =>
      rw [observeStep_ok_iff.mp hl]
      exact ih
    | conflict n old new =>
      rw [(observeStep_conflict_iff.mp hl).1]
      constructor
      · intro h; cases h
      · intro h; cases h

/-- An observed conflict is a true witness: the run fails, and the witness
records a genuine disagreement. -/
theorem observeRun_conflict_spec {s : Store N V} {steps : Steps N V} {n : N}
    {old new : V} (h : observeRun s steps = .conflict n old new) :
    refineRun s steps = none ∧ old ≠ new := by
  induction steps generalizing s with
  | nil => cases h
  | cons p rest ih =>
    unfold observeRun at h
    cases hl : observeStep s p with
    | ok s' =>
      rw [hl] at h
      obtain ⟨hrun, hne⟩ := ih h
      refine ⟨?_, hne⟩
      unfold refineRun
      rw [observeStep_ok_iff.mp hl]
      exact hrun
    | conflict m o w =>
      rw [hl] at h
      injection h with h1 h2 h3
      subst h1; subst h2; subst h3
      obtain ⟨hnone, -, -, -, hne⟩ := observeStep_conflict_iff.mp hl
      refine ⟨?_, hne⟩
      unfold refineRun
      rw [hnone]

/-- Forgetting the optional conflict details gives exactly the ordinary
refinement outcome. -/
def RunObservation.outcome : RunObservation N V → Option (Store N V)
  | .ok s => some s
  | .conflict _ _ _ => none

theorem observeRun_outcome_eq (s : Store N V) (steps : Steps N V) :
    (observeRun s steps).outcome = refineRun s steps := by
  cases hobs : observeRun s steps with
  | ok t =>
      rw [observeRun_ok_iff.mp hobs]
      rfl
  | conflict n old new =>
      rw [(observeRun_conflict_spec hobs).1]
      rfl

/-! ## Spelling is semantics for store names -/

/-- Renaming a store name can destroy solvability: `[(x,a),(y,b)]` is
consistent; identifying `y` with `x` makes it inconsistent.  Store-name
spelling is semantic identity — unlike lambda binders, whose spellings are
alpha-quotiented presentation with no analogous phenomenon. -/
theorem rename_store_name_breaks :
    Consistent ([("x", "a"), ("y", "b")] : Steps String String) ∧
    ¬ Consistent ([("x", "a"), ("x", "b")] : Steps String String) := by
  constructor
  · decide
  · decide

end Mettapedia.GSLT.LanguageDef.SequentialBindingDiscipline
