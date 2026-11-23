import Mathlib.Tactic

/-!
# The model controls: the menu's choices, the background refresh, the switch

The operator's model menu and the agent's model skills read only local state:
each provider catalog last observed (a record with the time it was observed,
the time it was last attempted, and its value) and the selected model.

* **Choices.** The menu offers the catalog ids, then the selected model when no
  catalog lists it, each once.
* **Refresh.** A record is *due* when it is stale (never observed, or observed
  at least its time to live ago) and its last attempt is at least the retry
  interval old. A control that finds a record due stamps the attempt first and
  then starts one background child, which reads the provider and writes the
  record back.
* **Writes.** The observations live in one file, written whole. Each writer
  reads the file, changes its own kind's record, and writes the file back, as
  one step under the file's lock.
* **Switch.** A switch is validated, then written to the state file; the model
  changes only when the write landed.

Invariants proved here:
* the choices hold no repeat, and always hold the selected model and every
  catalog id;
* after a control started a child, no control starts another before the retry
  interval has passed, however often the menu is opened;
* two locked writes of different kinds both land, in either order;
* a switch changes the selected model exactly when the name is valid and its
  write landed, and a refused or unwritten switch changes nothing.

The counterexample is the unlocked write: two children that read the file
before either writes it lose the first one's record.

This is an abstract contract, not a refinement proof of
`src/model_menu_cetta.metta`.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.ModelObservations

/-! ## Choices -/

/-- `items`, then each of `extra` not already there, in order. -/
def addNew {α : Type} [DecidableEq α] : List α → List α → List α
  | items, [] => items
  | items, x :: rest => addNew (if x ∈ items then items else items ++ [x]) rest

theorem addNew_nodup {α : Type} [DecidableEq α] (items extra : List α) (h : items.Nodup) :
    (addNew items extra).Nodup := by
  induction extra generalizing items with
  | nil => simpa [addNew] using h
  | cons x rest ih =>
    simp only [addNew]
    apply ih
    split_ifs with hx
    · exact h
    · refine List.nodup_append.mpr ⟨h, List.nodup_singleton x, ?_⟩
      simp only [List.mem_singleton]
      intro a ha b hb hab
      subst hb
      subst hab
      exact hx ha

theorem mem_addNew {α : Type} [DecidableEq α] (items extra : List α) (y : α) :
    y ∈ addNew items extra ↔ y ∈ items ∨ y ∈ extra := by
  induction extra generalizing items with
  | nil => simp [addNew]
  | cons x rest ih =>
    simp only [addNew]
    rw [ih]
    split_ifs with hx
    · constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem x h)
      · rintro (h | h)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl hx
          · exact Or.inr h
    · simp [List.mem_append, or_assoc]

/-- The menu's choices: the catalogs' ids, then the selected model. -/
def choices {α : Type} [DecidableEq α] (catalog : List α) (selected : α) : List α :=
  addNew (addNew [] catalog) [selected]

theorem choices_nodup {α : Type} [DecidableEq α] (catalog : List α) (selected : α) :
    (choices catalog selected).Nodup :=
  addNew_nodup _ _ (addNew_nodup _ _ List.nodup_nil)

theorem selected_offered {α : Type} [DecidableEq α] (catalog : List α) (selected : α) :
    selected ∈ choices catalog selected := by
  simp [choices, mem_addNew]

theorem catalog_offered {α : Type} [DecidableEq α] (catalog : List α) (selected : α) (x : α)
    (h : x ∈ catalog) : x ∈ choices catalog selected := by
  simp [choices, mem_addNew, h]

/-! ## Refresh -/

/-- A catalog's record: when it was observed and attempted (0 for never). -/
structure Record where
  observed : ℕ
  attempted : ℕ
  deriving DecidableEq

/-- Stale, and not attempted within the retry interval. -/
def due (ttl retry now : ℕ) (r : Record) : Prop :=
  (r.observed = 0 ∨ r.observed + ttl ≤ now) ∧ (r.attempted = 0 ∨ r.attempted + retry ≤ now)

instance (ttl retry now : ℕ) (r : Record) : Decidable (due ttl retry now r) := by
  unfold due; infer_instance

/-- A control at time `now`: the record after it, and whether it started a
child. The attempt is stamped before the child starts. -/
def control (ttl retry now : ℕ) (r : Record) : Record × Bool :=
  if due ttl retry now r then ({ r with attempted := now }, true) else (r, false)

/-- A child's record: the read lands, or its failure is noted. -/
def child (now : ℕ) (r : Record) (landed : Bool) : Record :=
  if landed then ⟨now, now⟩ else { r with attempted := now }

/-- Controls at times `times`, in order, none of them a child's write. -/
def controls (ttl retry : ℕ) : Record → List ℕ → Record × ℕ
  | r, [] => (r, 0)
  | r, t :: ts =>
    let step := control ttl retry t r
    let rest := controls ttl retry step.1 ts
    (rest.1, rest.2 + if step.2 then 1 else 0)

/-- After a control at `start > 0` started a child, any number of controls
before `start + retry` start no other. -/
theorem one_child_per_interval (ttl retry start : ℕ) (r : Record) (hstart : 0 < start)
    (hstarted : (control ttl retry start r).2 = true) (times : List ℕ)
    (htimes : ∀ t ∈ times, t < start + retry) :
    (controls ttl retry (control ttl retry start r).1 times).2 = 0 := by
  have hstamp : (control ttl retry start r).1.attempted = start := by
    unfold control at hstarted ⊢
    split_ifs at hstarted ⊢ with h
    simp_all
  generalize (control ttl retry start r).1 = r' at hstamp
  induction times generalizing r' with
  | nil => rfl
  | cons t ts ih =>
    have ht : t < start + retry := htimes t (by simp)
    have hnot : ¬ due ttl retry t r' := by
      rintro ⟨-, h | h⟩ <;> omega
    simp only [controls, control, hnot, if_false]
    simpa using ih (fun t' h' => htimes t' (List.mem_cons_of_mem t h')) r' hstamp

/-- A control finds a record it stamped itself not due within the interval. -/
theorem stamped_not_due (ttl retry now later : ℕ) (r : Record) (hnow : 0 < now)
    (hlater : later < now + retry) : ¬ due ttl retry later { r with attempted := now } := by
  rintro ⟨-, h | h⟩ <;> simp at h <;> omega

/-- A child that read its catalog leaves it fresh: no control within its time
to live starts another. -/
theorem landed_fresh (ttl retry now later : ℕ) (r : Record) (hnow : 0 < now)
    (hlater : later < now + ttl) : ¬ due ttl retry later (child now r true) := by
  rintro ⟨h | h, -⟩ <;> simp [child] at h <;> omega

/-! ## Writes -/

/-- The observations file: a record for each kind. -/
abbrev File (κ : Type) := κ → Record

/-- One writer's change: its kind, and what it makes of that kind's record. -/
structure Update (κ : Type) where
  kind : κ
  change : Record → Record

/-- A write from a snapshot: the writer changes its kind's record in what it
read and writes that file back whole. -/
def write {κ : Type} [DecidableEq κ] (snapshot : File κ) (u : Update κ) : File κ :=
  Function.update snapshot u.kind (u.change (snapshot u.kind))

/-- Under the lock the second writer reads what the first wrote. -/
def locked {κ : Type} [DecidableEq κ] (file : File κ) (first second : Update κ) : File κ :=
  write (write file first) second

/-- Without it both read the same file, and the second write replaces the first. -/
def unlocked {κ : Type} [DecidableEq κ] (file : File κ) (first second : Update κ) : File κ :=
  let _ := write file first
  write file second

theorem locked_both_land {κ : Type} [DecidableEq κ] (file : File κ) (first second : Update κ)
    (hdistinct : first.kind ≠ second.kind) :
    locked file first second first.kind = first.change (file first.kind) ∧
    locked file first second second.kind = second.change (file second.kind) := by
  constructor
  · simp [locked, write, Function.update_of_ne hdistinct]
  · simp [locked, write, Function.update_of_ne (Ne.symm hdistinct)]

theorem locked_order_free {κ : Type} [DecidableEq κ] (file : File κ) (first second : Update κ)
    (hdistinct : first.kind ≠ second.kind) :
    locked file first second = locked file second first := by
  funext k
  by_cases h1 : k = first.kind
  · subst h1
    simp [locked, write, Function.update_of_ne hdistinct]
  · by_cases h2 : k = second.kind
    · subst h2
      simp [locked, write, Function.update_of_ne (Ne.symm hdistinct)]
    · simp [locked, write, Function.update_of_ne h1, Function.update_of_ne h2]

/-- Counterexample: the unlocked write loses the first child's catalog. -/
theorem unlocked_loses_a_record :
    ∃ (file : File Bool) (first second : Update Bool), first.kind ≠ second.kind ∧
      unlocked file first second first.kind ≠ first.change (file first.kind) := by
  refine ⟨fun _ => ⟨0, 0⟩, ⟨true, fun _ => ⟨5, 5⟩⟩, ⟨false, fun _ => ⟨7, 7⟩⟩, by decide, ?_⟩
  simp [unlocked, write]

/-! ## The switch -/

/-- A switch to `name`: refused when invalid; otherwise written, and applied
only when the write landed. The state file's choice after it, and whether the
reply says it was set. -/
def switch {μ : Type} (valid : μ → Prop) [DecidablePred valid] (selected name : μ) (landed : Bool) :
    μ × Bool :=
  if valid name then (if landed then (name, true) else (selected, false)) else (selected, false)

theorem switch_applied_iff {μ : Type} (valid : μ → Prop) [DecidablePred valid] (selected name : μ)
    (landed : Bool) :
    (switch valid selected name landed).2 = true ↔ valid name ∧ landed = true := by
  unfold switch
  split_ifs with h <;> cases landed <;> simp_all

theorem switch_reply_matches_file {μ : Type} (valid : μ → Prop) [DecidablePred valid]
    (selected name : μ) (landed : Bool) (hset : (switch valid selected name landed).2 = true) :
    (switch valid selected name landed).1 = name := by
  unfold switch at hset ⊢
  cases landed <;> split_ifs at hset ⊢ <;> simp_all

theorem refused_switch_unchanged {μ : Type} (valid : μ → Prop) [DecidablePred valid]
    (selected name : μ) (landed : Bool) (hrefused : (switch valid selected name landed).2 = false) :
    (switch valid selected name landed).1 = selected := by
  unfold switch at hrefused ⊢
  split_ifs at hrefused ⊢ with h <;> cases landed <;> simp_all

end Mettapedia.Protocols.Agents.ModelObservations
