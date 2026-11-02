import Mettapedia.Machines.NamesOverStores

/-!
# Canonical admission while routing policies change

A term-keyed catalog remembers the canonical name already published for that
term. Only absent terms consult the current proposal function. A stale catalog
entry is refused, not silently renamed. Relocation that preserves decoding
therefore preserves catalog soundness, and a routing change cannot give an
already cataloged term a second published identity.

The catalog is a logical partial map. Theorems do not supply a constant-time
lookup, hash-collision policy, concurrency linearization, or persistent codec.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CanonicalNameAdmission

variable {Term Name : Type} [DecidableEq Term]

abbrev Catalog (Term Name : Type) := Term → Option Name

abbrev Sound (read : Name → Option Term) (catalog : Catalog Term Name) : Prop :=
  ∀ t n, catalog t = some n → read n = some t

def intern (read : Name → Option Term) (catalog : Catalog Term Name)
    (propose : Term → Name) (t : Term) : Option (Name × Catalog Term Name) :=
  match catalog t with
  | some old => if read old = some t then some (old, catalog) else none
  | none =>
      let fresh := propose t
      if read fresh = some t then some (fresh, Function.update catalog t (some fresh)) else none

theorem existing_name_wins (read : Name → Option Term) (catalog : Catalog Term Name)
    (propose : Term → Name) (t : Term) (old : Name)
    (known : catalog t = some old) (valid : read old = some t) :
    intern read catalog propose t = some (old, catalog) := by
  simp [intern, known, valid]

theorem stale_entry_refused (read : Name → Option Term) (catalog : Catalog Term Name)
    (propose : Term → Name) (t : Term) (old : Name)
    (known : catalog t = some old) (stale : read old ≠ some t) :
    intern read catalog propose t = none := by
  simp [intern, known, stale]

theorem intern_records (read : Name → Option Term) (catalog : Catalog Term Name)
    (propose : Term → Name) (t : Term) (n : Name) (next : Catalog Term Name)
    (accepted : intern read catalog propose t = some (n, next)) :
    next t = some n ∧ read n = some t := by
  unfold intern at accepted
  split at accepted
  · rename_i old found
    split at accepted <;> try contradiction
    cases accepted
    exact ⟨found, by assumption⟩
  · dsimp only at accepted
    split at accepted <;> try contradiction
    cases accepted
    exact ⟨Function.update_self _ _ _, by assumption⟩

theorem intern_sound (read : Name → Option Term) (catalog : Catalog Term Name)
    (propose : Term → Name) (t : Term) (n : Name) (next : Catalog Term Name)
    (sound : Sound read catalog)
    (accepted : intern read catalog propose t = some (n, next)) : Sound read next := by
  unfold intern at accepted
  split at accepted
  · split at accepted <;> try contradiction
    cases accepted
    exact sound
  · dsimp only at accepted
    split at accepted <;> try contradiction
    rename_i valid
    cases accepted
    intro query address found
    by_cases same : query = t
    · subst query
      simp only [Function.update_self, Option.some.injEq] at found
      subst address
      exact valid
    · rw [Function.update_of_ne same] at found
      exact sound query address found

theorem intern_preserves_existing (read : Name → Option Term) (catalog : Catalog Term Name)
    (propose : Term → Name) (t : Term) (n : Name) (next : Catalog Term Name)
    (accepted : intern read catalog propose t = some (n, next))
    (query : Term) (old : Name) (known : catalog query = some old) : next query = some old := by
  unfold intern at accepted
  split at accepted
  · split at accepted <;> try contradiction
    cases accepted
    exact known
  · rename_i absent
    dsimp only at accepted
    split at accepted <;> try contradiction
    cases accepted
    have different : query ≠ t := by intro same; subst query; rw [absent] at known; contradiction
    rw [Function.update_of_ne different]
    exact known

/-- Retry under any later proposal policy returns exactly the published name. -/
theorem intern_retry (read : Name → Option Term) (catalog : Catalog Term Name)
    (first later : Term → Name) (t : Term) (n : Name) (next : Catalog Term Name)
    (accepted : intern read catalog first t = some (n, next)) :
    intern read next later t = some (n, next) := by
  obtain ⟨known, valid⟩ := intern_records read catalog first t n next accepted
  exact existing_name_wins read next later t n known valid

omit [DecidableEq Term] in
theorem names_reflect_terms (read : Name → Option Term) (catalog : Catalog Term Name)
    (sound : Sound read catalog) (x y : Term) (n : Name)
    (hx : catalog x = some n) (hy : catalog y = some n) : x = y :=
  Option.some.inj ((sound x n hx).symm.trans (sound y n hy))

omit [DecidableEq Term] in
theorem terms_have_one_catalog_name (catalog : Catalog Term Name) (t : Term) (a b : Name)
    (ha : catalog t = some a) (hb : catalog t = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

omit [DecidableEq Term] in
theorem sound_after_relocation (before after : Name → Option Term) (catalog : Catalog Term Name)
    (same : ∀ n, before n = after n) (sound : Sound before catalog) : Sound after catalog := by
  intro t n known
  rw [← same n]
  exact sound t n known

namespace Controls

def read (_ : Bool) : Option Nat := some 7
def catalog : Catalog Nat Bool := fun t => if t = 7 then some false else none

/-- Both stores can decode 7; changed routing still reuses its old name. -/
example : intern read catalog (fun _ => true) 7 = some (false, catalog) := by
  exact existing_name_wins read catalog _ 7 false (by decide) rfl

example : intern (fun n : Bool => if n then some 7 else none) catalog (fun _ => true) 7 = none := by
  exact stale_entry_refused _ catalog _ 7 false (by decide) (by decide)

/-- An unsound catalog can collapse different terms to one identity. -/
theorem omitted_decode_check_collapses_terms :
    ¬ Sound (fun _ : Unit => some (0 : Nat)) (fun _ => some ()) := by
  intro valid
  have impossible := valid 1 () rfl
  cases impossible

end Controls

#print axioms intern_sound
#print axioms intern_preserves_existing
#print axioms intern_retry
#print axioms names_reflect_terms

end Mettapedia.Machines.CanonicalNameAdmission
