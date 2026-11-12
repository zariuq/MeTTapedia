import Mettapedia.Machines.Kernel.EpochMemory

/-!
# Allocation-incarnation frame leases

This models the bounded lease table's exact-identity detachment operation.
Detachment changes custody metadata; unmapping and translation invalidation
remain separate architectural obligations of the kernel caller.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.FrameLease

inductive Kind where
  | pinned | program | transient
  deriving DecidableEq, Repr

inductive Phase where
  | empty | live | detached | free
  deriving DecidableEq, Repr

structure Identity where
  base : Nat
  holder : Nat
  incarnation : Nat
  order : Nat
  kind : Kind
  deriving DecidableEq, Repr

structure Entry where
  identity : Identity
  pages : Nat
  phase : Phase
  deriving DecidableEq, Repr

def ValidRequest (request : Identity) : Prop :=
  request.base ≠ 0 ∧ request.base % 4096 = 0 ∧ request.holder ≠ 0 ∧
  request.incarnation ≠ 0 ∧ request.order ≤ 18 ∧ request.kind ≠ .pinned

instance (request : Identity) : Decidable (ValidRequest request) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def Matches (request : Identity) (entry : Entry) : Prop :=
  entry.phase = .live ∧ entry.identity = request

instance (request : Identity) (entry : Entry) : Decidable (Matches request entry) :=
  inferInstanceAs (Decidable (_ ∧ _))

def scan (request : Identity) : List Entry → Option (List Entry)
  | [] => none
  | entry :: rest =>
      if Matches request entry then
        some ({ entry with phase := .detached } :: rest)
      else
        (scan request rest).map (entry :: ·)

inductive Status where
  | ok | invalid | denied
  deriving DecidableEq, Repr

def detach (request : Identity) (entries : List Entry) : Status × List Entry :=
  if ValidRequest request then
    match scan request entries with
    | none => (.denied, entries)
    | some next => (.ok, next)
  else (.invalid, entries)

theorem scan_none_iff (request : Identity) (entries : List Entry) :
    scan request entries = none ↔ ∀ entry ∈ entries, ¬ Matches request entry := by
  induction entries with
  | nil => simp [scan]
  | cons entry rest ih =>
      by_cases matching : Matches request entry
      · simp [scan, matching]
      · simp [scan, matching, ih]

theorem scan_success_decomposition {request : Identity} {entries next : List Entry}
    (accepted : scan request entries = some next) :
    ∃ before hit after,
      entries = before ++ hit :: after ∧ Matches request hit ∧
      (∀ entry ∈ before, ¬ Matches request entry) ∧
      next = before ++ { hit with phase := .detached } :: after := by
  induction entries generalizing next with
  | nil => simp [scan] at accepted
  | cons entry rest ih =>
      by_cases matching : Matches request entry
      · simp [scan, matching] at accepted
        subst next
        exact ⟨[], entry, rest, rfl, matching, by simp, rfl⟩
      · simp only [scan, if_neg matching] at accepted
        cases result : scan request rest with
        | none => simp [result] at accepted
        | some tail =>
            simp only [result, Option.map_some, Option.some.injEq] at accepted
            subst next
            obtain ⟨before, hit, after, original, found, skipped, changed⟩ := ih result
            refine ⟨entry :: before, hit, after, ?_, found, ?_, ?_⟩
            · simp [original]
            · simpa using And.intro matching skipped
            · simp [changed]

theorem scan_preserves_length {request : Identity} {entries next : List Entry}
    (accepted : scan request entries = some next) : next.length = entries.length := by
  obtain ⟨before, hit, after, rfl, _, _, rfl⟩ := scan_success_decomposition accepted
  simp

theorem scan_preserves_identities {request : Identity} {entries next : List Entry}
    (accepted : scan request entries = some next) :
    next.map Entry.identity = entries.map Entry.identity := by
  obtain ⟨before, hit, after, rfl, _, _, rfl⟩ := scan_success_decomposition accepted
  simp

theorem scan_preserves_page_extents {request : Identity} {entries next : List Entry}
    (accepted : scan request entries = some next) :
    next.map Entry.pages = entries.map Entry.pages := by
  obtain ⟨before, hit, after, rfl, _, _, rfl⟩ := scan_success_decomposition accepted
  simp

theorem scan_preserves_other_identity {request other : Identity} {entries next : List Entry}
    (different : other ≠ request) (accepted : scan request entries = some next) :
    next.filter (fun entry => entry.identity == other) =
      entries.filter (fun entry => entry.identity == other) := by
  obtain ⟨before, hit, after, rfl, matching, _, rfl⟩ := scan_success_decomposition accepted
  have excluded : hit.identity ≠ other := by
    rw [matching.2]
    exact Ne.symm different
  simp [List.filter_append, excluded]

theorem refusal_preserves_table (request : Identity) (entries : List Entry)
    (refused : (detach request entries).1 ≠ .ok) :
    (detach request entries).2 = entries := by
  unfold detach at *
  split <;> rename_i validity
  · cases result : scan request entries <;> simp_all
  · rfl

theorem stale_incarnation_refused (request : Identity) (entries : List Entry)
    (stale : ∀ entry ∈ entries, entry.identity.incarnation ≠ request.incarnation) :
    (detach request entries).1 ≠ .ok ∧ (detach request entries).2 = entries := by
  have absent : scan request entries = none := (scan_none_iff request entries).2 <| by
    intro entry present matching
    exact stale entry present (congrArg Identity.incarnation matching.2)
  simp only [detach, absent]
  split <;> simp

theorem reused_base_rejects_old_incarnation (request : Identity) (entries : List Entry)
    (reused : ∀ entry ∈ entries, entry.identity.base = request.base →
      entry.identity.incarnation ≠ request.incarnation) :
    (detach request entries).1 ≠ .ok ∧ (detach request entries).2 = entries := by
  have absent : scan request entries = none := (scan_none_iff request entries).2 <| by
    intro entry present matching
    exact reused entry present (congrArg Identity.base matching.2)
      (congrArg Identity.incarnation matching.2)
  simp only [detach, absent]
  split <;> simp

def CallerAuthorized (caller : Nat) (request : Identity) : Prop :=
  caller ≠ 0 ∧ caller = request.holder

instance (caller : Nat) (request : Identity) : Decidable (CallerAuthorized caller request) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem matching_does_not_authenticate (request : Identity) (caller : Nat)
    (wrongCaller : caller ≠ request.holder) : ¬ CallerAuthorized caller request := by
  exact fun authorized => wrongCaller authorized.2

namespace Controls

def old : Identity := ⟨4096, 11, 17, 0, .program⟩
def replacement : Identity := { old with incarnation := 18 }
def unrelated : Identity := ⟨8192, 22, 19, 0, .program⟩
def entries : List Entry := [⟨replacement, 1, .live⟩, ⟨unrelated, 1, .live⟩]

theorem stale_request_is_inert : detach old entries = (.denied, entries) := by decide
theorem current_request_detaches :
    detach replacement entries =
      (.ok, [⟨replacement, 1, .detached⟩, ⟨unrelated, 1, .live⟩]) := by decide
theorem duplicate_detach_refused :
    (detach replacement (detach replacement entries).2).1 = .denied := by decide
theorem wrong_caller_refused : ¬ CallerAuthorized 22 replacement := by decide
theorem owner_authorized : CallerAuthorized 11 replacement := by decide

end Controls

#print axioms scan_success_decomposition
#print axioms scan_preserves_other_identity
#print axioms stale_incarnation_refused

end Mettapedia.Machines.Kernel.FrameLease
