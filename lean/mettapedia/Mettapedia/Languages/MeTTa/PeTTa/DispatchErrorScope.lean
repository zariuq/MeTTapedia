import Mathlib.Data.Multiset.Filter

/-!
# Dispatch error scope: branch-local recovery

A runtime dispatch runs a callee chosen at run time: `reduce`, an application
whose head is a variable or an expression, the element calls of `map-atom`,
`filter-atom` and `foldl-atom`, and the `foldall` and `forall` aggregators.
SWI-PeTTa runs each under `catch(call(Goal), _, fail)`.  When one path of the
dispatched body raises, the catch discards the body's remaining alternatives,
so which answers survive depends on the order in which the alternatives are
explored (`cutoff_order_dependent`).

PeTTa on CeTTa recovers branch-locally: the path that raises fails, and every
other alternative remains, with the answers already given.  On occurrence
bags this handler distributes over choice (`recover_add`), so no exploration
order changes its bag (`recoverList_perm`).  It agrees with SWI-PeTTa's cutoff
on a body that raises nothing (`cutoff_eq_recoverList_of_no_raise`), and a
handler may be dropped exactly where the body raises nothing
(`recoverList_map_answer_of_no_raise`, `recoverList_ne_of_raise`).  Nested
handlers are one handler (`recover_recover`).

Argument evaluation lies outside the handler, so an error there propagates
(`dispatch_argument_error`).  An `(Error …)` value that a path returns is an
answer, not a raise, and recovery keeps it with its multiplicity
(`recover_answer_cons`).
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.DispatchErrorScope

/-- One explored path of a dispatched body: it gives an answer, or it raises. -/
inductive Path (α ε : Type*) where
  | answer : α → Path α ε
  | raise : ε → Path α ε

variable {α β ε : Type*}

/-- The answer a path gives, if it gives one. -/
def Path.answer? : Path α ε → Option α
  | .answer a => some a
  | .raise _ => none

/-- Whether a path raised. -/
def Path.raised : Path α ε → Bool
  | .answer _ => false
  | .raise _ => true

/-- Branch-local recovery over one exploration order: each raising path
fails, and every other path keeps its answer. -/
def recoverList (paths : List (Path α ε)) : List α :=
  paths.filterMap Path.answer?

/-- Branch-local recovery over the occurrence bag of a body's paths. -/
def recover (paths : Multiset (Path α ε)) : Multiset α :=
  paths.filterMap Path.answer?

/-- The bag of an exploration's recovered answers is the recovery of its bag
of paths. -/
theorem recover_coe (paths : List (Path α ε)) :
    recover (paths : Multiset (Path α ε)) = (recoverList paths : Multiset α) :=
  Multiset.filterMap_coe _ _

/-- Choice is the sum of occurrence bags, and recovery distributes over it:
`handle(P ∪ Q) = handle(P) ∪ handle(Q)`. -/
theorem recover_add (p q : Multiset (Path α ε)) :
    recover (p + q) = recover p + recover q :=
  Multiset.filterMap_add _ _ _

theorem recover_zero : recover (0 : Multiset (Path α ε)) = 0 :=
  Multiset.filterMap_zero _

/-- An answer, an `(Error …)` value included, is kept with its multiplicity. -/
theorem recover_answer_cons (a : α) (p : Multiset (Path α ε)) :
    recover (Path.answer a ::ₘ p) = a ::ₘ recover p :=
  Multiset.filterMap_cons_some _ _ _ rfl

/-- A raising path contributes nothing, and removes nothing else. -/
theorem recover_raise_cons (e : ε) (p : Multiset (Path α ε)) :
    recover (Path.raise e ::ₘ p) = recover p :=
  Multiset.filterMap_cons_none _ _ rfl

/-- No exploration order changes the recovered bag. -/
theorem recoverList_perm {l₁ l₂ : List (Path α ε)} (h : l₁.Perm l₂) :
    (recoverList l₁).Perm (recoverList l₂) :=
  h.filterMap _

/-- A handler around a handled body changes nothing: nested handlers are one
handler. -/
theorem recover_recover (p : Multiset (Path α ε)) :
    recover ((recover p).map (Path.answer (ε := ε))) = recover p := by
  rw [recover, Multiset.filterMap_map]
  exact Multiset.filterMap_eq_map id ▸ Multiset.map_id (recover p)

/-- SWI-PeTTa's catch: once a path raises, the alternatives explored after it
are discarded. -/
def cutoff : List (Path α ε) → List α
  | [] => []
  | .answer a :: rest => a :: cutoff rest
  | .raise _ :: _ => []

/-- The cutoff's answers depend on the exploration order. -/
theorem cutoff_order_dependent (a : α) (e : ε) :
    cutoff [Path.raise e, Path.answer a] = [] ∧
    cutoff [Path.answer a, Path.raise e] = [a] :=
  ⟨rfl, rfl⟩

/-- The three orders of one raising path among the answers 1 and 2: the
cutoff gives three bags, branch-local recovery gives one. -/
example (e : ε) :
    cutoff [Path.raise e, .answer 1, .answer 2] = ([] : List Nat) ∧
    cutoff [.answer 1, Path.raise e, .answer 2] = ([1] : List Nat) ∧
    cutoff [.answer 1, .answer 2, Path.raise e] = ([1, 2] : List Nat) ∧
    recoverList [Path.raise e, .answer 1, .answer 2] = ([1, 2] : List Nat) ∧
    recoverList [.answer 1, Path.raise e, .answer 2] = ([1, 2] : List Nat) ∧
    recoverList [.answer 1, .answer 2, Path.raise e] = ([1, 2] : List Nat) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- On a body that raises nothing, SWI-PeTTa's cutoff and branch-local
recovery give the same answers in the same order. -/
theorem cutoff_eq_recoverList_of_no_raise :
    ∀ paths : List (Path α ε), (∀ p ∈ paths, p.raised = false) →
      cutoff paths = recoverList paths
  | [], _ => rfl
  | .answer a :: rest, h => by
      have hrest : ∀ p ∈ rest, p.raised = false :=
        fun p hp => h p (List.mem_cons_of_mem _ hp)
      show a :: cutoff rest = a :: recoverList rest
      rw [cutoff_eq_recoverList_of_no_raise rest hrest]
  | .raise _ :: _, h => Bool.noConfusion (h _ List.mem_cons_self : true = false)

/-- Dropping the handler of a body that raises nothing keeps every path:
the recovered answers are the paths themselves. -/
theorem recoverList_map_answer_of_no_raise :
    ∀ paths : List (Path α ε), (∀ p ∈ paths, p.raised = false) →
      (recoverList paths).map Path.answer = paths
  | [], _ => rfl
  | .answer a :: rest, h => by
      have hrest : ∀ p ∈ rest, p.raised = false :=
        fun p hp => h p (List.mem_cons_of_mem _ hp)
      show Path.answer a :: (recoverList rest).map Path.answer =
        Path.answer a :: rest
      rw [recoverList_map_answer_of_no_raise rest hrest]
  | .raise _ :: _, h => Bool.noConfusion (h _ List.mem_cons_self : true = false)

/-- Where a path raises, the handler is observable: the recovered answers
are fewer than the paths, so a handler may be dropped only where the body
provably raises nothing. -/
theorem recoverList_length_lt_of_raise :
    ∀ paths : List (Path α ε), (∃ p ∈ paths, p.raised = true) →
      (recoverList paths).length < paths.length
  | [], ⟨_, hp, _⟩ => absurd hp List.not_mem_nil
  | .raise _ :: rest, _ => by
      show (recoverList rest).length < rest.length + 1
      exact Nat.lt_succ_of_le (List.length_filterMap_le _ _)
  | .answer a :: rest, ⟨p, hp, hr⟩ => by
      have hrest : ∃ p ∈ rest, p.raised = true := by
        rcases List.mem_cons.mp hp with h | h
        · subst h; exact Bool.noConfusion (hr : false = true)
        · exact ⟨p, h, hr⟩
      show (recoverList rest).length + 1 < rest.length + 1
      exact Nat.succ_lt_succ (recoverList_length_lt_of_raise rest hrest)

/-- So a raising body's recovered answers, as paths, differ from its paths. -/
theorem recoverList_ne_of_raise (paths : List (Path α ε))
    (h : ∃ p ∈ paths, p.raised = true) :
    (recoverList paths).map Path.answer ≠ paths := by
  intro heq
  have hlen := congrArg List.length heq
  rw [List.length_map] at hlen
  exact Nat.lt_irrefl _ (hlen ▸ recoverList_length_lt_of_raise paths h)

/-- A covered dispatch: the argument is evaluated outside the handler, so an
error there propagates; only the dispatched body is recovered. -/
def dispatch (argument : Path α ε) (body : α → Multiset (Path β ε)) :
    Except ε (Multiset β) :=
  match argument with
  | .raise e => .error e
  | .answer a => .ok (recover (body a))

theorem dispatch_argument_error (e : ε) (body : α → Multiset (Path β ε)) :
    dispatch (.raise e) body = .error e :=
  rfl

theorem dispatch_answer (a : α) (body : α → Multiset (Path β ε)) :
    dispatch (.answer a) body = .ok (recover (body a)) :=
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.DispatchErrorScope
