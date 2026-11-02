import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.ReflectionClosure

/-!
# A proposed repaired interaction profile for the MeTTa calculus

The original symmetric reflective calculus is L. G. Meredith's
*The MeTTa calculus* (F1R3FLY manuscript). Its atomic unifying rendezvous is
an input to this proposal. The manuscript's illustrative identical encodings
of addition, removal and querying are separated here by explicit request
roles and the existing transform's produce, take and read ports.

This module is a client of the existing constraint multiset step, not a
second transition semantics. Values retain their original substitution
action. Roles and physical Spaces are rigid. These are the store-operation
and request laws of a proposed variant; quotation, binding permissions,
recursive reflection and the complete language require their stated bridges.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Repaired

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

universe uT uS uN uO

inductive Operation where
  | insert | erase | read
  deriving DecidableEq, Repr

inductive Role where
  | data
  | party
  | request (operation : Operation)
  | reply (operation : Operation)
  deriving DecidableEq, Repr

abbrev Row (Space : Type uN) (Value : Type uT) := (Role × Space) × Value

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO}

def data (space : N) (value : T) : Row N T := ((.data, space), value)
def request (operation : Operation) (space : N) (value : T) : Row N T := ((.request operation, space), value)
def reply (operation : Operation) (space : N) (value : T) : Row N T := ((.reply operation, space), value)
def party (space : N) (value : T) : Row N T := ((.party, space), value)

/-- One invocation consumes its request. The access mode determines the
ordinary resource ports; it does not change value equality or solving. -/
def operationRule (operation : Operation) (space : N) (pattern : T) : RuleInstance (Row N T) where
  take := request operation space pattern :: (if operation = .erase then [data space pattern] else [])
  read := if operation = .read then [data space pattern] else []
  tell := []
  checks := []
  produce := (if operation = .insert then [data space pattern] else []) ++ [reply operation space pattern]

/-- Explicitly active peers retain Meredith's atomic, symmetric unifying
interaction. Continuation templates and value substitution are declared
inputs; this does not silently impose a dot-substitution convention. -/
def rendezvousRule (space : N) (left right : T) (continuations : List (Row N T)) : RuleInstance (Row N T) where
  take := [party space left, party space right]
  read := []
  tell := [(party space left, party space right)]
  checks := []
  produce := continuations

abbrev action (base : SubstitutionAction T S) : SubstitutionAction (Row N T) S :=
  LocatedSubstitution.action base

variable [DecidableEq O]

theorem rendezvous_uses_one_joint_solution (base : SubstitutionAction T S) (label : O → Row N T)
    (space : N) (left right : T) (continuations : List (Row N T))
    {before : Configuration (Row N T) O} {picked : Selection O}
    (valid : picked.Valid (action base) label (rendezvousRule space left right continuations) before)
    (assignment : S)
    (solved : (action base).Models assignment (picked.problem label (rendezvousRule space left right continuations) before)) :
    base.E (base.apply assignment left) (base.apply assignment right) := by
  have equations := (Selection.models_problem (action base) valid solved).2.2.2
  exact (equations _ (List.mem_singleton_self _)).2

/-- Every admitted built-in store operation consumes an actual request
occurrence. Unification cannot turn a passive data role into that request. -/
theorem request_required (base : SubstitutionAction T S) (label : O → Row N T)
    (operation : Operation) (space : N) (pattern : T)
    {before : Configuration (Row N T) O} {picked : Selection O}
    (valid : picked.Valid (action base) label (operationRule operation space pattern) before) :
    ∃ occurrence ∈ before.present, (label occurrence).1 = (.request operation, space) := by
  have takes := LocatedSubstitution.take_locations base (fun occurrence => (label occurrence).1)
    (fun occurrence => (label occurrence).2) valid
  cases taken : picked.taken with
  | nil =>
      rw [taken] at takes
      cases takes
  | cons occurrence rest =>
      rw [taken] at takes
      have same := (List.forall₂_cons.mp takes).1
      refine ⟨occurrence, valid.occurrences.taken_subset ?_, same.symm⟩
      simp only [Selection.commit, taken, List.mem_toFinset, List.mem_cons, true_or]

/-- An admitted read finds a data occurrence in its declared Space and
retains that same physical occurrence in the result. -/
theorem read_requires_and_keeps_data (base : SubstitutionAction T S) (label : O → Row N T)
    (space : N) (pattern : T) {before : Configuration (Row N T) O} {picked : Selection O}
    (valid : picked.Valid (action base) label (operationRule .read space pattern) before) :
    ∃ occurrence ∈ before.present, (label occurrence).1 = (.data, space) ∧
      occurrence ∈ (picked.result label (operationRule .read space pattern) before).present := by
  have reads := LocatedSubstitution.read_locations base (fun occurrence => (label occurrence).1)
    (fun occurrence => (label occurrence).2) valid
  change List.Forall₂ (fun expected occurrence => expected.1 = (label occurrence).1)
    [data space pattern] picked.read at reads
  cases selected : picked.read with
  | nil => rw [selected] at reads; cases reads
  | cons occurrence rest =>
      rw [selected] at reads
      have same := (List.forall₂_cons.mp reads).1
      have chosen : occurrence ∈ picked.read := by simp [selected]
      exact ⟨occurrence, valid.occurrences.kept_subset (by simpa [Selection.commit] using chosen),
        same.symm, valid.kept_survive chosen⟩

/-- The corresponding destructive operation consumes one actual data
occurrence. Equal values at other identities are not implicitly removed. -/
theorem erase_requires_and_consumes_data (base : SubstitutionAction T S) (label : O → Row N T)
    (space : N) (pattern : T) {before : Configuration (Row N T) O} {picked : Selection O}
    (valid : picked.Valid (action base) label (operationRule .erase space pattern) before) :
    ∃ occurrence ∈ before.present, (label occurrence).1 = (.data, space) ∧
      occurrence ∉ (picked.result label (operationRule .erase space pattern) before).present := by
  have takes := LocatedSubstitution.take_locations base (fun occurrence => (label occurrence).1)
    (fun occurrence => (label occurrence).2) valid
  change List.Forall₂ (fun expected occurrence => expected.1 = (label occurrence).1)
    [request .erase space pattern, data space pattern] picked.taken at takes
  cases selected : picked.taken with
  | nil => rw [selected] at takes; cases takes
  | cons invocation rest =>
      rw [selected] at takes
      have later := (List.forall₂_cons.mp takes).2
      cases tail : rest with
      | nil => rw [tail] at later; cases later
      | cons occurrence others =>
          rw [tail] at later
          have same := (List.forall₂_cons.mp later).1
          have chosen : occurrence ∈ picked.taken := by simp [selected, tail]
          exact ⟨occurrence, valid.occurrences.taken_subset (by simpa [Selection.commit] using chosen),
            same.symm, valid.consumed_removed chosen⟩

/-- An exact open-term admission characterization: a request and a stored
datum must have one common solution with the retained constraints. Neither
one-sided matching nor separate satisfiability of the two equations suffices. -/
theorem read_admission_iff (base : SubstitutionAction T S) (label : O → Row N T)
    (space : N) (pattern requested stored : T) (before : Configuration (Row N T) O)
    (invocation datum response : O)
    (requestLabel : label invocation = request .read space requested)
    (dataLabel : label datum = data space stored)
    (replyLabel : label response = reply .read space pattern) :
    (⟨[invocation], [datum], [response]⟩ : Selection O).Valid
        (action base) label (operationRule .read space pattern) before ↔
      invocation ∈ before.present ∧ datum ∈ before.present ∧ response ∉ before.present ∧
        ∃ assignment, (action base).Models assignment before.equations ∧
          base.E (base.apply assignment pattern) (base.apply assignment requested) ∧
          base.E (base.apply assignment pattern) (base.apply assignment stored) := by
  let picked : Selection O := ⟨[invocation], [datum], [response]⟩
  have apart : invocation ≠ datum := by
    intro same
    have roles := congrArg (fun value : Row N T => value.1.1)
      (requestLabel.symm.trans (same ▸ dataLabel))
    cases roles
  have models (assignment : S) :
      (action base).Models assignment (picked.problem label (operationRule .read space pattern) before) ↔
        (action base).Models assignment before.equations ∧
          base.E (base.apply assignment pattern) (base.apply assignment requested) ∧
          base.E (base.apply assignment pattern) (base.apply assignment stored) := by
    simp [picked, Selection.problem, Selection.equations, operationRule, requestLabel, dataLabel,
      SubstitutionAction.models_append, SubstitutionAction.models_cons, SubstitutionAction.models_nil,
      SubstitutionAction.Solves, action, LocatedSubstitution.action, request, data]
  constructor
  · intro valid
    refine ⟨valid.occurrences.taken_subset (by simp [Selection.commit]),
      valid.occurrences.kept_subset (by simp [Selection.commit]), ?_, ?_⟩
    · intro present
      exact Finset.disjoint_left.mp valid.occurrences.fresh (by simp [Selection.commit]) present
    · obtain ⟨assignment, solved⟩ := valid.consistent
      exact ⟨assignment, (models assignment).mp solved⟩
  · rintro ⟨invoked, storedHere, fresh, assignment, old, requestSolved, dataSolved⟩
    refine ⟨by simp, by simp, rfl, rfl, ?_, ?_, ⟨assignment, ?_⟩, ?_⟩
    · simpa [operationRule] using replyLabel
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa [Selection.commit] using invoked
      · simpa [Selection.commit] using storedHere
      · simpa [Selection.commit] using apart
      · simpa [Selection.commit] using fresh
      · intro query member; cases member
    · exact (models assignment).mpr ⟨old, requestSolved, dataSolved⟩
    · intro check member; cases member

theorem passive_data_do_not_supply_requests (base : SubstitutionAction T S) (label : O → Row N T)
    (operation : Operation) (space : N) (pattern : T) (before : Configuration (Row N T) O)
    (passive : ∀ occurrence ∈ before.present, (label occurrence).1.1 = .data) :
    ¬ ∃ (picked : Selection O), picked.Valid (action base) label (operationRule operation space pattern) before := by
  rintro ⟨picked, valid⟩
  obtain ⟨occurrence, present, same⟩ := request_required base label operation space pattern valid
  have roles := congrArg Prod.fst same
  rw [passive occurrence present] at roles
  cases roles

/-- Requests and replies cannot answer one another as data, even when all
their payloads unify. A read needs a separately present data occurrence. -/
theorem requests_cannot_answer_an_empty_data_store (base : SubstitutionAction T S) (label : O → Row N T)
    (space : N) (pattern : T) (before : Configuration (Row N T) O)
    (noData : ∀ occurrence ∈ before.present, (label occurrence).1.1 ≠ .data) :
    ¬ ∃ (picked : Selection O), picked.Valid (action base) label (operationRule .read space pattern) before := by
  rintro ⟨picked, valid⟩
  obtain ⟨occurrence, present, same, _⟩ := read_requires_and_keeps_data base label space pattern valid
  exact noData occurrence present (congrArg Prod.fst same)

/-- The manuscript's literal stored-fact encoding permits two equal entries
to consume each other by its original symmetric COMM rule. This refutes that
particular passive-store interpretation, not the calculus's ability to use
a richer encoding or an explicitly active rendezvous protocol. -/
theorem literal_fact_pair_consumes_both (channel : Name) (term : Term) :
    ReflectionClosure.Step ReflectionClosure.executableUnifier SC
      (par (pFor term channel pZero) (pFor term channel pZero)) pZero := by
  have unifies : ReflectionClosure.executableUnifier term term [] := unifyPattern_self term
  have root := ReflectionClosure.Step.comm (unifies := ReflectionClosure.executableUnifier) (equivalent := SC)
    term term channel pZero pZero [] unifies
  apply ReflectionClosure.Step.congruence (SC.refl _) root
  simpa [applyDot, dotBindings, Mettapedia.OSLF.MeTTaIL.Match.applyBindings, pZero, par, pPar] using
    (SC.par_nil_right pZero)

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Repaired
