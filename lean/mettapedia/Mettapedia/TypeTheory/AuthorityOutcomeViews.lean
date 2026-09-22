import Mettapedia.TypeTheory.Authority

/-!
# Consumer-relative views of authority outcomes

`Outcome.asBool` gives no Boolean answer for both a fragment boundary and an
incomplete attempt. This view supports public status exactly when those two
cases cannot both occur in the outcome carrier. A consumer that distinguishes
their recovery axes therefore needs more information. Even public status
does not retain distinct incomplete receipts.

These are conditional requirements on specified consumers, not a universal
choice of result semantics. A local presentation can retain the unresolved
payload separately. The indexed version below retains its explicit context;
it does not introduce a global receipt store or classify every context change
as information loss. Positive and negative evidence payloads need not be
inhabited, and no recovery attempt is promised to succeed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.AuthorityOutcomeViews

open AuthorityTheory

universe u v w x y z

variable {Established : Sort u} {Refuted : Sort v}
variable {Boundary : Type w} {Incomplete : Type x} {Observation : Type y}

/-- An observer that distinguishes these two unresolved constructors cannot
be implemented from the Boolean answer alone. -/
theorem consumer_not_factors_asBool
    (consumer : Outcome Established Refuted Boundary Incomplete → Observation)
    (reason : Boundary) (receipt : Incomplete)
    (distinguishes : consumer (.outsideFragment reason) ≠ consumer (.incomplete receipt)) :
    ¬ ∃ decode : Option Bool → Observation, ∀ outcome,
      decode outcome.asBool = consumer outcome := by
  rintro ⟨decode, agrees⟩
  exact distinguishes ((agrees (.outsideFragment reason)).symm.trans
    (agrees (.incomplete receipt)))

/-- The exact carrier-level criterion. It imposes no assumptions on the
positive or negative evidence fibres, which may be empty for a sound fixed
judgment. A restricted actual producer can satisfy a weaker, image-relative
criterion even when its ambient carrier contains both unresolved cases. -/
theorem publicStatus_factors_asBool_iff :
    (∃ decode : Option Bool → Outcome.PublicStatus,
      ∀ outcome : Outcome Established Refuted Boundary Incomplete,
        decode outcome.asBool = outcome.publicStatus) ↔
      ¬ (Nonempty Boundary ∧ Nonempty Incomplete) := by
  constructor
  · intro factors
    rintro ⟨⟨reason⟩, ⟨receipt⟩⟩
    exact consumer_not_factors_asBool Outcome.publicStatus reason receipt
      (by intro same; cases same) factors
  · intro separate
    classical
    by_cases available : Nonempty Boundary
    · refine ⟨fun answer => match answer with
        | some true => .established
        | some false => .refuted
        | none => .undetermined, ?_⟩
      intro outcome
      cases outcome with
      | established _ => rfl
      | refuted _ => rfl
      | outsideFragment _ => rfl
      | incomplete receipt => exact (separate ⟨available, ⟨receipt⟩⟩).elim
    · refine ⟨fun answer => match answer with
        | some true => .established
        | some false => .refuted
        | none => .incomplete, ?_⟩
      intro outcome
      cases outcome with
      | established _ => rfl
      | refuted _ => rfl
      | outsideFragment reason => exact (available ⟨reason⟩).elim
      | incomplete _ => rfl

/-- A specified recovery consumer: reconsider coverage at a boundary, or
resources for an incomplete attempt. This labels the existing refinement
axes; it is neither an automatic scheduler nor a success guarantee. -/
def recoveryAxis : Outcome Established Refuted Boundary Incomplete → Option Outcome.RefinementAxis
  | .established _ | .refuted _ => none
  | .outsideFragment _ => some .authority
  | .incomplete _ => some .budget

def statusRecoveryAxis : Outcome.PublicStatus → Option Outcome.RefinementAxis
  | .established | .refuted => none
  | .undetermined => some .authority
  | .incomplete => some .budget

theorem recoveryAxis_factors_publicStatus
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    statusRecoveryAxis outcome.publicStatus = recoveryAxis outcome := by
  cases outcome <;> rfl

theorem recoveryAxis_not_factors_asBool (reason : Boundary) (receipt : Incomplete) :
    ¬ ∃ decode : Option Bool → Option Outcome.RefinementAxis,
      ∀ outcome : Outcome Established Refuted Boundary Incomplete,
        decode outcome.asBool = recoveryAxis outcome :=
  consumer_not_factors_asBool recoveryAxis reason receipt (by intro same; cases same)

/-- If a no-answer outcome actually reaches a decision by the existing
budget relation, its selected axis was the budget axis. -/
theorem budget_resolution_selects_budget
    {before after : Outcome Established Refuted Boundary Incomplete}
    (unanswered : before.asBool = none) (step : before.BudgetRefines after)
    (decided : after.isDecided = true) : recoveryAxis before = some .budget := by
  cases step <;> simp_all [Outcome.asBool, Outcome.isDecided, recoveryAxis]

/-- The corresponding statement for a successful authority refinement.
These implications do not promise that either relation produces a decision. -/
theorem authority_resolution_selects_authority
    {before after : Outcome Established Refuted Boundary Incomplete}
    (unanswered : before.asBool = none) (step : before.AuthorityRefines after)
    (decided : after.isDecided = true) : recoveryAxis before = some .authority := by
  cases step <;> simp_all [Outcome.asBool, Outcome.isDecided, recoveryAxis]

/-- Receipt observation is finer than status observation. -/
def incompleteReceipt : Outcome Established Refuted Boundary Incomplete → Option Incomplete
  | .incomplete receipt => some receipt
  | _ => none

theorem incompleteReceipt_not_factors_publicStatus (first second : Incomplete)
    (different : first ≠ second) :
    ¬ ∃ decode : Outcome.PublicStatus → Option Incomplete,
      ∀ outcome : Outcome Established Refuted Boundary Incomplete,
        decode outcome.publicStatus = incompleteReceipt outcome := by
  rintro ⟨decode, agrees⟩
  exact different (Option.some.inj ((agrees (.incomplete first)).symm.trans
    (agrees (.incomplete second))))

/-! ## A retained local presentation -/

/-- Retain unresolved payloads while omitting checked polarity evidence. -/
def unresolvedPayload :
    Outcome Established Refuted Boundary Incomplete → Option (Boundary ⊕ Incomplete)
  | .outsideFragment reason => some (.inl reason)
  | .incomplete receipt => some (.inr receipt)
  | _ => none

/-- This view retains the Boolean answer and a separate unresolved record.
It does not retain established/refuted evidence or an execution history. -/
def retainedView (outcome : Outcome Established Refuted Boundary Incomplete) :
    Option Bool × Option (Boundary ⊕ Incomplete) :=
  (outcome.asBool, unresolvedPayload outcome)

def retainedPublicStatus (view : Option Bool × Option (Boundary ⊕ Incomplete)) :
    Outcome.PublicStatus :=
  match view.1, view.2 with
  | some true, _ => .established
  | some false, _ => .refuted
  | none, some (.inr _) => .incomplete
  | none, _ => .undetermined

def retainedIncompleteReceipt (view : Option Bool × Option (Boundary ⊕ Incomplete)) :
    Option Incomplete :=
  match view.2 with
  | some (.inr receipt) => some receipt
  | _ => none

theorem retainedView_supports_publicStatus
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    retainedPublicStatus (retainedView outcome) = outcome.publicStatus := by
  cases outcome <;> rfl

theorem retainedView_supports_recoveryAxis
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    statusRecoveryAxis (retainedPublicStatus (retainedView outcome)) = recoveryAxis outcome := by
  rw [retainedView_supports_publicStatus, recoveryAxis_factors_publicStatus]

theorem retainedView_supports_incompleteReceipt
    (outcome : Outcome Established Refuted Boundary Incomplete) :
    retainedIncompleteReceipt (retainedView outcome) = incompleteReceipt outcome := by
  cases outcome <;> rfl

section Indexed

variable {Context : Type z} {BoundaryAt : Context → Type w} {IncompleteAt : Context → Type x}

/-- The context is retained with its dependent unresolved payload. -/
abbrev IndexedView (BoundaryAt : Context → Type w) (IncompleteAt : Context → Type x) :=
  Σ context, Option Bool × Option (BoundaryAt context ⊕ IncompleteAt context)

def indexedView (context : Context)
    (outcome : Outcome Established Refuted (BoundaryAt context) (IncompleteAt context)) :
    IndexedView BoundaryAt IncompleteAt := ⟨context, retainedView outcome⟩

def indexedIncompleteReceipt (view : IndexedView BoundaryAt IncompleteAt) :
    Option (Σ context, IncompleteAt context) :=
  (retainedIncompleteReceipt view.2).map (fun receipt => ⟨view.1, receipt⟩)

/-- The actual receipt is recoverable with its original context, even when
the answer view is empty. No lookup by an unscoped global key is required. -/
theorem indexedView_supports_incompleteReceipt (context : Context)
    (receipt : IncompleteAt context) :
    indexedIncompleteReceipt
      (indexedView (Established := Established) (Refuted := Refuted)
        (BoundaryAt := BoundaryAt) context (.incomplete receipt)) = some ⟨context, receipt⟩ := rfl

end Indexed

#print axioms publicStatus_factors_asBool_iff
#print axioms recoveryAxis_not_factors_asBool
#print axioms budget_resolution_selects_budget
#print axioms authority_resolution_selects_authority
#print axioms incompleteReceipt_not_factors_publicStatus
#print axioms retainedView_supports_publicStatus
#print axioms retainedView_supports_incompleteReceipt
#print axioms indexedView_supports_incompleteReceipt

end Mettapedia.TypeTheory.AuthorityOutcomeViews
