import Mettapedia.Languages.MeTTa.PeTTa.StableIntrinsicTypeQuery
import Mettapedia.Logic.LP.IndependentOutputUnification
import Mettapedia.Logic.LP.ConjunctiveUnification

/-!
# Ordered intrinsic-query replies joined to the reached caller record

The provider receives both operands under the actual incoming solver record.
Every reply is then unified with the original expected term while retaining
that record. Alternatives start from the same incoming record; a failed
trial cannot constrain its sibling. Query incompleteness is distinct from a
completed empty result and from an inconsistent caller record.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StableTypeCallerBinding

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.IndependentOutputUnification
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open IndependentTypeOutput (Path Supply)

abbrev Equations := List (TypeTerm × TypeTerm)

structure Delivery where
  occurrence : Nat
  reply : TypeTerm
  bindings : Subst signature

def deliverFrom (before : Equations) (expected : TypeTerm) : Nat → List TypeTerm → List Delivery
  | _, [] => []
  | occurrence, reply :: rest =>
      match unifyTotal (before ++ [(reply, expected)]) with
      | none => deliverFrom before expected (occurrence + 1) rest
      | some bindings => ⟨occurrence, reply, bindings⟩ :: deliverFrom before expected (occurrence + 1) rest

def deliver (before : Equations) (expected : TypeTerm) (replies : List TypeTerm) : List Delivery :=
  deliverFrom before expected 0 replies

inductive Result where
  | invalidCaller
  | pending
  | complete (deliveries : List Delivery)

def call (library : List Declaration) (supply : Supply) (fuel : Nat) (path : Path)
    (before : Equations) (subject expected : TypeTerm) : Result :=
  match unifyTotal before with
  | none => .invalidCaller
  | some caller =>
      match StableIntrinsicTypeQuery.run library supply fuel path
          (caller.applyTerm subject) (some (caller.applyTerm expected)) with
      | none => .pending
      | some replies => .complete (deliver before expected replies)

theorem delivery_origin (before : Equations) (expected : TypeTerm) (occurrence : Nat)
    (replies : List TypeTerm) (delivery : Delivery)
    (member : delivery ∈ deliverFrom before expected occurrence replies) :
    ∃ offset, replies[offset]? = some delivery.reply ∧
      delivery.occurrence = occurrence + offset ∧
      unifyTotal (before ++ [(delivery.reply, expected)]) = some delivery.bindings := by
  induction replies generalizing occurrence with
  | nil => simp [deliverFrom] at member
  | cons reply rest ih =>
    simp only [deliverFrom] at member
    cases matched : unifyTotal (before ++ [(reply, expected)]) with
    | none =>
      rw [matched] at member
      obtain ⟨offset, atOffset, position, accepted⟩ := ih (occurrence + 1) member
      refine ⟨offset + 1, ?_, ?_, accepted⟩
      · simpa using atOffset
      · omega
    | some bindings =>
      rw [matched] at member
      rcases List.mem_cons.mp member with first | later
      · cases first
        exact ⟨0, rfl, by simp, matched⟩
      · obtain ⟨offset, atOffset, position, accepted⟩ := ih (occurrence + 1) later
        refine ⟨offset + 1, ?_, ?_, accepted⟩
        · simpa using atOffset
        · omega

theorem delivery_keeps_caller (before : Equations) (expected : TypeTerm) (replies : List TypeTerm)
    (delivery : Delivery) (member : delivery ∈ deliver before expected replies) :
    Unifies delivery.bindings before := by
  obtain ⟨_offset, _reply, _position, accepted⟩ := delivery_origin before expected 0 replies delivery member
  intro equation occurs
  exact unifyTotal_sound _ _ accepted equation (List.mem_append_left _ occurs)

theorem delivery_binds_original_expected (before : Equations) (expected : TypeTerm)
    (replies : List TypeTerm) (delivery : Delivery) (member : delivery ∈ deliver before expected replies) :
    delivery.bindings.applyTerm delivery.reply = delivery.bindings.applyTerm expected := by
  obtain ⟨_offset, _reply, _position, accepted⟩ := delivery_origin before expected 0 replies delivery member
  exact unifyTotal_sound _ _ accepted (delivery.reply, expected) (by simp)

/-- All caller observations are projected together. This retains aliases
between the expected term, original subject and older caller continuations. -/
theorem delivery_joint_refinements (before : Equations) (expected : TypeTerm)
    (replies : List TypeTerm) (delivery : Delivery) (member : delivery ∈ deliver before expected replies)
    (observations : List TypeTerm) :
    refinements delivery.bindings observations =
      solutions (before ++ [(delivery.reply, expected)]) observations := by
  obtain ⟨_offset, _reply, _position, accepted⟩ := delivery_origin before expected 0 replies delivery member
  exact total_refinements_exact _ _ accepted observations

theorem failed_reply_keeps_sibling_record (before : Equations) (expected reply : TypeTerm)
    (occurrence : Nat) (rest : List TypeTerm)
    (refused : unifyTotal (before ++ [(reply, expected)]) = none) :
    deliverFrom before expected occurrence (reply :: rest) =
      deliverFrom before expected (occurrence + 1) rest := by simp [deliverFrom, refused]

theorem pending_not_empty (library : List Declaration) (supply : Supply) (fuel : Nat) (path : Path)
    (before : Equations) (subject expected : TypeTerm) (caller : Subst signature)
    (entered : unifyTotal before = some caller)
    (unfinished : StableIntrinsicTypeQuery.run library supply fuel path (caller.applyTerm subject)
      (some (caller.applyTerm expected)) = none) :
    call library supply fuel path before subject expected = .pending := by simp [call, entered, unfinished]

theorem complete_empty (library : List Declaration) (supply : Supply) (fuel : Nat) (path : Path)
    (before : Equations) (subject expected : TypeTerm) (caller : Subst signature)
    (entered : unifyTotal before = some caller)
    (empty : StableIntrinsicTypeQuery.run library supply fuel path (caller.applyTerm subject)
      (some (caller.applyTerm expected)) = some []) :
    call library supply fuel path before subject expected = .complete [] := by
  simp [call, entered, empty, deliver, deliverFrom]

theorem completed_call_origin (library : List Declaration) (supply : Supply) (fuel : Nat) (path : Path)
    (before : Equations) (subject expected : TypeTerm) (deliveries : List Delivery)
    (completed : call library supply fuel path before subject expected = .complete deliveries) :
    ∃ caller replies, unifyTotal before = some caller ∧
      StableIntrinsicTypeQuery.run library supply fuel path (caller.applyTerm subject)
        (some (caller.applyTerm expected)) = some replies ∧
      deliveries = deliver before expected replies := by
  unfold call at completed
  cases entered : unifyTotal before with
  | none => simp [entered] at completed
  | some caller =>
    simp only [entered] at completed
    cases queried : StableIntrinsicTypeQuery.run library supply fuel path
        (caller.applyTerm subject) (some (caller.applyTerm expected)) with
    | none => simp [queried] at completed
    | some replies =>
      simp only [queried, Result.complete.injEq] at completed
      exact ⟨caller, replies, rfl, queried, completed.symm⟩

/-- A ground value earned under the actual entering caller solver cannot be
changed by any successful query reply, even when other caller names alias the
required type and become refined during the query. -/
theorem delivery_keeps_ground_value (before : Equations) (expected : TypeTerm)
    (replies : List TypeTerm) (delivery : Delivery) (member : delivery ∈ deliver before expected replies)
    (caller : Subst signature) (entered : unifyTotal before = some caller)
    (kept : TypeTerm) (ground : (caller.applyTerm kept).isGround) :
    delivery.bindings.applyTerm kept = caller.applyTerm kept := by
  obtain ⟨later, factor⟩ := unifyTotal_mgu before caller entered delivery.bindings
    (delivery_keeps_caller before expected replies delivery member)
  have same : delivery.bindings = Subst.comp later caller := funext factor
  rw [same, Subst.applyTerm_comp,
    Mettapedia.Logic.LP.ConjunctiveUnification.applyTerm_of_isGround later ground]

/-- The ground-version fact is connected to a reached call, not to an assumed
reply vector or a value-only callee oracle. -/
theorem completed_call_keeps_ground_value (library : List Declaration) (supply : Supply)
    (fuel : Nat) (path : Path) (before : Equations) (subject expected kept : TypeTerm)
    (caller : Subst signature) (entered : unifyTotal before = some caller)
    (ground : (caller.applyTerm kept).isGround) (deliveries : List Delivery)
    (completed : call library supply fuel path before subject expected = .complete deliveries)
    (delivery : Delivery) (member : delivery ∈ deliveries) :
    delivery.bindings.applyTerm kept = caller.applyTerm kept := by
  obtain ⟨_entered, replies, _actual, _query, rfl⟩ :=
    completed_call_origin library supply fuel path before subject expected deliveries completed
  exact delivery_keeps_ground_value before expected replies delivery member caller entered kept ground

end Mettapedia.Languages.MeTTa.PeTTa.StableTypeCallerBinding
