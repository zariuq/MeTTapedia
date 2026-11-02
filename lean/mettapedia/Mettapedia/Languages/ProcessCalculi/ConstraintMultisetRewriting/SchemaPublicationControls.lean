import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Dynamic activation origins, physical routing and publication controls

One installed schema activates a genuinely input-dependent successor rule.
The kernel publishes through that computed instance, while a nonwriter cannot.
A fabricated concrete rule has no activation origin. An equal payload in a
different physical space cannot supply the declared theorem-space premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)

abbrev signature := ConstraintMultisetRewriting.Controls.signature
abbrev Base := FirstOrder.action signature

inductive Space where
  | client | theorems
  deriving DecidableEq

inductive Actor where
  | kernel | client
  deriving DecidableEq

inductive Schema where
  | successor | copy
  deriving DecidableEq

abbrev Value := Space × Term signature
abbrev A := LocatedSubstitution.action (N := Space) Base

def rule (input output : Nat) : RuleInstance Value :=
  ⟨[(.theorems, .const input)], [], [], [], [(.theorems, .const output)]⟩

def activate : Schema → Nat → Option (RuleInstance Value)
  | .successor, input => some (rule input (input + 1))
  | .copy, input => some (rule input input)

def location (occurrence : Nat) : Space := if occurrence = 9 then .client else .theorems
def payload (occurrence : Nat) : Term signature := if occurrence = 9 then .const 0 else .const occurrence
def label (occurrence : Nat) : Value := (location occurrence, payload occurrence)
def protectedOccurrence (occurrence : Nat) : Prop := location occurrence = .theorems

instance : DecidablePred protectedOccurrence := fun _ => inferInstanceAs (Decidable (_ = _))

def process : Actor → SchemaPublicationAuthority.Process Schema Space
  | .kernel => ⟨fun _ _ => true, [.successor]⟩
  | .client => ⟨fun space _ => space == .client, [.successor, .copy]⟩

def system : SchemaPublicationAuthority.System Schema Space Actor Nat location protectedOccurrence where
  process := process
  kernel := .kernel
  soleWriter := by
    intro actor notKernel occurrence isProtected
    cases actor with
    | kernel => exact False.elim (notKernel rfl)
    | client =>
        change (location occurrence == Space.client) = false
        rw [show location occurrence = Space.theorems from isProtected]
        rfl

def before : Configuration Value Nat := ⟨[], {0}⟩
def picked : Selection Nat := ⟨[0], [], [1]⟩

theorem ordinary_selection_is_valid : picked.Valid A label (rule 0 1) before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl,
    ⟨by decide, by decide, by decide, by decide, by simp [Selection.commit]⟩, ?_, ?_⟩
  · refine ⟨A.identity, ?_⟩
    intro equation member
    have same : equation = ((Space.theorems, Term.const (σ := signature) 0), (.theorems, .const 0)) := by
      simpa [Selection.problem, Selection.equations, picked, before, rule, label, location, payload] using member
    subst equation
    exact ⟨rfl, rfl⟩
  · intro check member
    cases member

theorem kernel_publishes_from_the_actual_schema :
    system.Step activate A label .kernel before (picked.result label (rule 0 1) before) := by
  refine ⟨.successor, by simp [system, process], 0, rule 0 1, rfl, picked, ordinary_selection_is_valid, ?_, rfl⟩
  intro occurrence member
  rfl

theorem a_fabricated_concrete_rule_has_no_successor_origin (input : Nat) :
    activate .successor input ≠ some (rule 0 99) := by
  intro computed
  have same := Option.some.inj computed
  have taken := congrArg RuleInstance.take same
  have inputZero : input = 0 := Term.const.inj (Prod.mk.inj (List.cons.inj taken).1).2
  subst input
  have outputs := congrArg RuleInstance.produce same
  have impossible : (1 : Nat) = 99 := Term.const.inj (Prod.mk.inj (List.cons.inj outputs).1).2
  omega

theorem client_cannot_publish_even_with_a_known_schema :
    ¬system.Step activate A label .client before (picked.result label (rule 0 1) before) := by
  intro stepped
  have inherited := system.nonwriter_creates_no_protected_occurrence activate A label
    (actor := .client) (by decide) stepped (occurrence := 1) (by decide) rfl
  have impossible : (1 : Nat) ∈ ({0} : Finset Nat) := inherited
  simp at impossible

def initial (value : Value) : Prop := value = (.theorems, .const 0)

theorem initial_derivation_invariant :
    SchemaPublicationAuthority.AllDerivable A label protectedOccurrence activate (process .kernel).schemas initial before := by
  intro assignment _ occurrence member _
  have same : occurrence = 0 := by simpa [before] using member
  subst occurrence
  exact .initial rfl

theorem published_value_has_installed_schema_provenance :
    Derivable initial (SchemaPublicationAuthority.Infers A label protectedOccurrence activate (process .kernel).schemas)
      (Space.theorems, Term.const (σ := signature) 1) := by
  have preserved := system.step_allDerivable activate A label initial kernel_publishes_from_the_actual_schema
    initial_derivation_invariant
  have models := ordinary_selection_is_valid.consistent
  obtain ⟨assignment, solved⟩ := models
  exact preserved assignment solved 1 (by decide) rfl

def unprotectedBefore : Configuration Value Nat := ⟨[], {9}⟩
def unprotectedSelection : Selection Nat := ⟨[9], [], [1]⟩

theorem unprotected_payload_is_the_same_value : payload 9 = payload 0 := rfl

theorem the_same_payload_cannot_supply_a_different_physical_space :
    ¬unprotectedSelection.Valid A label (rule 0 1) unprotectedBefore := by
  intro valid
  have places := LocatedSubstitution.take_locations Base location payload valid
  cases places with
  | cons same rest =>
      change Space.theorems = Space.client at same
      cases same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationControls
