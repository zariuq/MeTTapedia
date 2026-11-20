import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Relay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Publish
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program

/-!
# Optional laws for deterministic code reading and closed publication

The candidate's `Codes` remains an unconstrained interpretation interface.
This certificate supplies functionality, equality respect, substitution
stability and exact unfolding of closed publications when a consumer needs
those guarantees. The named relay and publisher interpretations discharge
the certificate. A relational code interpretation need not satisfy it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules

open RuleSyntax RuleSyntax.RuleOccurrences

universe uO uT uH uE uOcc uR uC uZ

section General

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  (X : Frames Tm Hom) {C : Type uC} {Z : Type uZ}

structure CodeReading (codes : Codes Tm C Z) : Prop where
  functional : ∀ (frame : Obj) (term : Tm frame) (first second : C),
    codes.denotes frame term first → codes.denotes frame term second → first = second
  respects : ∀ (frame : Obj) (first second : Tm frame) (code : C),
    X.E first second → codes.denotes frame first code → codes.denotes frame second code
  stable : ∀ (first last : Obj) (transport : Hom first last) (term : Tm first) (code : C),
    codes.denotes first term code → codes.denotes last (X.act transport term) code
  closes : ∀ (frame : Obj) (knowledge : EquationStore (Tm frame)) (term : Tm frame) (code : C),
    codes.close frame knowledge term = some code →
      codes.unfold code = Spec.ofRule (Spec.closedRow frame knowledge term)

private theorem functional_zip {A B : Type*} (relation : A → B → Prop)
    (functional : ∀ a b c, relation a b → relation a c → b = c) :
    ∀ (arguments : List A) (first second : List B), first.length = arguments.length →
      second.length = arguments.length →
      (∀ entry ∈ arguments.zip first, relation entry.1 entry.2) →
      (∀ entry ∈ arguments.zip second, relation entry.1 entry.2) → first = second := by
  intro arguments
  induction arguments with
  | nil =>
      intro first second firstLength secondLength _ _
      rw [List.length_eq_zero_iff.mp firstLength, List.length_eq_zero_iff.mp secondLength]
  | cons argument rest ih =>
      intro first second firstLength secondLength one two
      cases first with
      | nil => simp at firstLength
      | cons a first =>
          cases second with
          | nil => simp at secondLength
          | cons b second =>
              have head := functional argument a b
                (one (argument, a) (by simp)) (two (argument, b) (by simp))
              have tail := ih first second (by simpa using firstLength) (by simpa using secondLength)
                (fun entry inside => one entry (by simp [inside]))
                (fun entry inside => two entry (by simp [inside]))
              rw [head, tail]

variable {O : Type uOcc} [DecidableEq O] {R : Type uR}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z} {state : RState Tm O R C Z}

def replaceInstalled (firing : RFiring O R E codes state) (installed : List C) : RFiring O R E codes state :=
  ⟨firing.use, firing.ext, firing.opening, firing.selection, firing.seen, firing.madeRules,
    installed, firing.removedRules, firing.published⟩

theorem installed_unique (reading : CodeReading X codes) {ambient : Set C}
    (firing : RFiring O R E codes state) (installed : List C)
    (accepted : firing.Admits X ambient) (accepted' : (replaceInstalled firing installed).Admits X ambient) :
    installed = firing.installed := by
  obtain ⟨frame, model, solved⟩ := accepted.2.2.1
  have first := (accepted.2.2.2 frame model solved).2.2.1
  have second := (accepted'.2.2.2 frame model solved).2.2.1
  exact functional_zip
    (fun (entry : Install Tm Z firing.spec.locals) (code : C) =>
      codes.denotes frame (X.act model (X.act firing.opening entry.term)) code)
    (fun _ a b => reading.functional frame _ a b) firing.spec.installs installed firing.installed
    accepted'.1.2.2.installed accepted.1.2.2.installed second first

omit [DecidableEq O] in
theorem ofRules_reading (zone : Type uZ) : CodeReading X (ofRules zone : Codes Tm (Rule Tm) zone) where
  functional := fun _ _ _ _ impossible => impossible.elim
  respects := fun _ _ _ _ _ impossible => impossible.elim
  stable := fun _ _ _ _ _ impossible => impossible.elim
  closes := fun _ _ _ _ impossible => absurd impossible (by simp)

end General

namespace Instances

open Mettapedia.Logic.LP
open Examples (Tm X c x)

theorem relay_reading : CodeReading X Relay.codes where
  functional := by
    intro frame term first second one two
    have equal : c (100 + first) = c (100 + second) := one.symm.trans two
    have numbers : 100 + first = 100 + second := Term.const.inj equal
    omega
  respects := by
    intro frame first second code equal read
    have same : first = second := equal
    subst second
    exact read
  stable := by
    intro first last transport term code read
    have same : term = c (100 + code) := read
    subst term
    rfl
  closes := fun _ _ _ _ impossible => absurd impossible (by simp [Relay.codes])

theorem publish_reading : CodeReading X Publish.codes where
  functional := fun _ _ _ _ impossible => impossible.elim
  respects := fun _ _ _ _ _ impossible => impossible.elim
  stable := fun _ _ _ _ _ impossible => impossible.elim
  closes := by
    intro frame knowledge term code found
    obtain rfl := Option.some.inj found
    rfl

theorem relay_installs_named_code (message : Nat) (installed : List Nat)
    (accepted : (replaceInstalled (Relay.relayFiring message) installed).Admits X (∅ : Set Nat)) :
    installed = [message] :=
  installed_unique X relay_reading (Relay.relayFiring message) installed
    (Relay.relay_admitted message) accepted

theorem relay_rejects_changed_code {message other : Nat} (different : other ≠ message) :
    ¬ (replaceInstalled (Relay.relayFiring message) [other]).Admits X (∅ : Set Nat) := by
  intro accepted
  exact different (List.singleton_inj.mp (relay_installs_named_code message [other] accepted))

def ambiguous : Codes Tm Nat Unit :=
  ⟨Relay.codes.unfold, fun _ _ code => code = 0 ∨ code = 1, fun _ _ _ => none⟩

theorem ambiguous_not_functional : ¬ CodeReading X ambiguous := by
  intro reading
  have equal : (0 : Nat) = 1 := reading.functional PUnit.unit x 0 1 (Or.inl rfl) (Or.inr rfl)
  exact (by decide : (0 : Nat) ≠ 1) equal

def incorrectClose : Codes Tm Publish.Code Unit :=
  ⟨Publish.codes.unfold, fun _ _ _ => False, fun _ _ _ => some Publish.Code.publisher⟩

theorem incorrectClose_rejected : ¬ CodeReading X incorrectClose := by
  intro reading
  have same := reading.closes PUnit.unit [] x Publish.Code.publisher rfl
  have lengths := congrArg (fun spec : Spec Tm Publish.Code Unit => spec.publishes.length) same
  exact (by decide : (1 : Nat) ≠ 0) lengths

end Instances

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.LiveRules
