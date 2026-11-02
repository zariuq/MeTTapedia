import Mettapedia.Machines.SourceCase
import Mettapedia.Machines.SourceWordAdmission

/-!
# Fuse a ready pattern test with its selected binding

The reference tests a prepared pattern and, on success, matches it again to
install the selected bindings. The target keeps the bindings from one match.
Both use the same immutable inquiry and matching authority. A failed trial
preserves the entrance bindings; inability to decide is not a mismatch.

The read list counts matcher inquiries, not source fuel or effects. Actual
pattern preparation, native storage, C matching, code-coordinate relocation
and resumable-frame ownership remain native correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PatternBranchFusion

abbrev Atom := Mettapedia.Languages.MeTTa.OSLFCore.Atom
abbrev Bindings := Mettapedia.Languages.ProcessCalculi.MORK.Subst

structure Inquiry where
  pattern : Atom
  value : Atom
  deriving DecidableEq

inductive Decision where
  | matched (bindings : Bindings)
  | mismatch
  | refused
  deriving DecidableEq

inductive Branch where
  | selected (bindings : Bindings) (body : Atom)
  | fallback (bindings : Bindings) (body : Atom)
  | exhausted
  | refused
  deriving DecidableEq

structure Observation where
  branch : Branch
  reads : List Inquiry

def reference (decide : Bindings → Inquiry → Decision) (bindings : Bindings)
    (test bind : Inquiry) (yes no : Atom) : Observation :=
  match decide bindings test with
  | .mismatch => ⟨.fallback bindings no, [test]⟩
  | .refused => ⟨.refused, [test]⟩
  | .matched _ => match decide bindings bind with
    | .matched bound => ⟨.selected bound yes, [test, bind]⟩
    | .mismatch => ⟨.exhausted, [test, bind]⟩
    | .refused => ⟨.refused, [test, bind]⟩

def fused (decide : Bindings → Inquiry → Decision) (bindings : Bindings)
    (inquiry : Inquiry) (yes no : Atom) : Observation :=
  match decide bindings inquiry with
  | .matched bound => ⟨.selected bound yes, [inquiry]⟩
  | .mismatch => ⟨.fallback bindings no, [inquiry]⟩
  | .refused => ⟨.refused, [inquiry]⟩

theorem branch_refines (decide : Bindings → Inquiry → Decision)
    (bindings : Bindings) (inquiry : Inquiry) (yes no : Atom) :
    (fused decide bindings inquiry yes no).branch =
      (reference decide bindings inquiry inquiry yes no).branch := by
  cases result : decide bindings inquiry <;> simp [reference, fused, result]

theorem one_trial (decide : Bindings → Inquiry → Decision)
    (bindings : Bindings) (inquiry : Inquiry) (yes no : Atom) :
    (fused decide bindings inquiry yes no).reads = [inquiry] := by
  cases result : decide bindings inquiry <;> simp [fused, result]

theorem success_saves_one_trial (decide : Bindings → Inquiry → Decision)
    (bindings bound : Bindings) (inquiry : Inquiry) (yes no : Atom)
    (matched : decide bindings inquiry = .matched bound) :
    (reference decide bindings inquiry inquiry yes no).reads.length =
      (fused decide bindings inquiry yes no).reads.length + 1 := by
  simp [reference, fused, matched]

theorem mismatch_preserves_entrance (decide : Bindings → Inquiry → Decision)
    (bindings : Bindings) (inquiry : Inquiry) (yes no : Atom)
    (failed : decide bindings inquiry = .mismatch) :
    (fused decide bindings inquiry yes no).branch = .fallback bindings no := by
  simp [fused, failed]

theorem refusal_is_not_fallback (decide : Bindings → Inquiry → Decision)
    (bindings : Bindings) (inquiry : Inquiry) (yes no : Atom)
    (refused : decide bindings inquiry = .refused) :
    (fused decide bindings inquiry yes no).branch ≠ .fallback bindings no := by
  simp [fused, refused]

def structural (bindings : Bindings) (inquiry : Inquiry) : Decision :=
  match Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.matchValue
      bindings inquiry.pattern inquiry.value with
  | some bound => .matched bound
  | none => .mismatch

theorem fresh_variable_binds (bindings : Bindings) (name : String) (value yes no : Atom)
    (fresh : bindings.lookup name = none) :
    (fused structural bindings ⟨.var name, value⟩ yes no).branch =
      .selected ((name, value) :: bindings) yes := by
  simp [fused, structural, Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.matchValue,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fresh]

theorem prebound_variable_keeps_binding (bindings : Bindings) (name : String)
    (value yes no : Atom) (bound : bindings.lookup name = some value) :
    (fused structural bindings ⟨.var name, value⟩ yes no).branch =
      .selected bindings yes := by
  simp [fused, structural, Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.matchValue,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, bound]

theorem repeated_variable_mismatch_rolls_back :
    (fused structural []
      ⟨.expression [.symbol "Pair", .var "x", .var "x"],
       .expression [.symbol "Pair", .symbol "a", .symbol "b"]⟩
      (.symbol "yes") (.symbol "no")).branch = .fallback [] (.symbol "no") := by
  simp [fused, structural, Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.matchValue,
    Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.matchValue.matchValues,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem different_inquiries_cannot_fuse :
    (reference structural [] ⟨.var "x", .symbol "a"⟩ ⟨.var "x", .symbol "b"⟩
      (.symbol "yes") (.symbol "no")).branch ≠
    (fused structural [] ⟨.var "x", .symbol "a"⟩
      (.symbol "yes") (.symbol "no")).branch := by
  simp [reference, fused, structural,
    Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.matchValue,
    Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
    Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]

theorem selected_source_stays_pending (value : Atom) :
    (fused structural [] ⟨.var "x", value⟩
      (.expression [.symbol "println!", .var "x"]) (.symbol "no")).branch =
      .selected [("x", value)] (.expression [.symbol "println!", .var "x"]) := by
  exact fresh_variable_binds [] "x" value _ _ rfl

/-- A refused matcher has no core entry. A successful branch enters its body;
a failed trial continues the maintained selector under the entrance bindings.
Patterns and the key are already prepared values at this boundary. -/
def continueArm {Value Effect Fault Delay Suspension : Type}
    (decide : Bindings → Inquiry → Decision) (bindings : Bindings)
    (inquiry : Inquiry) (body : Atom)
    (remaining : List (Atom × Atom)) :
    Option (ContextualCBPV.Code Value (Bindings × Atom) Effect Fault Delay Suspension) :=
  match (fused decide bindings inquiry body body).branch with
  | .selected bound selected => some (.invoke (bound, selected))
  | .fallback entrance _ => some (SourceCase.sourceReady entrance inquiry.value remaining)
  | .exhausted => some .failure
  | .refused => none

theorem ready_arm_refines_source {Value Effect Fault Delay Suspension : Type}
    (bindings : Bindings) (pattern key body : Atom) (remaining : List (Atom × Atom)) :
    continueArm (Value := Value) (Effect := Effect) (Fault := Fault)
        (Delay := Delay) (Suspension := Suspension)
        structural bindings ⟨pattern, key⟩ body remaining =
      some (SourceCase.sourceReady bindings key ((pattern, body) :: remaining)) := by
  cases result : Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.matchValue
      bindings pattern key <;>
    simp [continueArm, fused, structural, SourceCase.sourceReady,
      Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.selectCase, result]

theorem first_success_ignores_later_arms {Value Effect Fault Delay Suspension : Type}
    (bindings bound : Bindings) (pattern key body : Atom)
    (remaining : List (Atom × Atom))
    (matched : Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.matchValue
      bindings pattern key = some bound) :
    continueArm (Value := Value) (Effect := Effect) (Fault := Fault)
        (Delay := Delay) (Suspension := Suspension)
        structural bindings ⟨pattern, key⟩ body remaining =
      some (.invoke (bound, body)) := by
  simp [continueArm, fused, structural, matched]

theorem refused_arm_has_no_core_entry {Value Effect Fault Delay Suspension : Type}
    (decide : Bindings → Inquiry → Decision) (bindings : Bindings)
    (inquiry : Inquiry) (body : Atom) (remaining : List (Atom × Atom))
    (refused : decide bindings inquiry = .refused) :
    continueArm (Value := Value) (Effect := Effect) (Fault := Fault)
        (Delay := Delay) (Suspension := Suspension)
        decide bindings inquiry body remaining = none := by
  simp [continueArm, fused, refused]

/-- Matching changes the selected focus, not the enclosing source debit or
physical allowance. The equality includes all saved frames, context and world. -/
theorem bounded_continuation_refines
    {Value Call Effect Fault Delay Suspension Context World Worker : Type}
    (sem : ContextualCBPV.Semantics Value Call Effect Fault Delay Suspension Context World Worker)
    (decide : Bindings → Inquiry → Decision) (bindings : Bindings)
    (inquiry : Inquiry) (yes no : Atom)
    (interpret : Branch → ContextualCBPV.Code Value Call Effect Fault Delay Suspension)
    (context : Context) (maximum : Nat) (limit : Option Nat)
    (occurrence : SourceAccounting.Origin) (debit : Nat)
    (state : SourceWordAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker) :
    let enter := fun branch => {state with meter := {state.meter with state :=
      {state.meter.state with focus := ⟨.compute context (interpret branch),
        state.meter.state.focus.frames⟩}}}
    SourceWordAdmission.nativeStep sem maximum limit occurrence debit
      (enter (fused decide bindings inquiry yes no).branch) =
    SourceWordAdmission.nativeStep sem maximum limit occurrence debit
      (enter (reference decide bindings inquiry inquiry yes no).branch) := by
  dsimp only
  rw [branch_refines]

end Mettapedia.Machines.PatternBranchFusion

#print axioms Mettapedia.Machines.PatternBranchFusion.branch_refines
#print axioms Mettapedia.Machines.PatternBranchFusion.one_trial
#print axioms Mettapedia.Machines.PatternBranchFusion.success_saves_one_trial
#print axioms Mettapedia.Machines.PatternBranchFusion.mismatch_preserves_entrance
#print axioms Mettapedia.Machines.PatternBranchFusion.refusal_is_not_fallback
#print axioms Mettapedia.Machines.PatternBranchFusion.fresh_variable_binds
#print axioms Mettapedia.Machines.PatternBranchFusion.prebound_variable_keeps_binding
#print axioms Mettapedia.Machines.PatternBranchFusion.repeated_variable_mismatch_rolls_back
#print axioms Mettapedia.Machines.PatternBranchFusion.different_inquiries_cannot_fuse
#print axioms Mettapedia.Machines.PatternBranchFusion.selected_source_stays_pending
#print axioms Mettapedia.Machines.PatternBranchFusion.ready_arm_refines_source
#print axioms Mettapedia.Machines.PatternBranchFusion.first_success_ignores_later_arms
#print axioms Mettapedia.Machines.PatternBranchFusion.refused_arm_has_no_core_entry
#print axioms Mettapedia.Machines.PatternBranchFusion.bounded_continuation_refines
