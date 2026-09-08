import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedRootConversionCode
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicNativeListRelator

/-!
# Finite codes for the existing List, identity and List-relator roots

The original List/identity code is reused alongside the two List-relator
constructors. All fields are finite scoped syntax; there is no typing or
eligibility proof in a raw code. The decoder reconstructs every parameter,
both List indices, both relational witnesses and the recursive motive result.

Exactness concerns the unchanged `IntrinsicRelator.rules` at every open
arity. The empty inherited computation and opaque declarations exclude other
root cases. This does not establish subject reduction or search for a code.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace NativeRelatorRootConversionCode

open Presentation Presentation.Declaration NativeIndexedFamilies

variable {n : Nat}

inductive Code (n : Nat) where
  | indexed (code : Intrinsic.IotaEvidenceCode n)
  | relNil (source target relation motive nilCase consCase : Tower.Tm n)
  | relCons (source target relation motive nilCase consCase sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence : Tower.Tm n)
  deriving DecidableEq

/-- Every output pair is calculated from the retained raw arguments. -/
def decode : Code n → Option (Tower.Tm n × Tower.Tm n)
  | .indexed code => NativeIndexedRootConversionCode.decode code
  | .relNil source target relation motive nilCase consCase =>
      some (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        (Intrinsic.nilApp source) (Intrinsic.nilApp target)
        (IntrinsicRelator.nilRelApp source target relation), nilCase)
  | .relCons source target relation motive nilCase consCase sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence =>
      some (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
        (Intrinsic.consApp source sourceHead sourceTail)
        (Intrinsic.consApp target targetHead targetTail)
        (IntrinsicRelator.consRelApp source target relation sourceHead targetHead
          sourceTail targetTail headEvidence tailEvidence),
        .app (.app (.app (.app (.app (.app (.app consCase sourceHead) targetHead)
          sourceTail) targetTail) headEvidence) tailEvidence)
          (IntrinsicRelator.eliminateApp source target relation motive nilCase consCase
            sourceTail targetTail tailEvidence))

def encodeEvidence : {left right : Tower.Tm n} →
    IntrinsicRelator.CombinedIotaEvidence n left right → Code n
  | _, _, .list evidence => .indexed evidence.code
  | _, _, .rel (.nil source target relation motive nilCase consCase) =>
      .relNil source target relation motive nilCase consCase
  | _, _, .rel (.cons source target relation motive nilCase consCase sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence) =>
      .relCons source target relation motive nilCase consCase sourceHead targetHead
        sourceTail targetTail headEvidence tailEvidence

theorem decode_evidence {left right : Tower.Tm n}
    (evidence : IntrinsicRelator.CombinedIotaEvidence n left right) :
    decode (encodeEvidence evidence) = some (left, right) := by
  cases evidence with
  | list evidence => exact NativeIndexedRootConversionCode.decode_evidence evidence
  | rel evidence => cases evidence <;> rfl

theorem decode_sound (code : Code n) {left right : Tower.Tm n}
    (decoded : decode code = some (left, right)) :
    IntrinsicRelator.rules.computation.step left right := by
  cases code with
  | indexed code =>
      cases code with
      | nil element motive nilCase consCase =>
          cases Option.some.inj decoded
          exact RootStep.declared ⟨.list (.nil _ _ _ _)⟩
      | cons element motive nilCase consCase head tail =>
          cases Option.some.inj decoded
          exact RootStep.declared ⟨.list (.cons _ _ _ _ _ _)⟩
      | identity element point motive reflCase =>
          cases Option.some.inj decoded
          exact RootStep.declared ⟨.list (.identity _ _ _ _)⟩
  | relNil source target relation motive nilCase consCase =>
      cases Option.some.inj decoded
      exact RootStep.declared ⟨.rel (.nil _ _ _ _ _ _)⟩
  | relCons source target relation motive nilCase consCase sourceHead targetHead
      sourceTail targetTail headEvidence tailEvidence =>
      cases Option.some.inj decoded
      exact RootStep.declared ⟨.rel (.cons _ _ _ _ _ _ _ _ _ _ _ _)⟩

theorem decode_complete {left right : Tower.Tm n}
    (step : IntrinsicRelator.rules.computation.step left right) :
    ∃ code : Code n, decode code = some (left, right) := by
  cases step with
  | inherited impossible => exact impossible.elim
  | delta unfolding =>
      rw [IntrinsicRelator.rawSignature_valueOf_none] at unfolding
      cases unfolding
  | declared retained =>
      obtain ⟨evidence⟩ := retained
      exact ⟨encodeEvidence evidence, decode_evidence evidence⟩

theorem root_iff_decodes {left right : Tower.Tm n} :
    IntrinsicRelator.rules.computation.step left right ↔
      ∃ code : Code n, decode code = some (left, right) :=
  ⟨decode_complete, fun ⟨code, decoded⟩ => decode_sound code decoded⟩

def rootDecoder : StructuralConversionCode.RootDecoder IntrinsicRelator.rules.computation where
  Code := Code
  decode := decode
  sound := decode_sound
  complete := decode_complete

def check (code : Code n) (left right : Tower.Tm n) : Bool :=
  decide (decode code = some (left, right))

theorem check_iff (code : Code n) (left right : Tower.Tm n) :
    check code left right = true ↔ decode code = some (left, right) := by simp [check]

theorem check_sound (code : Code n) {left right : Tower.Tm n}
    (checked : check code left right = true) :
    IntrinsicRelator.rules.computation.step left right :=
  decode_sound code ((check_iff code left right).mp checked)

theorem root_iff_checked {left right : Tower.Tm n} :
    IntrinsicRelator.rules.computation.step left right ↔
      ∃ code : Code n, check code left right = true := by
  simp only [check_iff, root_iff_decodes]

namespace Examples

def listNilCode : Code 4 := .indexed NativeIndexedRootConversionCode.nilCode
def listConsCode : Code 6 := .indexed NativeIndexedRootConversionCode.consCode
def identityCode : Code 4 := .indexed NativeIndexedRootConversionCode.identityCode

def relNilCode : Code 6 := .relNil (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def relConsCode : Code 12 :=
  .relCons (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
    (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

theorem list_nil_checked :
    check listNilCode Intrinsic.nilIotaLeft Intrinsic.nilIotaRight = true := by decide

theorem list_cons_checked :
    check listConsCode Intrinsic.consIotaLeft Intrinsic.consIotaRight = true := by decide

theorem identity_checked :
    check identityCode Intrinsic.identityIotaLeft Intrinsic.identityIotaRight = true := by decide

theorem rel_nil_checked :
    check relNilCode IntrinsicRelator.nilIotaLeft IntrinsicRelator.nilIotaRight = true := by decide

theorem rel_cons_checked :
    check relConsCode IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaRight = true := by decide

/-- A relational root cannot silently switch the relation parameter. -/
theorem changed_relation_rejected :
    check (.relNil (.var 5) (.var 4) (.var 2) (.var 2) (.var 1) (.var 0))
      IntrinsicRelator.nilIotaLeft IntrinsicRelator.nilIotaRight = false := by decide

/-- Retained relational evidence is not erased to the two endpoint Lists. -/
theorem changed_head_evidence_rejected :
    check (.relCons (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
      (.var 5) (.var 4) (.var 3) (.var 2) (.var 0) (.var 0))
      IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaRight = false := by decide

theorem changed_tail_evidence_rejected :
    check (.relCons (.var 11) (.var 10) (.var 9) (.var 8) (.var 7) (.var 6)
      (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 1))
      IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaRight = false := by decide

/-- The last branch argument is the actual recursively eliminated tail witness. -/
theorem missing_recursive_result_rejected :
    check relConsCode IntrinsicRelator.consIotaLeft
      (.app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 4))
        (.var 3)) (.var 2)) (.var 1)) (.var 0)) = false := by decide

theorem changed_output_rejected :
    check relNilCode IntrinsicRelator.nilIotaLeft (.var 0) = false := by decide

theorem wrong_branch_rejected :
    check listConsCode IntrinsicRelator.nilIotaLeft IntrinsicRelator.nilIotaRight = false := by decide

end Examples

#print axioms decode_evidence
#print axioms decode_sound
#print axioms decode_complete
#print axioms rootDecoder
#print axioms root_iff_checked
#print axioms Examples.list_nil_checked
#print axioms Examples.list_cons_checked
#print axioms Examples.identity_checked
#print axioms Examples.rel_nil_checked
#print axioms Examples.rel_cons_checked
#print axioms Examples.changed_relation_rejected
#print axioms Examples.changed_head_evidence_rejected
#print axioms Examples.changed_tail_evidence_rejected
#print axioms Examples.missing_recursive_result_rejected
#print axioms Examples.changed_output_rejected
#print axioms Examples.wrong_branch_rejected

end NativeRelatorRootConversionCode
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
