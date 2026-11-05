import Mathlib.Tactic

/-!
# AArch64 Phase-5 SVC and Phase-6A detection laws

The register-level mechanism proved by the pinned ARM gate: exact-width SVC
results, capability refusal, completion evidence, and the corrected feature
field positions.  It deliberately makes no POE enforcement claim.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.Arm64Phase5

abbrev Word := BitVec 64

def errCapInvalid : Word := 0xfffffffffffffffc

def svcResult (selector argument : Word) : Word :=
  if selector = 1 then argument + 1
  else if selector = 2 ∧ argument = 42 then 0
  else errCapInvalid

theorem echo_41 : svcResult 1 41 = 42 := by rfl

theorem echo_wraps : svcResult 1 0xffffffffffffffff = 0 := by rfl

theorem valid_capability_succeeds : svcResult 2 42 = 0 := by rfl

theorem invalid_capability_refused (capability : Word) (invalid : capability ≠ 42#64) :
    svcResult 2 capability = errCapInvalid := by
  unfold svcResult
  split
  · rename_i impossible
    have different : (2#64) ≠ 1#64 := by decide
    exact (different impossible).elim
  · split
    · rename_i selected
      exact (invalid selected.2).elim
    · rfl

theorem unknown_selector_refused (selector argument : Word)
    (notEcho : selector ≠ 1#64) (notCap : selector ≠ 2#64) :
    svcResult selector argument = errCapInvalid := by
  unfold svcResult
  split
  · rename_i selected
    exact (notEcho selected).elim
  · split
    · rename_i selected
      exact (notCap selected.1).elim
    · rfl

structure Completion where
  tag : Nat
  ec : Nat
  far : Word
  echo : Word
  capBad : Word
  capGood : Word
  deriving DecidableEq, Repr

def CompletionValid (completion : Completion) : Prop :=
  completion.tag = 5 ∧ completion.ec = 0x24 ∧ completion.far = 0x60000000 ∧
    completion.echo = 42 ∧ completion.capBad = errCapInvalid ∧ completion.capGood = 0

def expectedCompletion : Completion :=
  { tag := 5, ec := 0x24, far := 0x60000000, echo := 42,
    capBad := errCapInvalid, capGood := 0 }

theorem expected_completion_valid : CompletionValid expectedCompletion := by
  simp [CompletionValid, expectedCompletion, errCapInvalid]

theorem wrong_capability_result_invalid :
    ¬ CompletionValid { expectedCompletion with capBad := 0 } := by
  simp [CompletionValid, expectedCompletion, errCapInvalid]

structure FeatureFields where
  tcrx : Nat
  sctlrx : Nat
  s1pie : Nat
  s2pie : Nat
  s1poe : Nat
  deriving DecidableEq, Repr

def decodeFeatures (id : Nat) : FeatureFields :=
  { tcrx := id % 16
    sctlrx := (id / 2^4) % 16
    s1pie := (id / 2^8) % 16
    s2pie := (id / 2^12) % 16
    s1poe := (id / 2^16) % 16 }

theorem corrected_sample_decode :
    decodeFeatures 0x1000000011001111 =
      { tcrx := 1, sctlrx := 1, s1pie := 1, s2pie := 1, s1poe := 0 } := by
  norm_num [decodeFeatures]

#print axioms invalid_capability_refused
#print axioms unknown_selector_refused
#print axioms expected_completion_valid
#print axioms corrected_sample_decode

end Mettapedia.Machines.Kernel.Arm64Phase5
