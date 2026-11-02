import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise

/-!
# Compact immutable plan keys

The reference writes thirteen words. The target packs the narrow fields into
eight words. Both distinguish exactly the same metadata, including occurrence
positions, charges, flags and retained program identities. Packing uses the
declared field widths; native padding is never a key component.

This is a key-encoding refinement, not an injectivity claim for the hash.
Collisions still require exact comparison of metadata and ordered children.
Native pointer representation, allocator and C correspondence remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PackedPlanKey

abbrev Byte := Fin 256
abbrev Word := Fin 4294967296
abbrev Wide := Fin 18446744073709551616

def join (low high : Word) : Nat := low.val + 4294967296 * high.val

theorem join_injective (a b c d : Word) (same : join a b = join c d) :
    a = c ∧ b = d := by
  have ha := a.isLt
  have hc := c.isLt
  dsimp [join] at same
  constructor <;> apply Fin.ext <;> omega

theorem join_fits (low high : Word) : join low high < 18446744073709551616 := by
  have hl := low.isLt
  have hh := high.isLt
  dsimp [join]
  omega

theorem join_bitwise (low high : Word) :
    join low high = low.val ||| (high.val <<< 32) := by
  have bound : low.val < 2 ^ 32 := low.isLt
  simpa [join, Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm, Nat.or_comm] using
    (Nat.shiftLeft_add_eq_or_of_lt bound high.val)

def widenByte (value : Byte) : Word := ⟨value.val, by have h := value.isLt; omega⟩
def widenFlags (value : Fin 1024) : Word := ⟨value.val, by have h := value.isLt; omega⟩

def scopeHeader (flags : Fin 1024) (variableCount : Byte) : Word :=
  ⟨flags.val + 65536 * variableCount.val, by
    have hf := flags.isLt
    have hv := variableCount.isLt
    omega⟩

theorem scopeHeader_injective (flags flags' : Fin 1024) (variableCount variableCount' : Byte)
    (same : scopeHeader flags variableCount = scopeHeader flags' variableCount') :
    flags = flags' ∧ variableCount = variableCount' := by
  have hf := flags.isLt
  have hf' := flags'.isLt
  have hv := variableCount.isLt
  have hv' := variableCount'.isLt
  have equation := congrArg Fin.val same
  dsimp [scopeHeader] at equation
  constructor <;> apply Fin.ext <;> omega

theorem scopeHeader_bitwise (flags : Fin 1024) (variableCount : Byte) :
    (scopeHeader flags variableCount).val = flags.val ||| (variableCount.val <<< 16) := by
  have bound : flags.val < 2 ^ 16 := by have h := flags.isLt; norm_num; omega
  simpa [scopeHeader, Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm, Nat.or_comm] using
    (Nat.shiftLeft_add_eq_or_of_lt bound variableCount.val)

def header (role execution continuation output : Byte) : Word :=
  ⟨role.val + 256 * execution.val + 65536 * continuation.val + 16777216 * output.val, by
    have hr := role.isLt
    have he := execution.isLt
    have hc := continuation.isLt
    have ho := output.isLt
    omega⟩

theorem header_injective (a b c d a' b' c' d' : Byte)
    (same : header a b c d = header a' b' c' d') :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hd := d.isLt
  have ha' := a'.isLt
  have hb' := b'.isLt
  have hc' := c'.isLt
  have hd' := d'.isLt
  have equation := congrArg Fin.val same
  dsimp [header] at equation
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> omega

theorem header_bitwise (a b c d : Byte) :
    (header a b c d).val = a.val ||| (b.val <<< 8) ||| (c.val <<< 16) ||| (d.val <<< 24) := by
  have first : a.val + 256 * b.val = a.val ||| (b.val <<< 8) := by
    simpa [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm, Nat.or_comm] using
      (Nat.shiftLeft_add_eq_or_of_lt (i := 8) a.isLt b.val)
  have lower16 : a.val + 256 * b.val < 2 ^ 16 := by
    have ha := a.isLt
    have hb := b.isLt
    norm_num
    omega
  have second : (a.val + 256 * b.val) + 65536 * c.val =
      (a.val + 256 * b.val) ||| (c.val <<< 16) := by
    simpa [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm, Nat.or_comm] using
      (Nat.shiftLeft_add_eq_or_of_lt lower16 c.val)
  have lower24 : a.val + 256 * b.val + 65536 * c.val < 2 ^ 24 := by
    have ha := a.isLt
    have hb := b.isLt
    have hc := c.isLt
    norm_num
    omega
  have third : a.val + 256 * b.val + 65536 * c.val + 16777216 * d.val =
      (a.val + 256 * b.val + 65536 * c.val) ||| (d.val <<< 24) := by
    simpa [Nat.shiftLeft_eq, Nat.mul_comm, Nat.add_comm, Nat.or_comm] using
      (Nat.shiftLeft_add_eq_or_of_lt lower24 d.val)
  change a.val + 256 * b.val + 65536 * c.val + 16777216 * d.val = _
  rw [third, second, first]

structure Metadata where
  role : Byte
  execution : Byte
  continuation : Byte
  output : Byte
  invocation : Word
  control : Word
  flags : Fin 1024
  valueVariables : Byte
  scalarOperations : Word
  variableSlot : Word
  outputChild : Wide
  region : Wide
  holeProgram : Wide
  childCount : Wide
  position : Word
  debit : Word
  deriving DecidableEq

def reference (m : Metadata) : List Nat :=
  [join (widenByte m.role) m.invocation, m.execution.val, m.control.val,
   m.continuation.val, m.output.val, m.outputChild.val,
   join (widenFlags m.flags) m.scalarOperations, m.variableSlot.val,
   m.region.val, m.holeProgram.val, m.childCount.val, join m.position m.debit,
   m.valueVariables.val]

def packed (m : Metadata) : List Nat :=
  [join (header m.role m.execution m.continuation m.output) m.invocation,
   join m.control m.scalarOperations, join (scopeHeader m.flags m.valueVariables) m.variableSlot,
   m.outputChild.val, m.region.val, m.holeProgram.val, m.childCount.val,
   join m.position m.debit]

theorem packed_injective : Function.Injective packed := by
  intro a b same
  simp only [packed, List.cons.injEq, and_true] at same
  rcases same with ⟨h0, h1, h2, ho, hr, hh, hn, h7⟩
  obtain ⟨headerEq, invocationEq⟩ := join_injective _ _ _ _ h0
  obtain ⟨roleEq, executionEq, continuationEq, outputEq⟩ :=
    header_injective _ _ _ _ _ _ _ _ headerEq
  obtain ⟨controlEq, operationsEq⟩ := join_injective _ _ _ _ h1
  obtain ⟨scopeWordEq, slotEq⟩ := join_injective _ _ _ _ h2
  obtain ⟨flagsEq, variablesEq⟩ := scopeHeader_injective _ _ _ _ scopeWordEq
  obtain ⟨positionEq, debitEq⟩ := join_injective _ _ _ _ h7
  have outputChildEq := Fin.ext ho
  have regionEq := Fin.ext hr
  have holeEq := Fin.ext hh
  have countEq := Fin.ext hn
  cases a
  cases b
  simp_all

theorem reference_injective : Function.Injective reference := by
  intro a b same
  simp only [reference, List.cons.injEq, and_true] at same
  rcases same with ⟨h0, he, hc, hcont, hout, ho, h6, hv, hr, hh, hn, h11, hvars⟩
  obtain ⟨roleWordEq, invocationEq⟩ := join_injective _ _ _ _ h0
  have roleEq : a.role = b.role := Fin.ext (congrArg (fun value : Word => value.val) roleWordEq)
  obtain ⟨flagsWordEq, operationsEq⟩ := join_injective _ _ _ _ h6
  have flagsEq : a.flags = b.flags := Fin.ext (congrArg (fun value : Word => value.val) flagsWordEq)
  obtain ⟨positionEq, debitEq⟩ := join_injective _ _ _ _ h11
  have executionEq := Fin.ext he
  have controlEq := Fin.ext hc
  have continuationEq := Fin.ext hcont
  have outputEq := Fin.ext hout
  have outputChildEq := Fin.ext ho
  have slotEq := Fin.ext hv
  have regionEq := Fin.ext hr
  have holeEq := Fin.ext hh
  have countEq := Fin.ext hn
  have variablesEq := Fin.ext hvars
  cases a
  cases b
  simp_all

theorem comparison_refines (first second : Metadata) :
    packed first = packed second ↔ reference first = reference second := by
  constructor
  · intro same
    exact congrArg reference (packed_injective same)
  · intro same
    exact congrArg packed (reference_injective same)

theorem packed_words_fit (m : Metadata) :
    ∀ word ∈ packed m, word < 18446744073709551616 := by
  intro word member
  simp only [packed, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact join_fits _ _ | exact Fin.isLt _

theorem word_counts (m : Metadata) : (reference m).length = 13 ∧ (packed m).length = 8 := by
  exact ⟨rfl, rfl⟩

theorem valueVariables_distinguish (a b : Metadata) (different : a.valueVariables ≠ b.valueVariables) :
    packed a ≠ packed b := by
  intro same
  exact different (congrArg Metadata.valueVariables (packed_injective same))

theorem scopeFlags_distinguish (a b : Metadata) (different : a.flags ≠ b.flags) :
    packed a ≠ packed b := by
  intro same
  exact different (congrArg Metadata.flags (packed_injective same))

theorem ordered_metadata_refines (first second : List Metadata) :
    first.map packed = second.map packed ↔ first.map reference = second.map reference := by
  have inject (f : Metadata → List Nat) (faithful : Function.Injective f) :
      ∀ left right : List Metadata, left.map f = right.map f → left = right := by
    intro left
    induction left with
    | nil => intro right same; cases right <;> simp_all
    | cons head tail ih =>
        intro right same
        cases right with
        | nil => simp at same
        | cons next rest =>
            simp only [List.map_cons, List.cons.injEq] at same
            exact congrArg₂ List.cons (faithful same.1) (ih rest same.2)
  constructor
  · intro same
    exact congrArg (List.map reference) (inject packed packed_injective first second same)
  · intro same
    exact congrArg (List.map packed) (inject reference reference_injective first second same)

end Mettapedia.Machines.PackedPlanKey
