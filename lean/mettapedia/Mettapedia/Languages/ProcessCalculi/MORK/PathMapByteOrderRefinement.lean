import Mettapedia.Languages.ProcessCalculi.MORK.WorkQueueOrder

/-!
# Historical Location-Key Refinement

Records the abstract `atomKey : Atom → List ℕ` fragment from
`WorkQueueOrder.lean` beside the corresponding tag-level encoding used by the
Rust PathMap runtime.

## The Gap

`WorkQueueOrder.lean` line 28 says:
"This is NOT byte-identical to PathMap serialization."

This file refines the older `atomKey` approximation on a two-symbol location
fragment.  It does not establish full MM2 scheduler adequacy: the physical
queue orders complete `exec` atoms, and the active scheduler model now uses
`morkCompactKey?` on that complete directive.

## PathMap Tag Encoding (from Rust `expr/src/lib.rs`)

```
Tag::Arity(a)      → 0x00 | a     (byte 0x00–0x3F, a ∈ 0..63)
Tag::VarRef(i)     → 0x80 | i     (byte 0x80–0xBF, i ∈ 0..63)
Tag::SymbolSize(s) → 0xC0 | s     (byte 0xC0–0xFF, s ∈ 0..63)
Tag::NewVar        → 0xC0 | 0     (byte 0xC0)
```

## Results

- `symbolSizeTag_nat_mono` — symbol-size tag monotonicity below the 64-byte bound
- `ascii_byte_order` — ASCII character order agrees with its encoded byte order
- `schedulerLocFragment_pair` — symbol pairs inhabit the historical fragment
- `atomKey_order_eq_locLt_on_fragment` — the authored approximation agrees with
  `locLt` on that fragment

## CeTTa/MORK Mapping

| Lean | Rust |
|------|------|
| `serializeSymbol` / `serializeLocFragment` | `item_byte(Tag) + raw_bytes` in `expr/src/lib.rs` |
| byte-order comparison | `to_next_val()` in `space.rs:2582` |
| `atomKey_order_eq_locLt_on_fragment` | historical location projection only |
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK.ByteOrderRefinement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## §1: PathMap Tag Bytes

The Rust PathMap uses tag bytes to distinguish atom kinds.
Arity < VarRef < SymbolSize in byte order, which means
expressions sort before variables, variables before symbols.

However, for the SCHEDULER FRAGMENT (expressions containing only symbols),
only Arity and SymbolSize tags appear. -/

/-- Arity tag byte: `0x00 | arity` (arity ∈ 0..63). -/
def arityTag (arity : Nat) : UInt8 := ⟨arity % 64⟩

/-- SymbolSize tag byte: `0xC0 | length` (length ∈ 1..63). -/
def symbolSizeTag (len : Nat) : UInt8 := ⟨(0xC0 + len % 64) % 256⟩

/-- Variable tag byte: `0x80 | index` (index ∈ 0..63). -/
def varRefTag (idx : Nat) : UInt8 := ⟨(0x80 + idx % 64) % 256⟩

/-! ## §2: Concrete Serialization (Scheduler Fragment Only)

We define serialization for the scheduler fragment:
expressions of the form `(symbol₁ symbol₂)` where both children are symbols.
This matches the exec-location tuple `(priority name)`.

For the full atom type, serialization would need to handle nested expressions,
grounded values, and variables. We restrict to the fragment that matters for
scheduler ordering. -/

/-- Serialize a symbol to PathMap bytes: SymbolSize tag + raw ASCII bytes.

    Maps to: `item_byte(Tag::SymbolSize(s.len()))` + `s.as_bytes()` in Rust. -/
def serializeSymbol (s : String) : List UInt8 :=
  symbolSizeTag s.length :: s.toList.map (fun c => ⟨c.toNat % 256⟩)

/-- Serialize a scheduler location `(priority name)` to PathMap bytes.

    Format: `[2]` (arity 2) + serialize(priority) + serialize(name)

    Maps to: the byte path under the `exec` prefix in `metta_calculus`. -/
def serializeLocFragment (priority name : String) : List UInt8 :=
  arityTag 2 :: (serializeSymbol priority ++ serializeSymbol name)

/-! ## §3: Encoding Components

The definitions below model the two tag components used by the historical
fragment.  The active full-directive encoder and its scheduler proofs live in
`WorkQueueOrder.lean`; this file does not claim that `atomKey` is byte-identical
to `serializeLocFragment`. -/

/-- Arity tag for 2-element expression is 0x02. -/
theorem arityTag_two : arityTag 2 = ⟨2⟩ := rfl

/-- SymbolSize tag is monotone at the natural-number level:
    0xC0+len₁ < 0xC0+len₂ when len₁ < len₂ < 64.

    This captures the key ordering property without going through
    UInt8 comparison (which involves BitVec coercions). -/
theorem symbolSizeTag_nat_mono {len₁ len₂ : Nat}
    (h₁ : len₁ < 64) (h₂ : len₂ < 64) (hlt : len₁ < len₂) :
    (0xC0 + len₁ % 64) % 256 < (0xC0 + len₂ % 64) % 256 := by
  omega

/-- ASCII byte ordering matches Char.toNat ordering for 7-bit ASCII.

    Maps to: within the same-length symbol, raw bytes are compared as
    unsigned integers, which equals comparing Char.toNat values. -/
theorem ascii_byte_order (c₁ c₂ : Char)
    (h₁ : c₁.toNat < 128) (h₂ : c₂.toNat < 128) :
    (⟨c₁.toNat % 256⟩ : UInt8) < (⟨c₂.toNat % 256⟩ : UInt8) ↔ c₁.toNat < c₂.toNat := by
  constructor
  · intro h; simp [UInt8.lt_iff_toNat_lt_toNat, UInt8.toNat] at h; omega
  · intro h; simp [UInt8.lt_iff_toNat_lt_toNat, UInt8.toNat]; omega

/-! ## §4: Fragment Membership

The examples below show how symbol-pair locations are serialized.  No theorem
in this section identifies that byte order with the older `atomKey` order.

Positive example: `("0" "a")` serializes to `[0x02, 0xC1, 0x30, 0xC1, 0x61]`,
`("0" "b")` to `[0x02, 0xC1, 0x30, 0xC1, 0x62]`. Their byte comparison first
differs at the final byte: 0x61 < 0x62.

Negative example: `("1" "a")` vs `("0" "b")`. Byte comparison at position 2:
0xC1 = 0xC1 (same length), then position 3: 0x31 > 0x30 (ASCII '1' > '0').
So `("1" "a")` > `("0" "b")`. -/

/-- Two symbol pairs are members of the historical location fragment.

This theorem deliberately states only fragment membership.  Physical byte
ordering is handled by the exact full-directive key in `WorkQueueOrder.lean`. -/
theorem schedulerLocFragment_pair (p₁ n₁ p₂ n₂ : String) :
    let loc₁ := Atom.expression [.symbol p₁, .symbol n₁]
    let loc₂ := Atom.expression [.symbol p₂, .symbol n₂]
    schedulerLocFragment loc₁ ∧ schedulerLocFragment loc₂ :=
  ⟨⟨p₁, n₁, rfl⟩, ⟨p₂, n₂, rfl⟩⟩

/-! ## §5: Historical Authored Location Order

The result below relates `atomKey` and `locLt` for the supported location
fragment.  It must not be lifted to a claim about work-queue pop order, because
two complete directives with the same location may differ later in their
compact-expression bytes.

The theorem below is exactly the first, authored link:
`atomKey_order_on_fragment` from `WorkQueueOrder.lean` states
`lexLt ∘ atomKey = locLt`.  This section deliberately does not promote it to a
physical PathMap traversal theorem. -/

/-- **Historical location-key faithfulness on the fragment:**
    the location approximation agrees with `locLt`.

    This is `locLt = lexLt ∘ atomKey` on the fragment, as proved in
    `WorkQueueOrder.lean`.  It says nothing about the physical bytes of a
    complete directive.

    Positive example: the authored approximation orders locations
    `("0" "a")` before `("0" "b")`.

    Negative example: if the fragment restriction is dropped (e.g., nested
    expressions or grounded values in location tuples), this theorem does not
    apply. -/
theorem atomKey_order_eq_locLt_on_fragment (loc₁ loc₂ : Atom)
    (h₁ : schedulerLocFragment loc₁)
    (h₂ : schedulerLocFragment loc₂) :
    -- On the fragment, the two authored orderings agree.
    lexLt (atomKey loc₁) (atomKey loc₂) = locLt loc₁ loc₂ :=
  atomKey_order_on_fragment loc₁ loc₂ h₁ h₂

/-- Location-projection monotonicity on the two-symbol fragment.  This is not
a theorem about complete-directive pop order. -/
theorem atomKey_order_true_of_locLt_on_fragment (loc₁ loc₂ : Atom)
    (h₁ : schedulerLocFragment loc₁)
    (h₂ : schedulerLocFragment loc₂)
    (hlt : locLt loc₁ loc₂ = true) :
    lexLt (atomKey loc₁) (atomKey loc₂) = true := by
  rw [atomKey_order_on_fragment loc₁ loc₂ h₁ h₂]; exact hlt

/-! ## §6: Unsupported Remainder

The tag lemmas, serialization definitions, and authored `atomKey`/`locLt`
agreement above concern only the location fragment
`(priority_string name_string)`.  They do not constitute a physical scheduler
refinement.

**NOT covered by this historical projection:**
- Nested expression locations: `((1 (0)) name)` — common in MM2 scheduling
- Grounded value locations: `(42 name)` where 42 is a `GroundedValue.int`
- Variable locations: `($x name)` — unusual but syntactically valid
- Non-ASCII symbol content: UTF-8 multibyte characters in priority/name
- Symbols longer than 63 bytes: exceeds SymbolSize tag capacity

The active work-queue semantics instead uses `morkCompactKey?` on complete
representable directives; `atomKey` remains only an authored approximation.
-/

/-! ## §7: Summary

Key theorems:
- `symbolSizeTag_nat_mono` — shorter supported symbols have smaller tag bytes
- `ascii_byte_order` — byte comparison = char comparison for ASCII
- `schedulerLocFragment_pair` — symbol pairs inhabit the historical fragment
- `atomKey_order_eq_locLt_on_fragment` — `atomKey` ordering = `locLt` on the fragment
- `atomKey_order_true_of_locLt_on_fragment` — location-projection monotonicity

Maps to CeTTa/MORK runtime:
- `serializeSymbol` → `item_byte(Tag::SymbolSize)` + raw bytes
- `serializeLocFragment` → byte path under `exec` prefix
- full `metta_calculus` order → `morkCompactKey?` in `WorkQueueOrder.lean`
-/

end Mettapedia.Languages.ProcessCalculi.MORK.ByteOrderRefinement
