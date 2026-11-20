import Mettapedia.Languages.HOLLight.RuleModuleComponents

/-!
# The bindings of the HOLR stream reader

The HOLR stream reader is a rule module (module `HOLRStream`, theory `Format`, built from the
modules `ByteScalars`, `ByteDecode`, `ByteArithmetic`, `ByteRecords` and `HOLREquality`) compiled
to C.  Fifteen of its judgments are answered by generic C components, the blocks of its binding
table, and its schema lookup is kept by a memo; the rules stay the contract.  This file transcribes
the rules of the bound judgments and of every judgment they call, and proves that each block, as
its generated glue calls its component, computes what the rules compute.

* **The data.**  Bits (`Bit`), bytes (`Byte`: `Byte8` of eight bits, the first child most
  significant), binary numerals (`BinNat`: `NatZero`, `NatBit b n` for `2 n + b`), byte strings
  (`Bytes`), the module's `Ordering` (`Cmp`), the LEB fuel, the codec states these judgments use,
  and the sorts of the record schemas.  Their values are `Bit.val`, `BinNat.val`, `Byte.val` and
  `Bytes.toList`.  The canonical numerals (`BinNat.Canonical`) are exactly the numerals
  `BinNat.ofNat v` (`BinNat.canonical_iff`), one for each number; `NatBit Bit0 NatZero` is not one.
* **The judgments.**  Each is an inductive relation with one constructor per rule, named after the
  rule's label, carrying the rule's variables in the order the rule binds them and then the results
  of its nested calls; its premises are the nested calls in call-by-value order (the innermost
  first, arguments from left to right, as the compiled rules call them).  The transcription was
  checked rule by rule against the module text and against the rules' wire rows (the variables and
  their order).  For each judgment: the function its rules compute and the equivalence with it on
  every input (`*_iff_fn`); the relation holds exactly for the specified result on the stated
  domain (`*_iff`); a result exists on the domain (`*_total`); at most one result on every input
  (`*_functional`).  The domains: `MakeNatBit`, `CompareBits`, `NatCompare`, `NatInc`, `NatAdd`,
  `BitXor`, `NatXor`, `NatMultiply`, `PackByte`, `ByteLength`, `BytesEqual`, `BytesEqualNext`,
  `ReadULEB62`, `LebRead`, `FNV`, `FNVFrom`, `FNVByte`, `LookupSchema` and `SelectSchema` have one
  result on every input, and their specification is stated on numerals `ofNat v` where it is about
  numbers (`NatCompare` is not the order of the numbers on non-canonical numerals); `NatPred` has a
  result exactly on the numerals of positive numbers (no rule for `NatZero`); `NatTrim` on every
  numeral once its width is canonical; `NatSubtract` and `TakeBytes` on canonical numerals (no
  result through `NatBit Bit0 NatZero`, whose `NatPred` fails); `TakePush` on `Taken` and
  `NeedInput`; `LebJoin` on the states `LebRead` gives (`NeedInput`, `BadInteger`,
  `DecodedWord`).
* **The representations.**  `Byte`: an immediate word, viewed as `Byte8` of its bits from bit 7
  down (`wordKid`, `Byte.ofWord`), built by `RC_MKV_word_1` (`wordMk`); building then viewing and
  viewing then building are identities (`ofWord_wordMk`, `wordMk_kids`).  `Nat`: a natural, viewed
  as `NatZero` or `NatBit (n mod 2) (n div 2)` (`binTag_eq_natZero_iff`, `binView`), built by
  `RC_MK2_binary_5`, which stops the run on `NatBit Bit0 NatZero` and at `2 ^ 20` bits
  (`binMk2_eq_none_iff`) and otherwise builds `NatBit b` over its argument (`binMk2_read`).
  `Bytes`: a slice of the run's input (`start << 31 | end`, `slMake_fields`) or an interned string
  (`Slice`); a value's content is its `rc_sl_length` bytes from `rc_sl_data` (`content`); the views
  (`readBytes_view`, `content_rest`), the empty value (`slNil_spec`), the builder in both its
  branches (`content_slCons`, `slCons_imm_branch`, `slCons_copy_branch`, `readBytes_slCons`),
  `rc_sl_take`, `rc_sl_drop` and `rc_sl_equal` (`content_slTake`, `content_slDrop`,
  `slEqual_iff`) keep the content as stated, and every value they make is valid.
* **The blocks.**  `rc_bind_0` ... `rc_bind_14`: `cMakeNatBit_binding`, `natPred_binding` (the
  C's `NULL` is the rules' lack of a result), `natCompare_binding`, `natInc_binding`,
  `natAdd_binding`, `natXor_binding`, `natMultiply_binding`, `natTrim_binding`,
  `natSubtract_binding`, `packByte_binding`, `byteLength_binding`, `takeBytes_binding`,
  `bytesEqual_binding`, `readULEB62_binding` (the whole ULEB62 rule set against the loop: input
  ending first, the ninth byte above six bits, a last byte `0` after the first, the value;
  `ulebLoop_eq`) and `fnv_binding` (`((h xor b) * prime) mod 2 ^ 64` from the basis; the empty
  string gives the basis); and where each block stops the run (`cMakeNatBit_eq_none_iff`,
  `bnSucc_eq_none_iff`, `bnAdd_eq_none_iff`, `bnMul_eq_none_iff`, `cPackByte_eq_none_iff`).
  `LookupSchema` is a function of its arguments, so its memo answers every call with the rules'
  one result (`lookupSchema_memo_sound`, through `memo2_sound` of `RuleModuleComponents`).
* **Where the C stops the run.**  As the contract of `rc_bignat.h` states, a number above
  `2 ^ 20` bits stops the run, and so does a product whose two factors have more than `16384`
  64-bit limbs together, even when the product would fit (`bnMul_eq_none_iff`; the instance
  `2 ^ 524288 * 2 ^ 524224`, below `bnLimit`, in `bnMul_refuses_below_bnLimit`).  A stopped run
  never answers.
* **The probes.**  Lines 2, 3, 43, 45, 53, 54, 55, 77, 82, 191, 355, 374, 449, 468, 567, 579, 590,
  601, 612, 623, 634, 645, 650, 651, 656, 667, 678, 691, 699, 700, 701, 702 and 703 of `probe.txt`
  (byte strings built with the module's constructors, interned strings), and lines 711 to 750
  (slices of a registered input, at the offsets `0`, `3`, `6`, `9`, `12`: the slice branch) are
  checked on the models by `decide`, and several through the binding theorems on the rules
  (section `Examples`).

What the models leave out.

* A word of the sort `Nat` is modelled by the number it holds.  That an immediate holds a number
  below `2 ^ 62` and an interned magnitude the little-endian bytes of a larger one with no high
  zero byte, so that every number has one word (and the pointer test of `rc_bn_cmp` holds only of
  equal numbers), and that the limb loops of `rc_bignat.c` compute the value each model states for
  its branch, are trusted.  The models keep the C's branches where they decide whether the run
  stops (`mag_value`, the limb count of `rc_bn_mul`, the immediate cases).
* Words are numbers: `uint64_t` arithmetic is modelled where it could wrap (the shifts of the uleb
  loop, modulo `2 ^ 64`, shown not to wrap; the FNV product, modulo `2 ^ 64` as the C wraps it).
* The run's input is a list of bytes, and that a slice is used only while that input is the run's
  input is trusted (the contract of `rc_slices.h`).  An interned string is its list of bytes.
  Running out of memory, and `rc_intern_bytes` stopping the run beyond `2 ^ 32 - 1` bytes, are not
  modelled; `takeBytes_binding` assumes a length below `2 ^ 64`, which every value the C makes has.
* The keys of the memo are values; the C compares argument words, which for an immediate byte and
  an interned schema list are equal exactly on equal values (`interning_eq_iff`).
* The compiled rules of the other judgments are not modelled here; the view theorems are what they
  rely on.  A refusal (`none`, except for `bnPred`) stops the run; it is never an answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModuleReader

/-! ## The module's data -/

/-- Sort `Bit`. -/
inductive Bit
  /-- `Bit0`. -/
  | bit0
  /-- `Bit1`. -/
  | bit1
  deriving DecidableEq, Repr

/-- Sort `Byte`: `Byte8` of eight bits, the first child the most significant. -/
inductive Byte
  /-- `Byte8`. -/
  | byte8 (b7 b6 b5 b4 b3 b2 b1 b0 : Bit)
  deriving DecidableEq, Repr

/-- Sort `Nat` of the module: binary numerals, the least significant bit first. -/
inductive BinNat
  /-- `NatZero`. -/
  | zero
  /-- `NatBit`: `NatBit b n` stands for `2 n + b`. -/
  | bit (b : Bit) (n : BinNat)
  deriving DecidableEq, Repr

/-- Sort `Bytes`. -/
inductive Bytes
  /-- `BNil`. -/
  | nil
  /-- `BCons`. -/
  | cons (b : Byte) (xs : Bytes)
  deriving DecidableEq, Repr

/-- Sort `Ordering` (not Lean's `Ordering`). -/
inductive Cmp
  /-- `Less`. -/
  | less
  /-- `Equal`. -/
  | equal
  /-- `Greater`. -/
  | greater
  deriving DecidableEq, Repr

/-- Sort `LebFuel`. -/
inductive LebFuel
  /-- `LebLast`. -/
  | last
  /-- `LebMore`. -/
  | more (limit : LebFuel)
  deriving DecidableEq, Repr

/-- Sort `CodecState`: the constructors that the judgments below produce or take, and
`LimitExceeded`, on which `LebJoin` and `TakePush` have no rule. -/
inductive CodecState
  /-- `DecodedWord`. -/
  | decodedWord (n : BinNat) (rest : Bytes)
  /-- `NeedInput`. -/
  | needInput
  /-- `BadInteger`. -/
  | badInteger
  /-- `LimitExceeded`. -/
  | limitExceeded
  /-- `Taken`: the bytes taken and the rest. -/
  | taken (pre rest : Bytes)
  deriving DecidableEq, Repr

/-- Sort `FieldKind`. -/
inductive FieldKind
  /-- `WordField`. -/
  | word
  /-- `BytesField`. -/
  | bytes
  /-- `WordsField`. -/
  | words
  /-- `PairsField`. -/
  | pairs
  deriving DecidableEq, Repr

/-- Sort `FieldLayout`. -/
inductive FieldLayout
  /-- `FieldsEnd`. -/
  | fieldsEnd
  /-- `FieldNext`. -/
  | fieldNext (kind : FieldKind) (rest : FieldLayout)
  deriving DecidableEq, Repr

/-- Sort `Schema`. -/
inductive Schema
  /-- `RecordSchema`: an opcode and the layout of its fields. -/
  | recordSchema (tag : Byte) (fields : FieldLayout)
  deriving DecidableEq, Repr

/-- Sort `Schemas`. -/
inductive Schemas
  /-- `SchemasNil`. -/
  | nil
  /-- `SchemasCons`. -/
  | cons (s : Schema) (rest : Schemas)
  deriving DecidableEq, Repr

/-- Sort `FoundLayout`. -/
inductive FoundLayout
  /-- `NoLayout`. -/
  | noLayout
  /-- `FoundLayout`. -/
  | foundLayout (fields : FieldLayout)
  deriving DecidableEq, Repr

/-! ## Values -/

namespace Bit

/-- The value of a bit. -/
def val : Bit → Nat
  | bit0 => 0
  | bit1 => 1

/-- The bit that is the low bit of a number. -/
def ofLow (v : Nat) : Bit := if v % 2 = 1 then bit1 else bit0

@[simp] theorem val_bit0 : bit0.val = 0 := rfl

@[simp] theorem val_bit1 : bit1.val = 1 := rfl

theorem val_le_one (b : Bit) : b.val ≤ 1 := by
  cases b <;> decide

@[simp] theorem val_ofLow (v : Nat) : (ofLow v).val = v % 2 := by
  unfold ofLow
  split
  · rename_i h
    rw [h]
    rfl
  · rename_i h
    show 0 = v % 2
    omega

@[simp] theorem ofLow_val (b : Bit) : ofLow b.val = b := by
  cases b <;> rfl

theorem val_injective {a b : Bit} (h : a.val = b.val) : a = b := by
  rw [← ofLow_val a, ← ofLow_val b, h]

end Bit

/-- The order of two numbers as the module's `Ordering`. -/
def Cmp.ofNats (x y : Nat) : Cmp := if x < y then .less else if x = y then .equal else .greater

namespace BinNat

/-- The number a numeral stands for. -/
def val : BinNat → Nat
  | zero => 0
  | bit b n => 2 * n.val + b.val

@[simp] theorem val_zero : zero.val = 0 := rfl

@[simp] theorem val_bit (b : Bit) (n : BinNat) : (bit b n).val = 2 * n.val + b.val := rfl

/-- The numeral of a list of bits, the least significant first: how the rules write a literal. -/
def ofBits : List Bit → BinNat
  | [] => zero
  | b :: bs => bit b (ofBits bs)

/-- `ofNat` with a fuel, so that it is structural and the kernel evaluates it. -/
def ofNatAux : Nat → Nat → BinNat
  | 0, _ => zero
  | fuel + 1, v => if v = 0 then zero else bit (Bit.ofLow v) (ofNatAux fuel (v / 2))

/-- The canonical numeral of a number: `NatZero` for `0`, otherwise its low bit over the numeral
of its half. -/
def ofNat (v : Nat) : BinNat := ofNatAux v v

theorem ofNatAux_congr : ∀ (f g v : Nat), v ≤ f → v ≤ g → ofNatAux f v = ofNatAux g v
  | 0, g, v, hf, _ => by
    obtain rfl : v = 0 := by omega
    cases g <;> rfl
  | f + 1, 0, v, _, hg => by
    obtain rfl : v = 0 := by omega
    rfl
  | f + 1, g + 1, v, hf, hg => by
    simp only [ofNatAux]
    split
    · rfl
    · rw [ofNatAux_congr f g (v / 2) (by omega) (by omega)]

theorem ofNat_eq (v : Nat) :
    ofNat v = if v = 0 then zero else bit (Bit.ofLow v) (ofNat (v / 2)) := by
  unfold ofNat
  cases v with
  | zero => rfl
  | succ w =>
    rw [if_neg (Nat.succ_ne_zero w)]
    simp only [ofNatAux, if_neg (Nat.succ_ne_zero w)]
    rw [ofNatAux_congr w ((w + 1) / 2) ((w + 1) / 2) (by omega) (Nat.le_refl _)]

@[simp] theorem ofNat_zero : ofNat 0 = zero := rfl

/-- The view of a nonzero number: its low bit over its half. -/
theorem ofNat_of_ne_zero {v : Nat} (h : v ≠ 0) : ofNat v = bit (Bit.ofLow v) (ofNat (v / 2)) := by
  rw [ofNat_eq, if_neg h]

/-- `NatBit b (ofNat v)` is the numeral of `2 v + b`, unless it is `NatBit Bit0 NatZero`. -/
theorem ofNat_two_mul_add {v : Nat} {b : Bit} (h : v ≠ 0 ∨ b = .bit1) :
    ofNat (2 * v + b.val) = bit b (ofNat v) := by
  have hb := b.val_le_one
  have hne : 2 * v + b.val ≠ 0 := by
    rcases h with h | rfl
    · omega
    · simp
  rw [ofNat_of_ne_zero hne]
  have e1 : Bit.ofLow (2 * v + b.val) = b := by
    cases b with
    | bit0 =>
      unfold Bit.ofLow
      rw [if_neg (by simp only [Bit.val_bit0]; omega)]
    | bit1 =>
      unfold Bit.ofLow
      rw [if_pos (by simp only [Bit.val_bit1]; omega)]
  have e2 : (2 * v + b.val) / 2 = v := by omega
  rw [e1, e2]

@[simp] theorem val_ofNat (v : Nat) : (ofNat v).val = v := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases hv : v = 0
    · subst hv
      rfl
    · rw [ofNat_of_ne_zero hv, val_bit, Bit.val_ofLow, ih (v / 2) (by omega)]
      omega

/-- The canonical numerals: those that `MakeNatBit` builds from `NatZero`; exactly the numerals
whose most significant bit is `Bit1`, and exactly the numerals `ofNat v`. -/
inductive Canonical : BinNat → Prop
  /-- `NatZero`. -/
  | zero : Canonical zero
  /-- `NatBit Bit1 n` over a canonical `n`. -/
  | one {n : BinNat} : Canonical n → Canonical (bit .bit1 n)
  /-- `NatBit Bit0 n` over a canonical `n` other than `NatZero`. -/
  | even {b : Bit} {n : BinNat} : Canonical (bit b n) → Canonical (bit .bit0 (bit b n))

theorem Canonical.val_pos : ∀ {n : BinNat}, Canonical n → n ≠ .zero → 0 < n.val
  | _, .zero, h => absurd rfl h
  | _, .one _, _ => by
    simp only [val_bit, Bit.val_bit1]
    omega
  | _, .even h, _ => by
    have := h.val_pos (by simp)
    simp only [val_bit, Bit.val_bit0] at this ⊢
    omega

theorem Canonical.of_bit {b : Bit} {n : BinNat} (h : Canonical (bit b n)) : Canonical n := by
  cases h with
  | one h => exact h
  | even h => exact h

/-- `NatBit b m` is canonical when `m` is, unless it is `NatBit Bit0 NatZero`. -/
theorem Canonical.bit {b : Bit} {m : BinNat} (hm : m.Canonical) (h : m ≠ .zero ∨ b = .bit1) :
    (BinNat.bit b m).Canonical := by
  cases b with
  | bit1 => exact .one hm
  | bit0 =>
    cases m with
    | zero => simp at h
    | bit c n => exact .even hm

theorem canonical_ofNat (v : Nat) : (ofNat v).Canonical := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    by_cases hv : v = 0
    · subst hv
      exact .zero
    · rw [ofNat_of_ne_zero hv]
      refine (ih (v / 2) (by omega)).bit ?_
      by_cases h2 : v / 2 = 0
      · right
        unfold Bit.ofLow
        rw [if_pos (by omega)]
      · left
        intro h
        have := congrArg val h
        rw [val_ofNat] at this
        exact h2 this

/-- A canonical numeral is the numeral of its number. -/
theorem ofNat_val : ∀ {n : BinNat}, n.Canonical → ofNat n.val = n
  | _, .zero => rfl
  | _, .one h => by rw [val_bit, ofNat_two_mul_add (Or.inr rfl), ofNat_val h]
  | _, .even h => by
    have hp := h.val_pos (by simp)
    rw [val_bit, ofNat_two_mul_add (Or.inl (Nat.pos_iff_ne_zero.mp hp)), ofNat_val h]

theorem canonical_iff {n : BinNat} : n.Canonical ↔ ofNat n.val = n :=
  ⟨ofNat_val, fun h => h ▸ canonical_ofNat _⟩

instance : DecidablePred Canonical := fun _ => decidable_of_iff _ canonical_iff.symm

/-- A canonical numeral with the number `v` is `ofNat v`. -/
theorem eq_ofNat {n : BinNat} {v : Nat} (hc : n.Canonical) (hv : n.val = v) : n = ofNat v := by
  rw [← hv, ofNat_val hc]

theorem ofNat_injective {v w : Nat} (h : ofNat v = ofNat w) : v = w := by
  rw [← val_ofNat v, h, val_ofNat]

@[simp] theorem ofNat_inj {v w : Nat} : ofNat v = ofNat w ↔ v = w :=
  ⟨ofNat_injective, fun h => h ▸ rfl⟩

theorem ofNat_eq_zero_iff {v : Nat} : ofNat v = zero ↔ v = 0 :=
  ⟨fun h => by rw [← val_ofNat v, h]; rfl, fun h => h ▸ rfl⟩

/-- Two canonical numerals with the same number are the same numeral. -/
theorem Canonical.eq_of_val_eq {m n : BinNat} (hm : m.Canonical) (hn : n.Canonical)
    (h : m.val = n.val) : m = n := by
  rw [← ofNat_val hm, ← ofNat_val hn, h]

end BinNat

namespace Byte

/-- The value of a byte. -/
def val : Byte → Nat
  | byte8 b7 b6 b5 b4 b3 b2 b1 b0 =>
    128 * b7.val + 64 * b6.val + 32 * b5.val + 16 * b4.val + 8 * b3.val + 4 * b2.val +
      2 * b1.val + b0.val

theorem val_lt (b : Byte) : b.val < 256 := by
  obtain ⟨b7, b6, b5, b4, b3, b2, b1, b0⟩ := b
  have := b7.val_le_one; have := b6.val_le_one; have := b5.val_le_one; have := b4.val_le_one
  have := b3.val_le_one; have := b2.val_le_one; have := b1.val_le_one; have := b0.val_le_one
  simp only [val]
  omega

end Byte

namespace Bytes

/-- The bytes of a byte string. -/
def toList : Bytes → List Byte
  | nil => []
  | cons b xs => b :: xs.toList

/-- The byte string of a list of bytes. -/
def ofList : List Byte → Bytes
  | [] => nil
  | b :: l => cons b (ofList l)

@[simp] theorem toList_nil : nil.toList = [] := rfl

@[simp] theorem toList_cons (b : Byte) (xs : Bytes) : (cons b xs).toList = b :: xs.toList := rfl

@[simp] theorem ofList_nil : ofList [] = nil := rfl

@[simp] theorem ofList_cons (b : Byte) (l : List Byte) : ofList (b :: l) = cons b (ofList l) := rfl

@[simp] theorem toList_ofList (l : List Byte) : (ofList l).toList = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

@[simp] theorem ofList_toList (xs : Bytes) : ofList xs.toList = xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [ih]

end Bytes

open BinNat (ofNat val_ofNat canonical_ofNat)

/-! ## Arithmetic on binary numerals

Each judgment is an inductive relation with one constructor per rule, named after the rule's label
and carrying the rule's variables, in the order the rule binds them, then the results of its
nested calls; the premises are the nested calls in the order call-by-value evaluates them (the
innermost first, the arguments from left to right, as the compiled rules call them); the last
index is the rule's result.  Beside each judgment, the function its rules compute
(`makeNatBit`, `natPred`, ...), which the relation is equivalent to on every input
(`makeNatBit_iff_fn`, ...). -/

/-! ### `MakeNatBit` -/

/-- `MakeNatBit`. -/
inductive MakeNatBit : Bit → BinNat → BinNat → Prop
  /-- `CanonZero: (MakeNatBit (Bit0) (NatZero)) ~> (NatZero);` -/
  | canonZero : MakeNatBit .bit0 .zero .zero
  /-- `CanonOne: (MakeNatBit (Bit1) n) ~> (NatBit (Bit1) n);` -/
  | canonOne {n : BinNat} : MakeNatBit .bit1 n (.bit .bit1 n)
  /-- `CanonMore: (MakeNatBit (Bit0) (NatBit b n)) ~> (NatBit (Bit0) (NatBit b n));` -/
  | canonMore {b : Bit} {n : BinNat} : MakeNatBit .bit0 (.bit b n) (.bit .bit0 (.bit b n))

/-- What the rules of `MakeNatBit` compute. -/
def makeNatBit : Bit → BinNat → BinNat
  | .bit0, .zero => .zero
  | .bit1, n => .bit .bit1 n
  | .bit0, .bit b n => .bit .bit0 (.bit b n)

theorem makeNatBit_iff_fn {b : Bit} {n r : BinNat} : MakeNatBit b n r ↔ r = makeNatBit b n := by
  constructor
  · rintro ⟨⟩ <;> rfl
  · rintro rfl
    cases b <;> cases n <;> constructor

@[simp] theorem val_makeNatBit (b : Bit) (n : BinNat) :
    (makeNatBit b n).val = 2 * n.val + b.val := by
  cases b <;> cases n <;> rfl

theorem canonical_makeNatBit (b : Bit) {n : BinNat} (h : n.Canonical) :
    (makeNatBit b n).Canonical := by
  cases b with
  | bit1 => exact .one h
  | bit0 =>
    cases n with
    | zero => exact .zero
    | bit c m => exact .even h

theorem makeNatBit_ofNat (b : Bit) (v : Nat) : makeNatBit b (ofNat v) = ofNat (2 * v + b.val) :=
  BinNat.eq_ofNat (canonical_makeNatBit b (canonical_ofNat v)) (by simp)

/-- **`MakeNatBit`** has exactly one result on every bit and numeral; on the numeral of `v` it is
the numeral of `2 v + b`. -/
theorem makeNatBit_iff {b : Bit} {v : Nat} {r : BinNat} :
    MakeNatBit b (ofNat v) r ↔ r = ofNat (2 * v + b.val) := by
  rw [makeNatBit_iff_fn, makeNatBit_ofNat]

theorem makeNatBit_total (b : Bit) (n : BinNat) : ∃ r, MakeNatBit b n r :=
  ⟨_, makeNatBit_iff_fn.mpr rfl⟩

theorem makeNatBit_functional {b : Bit} {n r r' : BinNat} (h : MakeNatBit b n r)
    (h' : MakeNatBit b n r') : r = r' :=
  (makeNatBit_iff_fn.mp h).trans (makeNatBit_iff_fn.mp h').symm

/-! ### `NatPred` -/

/-- `NatPred`: no rule for `NatZero`. -/
inductive NatPred : BinNat → BinNat → Prop
  /-- `PredOdd: (NatPred (NatBit (Bit1) n)) ~> (MakeNatBit (Bit0) n);` -/
  | predOdd {n r : BinNat} : MakeNatBit .bit0 n r → NatPred (.bit .bit1 n) r
  /-- `PredEven: (NatPred (NatBit (Bit0) n)) ~> (NatBit (Bit1) (NatPred n));` -/
  | predEven {n m : BinNat} : NatPred n m → NatPred (.bit .bit0 n) (.bit .bit1 m)

/-- What the rules of `NatPred` compute; `none` where no rule applies. -/
def natPred : BinNat → Option BinNat
  | .zero => none
  | .bit .bit1 n => some (makeNatBit .bit0 n)
  | .bit .bit0 n => (natPred n).map (.bit .bit1)

theorem natPred_iff_fn {n r : BinNat} : NatPred n r ↔ natPred n = some r := by
  constructor
  · intro h
    induction h with
    | predOdd h => rw [makeNatBit_iff_fn.mp h]; rfl
    | predEven _ ih => simp [natPred, ih]
  · intro h
    induction n generalizing r with
    | zero => simp [natPred] at h
    | bit b n ih =>
      cases b with
      | bit1 =>
        simp only [natPred, Option.some.injEq] at h
        subst h
        exact .predOdd (makeNatBit_iff_fn.mpr rfl)
      | bit0 =>
        simp only [natPred, Option.map_eq_some_iff] at h
        obtain ⟨m, hm, rfl⟩ := h
        exact .predEven (ih hm)

/-- On every numeral, `natPred` answers exactly when the number is positive, and then the numeral
it answers stands for one less. -/
theorem natPred_val : ∀ {n p : BinNat}, natPred n = some p → 0 < n.val ∧ p.val = n.val - 1
  | .zero, _, h => by simp [natPred] at h
  | .bit .bit1 n, p, h => by
    simp only [natPred, Option.some.injEq] at h
    subst h
    simp
  | .bit .bit0 n, p, h => by
    simp only [natPred, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    have := natPred_val hm
    simp only [BinNat.val_bit, Bit.val_bit0, Bit.val_bit1]
    omega

theorem natPred_eq_none_iff : ∀ {n : BinNat}, natPred n = none ↔ n.val = 0
  | .zero => by simp [natPred]
  | .bit .bit1 n => by simp [natPred]
  | .bit .bit0 n => by
    simp only [natPred, Option.map_eq_none_iff, BinNat.val_bit, Bit.val_bit0]
    rw [natPred_eq_none_iff]
    omega

theorem canonical_natPred : ∀ {n p : BinNat}, n.Canonical → natPred n = some p → p.Canonical
  | .zero, _, _, h => by simp [natPred] at h
  | .bit .bit1 n, p, hc, h => by
    simp only [natPred, Option.some.injEq] at h
    subst h
    exact canonical_makeNatBit _ hc.of_bit
  | .bit .bit0 n, p, hc, h => by
    simp only [natPred, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    exact .one (canonical_natPred hc.of_bit hm)

theorem natPred_ofNat (v : Nat) :
    natPred (ofNat v) = if v = 0 then none else some (ofNat (v - 1)) := by
  split
  · rename_i hv
    exact natPred_eq_none_iff.mpr (by simp [hv])
  · rename_i hv
    cases h : natPred (ofNat v) with
    | none => exact absurd (by simpa using natPred_eq_none_iff.mp h) hv
    | some p =>
      have := natPred_val h
      rw [BinNat.eq_ofNat (canonical_natPred (canonical_ofNat v) h) (by simpa using this.2)]

/-- **`NatPred`**: on the numeral of `v`, a result exactly when `v > 0`, the numeral of `v - 1`. -/
theorem natPred_iff {v : Nat} {r : BinNat} :
    NatPred (ofNat v) r ↔ 0 < v ∧ r = ofNat (v - 1) := by
  rw [natPred_iff_fn, natPred_ofNat]
  split
  · rename_i hv
    simp [hv]
  · rename_i hv
    simp only [Option.some.injEq]
    constructor
    · intro h
      exact ⟨by omega, h.symm⟩
    · intro h
      exact h.2.symm

/-- `NatPred` has a result exactly on the numerals that stand for a positive number. -/
theorem natPred_total {n : BinNat} (h : 0 < n.val) : ∃ r, NatPred n r := by
  cases hp : natPred n with
  | none => exact absurd (natPred_eq_none_iff.mp hp) (by omega)
  | some p => exact ⟨p, natPred_iff_fn.mpr hp⟩

theorem natPred_zero_none (r : BinNat) : ¬ NatPred .zero r := nofun

theorem natPred_functional {n r r' : BinNat} (h : NatPred n r) (h' : NatPred n r') : r = r' := by
  rw [natPred_iff_fn] at h h'
  exact Option.some.inj (h.symm.trans h')

/-! ### `CompareBits` and `NatCompare` -/

/-- `CompareBits`. -/
inductive CompareBits : Bit → Bit → Cmp → Cmp → Prop
  /-- `CompareHigherLess: (CompareBits a b (Less)) ~> (Less);` -/
  | compareHigherLess {a b : Bit} : CompareBits a b .less .less
  /-- `CompareHigherGreater: (CompareBits a b (Greater)) ~> (Greater);` -/
  | compareHigherGreater {a b : Bit} : CompareBits a b .greater .greater
  /-- `CompareEqualZero: (CompareBits (Bit0) (Bit0) (Equal)) ~> (Equal);` -/
  | compareEqualZero : CompareBits .bit0 .bit0 .equal .equal
  /-- `CompareEqualOne: (CompareBits (Bit1) (Bit1) (Equal)) ~> (Equal);` -/
  | compareEqualOne : CompareBits .bit1 .bit1 .equal .equal
  /-- `CompareLowLess: (CompareBits (Bit0) (Bit1) (Equal)) ~> (Less);` -/
  | compareLowLess : CompareBits .bit0 .bit1 .equal .less
  /-- `CompareLowGreater: (CompareBits (Bit1) (Bit0) (Equal)) ~> (Greater);` -/
  | compareLowGreater : CompareBits .bit1 .bit0 .equal .greater

/-- What the rules of `CompareBits` compute. -/
def compareBits : Bit → Bit → Cmp → Cmp
  | _, _, .less => .less
  | _, _, .greater => .greater
  | .bit0, .bit0, .equal => .equal
  | .bit1, .bit1, .equal => .equal
  | .bit0, .bit1, .equal => .less
  | .bit1, .bit0, .equal => .greater

/-- **`CompareBits`** has exactly one result on every input. -/
theorem compareBits_iff {a b : Bit} {c r : Cmp} : CompareBits a b c r ↔ r = compareBits a b c := by
  constructor
  · rintro ⟨⟩ <;> rfl
  · rintro rfl
    cases a <;> cases b <;> cases c <;> constructor

theorem compareBits_total (a b : Bit) (c : Cmp) : ∃ r, CompareBits a b c r :=
  ⟨_, compareBits_iff.mpr rfl⟩

theorem compareBits_functional {a b : Bit} {c r r' : Cmp} (h : CompareBits a b c r)
    (h' : CompareBits a b c r') : r = r' :=
  (compareBits_iff.mp h).trans (compareBits_iff.mp h').symm

/-- The higher bits decide, then the low bits. -/
theorem compareBits_ofNats (a b : Bit) (x y : Nat) :
    compareBits a b (Cmp.ofNats x y) = Cmp.ofNats (2 * x + a.val) (2 * y + b.val) := by
  have ha := a.val_le_one
  have hb := b.val_le_one
  unfold Cmp.ofNats
  by_cases h₁ : x < y
  · rw [if_pos h₁, if_pos (by omega)]
    rfl
  · by_cases h₂ : x = y
    · subst h₂
      rw [if_neg h₁, if_pos rfl]
      cases a <;> cases b <;> simp [compareBits]
    · rw [if_neg h₁, if_neg h₂, if_neg (by omega), if_neg (by omega)]
      rfl

/-- `NatCompare`. -/
inductive NatCompare : BinNat → BinNat → Cmp → Prop
  /-- `CompareZero: (NatCompare (NatZero) (NatZero)) ~> (Equal);` -/
  | compareZero : NatCompare .zero .zero .equal
  /-- `CompareLeftZero: (NatCompare (NatZero) (NatBit b n)) ~> (Less);` -/
  | compareLeftZero {b : Bit} {n : BinNat} : NatCompare .zero (.bit b n) .less
  /-- `CompareRightZero: (NatCompare (NatBit b n) (NatZero)) ~> (Greater);` -/
  | compareRightZero {b : Bit} {n : BinNat} : NatCompare (.bit b n) .zero .greater
  /-- `CompareMore: (NatCompare (NatBit a n) (NatBit b m)) ~> (CompareBits a b (NatCompare n m));` -/
  | compareMore {a : Bit} {n : BinNat} {b : Bit} {m : BinNat} {c r : Cmp} :
      NatCompare n m c → CompareBits a b c r → NatCompare (.bit a n) (.bit b m) r

/-- What the rules of `NatCompare` compute. -/
def natCompare : BinNat → BinNat → Cmp
  | .zero, .zero => .equal
  | .zero, .bit _ _ => .less
  | .bit _ _, .zero => .greater
  | .bit a n, .bit b m => compareBits a b (natCompare n m)

theorem natCompare_iff_fn {m n : BinNat} {r : Cmp} : NatCompare m n r ↔ r = natCompare m n := by
  constructor
  · intro h
    induction h with
    | compareZero => rfl
    | compareLeftZero => rfl
    | compareRightZero => rfl
    | compareMore _ h ih => rw [compareBits_iff.mp h, ih]; rfl
  · rintro rfl
    induction m generalizing n with
    | zero => cases n <;> constructor
    | bit a m ih =>
      cases n with
      | zero => exact .compareRightZero
      | bit b n => exact .compareMore (ih (n := n)) (compareBits_iff.mpr rfl)

/-- On canonical numerals, `natCompare` is the order of the numbers. -/
theorem natCompare_canonical : ∀ {m n : BinNat}, m.Canonical → n.Canonical →
    natCompare m n = Cmp.ofNats m.val n.val
  | .zero, .zero, _, _ => rfl
  | .zero, .bit b n, _, hn => by
    have := hn.val_pos (by simp)
    unfold Cmp.ofNats
    rw [if_pos (by simpa using this)]
    rfl
  | .bit a m, .zero, hm, _ => by
    have := hm.val_pos (by simp)
    unfold Cmp.ofNats
    rw [if_neg (by rw [BinNat.val_zero]; omega), if_neg (by rw [BinNat.val_zero]; omega)]
    rfl
  | .bit a m, .bit b n, hm, hn => by
    simp only [natCompare]
    rw [natCompare_canonical hm.of_bit hn.of_bit, compareBits_ofNats]
    rfl

/-- **`NatCompare`** on the numerals of two numbers is the order of the numbers. -/
theorem natCompare_iff {v w : Nat} {r : Cmp} :
    NatCompare (ofNat v) (ofNat w) r ↔ r = Cmp.ofNats v w := by
  rw [natCompare_iff_fn, natCompare_canonical (canonical_ofNat v) (canonical_ofNat w),
    val_ofNat, val_ofNat]

theorem natCompare_total (m n : BinNat) : ∃ r, NatCompare m n r := ⟨_, natCompare_iff_fn.mpr rfl⟩

theorem natCompare_functional {m n : BinNat} {r r' : Cmp} (h : NatCompare m n r)
    (h' : NatCompare m n r') : r = r' :=
  (natCompare_iff_fn.mp h).trans (natCompare_iff_fn.mp h').symm

/-! ### `NatInc` -/

/-- `NatInc`. -/
inductive NatInc : BinNat → BinNat → Prop
  /-- `IncZero: (NatInc (NatZero)) ~> (NatBit (Bit1) (NatZero));` -/
  | incZero : NatInc .zero (.bit .bit1 .zero)
  /-- `IncEven: (NatInc (NatBit (Bit0) n)) ~> (NatBit (Bit1) n);` -/
  | incEven {n : BinNat} : NatInc (.bit .bit0 n) (.bit .bit1 n)
  /-- `IncOdd: (NatInc (NatBit (Bit1) n)) ~> (NatBit (Bit0) (NatInc n));` -/
  | incOdd {n m : BinNat} : NatInc n m → NatInc (.bit .bit1 n) (.bit .bit0 m)

/-- What the rules of `NatInc` compute. -/
def natInc : BinNat → BinNat
  | .zero => .bit .bit1 .zero
  | .bit .bit0 n => .bit .bit1 n
  | .bit .bit1 n => .bit .bit0 (natInc n)

theorem natInc_iff_fn {n r : BinNat} : NatInc n r ↔ r = natInc n := by
  constructor
  · intro h
    induction h with
    | incZero => rfl
    | incEven => rfl
    | incOdd _ ih => rw [ih]; rfl
  · rintro rfl
    induction n with
    | zero => exact .incZero
    | bit b n ih =>
      cases b with
      | bit0 => exact .incEven
      | bit1 => exact .incOdd ih

@[simp] theorem val_natInc : ∀ n : BinNat, (natInc n).val = n.val + 1
  | .zero => rfl
  | .bit .bit0 n => by simp [natInc]
  | .bit .bit1 n => by
    simp only [natInc, BinNat.val_bit, val_natInc n, Bit.val_bit0, Bit.val_bit1]
    omega

theorem natInc_ne_zero : ∀ n : BinNat, natInc n ≠ .zero
  | .zero => by simp [natInc]
  | .bit .bit0 _ => by simp [natInc]
  | .bit .bit1 _ => by simp [natInc]

theorem canonical_natInc : ∀ {n : BinNat}, n.Canonical → (natInc n).Canonical
  | .zero, _ => .one .zero
  | .bit .bit0 _, h => .one h.of_bit
  | .bit .bit1 n, h => (canonical_natInc h.of_bit).bit (Or.inl (natInc_ne_zero n))

theorem natInc_ofNat (v : Nat) : natInc (ofNat v) = ofNat (v + 1) :=
  BinNat.eq_ofNat (canonical_natInc (canonical_ofNat v)) (by simp)

/-- **`NatInc`** on the numeral of `v` is the numeral of `v + 1`. -/
theorem natInc_iff {v : Nat} {r : BinNat} : NatInc (ofNat v) r ↔ r = ofNat (v + 1) := by
  rw [natInc_iff_fn, natInc_ofNat]

theorem natInc_total (n : BinNat) : ∃ r, NatInc n r := ⟨_, natInc_iff_fn.mpr rfl⟩

theorem natInc_functional {n r r' : BinNat} (h : NatInc n r) (h' : NatInc n r') : r = r' :=
  (natInc_iff_fn.mp h).trans (natInc_iff_fn.mp h').symm

/-! ### `NatAdd` -/

/-- `NatAdd`. -/
inductive NatAdd : BinNat → BinNat → BinNat → Prop
  /-- `AddZero: (NatAdd (NatZero) (NatZero)) ~> (NatZero);` -/
  | addZero : NatAdd .zero .zero .zero
  /-- `AddLeftZero: (NatAdd (NatZero) (NatBit b n)) ~> (NatBit b n);` -/
  | addLeftZero {b : Bit} {n : BinNat} : NatAdd .zero (.bit b n) (.bit b n)
  /-- `AddRightZero: (NatAdd (NatBit b n) (NatZero)) ~> (NatBit b n);` -/
  | addRightZero {b : Bit} {n : BinNat} : NatAdd (.bit b n) .zero (.bit b n)
  /-- `AddEvenEven: (NatAdd (NatBit (Bit0) n) (NatBit (Bit0) m)) ~> (MakeNatBit (Bit0) (NatAdd n m));` -/
  | addEvenEven {n m s r : BinNat} :
      NatAdd n m s → MakeNatBit .bit0 s r → NatAdd (.bit .bit0 n) (.bit .bit0 m) r
  /-- `AddEvenOdd: (NatAdd (NatBit (Bit0) n) (NatBit (Bit1) m)) ~> (NatBit (Bit1) (NatAdd n m));` -/
  | addEvenOdd {n m s : BinNat} : NatAdd n m s → NatAdd (.bit .bit0 n) (.bit .bit1 m) (.bit .bit1 s)
  /-- `AddOddEven: (NatAdd (NatBit (Bit1) n) (NatBit (Bit0) m)) ~> (NatBit (Bit1) (NatAdd n m));` -/
  | addOddEven {n m s : BinNat} : NatAdd n m s → NatAdd (.bit .bit1 n) (.bit .bit0 m) (.bit .bit1 s)
  /-- `AddOddOdd: (NatAdd (NatBit (Bit1) n) (NatBit (Bit1) m)) ~>
  (NatBit (Bit0) (NatInc (NatAdd n m)));` -/
  | addOddOdd {n m s t : BinNat} :
      NatAdd n m s → NatInc s t → NatAdd (.bit .bit1 n) (.bit .bit1 m) (.bit .bit0 t)

/-- What the rules of `NatAdd` compute. -/
def natAdd : BinNat → BinNat → BinNat
  | .zero, .zero => .zero
  | .zero, .bit b n => .bit b n
  | .bit b n, .zero => .bit b n
  | .bit .bit0 n, .bit .bit0 m => makeNatBit .bit0 (natAdd n m)
  | .bit .bit0 n, .bit .bit1 m => .bit .bit1 (natAdd n m)
  | .bit .bit1 n, .bit .bit0 m => .bit .bit1 (natAdd n m)
  | .bit .bit1 n, .bit .bit1 m => .bit .bit0 (natInc (natAdd n m))

theorem natAdd_iff_fn {m n r : BinNat} : NatAdd m n r ↔ r = natAdd m n := by
  constructor
  · intro h
    induction h with
    | addZero => rfl
    | addLeftZero => rfl
    | addRightZero => rfl
    | addEvenEven _ h ih => rw [makeNatBit_iff_fn.mp h, ih]; rfl
    | addEvenOdd _ ih => rw [ih]; rfl
    | addOddEven _ ih => rw [ih]; rfl
    | addOddOdd _ h ih => rw [natInc_iff_fn.mp h, ih]; rfl
  · rintro rfl
    induction m generalizing n with
    | zero => cases n <;> constructor
    | bit a m ih =>
      cases n with
      | zero => exact .addRightZero
      | bit b n =>
        cases a <;> cases b
        · exact .addEvenEven (ih (n := n)) (makeNatBit_iff_fn.mpr rfl)
        · exact .addEvenOdd (ih (n := n))
        · exact .addOddEven (ih (n := n))
        · exact .addOddOdd (ih (n := n)) (natInc_iff_fn.mpr rfl)

@[simp] theorem val_natAdd : ∀ m n : BinNat, (natAdd m n).val = m.val + n.val
  | .zero, .zero => rfl
  | .zero, .bit _ _ => by simp [natAdd]
  | .bit _ _, .zero => by simp [natAdd]
  | .bit .bit0 m, .bit .bit0 n => by simp [natAdd, val_natAdd m n]; omega
  | .bit .bit0 m, .bit .bit1 n => by simp [natAdd, val_natAdd m n]; omega
  | .bit .bit1 m, .bit .bit0 n => by simp [natAdd, val_natAdd m n]; omega
  | .bit .bit1 m, .bit .bit1 n => by simp [natAdd, val_natAdd m n]; omega

theorem canonical_natAdd : ∀ {m n : BinNat}, m.Canonical → n.Canonical → (natAdd m n).Canonical
  | .zero, .zero, _, _ => .zero
  | .zero, .bit _ _, _, h => h
  | .bit _ _, .zero, h, _ => h
  | .bit .bit0 _, .bit .bit0 _, hm, hn => canonical_makeNatBit _ (canonical_natAdd hm.of_bit hn.of_bit)
  | .bit .bit0 _, .bit .bit1 _, hm, hn => .one (canonical_natAdd hm.of_bit hn.of_bit)
  | .bit .bit1 _, .bit .bit0 _, hm, hn => .one (canonical_natAdd hm.of_bit hn.of_bit)
  | .bit .bit1 _, .bit .bit1 _, hm, hn =>
    (canonical_natInc (canonical_natAdd hm.of_bit hn.of_bit)).bit (Or.inl (natInc_ne_zero _))

theorem natAdd_ofNat (v w : Nat) : natAdd (ofNat v) (ofNat w) = ofNat (v + w) :=
  BinNat.eq_ofNat (canonical_natAdd (canonical_ofNat v) (canonical_ofNat w)) (by simp)

/-- **`NatAdd`** on the numerals of `v` and `w` is the numeral of `v + w`. -/
theorem natAdd_iff {v w : Nat} {r : BinNat} : NatAdd (ofNat v) (ofNat w) r ↔ r = ofNat (v + w) := by
  rw [natAdd_iff_fn, natAdd_ofNat]

theorem natAdd_total (m n : BinNat) : ∃ r, NatAdd m n r := ⟨_, natAdd_iff_fn.mpr rfl⟩

theorem natAdd_functional {m n r r' : BinNat} (h : NatAdd m n r) (h' : NatAdd m n r') : r = r' :=
  (natAdd_iff_fn.mp h).trans (natAdd_iff_fn.mp h').symm

/-! ### `BitXor` and `NatXor` -/

/-- `BitXor`. -/
inductive BitXor : Bit → Bit → Bit → Prop
  /-- `Xor00: (BitXor (Bit0) (Bit0)) ~> (Bit0);` -/
  | xor00 : BitXor .bit0 .bit0 .bit0
  /-- `Xor01: (BitXor (Bit0) (Bit1)) ~> (Bit1);` -/
  | xor01 : BitXor .bit0 .bit1 .bit1
  /-- `Xor10: (BitXor (Bit1) (Bit0)) ~> (Bit1);` -/
  | xor10 : BitXor .bit1 .bit0 .bit1
  /-- `Xor11: (BitXor (Bit1) (Bit1)) ~> (Bit0);` -/
  | xor11 : BitXor .bit1 .bit1 .bit0

/-- What the rules of `BitXor` compute. -/
def bitXor : Bit → Bit → Bit
  | .bit0, .bit0 => .bit0
  | .bit0, .bit1 => .bit1
  | .bit1, .bit0 => .bit1
  | .bit1, .bit1 => .bit0

/-- **`BitXor`** has exactly one result, the exclusive or of the bits. -/
theorem bitXor_iff {a b r : Bit} : BitXor a b r ↔ r = bitXor a b := by
  constructor
  · rintro ⟨⟩ <;> rfl
  · rintro rfl
    cases a <;> cases b <;> constructor

@[simp] theorem val_bitXor (a b : Bit) : (bitXor a b).val = a.val ^^^ b.val := by
  cases a <;> cases b <;> rfl

theorem bitXor_total (a b : Bit) : ∃ r, BitXor a b r := ⟨_, bitXor_iff.mpr rfl⟩

theorem bitXor_functional {a b r r' : Bit} (h : BitXor a b r) (h' : BitXor a b r') : r = r' :=
  (bitXor_iff.mp h).trans (bitXor_iff.mp h').symm

/-- `NatXor`. -/
inductive NatXor : BinNat → BinNat → BinNat → Prop
  /-- `XorZero: (NatXor (NatZero) (NatZero)) ~> (NatZero);` -/
  | xorZero : NatXor .zero .zero .zero
  /-- `XorLeftZero: (NatXor (NatZero) (NatBit b n)) ~> (NatBit b n);` -/
  | xorLeftZero {b : Bit} {n : BinNat} : NatXor .zero (.bit b n) (.bit b n)
  /-- `XorRightZero: (NatXor (NatBit b n) (NatZero)) ~> (NatBit b n);` -/
  | xorRightZero {b : Bit} {n : BinNat} : NatXor (.bit b n) .zero (.bit b n)
  /-- `XorMore: (NatXor (NatBit b n) (NatBit c m)) ~> (MakeNatBit (BitXor b c) (NatXor n m));` -/
  | xorMore {b : Bit} {n : BinNat} {c : Bit} {m : BinNat} {d : Bit} {x r : BinNat} :
      BitXor b c d → NatXor n m x → MakeNatBit d x r → NatXor (.bit b n) (.bit c m) r

/-- What the rules of `NatXor` compute. -/
def natXor : BinNat → BinNat → BinNat
  | .zero, .zero => .zero
  | .zero, .bit b n => .bit b n
  | .bit b n, .zero => .bit b n
  | .bit b n, .bit c m => makeNatBit (bitXor b c) (natXor n m)

theorem natXor_iff_fn {m n r : BinNat} : NatXor m n r ↔ r = natXor m n := by
  constructor
  · intro h
    induction h with
    | xorZero => rfl
    | xorLeftZero => rfl
    | xorRightZero => rfl
    | xorMore h₁ _ h₃ ih => rw [makeNatBit_iff_fn.mp h₃, bitXor_iff.mp h₁, ih]; rfl
  · rintro rfl
    induction m generalizing n with
    | zero => cases n <;> constructor
    | bit b m ih =>
      cases n with
      | zero => exact .xorRightZero
      | bit c n => exact .xorMore (bitXor_iff.mpr rfl) (ih (n := n)) (makeNatBit_iff_fn.mpr rfl)

/-- The exclusive or of `2 x + a` and `2 y + b`, for bits `a` and `b`. -/
theorem xor_two_mul_add (x y : Nat) (a b : Bit) :
    (2 * x + a.val) ^^^ (2 * y + b.val) = 2 * (x ^^^ y) + (a.val ^^^ b.val) := by
  have ha := a.val_le_one
  have hb := b.val_le_one
  have h₁ : ((2 * x + a.val) ^^^ (2 * y + b.val)) / 2 = x ^^^ y := by
    have e := Nat.shiftRight_xor_distrib (i := 1) (a := 2 * x + a.val) (b := 2 * y + b.val)
    simp only [Nat.shiftRight_eq_div_pow, Nat.pow_one] at e
    rw [e]
    congr 1 <;> omega
  have h₂ : ((2 * x + a.val) ^^^ (2 * y + b.val)) % 2 = a.val ^^^ b.val := by
    have e := Nat.xor_mod_two_pow (a := 2 * x + a.val) (b := 2 * y + b.val) (n := 1)
    simp only [Nat.pow_one] at e
    rw [e]
    have e₁ : (2 * x + a.val) % 2 = a.val := by omega
    have e₂ : (2 * y + b.val) % 2 = b.val := by omega
    rw [e₁, e₂]
  have := Nat.div_add_mod ((2 * x + a.val) ^^^ (2 * y + b.val)) 2
  rw [h₁, h₂] at this
  exact this.symm

@[simp] theorem val_natXor : ∀ m n : BinNat, (natXor m n).val = m.val ^^^ n.val
  | .zero, .zero => rfl
  | .zero, .bit b n => by simp [natXor]
  | .bit b n, .zero => by simp [natXor]
  | .bit b n, .bit c m => by
    simp only [natXor, val_makeNatBit, val_bitXor, val_natXor n m, BinNat.val_bit]
    rw [xor_two_mul_add]

theorem canonical_natXor : ∀ {m n : BinNat}, m.Canonical → n.Canonical → (natXor m n).Canonical
  | .zero, .zero, _, _ => .zero
  | .zero, .bit _ _, _, h => h
  | .bit _ _, .zero, h, _ => h
  | .bit _ _, .bit _ _, hm, hn => canonical_makeNatBit _ (canonical_natXor hm.of_bit hn.of_bit)

theorem natXor_ofNat (v w : Nat) : natXor (ofNat v) (ofNat w) = ofNat (v ^^^ w) :=
  BinNat.eq_ofNat (canonical_natXor (canonical_ofNat v) (canonical_ofNat w)) (by simp)

/-- **`NatXor`** on the numerals of `v` and `w` is the numeral of their bitwise exclusive or. -/
theorem natXor_iff {v w : Nat} {r : BinNat} : NatXor (ofNat v) (ofNat w) r ↔ r = ofNat (v ^^^ w) := by
  rw [natXor_iff_fn, natXor_ofNat]

theorem natXor_total (m n : BinNat) : ∃ r, NatXor m n r := ⟨_, natXor_iff_fn.mpr rfl⟩

theorem natXor_functional {m n r r' : BinNat} (h : NatXor m n r) (h' : NatXor m n r') : r = r' :=
  (natXor_iff_fn.mp h).trans (natXor_iff_fn.mp h').symm

/-! ### `NatMultiply` -/

/-- `NatMultiply`. -/
inductive NatMultiply : BinNat → BinNat → BinNat → Prop
  /-- `MultiplyZero: (NatMultiply (NatZero) n) ~> (NatZero);` -/
  | multiplyZero {n : BinNat} : NatMultiply .zero n .zero
  /-- `MultiplyEven: (NatMultiply (NatBit (Bit0) n) m) ~> (MakeNatBit (Bit0) (NatMultiply n m));` -/
  | multiplyEven {n m p r : BinNat} :
      NatMultiply n m p → MakeNatBit .bit0 p r → NatMultiply (.bit .bit0 n) m r
  /-- `MultiplyOdd: (NatMultiply (NatBit (Bit1) n) m) ~>
  (NatAdd m (MakeNatBit (Bit0) (NatMultiply n m)));` -/
  | multiplyOdd {n m p q r : BinNat} :
      NatMultiply n m p → MakeNatBit .bit0 p q → NatAdd m q r → NatMultiply (.bit .bit1 n) m r

/-- What the rules of `NatMultiply` compute. -/
def natMultiply : BinNat → BinNat → BinNat
  | .zero, _ => .zero
  | .bit .bit0 n, m => makeNatBit .bit0 (natMultiply n m)
  | .bit .bit1 n, m => natAdd m (makeNatBit .bit0 (natMultiply n m))

theorem natMultiply_iff_fn {m n r : BinNat} : NatMultiply m n r ↔ r = natMultiply m n := by
  constructor
  · intro h
    induction h with
    | multiplyZero => rfl
    | multiplyEven _ h ih => rw [makeNatBit_iff_fn.mp h, ih]; rfl
    | multiplyOdd _ h₂ h₃ ih => rw [natAdd_iff_fn.mp h₃, makeNatBit_iff_fn.mp h₂, ih]; rfl
  · rintro rfl
    induction m with
    | zero => exact .multiplyZero
    | bit b m ih =>
      cases b with
      | bit0 => exact .multiplyEven ih (makeNatBit_iff_fn.mpr rfl)
      | bit1 => exact .multiplyOdd ih (makeNatBit_iff_fn.mpr rfl) (natAdd_iff_fn.mpr rfl)

@[simp] theorem val_natMultiply : ∀ m n : BinNat, (natMultiply m n).val = m.val * n.val
  | .zero, _ => by simp [natMultiply]
  | .bit .bit0 m, n => by
    simp only [natMultiply, val_makeNatBit, val_natMultiply m n, BinNat.val_bit, Bit.val_bit0,
      Nat.add_zero, Nat.mul_assoc]
  | .bit .bit1 m, n => by
    simp only [natMultiply, val_natAdd, val_makeNatBit, val_natMultiply m n, BinNat.val_bit,
      Bit.val_bit0, Bit.val_bit1, Nat.add_zero, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    omega

theorem canonical_natMultiply : ∀ (m : BinNat) {n : BinNat}, n.Canonical →
    (natMultiply m n).Canonical
  | .zero, _, _ => .zero
  | .bit .bit0 m, _, h => canonical_makeNatBit _ (canonical_natMultiply m h)
  | .bit .bit1 m, _, h => canonical_natAdd h (canonical_makeNatBit _ (canonical_natMultiply m h))

theorem natMultiply_ofNat (v w : Nat) : natMultiply (ofNat v) (ofNat w) = ofNat (v * w) :=
  BinNat.eq_ofNat (canonical_natMultiply _ (canonical_ofNat w)) (by simp)

/-- **`NatMultiply`** on the numerals of `v` and `w` is the numeral of `v * w`. -/
theorem natMultiply_iff {v w : Nat} {r : BinNat} :
    NatMultiply (ofNat v) (ofNat w) r ↔ r = ofNat (v * w) := by
  rw [natMultiply_iff_fn, natMultiply_ofNat]

theorem natMultiply_total (m n : BinNat) : ∃ r, NatMultiply m n r := ⟨_, natMultiply_iff_fn.mpr rfl⟩

theorem natMultiply_functional {m n r r' : BinNat} (h : NatMultiply m n r)
    (h' : NatMultiply m n r') : r = r' :=
  (natMultiply_iff_fn.mp h).trans (natMultiply_iff_fn.mp h').symm

/-! ### `NatTrim` -/

/-- `NatTrim`. -/
inductive NatTrim : BinNat → BinNat → BinNat → Prop
  /-- `TrimEnd: (NatTrim (NatZero) n) ~> (NatZero);` -/
  | trimEnd {n : BinNat} : NatTrim .zero n .zero
  /-- `TrimZero: (NatTrim (NatBit b width) (NatZero)) ~> (NatZero);` -/
  | trimZero {b : Bit} {width : BinNat} : NatTrim (.bit b width) .zero .zero
  /-- `TrimMore: (NatTrim (NatBit b width) (NatBit bit n)) ~>
  (MakeNatBit bit (NatTrim (NatPred (NatBit b width)) n));` -/
  | trimMore {b : Bit} {width : BinNat} {bit : Bit} {n p t r : BinNat} :
      NatPred (.bit b width) p → NatTrim p n t → MakeNatBit bit t r →
        NatTrim (.bit b width) (.bit bit n) r

/-- What the rules of `NatTrim` compute; `none` where no rule applies. -/
def natTrim : BinNat → BinNat → Option BinNat
  | .zero, _ => some .zero
  | .bit _ _, .zero => some .zero
  | .bit b w, .bit c n => ((natPred (.bit b w)).bind fun p => natTrim p n).map (makeNatBit c)

theorem natTrim_iff_fn {w n r : BinNat} : NatTrim w n r ↔ natTrim w n = some r := by
  constructor
  · intro h
    induction h with
    | trimEnd => simp [natTrim]
    | trimZero => rfl
    | trimMore h₁ _ h₃ ih =>
      simp only [natTrim, natPred_iff_fn.mp h₁, Option.bind_some, ih, Option.map_some,
        makeNatBit_iff_fn.mp h₃]
  · intro h
    induction n generalizing w r with
    | zero =>
      cases w with
      | zero => simp only [natTrim, Option.some.injEq] at h; subst h; exact .trimEnd
      | bit b w => simp only [natTrim, Option.some.injEq] at h; subst h; exact .trimZero
    | bit c n ih =>
      cases w with
      | zero => simp only [natTrim, Option.some.injEq] at h; subst h; exact .trimEnd
      | bit b w =>
        simp only [natTrim, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
        obtain ⟨t, ⟨p, hp, ht⟩, rfl⟩ := h
        exact .trimMore (natPred_iff_fn.mpr hp) (ih ht) (makeNatBit_iff_fn.mpr rfl)

/-- `(2 a + c) mod 2^(k+1) = 2 (a mod 2^k) + c` for a bit `c`. -/
theorem two_mul_add_mod_two_pow (a c k : Nat) (hc : c < 2) :
    (2 * a + c) % 2 ^ (k + 1) = 2 * (a % 2 ^ k) + c := by
  have hlt := Nat.mod_lt a (Nat.two_pow_pos k)
  have hd := Nat.div_add_mod a (2 ^ k)
  have e : 2 * a + c = 2 ^ (k + 1) * (a / 2 ^ k) + (2 * (a % 2 ^ k) + c) := by
    rw [Nat.pow_succ]
    generalize a / 2 ^ k = q at hd
    generalize a % 2 ^ k = s at hd hlt
    generalize 2 ^ k = P at hd hlt
    subst hd
    rw [Nat.mul_add, Nat.mul_comm P 2, Nat.mul_assoc]
    omega
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt]
  rw [Nat.pow_succ]
  omega

/-- On every input where it has a result, `natTrim w n` is the canonical numeral of
`n mod 2 ^ w`. -/
theorem natTrim_val : ∀ {w n r : BinNat}, natTrim w n = some r →
    r.Canonical ∧ r.val = n.val % 2 ^ w.val
  | .zero, n, r, h => by
    simp only [natTrim, Option.some.injEq] at h
    subst h
    exact ⟨.zero, by simp [Nat.mod_one]⟩
  | .bit b w, .zero, r, h => by
    simp only [natTrim, Option.some.injEq] at h
    subst h
    exact ⟨.zero, by simp⟩
  | .bit b w, .bit c n, r, h => by
    simp only [natTrim, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
    obtain ⟨t, ⟨p, hp, ht⟩, rfl⟩ := h
    obtain ⟨hpos, hpv⟩ := natPred_val hp
    obtain ⟨htc, htv⟩ := natTrim_val ht
    refine ⟨canonical_makeNatBit c htc, ?_⟩
    rw [val_makeNatBit, htv, hpv]
    obtain ⟨k, hk⟩ : ∃ k, (BinNat.bit b w).val = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hk, Nat.add_sub_cancel, BinNat.val_bit c n,
      two_mul_add_mod_two_pow _ _ _ (by have := c.val_le_one; omega)]

/-- On a canonical width, `natTrim` has a result. -/
theorem natTrim_isSome : ∀ {w : BinNat} (n : BinNat), w.Canonical → ∃ r, natTrim w n = some r
  | .zero, n, _ => ⟨_, by cases n <;> rfl⟩
  | .bit _ _, .zero, _ => ⟨_, rfl⟩
  | .bit b w, .bit c n, hw => by
    have hpos := hw.val_pos (by simp)
    cases hp : natPred (.bit b w) with
    | none => exact absurd (natPred_eq_none_iff.mp hp) (by omega)
    | some p =>
      obtain ⟨t, ht⟩ := natTrim_isSome n (canonical_natPred hw hp)
      exact ⟨makeNatBit c t, by simp [natTrim, hp, ht]⟩

theorem natTrim_ofNat (w : Nat) (n : BinNat) : natTrim (ofNat w) n = some (ofNat (n.val % 2 ^ w)) := by
  obtain ⟨r, hr⟩ := natTrim_isSome n (canonical_ofNat w)
  obtain ⟨hc, hv⟩ := natTrim_val hr
  rw [hr, BinNat.eq_ofNat hc hv, val_ofNat]

/-- **`NatTrim`** on the numerals of `w` and `v` is the numeral of `v mod 2 ^ w`; it has a result
on every numeral `n` once the width is canonical. -/
theorem natTrim_iff {w v : Nat} {r : BinNat} :
    NatTrim (ofNat w) (ofNat v) r ↔ r = ofNat (v % 2 ^ w) := by
  rw [natTrim_iff_fn, natTrim_ofNat, val_ofNat, Option.some.injEq]
  exact eq_comm

theorem natTrim_total {w : BinNat} (n : BinNat) (hw : w.Canonical) : ∃ r, NatTrim w n r := by
  obtain ⟨r, hr⟩ := natTrim_isSome n hw
  exact ⟨r, natTrim_iff_fn.mpr hr⟩

theorem natTrim_functional {w n r r' : BinNat} (h : NatTrim w n r) (h' : NatTrim w n r') :
    r = r' := by
  rw [natTrim_iff_fn] at h h'
  exact Option.some.inj (h.symm.trans h')

/-! ### `NatSubtract` -/

/-- `NatSubtract`. -/
inductive NatSubtract : BinNat → BinNat → BinNat → Prop
  /-- `SubtractZero: (NatSubtract (NatZero) n) ~> (NatZero);` -/
  | subtractZero {n : BinNat} : NatSubtract .zero n .zero
  /-- `SubtractRightZero: (NatSubtract (NatBit bit n) (NatZero)) ~> (NatBit bit n);` -/
  | subtractRightZero {bit : Bit} {n : BinNat} : NatSubtract (.bit bit n) .zero (.bit bit n)
  /-- `SubtractMore: (NatSubtract (NatBit bit n) (NatBit other m)) ~>
  (NatSubtract (NatPred (NatBit bit n)) (NatPred (NatBit other m)));` -/
  | subtractMore {bit : Bit} {n : BinNat} {other : Bit} {m p q r : BinNat} :
      NatPred (.bit bit n) p → NatPred (.bit other m) q → NatSubtract p q r →
        NatSubtract (.bit bit n) (.bit other m) r

/-- `NatSubtract` has at most one result on every input. -/
theorem natSubtract_functional {m n r r' : BinNat} (h : NatSubtract m n r)
    (h' : NatSubtract m n r') : r = r' := by
  induction h generalizing r' with
  | subtractZero => cases h'; rfl
  | subtractRightZero => cases h'; rfl
  | subtractMore h₁ h₂ _ ih =>
    cases h' with
    | subtractMore h₁' h₂' h₃' =>
      rw [natPred_functional h₁ h₁', natPred_functional h₂ h₂'] at ih
      exact ih h₃'

/-- Every result of `NatSubtract` on canonical numerals is the numeral of the truncated
difference. -/
theorem natSubtract_sound {m n r : BinNat} (h : NatSubtract m n r) :
    m.Canonical → n.Canonical → r = ofNat (m.val - n.val) := by
  induction h with
  | subtractZero => intro _ _; simp
  | subtractRightZero => intro hm _; rw [BinNat.val_zero, Nat.sub_zero, BinNat.ofNat_val hm]
  | subtractMore h₁ h₂ _ ih =>
    intro hm hn
    have hp := natPred_iff_fn.mp h₁
    have hq := natPred_iff_fn.mp h₂
    rw [ih (canonical_natPred hm hp) (canonical_natPred hn hq), (natPred_val hp).2,
      (natPred_val hq).2]
    congr 1
    have := (natPred_val hp).1
    have := (natPred_val hq).1
    omega

/-- `NatSubtract` derives the numeral of the truncated difference of two numbers. -/
theorem natSubtract_derives (v : Nat) : ∀ w : Nat, NatSubtract (ofNat v) (ofNat w) (ofNat (v - w)) := by
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro w
    by_cases hv : v = 0
    · subst hv
      simpa using (NatSubtract.subtractZero (n := ofNat w))
    · by_cases hw : w = 0
      · subst hw
        rw [Nat.sub_zero, BinNat.ofNat_zero, BinNat.ofNat_of_ne_zero hv]
        exact .subtractRightZero
      · have e₁ := natPred_ofNat v
        have e₂ := natPred_ofNat w
        rw [if_neg hv] at e₁
        rw [if_neg hw] at e₂
        have h := ih (v - 1) (by omega) (w - 1)
        rw [show v - 1 - (w - 1) = v - w by omega] at h
        rw [BinNat.ofNat_of_ne_zero hv, BinNat.ofNat_of_ne_zero hw]
        rw [BinNat.ofNat_of_ne_zero hv] at e₁
        rw [BinNat.ofNat_of_ne_zero hw] at e₂
        exact .subtractMore (natPred_iff_fn.mpr e₁) (natPred_iff_fn.mpr e₂) h

/-- **`NatSubtract`** on the numerals of `v` and `w` is the numeral of `v - w` (`0` when
`w > v`). -/
theorem natSubtract_iff {v w : Nat} {r : BinNat} :
    NatSubtract (ofNat v) (ofNat w) r ↔ r = ofNat (v - w) := by
  constructor
  · intro h
    rw [natSubtract_sound h (canonical_ofNat v) (canonical_ofNat w), val_ofNat, val_ofNat]
  · rintro rfl
    exact natSubtract_derives v w

/-- `NatSubtract` has a result on every pair of canonical numerals. -/
theorem natSubtract_total {m n : BinNat} (hm : m.Canonical) (hn : n.Canonical) :
    ∃ r, NatSubtract m n r := by
  rw [← BinNat.ofNat_val hm, ← BinNat.ofNat_val hn]
  exact ⟨_, natSubtract_derives _ _⟩

/-! ### `PackByte` -/

/-- `PackByte`. -/
inductive PackByte : Byte → BinNat → BinNat → Prop
  /-- `Pack: (PackByte (Byte8 b7 b6 b5 b4 b3 b2 b1 b0) high) ~> (MakeNatBit b0 (MakeNatBit b1
  (MakeNatBit b2 (MakeNatBit b3 (MakeNatBit b4 (MakeNatBit b5 (MakeNatBit b6
  (MakeNatBit b7 high))))))));` -/
  | pack {b7 b6 b5 b4 b3 b2 b1 b0 : Bit} {high r7 r6 r5 r4 r3 r2 r1 r0 : BinNat} :
      MakeNatBit b7 high r7 → MakeNatBit b6 r7 r6 → MakeNatBit b5 r6 r5 → MakeNatBit b4 r5 r4 →
      MakeNatBit b3 r4 r3 → MakeNatBit b2 r3 r2 → MakeNatBit b1 r2 r1 → MakeNatBit b0 r1 r0 →
      PackByte (.byte8 b7 b6 b5 b4 b3 b2 b1 b0) high r0

/-- What the rule of `PackByte` computes. -/
def packByte : Byte → BinNat → BinNat
  | .byte8 b7 b6 b5 b4 b3 b2 b1 b0, high =>
    makeNatBit b0 (makeNatBit b1 (makeNatBit b2 (makeNatBit b3 (makeNatBit b4 (makeNatBit b5
      (makeNatBit b6 (makeNatBit b7 high)))))))

theorem packByte_iff_fn {b : Byte} {high r : BinNat} : PackByte b high r ↔ r = packByte b high := by
  constructor
  · rintro ⟨h₇, h₆, h₅, h₄, h₃, h₂, h₁, h₀⟩
    simp only [makeNatBit_iff_fn] at h₇ h₆ h₅ h₄ h₃ h₂ h₁ h₀
    subst h₇ h₆ h₅ h₄ h₃ h₂ h₁ h₀
    rfl
  · rintro rfl
    obtain ⟨b7, b6, b5, b4, b3, b2, b1, b0⟩ := b
    exact .pack (makeNatBit_iff_fn.mpr rfl) (makeNatBit_iff_fn.mpr rfl) (makeNatBit_iff_fn.mpr rfl)
      (makeNatBit_iff_fn.mpr rfl) (makeNatBit_iff_fn.mpr rfl) (makeNatBit_iff_fn.mpr rfl)
      (makeNatBit_iff_fn.mpr rfl) (makeNatBit_iff_fn.mpr rfl)

@[simp] theorem val_packByte (b : Byte) (high : BinNat) :
    (packByte b high).val = 256 * high.val + b.val := by
  obtain ⟨b7, b6, b5, b4, b3, b2, b1, b0⟩ := b
  simp only [packByte, val_makeNatBit, Byte.val]
  omega

theorem canonical_packByte (b : Byte) {high : BinNat} (h : high.Canonical) :
    (packByte b high).Canonical := by
  obtain ⟨b7, b6, b5, b4, b3, b2, b1, b0⟩ := b
  simp only [packByte]
  repeat apply canonical_makeNatBit
  exact h

theorem packByte_ofNat (b : Byte) (v : Nat) : packByte b (ofNat v) = ofNat (256 * v + b.val) :=
  BinNat.eq_ofNat (canonical_packByte b (canonical_ofNat v)) (by simp)

/-- **`PackByte`** of a byte over the numeral of `v` is the numeral of `256 v + byte`. -/
theorem packByte_iff {b : Byte} {v : Nat} {r : BinNat} :
    PackByte b (ofNat v) r ↔ r = ofNat (256 * v + b.val) := by
  rw [packByte_iff_fn, packByte_ofNat]

theorem packByte_total (b : Byte) (high : BinNat) : ∃ r, PackByte b high r :=
  ⟨_, packByte_iff_fn.mpr rfl⟩

theorem packByte_functional {b : Byte} {high r r' : BinNat} (h : PackByte b high r)
    (h' : PackByte b high r') : r = r' :=
  (packByte_iff_fn.mp h).trans (packByte_iff_fn.mp h').symm


/-! ## Bytes as words -/

/-- `RC_KID_word_1`: the `i`-th child of the `Byte8` that a word `v` holds is bit `7 - i` of `v`
(`(v >> (7 - i)) & 1 ? Bit1 : Bit0`). -/
def wordKid (v i : Nat) : Bit := if (v >>> (7 - i)) &&& 1 ≠ 0 then .bit1 else .bit0

/-- The byte a word holds, read through the views: `RC_TAG_word_1` (always `Byte8`) and
`RC_KID_word_1`. -/
def Byte.ofWord (v : Nat) : Byte :=
  .byte8 (wordKid v 0) (wordKid v 1) (wordKid v 2) (wordKid v 3) (wordKid v 4) (wordKid v 5)
    (wordKid v 6) (wordKid v 7)

/-- Viewing the word of a byte's value gives the byte back. -/
theorem Byte.ofWord_val (b : Byte) : Byte.ofWord b.val = b := by
  obtain ⟨b7, b6, b5, b4, b3, b2, b1, b0⟩ := b
  cases b7 <;> cases b6 <;> cases b5 <;> cases b4 <;> cases b3 <;> cases b2 <;> cases b1 <;>
    cases b0 <;> rfl

/-- The value of the byte a word below `256` holds is the word. -/
theorem Byte.val_ofWord : ∀ v, v < 256 → (Byte.ofWord v).val = v := by
  decide +kernel

theorem Byte.val_injective {a b : Byte} (h : a.val = b.val) : a = b := by
  rw [← Byte.ofWord_val a, ← Byte.ofWord_val b, h]

/-! ## Byte strings -/

/-! ### `ByteLength` -/

/-- `ByteLength`. -/
inductive ByteLength : Bytes → BinNat → Prop
  /-- `LengthEmpty: (ByteLength (BNil)) ~> (NatZero);` -/
  | lengthEmpty : ByteLength .nil .zero
  /-- `LengthCons: (ByteLength (BCons b xs)) ~> (NatInc (ByteLength xs));` -/
  | lengthCons {b : Byte} {xs : Bytes} {n r : BinNat} :
      ByteLength xs n → NatInc n r → ByteLength (.cons b xs) r

/-- What the rules of `ByteLength` compute. -/
def byteLength : Bytes → BinNat
  | .nil => .zero
  | .cons _ xs => natInc (byteLength xs)

theorem byteLength_iff_fn {xs : Bytes} {r : BinNat} : ByteLength xs r ↔ r = byteLength xs := by
  constructor
  · intro h
    induction h with
    | lengthEmpty => rfl
    | lengthCons _ h ih => rw [natInc_iff_fn.mp h, ih]; rfl
  · rintro rfl
    induction xs with
    | nil => exact .lengthEmpty
    | cons b xs ih => exact .lengthCons ih (natInc_iff_fn.mpr rfl)

theorem byteLength_eq (xs : Bytes) : byteLength xs = ofNat xs.toList.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [byteLength, ih, natInc_ofNat]

/-- **`ByteLength`** is the numeral of the number of bytes. -/
theorem byteLength_iff {xs : Bytes} {r : BinNat} :
    ByteLength xs r ↔ r = ofNat xs.toList.length := by
  rw [byteLength_iff_fn, byteLength_eq]

theorem byteLength_total (xs : Bytes) : ∃ r, ByteLength xs r := ⟨_, byteLength_iff_fn.mpr rfl⟩

theorem byteLength_functional {xs : Bytes} {r r' : BinNat} (h : ByteLength xs r)
    (h' : ByteLength xs r') : r = r' :=
  (byteLength_iff_fn.mp h).trans (byteLength_iff_fn.mp h').symm

/-! ### `TakePush` and `TakeBytes` -/

/-- `TakePush`: no rule for a state other than `Taken` and `NeedInput`. -/
inductive TakePush : Byte → CodecState → CodecState → Prop
  /-- `TakeCons: (TakePush b (Taken prefix rest)) ~> (Taken (BCons b prefix) rest);` -/
  | takeCons {b : Byte} {pre rest : Bytes} : TakePush b (.taken pre rest) (.taken (.cons b pre) rest)
  /-- `TakePropagate: (TakePush b (NeedInput)) ~> (NeedInput);` -/
  | takePropagate {b : Byte} : TakePush b .needInput .needInput

/-- What the rules of `TakePush` compute; `none` where no rule applies. -/
def takePush (b : Byte) : CodecState → Option CodecState
  | .taken pre rest => some (.taken (.cons b pre) rest)
  | .needInput => some .needInput
  | _ => none

/-- **`TakePush`** on every input: exactly the result of `takePush`, which has one on `Taken` and
`NeedInput` and none elsewhere. -/
theorem takePush_iff_fn {b : Byte} {s r : CodecState} : TakePush b s r ↔ takePush b s = some r := by
  constructor
  · rintro ⟨⟩ <;> rfl
  · intro h
    cases s <;> simp only [takePush, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
      constructor

theorem takePush_functional {b : Byte} {s r r' : CodecState} (h : TakePush b s r)
    (h' : TakePush b s r') : r = r' := by
  rw [takePush_iff_fn] at h h'
  exact Option.some.inj (h.symm.trans h')

theorem takePush_total_taken (b : Byte) (pre rest : Bytes) : ∃ r, TakePush b (.taken pre rest) r :=
  ⟨_, .takeCons⟩

theorem takePush_total_needInput (b : Byte) : ∃ r, TakePush b .needInput r := ⟨_, .takePropagate⟩

/-- `TakeBytes`. -/
inductive TakeBytes : BinNat → Bytes → CodecState → Prop
  /-- `TakeEmpty: (TakeBytes (NatZero) xs) ~> (Taken (BNil) xs);` -/
  | takeEmpty {xs : Bytes} : TakeBytes .zero xs (.taken .nil xs)
  /-- `TakeShort: (TakeBytes (NatBit bit n) (BNil)) ~> (NeedInput);` -/
  | takeShort {bit : Bit} {n : BinNat} : TakeBytes (.bit bit n) .nil .needInput
  /-- `TakeMore: (TakeBytes (NatBit bit n) (BCons b xs)) ~>
  (TakePush b (TakeBytes (NatPred (NatBit bit n)) xs));` -/
  | takeMore {bit : Bit} {n : BinNat} {b : Byte} {xs : Bytes} {p : BinNat} {s r : CodecState} :
      NatPred (.bit bit n) p → TakeBytes p xs s → TakePush b s r →
        TakeBytes (.bit bit n) (.cons b xs) r

/-- What the rules of `TakeBytes` compute; `none` where no rule applies. -/
def takeBytes : BinNat → Bytes → Option CodecState
  | .zero, xs => some (.taken .nil xs)
  | .bit _ _, .nil => some .needInput
  | .bit bit n, .cons b xs =>
    ((natPred (.bit bit n)).bind fun p => takeBytes p xs).bind (takePush b)

theorem takeBytes_iff_fn {n : BinNat} {xs : Bytes} {r : CodecState} :
    TakeBytes n xs r ↔ takeBytes n xs = some r := by
  constructor
  · intro h
    induction h with
    | takeEmpty => simp [takeBytes]
    | takeShort => rfl
    | takeMore h₁ _ h₃ ih =>
      simp only [takeBytes, natPred_iff_fn.mp h₁, Option.bind_some, ih, takePush_iff_fn.mp h₃]
  · intro h
    induction xs generalizing n r with
    | nil =>
      cases n with
      | zero => simp only [takeBytes, Option.some.injEq] at h; subst h; exact .takeEmpty
      | bit bit n => simp only [takeBytes, Option.some.injEq] at h; subst h; exact .takeShort
    | cons b xs ih =>
      cases n with
      | zero => simp only [takeBytes, Option.some.injEq] at h; subst h; exact .takeEmpty
      | bit bit n =>
        simp only [takeBytes, Option.bind_eq_some_iff] at h
        obtain ⟨s, ⟨p, hp, hs⟩, hr⟩ := h
        exact .takeMore (natPred_iff_fn.mpr hp) (ih hs) (takePush_iff_fn.mpr hr)

/-- The first `k` bytes and the rest, or `NeedInput` when there are fewer than `k`. -/
def takeSpec (k : Nat) (xs : Bytes) : CodecState :=
  if k ≤ xs.toList.length then .taken (.ofList (xs.toList.take k)) (.ofList (xs.toList.drop k))
  else .needInput

theorem takeBytes_ofNat (xs : Bytes) : ∀ k : Nat, takeBytes (ofNat k) xs = some (takeSpec k xs) := by
  induction xs with
  | nil =>
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [takeBytes, takeSpec]
    · rw [BinNat.ofNat_of_ne_zero hk]
      unfold takeSpec
      rw [if_neg (by simp only [Bytes.toList_nil, List.length_nil]; omega)]
      rfl
  | cons b xs ih =>
    intro k
    by_cases hk : k = 0
    · subst hk
      simp [takeBytes, takeSpec]
    · have e := natPred_ofNat k
      rw [if_neg hk, BinNat.ofNat_of_ne_zero hk] at e
      rw [BinNat.ofNat_of_ne_zero hk]
      simp only [takeBytes, e, Option.bind_some, ih (k - 1)]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      unfold takeSpec
      rw [Nat.add_sub_cancel]
      by_cases hle : j ≤ xs.toList.length
      · rw [if_pos hle, if_pos (by simp only [Bytes.toList_cons, List.length_cons]; omega)]
        simp [takePush]
      · rw [if_neg hle, if_neg (by simp only [Bytes.toList_cons, List.length_cons]; omega)]
        rfl

/-- **`TakeBytes`** on the numeral of `k`: the first `k` bytes and the rest when there are at least
`k`, otherwise `NeedInput`. -/
theorem takeBytes_iff {k : Nat} {xs : Bytes} {r : CodecState} :
    TakeBytes (ofNat k) xs r ↔ r = takeSpec k xs := by
  rw [takeBytes_iff_fn, takeBytes_ofNat, Option.some.injEq]
  exact eq_comm

/-- `TakeBytes` has a result on every canonical numeral. -/
theorem takeBytes_total {n : BinNat} (hn : n.Canonical) (xs : Bytes) : ∃ r, TakeBytes n xs r := by
  rw [← BinNat.ofNat_val hn]
  exact ⟨_, takeBytes_iff.mpr rfl⟩

theorem takeBytes_functional {n : BinNat} {xs : Bytes} {r r' : CodecState} (h : TakeBytes n xs r)
    (h' : TakeBytes n xs r') : r = r' := by
  rw [takeBytes_iff_fn] at h h'
  exact Option.some.inj (h.symm.trans h')

/-! ### `BytesEqual` and `BytesEqualNext` -/

mutual

/-- `BytesEqual`. -/
inductive BytesEqual : Bytes → Bytes → Bit → Prop
  /-- `BytesEqualEmpty: (BytesEqual (BNil) (BNil)) ~> (Bit1);` -/
  | bytesEqualEmpty : BytesEqual .nil .nil .bit1
  /-- `BytesLeftEmpty: (BytesEqual (BNil) (BCons b xs)) ~> (Bit0);` -/
  | bytesLeftEmpty {b : Byte} {xs : Bytes} : BytesEqual .nil (.cons b xs) .bit0
  /-- `BytesRightEmpty: (BytesEqual (BCons b xs) (BNil)) ~> (Bit0);` -/
  | bytesRightEmpty {b : Byte} {xs : Bytes} : BytesEqual (.cons b xs) .nil .bit0
  /-- `BytesEqualMore: (BytesEqual (BCons b xs) (BCons c ys)) ~> (BytesEqualNext (NatCompare
  (PackByte b (NatZero)) (PackByte c (NatZero))) xs ys);` -/
  | bytesEqualMore {b : Byte} {xs : Bytes} {c : Byte} {ys : Bytes} {p q : BinNat} {o : Cmp}
      {r : Bit} :
      PackByte b .zero p → PackByte c .zero q → NatCompare p q o → BytesEqualNext o xs ys r →
        BytesEqual (.cons b xs) (.cons c ys) r

/-- `BytesEqualNext`. -/
inductive BytesEqualNext : Cmp → Bytes → Bytes → Bit → Prop
  /-- `BytesEqualMatch: (BytesEqualNext (Equal) xs ys) ~> (BytesEqual xs ys);` -/
  | bytesEqualMatch {xs ys : Bytes} {r : Bit} : BytesEqual xs ys r → BytesEqualNext .equal xs ys r
  /-- `BytesLessMismatch: (BytesEqualNext (Less) xs ys) ~> (Bit0);` -/
  | bytesLessMismatch {xs ys : Bytes} : BytesEqualNext .less xs ys .bit0
  /-- `BytesGreaterMismatch: (BytesEqualNext (Greater) xs ys) ~> (Bit0);` -/
  | bytesGreaterMismatch {xs ys : Bytes} : BytesEqualNext .greater xs ys .bit0

end

/-- What the rules of `BytesEqual` compute. -/
def bytesEqual : Bytes → Bytes → Bit
  | .nil, .nil => .bit1
  | .nil, .cons _ _ => .bit0
  | .cons _ _, .nil => .bit0
  | .cons b xs, .cons c ys =>
    match natCompare (packByte b .zero) (packByte c .zero) with
    | .equal => bytesEqual xs ys
    | .less => .bit0
    | .greater => .bit0

/-- What the rules of `BytesEqualNext` compute. -/
def bytesEqualNext : Cmp → Bytes → Bytes → Bit
  | .equal, xs, ys => bytesEqual xs ys
  | .less, _, _ => .bit0
  | .greater, _, _ => .bit0

theorem bytesEqual_cons (b : Byte) (xs : Bytes) (c : Byte) (ys : Bytes) :
    bytesEqual (.cons b xs) (.cons c ys) =
      bytesEqualNext (natCompare (packByte b .zero) (packByte c .zero)) xs ys := by
  rw [bytesEqual]
  cases natCompare (packByte b .zero) (packByte c .zero) <;> rfl

theorem bytesEqual_iff_fn {xs ys : Bytes} {r : Bit} : BytesEqual xs ys r ↔ r = bytesEqual xs ys := by
  constructor
  · intro h
    induction xs generalizing ys r with
    | nil => cases h <;> rfl
    | cons b xs ih =>
      cases h with
      | bytesRightEmpty => rfl
      | bytesEqualMore h₁ h₂ h₃ h₄ =>
        rw [bytesEqual_cons, ← packByte_iff_fn.mp h₁, ← packByte_iff_fn.mp h₂,
          ← natCompare_iff_fn.mp h₃]
        cases h₄ with
        | bytesEqualMatch h => exact ih h
        | bytesLessMismatch => rfl
        | bytesGreaterMismatch => rfl
  · rintro rfl
    induction xs generalizing ys with
    | nil =>
      cases ys with
      | nil => exact .bytesEqualEmpty
      | cons c ys => exact .bytesLeftEmpty
    | cons b xs ih =>
      cases ys with
      | nil => exact .bytesRightEmpty
      | cons c ys =>
        rw [bytesEqual_cons]
        refine .bytesEqualMore (packByte_iff_fn.mpr rfl) (packByte_iff_fn.mpr rfl)
          (natCompare_iff_fn.mpr rfl) ?_
        cases natCompare (packByte b .zero) (packByte c .zero)
        · exact .bytesLessMismatch
        · exact .bytesEqualMatch (ih (ys := ys))
        · exact .bytesGreaterMismatch

theorem bytesEqualNext_iff_fn {o : Cmp} {xs ys : Bytes} {r : Bit} :
    BytesEqualNext o xs ys r ↔ r = bytesEqualNext o xs ys := by
  constructor
  · rintro (h | _ | _)
    · exact bytesEqual_iff_fn.mp h
    · rfl
    · rfl
  · rintro rfl
    cases o
    · exact .bytesLessMismatch
    · exact .bytesEqualMatch (bytesEqual_iff_fn.mpr rfl)
    · exact .bytesGreaterMismatch

theorem Cmp.ofNats_eq_equal_iff {x y : Nat} : Cmp.ofNats x y = .equal ↔ x = y := by
  unfold Cmp.ofNats
  by_cases h₁ : x < y
  · rw [if_pos h₁]
    exact ⟨nofun, fun h => absurd h (by omega)⟩
  · by_cases h₂ : x = y
    · rw [if_neg h₁, if_pos h₂]
      exact ⟨fun _ => h₂, fun _ => rfl⟩
    · rw [if_neg h₁, if_neg h₂]
      exact ⟨nofun, fun h => absurd h h₂⟩

/-- Two bytes compare through `PackByte` and `NatCompare` by their values. -/
theorem natCompare_packByte (b c : Byte) :
    natCompare (packByte b .zero) (packByte c .zero) = Cmp.ofNats b.val c.val := by
  have e₁ := packByte_ofNat b 0
  have e₂ := packByte_ofNat c 0
  rw [BinNat.ofNat_zero] at e₁ e₂
  rw [e₁, e₂, natCompare_canonical (canonical_ofNat _) (canonical_ofNat _), val_ofNat, val_ofNat]
  simp

theorem bytesEqual_eq : ∀ xs ys : Bytes, bytesEqual xs ys = if xs = ys then .bit1 else .bit0
  | .nil, .nil => rfl
  | .nil, .cons _ _ => rfl
  | .cons _ _, .nil => rfl
  | .cons b xs, .cons c ys => by
    rw [bytesEqual_cons, natCompare_packByte]
    by_cases hbc : b = c
    · subst hbc
      have : Cmp.ofNats b.val b.val = .equal := Cmp.ofNats_eq_equal_iff.mpr rfl
      rw [this]
      show bytesEqual xs ys = _
      rw [bytesEqual_eq xs ys]
      by_cases hxy : xs = ys
      · rw [if_pos hxy, if_pos (by rw [hxy])]
      · rw [if_neg hxy, if_neg (fun h => hxy (Bytes.cons.inj h).2)]
    · rw [if_neg (fun h => hbc (Bytes.cons.inj h).1)]
      have hv : b.val ≠ c.val := fun h => hbc (Byte.val_injective h)
      unfold Cmp.ofNats
      by_cases h₁ : b.val < c.val
      · rw [if_pos h₁]
        rfl
      · rw [if_neg h₁, if_neg hv]
        rfl

/-- **`BytesEqual`** has exactly one result: `Bit1` on equal byte strings, `Bit0` otherwise. -/
theorem bytesEqual_iff {xs ys : Bytes} {r : Bit} :
    BytesEqual xs ys r ↔ r = if xs = ys then .bit1 else .bit0 := by
  rw [bytesEqual_iff_fn, bytesEqual_eq]

theorem bytesEqual_total (xs ys : Bytes) : ∃ r, BytesEqual xs ys r := ⟨_, bytesEqual_iff_fn.mpr rfl⟩

theorem bytesEqual_functional {xs ys : Bytes} {r r' : Bit} (h : BytesEqual xs ys r)
    (h' : BytesEqual xs ys r') : r = r' :=
  (bytesEqual_iff_fn.mp h).trans (bytesEqual_iff_fn.mp h').symm

/-- **`BytesEqualNext`**: on `Equal` the equality of the rests, otherwise `Bit0`. -/
theorem bytesEqualNext_iff {o : Cmp} {xs ys : Bytes} {r : Bit} :
    BytesEqualNext o xs ys r ↔ r = if o = .equal ∧ xs = ys then .bit1 else .bit0 := by
  rw [bytesEqualNext_iff_fn]
  cases o <;> simp [bytesEqualNext, bytesEqual_eq]

theorem bytesEqualNext_total (o : Cmp) (xs ys : Bytes) : ∃ r, BytesEqualNext o xs ys r :=
  ⟨_, bytesEqualNext_iff_fn.mpr rfl⟩

theorem bytesEqualNext_functional {o : Cmp} {xs ys : Bytes} {r r' : Bit}
    (h : BytesEqualNext o xs ys r) (h' : BytesEqualNext o xs ys r') : r = r' :=
  (bytesEqualNext_iff_fn.mp h).trans (bytesEqualNext_iff_fn.mp h').symm

/-! ### Unsigned LEB128: `ReadULEB62`, `LebRead`, `LebJoin` -/

/-- `LebJoin`: no rule for `LimitExceeded` or `Taken`. -/
inductive LebJoin : Bit → Bit → Bit → Bit → Bit → Bit → Bit → CodecState → CodecState → Prop
  /-- `LebNonminimal: (LebJoin b6 b5 b4 b3 b2 b1 b0 (DecodedWord (NatZero) rest)) ~>
  (BadInteger);` -/
  | lebNonminimal {b6 b5 b4 b3 b2 b1 b0 : Bit} {rest : Bytes} :
      LebJoin b6 b5 b4 b3 b2 b1 b0 (.decodedWord .zero rest) .badInteger
  /-- `LebCombine: (LebJoin b6 b5 b4 b3 b2 b1 b0 (DecodedWord (NatBit bit n) rest)) ~>
  (DecodedWord (MakeNatBit b0 (MakeNatBit b1 (MakeNatBit b2 (MakeNatBit b3 (MakeNatBit b4
  (MakeNatBit b5 (MakeNatBit b6 (NatBit bit n)))))))) rest);` -/
  | lebCombine {b6 b5 b4 b3 b2 b1 b0 bit : Bit} {n : BinNat} {rest : Bytes}
      {r6 r5 r4 r3 r2 r1 r0 : BinNat} :
      MakeNatBit b6 (.bit bit n) r6 → MakeNatBit b5 r6 r5 → MakeNatBit b4 r5 r4 →
      MakeNatBit b3 r4 r3 → MakeNatBit b2 r3 r2 → MakeNatBit b1 r2 r1 → MakeNatBit b0 r1 r0 →
      LebJoin b6 b5 b4 b3 b2 b1 b0 (.decodedWord (.bit bit n) rest) (.decodedWord r0 rest)
  /-- `LebJoinShort: (LebJoin b6 b5 b4 b3 b2 b1 b0 (NeedInput)) ~> (NeedInput);` -/
  | lebJoinShort {b6 b5 b4 b3 b2 b1 b0 : Bit} : LebJoin b6 b5 b4 b3 b2 b1 b0 .needInput .needInput
  /-- `LebJoinBad: (LebJoin b6 b5 b4 b3 b2 b1 b0 (BadInteger)) ~> (BadInteger);` -/
  | lebJoinBad {b6 b5 b4 b3 b2 b1 b0 : Bit} : LebJoin b6 b5 b4 b3 b2 b1 b0 .badInteger .badInteger

/-- `LebRead`. -/
inductive LebRead : LebFuel → Bytes → CodecState → Prop
  /-- `LebEmpty: (LebRead limit (BNil)) ~> (NeedInput);` -/
  | lebEmpty {limit : LebFuel} : LebRead limit .nil .needInput
  /-- `LebEnd: (LebRead (LebMore limit) (BCons (Byte8 (Bit0) b6 b5 b4 b3 b2 b1 b0) rest)) ~>
  (DecodedWord (MakeNatBit b0 (MakeNatBit b1 (MakeNatBit b2 (MakeNatBit b3 (MakeNatBit b4
  (MakeNatBit b5 (MakeNatBit b6 (NatZero)))))))) rest);` -/
  | lebEnd {limit : LebFuel} {b6 b5 b4 b3 b2 b1 b0 : Bit} {rest : Bytes}
      {r6 r5 r4 r3 r2 r1 r0 : BinNat} :
      MakeNatBit b6 .zero r6 → MakeNatBit b5 r6 r5 → MakeNatBit b4 r5 r4 → MakeNatBit b3 r4 r3 →
      MakeNatBit b2 r3 r2 → MakeNatBit b1 r2 r1 → MakeNatBit b0 r1 r0 →
      LebRead (.more limit) (.cons (.byte8 .bit0 b6 b5 b4 b3 b2 b1 b0) rest) (.decodedWord r0 rest)
  /-- `LebContinue: (LebRead (LebMore limit) (BCons (Byte8 (Bit1) b6 b5 b4 b3 b2 b1 b0) rest))
  ~> (LebJoin b6 b5 b4 b3 b2 b1 b0 (LebRead limit rest));` -/
  | lebContinue {limit : LebFuel} {b6 b5 b4 b3 b2 b1 b0 : Bit} {rest : Bytes} {s r : CodecState} :
      LebRead limit rest s → LebJoin b6 b5 b4 b3 b2 b1 b0 s r →
      LebRead (.more limit) (.cons (.byte8 .bit1 b6 b5 b4 b3 b2 b1 b0) rest) r
  /-- `LebNinth: (LebRead (LebLast) (BCons (Byte8 (Bit0) (Bit0) b5 b4 b3 b2 b1 b0) rest)) ~>
  (DecodedWord (MakeNatBit b0 (MakeNatBit b1 (MakeNatBit b2 (MakeNatBit b3 (MakeNatBit b4
  (MakeNatBit b5 (NatZero))))))) rest);` -/
  | lebNinth {b5 b4 b3 b2 b1 b0 : Bit} {rest : Bytes} {r5 r4 r3 r2 r1 r0 : BinNat} :
      MakeNatBit b5 .zero r5 → MakeNatBit b4 r5 r4 → MakeNatBit b3 r4 r3 → MakeNatBit b2 r3 r2 →
      MakeNatBit b1 r2 r1 → MakeNatBit b0 r1 r0 →
      LebRead .last (.cons (.byte8 .bit0 .bit0 b5 b4 b3 b2 b1 b0) rest) (.decodedWord r0 rest)
  /-- `LebOverflow: (LebRead (LebLast) (BCons (Byte8 (Bit0) (Bit1) b5 b4 b3 b2 b1 b0) rest)) ~>
  (BadInteger);` -/
  | lebOverflow {b5 b4 b3 b2 b1 b0 : Bit} {rest : Bytes} :
      LebRead .last (.cons (.byte8 .bit0 .bit1 b5 b4 b3 b2 b1 b0) rest) .badInteger
  /-- `LebTooLong: (LebRead (LebLast) (BCons (Byte8 (Bit1) b6 b5 b4 b3 b2 b1 b0) rest)) ~>
  (BadInteger);` -/
  | lebTooLong {b6 b5 b4 b3 b2 b1 b0 : Bit} {rest : Bytes} :
      LebRead .last (.cons (.byte8 .bit1 b6 b5 b4 b3 b2 b1 b0) rest) .badInteger

/-- `ReadULEB62`. -/
inductive ReadULEB62 : Bytes → CodecState → Prop
  /-- `StartLEB: (ReadULEB62 xs) ~> (LebRead (LebMore (LebMore (LebMore (LebMore (LebMore
  (LebMore (LebMore (LebMore (LebLast))))))))) xs);` -/
  | startLEB {xs : Bytes} {r : CodecState} :
      LebRead (.more (.more (.more (.more (.more (.more (.more (.more .last)))))))) xs r →
        ReadULEB62 xs r

/-- `k` times `LebMore` over `LebLast`: `k + 1` bytes at most. -/
def lebFuel : Nat → LebFuel
  | 0 => .last
  | k + 1 => .more (lebFuel k)

/-- The seven `MakeNatBit` calls of `LebEnd` and `LebCombine`, over `n`. -/
def mk7 (b6 b5 b4 b3 b2 b1 b0 : Bit) (n : BinNat) : BinNat :=
  makeNatBit b0 (makeNatBit b1 (makeNatBit b2 (makeNatBit b3 (makeNatBit b4 (makeNatBit b5
    (makeNatBit b6 n))))))

/-- What the rules of `LebJoin` compute; `none` where no rule applies. -/
def lebJoin (b6 b5 b4 b3 b2 b1 b0 : Bit) : CodecState → Option CodecState
  | .decodedWord .zero _ => some .badInteger
  | .decodedWord (.bit bit n) rest => some (.decodedWord (mk7 b6 b5 b4 b3 b2 b1 b0 (.bit bit n)) rest)
  | .needInput => some .needInput
  | .badInteger => some .badInteger
  | .limitExceeded => none
  | .taken _ _ => none

/-- What the rules of `LebRead` compute. -/
def lebRead : LebFuel → Bytes → Option CodecState
  | _, .nil => some .needInput
  | .more _, .cons (.byte8 .bit0 b6 b5 b4 b3 b2 b1 b0) rest =>
    some (.decodedWord (mk7 b6 b5 b4 b3 b2 b1 b0 .zero) rest)
  | .more limit, .cons (.byte8 .bit1 b6 b5 b4 b3 b2 b1 b0) rest =>
    (lebRead limit rest).bind (lebJoin b6 b5 b4 b3 b2 b1 b0)
  | .last, .cons (.byte8 .bit0 .bit0 b5 b4 b3 b2 b1 b0) rest =>
    some (.decodedWord (makeNatBit b0 (makeNatBit b1 (makeNatBit b2 (makeNatBit b3 (makeNatBit b4
      (makeNatBit b5 .zero)))))) rest)
  | .last, .cons (.byte8 .bit0 .bit1 _ _ _ _ _ _) _ => some .badInteger
  | .last, .cons (.byte8 .bit1 _ _ _ _ _ _ _) _ => some .badInteger

/-- The proof that `MakeNatBit` derives its function's result. -/
theorem MakeNatBit.fn (b : Bit) (n : BinNat) : MakeNatBit b n (makeNatBit b n) :=
  makeNatBit_iff_fn.mpr rfl

theorem lebJoin_iff_fn {b6 b5 b4 b3 b2 b1 b0 : Bit} {s r : CodecState} :
    LebJoin b6 b5 b4 b3 b2 b1 b0 s r ↔ lebJoin b6 b5 b4 b3 b2 b1 b0 s = some r := by
  constructor
  · intro h
    cases h with
    | lebNonminimal => rfl
    | lebCombine h₆ h₅ h₄ h₃ h₂ h₁ h₀ =>
      simp only [makeNatBit_iff_fn] at h₆ h₅ h₄ h₃ h₂ h₁ h₀
      subst h₆ h₅ h₄ h₃ h₂ h₁ h₀
      rfl
    | lebJoinShort => rfl
    | lebJoinBad => rfl
  · intro h
    cases s with
    | decodedWord n rest =>
      cases n with
      | zero =>
        simp only [lebJoin, Option.some.injEq] at h
        subst h
        exact .lebNonminimal
      | bit bit n =>
        simp only [lebJoin, Option.some.injEq] at h
        subst h
        exact .lebCombine (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _)
    | needInput =>
      simp only [lebJoin, Option.some.injEq] at h
      subst h
      exact .lebJoinShort
    | badInteger =>
      simp only [lebJoin, Option.some.injEq] at h
      subst h
      exact .lebJoinBad
    | limitExceeded => simp [lebJoin] at h
    | taken _ _ => simp [lebJoin] at h

theorem lebRead_iff_fn {f : LebFuel} {xs : Bytes} {r : CodecState} :
    LebRead f xs r ↔ lebRead f xs = some r := by
  constructor
  · intro h
    induction h with
    | lebEmpty => simp [lebRead]
    | lebEnd h₆ h₅ h₄ h₃ h₂ h₁ h₀ =>
      simp only [makeNatBit_iff_fn] at h₆ h₅ h₄ h₃ h₂ h₁ h₀
      subst h₆ h₅ h₄ h₃ h₂ h₁ h₀
      rfl
    | lebContinue _ h ih => simp only [lebRead, ih, Option.bind_some, lebJoin_iff_fn.mp h]
    | lebNinth h₅ h₄ h₃ h₂ h₁ h₀ =>
      simp only [makeNatBit_iff_fn] at h₅ h₄ h₃ h₂ h₁ h₀
      subst h₅ h₄ h₃ h₂ h₁ h₀
      rfl
    | lebOverflow => rfl
    | lebTooLong => rfl
  · intro h
    induction xs generalizing f r with
    | nil =>
      have e : r = .needInput := by cases f <;> simpa [lebRead] using h.symm
      subst e
      exact .lebEmpty
    | cons b rest ih =>
      obtain ⟨b7, b6, b5, b4, b3, b2, b1, b0⟩ := b
      cases f with
      | more limit =>
        cases b7 with
        | bit0 =>
          simp only [lebRead, Option.some.injEq] at h
          subst h
          exact .lebEnd (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _)
        | bit1 =>
          simp only [lebRead, Option.bind_eq_some_iff] at h
          obtain ⟨s, hs, hr⟩ := h
          exact .lebContinue (ih hs) (lebJoin_iff_fn.mpr hr)
      | last =>
        cases b7 with
        | bit0 =>
          cases b6 with
          | bit0 =>
            simp only [lebRead, Option.some.injEq] at h
            subst h
            exact .lebNinth (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _) (.fn _ _)
          | bit1 =>
            simp only [lebRead, Option.some.injEq] at h
            subst h
            exact .lebOverflow
        | bit1 =>
          simp only [lebRead, Option.some.injEq] at h
          subst h
          exact .lebTooLong

/-- The value of a byte's low seven bits through the seven `MakeNatBit` calls, over `ofNat w`. -/
theorem mk7_ofNat (b6 b5 b4 b3 b2 b1 b0 : Bit) (w : Nat) :
    mk7 b6 b5 b4 b3 b2 b1 b0 (ofNat w) =
      ofNat (128 * w + (64 * b6.val + 32 * b5.val + 16 * b4.val + 8 * b3.val + 4 * b2.val +
        2 * b1.val + b0.val)) := by
  simp only [mk7, makeNatBit_ofNat]
  congr 1
  omega

theorem mk6_zero (b5 b4 b3 b2 b1 b0 : Bit) :
    makeNatBit b0 (makeNatBit b1 (makeNatBit b2 (makeNatBit b3 (makeNatBit b4 (makeNatBit b5
      .zero))))) =
      ofNat (32 * b5.val + 16 * b4.val + 8 * b3.val + 4 * b2.val + 2 * b1.val + b0.val) := by
  rw [← BinNat.ofNat_zero]
  simp only [makeNatBit_ofNat]
  congr 1
  omega

/-- What reading an unsigned LEB128 number gives: input needed, a malformed number, or the number
and how many bytes it took. -/
inductive LebOut
  /-- The input ends first. -/
  | needInput
  /-- Too long, too large, or not minimal. -/
  | badInteger
  /-- The number and the number of bytes it took. -/
  | decoded (v used : Nat)
  deriving DecidableEq, Repr

/-- `LebJoin` on byte values: a continued byte's low seven bits `x` joined to what the rest gave;
a rest of value `0` is not minimal. -/
def lebJoinSpec (x : Nat) : LebOut → LebOut
  | .needInput => .needInput
  | .badInteger => .badInteger
  | .decoded w k => if w = 0 then .badInteger else .decoded (x + 128 * w) (k + 1)

/-- What the rules of `LebRead` compute with the fuel `lebFuel k`, on byte values. -/
def lebSpec : Nat → List Nat → LebOut
  | _, [] => .needInput
  | 0, c :: _ => if c < 64 then .decoded c 1 else .badInteger
  | k + 1, c :: rest => if c < 128 then .decoded c 1 else lebJoinSpec (c - 128) (lebSpec k rest)

/-- A reading as the module's `CodecState`, the rest being what follows the bytes it took. -/
def LebOut.toState (xs : List Byte) : LebOut → CodecState
  | .needInput => .needInput
  | .badInteger => .badInteger
  | .decoded v k => .decodedWord (ofNat v) (.ofList (xs.drop k))

theorem lebRead_spec : ∀ (xs : List Byte) (k : Nat),
    lebRead (lebFuel k) (.ofList xs) = some ((lebSpec k (xs.map Byte.val)).toState xs)
  | [], k => by cases k <;> rfl
  | .byte8 b7 b6 b5 b4 b3 b2 b1 b0 :: xs, 0 => by
    have := b5.val_le_one; have := b4.val_le_one; have := b3.val_le_one
    have := b2.val_le_one; have := b1.val_le_one; have := b0.val_le_one
    cases b7 with
    | bit0 =>
      cases b6 with
      | bit0 =>
        simp only [lebFuel, Bytes.ofList_cons, lebRead, List.map_cons, lebSpec, Byte.val,
          Bit.val_bit0, mk6_zero]
        rw [if_pos (by omega)]
        simp [LebOut.toState]
      | bit1 =>
        simp only [lebFuel, Bytes.ofList_cons, lebRead, List.map_cons, lebSpec, Byte.val,
          Bit.val_bit0, Bit.val_bit1]
        rw [if_neg (by omega)]
        rfl
    | bit1 =>
      simp only [lebFuel, Bytes.ofList_cons, lebRead, List.map_cons, lebSpec, Byte.val,
        Bit.val_bit1]
      rw [if_neg (by have := b6.val_le_one; omega)]
      rfl
  | .byte8 b7 b6 b5 b4 b3 b2 b1 b0 :: xs, k + 1 => by
    have := b6.val_le_one; have := b5.val_le_one; have := b4.val_le_one; have := b3.val_le_one
    have := b2.val_le_one; have := b1.val_le_one; have := b0.val_le_one
    cases b7 with
    | bit0 =>
      have e := mk7_ofNat b6 b5 b4 b3 b2 b1 b0 0
      rw [BinNat.ofNat_zero] at e
      simp only [lebFuel, Bytes.ofList_cons, lebRead, List.map_cons, lebSpec, Byte.val,
        Bit.val_bit0, e]
      rw [if_pos (by omega)]
      simp [LebOut.toState]
    | bit1 =>
      simp only [lebFuel, Bytes.ofList_cons, lebRead]
      rw [lebRead_spec xs k, Option.bind_some]
      simp only [List.map_cons, lebSpec, Byte.val, Bit.val_bit1]
      rw [if_neg (by omega)]
      have hx : 128 * 1 + 64 * b6.val + 32 * b5.val + 16 * b4.val + 8 * b3.val + 4 * b2.val +
          2 * b1.val + b0.val - 128 =
          64 * b6.val + 32 * b5.val + 16 * b4.val + 8 * b3.val + 4 * b2.val + 2 * b1.val +
            b0.val := by omega
      rw [hx]
      cases hS : lebSpec k (List.map Byte.val xs) with
      | needInput => rfl
      | badInteger => rfl
      | decoded w j =>
        simp only [LebOut.toState, lebJoinSpec]
        by_cases hw : w = 0
        · subst hw
          rw [if_pos rfl]
          rfl
        · rw [if_neg hw, BinNat.ofNat_of_ne_zero hw]
          simp only [lebJoin, Option.some.injEq, CodecState.decodedWord.injEq]
          rw [← BinNat.ofNat_of_ne_zero hw, mk7_ofNat]
          exact ⟨congrArg ofNat (by omega), by simp⟩

/-- **`LebRead`** with `k + 1` bytes of fuel on any byte string: what `lebSpec` computes on the
values of its bytes. -/
theorem lebRead_iff {k : Nat} {xs : Bytes} {r : CodecState} :
    LebRead (lebFuel k) xs r ↔ r = (lebSpec k (xs.toList.map Byte.val)).toState xs.toList := by
  have e := lebRead_spec xs.toList k
  rw [Bytes.ofList_toList] at e
  rw [lebRead_iff_fn, e, Option.some.injEq]
  exact eq_comm

theorem lebFuel_surjective (f : LebFuel) : ∃ k, lebFuel k = f := by
  induction f with
  | last => exact ⟨0, rfl⟩
  | more f ih =>
    obtain ⟨k, rfl⟩ := ih
    exact ⟨k + 1, rfl⟩

/-- `LebRead` has a result on every fuel and byte string. -/
theorem lebRead_total (f : LebFuel) (xs : Bytes) : ∃ r, LebRead f xs r := by
  obtain ⟨k, rfl⟩ := lebFuel_surjective f
  exact ⟨_, lebRead_iff.mpr rfl⟩

theorem lebRead_functional {f : LebFuel} {xs : Bytes} {r r' : CodecState} (h : LebRead f xs r)
    (h' : LebRead f xs r') : r = r' := by
  rw [lebRead_iff_fn] at h h'
  exact Option.some.inj (h.symm.trans h')

/-- **`LebJoin`** has a result on exactly the states `LebRead` gives (`NeedInput`, `BadInteger`,
`DecodedWord`); on a decoded canonical numeral it is `BadInteger` for zero and the joined number
otherwise. -/
theorem lebJoin_iff {b6 b5 b4 b3 b2 b1 b0 : Bit} {w : Nat} {rest : Bytes} {r : CodecState} :
    LebJoin b6 b5 b4 b3 b2 b1 b0 (.decodedWord (ofNat w) rest) r ↔
      r = if w = 0 then .badInteger else
        .decodedWord (ofNat (128 * w + (64 * b6.val + 32 * b5.val + 16 * b4.val + 8 * b3.val +
          4 * b2.val + 2 * b1.val + b0.val))) rest := by
  rw [lebJoin_iff_fn]
  by_cases hw : w = 0
  · subst hw
    rw [if_pos rfl]
    simp only [BinNat.ofNat_zero, lebJoin, Option.some.injEq]
    exact eq_comm
  · rw [if_neg hw, BinNat.ofNat_of_ne_zero hw]
    simp only [lebJoin, Option.some.injEq]
    rw [← BinNat.ofNat_of_ne_zero hw, mk7_ofNat]
    exact eq_comm

theorem lebJoin_total {b6 b5 b4 b3 b2 b1 b0 : Bit} {s : CodecState}
    (hs : s = .needInput ∨ s = .badInteger ∨ ∃ n rest, s = .decodedWord n rest) :
    ∃ r, LebJoin b6 b5 b4 b3 b2 b1 b0 s r := by
  rcases hs with rfl | rfl | ⟨n, rest, rfl⟩
  · exact ⟨_, .lebJoinShort⟩
  · exact ⟨_, .lebJoinBad⟩
  · cases n with
    | zero => exact ⟨_, .lebNonminimal⟩
    | bit bit n => exact ⟨_, lebJoin_iff_fn.mpr rfl⟩

theorem lebJoin_none_limitExceeded {b6 b5 b4 b3 b2 b1 b0 : Bit} (r : CodecState) :
    ¬ LebJoin b6 b5 b4 b3 b2 b1 b0 .limitExceeded r := nofun

theorem lebJoin_functional {b6 b5 b4 b3 b2 b1 b0 : Bit} {s r r' : CodecState}
    (h : LebJoin b6 b5 b4 b3 b2 b1 b0 s r) (h' : LebJoin b6 b5 b4 b3 b2 b1 b0 s r') : r = r' := by
  rw [lebJoin_iff_fn] at h h'
  exact Option.some.inj (h.symm.trans h')

/-- **`ReadULEB62`** on any byte string: what `lebSpec 8` computes on the values of its bytes. -/
theorem readULEB62_iff {xs : Bytes} {r : CodecState} :
    ReadULEB62 xs r ↔ r = (lebSpec 8 (xs.toList.map Byte.val)).toState xs.toList := by
  rw [← lebRead_iff]
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem readULEB62_total (xs : Bytes) : ∃ r, ReadULEB62 xs r := ⟨_, readULEB62_iff.mpr rfl⟩

theorem readULEB62_functional {xs : Bytes} {r r' : CodecState} (h : ReadULEB62 xs r)
    (h' : ReadULEB62 xs r') : r = r' :=
  (readULEB62_iff.mp h).trans (readULEB62_iff.mp h').symm

/-! ### `FNV`, `FNVFrom`, `FNVByte` -/

/-- The literal of `FnvInit`, its bits least significant first as the rule writes them: the 64-bit
FNV offset basis. -/
def fnvBasis : BinNat := BinNat.ofBits
    [.bit1, .bit0, .bit1, .bit0, .bit0, .bit1, .bit0, .bit0, .bit1, .bit1, .bit0, .bit0, .bit0,
      .bit1, .bit0, .bit0, .bit0, .bit1, .bit0, .bit0, .bit0, .bit1, .bit0, .bit0, .bit0, .bit0,
      .bit1, .bit0, .bit0, .bit0, .bit0, .bit1, .bit0, .bit0, .bit1, .bit0, .bit0, .bit1, .bit1,
      .bit1, .bit0, .bit0, .bit1, .bit1, .bit1, .bit0, .bit0, .bit1, .bit0, .bit1, .bit0, .bit0,
      .bit1, .bit1, .bit1, .bit1, .bit1, .bit1, .bit0, .bit1, .bit0, .bit0, .bit1, .bit1]

/-- The first literal of `FnvByte`: the width `64`. -/
def fnvWidth : BinNat := BinNat.ofBits [.bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit1]

/-- The second literal of `FnvByte`: the 64-bit FNV prime. -/
def fnvPrime : BinNat := BinNat.ofBits
    [.bit1, .bit1, .bit0, .bit0, .bit1, .bit1, .bit0, .bit1, .bit1, .bit0, .bit0, .bit0, .bit0,
      .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0,
      .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0, .bit0,
      .bit0, .bit1]

theorem fnvBasis_eq : fnvBasis = ofNat 14695981039346656037 := by decide

theorem fnvWidth_eq : fnvWidth = ofNat 64 := by decide

theorem fnvPrime_eq : fnvPrime = ofNat 1099511628211 := by decide

/-- `FNVByte`. -/
inductive FNVByte : BinNat → Byte → BinNat → Prop
  /-- `FnvByte: (FNVByte h b) ~> (NatTrim (64) (NatMultiply (1099511628211) (NatXor h (PackByte b
  (NatZero)))));` with the two literals written as the rule writes them (`fnvWidth`,
  `fnvPrime`). -/
  | fnvByte {h : BinNat} {b : Byte} {p x y r : BinNat} :
      PackByte b .zero p → NatXor h p x → NatMultiply fnvPrime x y → NatTrim fnvWidth y r →
        FNVByte h b r

/-- `FNVFrom`. -/
inductive FNVFrom : BinNat → Bytes → BinNat → Prop
  /-- `FnvDone: (FNVFrom h (BNil)) ~> h;` -/
  | fnvDone {h : BinNat} : FNVFrom h .nil h
  /-- `FnvNext: (FNVFrom h (BCons b xs)) ~> (FNVFrom (FNVByte h b) xs);` -/
  | fnvNext {h : BinNat} {b : Byte} {xs : Bytes} {h' r : BinNat} :
      FNVByte h b h' → FNVFrom h' xs r → FNVFrom h (.cons b xs) r

/-- `FNV`. -/
inductive FNV : Bytes → BinNat → Prop
  /-- `FnvInit: (FNV xs) ~> (FNVFrom (14695981039346656037) xs);` with the literal as the rule
  writes it (`fnvBasis`). -/
  | fnvInit {xs : Bytes} {r : BinNat} : FNVFrom fnvBasis xs r → FNV xs r

/-- One step of 64-bit FNV-1a on numbers: `(prime * (h xor b)) mod 2^64`. -/
def fnvStep (h c : Nat) : Nat := (1099511628211 * (h ^^^ c)) % 2 ^ 64

/-- 64-bit FNV-1a of a list of byte values. -/
def fnvSpec (l : List Nat) : Nat := l.foldl fnvStep 14695981039346656037

/-- What the rule of `FNVByte` computes. -/
def fnvByteFn (h : BinNat) (b : Byte) : Option BinNat :=
  natTrim fnvWidth (natMultiply fnvPrime (natXor h (packByte b .zero)))

/-- What the rules of `FNVFrom` compute. -/
def fnvFromFn : BinNat → Bytes → Option BinNat
  | h, .nil => some h
  | h, .cons b xs => (fnvByteFn h b).bind fun h' => fnvFromFn h' xs

theorem fnvByte_iff_fn {h : BinNat} {b : Byte} {r : BinNat} :
    FNVByte h b r ↔ fnvByteFn h b = some r := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    rw [packByte_iff_fn.mp h₁] at h₂
    rw [natXor_iff_fn.mp h₂] at h₃
    rw [natMultiply_iff_fn.mp h₃] at h₄
    exact natTrim_iff_fn.mp h₄
  · intro e
    exact .fnvByte (packByte_iff_fn.mpr rfl) (natXor_iff_fn.mpr rfl) (natMultiply_iff_fn.mpr rfl)
      (natTrim_iff_fn.mpr e)

/-- `FNVByte` on any numeral `h`: the canonical numeral of `(prime * (h xor b)) mod 2^64`. -/
theorem fnvByteFn_eq (h : BinNat) (b : Byte) :
    fnvByteFn h b = some (ofNat (fnvStep h.val b.val)) := by
  unfold fnvByteFn
  rw [fnvWidth_eq, natTrim_ofNat]
  simp [fnvStep, fnvPrime_eq]

theorem fnvFrom_iff_fn {h : BinNat} {xs : Bytes} {r : BinNat} :
    FNVFrom h xs r ↔ fnvFromFn h xs = some r := by
  constructor
  · intro hd
    induction hd with
    | fnvDone => rfl
    | fnvNext h₁ _ ih => simp only [fnvFromFn, fnvByte_iff_fn.mp h₁, Option.bind_some, ih]
  · intro e
    induction xs generalizing h r with
    | nil =>
      simp only [fnvFromFn, Option.some.injEq] at e
      subst e
      exact .fnvDone
    | cons b xs ih =>
      simp only [fnvFromFn, Option.bind_eq_some_iff] at e
      obtain ⟨h', h₁, h₂⟩ := e
      exact .fnvNext (fnvByte_iff_fn.mpr h₁) (ih h₂)

theorem fnvFromFn_eq (xs : Bytes) : ∀ {h : BinNat}, h.Canonical →
    fnvFromFn h xs = some (ofNat ((xs.toList.map Byte.val).foldl fnvStep h.val)) := by
  induction xs with
  | nil => intro h hc; simp [fnvFromFn, BinNat.ofNat_val hc]
  | cons b xs ih =>
    intro h _
    simp only [fnvFromFn, fnvByteFn_eq, Option.bind_some, ih (canonical_ofNat _), val_ofNat,
      Bytes.toList_cons, List.map_cons, List.foldl_cons]

/-- **`FNVFrom`** from a canonical numeral: the canonical numeral of FNV-1a continued from it. -/
theorem fnvFrom_iff {v : Nat} {xs : Bytes} {r : BinNat} :
    FNVFrom (ofNat v) xs r ↔ r = ofNat ((xs.toList.map Byte.val).foldl fnvStep v) := by
  rw [fnvFrom_iff_fn, fnvFromFn_eq xs (canonical_ofNat v), val_ofNat, Option.some.injEq]
  exact eq_comm

/-- **`FNV`** is 64-bit FNV-1a of the values of the bytes. -/
theorem fnv_iff {xs : Bytes} {r : BinNat} : FNV xs r ↔ r = ofNat (fnvSpec (xs.toList.map Byte.val)) := by
  unfold fnvSpec
  rw [← fnvFrom_iff, ← fnvBasis_eq]
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- **`FNVByte`** on every numeral `h`. -/
theorem fnvByte_iff {h : BinNat} {b : Byte} {r : BinNat} :
    FNVByte h b r ↔ r = ofNat (fnvStep h.val b.val) := by
  rw [fnvByte_iff_fn, fnvByteFn_eq, Option.some.injEq]
  exact eq_comm

theorem fnvByte_total (h : BinNat) (b : Byte) : ∃ r, FNVByte h b r := ⟨_, fnvByte_iff.mpr rfl⟩

theorem fnvByte_functional {h : BinNat} {b : Byte} {r r' : BinNat} (h₁ : FNVByte h b r)
    (h₂ : FNVByte h b r') : r = r' :=
  (fnvByte_iff.mp h₁).trans (fnvByte_iff.mp h₂).symm

theorem fnvFrom_total (h : BinNat) (xs : Bytes) : ∃ r, FNVFrom h xs r := by
  induction xs generalizing h with
  | nil => exact ⟨_, .fnvDone⟩
  | cons b xs ih =>
    obtain ⟨r, hr⟩ := ih (ofNat (fnvStep h.val b.val))
    exact ⟨r, .fnvNext (fnvByte_iff.mpr rfl) hr⟩

theorem fnvFrom_functional {h : BinNat} {xs : Bytes} {r r' : BinNat} (h₁ : FNVFrom h xs r)
    (h₂ : FNVFrom h xs r') : r = r' := by
  rw [fnvFrom_iff_fn] at h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

theorem fnv_total (xs : Bytes) : ∃ r, FNV xs r := ⟨_, fnv_iff.mpr rfl⟩

theorem fnv_functional {xs : Bytes} {r r' : BinNat} (h : FNV xs r) (h' : FNV xs r') : r = r' :=
  (fnv_iff.mp h).trans (fnv_iff.mp h').symm

/-! ### `LookupSchema` and `SelectSchema` -/

mutual

/-- `LookupSchema`. -/
inductive LookupSchema : Byte → Schemas → FoundLayout → Prop
  /-- `LookupEmpty: (LookupSchema op (SchemasNil)) ~> (NoLayout);` -/
  | lookupEmpty {op : Byte} : LookupSchema op .nil .noLayout
  /-- `LookupMore: (LookupSchema op (SchemasCons (RecordSchema tag fields) rest)) ~> (SelectSchema
  (NatCompare (PackByte op (NatZero)) (PackByte tag (NatZero))) op fields rest);` -/
  | lookupMore {op tag : Byte} {fields : FieldLayout} {rest : Schemas} {p q : BinNat} {o : Cmp}
      {r : FoundLayout} :
      PackByte op .zero p → PackByte tag .zero q → NatCompare p q o → SelectSchema o op fields rest r →
        LookupSchema op (.cons (.recordSchema tag fields) rest) r

/-- `SelectSchema`. -/
inductive SelectSchema : Cmp → Byte → FieldLayout → Schemas → FoundLayout → Prop
  /-- `LookupEqual: (SelectSchema (Equal) op fields rest) ~> (FoundLayout fields);` -/
  | lookupEqual {op : Byte} {fields : FieldLayout} {rest : Schemas} :
      SelectSchema .equal op fields rest (.foundLayout fields)
  /-- `LookupLess: (SelectSchema (Less) op fields rest) ~> (LookupSchema op rest);` -/
  | lookupLess {op : Byte} {fields : FieldLayout} {rest : Schemas} {r : FoundLayout} :
      LookupSchema op rest r → SelectSchema .less op fields rest r
  /-- `LookupGreater: (SelectSchema (Greater) op fields rest) ~> (LookupSchema op rest);` -/
  | lookupGreater {op : Byte} {fields : FieldLayout} {rest : Schemas} {r : FoundLayout} :
      LookupSchema op rest r → SelectSchema .greater op fields rest r

end

/-- What the rules of `LookupSchema` compute: the layout of the first schema whose tag is the
opcode. -/
def lookupSchema (op : Byte) : Schemas → FoundLayout
  | .nil => .noLayout
  | .cons (.recordSchema tag fields) rest =>
    match natCompare (packByte op .zero) (packByte tag .zero) with
    | .equal => .foundLayout fields
    | .less => lookupSchema op rest
    | .greater => lookupSchema op rest

/-- What the rules of `SelectSchema` compute. -/
def selectSchema : Cmp → Byte → FieldLayout → Schemas → FoundLayout
  | .equal, _, fields, _ => .foundLayout fields
  | .less, op, _, rest => lookupSchema op rest
  | .greater, op, _, rest => lookupSchema op rest

theorem lookupSchema_cons (op tag : Byte) (fields : FieldLayout) (rest : Schemas) :
    lookupSchema op (.cons (.recordSchema tag fields) rest) =
      selectSchema (natCompare (packByte op .zero) (packByte tag .zero)) op fields rest := by
  rw [lookupSchema]
  cases natCompare (packByte op .zero) (packByte tag .zero) <;> rfl

theorem lookupSchema_iff_fn {op : Byte} {ss : Schemas} {r : FoundLayout} :
    LookupSchema op ss r ↔ r = lookupSchema op ss := by
  constructor
  · intro h
    induction ss generalizing r with
    | nil => cases h; rfl
    | cons s rest ih =>
      cases h with
      | lookupMore h₁ h₂ h₃ h₄ =>
        rw [lookupSchema_cons, ← packByte_iff_fn.mp h₁, ← packByte_iff_fn.mp h₂,
          ← natCompare_iff_fn.mp h₃]
        cases h₄ with
        | lookupEqual => rfl
        | lookupLess h => exact ih h
        | lookupGreater h => exact ih h
  · rintro rfl
    induction ss with
    | nil => exact .lookupEmpty
    | cons s rest ih =>
      obtain ⟨tag, fields⟩ := s
      rw [lookupSchema_cons]
      refine .lookupMore (packByte_iff_fn.mpr rfl) (packByte_iff_fn.mpr rfl)
        (natCompare_iff_fn.mpr rfl) ?_
      cases natCompare (packByte op .zero) (packByte tag .zero)
      · exact .lookupLess ih
      · exact .lookupEqual
      · exact .lookupGreater ih

theorem selectSchema_iff_fn {o : Cmp} {op : Byte} {fields : FieldLayout} {rest : Schemas}
    {r : FoundLayout} : SelectSchema o op fields rest r ↔ r = selectSchema o op fields rest := by
  constructor
  · rintro (_ | h | h)
    · rfl
    · exact lookupSchema_iff_fn.mp h
    · exact lookupSchema_iff_fn.mp h
  · rintro rfl
    cases o
    · exact .lookupLess (lookupSchema_iff_fn.mpr rfl)
    · exact .lookupEqual
    · exact .lookupGreater (lookupSchema_iff_fn.mpr rfl)

/-- The first layout whose tag is the opcode, found by equality of bytes. -/
def findLayout (op : Byte) : Schemas → FoundLayout
  | .nil => .noLayout
  | .cons (.recordSchema tag fields) rest => if op = tag then .foundLayout fields else findLayout op rest

theorem lookupSchema_eq (op : Byte) : ∀ ss : Schemas, lookupSchema op ss = findLayout op ss
  | .nil => rfl
  | .cons (.recordSchema tag fields) rest => by
    rw [lookupSchema_cons, natCompare_packByte, findLayout]
    by_cases h : op = tag
    · subst h
      rw [if_pos rfl, Cmp.ofNats_eq_equal_iff.mpr rfl]
      rfl
    · rw [if_neg h]
      have hv : op.val ≠ tag.val := fun e => h (Byte.val_injective e)
      unfold Cmp.ofNats
      by_cases h₁ : op.val < tag.val
      · rw [if_pos h₁]
        exact lookupSchema_eq op rest
      · rw [if_neg h₁, if_neg hv]
        exact lookupSchema_eq op rest

/-- **`LookupSchema`** has exactly one result on every opcode and schema list: the layout of the
first schema with that tag, or `NoLayout`. -/
theorem lookupSchema_iff {op : Byte} {ss : Schemas} {r : FoundLayout} :
    LookupSchema op ss r ↔ r = findLayout op ss := by
  rw [lookupSchema_iff_fn, lookupSchema_eq]

theorem lookupSchema_total (op : Byte) (ss : Schemas) : ∃ r, LookupSchema op ss r :=
  ⟨_, lookupSchema_iff_fn.mpr rfl⟩

theorem lookupSchema_functional {op : Byte} {ss : Schemas} {r r' : FoundLayout}
    (h : LookupSchema op ss r) (h' : LookupSchema op ss r') : r = r' :=
  (lookupSchema_iff_fn.mp h).trans (lookupSchema_iff_fn.mp h').symm

/-- **`SelectSchema`**: on `Equal` the layout given, otherwise the lookup in the rest. -/
theorem selectSchema_iff {o : Cmp} {op : Byte} {fields : FieldLayout} {rest : Schemas}
    {r : FoundLayout} :
    SelectSchema o op fields rest r ↔ r = if o = .equal then .foundLayout fields else findLayout op rest := by
  rw [selectSchema_iff_fn]
  cases o <;> simp [selectSchema, lookupSchema_eq]

theorem selectSchema_total (o : Cmp) (op : Byte) (fields : FieldLayout) (rest : Schemas) :
    ∃ r, SelectSchema o op fields rest r := ⟨_, selectSchema_iff_fn.mpr rfl⟩

theorem selectSchema_functional {o : Cmp} {op : Byte} {fields : FieldLayout} {rest : Schemas}
    {r r' : FoundLayout} (h : SelectSchema o op fields rest r) (h' : SelectSchema o op fields rest r') :
    r = r' :=
  (selectSchema_iff_fn.mp h).trans (selectSchema_iff_fn.mp h').symm


/-! ## The C models

Each C function is modelled on the numbers its words hold (a word of the sort `Nat` holds a
natural, a word of the sort `Byte` holds a byte value) and, for the sort `Bytes`, on slices and
interned strings (`Slice`).  A model returns `none` where the C stops the run
(`rc_refinement_fail`), except `bnPred`, whose `none` is the C's `NULL`: no rule applies. -/

/-! ### Naturals of any size (`rc_bignat.c`) -/

/-- `RC_BN_SMALL`: the naturals below are immediates, the others interned magnitudes. -/
def bnSmall : Nat := 2 ^ 62

/-- `RC_BN_LIMBS * 64`: the bits a natural may have.  Irreducible, so that nothing evaluates
`2 ^ bnBits`. -/
@[irreducible] def bnBits : Nat := 16384 * 64

theorem bnBits_eq : bnBits = 16384 * 64 := by unfold bnBits; rfl

/-- The naturals the C represents: `mag_value` stops the run on any natural of `2 ^ 20` bits or
more. -/
def bnLimit : Nat := 2 ^ bnBits

theorem bnSmall_lt_bnLimit : bnSmall < bnLimit :=
  Nat.pow_lt_pow_right (by decide) (by rw [bnBits_eq]; decide)

theorem two_pow_64_le_bnLimit : 2 ^ 64 ≤ bnLimit :=
  Nat.pow_le_pow_right (by decide) (by rw [bnBits_eq]; decide)

/-- `mag_value`: the value of a computed magnitude; at `bnLimit` or above it stops the run. -/
def magValue (v : Nat) : Option Nat := if v < bnLimit then some v else none

theorem magValue_eq_some_iff {v w : Nat} : magValue v = some w ↔ v < bnLimit ∧ w = v := by
  unfold magValue
  split
  · rename_i h
    exact ⟨fun e => ⟨h, (Option.some.inj e).symm⟩, fun ⟨_, e⟩ => e ▸ rfl⟩
  · rename_i h
    exact ⟨nofun, fun ⟨h', _⟩ => absurd h' h⟩

theorem magValue_eq_none_iff {v : Nat} : magValue v = none ↔ bnLimit ≤ v := by
  unfold magValue
  split <;> rename_i h
  · exact ⟨nofun, fun h' => absurd h (by omega)⟩
  · exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem magValue_of_lt {v : Nat} (h : v < bnLimit) : magValue v = some v := by
  unfold magValue
  rw [if_pos h]

/-- `rc_bn_shl1_or(x, bit)`: `2 x + (bit & 1)`; an immediate below `2 ^ 61` gives an immediate,
anything else goes through `mag_value`. -/
def bnShl1Or (x bit : Nat) : Option Nat :=
  if x < bnSmall / 2 then some (2 * x + bit % 2) else magValue (2 * x + bit % 2)

theorem bnShl1Or_eq (x bit : Nat) : bnShl1Or x bit = magValue (2 * x + bit % 2) := by
  unfold bnShl1Or
  split
  · rename_i h
    have := bnSmall_lt_bnLimit
    unfold bnSmall at h this
    rw [magValue_of_lt (by omega)]
  · rfl

/-- `rc_bn_add`: the sum of two immediates is an immediate while below `2 ^ 62`; any other sum
goes through `mag_value`. -/
def bnAdd (a b : Nat) : Option Nat :=
  if a < bnSmall ∧ b < bnSmall ∧ a + b < bnSmall then some (a + b) else magValue (a + b)

theorem bnAdd_eq (a b : Nat) : bnAdd a b = magValue (a + b) := by
  unfold bnAdd
  split
  · rename_i h
    rw [magValue_of_lt (Nat.lt_trans h.2.2 bnSmall_lt_bnLimit)]
  · rfl

/-- `rc_bn_succ`: `rc_bn_add(a, 1)`. -/
def bnSucc (a : Nat) : Option Nat := bnAdd a 1

/-- `rc_bn_sub`: `a - b` when `b ≤ a`, else `0` (the immediate and the limb branch alike). -/
def bnSub (a b : Nat) : Nat := if a < b then 0 else a - b

theorem bnSub_eq (a b : Nat) : bnSub a b = a - b := by
  unfold bnSub
  split <;> omega

/-- `rc_bn_pred`: `NULL` (no rule applies) for `0`, else `rc_bn_sub(a, 1)`. -/
def bnPred (a : Nat) : Option Nat := if a = 0 then none else some (bnSub a 1)

/-- `rc_bn_xor`. -/
def bnXor (a b : Nat) : Option Nat :=
  if a < bnSmall ∧ b < bnSmall then some (a ^^^ b) else magValue (a ^^^ b)

theorem bnXor_eq {a b : Nat} (ha : a < bnLimit) (hb : b < bnLimit) :
    bnXor a b = some (a ^^^ b) := by
  unfold bnXor
  split
  · rfl
  · exact magValue_of_lt (Nat.xor_lt_two_pow ha hb)

/-- `rc_bn_cmp`. -/
def bnCmp (a b : Nat) : Int := if a < b then -1 else if b < a then 1 else 0

/-- The number of bits of a natural. -/
def bitLen (v : Nat) : Nat := if v = 0 then 0 else Nat.log2 v + 1

/-- `mag_of`: the 64-bit limbs of a natural: `0` or `1` for an immediate, `(bytes + 7) / 8` for an
interned magnitude of `bytes` bytes (no high zero byte). -/
def magLimbs (v : Nat) : Nat :=
  if v < bnSmall then (if v = 0 then 0 else 1) else ((bitLen v + 7) / 8 + 7) / 8

theorem lt_two_pow_magLimbs (v : Nat) : v < 2 ^ (64 * magLimbs v) := by
  unfold magLimbs
  split
  · rename_i h
    split
    · rename_i h0
      subst h0
      decide
    · have : bnSmall ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)
      rw [Nat.mul_one]
      omega
  · rename_i h
    have hv : v ≠ 0 := by have : 0 < bnSmall := Nat.two_pow_pos 62; omega
    have h₁ := Nat.lt_log2_self (n := v)
    unfold bitLen
    rw [if_neg hv]
    refine Nat.lt_of_lt_of_le h₁ (Nat.pow_le_pow_right (by decide) ?_)
    omega

/-- `rc_bn_mul`: two immediates multiply in 128 bits; otherwise the run stops when the limbs of the
two factors are more than `RC_BN_LIMBS` together, and the product goes through `mag_value`. -/
def bnMul (a b : Nat) : Option Nat :=
  if a < bnSmall ∧ b < bnSmall then magValue (a * b)
  else if 16384 + 1 < magLimbs a + magLimbs b + 1 then none else magValue (a * b)

theorem bnMul_eq (a b : Nat) :
    bnMul a b = if 16384 < magLimbs a + magLimbs b then none else some (a * b) := by
  have hprod : magLimbs a + magLimbs b ≤ 16384 → a * b < bnLimit := by
    intro h
    have h₁ := Nat.mul_lt_mul_of_lt_of_lt (lt_two_pow_magLimbs a) (lt_two_pow_magLimbs b)
    rw [← Nat.pow_add, ← Nat.mul_add] at h₁
    refine Nat.lt_of_lt_of_le h₁ (Nat.pow_le_pow_right (by decide) ?_)
    rw [bnBits_eq]
    omega
  unfold bnMul
  split
  · rename_i hs
    have ha : magLimbs a ≤ 1 := by unfold magLimbs; rw [if_pos hs.1]; split <;> omega
    have hb : magLimbs b ≤ 1 := by unfold magLimbs; rw [if_pos hs.2]; split <;> omega
    rw [if_neg (by omega), magValue_of_lt (hprod (by omega))]
  · split
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), magValue_of_lt (hprod (by omega))]

/-- `rc_bn_trim(a, width)`: `a` itself when the width does not fit 64 bits or is `2 ^ 20` or
more; an immediate masked below `62` bits; an interned magnitude with the limbs above the width
cleared. -/
def bnTrim (a w : Nat) : Nat :=
  if ¬ w < 2 ^ 64 ∨ 16384 * 64 ≤ w then a
  else if a < bnSmall then (if 62 ≤ w then a else a &&& (2 ^ w - 1))
  else a % 2 ^ w

theorem bnTrim_eq {a : Nat} (ha : a < bnLimit) (w : Nat) : bnTrim a w = a % 2 ^ w := by
  unfold bnTrim
  split
  · rename_i h
    have : bnLimit ≤ 2 ^ w := by
      unfold bnLimit
      refine Nat.pow_le_pow_right (by decide) ?_
      rw [bnBits_eq]
      rcases h with h | h
      · have : 2 ^ 20 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by decide)
        have : w ≥ 2 ^ 64 := by omega
        have : (2 : Nat) ^ 20 = 1048576 := by decide
        omega
      · exact h
    rw [Nat.mod_eq_of_lt (by omega)]
  · split
    · split
      · rename_i hs hw
        have : bnSmall ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
        rw [Nat.mod_eq_of_lt (by omega)]
      · exact Nat.and_two_pow_sub_one_eq_mod a w
    · rfl

/-- The loop of `rc_bn_pack`: `rc_bn_shl1_or(s, 0)` `k` times. -/
def bnShl1Iter : Nat → Nat → Option Nat
  | 0, s => some s
  | k + 1, s => (bnShl1Or s 0).bind (bnShl1Iter k)

/-- `rc_bn_pack(high, v, bits)`: `(high << bits) | v` when `high` is an immediate small enough,
otherwise `high` shifted one bit at a time, then `rc_bn_add` of `v`. -/
def bnPack (high v bits : Nat) : Option Nat :=
  if high < bnSmall ∧ bits < 62 ∧ high < bnSmall >>> bits then some ((high <<< bits) ||| v)
  else (bnShl1Iter bits high).bind fun s => bnAdd s v

theorem bnShl1Iter_eq : ∀ (k : Nat) {s : Nat}, s < bnLimit → bnShl1Iter k s = magValue (2 ^ k * s)
  | 0, s, hs => by rw [bnShl1Iter, Nat.pow_zero, Nat.one_mul, magValue_of_lt hs]
  | k + 1, s, hs => by
    rw [bnShl1Iter, bnShl1Or_eq, Nat.zero_mod, Nat.add_zero]
    have e : 2 ^ (k + 1) * s = 2 ^ k * (2 * s) := by rw [Nat.pow_succ, Nat.mul_assoc]
    by_cases h2 : 2 * s < bnLimit
    · rw [magValue_of_lt h2, Option.bind_some, bnShl1Iter_eq k h2, e]
    · have h3 : 2 * s ≤ 2 ^ (k + 1) * s :=
        Nat.mul_le_mul_right s (Nat.le_self_pow (Nat.succ_ne_zero k) 2)
      rw [magValue_eq_none_iff.mpr (by omega), Option.bind_none,
        magValue_eq_none_iff.mpr (by omega)]

theorem bnPack_eq {high v : Nat} (hh : high < bnLimit) (hv : v < 256) :
    bnPack high v 8 = magValue (256 * high + v) := by
  unfold bnPack
  split
  · rename_i h
    have e8 : (2 : Nat) ^ 8 = 256 := by decide
    have hlt : v < 2 ^ 8 := by rw [e8]; exact hv
    rw [← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, e8]
    have h₁ : high < 2 ^ 54 := by
      have := h.2.2
      unfold bnSmall at this
      rw [Nat.shiftRight_eq_div_pow] at this
      have e : 2 ^ 62 / 2 ^ 8 = 2 ^ 54 := by decide
      omega
    have e54 : (2 : Nat) ^ 54 = 18014398509481984 := by decide
    have e62 : bnSmall = 4611686018427387904 := by decide
    rw [e54] at h₁
    rw [magValue_of_lt (by have := bnSmall_lt_bnLimit; omega)]
    congr 1
    omega
  · rw [bnShl1Iter_eq 8 hh]
    by_cases h₁ : 2 ^ 8 * high < bnLimit
    · rw [magValue_of_lt h₁, Option.bind_some, bnAdd_eq]
    · rw [magValue_eq_none_iff.mpr (by omega), Option.bind_none,
        magValue_eq_none_iff.mpr (by omega)]


/-! ### The representation of `Byte`: words of eight bits, the first child most significant -/

/-- `RC_MKV_word_1(c, n, k)`: `v = (v << 1) | RC_BIT_word_1(k[i])` over the children in order. -/
def wordMk (ks : List Bit) : Nat := ks.foldl (fun v k => (v <<< 1) ||| k.val) 0

theorem shl1_or_val (v : Nat) (k : Bit) : (v <<< 1) ||| k.val = 2 * v + k.val := by
  have hk : k.val < 2 ^ 1 := by have := k.val_le_one; omega
  rw [← Nat.shiftLeft_add_eq_or_of_lt hk, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]

/-- `RC_MK8_word_1` builds the word of the value of the byte of its eight children. -/
theorem wordMk_byte8 (b7 b6 b5 b4 b3 b2 b1 b0 : Bit) :
    wordMk [b7, b6, b5, b4, b3, b2, b1, b0] = (Byte.byte8 b7 b6 b5 b4 b3 b2 b1 b0).val := by
  simp only [wordMk, List.foldl_cons, List.foldl_nil, shl1_or_val, Byte.val]
  omega

/-- **Build, then view**: the views of the word `RC_MK8_word_1` builds give its eight children
back. -/
theorem ofWord_wordMk (b7 b6 b5 b4 b3 b2 b1 b0 : Bit) :
    Byte.ofWord (wordMk [b7, b6, b5, b4, b3, b2, b1, b0]) = .byte8 b7 b6 b5 b4 b3 b2 b1 b0 := by
  rw [wordMk_byte8, Byte.ofWord_val]

/-- **View, then build**: building from the eight views of a word below `256` gives the word. -/
theorem wordMk_kids {v : Nat} (h : v < 256) :
    wordMk [wordKid v 0, wordKid v 1, wordKid v 2, wordKid v 3, wordKid v 4, wordKid v 5,
      wordKid v 6, wordKid v 7] = v :=
  (wordMk_byte8 _ _ _ _ _ _ _ _).trans (Byte.val_ofWord v h)

/-! ### The representation of `Nat`: naturals viewed as `NatZero` / `NatBit (n mod 2) (n div 2)` -/

/-- The constructors of the sort `Nat`, as `RC_TAG_binary_5` names them. -/
inductive NatTag
  /-- `NatZero`. -/
  | natZero
  /-- `NatBit`. -/
  | natBit
  deriving DecidableEq, Repr

/-- `RC_TAG_binary_5`: `rc_bn_is_zero(x) ? NatZero : NatBit`. -/
def binTag (v : Nat) : NatTag := if v = 0 then .natZero else .natBit

/-- `RC_KID_binary_5(x, 0)`: `rc_bn_low_bit(x) ? Bit1 : Bit0` (the low bit of an immediate, or of
the first byte of a magnitude). -/
def binKid0 (v : Nat) : Bit := if v &&& 1 ≠ 0 then .bit1 else .bit0

/-- `RC_KID_binary_5(x, 1)`: `rc_bn_shr1(x)`. -/
def binKid1 (v : Nat) : Nat := v >>> 1

/-- `RC_NUL_binary_5`: the immediate `0`. -/
def binNul : Nat := 0

/-- `RC_MK2_binary_5(c, b, n)`: stops the run on `NatBit Bit0 NatZero`, otherwise
`rc_bn_shl1_or(n, b == Bit1)`. -/
def binMk2 (b : Bit) (n : Nat) : Option Nat :=
  if b = .bit0 ∧ n = 0 then none else bnShl1Or n (if b = .bit1 then 1 else 0)

theorem binKid0_eq (v : Nat) : binKid0 v = Bit.ofLow v := by
  unfold binKid0 Bit.ofLow
  rw [Nat.and_one_is_mod]
  by_cases h : v % 2 = 1
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

/-- `RC_TAG_binary_5` answers `NatZero` exactly on the word whose numeral is `NatZero`. -/
theorem binTag_eq_natZero_iff {v : Nat} : binTag v = .natZero ↔ ofNat v = .zero := by
  unfold binTag
  rw [BinNat.ofNat_eq_zero_iff]
  by_cases h : v = 0
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨nofun, fun h' => absurd h' h⟩

/-- **The views of a word tagged `NatBit`** read its numeral: the low bit over the numeral of the
half. -/
theorem binView {v : Nat} (h : binTag v = .natBit) :
    ofNat v = .bit (binKid0 v) (ofNat (binKid1 v)) := by
  have hv : v ≠ 0 := by
    intro e
    unfold binTag at h
    rw [if_pos e] at h
    exact absurd h nofun
  rw [BinNat.ofNat_of_ne_zero hv, binKid0_eq, binKid1, Nat.shiftRight_eq_div_pow, Nat.pow_one]

theorem binNul_read : ofNat binNul = .zero := rfl

theorem bit_ite_eq_val (b : Bit) : (if b = .bit1 then 1 else 0) = b.val := by
  cases b <;> rfl

/-- **The builder** stops the run exactly on `NatBit Bit0 NatZero` (which no canonical numeral
is) and on numbers of `2 ^ 20` bits or more. -/
theorem binMk2_eq_none_iff {b : Bit} {n : Nat} :
    binMk2 b n = none ↔ (b = .bit0 ∧ n = 0) ∨ bnLimit ≤ 2 * n + b.val := by
  unfold binMk2
  split
  · rename_i h
    exact ⟨fun _ => Or.inl h, fun _ => rfl⟩
  · rename_i h
    rw [bnShl1Or_eq, bit_ite_eq_val, magValue_eq_none_iff,
      Nat.mod_eq_of_lt (by have := b.val_le_one; omega)]
    exact ⟨Or.inr, fun h' => h'.resolve_left h⟩

/-- **What the builder builds** reads back as `NatBit b` over the numeral of `n`. -/
theorem binMk2_read {b : Bit} {n m : Nat} (h : binMk2 b n = some m) :
    ofNat m = .bit b (ofNat n) := by
  unfold binMk2 at h
  split at h
  · exact absurd h nofun
  · rename_i hb
    rw [bnShl1Or_eq, bit_ite_eq_val, magValue_eq_some_iff,
      Nat.mod_eq_of_lt (by have := b.val_le_one; omega)] at h
    rw [h.2]
    refine BinNat.ofNat_two_mul_add ?_
    cases b with
    | bit0 => exact Or.inl (fun hn => hb ⟨rfl, hn⟩)
    | bit1 => exact Or.inr rfl

/-! ### The representation of `Bytes`: slices of the run's input, or interned strings -/

/-- `RC_SL_MAX`. -/
def slMax : Nat := 0x7fffffff

theorem slMax_eq : slMax = 2 ^ 31 - 1 := by decide

/-- A word of the sort `Bytes`. -/
inductive Slice
  /-- An immediate: the slice `start << 31 | end` of the run's input. -/
  | imm (v : Nat)
  /-- An interned byte string. -/
  | interned (bs : List UInt8)
  deriving DecidableEq, Repr

/-- `rc_sl_start`. -/
def slStart (v : Nat) : Nat := v >>> 31

/-- `rc_sl_end`. -/
def slEnd (v : Nat) : Nat := v &&& slMax

/-- `rc_sl_make`. -/
def slMake (s e : Nat) : Slice := .imm ((s <<< 31) ||| e)

theorem slStart_enc {s e : Nat} (he : e < 2 ^ 31) : (s * 2 ^ 31 + e) >>> 31 = s := by
  rw [Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 31),
    Nat.div_eq_of_lt he, Nat.zero_add]

theorem slEnd_enc {s e : Nat} (he : e < 2 ^ 31) : (s * 2 ^ 31 + e) &&& slMax = e := by
  rw [slMax_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt he]

/-- `rc_sl_start` and `rc_sl_end` of `rc_sl_make(s, e)` are `s` and `e` when `e ≤ RC_SL_MAX`. -/
theorem slMake_fields {s e : Nat} (he : e ≤ slMax) :
    slStart ((s <<< 31) ||| e) = s ∧ slEnd ((s <<< 31) ||| e) = e := by
  have h31 : (2 : Nat) ^ 31 = 2147483648 := by decide
  have he' : e < 2 ^ 31 := by rw [h31]; unfold slMax at he; omega
  have e1 : (s <<< 31) ||| e = s * 2 ^ 31 + e := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt he', Nat.shiftLeft_eq]
  refine ⟨?_, ?_⟩
  · show ((s <<< 31) ||| e) >>> 31 = s
    rw [e1]
    exact slStart_enc he'
  · show ((s <<< 31) ||| e) &&& slMax = e
    rw [e1]
    exact slEnd_enc he'

/-- `rc_sl_length`. -/
def slLength : Slice → Nat
  | .imm v => slEnd v - slStart v
  | .interned bs => bs.length

/-- `rc_sl_data`: the bytes from the value's first on. -/
def slData (buf : List UInt8) : Slice → List UInt8
  | .imm v => buf.drop (slStart v)
  | .interned bs => bs

/-- The content of a value: its `rc_sl_length` bytes from `rc_sl_data`. -/
def content (buf : List UInt8) (x : Slice) : List UInt8 := (slData buf x).take (slLength x)

/-- `rc_sl_first`. -/
def slFirst (buf : List UInt8) (x : Slice) : UInt8 := (slData buf x).headD 0

/-- `rc_sl_rest`: a slice one byte shorter, or the interned string of the remaining bytes. -/
def slRest : Slice → Slice
  | .imm v => slMake (slStart v + 1) (slEnd v)
  | .interned bs => .interned bs.tail

/-- `rc_sl_cons(b, s)`: the slice one byte longer when the input's byte before the slice is `b`,
otherwise (`rc_sl_cons_big`) the interned string of `b` and the content. -/
def slCons (buf : List UInt8) (b : Nat) : Slice → Slice
  | .imm v =>
    if 0 < slStart v ∧ buf[slStart v - 1]? = some (UInt8.ofNat b) then
      slMake (slStart v - 1) (slEnd v)
    else .interned (UInt8.ofNat b :: content buf (.imm v))
  | .interned bs => .interned (UInt8.ofNat b :: bs)

/-- `RC_NUL_slices_3`: the immediate `0`, the empty slice. -/
def slNil : Slice := .imm 0

/-- `rc_sl_take`. -/
def slTake : Slice → Nat → Slice
  | .imm v, n => slMake (slStart v) (slStart v + n)
  | .interned bs, n => .interned (bs.take n)

/-- `rc_sl_drop`. -/
def slDrop : Slice → Nat → Slice
  | .imm v, n => slMake (slStart v + n) (slEnd v)
  | .interned bs, n => .interned (bs.drop n)

/-- `rc_sl_equal`: equal lengths and, unless empty, `memcmp` of the data over the length. -/
def slEqual (buf : List UInt8) (x y : Slice) : Bool :=
  slLength x == slLength y &&
    (slLength x == 0 || (slData buf x).take (slLength x) == (slData buf y).take (slLength x))

/-- `rc_bytes_input`: the whole input as a slice. -/
def slInput (buf : List UInt8) : Slice := slMake 0 buf.length

/-- A value fits the input: a slice lies within it. -/
inductive SliceValid (buf : List UInt8) : Slice → Prop
  /-- A slice `start ≤ end ≤ length of the input`. -/
  | imm {v : Nat} : slStart v ≤ slEnd v → slEnd v ≤ buf.length → SliceValid buf (.imm v)
  /-- An interned string. -/
  | interned (bs : List UInt8) : SliceValid buf (.interned bs)

theorem slMake_valid {buf : List UInt8} {s e : Nat} (hse : s ≤ e) (he : e ≤ buf.length)
    (hbuf : buf.length ≤ slMax) : SliceValid buf (slMake s e) := by
  have := slMake_fields (s := s) (Nat.le_trans he hbuf)
  exact .imm (by rw [this.1, this.2]; exact hse) (by rw [this.2]; exact he)

theorem content_slMake {buf : List UInt8} {s e : Nat} (he : e ≤ slMax) :
    content buf (slMake s e) = (buf.drop s).take (e - s) := by
  have := slMake_fields (s := s) he
  simp only [content, slMake, slData, slLength, this.1, this.2]

theorem content_interned (buf bs : List UInt8) : content buf (.interned bs) = bs := by
  simp [content, slData, slLength]

/-- `rc_bytes_input` is valid and its content is the input. -/
theorem slInput_spec {buf : List UInt8} (hbuf : buf.length ≤ slMax) :
    SliceValid buf (slInput buf) ∧ content buf (slInput buf) = buf := by
  refine ⟨slMake_valid (Nat.zero_le _) (Nat.le_refl _) hbuf, ?_⟩
  rw [slInput, content_slMake hbuf, List.drop_zero, Nat.sub_zero, List.take_length]

/-- **`RC_NUL_slices_3`** is valid and empty. -/
theorem slNil_spec (buf : List UInt8) : SliceValid buf slNil ∧ content buf slNil = [] := by
  have hs : slStart 0 = 0 := Nat.zero_shiftRight _
  have he : slEnd 0 = 0 := Nat.zero_and _
  exact ⟨.imm (by rw [hs, he]; exact Nat.le_refl 0) (by rw [he]; exact Nat.zero_le _),
    by simp [content, slNil, slData, slLength, hs, he]⟩

/-- The length of a valid value is the length of its content. -/
theorem length_content {buf : List UInt8} {x : Slice} (hx : SliceValid buf x) :
    (content buf x).length = slLength x := by
  cases hx with
  | imm h₁ h₂ =>
    simp only [content, slData, slLength, List.length_take, List.length_drop]
    omega
  | interned bs => simp [content, slData, slLength]

/-- **`RC_KID_slices_3`**: a nonempty valid value is its first byte before the content of its
rest, which is valid. -/
theorem content_rest {buf : List UInt8} {x : Slice} (hx : SliceValid buf x) (hne : slLength x ≠ 0)
    (hbuf : buf.length ≤ slMax) :
    content buf x = slFirst buf x :: content buf (slRest x) ∧ SliceValid buf (slRest x) := by
  cases hx with
  | @imm v h₁ h₂ =>
    simp only [slLength] at hne
    have hlt : slStart v < buf.length := by omega
    refine ⟨?_, slMake_valid (by omega) h₂ hbuf⟩
    rw [slRest, content_slMake (Nat.le_trans h₂ hbuf)]
    simp only [content, slData, slLength, slFirst]
    rw [List.drop_eq_getElem_cons hlt]
    obtain ⟨k, hk⟩ : ∃ k, slEnd v - slStart v = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
    rw [hk, List.take_succ_cons, List.headD_cons, show slEnd v - (slStart v + 1) = k by omega]
  | interned bs =>
    simp only [slLength] at hne
    refine ⟨?_, .interned _⟩
    cases bs with
    | nil => exact absurd rfl hne
    | cons c bs => simp [content, slData, slLength, slFirst, slRest]

/-- **`RC_MK2_slices_3`**, both branches: the value `rc_sl_cons` builds is valid and holds `b`
before the content. -/
theorem content_slCons {buf : List UInt8} {x : Slice} (hx : SliceValid buf x) (b : Nat)
    (hbuf : buf.length ≤ slMax) :
    content buf (slCons buf b x) = UInt8.ofNat b :: content buf x ∧
      SliceValid buf (slCons buf b x) := by
  cases hx with
  | @imm v h₁ h₂ =>
    simp only [slCons]
    split
    · rename_i h
      obtain ⟨hpos, hget⟩ := h
      have hlt : slStart v - 1 < buf.length := by omega
      refine ⟨?_, slMake_valid (by omega) h₂ hbuf⟩
      rw [content_slMake (Nat.le_trans h₂ hbuf)]
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hget
      simp only [content, slData, slLength]
      rw [List.drop_eq_getElem_cons hlt, hget,
        show slEnd v - (slStart v - 1) = (slEnd v - slStart v) + 1 by omega, List.take_succ_cons,
        show slStart v - 1 + 1 = slStart v by omega]
    · exact ⟨content_interned _ _, .interned _⟩
  | interned bs =>
    refine ⟨?_, .interned _⟩
    simp [slCons, content_interned]

/-- The slice branch of `rc_sl_cons`: when the input's byte before a slice is `b`, the slice one
byte longer. -/
theorem slCons_imm_branch {buf : List UInt8} {v b : Nat} (hpos : 0 < slStart v)
    (hget : buf[slStart v - 1]? = some (UInt8.ofNat b)) :
    slCons buf b (.imm v) = slMake (slStart v - 1) (slEnd v) := by
  simp only [slCons]
  rw [if_pos ⟨hpos, hget⟩]

/-- The copying branch of `rc_sl_cons`: otherwise an interned string. -/
theorem slCons_copy_branch {buf : List UInt8} {v b : Nat}
    (h : ¬ (0 < slStart v ∧ buf[slStart v - 1]? = some (UInt8.ofNat b))) :
    slCons buf b (.imm v) = .interned (UInt8.ofNat b :: content buf (.imm v)) := by
  simp only [slCons]
  rw [if_neg h]

/-- **`rc_sl_take`**. -/
theorem content_slTake {buf : List UInt8} {x : Slice} (hx : SliceValid buf x) {n : Nat}
    (hn : n ≤ slLength x) (hbuf : buf.length ≤ slMax) :
    content buf (slTake x n) = (content buf x).take n ∧ SliceValid buf (slTake x n) := by
  cases hx with
  | @imm v h₁ h₂ =>
    simp only [slLength] at hn
    refine ⟨?_, slMake_valid (by omega) (by omega) hbuf⟩
    rw [slTake, content_slMake (by omega)]
    simp only [content, slData, slLength, List.take_take]
    rw [Nat.add_sub_cancel_left, Nat.min_eq_left hn]
  | interned bs =>
    refine ⟨?_, .interned _⟩
    simp only [slTake, content_interned]

/-- **`rc_sl_drop`**. -/
theorem content_slDrop {buf : List UInt8} {x : Slice} (hx : SliceValid buf x) {n : Nat}
    (hn : n ≤ slLength x) (hbuf : buf.length ≤ slMax) :
    content buf (slDrop x n) = (content buf x).drop n ∧ SliceValid buf (slDrop x n) := by
  cases hx with
  | @imm v h₁ h₂ =>
    simp only [slLength] at hn
    refine ⟨?_, slMake_valid (by omega) h₂ hbuf⟩
    rw [slDrop, content_slMake (Nat.le_trans h₂ hbuf)]
    simp only [content, slData, slLength, List.drop_take, List.drop_drop]
    rw [show slEnd v - (slStart v + n) = slEnd v - slStart v - n by omega]
  | interned bs =>
    refine ⟨?_, .interned _⟩
    simp only [slDrop, content_interned]

/-- **`rc_sl_equal`** is the equality of the contents. -/
theorem slEqual_iff {buf : List UInt8} {x y : Slice} (hx : SliceValid buf x)
    (hy : SliceValid buf y) : slEqual buf x y = true ↔ content buf x = content buf y := by
  have lx := length_content hx
  have ly := length_content hy
  unfold slEqual
  unfold content at lx ly ⊢
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨hl, h | h⟩ := h
    · have hy0 : slLength y = 0 := hl ▸ h
      rw [h, hy0, List.take_zero, List.take_zero]
    · rw [h, hl]
  · intro h
    have hl : slLength x = slLength y := by rw [← lx, ← ly, h]
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    exact ⟨hl, Or.inr (by rw [h, hl])⟩

/-- A byte of the input as the module's byte. -/
def Byte.ofU8 (c : UInt8) : Byte := Byte.ofWord c.toNat

theorem Byte.val_ofU8 (c : UInt8) : (Byte.ofU8 c).val = c.toNat :=
  Byte.val_ofWord _ (UInt8.toNat_lt c)

theorem Byte.ofU8_injective {c d : UInt8} (h : Byte.ofU8 c = Byte.ofU8 d) : c = d := by
  have := congrArg Byte.val h
  rw [Byte.val_ofU8, Byte.val_ofU8] at this
  exact UInt8.toNat_inj.mp this

/-- The byte string a value of the sort `Bytes` holds: its content as the module's bytes. -/
def readBytes (buf : List UInt8) (x : Slice) : Bytes := .ofList ((content buf x).map Byte.ofU8)

theorem map_val_readBytes (buf : List UInt8) (x : Slice) :
    (readBytes buf x).toList.map Byte.val = (content buf x).map UInt8.toNat := by
  simp only [readBytes, Bytes.toList_ofList, List.map_map]
  congr 1
  funext c
  exact Byte.val_ofU8 c

/-- **The views of `Bytes`** read a valid value as `BNil` when its length is `0`, otherwise as
`BCons` of the byte `RC_KID_slices_3(x, 0)` holds and the value `RC_KID_slices_3(x, 1)`. -/
theorem readBytes_view {buf : List UInt8} {x : Slice} (hx : SliceValid buf x)
    (hbuf : buf.length ≤ slMax) :
    (slLength x = 0 → readBytes buf x = .nil) ∧
      (slLength x ≠ 0 → readBytes buf x =
        .cons (Byte.ofWord (slFirst buf x).toNat) (readBytes buf (slRest x))) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := length_content hx
    rw [h] at this
    simp [readBytes, List.length_eq_zero_iff.mp this]
  · simp only [readBytes, (content_rest hx h hbuf).1, List.map_cons, Bytes.ofList_cons]
    rfl

/-- **The builder of `Bytes`** builds `BCons` of the byte a word below `256` holds. -/
theorem readBytes_slCons {buf : List UInt8} {x : Slice} (hx : SliceValid buf x) {b : Nat}
    (hb : b < 256) (hbuf : buf.length ≤ slMax) :
    readBytes buf (slCons buf b x) = .cons (Byte.ofWord b) (readBytes buf x) := by
  simp only [readBytes, (content_slCons hx b hbuf).1, List.map_cons, Bytes.ofList_cons]
  congr 1
  have h8 : b < 2 ^ 8 := by rw [show (2 : Nat) ^ 8 = 256 from rfl]; exact hb
  simp only [Byte.ofU8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt h8]

theorem readBytes_slNil (buf : List UInt8) : readBytes buf slNil = .nil := by
  simp [readBytes, (slNil_spec buf).2]

/-! ### The blocks and their bindings

The glue of each block (`emit_component_glue`; the functions `rc_bind_0` ... `rc_bind_14` of the
generated reader) composed with its component.  Each binding theorem says that on represented
values (the numerals of naturals below `bnLimit`, bytes below `256`, valid values of an input
shorter than `2 ^ 31`) the block answers what the rules answer, and characterises where it stops
the run. -/

/-- **`rc_bind_0`** (`MakeNatBit`, `nat-push-bit`): `rc_bn_shl1_or(a1, a0 == Bit1)`. -/
def cMakeNatBit (b : Bit) (n : Nat) : Option Nat := bnShl1Or n (if b = .bit1 then 1 else 0)

theorem cMakeNatBit_binding {b : Bit} {n m : Nat} (h : cMakeNatBit b n = some m) {r : BinNat} :
    MakeNatBit b (ofNat n) r ↔ r = ofNat m := by
  unfold cMakeNatBit at h
  rw [bnShl1Or_eq, bit_ite_eq_val, Nat.mod_eq_of_lt (by have := b.val_le_one; omega),
    magValue_eq_some_iff] at h
  rw [makeNatBit_iff, h.2]

theorem cMakeNatBit_eq_none_iff {b : Bit} {n : Nat} :
    cMakeNatBit b n = none ↔ bnLimit ≤ 2 * n + b.val := by
  unfold cMakeNatBit
  rw [bnShl1Or_eq, bit_ite_eq_val, Nat.mod_eq_of_lt (by have := b.val_le_one; omega),
    magValue_eq_none_iff]

/-- **`rc_bind_1`** (`NatPred`, `nat-pred`): `rc_bn_pred(a0)`; its `NULL` is the rules' lack of a
result. -/
theorem natPred_binding {n : Nat} {r : BinNat} :
    NatPred (ofNat n) r ↔ ∃ m, bnPred n = some m ∧ r = ofNat m := by
  rw [natPred_iff]
  unfold bnPred
  rw [bnSub_eq]
  by_cases h : n = 0
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    constructor
    · intro h'
      exact ⟨n - 1, rfl, h'.2⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨by omega, by rw [Option.some.inj hm]⟩

/-- **`rc_bind_2`** (`NatCompare`, `nat-order`): `rc_bn_cmp` with the glue
`c < 0 ? Less : c > 0 ? Greater : Equal`. -/
def cNatCompare (a b : Nat) : Cmp :=
  let c := bnCmp a b
  if c < 0 then .less else if c > 0 then .greater else .equal

theorem cNatCompare_eq (a b : Nat) : cNatCompare a b = Cmp.ofNats a b := by
  unfold cNatCompare bnCmp Cmp.ofNats
  by_cases h₁ : a < b
  · simp [h₁]
  · by_cases h₂ : b < a
    · have h₃ : a ≠ b := by omega
      simp [h₁, h₂, h₃]
    · have h₃ : a = b := by omega
      subst h₃
      simp

theorem natCompare_binding {a b : Nat} {r : Cmp} :
    NatCompare (ofNat a) (ofNat b) r ↔ r = cNatCompare a b := by
  rw [natCompare_iff, cNatCompare_eq]

/-- **`rc_bind_3`** (`NatInc`, `nat-succ`): `rc_bn_succ(a0)`. -/
theorem natInc_binding {a m : Nat} (h : bnSucc a = some m) {r : BinNat} :
    NatInc (ofNat a) r ↔ r = ofNat m := by
  unfold bnSucc at h
  rw [bnAdd_eq, magValue_eq_some_iff] at h
  rw [natInc_iff, h.2]

theorem bnSucc_eq_none_iff {a : Nat} : bnSucc a = none ↔ bnLimit ≤ a + 1 := by
  unfold bnSucc
  rw [bnAdd_eq, magValue_eq_none_iff]

/-- **`rc_bind_4`** (`NatAdd`, `nat-add`): `rc_bn_add(a0, a1)`. -/
theorem natAdd_binding {a b m : Nat} (h : bnAdd a b = some m) {r : BinNat} :
    NatAdd (ofNat a) (ofNat b) r ↔ r = ofNat m := by
  rw [bnAdd_eq, magValue_eq_some_iff] at h
  rw [natAdd_iff, h.2]

theorem bnAdd_eq_none_iff {a b : Nat} : bnAdd a b = none ↔ bnLimit ≤ a + b := by
  rw [bnAdd_eq, magValue_eq_none_iff]

/-- **`rc_bind_5`** (`NatXor`, `nat-xor`): `rc_bn_xor(a0, a1)`, which never stops the run on
represented values. -/
theorem natXor_binding {a b : Nat} (ha : a < bnLimit) (hb : b < bnLimit) {r : BinNat} :
    bnXor a b = some (a ^^^ b) ∧ (NatXor (ofNat a) (ofNat b) r ↔ r = ofNat (a ^^^ b)) :=
  ⟨bnXor_eq ha hb, natXor_iff⟩

/-- **`rc_bind_6`** (`NatMultiply`, `nat-multiply`): `rc_bn_mul(a0, a1)`. -/
theorem natMultiply_binding {a b m : Nat} (h : bnMul a b = some m) {r : BinNat} :
    NatMultiply (ofNat a) (ofNat b) r ↔ r = ofNat m := by
  rw [bnMul_eq] at h
  split at h
  · exact absurd h nofun
  · rw [natMultiply_iff, (Option.some.inj h).symm]

theorem bnMul_eq_none_iff {a b : Nat} : bnMul a b = none ↔ 16384 < magLimbs a + magLimbs b := by
  rw [bnMul_eq]
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    exact ⟨nofun, fun h' => absurd h' h⟩

/-- **`rc_bind_7`** (`NatTrim`, `nat-trim`): `rc_bn_trim(a1, a0)`, the arguments swapped. -/
def cNatTrim (w n : Nat) : Nat := bnTrim n w

theorem natTrim_binding {w n : Nat} (hn : n < bnLimit) {r : BinNat} :
    NatTrim (ofNat w) (ofNat n) r ↔ r = ofNat (cNatTrim w n) := by
  rw [natTrim_iff, cNatTrim, bnTrim_eq hn]

/-- **`rc_bind_8`** (`NatSubtract`, `nat-subtract`): `rc_bn_sub(a0, a1)`. -/
theorem natSubtract_binding {a b : Nat} {r : BinNat} :
    NatSubtract (ofNat a) (ofNat b) r ↔ r = ofNat (bnSub a b) := by
  rw [natSubtract_iff, bnSub_eq]

/-- **`rc_bind_9`** (`PackByte`, `word-pack`): `rc_bn_pack(a1, RC_IMM_VAL(a0), 8)`. -/
def cPackByte (byte high : Nat) : Option Nat := bnPack high byte 8

theorem packByte_binding {byte high m : Nat} (hb : byte < 256) (hh : high < bnLimit)
    (h : cPackByte byte high = some m) {r : BinNat} :
    PackByte (Byte.ofWord byte) (ofNat high) r ↔ r = ofNat m := by
  unfold cPackByte at h
  rw [bnPack_eq hh hb, magValue_eq_some_iff] at h
  rw [packByte_iff, Byte.val_ofWord byte hb, h.2]

theorem cPackByte_eq_none_iff {byte high : Nat} (hb : byte < 256) (hh : high < bnLimit) :
    cPackByte byte high = none ↔ bnLimit ≤ 256 * high + byte := by
  unfold cPackByte
  rw [bnPack_eq hh hb, magValue_eq_none_iff]

/-- **`rc_bind_10`** (`ByteLength`, `bytes-length`): `rc_bn_from_u64(rc_sl_length(a0))`. -/
theorem byteLength_binding {buf : List UInt8} {x : Slice} (hx : SliceValid buf x) {r : BinNat} :
    ByteLength (readBytes buf x) r ↔ r = ofNat (slLength x) := by
  rw [byteLength_iff, readBytes, Bytes.toList_ofList, List.length_map, length_content hx]

/-- The module's codec states as the blocks build them: the words they hold. -/
inductive CState
  /-- `RC_NUL_symbolic(NeedInput)`. -/
  | needInput
  /-- `RC_NUL_symbolic(BadInteger)`. -/
  | badInteger
  /-- `RC_MK2_symbolic(DecodedWord, n, rest)`. -/
  | decodedWord (n : Nat) (rest : Slice)
  /-- `RC_MK2_symbolic(Taken, pre, rest)`. -/
  | taken (pre rest : Slice)
  deriving DecidableEq, Repr

/-- The codec state a C state stands for. -/
def readState (buf : List UInt8) : CState → CodecState
  | .needInput => .needInput
  | .badInteger => .badInteger
  | .decodedWord n rest => .decodedWord (ofNat n) (readBytes buf rest)
  | .taken pre rest => .taken (readBytes buf pre) (readBytes buf rest)

/-- **`rc_bind_11`** (`TakeBytes`, `bytes-take`): `NeedInput` when the count does not fit 64 bits
or exceeds the length, otherwise `Taken` of `rc_sl_take` and `rc_sl_drop`. -/
def cTakeBytes (n : Nat) (x : Slice) : CState :=
  if ¬ n < 2 ^ 64 ∨ slLength x < n then .needInput else .taken (slTake x n) (slDrop x n)

/-- The binding of `TakeBytes`, on values of fewer than `2 ^ 64` bytes (every value the C makes:
a slice has fewer than `2 ^ 31`, and `rc_intern_bytes` stops the run beyond `2 ^ 32 - 1`). -/
theorem takeBytes_binding {buf : List UInt8} {x : Slice} (hx : SliceValid buf x)
    (hbuf : buf.length ≤ slMax) (hlen : slLength x < 2 ^ 64) {n : Nat} {r : CodecState} :
    TakeBytes (ofNat n) (readBytes buf x) r ↔ r = readState buf (cTakeBytes n x) := by
  rw [takeBytes_iff]
  have hl : (readBytes buf x).toList.length = slLength x := by
    rw [readBytes, Bytes.toList_ofList, List.length_map, length_content hx]
  unfold takeSpec cTakeBytes
  rw [hl]
  by_cases hn : n ≤ slLength x
  · rw [if_pos hn, if_neg (by omega)]
    simp only [readState, readBytes, (content_slTake hx hn hbuf).1, (content_slDrop hx hn hbuf).1,
      List.map_take, List.map_drop, Bytes.toList_ofList]
  · rw [if_neg hn, if_pos (by omega)]
    rfl

/-- **`rc_bind_12`** (`BytesEqual`, `bytes-equal`): `rc_sl_equal(a0, a1) ? Bit1 : Bit0`. -/
def cBytesEqual (buf : List UInt8) (x y : Slice) : Bit :=
  if slEqual buf x y then .bit1 else .bit0

theorem bytesEqual_binding {buf : List UInt8} {x y : Slice} (hx : SliceValid buf x)
    (hy : SliceValid buf y) {r : Bit} :
    BytesEqual (readBytes buf x) (readBytes buf y) r ↔ r = cBytesEqual buf x y := by
  rw [bytesEqual_iff, cBytesEqual]
  have e : readBytes buf x = readBytes buf y ↔ slEqual buf x y = true := by
    rw [slEqual_iff hx hy]
    constructor
    · intro h
      have := congrArg Bytes.toList h
      simp only [readBytes, Bytes.toList_ofList] at this
      exact (List.map_inj_right (fun _ _ h => Byte.ofU8_injective h)).mp this
    · intro h
      simp only [readBytes, h]
  by_cases h : slEqual buf x y = true
  · rw [if_pos (e.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (e.mp h')), if_neg h]

/-- **The loop of `rc_bind_13`** (`ReadULEB62`, `uleb` with the parameters `9` and `6`), on the
bytes it reads: at index `i`, with the value `v` gathered so far.  The ninth byte (`i = 8`) is
refused when `b >> 6` is not zero; `v |= (b & 0x7f) << (7 i)` on 64-bit words; a byte without
`0x80` ends the number, refused when it is `0` and not the first. -/
def ulebLoop : Nat → Nat → List Nat → LebOut
  | _, _, [] => .needInput
  | i, v, b :: rest =>
    if i = 8 ∧ b >>> 6 ≠ 0 then .badInteger
    else if b &&& 0x80 = 0 then
      (if 0 < i ∧ b = 0 then .badInteger
       else .decoded (v ||| (((b &&& 0x7f) <<< (7 * i)) % 2 ^ 64)) (i + 1))
    else ulebLoop (i + 1) (v ||| (((b &&& 0x7f) <<< (7 * i)) % 2 ^ 64)) rest

/-- `rc_bind_13`: the loop over the data of the argument, the rest `rc_sl_drop(a0, i + 1)`. -/
def cUleb (buf : List UInt8) (x : Slice) : CState :=
  match ulebLoop 0 0 ((content buf x).map UInt8.toNat) with
  | .needInput => .needInput
  | .badInteger => .badInteger
  | .decoded v k => .decodedWord v (slDrop x k)

/-- What the rules' reading of the bytes from index `i` on becomes in the loop, which has
gathered `v` from the bytes before. -/
def lebAdjust (i v : Nat) : LebOut → LebOut
  | .needInput => .needInput
  | .badInteger => .badInteger
  | .decoded w k => if 0 < i ∧ w = 0 then .badInteger else .decoded (v + w * 2 ^ (7 * i)) (i + k)

theorem lebAdjust_zero (S : LebOut) : lebAdjust 0 0 S = S := by
  cases S with
  | needInput => rfl
  | badInteger => rfl
  | decoded w k => simp [lebAdjust]

theorem byte_and80 : ∀ c, c < 256 → (c &&& 0x80 = 0 ↔ c < 128) := by decide +kernel

theorem byte_shr6 : ∀ c, c < 256 → (c >>> 6 ≠ 0 ↔ 64 ≤ c) := by decide +kernel

theorem uleb_acc {i v x : Nat} (hi : i ≤ 8) (hv : v < 2 ^ (7 * i)) (hx : x < 128)
    (h8 : i = 8 → x < 64) : (v ||| ((x <<< (7 * i)) % 2 ^ 64)) = v + x * 2 ^ (7 * i) := by
  have hlt : x <<< (7 * i) < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceMul, Nat.reducePow] at h8 ⊢ <;> omega
  rw [Nat.mod_eq_of_lt hlt, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hv, Nat.shiftLeft_eq,
    Nat.add_comm]

theorem uleb_acc_lt {i v x : Nat} (hi : i < 8) (hv : v < 2 ^ (7 * i)) (hx : x < 128) :
    v + x * 2 ^ (7 * i) < 2 ^ (7 * (i + 1)) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at hv ⊢ <;> omega

theorem uleb_join_arith {i v x w : Nat} (hi : i < 8) :
    v + x * 2 ^ (7 * i) + w * 2 ^ (7 * (i + 1)) = v + (x + 128 * w) * 2 ^ (7 * i) := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] <;> omega

/-- **The loop and the rules.**  From index `i ≤ 8`, having gathered `v < 2 ^ (7 i)`, the loop
gives what the rules give with `8 - i` more `LebMore`s, adjusted by `lebAdjust`. -/
theorem ulebLoop_eq : ∀ (l : List Nat) (i v : Nat), i ≤ 8 → v < 2 ^ (7 * i) →
    (∀ c ∈ l, c < 256) → ulebLoop i v l = lebAdjust i v (lebSpec (8 - i) l)
  | [], i, v, _, _, _ => by
    cases h : 8 - i <;> simp [ulebLoop, lebSpec, lebAdjust]
  | c :: rest, i, v, hi, hv, hl => by
    have hc : c < 256 := hl c (List.mem_cons_self ..)
    have hrest : ∀ d ∈ rest, d < 256 := fun d h => hl d (List.mem_cons_of_mem _ h)
    have h7f : c &&& 0x7f = c % 128 := Nat.and_two_pow_sub_one_eq_mod c 7
    by_cases h8 : i = 8
    · subst h8
      have hspec : lebSpec (8 - 8) (c :: rest) = if c < 64 then .decoded c 1 else .badInteger := rfl
      rw [hspec]
      by_cases h64 : c < 64
      · have hs : ¬ (c >>> 6 ≠ 0) := fun h => absurd ((byte_shr6 c hc).mp h) (by omega)
        have ha : c &&& 0x80 = 0 := (byte_and80 c hc).mpr (by omega)
        rw [ulebLoop.eq_2, if_neg (fun h => hs h.2), if_pos ha, if_pos h64, h7f,
          Nat.mod_eq_of_lt (by omega : c < 128), uleb_acc (by omega) hv (by omega) (fun _ => h64)]
        simp only [lebAdjust]
      · have hs : c >>> 6 ≠ 0 := (byte_shr6 c hc).mpr (by omega)
        rw [ulebLoop.eq_2, if_pos ⟨rfl, hs⟩, if_neg h64]
        rfl
    · have hi8 : i < 8 := by omega
      have hspec : lebSpec (8 - i) (c :: rest) =
          if c < 128 then .decoded c 1 else lebJoinSpec (c - 128) (lebSpec (7 - i) rest) := by
        rw [show 8 - i = (7 - i) + 1 by omega]
        rfl
      rw [hspec, ulebLoop.eq_2, if_neg (fun h => h8 h.1)]
      by_cases h128 : c < 128
      · rw [if_pos ((byte_and80 c hc).mpr h128), if_pos h128, h7f, Nat.mod_eq_of_lt h128,
          uleb_acc hi hv h128 (fun h => absurd h h8)]
        simp only [lebAdjust]
      · rw [if_neg (fun h => h128 ((byte_and80 c hc).mp h)), if_neg h128, h7f,
          uleb_acc hi hv (Nat.mod_lt _ (by decide)) (fun h => absurd h h8),
          show c % 128 = c - 128 by omega,
          ulebLoop_eq rest (i + 1) _ (by omega) (uleb_acc_lt hi8 hv (by omega)) hrest,
          show 8 - (i + 1) = 7 - i by omega]
        cases lebSpec (7 - i) rest with
        | needInput => rfl
        | badInteger => rfl
        | decoded w k =>
          simp only [lebAdjust, lebJoinSpec]
          by_cases hw : w = 0
          · subst hw
            simp
          · rw [if_neg (fun h => hw h.2), if_neg hw]
            simp only
            rw [if_neg (by omega), uleb_join_arith hi8, show i + 1 + k = i + (k + 1) by omega]

theorem lebJoinSpec_used {x : Nat} {S : LebOut} {v j : Nat} (h : lebJoinSpec x S = .decoded v j) :
    ∃ w k, S = .decoded w k ∧ j = k + 1 := by
  cases S with
  | needInput => exact absurd h nofun
  | badInteger => exact absurd h nofun
  | decoded w k =>
    simp only [lebJoinSpec] at h
    split at h
    · exact absurd h nofun
    · injection h with _ hj
      exact ⟨w, k, rfl, hj.symm⟩

/-- A reading takes at most the bytes there are. -/
theorem lebSpec_used : ∀ {k : Nat} {l : List Nat} {v j : Nat}, lebSpec k l = .decoded v j →
    j ≤ l.length
  | _, [], _, _, h => by cases ‹Nat› <;> exact absurd h (by simp [lebSpec])
  | 0, c :: rest, v, j, h => by
    simp only [lebSpec] at h
    split at h
    · injection h with _ hj
      simp [← hj]
    · exact absurd h nofun
  | k + 1, c :: rest, v, j, h => by
    simp only [lebSpec] at h
    split at h
    · injection h with _ hj
      simp [← hj]
    · obtain ⟨w, i, hS, rfl⟩ := lebJoinSpec_used h
      have := lebSpec_used hS
      simp only [List.length_cons]
      omega

/-- **`rc_bind_13`** (`ReadULEB62`): the loop of the glue computes the rules `StartLEB` ...
`LebJoinBad`: `NeedInput` when the input ends first, `BadInteger` for a ninth byte above six bits
(too long or too large) and for a last byte `0` after the first (not minimal), otherwise the number
and the rest after it. -/
theorem readULEB62_binding {buf : List UInt8} {x : Slice} (hx : SliceValid buf x)
    (hbuf : buf.length ≤ slMax) {r : CodecState} :
    ReadULEB62 (readBytes buf x) r ↔ r = readState buf (cUleb buf x) := by
  rw [readULEB62_iff, map_val_readBytes]
  have hl : ∀ c ∈ (content buf x).map UInt8.toNat, c < 256 := by
    intro c hc
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
    exact UInt8.toNat_lt d
  have e := ulebLoop_eq _ 0 0 (by omega) (by decide) hl
  rw [lebAdjust_zero] at e
  unfold cUleb
  rw [e]
  cases hS : lebSpec 8 ((content buf x).map UInt8.toNat) with
  | needInput => rfl
  | badInteger => rfl
  | decoded v k =>
    have hk : k ≤ slLength x := by
      have := lebSpec_used hS
      rw [List.length_map, length_content hx] at this
      exact this
    simp only [LebOut.toState, readState, readBytes, (content_slDrop hx hk hbuf).1,
      Bytes.toList_ofList, List.map_drop]

/-- One turn of the `fnv-hash` loop (`0xcbf29ce484222325`, `0x100000001b3`, `64`):
`((h ^ b) * PRIME) & MASK` on 64-bit words, the product wrapping modulo `2 ^ 64`. -/
def fnvStepC (h b : Nat) : Nat := (((h ^^^ b) * 1099511628211) % 2 ^ 64) &&& (2 ^ 64 - 1)

/-- **`rc_bind_14`** (`FNV`): the loop over the data of the argument, from the basis. -/
def cFnv (buf : List UInt8) (x : Slice) : Nat :=
  ((content buf x).map UInt8.toNat).foldl fnvStepC 14695981039346656037

theorem fnvStepC_eq (h b : Nat) : fnvStepC h b = fnvStep h b := by
  unfold fnvStepC fnvStep
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod, Nat.mul_comm]

/-- **`rc_bind_14`**: the loop computes the rules `FnvInit`, `FnvDone`, `FnvNext`, `FnvByte`; the
empty string gives the basis. -/
theorem fnv_binding {buf : List UInt8} {x : Slice} {r : BinNat} :
    FNV (readBytes buf x) r ↔ r = ofNat (cFnv buf x) := by
  rw [fnv_iff, map_val_readBytes, cFnv, fnvSpec]
  have : fnvStepC = fnvStep := funext fun h => funext fun b => fnvStepC_eq h b
  rw [this]

/-! ### The memo of `LookupSchema` -/

/-- What the memo of `LookupSchema` keeps for its key (the opcode and the schema list): the
rules' one result. -/
def lookupMemoFn (k : Byte × Schemas) : Option FoundLayout := some (lookupSchema k.1 k.2)

/-- **The memo of `LookupSchema` is sound**: `LookupSchema` is a function of its arguments
(`lookupSchema_iff_fn`), so by the memo theorem of the components (`memo2_sound`) every run of
calls and clearings, from empty generations and with any capacity, answers each call with the
rules' one result on its key. -/
theorem lookupSchema_memo_sound (cap : Nat)
    (ops : List (RuleModuleComponents.MemoOp (Byte × Schemas))) :
    (RuleModuleComponents.memoRun2 cap lookupMemoFn ⟨[], []⟩ ops).1 =
        (ops.filterMap RuleModuleComponents.MemoOp.key?).map lookupMemoFn ∧
      ∀ (k : Byte × Schemas) (r : FoundLayout), LookupSchema k.1 k.2 r ↔ lookupMemoFn k = some r := by
  refine ⟨(RuleModuleComponents.memo2_sound cap lookupMemoFn
    (RuleModuleComponents.memo2Sound_empty lookupMemoFn) ops).1, fun k r => ?_⟩
  rw [lookupSchema_iff_fn, lookupMemoFn, Option.some.injEq]
  exact eq_comm


/-! ### Products whose factors have too many limbs -/

theorem magLimbs_two_pow {k : Nat} (hk : 62 ≤ k) : magLimbs (2 ^ k) = ((k + 1 + 7) / 8 + 7) / 8 := by
  have h : bnSmall ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  unfold magLimbs bitLen
  rw [if_neg (Nat.not_lt.mpr h), if_neg (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)),
    Nat.log2_two_pow]

/-- `rc_bn_mul` stops the run on `2 ^ j * 2 ^ k` when the factors have more than `RC_BN_LIMBS`
limbs together, though the product may be below `bnLimit`. -/
theorem bnMul_two_pow_none {j k : Nat} (hj : 62 ≤ j) (hk : 62 ≤ k)
    (hl : 16384 < ((j + 1 + 7) / 8 + 7) / 8 + ((k + 1 + 7) / 8 + 7) / 8) (hjk : j + k < bnBits) :
    bnMul (2 ^ j) (2 ^ k) = none ∧ 2 ^ j * 2 ^ k < bnLimit := by
  refine ⟨?_, ?_⟩
  · rw [bnMul_eq_none_iff, magLimbs_two_pow hj, magLimbs_two_pow hk]
    exact hl
  · rw [← Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) hjk

set_option exponentiation.threshold 1048576 in
/-- **The stated contract on large products**: `rc_bn_mul` stops the run on `2 ^ 524288 * 2 ^ 524224`,
whose `2 ^ 20 - 63` bits are below `bnLimit`, because its factors have `8193 + 8192` limbs, more
than `RC_BN_LIMBS`. -/
theorem bnMul_refuses_below_bnLimit :
    bnMul (2 ^ (64 * 8192)) (2 ^ (64 * 8191)) = none ∧
      2 ^ (64 * 8192) * 2 ^ (64 * 8191) < bnLimit :=
  bnMul_two_pow_none (j := 64 * 8192) (k := 64 * 8191) (by decide) (by decide) (by decide)
    (by rw [bnBits_eq]; decide)

/-! ## Examples -/

section Examples

/-! ### Derivations of the rules, and inputs on which no rule applies -/

/-- `CanonZero`; `NatBit Bit0 NatZero` is never a result of `MakeNatBit`. -/
example : MakeNatBit .bit0 .zero .zero := .canonZero
example : ¬ MakeNatBit .bit0 .zero (.bit .bit0 .zero) := nofun

/-- `NatPred` of `6` is `5`, by `PredEven` over `PredOdd` over `CanonMore`. -/
example : NatPred (.bit .bit0 (.bit .bit1 (.bit .bit1 .zero))) (.bit .bit1 (.bit .bit0 (.bit .bit1 .zero))) :=
  .predEven (.predOdd .canonMore)
example : NatPred (ofNat 6) (ofNat 5) := natPred_iff.mpr ⟨by decide, rfl⟩

/-- No rule of `NatPred` applies to `NatZero`, nor to the non-canonical `NatBit Bit0 NatZero`. -/
example (r : BinNat) : ¬ NatPred .zero r := nofun
example (r : BinNat) : ¬ NatPred (.bit .bit0 .zero) r := by
  intro h
  cases h with
  | predEven h => cases h

/-- `NatSubtract` has no result on the non-canonical `NatBit Bit0 NatZero`: its `NatPred` fails. -/
example : ¬ ∃ r, NatSubtract (.bit .bit1 .zero) (.bit .bit0 .zero) r := by
  rintro ⟨r, h⟩
  cases h with
  | subtractMore _ h₂ _ =>
    cases h₂ with
    | predEven h => cases h

/-- `NatSubtract` truncates: `3 - 5` is `0`. -/
example : NatSubtract (ofNat 3) (ofNat 5) .zero := natSubtract_iff.mpr rfl

/-- `TakeBytes` has no result on a non-canonical count over a nonempty string. -/
example (b : Byte) : ¬ ∃ r, TakeBytes (.bit .bit0 .zero) (.cons b .nil) r := by
  rintro ⟨r, h⟩
  cases h with
  | takeMore h₁ _ _ =>
    cases h₁ with
    | predEven h => cases h

/-- `TakePush` and `LebJoin` have no rule on `LimitExceeded`. -/
example (b : Byte) (r : CodecState) : ¬ TakePush b .limitExceeded r := nofun
example (r : CodecState) : ¬ LebJoin .bit0 .bit0 .bit0 .bit0 .bit0 .bit0 .bit0 .limitExceeded r :=
  lebJoin_none_limitExceeded r

/-- `LebNonminimal`: a continued byte before a rest of value `0` is not minimal. -/
example (rest : Bytes) :
    LebJoin .bit0 .bit0 .bit0 .bit0 .bit0 .bit0 .bit1 (.decodedWord .zero rest) .badInteger :=
  .lebNonminimal

/-- `BytesEqual` compares bytes through `PackByte` and `NatCompare`. -/
example : BytesEqual (.cons (Byte.ofWord 1) .nil) (.cons (Byte.ofWord 1) .nil) .bit1 :=
  bytesEqual_iff.mpr (by rw [if_pos rfl])
example : ¬ BytesEqual (.cons (Byte.ofWord 1) .nil) (.cons (Byte.ofWord 2) .nil) .bit1 := by
  rw [bytesEqual_iff, if_neg (by decide)]
  exact nofun

/-- The literals of the FNV rules are the 64-bit FNV-1a constants, and canonical. -/
example : fnvBasis.Canonical ∧ fnvPrime.Canonical ∧ fnvWidth.Canonical := by decide

/-! ### The representations -/

/-- Words of `Byte`: `0xA5` views as `Byte8 1 0 1 0 0 1 0 1`, and building it back gives
`0xA5`. -/
example : Byte.ofWord 0xA5 = .byte8 .bit1 .bit0 .bit1 .bit0 .bit0 .bit1 .bit0 .bit1 := by decide
example : wordMk [.bit1, .bit0, .bit1, .bit0, .bit0, .bit1, .bit0, .bit1] = 0xA5 := by decide

/-- Binary naturals: `6` views as `NatBit Bit0 3`; the builder refuses `NatBit Bit0 NatZero` and
builds `NatBit Bit1 NatZero` as `1`. -/
example : binTag 6 = .natBit ∧ binKid0 6 = .bit0 ∧ binKid1 6 = 3 := by decide
example : binMk2 .bit0 0 = none := by decide
example : binMk2 .bit1 0 = some 1 := by decide

/-- Slices: on the input `[7, 1, 2]`, the slice of `[1, 2]` with `7` consed is the whole input (the
slice branch); with `9` consed it is the interned `[9, 1, 2]` (the copying branch). -/
example : slCons [7, 1, 2] 7 (slMake 1 3) = slMake 0 3 := by decide +kernel
example : content [7, 1, 2] (slMake 0 3) = [7, 1, 2] := by decide +kernel
example : slCons [7, 1, 2] 9 (slMake 1 3) = .interned [9, 1, 2] := by decide +kernel
/-- The rest of a slice is a slice, the rest of an interned string an interned string. -/
example : slRest (slMake 1 3) = slMake 2 3 ∧ slRest (.interned [9, 1, 2]) = .interned [1, 2] := by
  decide +kernel
/-- A slice and an interned string of equal content are equal as module data. -/
example : cBytesEqual [7, 1, 2] (slMake 1 3) (.interned [1, 2]) = .bit1 := by decide +kernel

/-! ### Lines of the probe file (`probe.txt`), checked on the models

The probe printed each judgment, its arguments and the compiled block's result; the probe built
its byte strings with the module's constructors, so they are interned strings.  Each line below is
checked on the model of its block (by `decide`), and, through the block's binding theorem, on the
rules. -/

/-- Line 2, `NatPred 0 => none`; line 43, `NatPred 1 => 0`. -/
example : bnPred 0 = none := rfl
example (r : BinNat) : ¬ NatPred (ofNat 0) r := fun h => by
  obtain ⟨m, hm, _⟩ := natPred_binding.mp h
  exact absurd hm nofun
example : bnPred 1 = some 0 := rfl
example : NatPred (ofNat 1) (ofNat 0) := natPred_binding.mpr ⟨0, rfl, rfl⟩

/-- Line 3, `MakeNatBit (Bit0) 0 => 0`; line 45, `MakeNatBit (Bit1) 1 => 3`. -/
example : cMakeNatBit .bit0 0 = some 0 := by decide
example : cMakeNatBit .bit1 1 = some 3 := by decide
example : MakeNatBit .bit1 (ofNat 1) (ofNat 3) := (cMakeNatBit_binding (by decide)).mpr rfl

/-- Lines 53 to 55: `NatAdd 1 3 => 4`, `NatXor 1 3 => 2`, `NatSubtract 1 3 => 0`. -/
example : bnAdd 1 3 = some 4 := by decide
example : NatAdd (ofNat 1) (ofNat 3) (ofNat 4) := (natAdd_binding (by decide)).mpr rfl
example : bnXor 1 3 = some 2 := by decide
example : NatXor (ofNat 1) (ofNat 3) (ofNat 2) := natXor_iff.mpr (by decide)
example : bnSub 1 3 = 0 := by decide
example : NatSubtract (ofNat 1) (ofNat 3) (ofNat 0) := natSubtract_binding.mpr (by decide)

/-- Line 77, `NatAdd 1 18446744073709551615 => big`: the sum `2 ^ 64` is an interned magnitude. -/
example : bnAdd 1 18446744073709551615 = some 18446744073709551616 := by
  rw [bnAdd_eq]
  exact magValue_of_lt (Nat.lt_of_lt_of_le (by decide : 1 + 18446744073709551615 < 2 ^ 65)
    (Nat.pow_le_pow_right (by decide) (by rw [bnBits_eq]; decide)))

/-- Line 82, `PackByte 165 1 => 421`. -/
example : cPackByte 165 1 = some 421 := by decide
example : PackByte (Byte.ofWord 165) (ofNat 1) (ofNat 421) :=
  (packByte_binding (by decide) (Nat.lt_of_lt_of_le (by decide) two_pow_64_le_bnLimit)
    (by decide)).mpr rfl

/-- Line 191, `NatTrim 5 1000 => 8`. -/
example : cNatTrim 5 1000 = 8 := by decide
example : NatTrim (ofNat 5) (ofNat 1000) (ofNat 8) :=
  (natTrim_binding (Nat.lt_of_lt_of_le (by decide) two_pow_64_le_bnLimit)).mpr (by decide)

/-- Line 355, `NatCompare 1000 3 => (Greater)`. -/
example : cNatCompare 1000 3 = .greater := by decide
example : NatCompare (ofNat 1000) (ofNat 3) .greater := natCompare_binding.mpr (by decide)

/-- Line 374, `NatMultiply 1000 4611686018427387903 => big`. -/
example : bnMul 1000 4611686018427387903 = some 4611686018427387903000 := by
  rw [bnMul_eq]
  decide
example : 2 ^ 64 ≤ 4611686018427387903000 := by decide

/-- Line 449, `NatInc 4611686018427387903 => 4611686018427387904`: the successor of the largest
immediate is the first interned magnitude. -/
example : bnSucc 4611686018427387903 = some 4611686018427387904 := by
  rw [bnSucc, bnAdd_eq]
  exact magValue_of_lt bnSmall_lt_bnLimit

/-- Line 468, `NatSubtract 4611686018427387903 1000 => 4611686018427386903`. -/
example : bnSub 4611686018427387903 1000 = 4611686018427386903 := by decide

/-- Lines 701 to 703: `ByteLength [] => 0`, `FNV [] => 14695981039346656037` (the basis),
`TakeBytes 0 [] => (Taken [] [])`. -/
example : slLength (.interned []) = 0 := rfl
example : cFnv [] (.interned []) = 14695981039346656037 := by decide
example : FNV (readBytes [] (.interned [])) (ofNat 14695981039346656037) := fnv_binding.mpr rfl
example : cTakeBytes 0 (.interned []) = .taken (.interned []) (.interned []) := by decide

/-- Line 691, `FNV [72,79,76,82] => 9063298369963621018`. -/
example : cFnv [] (.interned [72, 79, 76, 82]) = 9063298369963621018 := by decide +kernel
example : FNV (readBytes [] (.interned [72, 79, 76, 82])) (ofNat 9063298369963621018) :=
  fnv_binding.mpr (congrArg ofNat (by decide +kernel))

/-- Line 650, `TakeBytes 2 [0,5] => (Taken [0,5] [])`; line 651, a count beyond the length needs
input. -/
example : cTakeBytes 2 (.interned [0, 5]) = .taken (.interned [0, 5]) (.interned []) := by decide
example : cTakeBytes 3 (.interned [0, 5]) = .needInput := by decide

/-- Line 699, `BytesEqual [72,79,76,82] [72,79,76,82] => (Bit1)`; line 567,
`BytesEqual [1] [72,79,76,82] => (Bit0)`. -/
example : cBytesEqual [] (.interned [72, 79, 76, 82]) (.interned [72, 79, 76, 82]) = .bit1 := by
  decide
example : cBytesEqual [] (.interned [1]) (.interned [72, 79, 76, 82]) = .bit0 := by decide

/-- The `ReadULEB62` lines 656, 579, 645, 601 and 700: every branch of the loop. -/
example : cUleb [] (.interned [229, 142, 38, 7]) = .decodedWord 624485 (.interned [7]) := by
  decide +kernel
example : cUleb [] (.interned [128, 1]) = .decodedWord 128 (.interned []) := by decide +kernel
example : cUleb [] (.interned [0, 5]) = .decodedWord 0 (.interned [5]) := by decide +kernel
example : cUleb [] (.interned [128]) = .needInput := by decide +kernel
example : cUleb [] (.interned []) = .needInput := by decide +kernel
/-- Lines 590 and 667, not minimal: a last byte `0` after the first. -/
example : cUleb [] (.interned [128, 0]) = .badInteger := by decide +kernel
example : cUleb [] (.interned [129, 128, 0]) = .badInteger := by decide +kernel
/-- Lines 612, 678, 623 and 634, the ninth byte: below `64` it ends the number (the largest,
`2 ^ 62 - 1`, and `2 ^ 56`); `64` is too large; `128` makes the number too long. -/
example : cUleb [] (.interned [255, 255, 255, 255, 255, 255, 255, 255, 63]) =
    .decodedWord 4611686018427387903 (.interned []) := by decide +kernel
example : cUleb [] (.interned [128, 128, 128, 128, 128, 128, 128, 128, 1]) =
    .decodedWord 72057594037927936 (.interned []) := by decide +kernel
example : cUleb [] (.interned [255, 255, 255, 255, 255, 255, 255, 255, 64]) = .badInteger := by
  decide +kernel
example : cUleb [] (.interned [255, 255, 255, 255, 255, 255, 255, 255, 128]) = .badInteger := by
  decide +kernel
/-- Line 656 through the binding: the rules derive what the block answers. -/
example : ReadULEB62 (readBytes [] (.interned [229, 142, 38, 7]))
    (.decodedWord (ofNat 624485) (readBytes [] (.interned [7]))) :=
  (readULEB62_binding (.interned _) (by decide)).mpr
    (by rw [show cUleb [] (.interned [229, 142, 38, 7]) = .decodedWord 624485 (.interned [7]) by
      decide +kernel]; rfl)

/-! ### Lines 711 to 750: the blocks on slices of a registered input

The probe registered the twelve bytes below as the run's input (`rc_bytes_input`) and read the
argument at the offsets `0`, `3`, `6`, `9` and `12` through the view `RC_KID_slices_3(x, 1)`,
that is `rc_sl_rest` applied `off` times: the slice branch of the representation.  The second
argument of each `BytesEqual` line is built with the module's constructors, an interned string. -/

/-- The probe's input: `e5 8e 26 07 80 00 7f 'H' 'O' 'L' 'R' 01`. -/
def probeInput : List UInt8 := [229, 142, 38, 7, 128, 0, 127, 72, 79, 76, 82, 1]

/-- `rc_sl_rest` applied `n` times. -/
def restN : Nat → Slice → Slice
  | 0, x => x
  | n + 1, x => restN n (slRest x)

/-- The argument at offset `off`. -/
def probeAt (off : Nat) : Slice := restN off (slInput probeInput)

/-- The views move a slice: the argument at offset `off` is the slice from `off` to `12`. -/
example : probeAt 0 = slMake 0 12 ∧ probeAt 3 = slMake 3 12 ∧ probeAt 6 = slMake 6 12 ∧
    probeAt 9 = slMake 9 12 ∧ probeAt 12 = slMake 12 12 := by decide +kernel

theorem probeAt_valid (off : Nat) (h : off ≤ 12) : SliceValid probeInput (slMake off 12) :=
  slMake_valid h (by decide) (by decide)

/-- Lines 711, 719, 727, 735, 743 (`ReadULEB62`): the rest is a slice of the input. -/
example : cUleb probeInput (probeAt 0) = .decodedWord 624485 (slMake 3 12) ∧
    content probeInput (slMake 3 12) = [7, 128, 0, 127, 72, 79, 76, 82, 1] := by decide +kernel
example : cUleb probeInput (probeAt 3) = .decodedWord 7 (slMake 4 12) ∧
    content probeInput (slMake 4 12) = [128, 0, 127, 72, 79, 76, 82, 1] := by decide +kernel
example : cUleb probeInput (probeAt 6) = .decodedWord 127 (slMake 7 12) ∧
    content probeInput (slMake 7 12) = [72, 79, 76, 82, 1] := by decide +kernel
example : cUleb probeInput (probeAt 9) = .decodedWord 76 (slMake 10 12) ∧
    content probeInput (slMake 10 12) = [82, 1] := by decide +kernel
example : cUleb probeInput (probeAt 12) = .needInput := by decide +kernel
/-- Line 711 on the rules, through the binding. -/
example : ReadULEB62 (readBytes probeInput (slMake 0 12))
    (.decodedWord (ofNat 624485) (readBytes probeInput (slMake 3 12))) :=
  (readULEB62_binding (probeAt_valid 0 (by decide)) (by decide)).mpr
    (by rw [show cUleb probeInput (slMake 0 12) = .decodedWord 624485 (slMake 3 12) by
      decide +kernel]; rfl)

/-- Lines 712, 720, 728, 736, 744 (`ByteLength`). -/
example : slLength (probeAt 0) = 12 ∧ slLength (probeAt 3) = 9 ∧ slLength (probeAt 6) = 6 ∧
    slLength (probeAt 9) = 3 ∧ slLength (probeAt 12) = 0 := by decide +kernel
example : ByteLength (readBytes probeInput (slMake 3 12)) (ofNat 9) :=
  (byteLength_binding (probeAt_valid 3 (by decide))).mpr (by decide +kernel)

/-- Lines 713, 721, 729, 737, 745 (`FNV`). -/
example : cFnv probeInput (probeAt 0) = 14631914635618494924 ∧
    cFnv probeInput (probeAt 3) = 3732975564598564459 ∧
    cFnv probeInput (probeAt 6) = 2036705672826075880 ∧
    cFnv probeInput (probeAt 9) = 2713367208924181870 ∧
    cFnv probeInput (probeAt 12) = 14695981039346656037 := by decide +kernel
example : FNV (readBytes probeInput (slMake 0 12)) (ofNat 14631914635618494924) :=
  fnv_binding.mpr (congrArg ofNat (by decide +kernel))

/-- Lines 715, 716, 724, 732, 739, 740, 746, 747 (`TakeBytes`): slices of slices, or `NeedInput`
past the end. -/
example : cTakeBytes 2 (probeAt 0) = .taken (slMake 0 2) (slMake 2 12) ∧
    content probeInput (slMake 0 2) = [229, 142] := by decide +kernel
example : cTakeBytes 4 (probeAt 0) = .taken (slMake 0 4) (slMake 4 12) := by decide +kernel
example : cTakeBytes 4 (probeAt 3) = .taken (slMake 3 7) (slMake 7 12) ∧
    content probeInput (slMake 3 7) = [7, 128, 0, 127] := by decide +kernel
example : cTakeBytes 4 (probeAt 6) = .taken (slMake 6 10) (slMake 10 12) ∧
    content probeInput (slMake 6 10) = [127, 72, 79, 76] := by decide +kernel
example : cTakeBytes 2 (probeAt 9) = .taken (slMake 9 11) (slMake 11 12) := by decide +kernel
example : cTakeBytes 4 (probeAt 9) = .needInput := by decide +kernel
example : cTakeBytes 0 (probeAt 12) = .taken (slMake 12 12) (slMake 12 12) := by decide +kernel
example : cTakeBytes 2 (probeAt 12) = .needInput := by decide +kernel
/-- Line 732 on the rules, through the binding. -/
example : TakeBytes (ofNat 4) (readBytes probeInput (slMake 6 12))
    (.taken (readBytes probeInput (slMake 6 10)) (readBytes probeInput (slMake 10 12))) :=
  (takeBytes_binding (probeAt_valid 6 (by decide)) (by decide) (by decide +kernel)).mpr
    (by rw [show cTakeBytes 4 (slMake 6 12) = .taken (slMake 6 10) (slMake 10 12) by
      decide +kernel]; rfl)

/-- Lines 717, 718, 725, 726, 733, 734, 741, 742, 749, 750 (`BytesEqual`): a slice against an
interned string. -/
example : cBytesEqual probeInput (probeAt 0) (.interned probeInput) = .bit1 := by decide +kernel
example : cBytesEqual probeInput (probeAt 3) (.interned (probeInput.drop 3)) = .bit1 ∧
    cBytesEqual probeInput (probeAt 3) (.interned probeInput) = .bit0 := by decide +kernel
example : cBytesEqual probeInput (probeAt 6) (.interned (probeInput.drop 6)) = .bit1 ∧
    cBytesEqual probeInput (probeAt 6) (.interned probeInput) = .bit0 := by decide +kernel
example : cBytesEqual probeInput (probeAt 9) (.interned (probeInput.drop 9)) = .bit1 ∧
    cBytesEqual probeInput (probeAt 9) (.interned probeInput) = .bit0 := by decide +kernel
example : cBytesEqual probeInput (probeAt 12) (.interned []) = .bit1 ∧
    cBytesEqual probeInput (probeAt 12) (.interned probeInput) = .bit0 := by decide +kernel
/-- Line 726 on the rules, through the binding. -/
example : BytesEqual (readBytes probeInput (slMake 3 12)) (readBytes probeInput (.interned probeInput))
    .bit0 :=
  (bytesEqual_binding (probeAt_valid 3 (by decide)) (.interned _)).mpr (by decide +kernel)

/-! ### The memo of `LookupSchema` -/

/-- A schema list with the opcode `1`. -/
def schemasOne : Schemas := .cons (.recordSchema (Byte.ofWord 1) (.fieldNext .word .fieldsEnd)) .nil

/-- Calls with the opcodes `1`, `2`, `1` and capacity `1`: the third call is answered after the
generations turned over, and every answer is the rules' result. -/
example : (RuleModuleComponents.memoRun2 1 lookupMemoFn ⟨[], []⟩
    [.call (Byte.ofWord 1, schemasOne), .call (Byte.ofWord 2, schemasOne),
      .call (Byte.ofWord 1, schemasOne)]).1 =
    [some (.foundLayout (.fieldNext .word .fieldsEnd)), some .noLayout,
      some (.foundLayout (.fieldNext .word .fieldsEnd))] := by decide
example : LookupSchema (Byte.ofWord 2) schemasOne .noLayout := lookupSchema_iff.mpr (by decide)

end Examples

end Mettapedia.Languages.HOLLight.RuleModuleReader

/-! ## Axioms -/

#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bit.val_bit0
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bit.val_bit1
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bit.val_le_one
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bit.val_ofLow
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bit.ofLow_val
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bit.val_injective
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.val_zero
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.val_bit
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNatAux_congr
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNat_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNat_zero
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNat_of_ne_zero
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNat_two_mul_add
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.val_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.Canonical.val_pos
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.Canonical.of_bit
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.Canonical.bit
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.canonical_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNat_val
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.canonical_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.eq_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNat_injective
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNat_inj
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.ofNat_eq_zero_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.BinNat.Canonical.eq_of_val_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Byte.val_lt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bytes.toList_nil
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bytes.toList_cons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bytes.ofList_nil
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bytes.ofList_cons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bytes.toList_ofList
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Bytes.ofList_toList
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.makeNatBit_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.val_makeNatBit
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.canonical_makeNatBit
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.makeNatBit_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.makeNatBit_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.makeNatBit_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.makeNatBit_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_val
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_eq_none_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.canonical_natPred
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_zero_none
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.compareBits_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.compareBits_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.compareBits_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.compareBits_ofNats
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natCompare_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natCompare_canonical
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natCompare_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natCompare_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natCompare_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natInc_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.val_natInc
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natInc_ne_zero
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.canonical_natInc
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natInc_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natInc_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natInc_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natInc_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natAdd_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.val_natAdd
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.canonical_natAdd
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natAdd_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natAdd_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natAdd_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natAdd_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bitXor_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.val_bitXor
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bitXor_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bitXor_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natXor_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.xor_two_mul_add
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.val_natXor
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.canonical_natXor
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natXor_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natXor_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natXor_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natXor_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natMultiply_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.val_natMultiply
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.canonical_natMultiply
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natMultiply_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natMultiply_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natMultiply_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natMultiply_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natTrim_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.two_mul_add_mod_two_pow
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natTrim_val
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natTrim_isSome
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natTrim_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natTrim_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natTrim_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natTrim_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natSubtract_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natSubtract_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natSubtract_derives
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natSubtract_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natSubtract_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.packByte_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.val_packByte
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.canonical_packByte
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.packByte_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.packByte_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.packByte_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.packByte_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Byte.ofWord_val
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Byte.val_ofWord
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Byte.val_injective
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.byteLength_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.byteLength_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.byteLength_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.byteLength_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.byteLength_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takePush_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takePush_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takePush_total_taken
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takePush_total_needInput
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takeBytes_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takeBytes_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takeBytes_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takeBytes_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takeBytes_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqual_cons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqual_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqualNext_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Cmp.ofNats_eq_equal_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natCompare_packByte
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqual_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqual_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqual_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqual_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqualNext_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqualNext_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqualNext_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.MakeNatBit.fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebJoin_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebRead_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.mk7_ofNat
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.mk6_zero
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebRead_spec
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebRead_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebFuel_surjective
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebRead_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebRead_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebJoin_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebJoin_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebJoin_none_limitExceeded
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebJoin_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.readULEB62_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.readULEB62_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.readULEB62_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvBasis_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvWidth_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvPrime_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvByte_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvByteFn_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvFrom_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvFromFn_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvFrom_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnv_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvByte_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvByte_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvByte_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvFrom_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvFrom_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnv_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnv_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lookupSchema_cons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lookupSchema_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.selectSchema_iff_fn
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lookupSchema_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lookupSchema_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lookupSchema_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lookupSchema_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.selectSchema_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.selectSchema_total
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.selectSchema_functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnBits_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnSmall_lt_bnLimit
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.two_pow_64_le_bnLimit
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.magValue_eq_some_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.magValue_eq_none_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.magValue_of_lt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnShl1Or_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnAdd_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnSub_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnXor_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lt_two_pow_magLimbs
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnMul_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnTrim_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnShl1Iter_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnPack_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.shl1_or_val
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.wordMk_byte8
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.ofWord_wordMk
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.wordMk_kids
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.binKid0_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.binTag_eq_natZero_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.binView
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.binNul_read
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bit_ite_eq_val
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.binMk2_eq_none_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.binMk2_read
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slMax_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slStart_enc
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slEnd_enc
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slMake_fields
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slMake_valid
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.content_slMake
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.content_interned
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slInput_spec
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slNil_spec
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.length_content
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.content_rest
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.content_slCons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slCons_imm_branch
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slCons_copy_branch
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.content_slTake
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.content_slDrop
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.slEqual_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Byte.val_ofU8
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.Byte.ofU8_injective
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.map_val_readBytes
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.readBytes_view
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.readBytes_slCons
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.readBytes_slNil
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.cMakeNatBit_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.cMakeNatBit_eq_none_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natPred_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.cNatCompare_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natCompare_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natInc_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnSucc_eq_none_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natAdd_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnAdd_eq_none_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natXor_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natMultiply_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnMul_eq_none_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natTrim_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.natSubtract_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.packByte_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.cPackByte_eq_none_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.byteLength_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.takeBytes_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bytesEqual_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebAdjust_zero
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.byte_and80
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.byte_shr6
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.uleb_acc
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.uleb_acc_lt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.uleb_join_arith
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.ulebLoop_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebJoinSpec_used
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lebSpec_used
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.readULEB62_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnvStepC_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.fnv_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.lookupSchema_memo_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.magLimbs_two_pow
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnMul_two_pow_none
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.bnMul_refuses_below_bnLimit
#print axioms Mettapedia.Languages.HOLLight.RuleModuleReader.probeAt_valid

-- Written by a sub-agent of Claude (Oruži), main:14 "CC FM".
