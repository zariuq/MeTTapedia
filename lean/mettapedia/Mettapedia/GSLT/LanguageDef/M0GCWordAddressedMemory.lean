import Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory

/-!
# Finite-word byte addressing for the M0GC checker

This module refines the target-neutral `Nat`-indexed byte region to explicit
unsigned 64-bit addresses.  Address addition is checked before conversion or
array access; modular wraparound is never treated as a valid address.

In standard terminology, this is a finite-word abstract-machine refinement
for an executable proof-certificate checker.  It is a fully connected
intermediate proof of concept, not yet mutable memory, allocation, pointer
provenance, file I/O, Pancake or Clight execution, compiler correctness, or
machine-code correctness.
-/

namespace Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory

open Mettapedia.GSLT.LanguageDef.M0GCBoundedByteMemory
open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCWireFormat
open Mettapedia.GSLT.LanguageDef.M0GCFlatBodyLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatHeaderLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCorrespondence
open Mettapedia.GSLT.LanguageDef.M0GCFlatCertificateLoaderCompleteness

/-! ## Checked unsigned address arithmetic -/

/-- Mathematical addition guarded by the exact unsigned 64-bit carrier
boundary.  Successful results therefore have their ordinary natural-number
meaning; failure means that the sum would wrap. -/
def checkedAdd (left right : UInt64) : Option UInt64 :=
  if fits : left.toNat + right.toNat < UInt64.size then
    some (UInt64.ofNatLT (left.toNat + right.toNat) fits)
  else
    none

theorem checkedAdd_of_lt (left right : UInt64)
    (fits : left.toNat + right.toNat < UInt64.size) :
    checkedAdd left right =
      some (UInt64.ofNatLT (left.toNat + right.toNat) fits) := by
  simp [checkedAdd, fits]

theorem checkedAdd_eq_none_iff (left right : UInt64) :
    checkedAdd left right = none ↔
      UInt64.size ≤ left.toNat + right.toNat := by
  simp [checkedAdd]

theorem checkedAdd_some_toNat
    {left right result : UInt64}
    (accepted : checkedAdd left right = some result) :
    result.toNat = left.toNat + right.toNat := by
  unfold checkedAdd at accepted
  split at accepted
  next fits =>
    simp only [Option.some.injEq] at accepted
    subst result
    exact UInt64.toNat_ofNatLT
  next overflow => contradiction

@[simp] theorem checkedAdd_zero (address : UInt64) :
    checkedAdd address 0 = some address := by
  have fits : address.toNat + (0 : UInt64).toNat < UInt64.size := by
    simpa using address.toNat_lt_size
  rw [checkedAdd_of_lt address 0 fits]
  congr 1

/-- Mathematical multiplication guarded by the exact unsigned 64-bit carrier
boundary.  This is used for byte strides and record counts; modular
multiplication is never accepted as an address calculation. -/
def checkedMul (left right : UInt64) : Option UInt64 :=
  if fits : left.toNat * right.toNat < UInt64.size then
    some (UInt64.ofNatLT (left.toNat * right.toNat) fits)
  else
    none

theorem checkedMul_of_lt (left right : UInt64)
    (fits : left.toNat * right.toNat < UInt64.size) :
    checkedMul left right =
      some (UInt64.ofNatLT (left.toNat * right.toNat) fits) := by
  simp [checkedMul, fits]

theorem checkedMul_eq_none_iff (left right : UInt64) :
    checkedMul left right = none ↔
      UInt64.size ≤ left.toNat * right.toNat := by
  simp [checkedMul]

theorem checkedMul_some_toNat
    {left right result : UInt64}
    (accepted : checkedMul left right = some result) :
    result.toNat = left.toNat * right.toNat := by
  unfold checkedMul at accepted
  split at accepted
  next fits =>
    simp only [Option.some.injEq] at accepted
    subst result
    exact UInt64.toNat_ofNatLT
  next overflow => contradiction

/-- Positive arithmetic discriminator below the carrier boundary. -/
example : checkedAdd 104 32 = some 136 := by
  decide

/-- Negative arithmetic discriminator: maximum address plus one is rejected
instead of wrapping to zero. -/
example : checkedAdd (UInt64.ofNat (UInt64.size - 1)) 1 = none := by
  decide

/-- Positive checked-scaling discriminator. -/
example : checkedMul 20 7 = some 140 := by
  decide

/-- Negative checked-scaling discriminator. -/
example : checkedMul (UInt64.ofNat (UInt64.size - 1)) 2 = none := by
  decide

/-! ## Word-addressed regions -/

/-- An immutable byte region whose base and extent fit in the unsigned 64-bit
address space.  `addressable` rules out overflow at the region's upper bound;
`inBounds` connects those addresses to the backing array. -/
structure WordRegion where
  cells : Array UInt8
  base : UInt64
  extent : UInt64
  inBounds : base.toNat + extent.toNat ≤ cells.size
  addressable : base.toNat + extent.toNat < UInt64.size

namespace WordRegion

/-- Forget finite-word representation while retaining the same array region. -/
def toNeutral (region : WordRegion) : ByteRegion where
  cells := region.cells
  base := region.base.toNat
  extent := region.extent.toNat
  inBounds := region.inBounds

/-- Compile a source byte list only when its complete length is representable
as a 64-bit extent. -/
def ofList? (bytes : List UInt8) : Option WordRegion :=
  if fits : bytes.length < UInt64.size then
    some
      { cells := bytes.toArray
        base := 0
        extent := UInt64.ofNatLT bytes.length fits
        inBounds := by simp
        addressable := by simpa }
  else
    none

theorem ofList?_eq_none_iff (bytes : List UInt8) :
    ofList? bytes = none ↔ UInt64.size ≤ bytes.length := by
  simp [ofList?]

/-- Every admitted source compilation forgets to the original neutral byte
region exactly. -/
theorem toNeutral_of_ofList?
    (bytes : List UInt8) (region : WordRegion)
    (compiled : ofList? bytes = some region) :
    region.toNeutral = ByteRegion.ofList bytes := by
  unfold ofList? at compiled
  split at compiled
  next fits =>
    simp only [Option.some.injEq] at compiled
    subst region
    simp [toNeutral, ByteRegion.ofList]
  next tooLarge => contradiction

/-- Ordinary finite fixtures compile successfully. -/
example : (ofList? [10, 20, 30]).isSome = true := by
  decide

/-! ## Checked range loads -/

/-- Read a complete half-open byte range using finite-word addresses.

The implementation checks three distinct additions before touching the
backing array:

1. `offset + width`, to reject a wrapped relative interval;
2. `base + offset`, to reject a wrapped starting address;
3. `absoluteStart + width`, to reject a wrapped ending address.

The mathematical region invariant makes the second and third failures
unreachable after a successful relative bounds check, but retaining those
checks in the executable definition keeps the target operation faithful to a
future low-level implementation. -/
def loadBytes? (region : WordRegion) (offset width : UInt64) :
    Option (List UInt8) :=
  match checkedAdd offset width with
  | none => none
  | some relativeEnd =>
      if relativeEnd.toNat ≤ region.extent.toNat then
        match checkedAdd region.base offset with
        | none => none
        | some absoluteStart =>
            match checkedAdd absoluteStart width with
            | none => none
            | some absoluteEnd =>
                some
                  ((region.cells.extract absoluteStart.toNat
                    absoluteEnd.toNat).toList)
      else
        none

/-- Finite-word range loading refines the already-qualified neutral memory
operation exactly.  This theorem covers success, declared-region overflow,
and unsigned-address overflow; it is not agreement-by-definition because the
word loader independently performs three checked additions. -/
theorem loadBytes?_refines_neutral
    (region : WordRegion) (offset width : UInt64) :
    region.loadBytes? offset width =
      region.toNeutral.loadBytes? offset.toNat width.toNat := by
  have addressable := region.addressable
  unfold loadBytes?
  cases relativeResult : checkedAdd offset width with
  | none =>
      have overflow : UInt64.size ≤ offset.toNat + width.toNat :=
        (checkedAdd_eq_none_iff offset width).mp relativeResult
      have outside :
          ¬(offset.toNat + width.toNat ≤ region.extent.toNat) := by
        omega
      simp [ByteRegion.loadBytes?, toNeutral, outside]
  | some relativeEnd =>
      have relativeValue :
          relativeEnd.toNat = offset.toNat + width.toNat :=
        checkedAdd_some_toNat relativeResult
      by_cases within : relativeEnd.toNat ≤ region.extent.toNat
      · have neutralWithin :
            offset.toNat + width.toNat ≤ region.extent.toNat := by
          simpa [relativeValue] using within
        have startFits :
            region.base.toNat + offset.toNat < UInt64.size := by
          omega
        let absoluteStart := UInt64.ofNatLT
          (region.base.toNat + offset.toNat) startFits
        have startResult :
            checkedAdd region.base offset = some absoluteStart := by
          exact checkedAdd_of_lt region.base offset startFits
        have startValue :
            absoluteStart.toNat = region.base.toNat + offset.toNat := by
          exact UInt64.toNat_ofNatLT
        have endFits :
            absoluteStart.toNat + width.toNat < UInt64.size := by
          omega
        let absoluteEnd := UInt64.ofNatLT
          (absoluteStart.toNat + width.toNat) endFits
        have endResult :
            checkedAdd absoluteStart width = some absoluteEnd := by
          exact checkedAdd_of_lt absoluteStart width endFits
        have endValue :
            absoluteEnd.toNat = absoluteStart.toNat + width.toNat := by
          exact UInt64.toNat_ofNatLT
        simp only [within, startResult, endResult]
        simp [ByteRegion.loadBytes?, toNeutral, neutralWithin,
          startValue, endValue, Nat.add_assoc]
      · have neutralOutside :
            ¬(offset.toNat + width.toNat ≤ region.extent.toNat) := by
          simpa [relativeValue] using within
        simp [within, ByteRegion.loadBytes?, toNeutral,
          neutralOutside]

/-- A nonzero-base fixture ensures that the representation theorem is not
validated only by zero-based address arithmetic. -/
def nonzeroBaseFixture : WordRegion where
  cells := #[99, 10, 20, 30, 88]
  base := 1
  extent := 3
  inBounds := by decide
  addressable := by decide

/-- Positive range discriminator through a nonzero base. -/
example : nonzeroBaseFixture.loadBytes? 1 2 = some [20, 30] := by
  decide

/-- Negative bounds discriminator: a partial suffix is never returned. -/
example : nonzeroBaseFixture.loadBytes? 2 2 = none := by
  decide

/-- Negative overflow discriminator at the executable memory operation. -/
example :
    nonzeroBaseFixture.loadBytes?
      (UInt64.ofNat (UInt64.size - 1)) 1 = none := by
  decide

/-! ## Fixed-width fields over word addresses -/

/-- Apply a sequential decoder only to an exactly bounded word-addressed
field.  Exhaustion is checked locally, so a shorter decoder cannot accept a
prefix of the declared field. -/
def readField? (read : Reader α) (width : UInt64) (region : WordRegion)
    (offset : UInt64) : Option α := do
  let field ← region.loadBytes? offset width
  ByteRegion.readerExhaustive? read field

/-- Word-addressed field decoding is a congruent lifting of the proved range
refinement.  All arithmetic content remains in
`loadBytes?_refines_neutral`; this theorem records compositionality of the
decoder boundary. -/
theorem readField?_refines_neutral
    (read : Reader α) (width : UInt64) (region : WordRegion)
    (offset : UInt64) :
    readField? read width region offset =
      ByteRegion.readField? read width.toNat region.toNeutral offset.toNat := by
  unfold readField? ByteRegion.readField?
  rw [loadBytes?_refines_neutral]

/-- A successful bounded field read witnesses a non-overflowing next address.
This is the progress invariant needed by checked fixed-stride loops. -/
theorem readField?_some_implies_checkedAdd
    (read : Reader α) (width : UInt64) (region : WordRegion)
    (offset : UInt64) (value : α)
    (accepted : readField? read width region offset = some value) :
    ∃ next, checkedAdd offset width = some next := by
  unfold readField? at accepted
  cases nextResult : checkedAdd offset width with
  | none =>
      simp [loadBytes?, nextResult] at accepted
  | some next =>
      exact ⟨next, rfl⟩

def loadUInt16LE? (region : WordRegion) (offset : UInt64) : Option UInt16 :=
  readField? readUInt16LE 2 region offset

theorem loadUInt16LE?_refines_neutral
    (region : WordRegion) (offset : UInt64) :
    region.loadUInt16LE? offset =
      region.toNeutral.loadUInt16LE? offset.toNat := by
  exact readField?_refines_neutral readUInt16LE 2 region offset

def loadUInt32LE? (region : WordRegion) (offset : UInt64) : Option UInt32 :=
  readField? readUInt32LE 4 region offset

theorem loadUInt32LE?_refines_neutral
    (region : WordRegion) (offset : UInt64) :
    region.loadUInt32LE? offset =
      region.toNeutral.loadUInt32LE? offset.toNat := by
  exact readField?_refines_neutral readUInt32LE 4 region offset

def loadUInt64LE? (region : WordRegion) (offset : UInt64) : Option UInt64 :=
  readField? readUInt64LE 8 region offset

theorem loadUInt64LE?_refines_neutral
    (region : WordRegion) (offset : UInt64) :
    region.loadUInt64LE? offset =
      region.toNeutral.loadUInt64LE? offset.toNat := by
  exact readField?_refines_neutral readUInt64LE 8 region offset

def loadBlock? (region : WordRegion) (offset width : UInt64) :
    Option (List UInt8) :=
  readField? (readBytes width.toNat) width region offset

theorem loadBlock?_refines_neutral
    (region : WordRegion) (offset width : UInt64) :
    region.loadBlock? offset width =
      region.toNeutral.loadBlock? offset.toNat width.toNat := by
  exact readField?_refines_neutral (readBytes width.toNat) width region offset

/-! ## Checked fixed-stride table loops -/

/-- Read a fixed number of equally sized fields.  Each recursive address is
obtained by checked unsigned addition; overflow terminates with rejection. -/
def loadManyFields? (read : Reader α) (width : UInt64)
    (region : WordRegion) : UInt64 → Nat → Option (List α)
  | _, 0 => some []
  | offset, count + 1 => do
      let head ← readField? read width region offset
      let next ← checkedAdd offset width
      let tail ← loadManyFields? read width region next count
      some (head :: tail)

/-- Exact loop refinement.  The proof uses successful field decoding to
obtain the checked successor address at every iteration, then relates that
address to ordinary natural-number stride addition. -/
theorem loadManyFields?_refines_neutral
    (read : Reader α) (width : UInt64) (region : WordRegion) :
    ∀ offset count,
      loadManyFields? read width region offset count =
        ByteRegion.loadMany?
          (ByteRegion.readField? read width.toNat) width.toNat
          region.toNeutral offset.toNat count := by
  intro offset count
  induction count generalizing offset with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [loadManyFields?, ByteRegion.loadMany?]
      rw [readField?_refines_neutral]
      cases fieldResult :
          ByteRegion.readField? read width.toNat region.toNeutral offset.toNat with
      | none => simp
      | some head =>
          have wordAccepted :
              readField? read width region offset = some head := by
            rw [readField?_refines_neutral]
            exact fieldResult
          obtain ⟨next, nextResult⟩ :=
            readField?_some_implies_checkedAdd
              read width region offset head wordAccepted
          have nextValue :
              next.toNat = offset.toNat + width.toNat :=
            checkedAdd_some_toNat nextResult
          rw [nextResult]
          dsimp only [Bind.bind, instMonadOption, Option.bind]
          rw [inductionHypothesis next]
          simp [nextValue]

def loadTermNode? (region : WordRegion) (offset : UInt64) :
    Option TermNode :=
  readField? readTermNode 20 region offset

theorem loadTermNode?_refines_neutral
    (region : WordRegion) (offset : UInt64) :
    region.loadTermNode? offset =
      region.toNeutral.loadTermNode? offset.toNat := by
  exact readField?_refines_neutral readTermNode 20 region offset

def loadProofNode? (region : WordRegion) (offset : UInt64) :
    Option ProofNode :=
  readField? readProofNode 32 region offset

theorem loadProofNode?_refines_neutral
    (region : WordRegion) (offset : UInt64) :
    region.loadProofNode? offset =
      region.toNeutral.loadProofNode? offset.toNat := by
  exact readField?_refines_neutral readProofNode 32 region offset

/-- Positive table-loop discriminator. -/
example :
    loadManyFields? readUInt16LE 2
      { cells := (encodeUInt16LE 7 ++ encodeUInt16LE 9).toArray
        base := 0
        extent := 4
        inBounds := by simp [encodeUInt16LE]
        addressable := by decide }
      0 2 = some [7, 9] := by
  decide

/-- Negative table-loop discriminator: the second record is incomplete and
the loop rejects the whole table. -/
example :
    loadManyFields? readUInt16LE 2
      { cells := (encodeUInt16LE 7 ++ [9]).toArray
        base := 0
        extent := 3
        inBounds := by simp [encodeUInt16LE]
        addressable := by decide }
      0 2 = none := by
  decide

/-! ## Checked body layout -/

theorem termTableOffset_le_bodyByteLength (counts : BodyCounts) :
    termTableOffset counts ≤ bodyByteLength counts := by
  simp [termTableOffset, bodyByteLength, premiseTableOffset,
    argumentTableOffset, proofTableOffset, childTableOffset]

theorem childTableOffset_le_bodyByteLength (counts : BodyCounts) :
    childTableOffset counts ≤ bodyByteLength counts := by
  unfold bodyByteLength premiseTableOffset argumentTableOffset
    proofTableOffset
  omega

theorem proofTableOffset_le_bodyByteLength (counts : BodyCounts) :
    proofTableOffset counts ≤ bodyByteLength counts := by
  unfold bodyByteLength premiseTableOffset argumentTableOffset
  omega

theorem argumentTableOffset_le_bodyByteLength (counts : BodyCounts) :
    argumentTableOffset counts ≤ bodyByteLength counts := by
  unfold bodyByteLength premiseTableOffset
  omega

theorem premiseTableOffset_le_bodyByteLength (counts : BodyCounts) :
    premiseTableOffset counts ≤ bodyByteLength counts := by
  simp [bodyByteLength]

/-- All count-derived body offsets compiled to finite words under one common
proof that the complete body width is addressable. -/
structure BodyLayout where
  termOffset : UInt64
  childOffset : UInt64
  proofOffset : UInt64
  argumentOffset : UInt64
  premiseOffset : UInt64
  bodyWidth : UInt64

/-- Compile the complete layout atomically.  Checking the largest endpoint is
sufficient because every table offset is proved below it. -/
def BodyLayout.ofCounts? (counts : BodyCounts) : Option BodyLayout :=
  if bodyFits : bodyByteLength counts < UInt64.size then
    some
      { termOffset := UInt64.ofNatLT (termTableOffset counts)
          (lt_of_le_of_lt (termTableOffset_le_bodyByteLength counts) bodyFits)
        childOffset := UInt64.ofNatLT (childTableOffset counts)
          (lt_of_le_of_lt (childTableOffset_le_bodyByteLength counts) bodyFits)
        proofOffset := UInt64.ofNatLT (proofTableOffset counts)
          (lt_of_le_of_lt (proofTableOffset_le_bodyByteLength counts) bodyFits)
        argumentOffset := UInt64.ofNatLT (argumentTableOffset counts)
          (lt_of_le_of_lt (argumentTableOffset_le_bodyByteLength counts) bodyFits)
        premiseOffset := UInt64.ofNatLT (premiseTableOffset counts)
          (lt_of_le_of_lt (premiseTableOffset_le_bodyByteLength counts) bodyFits)
        bodyWidth := UInt64.ofNatLT (bodyByteLength counts) bodyFits }
  else
    none

theorem BodyLayout.ofCounts?_eq_none_iff (counts : BodyCounts) :
    BodyLayout.ofCounts? counts = none ↔
      UInt64.size ≤ bodyByteLength counts := by
  simp [BodyLayout.ofCounts?]

theorem BodyLayout.ofCounts?_some_bodyWidth
    (counts : BodyCounts) (layout : BodyLayout)
    (compiled : BodyLayout.ofCounts? counts = some layout) :
    layout.bodyWidth.toNat = bodyByteLength counts := by
  unfold BodyLayout.ofCounts? at compiled
  split at compiled
  next bodyFits =>
    simp only [Option.some.injEq] at compiled
    subst layout
    exact UInt64.toNat_ofNatLT
  next tooLarge => contradiction

/-- Load the five M0GC body tables through checked word addresses.  The body
must exactly exhaust the suffix beginning at `bodyBase`. -/
def readBodyAt? (counts : BodyCounts) (region : WordRegion)
    (bodyBase : UInt64) : Option BodyTables := do
  let layout ← BodyLayout.ofCounts? counts
  if bodyBase.toNat ≤ region.extent.toNat ∧
      region.extent.toNat - bodyBase.toNat = layout.bodyWidth.toNat then do
    let termStart ← checkedAdd bodyBase layout.termOffset
    let childStart ← checkedAdd bodyBase layout.childOffset
    let proofStart ← checkedAdd bodyBase layout.proofOffset
    let argumentStart ← checkedAdd bodyBase layout.argumentOffset
    let premiseStart ← checkedAdd bodyBase layout.premiseOffset
    let terms ←
      loadManyFields? readTermNode 20 region termStart counts.termCount
    let children ←
      loadManyFields? readUInt32LE 4 region childStart counts.childCount
    let proofs ←
      loadManyFields? readProofNode 32 region proofStart counts.proofCount
    let arguments ←
      loadManyFields? readUInt32LE 4 region argumentStart counts.argumentCount
    let premises ←
      loadManyFields? readUInt32LE 4 region premiseStart counts.premiseCount
    some { terms, children, proofs, arguments, premises }
  else
    none

/-- The checked word-addressed body algorithm has exactly the behavior of the
neutral body algorithm, including rejection when the count-derived layout is
too large for the word carrier. -/
theorem readBodyAt?_refines_neutral
    (counts : BodyCounts) (region : WordRegion) (bodyBase : UInt64) :
    readBodyAt? counts region bodyBase =
      ByteRegion.readBodyAtMemory?
        counts region.toNeutral bodyBase.toNat := by
  unfold readBodyAt?
  cases layoutResult : BodyLayout.ofCounts? counts with
  | none =>
      have bodyTooLarge :
          UInt64.size ≤ bodyByteLength counts :=
        (BodyLayout.ofCounts?_eq_none_iff counts).mp layoutResult
      have extentFits : region.extent.toNat < UInt64.size := by
        have addressable := region.addressable
        omega
      have bodyMismatch :
          region.extent.toNat - bodyBase.toNat ≠ bodyByteLength counts := by
        omega
      simp [ByteRegion.readBodyAtMemory?, toNeutral, bodyMismatch]
  | some layout =>
      unfold BodyLayout.ofCounts? at layoutResult
      split at layoutResult
      next bodyFits =>
        simp only [Option.some.injEq] at layoutResult
        subst layout
        let compiledLayout : BodyLayout :=
          { termOffset := UInt64.ofNatLT (termTableOffset counts)
              (lt_of_le_of_lt
                (termTableOffset_le_bodyByteLength counts) bodyFits)
            childOffset := UInt64.ofNatLT (childTableOffset counts)
              (lt_of_le_of_lt
                (childTableOffset_le_bodyByteLength counts) bodyFits)
            proofOffset := UInt64.ofNatLT (proofTableOffset counts)
              (lt_of_le_of_lt
                (proofTableOffset_le_bodyByteLength counts) bodyFits)
            argumentOffset := UInt64.ofNatLT (argumentTableOffset counts)
              (lt_of_le_of_lt
                (argumentTableOffset_le_bodyByteLength counts) bodyFits)
            premiseOffset := UInt64.ofNatLT (premiseTableOffset counts)
              (lt_of_le_of_lt
                (premiseTableOffset_le_bodyByteLength counts) bodyFits)
            bodyWidth := UInt64.ofNatLT (bodyByteLength counts) bodyFits }
        change
          (if bodyBase.toNat ≤ region.extent.toNat ∧
              region.extent.toNat - bodyBase.toNat =
                compiledLayout.bodyWidth.toNat then _ else none) = _
        have extentFits : region.extent.toNat < UInt64.size := by
          have addressable := region.addressable
          omega
        by_cases bodyExact :
            bodyBase.toNat ≤ region.extent.toNat ∧
              region.extent.toNat - bodyBase.toNat = bodyByteLength counts
        · have termStartFits :
              bodyBase.toNat + termTableOffset counts < UInt64.size := by
            have termLe := termTableOffset_le_bodyByteLength counts
            omega
          have childStartFits :
              bodyBase.toNat + childTableOffset counts < UInt64.size := by
            have childLe := childTableOffset_le_bodyByteLength counts
            omega
          have proofStartFits :
              bodyBase.toNat + proofTableOffset counts < UInt64.size := by
            have proofLe := proofTableOffset_le_bodyByteLength counts
            omega
          have argumentStartFits :
              bodyBase.toNat + argumentTableOffset counts < UInt64.size := by
            have argumentLe := argumentTableOffset_le_bodyByteLength counts
            omega
          have premiseStartFits :
              bodyBase.toNat + premiseTableOffset counts < UInt64.size := by
            have premiseLe := premiseTableOffset_le_bodyByteLength counts
            omega
          have wordBodyExact :
              bodyBase.toNat ≤ region.extent.toNat ∧
                region.extent.toNat - bodyBase.toNat =
                  compiledLayout.bodyWidth.toNat := by
            simpa [compiledLayout] using bodyExact
          have termStartFits' :
              bodyBase.toNat + compiledLayout.termOffset.toNat <
                UInt64.size := by
            simpa [compiledLayout] using termStartFits
          have childStartFits' :
              bodyBase.toNat + compiledLayout.childOffset.toNat <
                UInt64.size := by
            simpa [compiledLayout] using childStartFits
          have proofStartFits' :
              bodyBase.toNat + compiledLayout.proofOffset.toNat <
                UInt64.size := by
            simpa [compiledLayout] using proofStartFits
          have argumentStartFits' :
              bodyBase.toNat + compiledLayout.argumentOffset.toNat <
                UInt64.size := by
            simpa [compiledLayout] using argumentStartFits
          have premiseStartFits' :
              bodyBase.toNat + compiledLayout.premiseOffset.toNat <
                UInt64.size := by
            simpa [compiledLayout] using premiseStartFits
          rw [if_pos wordBodyExact]
          unfold ByteRegion.readBodyAtMemory?
          simp only [toNeutral]
          rw [if_pos bodyExact]
          rw [checkedAdd_of_lt bodyBase compiledLayout.termOffset
            termStartFits']
          rw [checkedAdd_of_lt bodyBase compiledLayout.childOffset
            childStartFits']
          rw [checkedAdd_of_lt bodyBase compiledLayout.proofOffset
            proofStartFits']
          rw [checkedAdd_of_lt bodyBase compiledLayout.argumentOffset
            argumentStartFits']
          rw [checkedAdd_of_lt bodyBase compiledLayout.premiseOffset
            premiseStartFits']
          dsimp only [Bind.bind, instMonadOption, Option.bind]
          rw [loadManyFields?_refines_neutral]
          rw [loadManyFields?_refines_neutral]
          rw [loadManyFields?_refines_neutral]
          rw [loadManyFields?_refines_neutral]
          rw [loadManyFields?_refines_neutral]
          simp [compiledLayout]
          rw [Nat.mod_eq_of_lt termStartFits]
          rw [Nat.mod_eq_of_lt childStartFits]
          rw [Nat.mod_eq_of_lt proofStartFits]
          rw [Nat.mod_eq_of_lt argumentStartFits]
          rw [Nat.mod_eq_of_lt premiseStartFits]
          rfl
        · have wordBodyNotExact :
              ¬(bodyBase.toNat ≤ region.extent.toNat ∧
                region.extent.toNat - bodyBase.toNat =
                  compiledLayout.bodyWidth.toNat) := by
            simpa [compiledLayout] using bodyExact
          simp [wordBodyNotExact, ByteRegion.readBodyAtMemory?, toNeutral,
            bodyExact]
      next bodyTooLarge => contradiction

/-! ## Header loading over word addresses -/

/-- The fixed-offset M0GC header algorithm expressed entirely through
finite-word field loads.  M0GC remains an experimental GSLT certificate
format; this is not an official MM0/MMB parser. -/
def readHeader? (region : WordRegion) : Option Header := do
  let decodedMagic ← region.loadBlock? 0 4
  if decodedMagic = M0GCWireFormat.magic then do
    let decodedVersion ← region.loadUInt16LE? 4
    if decodedVersion = version then do
      let flags ← region.loadUInt16LE? 6
      let termCount ← region.loadUInt32LE? 8
      let childCount ← region.loadUInt32LE? 12
      let proofCount ← region.loadUInt32LE? 16
      let argumentCount ← region.loadUInt32LE? 20
      let premiseReferenceCount ← region.loadUInt32LE? 24
      let goalTerm ← region.loadUInt32LE? 28
      let profileDigest ← region.loadBlock? 32 32
      let sourceDigest ← region.loadBlock? 64 32
      let bodyChecksum ← region.loadUInt64LE? 96
      some
        { flags, termCount, childCount, proofCount, argumentCount,
          premiseReferenceCount, goalTerm, profileDigest, sourceDigest,
          bodyChecksum }
    else
      none
  else
    none

/-- The independently word-addressed header algorithm refines the neutral
bounded-memory header algorithm on every admitted region. -/
theorem readHeader?_refines_neutral (region : WordRegion) :
    region.readHeader? = region.toNeutral.readHeaderMemory? := by
  unfold readHeader? ByteRegion.readHeaderMemory?
  rw [loadBlock?_refines_neutral]
  rw [loadUInt16LE?_refines_neutral]
  rw [loadUInt16LE?_refines_neutral]
  rw [loadUInt32LE?_refines_neutral]
  rw [loadUInt32LE?_refines_neutral]
  rw [loadUInt32LE?_refines_neutral]
  rw [loadUInt32LE?_refines_neutral]
  rw [loadUInt32LE?_refines_neutral]
  rw [loadUInt32LE?_refines_neutral]
  rw [loadBlock?_refines_neutral]
  rw [loadBlock?_refines_neutral]
  rw [loadUInt64LE?_refines_neutral]
  simp [digestWidth]

/-- Compiling a source list to finite-word memory and reading its header has
exactly the behavior of the proved flat list loader. -/
theorem readHeader?_ofList?
    (bytes : List UInt8) (region : WordRegion)
    (compiled : ofList? bytes = some region) :
    region.readHeader? = readHeaderFlat? bytes := by
  rw [readHeader?_refines_neutral]
  rw [toNeutral_of_ofList? bytes region compiled]
  exact ByteRegion.readHeaderMemory?_ofList bytes

/-- Positive full-header discriminator for every successful compilation of
the canonical canary certificate. -/
theorem canary_word_header_accepts
    (region : WordRegion)
    (compiled :
      ofList? (encodeCertificate canaryCertificate) = some region) :
    region.readHeader? = some canaryHeader := by
  rw [readHeader?_ofList? _ region compiled]
  exact canary_flat_header_accepts

/-- Negative header discriminator: corrupt magic remains rejected through
the finite-word representation. -/
theorem corrupt_magic_word_header_rejected
    (region : WordRegion)
    (compiled :
      ofList? (0 :: (encodeCertificate canaryCertificate).tail) =
        some region) :
    region.readHeader? = none := by
  rw [readHeader?_ofList? _ region compiled]
  exact corrupt_magic_flat_header_rejected

/-! ## Complete certificates over word addresses -/

/-- Header, exact body, and original-byte checksum composed over one
finite-word region.  The layout is compiled before either the raw-body load
or the five typed table loops, so an unrepresentable body is rejected
uniformly. -/
def readCertificate? (region : WordRegion) : Option Certificate := do
  let header ← region.readHeader?
  let counts := BodyCounts.ofHeader header
  let layout ← BodyLayout.ofCounts? counts
  let bodyBytes ← region.loadBytes? 104 layout.bodyWidth
  let tables ← region.readBodyAt? counts 104
  if header.bodyChecksum = fnv1a64 bodyBytes then
    some (M0GCCanonicalBodyBytes.certificateOfTables header tables)
  else
    none

/-- The complete finite-word loader exactly refines the complete neutral
bounded-memory loader for every admitted region. -/
theorem readCertificate?_refines_neutral (region : WordRegion) :
    region.readCertificate? = region.toNeutral.readCertificateMemory? := by
  unfold readCertificate? ByteRegion.readCertificateMemory?
  rw [readHeader?_refines_neutral]
  cases headerResult : region.toNeutral.readHeaderMemory? with
  | none => rfl
  | some header =>
      dsimp only [Bind.bind, instMonadOption, Option.bind]
      let counts := BodyCounts.ofHeader header
      cases layoutResult : BodyLayout.ofCounts? counts with
      | none =>
          have bodyTooLarge :
              UInt64.size ≤ bodyByteLength counts :=
            (BodyLayout.ofCounts?_eq_none_iff counts).mp layoutResult
          have extentFits : region.extent.toNat < UInt64.size := by
            have addressable := region.addressable
            omega
          have rangeOutside :
              ¬(104 + bodyByteLength counts ≤ region.extent.toNat) := by
            omega
          have neutralRangeRejected :
              region.toNeutral.loadBytes? 104 (bodyByteLength counts) =
                none := by
            simp [ByteRegion.loadBytes?, toNeutral, rangeOutside]
          dsimp [counts] at neutralRangeRejected
          rw [neutralRangeRejected]
      | some layout =>
          dsimp only [Bind.bind, instMonadOption, Option.bind]
          have bodyWidth :=
            BodyLayout.ofCounts?_some_bodyWidth
              counts layout layoutResult
          rw [loadBytes?_refines_neutral]
          rw [bodyWidth]
          rw [readBodyAt?_refines_neutral]
          simp [counts]

/-- Successful source compilation transports the word loader all the way to
the proved flat certificate loader. -/
theorem readCertificate?_ofList?
    (bytes : List UInt8) (region : WordRegion)
    (compiled : ofList? bytes = some region) :
    region.readCertificate? = readCertificateFlat? bytes := by
  rw [readCertificate?_refines_neutral]
  rw [toNeutral_of_ofList? bytes region compiled]
  exact ByteRegion.readCertificateMemory?_ofList bytes

/-- Standard producer completeness at the finite-word boundary. -/
theorem readCertificate?_encodeCertificate
    (certificate : Certificate) (encodable : certificate.Encodable)
    (region : WordRegion)
    (compiled : ofList? (encodeCertificate certificate) = some region) :
    region.readCertificate? = some certificate := by
  rw [readCertificate?_ofList? _ region compiled]
  exact readCertificateFlat?_encodeCertificate certificate encodable

/-- Positive complete-certificate discriminator. -/
theorem canary_word_certificate_accepts
    (region : WordRegion)
    (compiled :
      ofList? (encodeCertificate canaryCertificate) = some region) :
    region.readCertificate? = some canaryCertificate := by
  exact readCertificate?_encodeCertificate
    canaryCertificate canaryCertificate_encodable region compiled

/-- Negative complete-certificate discriminator: a checksum mutation remains
rejected through word addressing. -/
theorem wrong_checksum_word_certificate_rejected
    (region : WordRegion)
    (compiled : ofList? wrongChecksumCanary = some region) :
    region.readCertificate? = none := by
  rw [readCertificate?_ofList? _ region compiled]
  exact wrong_checksum_flat_rejected

/-- Negative complete-certificate discriminator: trailing bytes remain
observable and force rejection. -/
theorem trailing_word_certificate_rejected
    (region : WordRegion)
    (compiled :
      ofList? (encodeCertificate canaryCertificate ++ [0]) = some region) :
    region.readCertificate? = none := by
  rw [readCertificate?_ofList? _ region compiled]
  exact trailing_byte_flat_rejected

end WordRegion

#print axioms checkedAdd_eq_none_iff
#print axioms checkedAdd_some_toNat
#print axioms checkedMul_eq_none_iff
#print axioms checkedMul_some_toNat
#print axioms WordRegion.toNeutral_of_ofList?
#print axioms WordRegion.loadBytes?_refines_neutral
#print axioms WordRegion.readField?_refines_neutral
#print axioms WordRegion.readField?_some_implies_checkedAdd
#print axioms WordRegion.loadManyFields?_refines_neutral
#print axioms WordRegion.BodyLayout.ofCounts?_eq_none_iff
#print axioms WordRegion.BodyLayout.ofCounts?_some_bodyWidth
#print axioms WordRegion.readBodyAt?_refines_neutral
#print axioms WordRegion.readHeader?_refines_neutral
#print axioms WordRegion.readHeader?_ofList?
#print axioms WordRegion.canary_word_header_accepts
#print axioms WordRegion.corrupt_magic_word_header_rejected
#print axioms WordRegion.readCertificate?_refines_neutral
#print axioms WordRegion.readCertificate?_ofList?
#print axioms WordRegion.readCertificate?_encodeCertificate
#print axioms WordRegion.canary_word_certificate_accepts
#print axioms WordRegion.wrong_checksum_word_certificate_rejected

end Mettapedia.GSLT.LanguageDef.M0GCWordAddressedMemory
