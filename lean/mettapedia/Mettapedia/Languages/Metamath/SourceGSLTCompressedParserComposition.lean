import Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
import Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
import Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition
import Mettapedia.Languages.Metamath.ByteSliceForInSupport

/-!
# Raw compressed payloads through the shipped mm-lean4 parser

Tranche item 4.  The raw-source composition carries each compressed
`$p`'s payload as exact located tokens (parentheses, header labels,
body words, terminator, with spans).  The shipped-parser seam
(`CompressedProofLocatedTokens`) consumes located `ByteSlice`s with
byte-content side conditions.  This module constructs the slices from
the same `FileMap` the expansion read and proves the content facts from
the segmentation's own admission guards — no token ledger is invented.

Layer 1 (this section): the slice-of-span constructor and the
loop-free content bridge — `sliceBytes` of a constructed slice is
exactly the composition's `spanBytes`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.SourceGSLTCompressedParserComposition

open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical (LocatedByteSpan)
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTCompressedMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTCompressedParserMMLean4
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTLifecycleComposition

/-- The byte slice a located span denotes inside its file's bytes. -/
def sliceOfSpan (bytes : ByteArray) (span : LocatedByteSpan) : ByteSlice :=
  ByteSlice.mk bytes span.start (span.stop - span.start)

/-- In-range spans (every tokenizer-emitted span is one). -/
structure SpanInRange (bytes : ByteArray) (span : LocatedByteSpan) : Prop where
  start_le_stop : span.start ≤ span.stop
  stop_le_size : span.stop ≤ bytes.size

theorem sliceOfSpan_fields {bytes : ByteArray} {span : LocatedByteSpan}
    (h : SpanInRange bytes span) :
    (sliceOfSpan bytes span).byteArray = bytes ∧
      (sliceOfSpan bytes span).start = span.start ∧
      (sliceOfSpan bytes span).stop = span.stop := by
  have harith : span.start + (span.stop - span.start) = span.stop :=
    Nat.add_sub_cancel' h.start_le_stop
  unfold sliceOfSpan ByteSlice.mk ByteArray.toByteSlice
  rw [harith]
  rw [dif_pos h.stop_le_size, dif_pos h.start_le_stop]
  exact ⟨rfl, rfl, rfl⟩

theorem sliceOfSpan_size {bytes : ByteArray} {span : LocatedByteSpan}
    (h : SpanInRange bytes span) :
    (sliceOfSpan bytes span).size = span.stop - span.start := by
  obtain ⟨-, hstart, hstop⟩ := sliceOfSpan_fields h
  simp [ByteSlice.size, hstart, hstop]

/-- The loop-free content bridge, loop form: the shipped
`sliceBytesLoop` traversal of any slice is a drop/take of the
underlying array's list.  The getElem chains are definitional
(`s[i] = s.byteArray[s.start + i] = s.byteArray.data.toList[s.start + i]`). -/
theorem sliceBytesLoop_eq_drop_take (s : ByteSlice) :
    ∀ (remaining : Nat) (h : remaining ≤ s.size),
      sliceBytesLoop s remaining h =
        (s.byteArray.data.toList.drop
          (s.start + (s.size - remaining))).take remaining
  | 0, _ => by
      rw [List.take_zero]
      rfl
  | remaining + 1, h => by
      have hstop := s.stop_le_size_byteArray
      have hsize : s.size = s.stop - s.start := rfl
      have hlen : s.byteArray.data.toList.length = s.byteArray.size :=
        rfl
      have hbound : s.start + (s.size - 1 - remaining) <
          s.byteArray.data.toList.length := by
        omega
      have h1 : s.start + (s.size - (remaining + 1)) =
          s.start + (s.size - 1 - remaining) := by
        omega
      have h2 : s.start + (s.size - remaining) =
          (s.start + (s.size - 1 - remaining)) + 1 := by
        omega
      simp only [sliceBytesLoop]
      rw [sliceBytesLoop_eq_drop_take s remaining (Nat.le_of_succ_le h)]
      rw [h1, h2, List.drop_eq_getElem_cons hbound,
        List.take_succ_cons]
      congr 1

/-- **The content bridge**: the shipped byte traversal of a
span-constructed slice is exactly the composition's `spanBytes`. -/
theorem sliceBytes_sliceOfSpan {bytes : ByteArray} {span : LocatedByteSpan}
    (h : SpanInRange bytes span) :
    sliceBytes (sliceOfSpan bytes span) =
      spanBytes bytes.data.toList span := by
  unfold sliceBytes spanBytes
  obtain ⟨harr, hstart, hstop⟩ := sliceOfSpan_fields h
  rw [sliceBytesLoop_eq_drop_take]
  rw [sliceOfSpan_size h, harr, hstart]
  simp

/-- Kernel calibration of the bridge. -/
example :
    sliceBytes (sliceOfSpan (ByteArray.mk #[10, 20, 30, 40])
        ⟨"f", 1, 3⟩) =
      spanBytes (ByteArray.mk #[10, 20, 30, 40]).data.toList
        ⟨"f", 1, 3⟩ := by decide

/-! ## Layer 2 — the shipped byte loops through `sliceBytes`

The general `forIn` characterizations live in the module-system support
file (`ByteSliceForInSupport`), where the Batteries loop is nameable;
here they are instantiated for the shipped mm-lean4 content loops. -/

open Mettapedia.Languages.Metamath.ByteSliceForInSupport

/-- The two loop-free byte extractions agree. -/
theorem sliceBytes_eq_sliceList (s : ByteSlice) :
    sliceBytes s = sliceList s := by
  unfold sliceBytes
  rw [sliceBytesLoop_eq_drop_take, sliceList_def, Nat.sub_self,
    Nat.add_zero]

/-- The shipped label lexer as a byte fold (joint accumulator form). -/
theorem toLabel_eq_fold (bs : ByteSlice) :
    Metamath.Verify.toLabel bs =
      (((sliceBytes bs).foldl
          (fun (r : MProd Bool String) c =>
            ⟨if Metamath.Verify.isLabelChar c then r.fst else false,
              r.snd.push (Metamath.Verify.uint8ToChar c)⟩)
          ⟨true, ""⟩).fst,
        ((sliceBytes bs).foldl
          (fun (r : MProd Bool String) c =>
            ⟨if Metamath.Verify.isLabelChar c then r.fst else false,
              r.snd.push (Metamath.Verify.uint8ToChar c)⟩)
          ⟨true, ""⟩).snd) := by
  have hrun : Metamath.Verify.toLabel bs =
      (fun (r : MProd Bool String) => (r.fst, r.snd))
        (ByteSlice.forIn (m := Id) bs (⟨true, ""⟩ : MProd Bool String)
          (fun c r =>
            if Metamath.Verify.isLabelChar c = true then
              pure (ForInStep.yield
                (⟨r.fst, r.snd.push (Metamath.Verify.uint8ToChar c)⟩ :
                  MProd Bool String))
            else
              pure (ForInStep.yield
                (⟨false, r.snd.push (Metamath.Verify.uint8ToChar c)⟩ :
                  MProd Bool String)))) := rfl
  rw [hrun, byteSlice_forIn_yield (β := MProd Bool String) bs _
    (fun c r =>
      ⟨if Metamath.Verify.isLabelChar c then r.fst else false,
        r.snd.push (Metamath.Verify.uint8ToChar c)⟩)
    (fun c r => by
      by_cases hcase : Metamath.Verify.isLabelChar c = true
      · rw [if_pos hcase, if_pos hcase]
      · rw [if_neg hcase, if_neg (by simpa using hcase)]),
    ← sliceBytes_eq_sliceList]

/-- First component of the label fold: the charset check. -/
theorem toLabel_fold_fst (bytes : List UInt8) :
    ∀ (ok₀ : Bool) (s₀ : String),
      (bytes.foldl
          (fun (r : MProd Bool String) c =>
            ⟨if Metamath.Verify.isLabelChar c then r.fst else false,
              r.snd.push (Metamath.Verify.uint8ToChar c)⟩)
          ⟨ok₀, s₀⟩).fst =
        (ok₀ && bytes.all Metamath.Verify.isLabelChar)
  | ok₀, s₀ => by
      induction bytes generalizing ok₀ s₀ with
      | nil => simp
      | cons b rest ih =>
          simp only [List.foldl_cons, List.all_cons]
          rw [ih]
          by_cases hcase : Metamath.Verify.isLabelChar b = true <;>
            simp [hcase]

/-- Second component of the label fold: the pushed string. -/
theorem toLabel_fold_snd (bytes : List UInt8) :
    ∀ (ok₀ : Bool) (s₀ : String),
      (bytes.foldl
          (fun (r : MProd Bool String) c =>
            ⟨if Metamath.Verify.isLabelChar c then r.fst else false,
              r.snd.push (Metamath.Verify.uint8ToChar c)⟩)
          ⟨ok₀, s₀⟩).snd =
        bytes.foldl
          (fun s c => s.push (Metamath.Verify.uint8ToChar c)) s₀
  | ok₀, s₀ => by
      induction bytes generalizing ok₀ s₀ with
      | nil => rfl
      | cons b rest ih =>
          simp only [List.foldl_cons]
          rw [ih]

/-- The shipped byte-to-char embedding is the codepoint embedding. -/
theorem uint8ToChar_eq (b : UInt8) :
    Metamath.Verify.uint8ToChar b = Char.ofNat b.toNat := by
  have h256 : b.toNat < 256 := b.toBitVec.isLt
  have hvalid : Nat.isValidChar b.toNat :=
    Or.inl (Nat.lt_trans h256 (by decide))
  simp only [Metamath.Verify.uint8ToChar, Char.ofNat, hvalid, dif_pos]
  rfl

/-- The pushed-character fold is the composition's token text. -/
theorem foldl_push_eq_tokenText :
    ∀ (bytes : List UInt8) (s₀ : String),
      bytes.foldl
          (fun s c => s.push (Metamath.Verify.uint8ToChar c)) s₀ =
        s₀ ++ tokenText bytes
  | [], s₀ => by
      apply String.ext
      simp [tokenText]
  | b :: rest, s₀ => by
      simp only [List.foldl_cons]
      rw [foldl_push_eq_tokenText rest
        (s₀.push (Metamath.Verify.uint8ToChar b)), uint8ToChar_eq]
      apply String.ext
      simp [tokenText]

/-- **The shipped label lexer, characterized**: on a label-charset
slice it returns `true` and exactly the composition's token text. -/
theorem toLabel_of_labelBytes {bs : ByteSlice}
    (hcharset : (sliceBytes bs).all Metamath.Verify.isLabelChar = true) :
    Metamath.Verify.toLabel bs = (true, tokenText (sliceBytes bs)) := by
  rw [toLabel_eq_fold, toLabel_fold_fst, toLabel_fold_snd,
    foldl_push_eq_tokenText, hcharset]
  apply Prod.ext <;> [skip; apply String.ext] <;> simp

/-- The `eqArray` exit fold, specified: the result bit is prefix
agreement at the running index. -/
theorem eqArray_fold_spec (arr : ByteArray) :
    ∀ (bytes : List UInt8) (k : Nat) (ok : Bool),
      k + bytes.length ≤ arr.size →
      ((foldWithExit
          (fun c (r : MProd Nat Bool) => !(arr[r.fst]! == c))
          (fun _ r => ⟨r.fst, false⟩)
          (fun _ r => ⟨r.fst + 1, r.snd⟩) bytes ⟨k, ok⟩).snd = true ↔
        (ok = true ∧
          bytes = (arr.data.toList.drop k).take bytes.length))
  | [], k, ok, _ => by
      simp [foldWithExit]
  | b :: rest, k, ok, hle => by
      have hk : k < arr.size := by
        have := hle
        simp only [List.length_cons] at this
        omega
      have hkl : k < arr.data.toList.length := hk
      have hbang : arr[k]! = arr[k] := getElem!_pos arr k hk
      have hhead : arr.data.toList[k]'hkl = arr[k] := rfl
      simp only [foldWithExit]
      by_cases harr : arr[k] = b
      · rw [if_neg (by simp [hbang, harr])]
        rw [eqArray_fold_spec arr rest (k + 1) ok (by
          have := hle
          simp only [List.length_cons] at this
          omega)]
        rw [List.drop_eq_getElem_cons hkl, List.length_cons,
          List.take_succ_cons, hhead, harr]
        constructor
        · rintro ⟨hok, hrest⟩
          exact ⟨hok, by rw [← hrest]⟩
        · rintro ⟨hok, heq⟩
          exact ⟨hok, by
            have := List.cons.inj heq
            exact this.2⟩
      · rw [if_pos (by simp [hbang, harr])]
        simp only []
        constructor
        · intro hfalse
          exact absurd hfalse (by simp)
        · rintro ⟨-, heq⟩
          rw [List.drop_eq_getElem_cons hkl, List.length_cons,
            List.take_succ_cons, hhead] at heq
          exact absurd (List.cons.inj heq).1 (fun hh => harr hh.symm)

/-- **The shipped slice/array comparison, characterized.** -/
theorem eqArray_true_iff (bs : ByteSlice) (arr : ByteArray) :
    bs.eqArray arr = true ↔ sliceBytes bs = arr.data.toList := by
  have hrun : bs.eqArray arr =
      (if bs.size ≠ arr.size then false
       else
        (ByteSlice.forIn (m := Id) bs (⟨0, true⟩ : MProd Nat Bool)
          (fun b r =>
            if arr[r.fst]! ≠ b then
              pure (ForInStep.done (⟨r.fst, false⟩ : MProd Nat Bool))
            else
              pure (ForInStep.yield
                (⟨r.fst + 1, r.snd⟩ : MProd Nat Bool)))).snd) := rfl
  have hlistlen : arr.data.toList.length = arr.size := rfl
  by_cases hsize : bs.size = arr.size
  · rw [hrun, if_neg (by simp [hsize])]
    rw [byteSlice_forIn_exit (β := MProd Nat Bool) bs _
      (fun c (r : MProd Nat Bool) => !(arr[r.fst]! == c))
      (fun _ r => ⟨r.fst, false⟩)
      (fun _ r => ⟨r.fst + 1, r.snd⟩)
      (fun c r => by
        by_cases harr : arr[r.fst]! = c
        · rw [if_neg (by simp [harr]), if_neg (by simp [harr])]
        · rw [if_pos (by simp [harr]), if_pos (by simp [harr])])]
    rw [← sliceBytes_eq_sliceList]
    rw [eqArray_fold_spec arr (sliceBytes bs) 0 true (by
      rw [sliceBytes_length]
      omega)]
    rw [List.drop_zero, sliceBytes_length, hsize, ← hlistlen,
      List.take_length]
    simp
  · rw [hrun, if_pos (by simpa using hsize)]
    constructor
    · intro hfalse
      exact absurd hfalse (by simp)
    · intro heq
      have := congrArg List.length heq
      rw [sliceBytes_length, hlistlen] at this
      exact absurd this hsize

/-- Dispatch fact: content inequality forces `eqArray` false. -/
theorem eqArray_eq_false_of_ne {bs : ByteSlice} {arr : ByteArray}
    (h : sliceBytes bs ≠ arr.data.toList) :
    bs.eqArray arr = false := by
  cases heq : bs.eqArray arr with
  | false => rfl
  | true => exact absurd ((eqArray_true_iff bs arr).mp heq) h

/-- Dispatch fact: content equality forces `eqArray` true. -/
theorem eqArray_eq_true_of_eq {bs : ByteSlice} {arr : ByteArray}
    (h : sliceBytes bs = arr.data.toList) :
    bs.eqArray arr = true :=
  (eqArray_true_iff bs arr).mpr h

/-! ## Layer 3 — provenance to slices

Every tokenizer-emitted span is in range, and resolution records each
token's bytes as exactly the span's file content; together these hand
the slice constructor its side conditions with no hypotheses left
behind. -/

/-- Scanner spans are in range (tracked mode start stays behind the
cursor). -/
theorem tokenizesFrom_spans_inRange {fileId : String}
    {bytes : ByteArray} :
    ∀ {cursor : Nat}
      {mode : Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.ScanMode}
      {spans : List LocatedByteSpan},
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.TokenizesFrom
        fileId bytes cursor mode spans →
      (∀ start, mode = .token start → start ≤ cursor) →
      cursor ≤ bytes.size →
      ∀ s ∈ spans, s.start ≤ s.stop ∧ s.stop ≤ bytes.size := by
  intro cursor mode spans h
  induction h with
  | endSeparator cursor atEnd =>
      intro _ _ s hs
      exact nomatch hs
  | endToken cursor start atEnd =>
      intro hmode hcursor s hs
      rcases List.mem_singleton.mp hs with rfl
      exact ⟨Nat.le_trans (hmode start rfl) hcursor, Nat.le_refl _⟩
  | whitespaceSeparator cursor spans inBounds isSpace rest ih =>
      intro _ _ s hs
      exact ih (fun _ h => nomatch h) inBounds s hs
  | whitespaceToken cursor start spans inBounds isSpace rest ih =>
      intro hmode hcursor s hs
      rcases List.mem_cons.mp hs with rfl | htail
      · exact ⟨hmode start rfl, Nat.le_of_lt inBounds⟩
      · exact ih (fun _ h => nomatch h) inBounds s htail
  | nonWhitespaceSeparator cursor spans inBounds notSpace rest ih =>
      intro _ _ s hs
      exact ih
        (fun start h => by
          cases Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.ScanMode.token.inj
            h
          exact Nat.le_succ _)
        inBounds s hs
  | nonWhitespaceToken cursor start spans inBounds notSpace rest ih =>
      intro hmode hcursor s hs
      exact ih
        (fun start' h => by
          cases Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.ScanMode.token.inj
            h
          exact Nat.le_trans (hmode _ rfl) (Nat.le_succ _))
        inBounds s hs

/-- Every span of the canonical scanner is in range. -/
theorem tokenize_spans_inRange {fileId : String} {bytes : ByteArray}
    {s : LocatedByteSpan}
    (hs : s ∈
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.tokenize
        fileId bytes) :
    SpanInRange bytes s := by
  have hrel :=
    (Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.tokenizeFrom
      fileId bytes 0 .separator).2
  have := tokenizesFrom_spans_inRange hrel
    (fun _ h => nomatch h) (Nat.zero_le _) s hs
  exact ⟨this.1, this.2⟩

/-- Resolution records each token's bytes as exactly its span's file
content. -/
theorem resolveTokens_spec (files : FileMap) :
    ∀ {spans : List LocatedByteSpan} {tokens : List LocatedToken},
      resolveTokens files spans = some tokens →
      ∀ t ∈ tokens, ∃ bytes, files t.span.fileId = some bytes ∧
        t.bytes = spanBytes bytes.data.toList t.span ∧ t.span ∈ spans
  | [], tokens, h => by
      simp only [resolveTokens] at h
      cases h
      intro t ht
      exact nomatch ht
  | span :: rest, tokens, h => by
      simp only [resolveTokens] at h
      cases hfile : files span.fileId with
      | none => simp only [hfile] at h; exact nomatch h
      | some content =>
          simp only [hfile] at h
          cases hrest : resolveTokens files rest with
          | none => simp only [hrest] at h; exact nomatch h
          | some tokens' =>
              simp only [hrest] at h
              cases h
              intro t ht
              rcases List.mem_cons.mp ht with rfl | htail
              · exact ⟨content, hfile, rfl, List.Mem.head _⟩
              · obtain ⟨bytes, h1, h2, h3⟩ :=
                  resolveTokens_spec files hrest t htail
                exact ⟨bytes, h1, h2, List.Mem.tail _ h3⟩

/-! ## Layer 4 — charset agreements with the shipped lexer -/

/-- The composition's label charset is exactly mm-lean4's. -/
theorem labelByte_eq_isLabelChar (b : UInt8) :
    labelByte b = Metamath.Verify.isLabelChar b := by
  have hfin : ∀ n : Fin 256,
      labelByte (UInt8.ofNat n.val) =
        Metamath.Verify.isLabelChar (UInt8.ofNat n.val) := by decide
  have h256 : b.toNat < 256 := b.toBitVec.isLt
  have := hfin ⟨b.toNat, h256⟩
  simpa [UInt8.ofNat_toNat] using this

theorem labelBytesValid_all_isLabelChar {tok : List UInt8}
    (h : labelBytesValid tok = true) :
    tok.all Metamath.Verify.isLabelChar = true := by
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  rw [List.all_eq_true] at h2 ⊢
  intro b hb
  rw [← labelByte_eq_isLabelChar]
  exact h2 b hb

/-! ## Layer 5 — the segmentation content invariant

Every span a compressed payload retains was admitted by a byte guard;
the sweep records those guards as membership facts against the token
stream, so the slice builder's side conditions are theorems, not
hypotheses. -/

/-- A located name that arose from a label-charset token. -/
def NameFromLabelToken (tokens : List LocatedToken)
    (n : LocatedName) : Prop :=
  ∃ bytes, (⟨n.span, bytes⟩ : LocatedToken) ∈ tokens ∧
    labelBytesValid bytes = true ∧ n.name = tokenText bytes

/-- The byte-content facts a compressed payload carries. -/
structure CompressedPayloadContent (tokens : List LocatedToken)
    (openParen : LocatedByteSpan) (header : List LocatedName)
    (closeParen : LocatedByteSpan) (words : List LocatedToken)
    (separator terminator : LocatedByteSpan) : Prop where
  sepTok : (⟨separator, proofSeparatorBytes⟩ : LocatedToken) ∈ tokens
  openTok : (⟨openParen, parenOpenBytes⟩ : LocatedToken) ∈ tokens
  closeTok : (⟨closeParen, parenCloseBytes⟩ : LocatedToken) ∈ tokens
  termTok : (⟨terminator,
    SourceGSLTRawSourceComposition.statementEndBytes⟩ :
      LocatedToken) ∈ tokens
  headerToks : ∀ n ∈ header, NameFromLabelToken tokens n
  wordToks : ∀ w ∈ words,
    w ∈ tokens ∧ compressedWordValid w.bytes = true

/-- Content obligations per statement (compressed payloads only). -/
def StatementContent (tokens : List LocatedToken) :
    RawStatement → Prop
  | .provable _ _ _ _ (.compressed openParen header closeParen words)
      separator terminator =>
      CompressedPayloadContent tokens openParen header closeParen words
        separator terminator
  | _ => True

/-- Content already accumulated by an open mode. -/
def ModeContent (tokens : List LocatedToken) : SegMode → Prop
  | .proofDecide _ _ _ separator =>
      (⟨separator, proofSeparatorBytes⟩ : LocatedToken) ∈ tokens
  | .proofHeader _ _ _ separator openParen acc =>
      (⟨separator, proofSeparatorBytes⟩ : LocatedToken) ∈ tokens ∧
      (⟨openParen, parenOpenBytes⟩ : LocatedToken) ∈ tokens ∧
      ∀ n ∈ acc, NameFromLabelToken tokens n
  | .proofWords _ _ _ separator openParen closeParen header acc =>
      (⟨separator, proofSeparatorBytes⟩ : LocatedToken) ∈ tokens ∧
      (⟨openParen, parenOpenBytes⟩ : LocatedToken) ∈ tokens ∧
      (⟨closeParen, parenCloseBytes⟩ : LocatedToken) ∈ tokens ∧
      (∀ n ∈ header, NameFromLabelToken tokens n) ∧
      ∀ w ∈ acc, w ∈ tokens ∧ compressedWordValid w.bytes = true
  | _ => True

set_option linter.unusedSimpArgs false in
/-- One segmentation step preserves the content invariant and emits
only content-carrying statements. -/
theorem segmentStep_content {tokens₀ : List LocatedToken}
    {mode : SegMode} {tok : LocatedToken}
    {emitted : List RawStatement} {next : SegMode}
    (h : segmentStep mode tok = .ok (emitted, next))
    (htok : tok ∈ tokens₀)
    (hmode : ModeContent tokens₀ mode) :
    (∀ st ∈ emitted, StatementContent tokens₀ st) ∧
      ModeContent tokens₀ next := by
  cases mode with
  | top =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        refine ⟨fun st hst => ?_, trivial⟩
      all_goals
        first
          | (rcases List.mem_singleton.mp hst with rfl; trivial)
          | exact nomatch hst
  | pendingLabel label =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals exact ⟨(fun st hst => nomatch hst), trivial⟩
  | collecting kind site acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        refine ⟨fun st hst => ?_, trivial⟩
      all_goals
        first
          | (rcases List.mem_singleton.mp hst with rfl; trivial)
          | exact nomatch hst
  | floatBody site label acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        refine ⟨fun st hst => ?_, trivial⟩
      all_goals
        first
          | (rcases List.mem_singleton.mp hst with rfl; trivial)
          | exact nomatch hst
  | essentialBody site label acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        refine ⟨fun st hst => ?_, trivial⟩
      all_goals
        first
          | (rcases List.mem_singleton.mp hst with rfl; trivial)
          | exact nomatch hst
  | axiomBody site label acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        refine ⟨fun st hst => ?_, trivial⟩
      all_goals
        first
          | (rcases List.mem_singleton.mp hst with rfl; trivial)
          | exact nomatch hst
  | provableBody site label acc =>
      simp only [segmentStep] at h
      by_cases hsep : tok.bytes = proofSeparatorBytes
      · rw [if_pos hsep] at h
        cases h
        refine ⟨(fun st hst => nomatch hst), ?_⟩
        show (⟨tok.span, proofSeparatorBytes⟩ : LocatedToken) ∈ tokens₀
        rw [← hsep]
        exact htok
      · rw [if_neg hsep] at h
        repeat' split at h
        all_goals cases h
        all_goals exact ⟨(fun st hst => nomatch hst), trivial⟩
  | proofDecide site label formula separator =>
      simp only [segmentStep] at h
      by_cases hopen : tok.bytes = parenOpenBytes
      · rw [if_pos hopen] at h
        cases h
        refine ⟨(fun st hst => nomatch hst), ?_⟩
        refine ⟨hmode, ?_, ?_⟩
        · show (⟨tok.span, parenOpenBytes⟩ : LocatedToken) ∈ tokens₀
          rw [← hopen]
          exact htok
        · intro n hn
          exact nomatch hn
      · rw [if_neg hopen] at h
        repeat' split at h
        all_goals cases h
        all_goals exact ⟨(fun st hst => nomatch hst), trivial⟩
  | proofNormal site label formula separator acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        refine ⟨fun st hst => ?_, trivial⟩
      all_goals
        first
          | (rcases List.mem_singleton.mp hst with rfl; trivial)
          | exact nomatch hst
  | proofHeader site label formula separator openParen acc =>
      simp only [segmentStep] at h
      obtain ⟨hsep, hopen, hacc⟩ := hmode
      by_cases hclose : tok.bytes = parenCloseBytes
      · rw [if_pos hclose] at h
        cases h
        refine ⟨(fun st hst => nomatch hst), ?_⟩
        refine ⟨hsep, hopen, ?_, ?_, ?_⟩
        · show (⟨tok.span, parenCloseBytes⟩ : LocatedToken) ∈ tokens₀
          rw [← hclose]
          exact htok
        · intro n hn
          exact hacc n (List.mem_reverse.mp hn)
        · intro w hw
          exact nomatch hw
      · rw [if_neg hclose] at h
        by_cases hlab : labelBytesValid tok.bytes = true
        · rw [if_pos hlab] at h
          cases h
          refine ⟨(fun st hst => nomatch hst), ?_⟩
          refine ⟨hsep, hopen, ?_⟩
          intro n hn
          rcases List.mem_cons.mp hn with rfl | htail
          · exact ⟨tok.bytes, htok, hlab, rfl⟩
          · exact hacc n htail
        · rw [if_neg hlab] at h
          exact nomatch h
  | proofWords site label formula separator openParen closeParen
      header acc =>
      simp only [segmentStep] at h
      obtain ⟨hsep, hopen, hclose, hheader, hacc⟩ := hmode
      by_cases hterm : tok.bytes =
          SourceGSLTRawSourceComposition.statementEndBytes
      · rw [if_pos hterm] at h
        by_cases haccne : acc.isEmpty
        · rw [if_pos haccne] at h
          exact nomatch h
        · rw [if_neg haccne] at h
          cases hsp : splitFormula site formula with
          | rejected r =>
              simp only [hsp] at h
              exact nomatch h
          | ok pair =>
              obtain ⟨typecode, body⟩ := pair
              simp only [hsp] at h
              cases h
              refine ⟨fun st hst => ?_, trivial⟩
              rcases List.mem_singleton.mp hst with rfl
              exact ⟨hsep, hopen, hclose,
                (by
                  show (⟨tok.span,
                      SourceGSLTRawSourceComposition.statementEndBytes⟩ :
                        LocatedToken) ∈ tokens₀
                  rw [← hterm]
                  exact htok),
                hheader,
                fun w hw => hacc w (List.mem_reverse.mp hw)⟩
      · rw [if_neg hterm] at h
        by_cases hword : compressedWordValid tok.bytes = true
        · rw [if_pos hword] at h
          cases h
          refine ⟨(fun st hst => nomatch hst), ?_⟩
          refine ⟨hsep, hopen, hclose, hheader, ?_⟩
          intro w hw
          rcases List.mem_cons.mp hw with rfl | htail
          · exact ⟨htok, hword⟩
          · exact hacc w htail
        · rw [if_neg hword] at h
          exact nomatch h

/-- Run-level content: every statement an accepted run emits carries
its content facts against the full token stream. -/
theorem segmentRun_content {tokens₀ : List LocatedToken} :
    ∀ (tokens : List LocatedToken) (mode : SegMode)
      (acc statements : List RawStatement),
      (∀ t ∈ tokens, t ∈ tokens₀) →
      ModeContent tokens₀ mode →
      (∀ st ∈ acc, StatementContent tokens₀ st) →
      segmentRun tokens mode acc = .ok statements →
      ∀ st ∈ statements, StatementContent tokens₀ st
  | [], mode, acc, statements, hsub, hmode, hacc, h => by
      simp only [segmentRun] at h
      cases hsite : mode.site with
      | none =>
          simp only [hsite] at h
          cases h
          intro st hst
          exact hacc st (List.mem_reverse.mp hst)
      | some site =>
          simp only [hsite] at h
          exact nomatch h
  | tok :: rest, mode, acc, statements, hsub, hmode, hacc, h => by
      simp only [segmentRun] at h
      cases hstep : segmentStep mode tok with
      | rejected r =>
          simp only [hstep] at h
          exact nomatch h
      | ok pair =>
          obtain ⟨emitted, nextMode⟩ := pair
          simp only [hstep] at h
          obtain ⟨hemit, hnext⟩ := segmentStep_content hstep
            (hsub tok (List.Mem.head _)) hmode
          exact segmentRun_content rest nextMode _ statements
            (fun t ht => hsub t (List.Mem.tail _ ht)) hnext
            (fun st hst => by
              rcases List.mem_append.mp hst with hrev | hold
              · exact hemit st (List.mem_reverse.mp hrev)
              · exact hacc st hold)
            h

/-- **Segmentation content**: every accepted statement's compressed
payload spans carry their admission-guard byte facts. -/
theorem segmentStatements_content {tokens : List LocatedToken}
    {statements : List RawStatement}
    (h : segmentStatements tokens = .ok statements) :
    ∀ st ∈ statements, StatementContent tokens st :=
  segmentRun_content tokens .top [] statements (fun _ ht => ht)
    trivial (fun _ hst => nomatch hst) h

/-! ## Layer 6 — byte-fact toolkit for the seam's side conditions -/

theorem parenOpen_toAscii : ("(".toAscii).data.toList = parenOpenBytes := by
  decide

theorem parenClose_toAscii : (")".toAscii).data.toList = parenCloseBytes := by
  decide

theorem commentOpen_toAscii :
    ("$(".toAscii).data.toList = [36, 40] := by decide

theorem includeOpen_toAscii :
    ("$[".toAscii).data.toList = [36, 91] := by decide

theorem finish_toAscii :
    ("$.".toAscii).data.toList =
      SourceGSLTRawSourceComposition.statementEndBytes := by decide

/-- A label-charset token is never a `$`-headed or paren token. -/
theorem labelBytes_ne_dollarHeaded {tok : List UInt8}
    (h : labelBytesValid tok = true) :
    ∀ b rest, tok = b :: rest → b ≠ 36 ∧ b ≠ 41 := by
  intro b rest heq
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  rw [heq, List.all_cons, Bool.and_eq_true] at h2
  constructor
  · intro hb
    rw [hb] at h2
    exact absurd h2.1 (by decide)
  · intro hb
    rw [hb] at h2
    exact absurd h2.1 (by decide)

/-- A compressed-word token is never `$`-headed. -/
theorem compressedWord_ne_dollarHeaded {tok : List UInt8}
    (h : compressedWordValid tok = true) :
    ∀ b rest, tok = b :: rest → b ≠ 36 := by
  intro b rest heq hb
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  rw [heq, List.all_cons, Bool.and_eq_true] at h2
  rw [hb] at h2
  exact absurd h2.1 (by decide)

/-- Head disagreement refutes list equality. -/
theorem ne_of_head_ne {b : UInt8} {rest : List UInt8} {c : UInt8}
    {tail : List UInt8} (hb : b ≠ c) :
    b :: rest ≠ c :: tail := by
  intro h
  exact hb (List.cons.inj h).1

/-- Nonempty charset tokens decompose. -/
theorem exists_cons_of_valid {tok : List UInt8}
    (h : ¬ tok.isEmpty = true) :
    ∃ b rest, tok = b :: rest := by
  cases tok with
  | nil => exact absurd rfl h
  | cons b rest => exact ⟨b, rest, rfl⟩

/-! ## Layer 7 — the located compressed-proof token builder

From per-span slice facts (file bytes, range, exact content), the
shipped seam's `CompressedProofLocatedTokens` is constructed with every
side condition proved. -/

/-- A span together with its file bytes and exact content. -/
structure SliceFacts (expected : List UInt8) : Type where
  fileBytes : ByteArray
  span : LocatedByteSpan
  hrange : SpanInRange fileBytes span
  hcontent : spanBytes fileBytes.data.toList span = expected

def SliceFacts.slice {expected : List UInt8}
    (sf : SliceFacts expected) : ByteSlice :=
  sliceOfSpan sf.fileBytes sf.span

theorem SliceFacts.sliceBytes_eq {expected : List UInt8}
    (sf : SliceFacts expected) :
    sliceBytes sf.slice = expected := by
  rw [SliceFacts.slice, sliceBytes_sliceOfSpan sf.hrange, sf.hcontent]

/-- Slice facts for one explicit-header label. -/
structure HeaderSliceFacts (n : LocatedName) : Type where
  bytes : List UInt8
  sf : SliceFacts bytes
  hvalid : labelBytesValid bytes = true
  hname : n.name = tokenText bytes

/-- Bool-level inequality to the seam's `eqArray` negation. -/
theorem not_eqArray_of_bytes_ne {bs : ByteSlice} {arr : ByteArray}
    (h : sliceBytes bs ≠ arr.data.toList) :
    ¬ bs.eqArray arr = true := by
  rw [eqArray_eq_false_of_ne h]
  exact Bool.false_ne_true

/-- Label-charset slices dispatch to `feedProof` and are not the
header-closing delimiter. -/
theorem label_slice_dispatch {n : LocatedName} (hf : HeaderSliceFacts n) :
    ProofTokenDispatchesToFeedProof hf.sf.slice ∧
      ¬ hf.sf.slice.eqArray ")".toAscii = true := by
  obtain ⟨b, rest, hcons⟩ := exists_cons_of_valid
    (by
      intro hempty
      have := ((Bool.and_eq_true _ _).mp hf.hvalid).1
      rw [hempty] at this
      exact absurd this (by decide))
  obtain ⟨hb36, hb41⟩ := labelBytes_ne_dollarHeaded hf.hvalid b rest hcons
  have hbytes : sliceBytes hf.sf.slice = b :: rest := by
    rw [hf.sf.sliceBytes_eq, hcons]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · exact eqArray_eq_false_of_ne (by
      rw [hbytes, commentOpen_toAscii]
      exact ne_of_head_ne hb36)
  · exact eqArray_eq_false_of_ne (by
      rw [hbytes, includeOpen_toAscii]
      exact ne_of_head_ne hb36)
  · exact eqArray_eq_false_of_ne (by
      rw [hbytes, finish_toAscii]
      exact ne_of_head_ne hb36)
  · exact not_eqArray_of_bytes_ne (by
      rw [hbytes, parenClose_toAscii]
      exact ne_of_head_ne hb41)

/-- Compressed-word slices dispatch to `feedProof`. -/
theorem word_slice_dispatch {expected : List UInt8}
    (sf : SliceFacts expected)
    (hword : compressedWordValid expected = true) :
    ProofTokenDispatchesToFeedProof sf.slice := by
  obtain ⟨b, rest, hcons⟩ := exists_cons_of_valid
    (by
      intro hempty
      have := ((Bool.and_eq_true _ _).mp hword).1
      rw [hempty] at this
      exact absurd this (by decide))
  have hb36 := compressedWord_ne_dollarHeaded hword b rest hcons
  have hbytes : sliceBytes sf.slice = b :: rest := by
    rw [sf.sliceBytes_eq, hcons]
  refine ⟨?_, ?_, ?_⟩
  · exact eqArray_eq_false_of_ne (by
      rw [hbytes, commentOpen_toAscii]
      exact ne_of_head_ne hb36)
  · exact eqArray_eq_false_of_ne (by
      rw [hbytes, includeOpen_toAscii]
      exact ne_of_head_ne hb36)
  · exact eqArray_eq_false_of_ne (by
      rw [hbytes, finish_toAscii]
      exact ne_of_head_ne hb36)

/-- Header sub-builder: located slices with representation and
dispatch, in order. -/
def buildHeader :
    (header : List LocatedName) →
    ((n : LocatedName) → n ∈ header → HeaderSliceFacts n) →
    { l : List (Nat × ByteSlice) //
      PreloadTokensRepresent (l.map Prod.snd) (header.map (·.name)) ∧
        ∀ p ∈ l, ProofTokenDispatchesToFeedProof p.2 }
  | [], _ => ⟨[], .nil, fun p hp => nomatch hp⟩
  | n :: rest, f =>
      let hf := f n (List.Mem.head _)
      let tl := buildHeader rest (fun m hm => f m (List.Mem.tail _ hm))
      ⟨(hf.sf.span.start, hf.sf.slice) :: tl.1,
        by
          refine .cons ⟨(label_slice_dispatch hf).2, ?_⟩ tl.2.1
          rw [toLabel_of_labelBytes (by
            rw [hf.sf.sliceBytes_eq]
            exact labelBytesValid_all_isLabelChar hf.hvalid)]
          rw [hf.sf.sliceBytes_eq, ← hf.hname],
        by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | htail
          · exact (label_slice_dispatch hf).1
          · exact tl.2.2 p htail⟩

/-- Word sub-builder: located slices with exact bytes and dispatch. -/
def buildWords :
    (words : List LocatedToken) →
    ((w : LocatedToken) → w ∈ words → SliceFacts w.bytes) →
    (∀ w ∈ words, compressedWordValid w.bytes = true) →
    { l : List (Nat × ByteSlice) //
      (l.map Prod.snd).map sliceBytes = words.map (·.bytes) ∧
        ∀ p ∈ l, ProofTokenDispatchesToFeedProof p.2 }
  | [], _, _ => ⟨[], rfl, fun p hp => nomatch hp⟩
  | w :: rest, f, hcs =>
      let sf := f w (List.Mem.head _)
      let tl := buildWords rest (fun v hv => f v (List.Mem.tail _ hv))
        (fun v hv => hcs v (List.Mem.tail _ hv))
      ⟨(sf.span.start, sf.slice) :: tl.1,
        by
          simp only [List.map_cons]
          rw [sf.sliceBytes_eq, tl.2.1],
        by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | htail
          · exact word_slice_dispatch sf (hcs w (List.Mem.head _))
          · exact tl.2.2 p htail⟩

/-- **The seam builder**: from per-component slice facts, the shipped
parser's located compressed-proof token sequence, every side condition
proved. -/
def mkCompressedProofLocatedTokens
    (openSF : SliceFacts parenOpenBytes)
    (closeSF : SliceFacts parenCloseBytes)
    (termSF : SliceFacts
      SourceGSLTRawSourceComposition.statementEndBytes)
    {header : List LocatedName}
    (headerSF : (n : LocatedName) → n ∈ header → HeaderSliceFacts n)
    {words : List LocatedToken}
    (wordSF : (w : LocatedToken) → w ∈ words → SliceFacts w.bytes)
    (hwords : ∀ w ∈ words, compressedWordValid w.bytes = true) :
    CompressedProofLocatedTokens (header.map (·.name))
      (words.map (·.bytes)) :=
  let hd := buildHeader header headerSF
  let wd := buildWords words wordSF hwords
  { openLocated := (openSF.span.start, openSF.slice)
    openDispatch :=
      ⟨eqArray_eq_false_of_ne (by
          rw [openSF.sliceBytes_eq, commentOpen_toAscii]
          decide),
        eqArray_eq_false_of_ne (by
          rw [openSF.sliceBytes_eq, includeOpen_toAscii]
          decide),
        eqArray_eq_false_of_ne (by
          rw [openSF.sliceBytes_eq, finish_toAscii]
          decide)⟩
    openDelimiter := eqArray_eq_true_of_eq (by
      rw [openSF.sliceBytes_eq, parenOpen_toAscii])
    headerLocated := hd.1
    headerRepresentation := hd.2.1
    headerDispatch := hd.2.2
    closeLocated := (closeSF.span.start, closeSF.slice)
    closeDispatch :=
      ⟨eqArray_eq_false_of_ne (by
          rw [closeSF.sliceBytes_eq, commentOpen_toAscii]
          decide),
        eqArray_eq_false_of_ne (by
          rw [closeSF.sliceBytes_eq, includeOpen_toAscii]
          decide),
        eqArray_eq_false_of_ne (by
          rw [closeSF.sliceBytes_eq, finish_toAscii]
          decide)⟩
    closeDelimiter := eqArray_eq_true_of_eq (by
      rw [closeSF.sliceBytes_eq, parenClose_toAscii])
    bodyLocated := wd.1
    bodyBytes := wd.2.1
    bodyDispatch := wd.2.2
    finishLocated := (termSF.span.start, termSF.slice)
    finishToken :=
      ⟨eqArray_eq_false_of_ne (by
          rw [termSF.sliceBytes_eq, commentOpen_toAscii]
          decide),
        eqArray_eq_false_of_ne (by
          rw [termSF.sliceBytes_eq, includeOpen_toAscii]
          decide),
        eqArray_eq_true_of_eq (by
          rw [termSF.sliceBytes_eq, finish_toAscii])⟩ }

/-! ## Layer 8 — pipeline obligations determine located proof tokens

The upstream `mmLean4FeedTokensPreserved` consumes, but does not
determine, the located-token sequence.  Here the composed pipeline
constructs it: content facts from the segmentation sweep, file bytes from
the same `FileMap` the expansion read, ranges from the scanner
derivation. -/

/-- One content fact yields the slice facts for its span. -/
theorem sliceFacts_of_content {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {spans : List LocatedByteSpan} {tokens : List LocatedToken}
    (hexp : expandDatabase files policy root fuel = .ok spans)
    (hres : resolveTokens files spans = some tokens)
    {span : LocatedByteSpan} {knownBytes : List UInt8}
    (hmem : (⟨span, knownBytes⟩ : LocatedToken) ∈ tokens) :
    Nonempty (SliceFacts knownBytes) := by
  obtain ⟨fb, hfile, hbytes, hspan⟩ :=
    resolveTokens_spec files hres _ hmem
  obtain ⟨fb', hfile', htok⟩ := expandDatabase_provenance hexp _ hspan
  have hfb : fb = fb' := Option.some.inj (hfile.symm.trans hfile')
  subst hfb
  exact ⟨⟨fb, span, tokenize_spans_inRange htok, hbytes.symm⟩⟩

/-- Every fold obligation's payload is a statement's payload. -/
theorem foldStatements_obligation_payload :
    ∀ {statements : List RawStatement} {state final : SourceState}
      {obligations : List TheoremObligation},
      foldStatements state statements = .ok (final, obligations) →
      ∀ ob ∈ obligations,
        ∃ site label typecode body separator terminator,
          (RawStatement.provable site label typecode body ob.proof
            separator terminator) ∈ statements
  | [], state, final, obligations, h => by
      simp only [foldStatements] at h
      cases h
      intro ob hob
      exact nomatch hob
  | stmt :: rest, state, final, obligations, h => by
      simp only [foldStatements] at h
      cases happ : applyStatement state stmt with
      | rejected r =>
          simp only [happ] at h
          exact nomatch h
      | ok pair =>
          obtain ⟨next, stepObligations⟩ := pair
          simp only [happ] at h
          cases hrest : foldStatements next rest with
          | rejected r =>
              simp only [hrest] at h
              exact nomatch h
          | ok finalPair =>
              obtain ⟨final', restObligations⟩ := finalPair
              simp only [hrest] at h
              cases h
              intro ob hob
              rcases List.mem_append.mp hob with hstep | htail
              · cases stmt with
                | provable site label typecode body proof separator
                    terminator =>
                    obtain ⟨syms, htag, hins, hobs⟩ :=
                      applyStatement_provable_inv happ
                    rw [hobs] at hstep
                    rcases List.mem_singleton.mp hstep with rfl
                    exact ⟨site, label, typecode, body, separator,
                      terminator, List.Mem.head _⟩
                | openScope site =>
                    exact absurd hstep (by
                      intro hmem
                      cases happ2 : applyLocalPayload? .openScope state with
                      | none =>
                          simp only [applyStatement, happ2] at happ
                          exact nomatch happ
                      | some s =>
                          simp only [applyStatement, happ2] at happ
                          cases happ
                          exact nomatch hmem)
                | closeScope site =>
                    exact absurd hstep (by
                      intro hmem
                      cases happ2 : applyLocalPayload? .closeScope state with
                      | none =>
                          simp only [applyStatement, happ2] at happ
                          exact nomatch happ
                      | some middle =>
                          simp only [applyStatement, happ2] at happ
                          cases happ3 : applyLocalPayload? .completeBlock
                              middle with
                          | none =>
                              simp only [happ3] at happ
                              exact nomatch happ
                          | some s =>
                              simp only [happ3] at happ
                              cases happ
                              exact nomatch hmem)
                | constDecl site names terminator =>
                    exact absurd hstep (by
                      intro hmem
                      cases happ2 : applyLocalPayload?
                          (.declareConstants (names.map (·.name)))
                          state with
                      | none =>
                          simp only [applyStatement, happ2] at happ
                          exact nomatch happ
                      | some s =>
                          simp only [applyStatement, happ2] at happ
                          cases happ
                          exact nomatch hmem)
                | varDecl site names terminator =>
                    exact absurd hstep (by
                      intro hmem
                      cases happ2 : applyLocalPayload?
                          (.declareVariables (names.map (·.name)))
                          state with
                      | none =>
                          simp only [applyStatement, happ2] at happ
                          exact nomatch happ
                      | some s =>
                          simp only [applyStatement, happ2] at happ
                          cases happ
                          exact nomatch hmem)
                | djDecl site names terminator =>
                    exact absurd hstep (by
                      intro hmem
                      cases happ2 : applyLocalPayload?
                          (.declareDisjoint (names.map (·.name)))
                          state with
                      | none =>
                          simp only [applyStatement, happ2] at happ
                          exact nomatch happ
                      | some s =>
                          simp only [applyStatement, happ2] at happ
                          cases happ
                          exact nomatch hmem)
                | floating site label typecode variableName terminator =>
                    exact absurd hstep (by
                      intro hmem
                      cases happ2 : applyLocalPayload?
                          (.declareFloating label.name typecode.name
                            variableName.name) state with
                      | none =>
                          simp only [applyStatement, happ2] at happ
                          exact nomatch happ
                      | some s =>
                          simp only [applyStatement, happ2] at happ
                          cases happ
                          exact nomatch hmem)
                | essential site label typecode body terminator =>
                    exact absurd hstep (by
                      intro hmem
                      cases htag : tagBody state body with
                      | rejected r =>
                          simp only [applyStatement, htag] at happ
                          exact nomatch happ
                      | ok syms =>
                          simp only [applyStatement, htag] at happ
                          cases happ2 : applyLocalPayload?
                              (.declareEssential label.name
                                ⟨typecode.name, syms⟩) state with
                          | none =>
                              simp only [happ2] at happ
                              exact nomatch happ
                          | some s =>
                              simp only [happ2] at happ
                              cases happ
                              exact nomatch hmem)
                | axiomatic site label typecode body terminator =>
                    exact absurd hstep (by
                      intro hmem
                      cases htag : tagBody state body with
                      | rejected r =>
                          simp only [applyStatement, htag] at happ
                          exact nomatch happ
                      | ok syms =>
                          simp only [applyStatement, htag] at happ
                          cases happ2 : applyLocalPayload?
                              (.declareAxiom label.name
                                ⟨typecode.name, syms⟩) state with
                          | none =>
                              simp only [happ2] at happ
                              exact nomatch happ
                          | some s =>
                              simp only [happ2] at happ
                              cases happ
                              exact nomatch hmem)
              · obtain ⟨site, label, typecode, body, separator,
                  terminator, hmem⟩ :=
                    foldStatements_obligation_payload hrest ob htail
                exact ⟨site, label, typecode, body, separator,
                  terminator, List.Mem.tail _ hmem⟩

/-- Every compressed obligation produced by an accepted source run determines
the shipped parser's located compressed-proof token sequence, with all side
conditions proved from the run's own content, resolution, and provenance. -/
theorem runSource_compressedProofLocatedTokens {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {state : SourceState} {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations)
    {ob : TheoremObligation} (hob : ob ∈ obligations)
    {openParen closeParen : LocatedByteSpan}
    {header : List LocatedName} {words : List LocatedToken}
    (hproof : ob.proof =
      .compressed openParen header closeParen words) :
    Nonempty (CompressedProofLocatedTokens (header.map (·.name))
      (words.map (·.bytes))) := by
  classical
  simp only [runSource] at h
  cases hexp : expandDatabase files policy root fuel with
  | rejected r => simp only [hexp] at h; exact nomatch h
  | ok spans =>
      simp only [hexp] at h
      cases hres : resolveTokens files spans with
      | none => simp only [hres] at h; exact nomatch h
      | some tokens =>
          simp only [hres] at h
          cases hseg : segmentStatements tokens with
          | rejected r => simp only [hseg] at h; exact nomatch h
          | ok statements =>
              simp only [hseg] at h
              cases hfold : foldStatements initialState statements with
              | rejected r => simp only [hfold] at h; exact nomatch h
              | ok pair =>
                  obtain ⟨final, obs⟩ := pair
                  simp only [hfold] at h
                  cases hcomplete : sourceStateComplete final with
                  | false =>
                      rw [if_neg (by simp [hcomplete])] at h
                      cases hscan : scopeSites statements [] with
                      | nil => simp only [hscan] at h; exact nomatch h
                      | cons site rest =>
                          simp only [hscan] at h
                          exact nomatch h
                  | true =>
                      simp only [hcomplete, ↓reduceIte] at h
                      cases h
                      obtain ⟨site, label, typecode, body, separator,
                        terminator, hmem⟩ :=
                        foldStatements_obligation_payload hfold ob hob
                      have hcontent :=
                        segmentStatements_content hseg _ hmem
                      rw [hproof] at hcontent
                      obtain ⟨hsep, hopen, hclose, hterm, hheader,
                        hwords⟩ := hcontent
                      obtain ⟨openSF⟩ :=
                        sliceFacts_of_content hexp hres hopen
                      obtain ⟨closeSF⟩ :=
                        sliceFacts_of_content hexp hres hclose
                      obtain ⟨termSF⟩ :=
                        sliceFacts_of_content hexp hres hterm
                      refine ⟨mkCompressedProofLocatedTokens openSF
                        closeSF termSF
                        (fun n hn => ?_) (fun w hw => ?_)
                        (fun w hw => (hwords w hw).2)⟩
                      · have hnf : Nonempty (HeaderSliceFacts n) := by
                          obtain ⟨bytes, hmem', hvalid, hname⟩ :=
                            hheader n hn
                          obtain ⟨sf⟩ :=
                            sliceFacts_of_content hexp hres hmem'
                          exact ⟨⟨bytes, sf, hvalid, hname⟩⟩
                        exact Classical.choice hnf
                      · exact Classical.choice
                          (sliceFacts_of_content hexp hres
                            (hwords w hw).1)

end Mettapedia.Languages.Metamath.SourceGSLTCompressedParserComposition
