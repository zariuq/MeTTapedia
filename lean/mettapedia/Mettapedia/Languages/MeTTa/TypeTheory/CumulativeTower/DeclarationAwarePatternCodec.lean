import Mettapedia.GSLT.LanguageDef.ExactEndpointCodec
import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation

/-!
# Exact Pattern data for declaration-aware Prime terms

The declaration-aware kernel uses intrinsically scoped terms: a value of
`Tm Head n` can mention exactly the `n` variables in its ambient telescope.
The generic inference checker, by contrast, consumes unindexed `Pattern`
data.  This file supplies the lossless bridge between the two levels.

The encoding uses a fixed constructor alphabet.  Natural numbers, strings,
declaration names, levels, heads, terms, and contexts are all ordinary ground
data rather than dynamic constructor labels.  A typing claim records its
ambient arity once and decodes the context, subject, and type at that same
index.  Consequently malformed scope cannot enter through the decoder.
-/

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec

open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Fixed-alphabet scalar data -/

def encodeNat : Nat → Pattern
  | 0 => .apply "prime-nat-zero" []
  | n + 1 => .apply "prime-nat-succ" [encodeNat n]

def decodeNat? : Pattern → Option Nat
  | .apply "prime-nat-zero" [] => some 0
  | .apply "prime-nat-succ" [predecessor] => do
      pure ((← decodeNat? predecessor) + 1)
  | _ => none

@[simp] theorem decodeNat?_encodeNat (value : Nat) :
    decodeNat? (encodeNat value) = some value := by
  induction value with
  | zero => rfl
  | succ value ih => simp [encodeNat, decodeNat?, ih]

theorem encodeNat_injective : Function.Injective encodeNat :=
  PartialCodec.encode_injective
    { encode := encodeNat
      decode := decodeNat?
      decode_encode := decodeNat?_encodeNat }

def encodeChars : List Char → Pattern
  | [] => .apply "prime-string-nil" []
  | character :: rest =>
      .apply "prime-string-cons" [encodeNat character.toNat, encodeChars rest]

def decodeChars? : Pattern → Option (List Char)
  | .apply "prime-string-nil" [] => some []
  | .apply "prime-string-cons" [codepoint, rest] => do
      pure (Char.ofNat (← decodeNat? codepoint) :: (← decodeChars? rest))
  | _ => none

@[simp] theorem decodeChars?_encodeChars (characters : List Char) :
    decodeChars? (encodeChars characters) = some characters := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
      simp [encodeChars, decodeChars?, ih, Char.ofNat_toNat]

def encodeString (value : String) : Pattern := encodeChars value.toList

def decodeString? (encoded : Pattern) : Option String := do
  pure (String.ofList (← decodeChars? encoded))

@[simp] theorem decodeString?_encodeString (value : String) :
    decodeString? (encodeString value) = some value := by
  have rebuild : String.ofList value.toList = value := by
    apply String.toList_injective
    simp
  simp [decodeString?, encodeString, rebuild]

def encodeDeclName : Lean.Name → Pattern
  | .anonymous => .apply "prime-name-anonymous" []
  | .str pre component =>
      .apply "prime-name-string" [encodeDeclName pre, encodeString component]
  | .num pre component =>
      .apply "prime-name-number" [encodeDeclName pre, encodeNat component]

def decodeDeclName? : Pattern → Option Lean.Name
  | .apply "prime-name-anonymous" [] => some .anonymous
  | .apply "prime-name-string" [pre, component] => do
      pure (.str (← decodeDeclName? pre) (← decodeString? component))
  | .apply "prime-name-number" [pre, component] => do
      pure (.num (← decodeDeclName? pre) (← decodeNat? component))
  | _ => none

@[simp] theorem decodeDeclName?_encodeDeclName (name : Lean.Name) :
    decodeDeclName? (encodeDeclName name) = some name := by
  induction name with
  | anonymous => rfl
  | str pre component ih =>
      simp [encodeDeclName, decodeDeclName?, ih]
  | num pre component ih =>
      simp [encodeDeclName, decodeDeclName?, ih]

def encodeLevel : LevelExpr → Pattern
  | .const value => .apply "prime-level-const" [encodeNat value]
  | .param index => .apply "prime-level-param" [encodeNat index]
  | .succ level => .apply "prime-level-succ" [encodeLevel level]
  | .max left right =>
      .apply "prime-level-max" [encodeLevel left, encodeLevel right]

def decodeLevel? : Pattern → Option LevelExpr
  | .apply "prime-level-const" [value] => do
      pure (.const (← decodeNat? value))
  | .apply "prime-level-param" [index] => do
      pure (.param (← decodeNat? index))
  | .apply "prime-level-succ" [level] => do
      pure (.succ (← decodeLevel? level))
  | .apply "prime-level-max" [left, right] => do
      pure (.max (← decodeLevel? left) (← decodeLevel? right))
  | _ => none

@[simp] theorem decodeLevel?_encodeLevel (level : LevelExpr) :
    decodeLevel? (encodeLevel level) = some level := by
  induction level with
  | const value => simp [encodeLevel, decodeLevel?]
  | param index => simp [encodeLevel, decodeLevel?]
  | succ level ih => simp [encodeLevel, decodeLevel?, ih]
  | max left right leftIH rightIH =>
      simp [encodeLevel, decodeLevel?, leftIH, rightIH]

def encodeTowerHead : Tower.Head → Pattern
  | .legacyGround => .apply "prime-head-legacy-ground" []
  | .sort level => .apply "prime-head-sort" [encodeLevel level]

def decodeTowerHead? : Pattern → Option Tower.Head
  | .apply "prime-head-legacy-ground" [] => some .legacyGround
  | .apply "prime-head-sort" [level] => do
      pure (.sort (← decodeLevel? level))
  | _ => none

@[simp] theorem decodeTowerHead?_encodeTowerHead (head : Tower.Head) :
    decodeTowerHead? (encodeTowerHead head) = some head := by
  cases head with
  | legacyGround => rfl
  | sort level => simp [encodeTowerHead, decodeTowerHead?]

def towerHeadCodec : PartialCodec Tower.Head Pattern where
  encode := encodeTowerHead
  decode := decodeTowerHead?
  decode_encode := decodeTowerHead?_encodeTowerHead

/-! ## Intrinsically scoped terms and contexts -/

def encodeTm (headCodec : PartialCodec Head Pattern) :
    Tm Head n → Pattern
  | .var index => .apply "prime-tm-var" [encodeNat index.val]
  | .const name => .apply "prime-tm-const" [encodeDeclName name]
  | .head head => .apply "prime-tm-head" [headCodec.encode head]
  | .pi domain body =>
      .apply "prime-tm-pi" [encodeTm headCodec domain, encodeTm headCodec body]
  | .sigma domain body =>
      .apply "prime-tm-sigma" [encodeTm headCodec domain, encodeTm headCodec body]
  | .id type left right =>
      .apply "prime-tm-id"
        [encodeTm headCodec type, encodeTm headCodec left,
          encodeTm headCodec right]
  | .lam body => .apply "prime-tm-lam" [encodeTm headCodec body]
  | .app function argument =>
      .apply "prime-tm-app"
        [encodeTm headCodec function, encodeTm headCodec argument]
  | .pair first second =>
      .apply "prime-tm-pair"
        [encodeTm headCodec first, encodeTm headCodec second]
  | .fst pair => .apply "prime-tm-fst" [encodeTm headCodec pair]
  | .snd pair => .apply "prime-tm-snd" [encodeTm headCodec pair]
  | .refl term => .apply "prime-tm-refl" [encodeTm headCodec term]

def decodeTm? (headCodec : PartialCodec Head Pattern) (n : Nat) :
    Pattern → Option (Tm Head n)
  | .apply "prime-tm-var" [encodedIndex] => do
      let index ← decodeNat? encodedIndex
      if inScope : index < n then
        pure (.var ⟨index, inScope⟩)
      else
        none
  | .apply "prime-tm-const" [name] => do
      pure (.const (← decodeDeclName? name))
  | .apply "prime-tm-head" [head] => do
      pure (.head (← headCodec.decode head))
  | .apply "prime-tm-pi" [domain, body] => do
      pure (.pi (← decodeTm? headCodec n domain)
        (← decodeTm? headCodec (n + 1) body))
  | .apply "prime-tm-sigma" [domain, body] => do
      pure (.sigma (← decodeTm? headCodec n domain)
        (← decodeTm? headCodec (n + 1) body))
  | .apply "prime-tm-id" [type, left, right] => do
      pure (.id (← decodeTm? headCodec n type)
        (← decodeTm? headCodec n left) (← decodeTm? headCodec n right))
  | .apply "prime-tm-lam" [body] => do
      pure (.lam (← decodeTm? headCodec (n + 1) body))
  | .apply "prime-tm-app" [function, argument] => do
      pure (.app (← decodeTm? headCodec n function)
        (← decodeTm? headCodec n argument))
  | .apply "prime-tm-pair" [first, second] => do
      pure (.pair (← decodeTm? headCodec n first)
        (← decodeTm? headCodec n second))
  | .apply "prime-tm-fst" [pair] => do
      pure (.fst (← decodeTm? headCodec n pair))
  | .apply "prime-tm-snd" [pair] => do
      pure (.snd (← decodeTm? headCodec n pair))
  | .apply "prime-tm-refl" [term] => do
      pure (.refl (← decodeTm? headCodec n term))
  | _ => none

@[simp] theorem decodeTm?_encodeTm
    (headCodec : PartialCodec Head Pattern) (term : Tm Head n) :
    decodeTm? headCodec n (encodeTm headCodec term) = some term := by
  induction term with
  | var index =>
      simp [encodeTm, decodeTm?, index.isLt]
  | const name => simp [encodeTm, decodeTm?]
  | head head => simp [encodeTm, decodeTm?, headCodec.decode_encode]
  | pi domain body domainIH bodyIH =>
      simp [encodeTm, decodeTm?, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [encodeTm, decodeTm?, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [encodeTm, decodeTm?, typeIH, leftIH, rightIH]
  | lam body bodyIH => simp [encodeTm, decodeTm?, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTm, decodeTm?, functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [encodeTm, decodeTm?, firstIH, secondIH]
  | fst pair pairIH => simp [encodeTm, decodeTm?, pairIH]
  | snd pair pairIH => simp [encodeTm, decodeTm?, pairIH]
  | refl term termIH => simp [encodeTm, decodeTm?, termIH]

def tmCodec (headCodec : PartialCodec Head Pattern) (n : Nat) :
    PartialCodec (Tm Head n) Pattern where
  encode := encodeTm headCodec
  decode := decodeTm? headCodec n
  decode_encode := decodeTm?_encodeTm headCodec

def encodeCtx (headCodec : PartialCodec Head Pattern) :
    Ctx Head n → Pattern
  | .nil => .apply "prime-ctx-nil" []
  | .snoc context type =>
      .apply "prime-ctx-snoc"
        [encodeCtx headCodec context, encodeTm headCodec type]

def decodeCtx? (headCodec : PartialCodec Head Pattern) :
    (n : Nat) → Pattern → Option (Ctx Head n)
  | 0, .apply "prime-ctx-nil" [] => some .nil
  | n + 1, .apply "prime-ctx-snoc" [context, type] => do
      pure (.snoc (← decodeCtx? headCodec n context)
        (← decodeTm? headCodec n type))
  | _, _ => none

@[simp] theorem decodeCtx?_encodeCtx
    (headCodec : PartialCodec Head Pattern) (context : Ctx Head n) :
    decodeCtx? headCodec n (encodeCtx headCodec context) = some context := by
  induction context with
  | nil => rfl
  | snoc context type contextIH =>
      simp [encodeCtx, decodeCtx?, contextIH]

def ctxCodec (headCodec : PartialCodec Head Pattern) (n : Nat) :
    PartialCodec (Ctx Head n) Pattern where
  encode := encodeCtx headCodec
  decode := decodeCtx? headCodec n
  decode_encode := decodeCtx?_encodeCtx headCodec

/-! ## One scope-coherent typing-claim carrier -/

/-- A context, subject, and type sharing one intrinsic ambient arity. -/
structure TypingClaim (Head : Type) where
  arity : Nat
  context : Ctx Head arity
  subject : Tm Head arity
  type : Tm Head arity

def encodeTypingClaim (headCodec : PartialCodec Head Pattern)
    (claim : TypingClaim Head) : Pattern :=
  .apply "prime-has-type"
    [encodeNat claim.arity, encodeCtx headCodec claim.context,
      encodeTm headCodec claim.subject, encodeTm headCodec claim.type]

def decodeTypingClaim? (headCodec : PartialCodec Head Pattern) :
    Pattern → Option (TypingClaim Head)
  | .apply "prime-has-type" [arity, context, subject, type] => do
      let n ← decodeNat? arity
      pure
        { arity := n
          context := ← decodeCtx? headCodec n context
          subject := ← decodeTm? headCodec n subject
          type := ← decodeTm? headCodec n type }
  | _ => none

@[simp] theorem decodeTypingClaim?_encodeTypingClaim
    (headCodec : PartialCodec Head Pattern) (claim : TypingClaim Head) :
    decodeTypingClaim? headCodec (encodeTypingClaim headCodec claim) =
      some claim := by
  cases claim
  simp [encodeTypingClaim, decodeTypingClaim?]

def typingClaimCodec (headCodec : PartialCodec Head Pattern) :
    PartialCodec (TypingClaim Head) Pattern where
  encode := encodeTypingClaim headCodec
  decode := decodeTypingClaim? headCodec
  decode_encode := decodeTypingClaim?_encodeTypingClaim headCodec

def towerTypingClaimCodec : PartialCodec (TypingClaim Tower.Head) Pattern :=
  typingClaimCodec towerHeadCodec

/-! ## Checker-side shape laws -/

theorem encodeNat_ground (value : Nat) :
    (encodeNat value).isGroundAt 0 = true := by
  induction value with
  | zero => simp [encodeNat, Pattern.isGroundAt, Pattern.isGroundListAt]
  | succ value ih =>
      simp [encodeNat, Pattern.isGroundAt, Pattern.isGroundListAt, ih]

theorem encodeNat_canonical (value : Nat) :
    (encodeNat value).hasCanonicalBinderMetadata = true := by
  induction value with
  | zero =>
      simp [encodeNat, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | succ value ih =>
      simp [encodeNat, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

private theorem encodeChars_ground (characters : List Char) :
    (encodeChars characters).isGroundAt 0 = true := by
  induction characters with
  | nil => simp [encodeChars, Pattern.isGroundAt, Pattern.isGroundListAt]
  | cons character rest ih =>
      simp [encodeChars, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeNat_ground, ih]

private theorem encodeChars_canonical (characters : List Char) :
    (encodeChars characters).hasCanonicalBinderMetadata = true := by
  induction characters with
  | nil =>
      simp [encodeChars, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons character rest ih =>
      simp [encodeChars, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical, ih]

theorem encodeDeclName_ground (name : Lean.Name) :
    (encodeDeclName name).isGroundAt 0 = true := by
  induction name with
  | anonymous =>
      simp [encodeDeclName, Pattern.isGroundAt, Pattern.isGroundListAt]
  | str pre component ih =>
      simp [encodeDeclName, encodeString, Pattern.isGroundAt,
        Pattern.isGroundListAt, ih, encodeChars_ground]
  | num pre component ih =>
      simp [encodeDeclName, Pattern.isGroundAt, Pattern.isGroundListAt,
        ih, encodeNat_ground]

theorem encodeDeclName_canonical (name : Lean.Name) :
    (encodeDeclName name).hasCanonicalBinderMetadata = true := by
  induction name with
  | anonymous =>
      simp [encodeDeclName, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | str pre component ih =>
      simp [encodeDeclName, encodeString, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih, encodeChars_canonical]
  | num pre component ih =>
      simp [encodeDeclName, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih, encodeNat_canonical]

theorem encodeLevel_ground (level : LevelExpr) :
    (encodeLevel level).isGroundAt 0 = true := by
  induction level with
  | const value =>
      simp [encodeLevel, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeNat_ground]
  | param index =>
      simp [encodeLevel, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeNat_ground]
  | succ level ih =>
      simp [encodeLevel, Pattern.isGroundAt, Pattern.isGroundListAt, ih]
  | max left right leftIH rightIH =>
      simp [encodeLevel, Pattern.isGroundAt, Pattern.isGroundListAt,
        leftIH, rightIH]

theorem encodeLevel_canonical (level : LevelExpr) :
    (encodeLevel level).hasCanonicalBinderMetadata = true := by
  induction level with
  | const value =>
      simp [encodeLevel, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical]
  | param index =>
      simp [encodeLevel, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical]
  | succ level ih =>
      simp [encodeLevel, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]
  | max left right leftIH rightIH =>
      simp [encodeLevel, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, leftIH, rightIH]

theorem encodeTowerHead_ground (head : Tower.Head) :
    (encodeTowerHead head).isGroundAt 0 = true := by
  cases head with
  | legacyGround =>
      simp [encodeTowerHead, Pattern.isGroundAt, Pattern.isGroundListAt]
  | sort level =>
      simp [encodeTowerHead, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeLevel_ground]

theorem encodeTowerHead_canonical (head : Tower.Head) :
    (encodeTowerHead head).hasCanonicalBinderMetadata = true := by
  cases head with
  | legacyGround =>
      simp [encodeTowerHead, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | sort level =>
      simp [encodeTowerHead, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeLevel_canonical]

theorem encodeTm_ground (headCodec : PartialCodec Head Pattern)
    (headGround : ∀ head, (headCodec.encode head).isGroundAt 0 = true)
    (term : Tm Head n) :
    (encodeTm headCodec term).isGroundAt 0 = true := by
  induction term with
  | var index =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeNat_ground]
  | const name =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeDeclName_ground]
  | head head =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt,
        headGround]
  | pi domain body domainIH bodyIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt,
        typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt,
        functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt,
        firstIH, secondIH]
  | fst pair pairIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt, pairIH]
  | snd pair pairIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt, pairIH]
  | refl term termIH =>
      simp [encodeTm, Pattern.isGroundAt, Pattern.isGroundListAt, termIH]

theorem encodeTm_canonical (headCodec : PartialCodec Head Pattern)
    (headCanonical : ∀ head,
      (headCodec.encode head).hasCanonicalBinderMetadata = true)
    (term : Tm Head n) :
    (encodeTm headCodec term).hasCanonicalBinderMetadata = true := by
  induction term with
  | var index =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical]
  | const name =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeDeclName_canonical]
  | head head =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, headCanonical]
  | pi domain body domainIH bodyIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, firstIH, secondIH]
  | fst pair pairIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, pairIH]
  | snd pair pairIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, pairIH]
  | refl term termIH =>
      simp [encodeTm, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, termIH]

theorem encodeCtx_ground (headCodec : PartialCodec Head Pattern)
    (headGround : ∀ head, (headCodec.encode head).isGroundAt 0 = true)
    (context : Ctx Head n) :
    (encodeCtx headCodec context).isGroundAt 0 = true := by
  induction context with
  | nil => simp [encodeCtx, Pattern.isGroundAt, Pattern.isGroundListAt]
  | snoc context type contextIH =>
      simp [encodeCtx, Pattern.isGroundAt, Pattern.isGroundListAt,
        contextIH, encodeTm_ground headCodec headGround]

theorem encodeCtx_canonical (headCodec : PartialCodec Head Pattern)
    (headCanonical : ∀ head,
      (headCodec.encode head).hasCanonicalBinderMetadata = true)
    (context : Ctx Head n) :
    (encodeCtx headCodec context).hasCanonicalBinderMetadata = true := by
  induction context with
  | nil =>
      simp [encodeCtx, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | snoc context type contextIH =>
      simp [encodeCtx, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, contextIH,
        encodeTm_canonical headCodec headCanonical]

theorem encodeNat_argumentValid (value : Nat) :
    argumentValidAt 0 (encodeNat value) = true := by
  simp [argumentValidAt, encodeNat_ground, encodeNat_canonical]

theorem encodeLevel_argumentValid (level : LevelExpr) :
    argumentValidAt 0 (encodeLevel level) = true := by
  simp [argumentValidAt, encodeLevel_ground, encodeLevel_canonical]

theorem encodeTowerHead_argumentValid (head : Tower.Head) :
    argumentValidAt 0 (encodeTowerHead head) = true := by
  simp [argumentValidAt, encodeTowerHead_ground,
    encodeTowerHead_canonical]

theorem encodeTowerTm_argumentValid (term : Tower.Tm n) :
    argumentValidAt 0 (encodeTm towerHeadCodec term) = true := by
  simp [argumentValidAt,
    encodeTm_ground towerHeadCodec encodeTowerHead_ground,
    encodeTm_canonical towerHeadCodec encodeTowerHead_canonical]

theorem encodeTowerCtx_argumentValid (context : Tower.Ctx n) :
    argumentValidAt 0 (encodeCtx towerHeadCodec context) = true := by
  simp [argumentValidAt,
    encodeCtx_ground towerHeadCodec encodeTowerHead_ground,
    encodeCtx_canonical towerHeadCodec encodeTowerHead_canonical]

theorem encodeTowerTypingClaim_argumentValid
    (claim : TypingClaim Tower.Head) :
    argumentValidAt 0 (encodeTypingClaim towerHeadCodec claim) = true := by
  cases claim with
  | mk arity context subject type =>
      simp [argumentValidAt, encodeTypingClaim, Pattern.isGroundAt,
        Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_ground,
        encodeNat_canonical,
        encodeCtx_ground towerHeadCodec encodeTowerHead_ground,
        encodeCtx_canonical towerHeadCodec encodeTowerHead_canonical,
        encodeTm_ground towerHeadCodec encodeTowerHead_ground,
        encodeTm_canonical towerHeadCodec encodeTowerHead_canonical]

/-! ## Positive and negative controls -/

def legacyGroundClaim : TypingClaim Tower.Head where
  arity := 0
  context := .nil
  subject := .head .legacyGround
  type := .head (.sort Tower.zero)

theorem legacyGroundClaim_round_trip :
    decodeTypingClaim? towerHeadCodec
        (encodeTypingClaim towerHeadCodec legacyGroundClaim) =
      some legacyGroundClaim := by
  exact decodeTypingClaim?_encodeTypingClaim towerHeadCodec legacyGroundClaim

/-- A variable encoded from a one-variable term cannot be decoded at arity
zero.  Scope is checked by construction rather than trusted metadata. -/
theorem outOfScopeVariable_rejected :
    decodeTm? towerHeadCodec 0
        (encodeTm towerHeadCodec
          (Tm.var (Head := Tower.Head) (0 : Fin 1))) = none := by
  rfl

/-- A one-entry context cannot be relabeled as an empty context. -/
theorem mismatchedContextArity_rejected :
    decodeCtx? towerHeadCodec 0
        (encodeCtx towerHeadCodec
          (Ctx.snoc Ctx.nil
            (Tm.head (Head := Tower.Head) .legacyGround))) = none := by
  rfl

/-- Exact decoding makes the full dependent claim encoder injective. -/
theorem encodeTowerTypingClaim_injective :
    Function.Injective (encodeTypingClaim towerHeadCodec) :=
  towerTypingClaimCodec.encode_injective

#print axioms legacyGroundClaim_round_trip
#print axioms mismatchedContextArity_rejected
#print axioms encodeTowerTypingClaim_injective

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
