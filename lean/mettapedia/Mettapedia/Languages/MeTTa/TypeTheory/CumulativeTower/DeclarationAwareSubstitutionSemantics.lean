import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionLanguage
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.TypedSubstitution

/-!
# Independent first-order semantics for authored Prime substitution

The generic inference checker sees canonical first-order data, whereas the
intrinsic dependent presentation uses `Fin`-scoped terms.  This module places
an independently defined first-order term algebra between those two views.
Its variables are natural numbers, its binding operations are ordinary total
functions, and its encoding uses the same public canonical constructor tags as
the declaration-aware language.

The algebra is intentionally not a proof artifact.  It is the functional
semantic companion whose graph the authored weakening and substitution rules
must present.  Intrinsic scoping and typing are added only by subsequent
commuting theorems.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionSemantics

open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwarePatternCodec
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {Head : Type} {n : Nat}

/-! ## One reusable first-order binding carrier -/

/-- The binder-explicit first-order shadow shared by every intrinsic Prime
term.  Variables are deliberately unscoped here: scope is a property supplied
by a typed guest, not an assumption made by the generic operational layer. -/
inductive RawTm (Head : Type) where
  | var : Nat → RawTm Head
  | const : Lean.Name → RawTm Head
  | head : Head → RawTm Head
  | pi : RawTm Head → RawTm Head → RawTm Head
  | sigma : RawTm Head → RawTm Head → RawTm Head
  | id : RawTm Head → RawTm Head → RawTm Head → RawTm Head
  | lam : RawTm Head → RawTm Head
  | app : RawTm Head → RawTm Head → RawTm Head
  | pair : RawTm Head → RawTm Head → RawTm Head
  | fst : RawTm Head → RawTm Head
  | snd : RawTm Head → RawTm Head
  | refl : RawTm Head → RawTm Head
  deriving DecidableEq, Repr

/-- Forget intrinsic scope while preserving every constructor occurrence. -/
def erase : {n : Nat} → Tm Head n → RawTm Head
  | _, .var index => .var index.val
  | _, .const name => .const name
  | _, .head head => .head head
  | _, .pi domain body => .pi (erase domain) (erase body)
  | _, .sigma domain body => .sigma (erase domain) (erase body)
  | _, .id type left right => .id (erase type) (erase left) (erase right)
  | _, .lam body => .lam (erase body)
  | _, .app function argument => .app (erase function) (erase argument)
  | _, .pair first second => .pair (erase first) (erase second)
  | _, .fst pair => .fst (erase pair)
  | _, .snd pair => .snd (erase pair)
  | _, .refl term => .refl (erase term)

/-- Canonical first-order encoding, defined independently of intrinsic term
encoding. -/
def encode (headCodec : PartialCodec Head Pattern) : RawTm Head → Pattern
  | .var index => .apply "prime-tm-var" [encodeNat index]
  | .const name => .apply "prime-tm-const" [encodeDeclName name]
  | .head head => .apply "prime-tm-head" [headCodec.encode head]
  | .pi domain body =>
      .apply "prime-tm-pi" [encode headCodec domain, encode headCodec body]
  | .sigma domain body =>
      .apply "prime-tm-sigma" [encode headCodec domain, encode headCodec body]
  | .id type left right =>
      .apply "prime-tm-id"
        [encode headCodec type, encode headCodec left, encode headCodec right]
  | .lam body => .apply "prime-tm-lam" [encode headCodec body]
  | .app function argument =>
      .apply "prime-tm-app"
        [encode headCodec function, encode headCodec argument]
  | .pair first second =>
      .apply "prime-tm-pair"
        [encode headCodec first, encode headCodec second]
  | .fst pair => .apply "prime-tm-fst" [encode headCodec pair]
  | .snd pair => .apply "prime-tm-snd" [encode headCodec pair]
  | .refl term => .apply "prime-tm-refl" [encode headCodec term]

/-- Erasure followed by the independent encoder is exactly the established
canonical intrinsic encoder. -/
@[simp] theorem encode_erase
    (headCodec : PartialCodec Head Pattern) (term : Tm Head n) :
    encode headCodec (erase term) = encodeTm headCodec term := by
  induction term with
  | var index => simp [erase, encode, encodeTm]
  | const name => simp [erase, encode, encodeTm]
  | head head => simp [erase, encode, encodeTm]
  | pi domain body domainIH bodyIH =>
      simp [erase, encode, encodeTm, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [erase, encode, encodeTm, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [erase, encode, encodeTm, typeIH, leftIH, rightIH]
  | lam body bodyIH => simp [erase, encode, encodeTm, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [erase, encode, encodeTm, functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [erase, encode, encodeTm, firstIH, secondIH]
  | fst pair pairIH => simp [erase, encode, encodeTm, pairIH]
  | snd pair pairIH => simp [erase, encode, encodeTm, pairIH]
  | refl term termIH => simp [erase, encode, encodeTm, termIH]

/-- Canonical encoding of a first-order term is closed whenever the chosen
head encoding is closed. -/
theorem encode_ground (headCodec : PartialCodec Head Pattern)
    (headGround : ∀ head, (headCodec.encode head).isGroundAt 0 = true)
    (term : RawTm Head) :
    (encode headCodec term).isGroundAt 0 = true := by
  induction term with
  | var index =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeNat_ground]
  | const name =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeDeclName_ground]
  | head head =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt, headGround]
  | pi domain body domainIH bodyIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
        typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
        functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt,
        firstIH, secondIH]
  | fst pair pairIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt, pairIH]
  | snd pair pairIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt, pairIH]
  | refl term termIH =>
      simp [encode, Pattern.isGroundAt, Pattern.isGroundListAt, termIH]

/-- Canonical encoding introduces no generic binder metadata whenever the
chosen head encoding introduces none. -/
theorem encode_canonical (headCodec : PartialCodec Head Pattern)
    (headCanonical : ∀ head,
      (headCodec.encode head).hasCanonicalBinderMetadata = true)
    (term : RawTm Head) :
    (encode headCodec term).hasCanonicalBinderMetadata = true := by
  induction term with
  | var index =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical]
  | const name =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeDeclName_canonical]
  | head head =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, headCanonical]
  | pi domain body domainIH bodyIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, firstIH, secondIH]
  | fst pair pairIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, pairIH]
  | snd pair pairIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, pairIH]
  | refl term termIH =>
      simp [encode, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, termIH]

theorem encode_argumentValid (term : RawTm Tower.Head) :
    Mettapedia.GSLT.LanguageDef.InferenceChecker.argumentValidAt 0
      (encode towerHeadCodec term) = true := by
  simp [Mettapedia.GSLT.LanguageDef.InferenceChecker.argumentValidAt,
    encode_ground towerHeadCodec encodeTowerHead_ground,
    encode_canonical towerHeadCodec encodeTowerHead_canonical]

/-! ## Total binding operations -/

/-- Insert one variable at `cutoff`.  Indices below the cutoff are unchanged;
all remaining indices move one place outward. -/
def weakenAt (cutoff : Nat) : RawTm Head → RawTm Head
  | .var index =>
      if index < cutoff then .var index else .var (index + 1)
  | .const name => .const name
  | .head head => .head head
  | .pi domain body =>
      .pi (weakenAt cutoff domain) (weakenAt (cutoff + 1) body)
  | .sigma domain body =>
      .sigma (weakenAt cutoff domain) (weakenAt (cutoff + 1) body)
  | .id type left right =>
      .id (weakenAt cutoff type) (weakenAt cutoff left)
        (weakenAt cutoff right)
  | .lam body => .lam (weakenAt (cutoff + 1) body)
  | .app function argument =>
      .app (weakenAt cutoff function) (weakenAt cutoff argument)
  | .pair first second =>
      .pair (weakenAt cutoff first) (weakenAt cutoff second)
  | .fst pair => .fst (weakenAt cutoff pair)
  | .snd pair => .snd (weakenAt cutoff pair)
  | .refl term => .refl (weakenAt cutoff term)

/-- Remove `index` and replace its occurrence by `replacement`.  Variables
above the removed position move one place inward.  Crossing a binder both
lifts the replacement and shifts the selected index. -/
def substituteAt (index : Nat) (replacement : RawTm Head) :
    RawTm Head → RawTm Head
  | .var variableIndex =>
      if variableIndex = index then replacement
      else if variableIndex < index then .var variableIndex
      else .var (variableIndex - 1)
  | .const name => .const name
  | .head head => .head head
  | .pi domain body =>
      .pi (substituteAt index replacement domain)
        (substituteAt (index + 1) (weakenAt 0 replacement) body)
  | .sigma domain body =>
      .sigma (substituteAt index replacement domain)
        (substituteAt (index + 1) (weakenAt 0 replacement) body)
  | .id type left right =>
      .id (substituteAt index replacement type)
        (substituteAt index replacement left)
        (substituteAt index replacement right)
  | .lam body =>
      .lam (substituteAt (index + 1) (weakenAt 0 replacement) body)
  | .app function argument =>
      .app (substituteAt index replacement function)
        (substituteAt index replacement argument)
  | .pair first second =>
      .pair (substituteAt index replacement first)
        (substituteAt index replacement second)
  | .fst pair => .fst (substituteAt index replacement pair)
  | .snd pair => .snd (substituteAt index replacement pair)
  | .refl term => .refl (substituteAt index replacement term)

/-- The independently defined root-beta function. -/
def rootBeta (body argument : RawTm Head) : RawTm Head :=
  substituteAt 0 argument body

/-! ## Elementary discriminating laws -/

@[simp] theorem weakenAt_var_below {index cutoff : Nat}
    (below : index < cutoff) :
    weakenAt (Head := Head) cutoff (.var index) = .var index := by
  simp [weakenAt, below]

@[simp] theorem weakenAt_var_atOrAbove {index cutoff : Nat}
    (notBelow : ¬ index < cutoff) :
    weakenAt (Head := Head) cutoff (.var index) = .var (index + 1) := by
  simp [weakenAt, notBelow]

@[simp] theorem substituteAt_var_equal (index : Nat)
    (replacement : RawTm Head) :
    substituteAt index replacement (.var index) = replacement := by
  simp [substituteAt]

@[simp] theorem substituteAt_var_below {variableIndex index : Nat}
    (replacement : RawTm Head) (below : variableIndex < index) :
    substituteAt index replacement (.var variableIndex) = .var variableIndex := by
  have distinct : variableIndex ≠ index := Nat.ne_of_lt below
  simp [substituteAt, distinct, below]

@[simp] theorem substituteAt_var_above {variableIndex index : Nat}
    (replacement : RawTm Head) (above : index < variableIndex) :
    substituteAt index replacement (.var variableIndex) =
      .var (variableIndex - 1) := by
  have distinct : variableIndex ≠ index := Nat.ne_of_gt above
  have notBelow : ¬ variableIndex < index :=
    Nat.not_lt.mpr (Nat.le_of_lt above)
  simp [substituteAt, distinct, notBelow]

/-- Structural equality is not occurrence identity: the functional binding
semantics preserves duplicate constructor occurrences even when their payloads
are equal. -/
theorem duplicate_pair_is_not_deduplicated (term : RawTm Head) :
    substituteAt 0 (.var 0) (.pair term term) =
      .pair (substituteAt 0 (.var 0) term)
        (substituteAt 0 (.var 0) term) := by
  rfl

/-- A variable above the removed position cannot retain its old index. -/
theorem removal_changes_successor (replacement : RawTm Head) (index : Nat) :
    substituteAt index replacement (.var (index + 1)) = .var index := by
  simp [substituteAt]

/-! ## Axiom audit -/

#print axioms encode_erase
#print axioms encode_ground
#print axioms encode_canonical
#print axioms encode_argumentValid
#print axioms weakenAt_var_below
#print axioms weakenAt_var_atOrAbove
#print axioms substituteAt_var_equal
#print axioms substituteAt_var_below
#print axioms substituteAt_var_above
#print axioms duplicate_pair_is_not_deduplicated
#print axioms removal_changes_successor

end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.DeclarationAwareSubstitutionSemantics
