import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalExecPrefixOrder
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Physical support distinguishes ground expression heads

MORK deliberately identifies alpha-equivalent executable patterns.  Ground
runtime rows have a stronger property: two expressions whose leading symbols
differ cannot share a physical support key.  This module isolates the small
compact-encoding fact needed by source-derived MM2 simulations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private theorem uint8ToNat_injective : Function.Injective UInt8.toNat := by
  intro left right equal
  calc
    left = UInt8.ofNat left.toNat := UInt8.ofNat_toNat.symm
    _ = UInt8.ofNat right.toNat := congrArg UInt8.ofNat equal
    _ = right := UInt8.ofNat_toNat

private theorem map_uint8ToNat_injective :
    Function.Injective (List.map UInt8.toNat) := by
  intro left right equal
  induction left generalizing right with
  | nil => simpa using equal
  | cons head tail induction =>
      cases right with
      | nil => simp at equal
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at equal
          exact congrArg₂ List.cons
            (uint8ToNat_injective equal.1) (induction equal.2)

theorem morkUtf8NatBytes_injective :
    Function.Injective (fun name => (morkUtf8Bytes name).map UInt8.toNat) := by
  intro left right equal
  have bytesEqual : morkUtf8Bytes left = morkUtf8Bytes right :=
    map_uint8ToNat_injective equal
  have arraysEqual := congrArg List.toByteArray bytesEqual
  rw [morkUtf8Bytes_toByteArray, morkUtf8Bytes_toByteArray,
    String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray] at arraysEqual
  exact String.toByteArray_inj.mp arraysEqual

/-- A compact symbol is self-delimiting, so equal symbol prefixes force equal
symbol names even when followed by unrelated encoded suffixes. -/
theorem compactSymbolBytes_append_injective_left
    (left right : String) (leftRest rightRest : List Nat)
    (equal : compactSymbolBytes left ++ leftRest =
      compactSymbolBytes right ++ rightRest) :
    left = right := by
  let leftBytes := (morkUtf8Bytes left).map UInt8.toNat
  let rightBytes := (morkUtf8Bytes right).map UInt8.toNat
  have expanded :
      ((0xC0 + leftBytes.length) :: leftBytes) ++ leftRest =
        ((0xC0 + rightBytes.length) :: rightBytes) ++ rightRest := by
    simpa [compactSymbolBytes, leftBytes, rightBytes] using equal
  have tagEqual : 0xC0 + leftBytes.length = 0xC0 + rightBytes.length :=
    by simpa using congrArg List.head? expanded
  have lengthEqual : leftBytes.length = rightBytes.length := by
    omega
  have tailEqual : leftBytes ++ leftRest = rightBytes ++ rightRest := by
    exact List.cons.inj expanded |>.2
  have bytesEqual : leftBytes = rightBytes := by
    calc
      leftBytes = List.take leftBytes.length (leftBytes ++ leftRest) := by simp
      _ = List.take leftBytes.length (rightBytes ++ rightRest) :=
        congrArg (List.take leftBytes.length) tailEqual
      _ = rightBytes := by rw [lengthEqual]; simp
  exact morkUtf8NatBytes_injective bytesEqual

/-- Successful compact encoding of an expression with a symbolic head exposes
that self-delimiting head as an exact prefix. -/
theorem morkCompactKey_expression_symbol_prefix
    (head : String) (tail : List Atom) (key : List Nat)
    (arityBound : (tail.length + 1) < 64)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (keyExact :
      morkCompactKey? (.expression (.symbol head :: tail)) = some key) :
    ∃ suffix,
      key = (tail.length + 1) :: compactSymbolBytes head ++ suffix := by
  unfold morkCompactKey? at keyExact
  simp only [morkCompactEncodeAtom] at keyExact
  rw [if_pos (by simpa using arityBound)] at keyExact
  simp only [morkCompactEncodeAtom.encodeList] at keyExact
  rw [morkCompactEncodeAtom_symbol_exact [] head headPositive headBound]
    at keyExact
  cases tailExact : morkCompactEncodeAtom.encodeList [] tail with
  | none => simp [tailExact] at keyExact
  | some result =>
      rcases result with ⟨tailBytes, environment⟩
      simp only [tailExact, Option.map_some, Option.some.injEq] at keyExact
      subst key
      exact ⟨tailBytes, by simp [compactSymbolBytes]⟩

/-- Different symbolic heads are different physical MORK support identities.
The result covers both compactly encoded rows and abstract fallback rows. -/
theorem morkSupportKey_expression_symbol_head_ne
    (leftHead rightHead : String) (leftTail rightTail : List Atom)
    (leftArityBound : leftTail.length + 1 < 64)
    (rightArityBound : rightTail.length + 1 < 64)
    (leftHeadPositive : 0 < (morkUtf8Bytes leftHead).length)
    (rightHeadPositive : 0 < (morkUtf8Bytes rightHead).length)
    (leftHeadBound : (morkUtf8Bytes leftHead).length < 64)
    (rightHeadBound : (morkUtf8Bytes rightHead).length < 64)
    (different : leftHead ≠ rightHead) :
    morkSupportKey (.expression (.symbol leftHead :: leftTail)) ≠
      morkSupportKey (.expression (.symbol rightHead :: rightTail)) := by
  intro equal
  unfold morkSupportKey at equal
  cases leftExact :
      morkCompactKey? (.expression (.symbol leftHead :: leftTail)) with
  | none =>
      cases rightExact :
          morkCompactKey? (.expression (.symbol rightHead :: rightTail)) with
      | none =>
          simp only [leftExact, rightExact, MorkSupportKey.abstract.injEq,
            Atom.expression.injEq, List.cons.injEq] at equal
          exact different (Atom.symbol.inj equal.1)
      | some rightKey => simp [leftExact, rightExact] at equal
  | some leftKey =>
      cases rightExact :
          morkCompactKey? (.expression (.symbol rightHead :: rightTail)) with
      | none => simp [leftExact, rightExact] at equal
      | some rightKey =>
          simp only [leftExact, rightExact, MorkSupportKey.compact.injEq]
            at equal
          obtain ⟨leftSuffix, leftPrefix⟩ :=
            morkCompactKey_expression_symbol_prefix leftHead leftTail leftKey
              leftArityBound leftHeadPositive leftHeadBound leftExact
          obtain ⟨rightSuffix, rightPrefix⟩ :=
            morkCompactKey_expression_symbol_prefix rightHead rightTail rightKey
              rightArityBound rightHeadPositive rightHeadBound rightExact
          rw [leftPrefix, rightPrefix] at equal
          have tailsEqual :
              compactSymbolBytes leftHead ++ leftSuffix =
                compactSymbolBytes rightHead ++ rightSuffix := by
            exact List.cons.inj equal |>.2
          exact different
            (compactSymbolBytes_append_injective_left leftHead rightHead
              leftSuffix rightSuffix tailsEqual)

/-- Different nonempty bounded symbolic heads remain physically distinct even
when either expression is too wide for compact encoding.  Successful compact
encoding supplies the missing arity bounds; failed encoding falls back to the
exact abstract atom. -/
theorem morkSupportKey_expression_symbol_head_ne_any_arity
    (leftHead rightHead : String) (leftTail rightTail : List Atom)
    (leftHeadPositive : 0 < (morkUtf8Bytes leftHead).length)
    (rightHeadPositive : 0 < (morkUtf8Bytes rightHead).length)
    (leftHeadBound : (morkUtf8Bytes leftHead).length < 64)
    (rightHeadBound : (morkUtf8Bytes rightHead).length < 64)
    (different : leftHead ≠ rightHead) :
    morkSupportKey (.expression (.symbol leftHead :: leftTail)) ≠
      morkSupportKey (.expression (.symbol rightHead :: rightTail)) := by
  intro keysEqual
  have originalKeysEqual := keysEqual
  unfold morkSupportKey at keysEqual
  cases leftExact :
      morkCompactKey? (.expression (.symbol leftHead :: leftTail)) with
  | none =>
      cases rightExact :
          morkCompactKey? (.expression (.symbol rightHead :: rightTail)) with
      | none =>
          simp only [leftExact, rightExact, MorkSupportKey.abstract.injEq,
            Atom.expression.injEq, List.cons.injEq] at keysEqual
          exact different (Atom.symbol.inj keysEqual.1)
      | some rightKey => simp [leftExact, rightExact] at keysEqual
  | some leftKey =>
      cases rightExact :
          morkCompactKey? (.expression (.symbol rightHead :: rightTail)) with
      | none => simp [leftExact, rightExact] at keysEqual
      | some rightKey =>
          have leftArity : leftTail.length + 1 < 64 := by
            unfold morkCompactKey? at leftExact
            simp only [morkCompactEncodeAtom] at leftExact
            split at leftExact
            · assumption
            · simp at leftExact
          have rightArity : rightTail.length + 1 < 64 := by
            unfold morkCompactKey? at rightExact
            simp only [morkCompactEncodeAtom] at rightExact
            split at rightExact
            · assumption
            · simp at rightExact
          exact (morkSupportKey_expression_symbol_head_ne leftHead rightHead
            leftTail rightTail leftArity rightArity leftHeadPositive
            rightHeadPositive leftHeadBound rightHeadBound different)
            originalKeysEqual

/-- Head separation transported across opaque expression tails.  Clients need
only expose the leading symbol of each row; the remaining payload is never
unfolded in downstream physical-support proofs. -/
theorem morkSupportKey_expression_symbol_head_ne_any_arity_of_shapes
    {left right : Atom} (leftHead rightHead : String)
    (leftShape : ∃ tail, left = .expression (.symbol leftHead :: tail))
    (rightShape : ∃ tail, right = .expression (.symbol rightHead :: tail))
    (leftHeadPositive : 0 < (morkUtf8Bytes leftHead).length)
    (rightHeadPositive : 0 < (morkUtf8Bytes rightHead).length)
    (leftHeadBound : (morkUtf8Bytes leftHead).length < 64)
    (rightHeadBound : (morkUtf8Bytes rightHead).length < 64)
    (different : leftHead ≠ rightHead) :
    morkSupportKey left ≠ morkSupportKey right := by
  rcases leftShape with ⟨leftTail, rfl⟩
  rcases rightShape with ⟨rightTail, rfl⟩
  exact morkSupportKey_expression_symbol_head_ne_any_arity
    leftHead rightHead leftTail rightTail leftHeadPositive rightHeadPositive
      leftHeadBound rightHeadBound different

/-- A non-executable symbolic row cannot share physical support identity with
any successfully decoded executable directive.  The directive body remains
opaque; successful decoding exposes only its outer `exec` constructor. -/
theorem morkSupportKey_expression_symbol_head_ne_supported_exec
    (rowHead : String) (rowTail : List Atom) {executable : Atom}
    {directive : SourceExecFact}
    (rowHeadPositive : 0 < (morkUtf8Bytes rowHead).length)
    (rowHeadBound : (morkUtf8Bytes rowHead).length < 64)
    (nonExecutable : rowHead ≠ "exec")
    (decoded : extractSupportedSourceExecFact executable = some directive) :
    morkSupportKey (.expression (.symbol rowHead :: rowTail)) ≠
      morkSupportKey executable := by
  obtain ⟨location, input, output, executableShape⟩ :=
    extractSupportedSourceExecFact_exec_shape decoded
  exact morkSupportKey_expression_symbol_head_ne_any_arity_of_shapes
    rowHead "exec" ⟨rowTail, rfl⟩
      ⟨[location, input, output], executableShape⟩
      rowHeadPositive (by decide) rowHeadBound (by decide) nonExecutable

/-- Executables at different two-symbol priority locations have distinct
physical identities whenever their compact location prefixes are strictly
ordered.  The rule bodies remain opaque, and the abstract-key fallback uses
only nominal location inequality. -/
theorem morkSupportKey_exec_two_symbol_location_ne
    (leftPriority leftName rightPriority rightName : String)
    (leftInput leftOutput rightInput rightOutput : Atom)
    (leftPriorityPositive : 0 < (morkUtf8Bytes leftPriority).length)
    (leftPriorityBound : (morkUtf8Bytes leftPriority).length < 64)
    (leftNamePositive : 0 < (morkUtf8Bytes leftName).length)
    (leftNameBound : (morkUtf8Bytes leftName).length < 64)
    (rightPriorityPositive : 0 < (morkUtf8Bytes rightPriority).length)
    (rightPriorityBound : (morkUtf8Bytes rightPriority).length < 64)
    (rightNamePositive : 0 < (morkUtf8Bytes rightName).length)
    (rightNameBound : (morkUtf8Bytes rightName).length < 64)
    (priorityDifferent : leftPriority ≠ rightPriority)
    (prefixOrdered : ∀ leftRest rightRest,
      lexLt
        ([4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes leftPriority ++
          compactSymbolBytes leftName ++ leftRest)
        ([4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes rightPriority ++
          compactSymbolBytes rightName ++ rightRest) = true) :
    morkSupportKey
        (.expression
          [.symbol "exec",
           .expression [.symbol leftPriority, .symbol leftName],
           leftInput, leftOutput]) ≠
      morkSupportKey
        (.expression
          [.symbol "exec",
           .expression [.symbol rightPriority, .symbol rightName],
           rightInput, rightOutput]) := by
  let leftAtom : Atom :=
    .expression
      [.symbol "exec",
       .expression [.symbol leftPriority, .symbol leftName],
       leftInput, leftOutput]
  let rightAtom : Atom :=
    .expression
      [.symbol "exec",
       .expression [.symbol rightPriority, .symbol rightName],
       rightInput, rightOutput]
  change morkSupportKey leftAtom ≠ morkSupportKey rightAtom
  intro keysEqual
  unfold morkSupportKey at keysEqual
  cases leftExact : morkCompactKey? leftAtom with
  | none =>
      cases rightExact : morkCompactKey? rightAtom with
      | none =>
          simp only [leftExact, rightExact, MorkSupportKey.abstract.injEq]
            at keysEqual
          have childrenEqual := Atom.expression.inj keysEqual
          have tailEqual := (List.cons.inj childrenEqual).2
          have locationEqual := (List.cons.inj tailEqual).1
          have locationChildrenEqual := Atom.expression.inj locationEqual
          have priorityEqual := (List.cons.inj locationChildrenEqual).1
          exact priorityDifferent (Atom.symbol.inj priorityEqual)
      | some rightKey => simp [leftExact, rightExact] at keysEqual
  | some leftKey =>
      cases rightExact : morkCompactKey? rightAtom with
      | none => simp [leftExact, rightExact] at keysEqual
      | some rightKey =>
          simp only [leftExact, rightExact, MorkSupportKey.compact.injEq]
            at keysEqual
          obtain ⟨leftRest, leftPrefix⟩ :=
            morkCompactExec_location_prefix leftPriority leftName leftInput
              leftOutput leftKey (by rfl) (by rfl) leftPriorityPositive
              leftPriorityBound leftNamePositive leftNameBound leftExact
          obtain ⟨rightRest, rightPrefix⟩ :=
            morkCompactExec_location_prefix rightPriority rightName rightInput
              rightOutput rightKey (by rfl) (by rfl) rightPriorityPositive
              rightPriorityBound rightNamePositive rightNameBound rightExact
          have ordered := prefixOrdered leftRest rightRest
          rw [← leftPrefix, ← rightPrefix, keysEqual, lexLt_irrefl] at ordered
          contradiction

/-- Location-prefix separation transported across opaque executable bodies.
Clients supply only the two outer executable shapes; neither body is unfolded
or retained in the theorem statement. -/
theorem morkSupportKey_exec_two_symbol_location_ne_of_shapes
    {left right : Atom}
    (leftPriority leftName rightPriority rightName : String)
    (leftShape : ∃ input output,
      left =
        .expression
          [.symbol "exec",
           .expression [.symbol leftPriority, .symbol leftName],
           input, output])
    (rightShape : ∃ input output,
      right =
        .expression
          [.symbol "exec",
           .expression [.symbol rightPriority, .symbol rightName],
           input, output])
    (leftPriorityPositive : 0 < (morkUtf8Bytes leftPriority).length)
    (leftPriorityBound : (morkUtf8Bytes leftPriority).length < 64)
    (leftNamePositive : 0 < (morkUtf8Bytes leftName).length)
    (leftNameBound : (morkUtf8Bytes leftName).length < 64)
    (rightPriorityPositive : 0 < (morkUtf8Bytes rightPriority).length)
    (rightPriorityBound : (morkUtf8Bytes rightPriority).length < 64)
    (rightNamePositive : 0 < (morkUtf8Bytes rightName).length)
    (rightNameBound : (morkUtf8Bytes rightName).length < 64)
    (priorityDifferent : leftPriority ≠ rightPriority)
    (prefixOrdered : ∀ leftRest rightRest,
      lexLt
        ([4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes leftPriority ++
          compactSymbolBytes leftName ++ leftRest)
        ([4, 196, 101, 120, 101, 99, 2] ++
          compactSymbolBytes rightPriority ++
          compactSymbolBytes rightName ++ rightRest) = true) :
    morkSupportKey left ≠ morkSupportKey right := by
  rcases leftShape with ⟨leftInput, leftOutput, rfl⟩
  rcases rightShape with ⟨rightInput, rightOutput, rfl⟩
  exact morkSupportKey_exec_two_symbol_location_ne
    leftPriority leftName rightPriority rightName leftInput leftOutput
      rightInput rightOutput leftPriorityPositive leftPriorityBound
      leftNamePositive leftNameBound rightPriorityPositive rightPriorityBound
      rightNamePositive rightNameBound priorityDifferent prefixOrdered

/-- Equality of physical support identities entails equality of the total
scheduler keys. -/
theorem totalMorkCompactKey_eq_of_morkSupportKey_eq
    {left right : Atom}
    (equal : morkSupportKey left = morkSupportKey right) :
    totalMorkCompactKey left = totalMorkCompactKey right := by
  unfold morkSupportKey at equal
  unfold totalMorkCompactKey
  cases leftExact : morkCompactKey? left <;>
    cases rightExact : morkCompactKey? right <;>
      simp [leftExact, rightExact] at equal ⊢
  · subst right
    rfl
  · exact equal

/-- A strict total scheduler order is also a proof that two atoms have
different physical support identities. -/
theorem morkSupportKey_ne_of_total_lexLt
    {left right : Atom}
    (ordered : lexLt (totalMorkCompactKey left)
      (totalMorkCompactKey right) = true) :
    morkSupportKey left ≠ morkSupportKey right := by
  intro equal
  have totalEqual := totalMorkCompactKey_eq_of_morkSupportKey_eq equal
  rw [totalEqual, lexLt_irrefl] at ordered
  contradiction

/-! ## Membership laws for physical support operations -/

theorem morkSupportContains_eq_true_of_mem
    {support : List Atom} {atom : Atom} (member : atom ∈ support) :
    morkSupportContains support atom = true := by
  unfold morkSupportContains morkSupportFind?
  rw [List.find?_isSome]
  exact ⟨atom, member, (sameMorkSupportAtom_eq_true_iff atom atom).2 rfl⟩

/-- Quotient-level presence yields exact nominal membership whenever the live
support reflects the requested physical key to that one representative. -/
theorem mem_of_morkSupportContains_of_key_reflection
    {support : List Atom} {atom : Atom}
    (present : morkSupportContains support atom = true)
    (reflects : ∀ candidate ∈ support,
      morkSupportKey candidate = morkSupportKey atom → candidate = atom) :
    atom ∈ support := by
  unfold morkSupportContains morkSupportFind? at present
  obtain ⟨candidate, candidateMember, matched⟩ :=
    List.find?_isSome.mp present
  have exactCandidate := reflects candidate candidateMember
    ((sameMorkSupportAtom_eq_true_iff candidate atom).1 matched)
  simpa [exactCandidate] using candidateMember

theorem mem_morkInsertSupport_of_mem
    {support : List Atom} {candidate inserted : Atom}
    (member : candidate ∈ support) :
    candidate ∈ morkInsertSupport support inserted := by
  unfold morkInsertSupport
  split
  · exact member
  · exact List.mem_append_left _ member

theorem mem_morkEraseSupport_of_mem_of_key_ne
    {support : List Atom} {candidate removed : Atom}
    (member : candidate ∈ support)
    (different : morkSupportKey candidate ≠ morkSupportKey removed) :
    candidate ∈ morkEraseSupport support removed := by
  apply List.mem_filter.mpr
  refine ⟨member, ?_⟩
  simp [sameMorkSupportAtom, different]

/-- An externally characterized erasure endpoint inherits exact membership
from a source representative with a different physical key. -/
theorem mem_of_eq_morkEraseSupport
    {before after : List Atom} {candidate selected : Atom}
    (afterExact : after = morkEraseSupport before selected)
    (member : candidate ∈ before)
    (different : morkSupportKey candidate ≠ morkSupportKey selected) :
    candidate ∈ after := by
  rw [afterExact]
  exact mem_morkEraseSupport_of_mem_of_key_ne member different

/-- An externally characterized erasure endpoint preserves any pointwise
support invariant. -/
theorem atomsWithin_of_eq_morkEraseSupport
    {property : Atom → Prop} {before after : List Atom} {selected : Atom}
    (afterExact : after = morkEraseSupport before selected)
    (within : AtomsWithin property before) :
    AtomsWithin property after := by
  rw [afterExact]
  exact morkEraseSupport_atomsWithin property before selected within

/-- Removing one selected key transports a source-wide freshness invariant
into exact representative reflection for any other distinguished key. -/
theorem morkEraseSupport_atomsWithin_key_reflects_of_fresh
    (support : List Atom) (selected distinguished : Atom)
    (fresh : ∀ row ∈ support, row ≠ selected →
      morkSupportKey row ≠ morkSupportKey distinguished) :
    AtomsWithin
      (fun row => morkSupportKey row = morkSupportKey distinguished →
        row = distinguished)
      (morkEraseSupport support selected) := by
  intro row liveMember keyEqual
  have sourceMember : row ∈ support := List.mem_of_mem_filter liveMember
  have notSelected : row ≠ selected := by
    intro equal
    subst row
    exact (not_mem_morkEraseSupport_self support selected) liveMember
  exact (fresh row sourceMember notSelected keyEqual).elim

theorem morkSupportContains_morkInsertSupport_self
    (support : List Atom) (atom : Atom) :
    morkSupportContains (morkInsertSupport support atom) atom = true := by
  unfold morkInsertSupport
  split
  · assumption
  · apply morkSupportContains_eq_true_of_mem
    simp

theorem morkSupportContains_morkInsertSupport_of_contains
    (support : List Atom) (inserted candidate : Atom)
    (present : morkSupportContains support candidate = true) :
    morkSupportContains (morkInsertSupport support inserted) candidate = true := by
  unfold morkInsertSupport
  split
  · exact present
  · unfold morkSupportContains morkSupportFind? at present ⊢
    obtain ⟨representative, representativeMember, matched⟩ :=
      List.find?_isSome.mp present
    exact List.find?_isSome.mpr
      ⟨representative, List.mem_append_left _ representativeMember, matched⟩

theorem morkSupportContains_morkEraseSupport_of_key_ne
    (support : List Atom) (removed candidate : Atom)
    (different : morkSupportKey candidate ≠ morkSupportKey removed)
    (present : morkSupportContains support candidate = true) :
    morkSupportContains (morkEraseSupport support removed) candidate = true := by
  unfold morkSupportContains morkSupportFind? at present ⊢
  obtain ⟨representative, representativeMember, matched⟩ :=
    List.find?_isSome.mp present
  have representativeKey :
      morkSupportKey representative = morkSupportKey candidate := by
    exact (sameMorkSupportAtom_eq_true_iff representative candidate).mp matched
  have survives : representative ∈ morkEraseSupport support removed := by
    apply List.mem_filter.mpr
    refine ⟨representativeMember, ?_⟩
    have keyNe : morkSupportKey representative ≠ morkSupportKey removed := by
      simpa [representativeKey] using different
    simp [sameMorkSupportAtom, keyNe]
  exact List.find?_isSome.mpr ⟨representative, survives, matched⟩

theorem morkSupportContains_morkUnionSupport_of_contains
    (support staged : List Atom) (candidate : Atom)
    (present : morkSupportContains support candidate = true) :
    morkSupportContains (morkUnionSupport support staged) candidate = true := by
  unfold morkUnionSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      exact induction (morkInsertSupport support head)
        (morkSupportContains_morkInsertSupport_of_contains support head candidate
          present)

/-- Every exact staged representative is present by physical identity after
union, even when an equivalent key was already resident. -/
theorem morkSupportContains_morkUnionSupport_of_mem_staged
    (support staged : List Atom) (candidate : Atom)
    (member : candidate ∈ staged) :
    morkSupportContains (morkUnionSupport support staged) candidate = true := by
  unfold morkUnionSupport
  induction staged generalizing support with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact morkSupportContains_morkUnionSupport_of_contains
          (morkInsertSupport support candidate) tail candidate
          (morkSupportContains_morkInsertSupport_self support candidate)
      · exact induction (morkInsertSupport support head) tailMember

theorem morkSupportContains_morkSubtractSupport_of_keys_ne
    (support staged : List Atom) (candidate : Atom)
    (present : morkSupportContains support candidate = true)
    (different : ∀ removed ∈ staged,
      morkSupportKey candidate ≠ morkSupportKey removed) :
    morkSupportContains (morkSubtractSupport support staged) candidate = true := by
  unfold morkSubtractSupport
  induction staged generalizing support with
  | nil => simpa
  | cons head tail induction =>
      simp only [List.foldl_cons]
      apply induction (morkEraseSupport support head)
      · exact morkSupportContains_morkEraseSupport_of_key_ne support head
          candidate (different head (by simp)) present
      · intro removed member
        exact different removed (by simp [member])

/-- Positive control: different runtime row heads stay physically distinct. -/
example :
    morkSupportKey
        (.expression [.symbol "mm-compressed-heap-proof", .symbol "owner"]) ≠
      morkSupportKey
        (.expression [.symbol "mm-compressed-step-pending", .symbol "owner"]) := by
  apply morkSupportKey_expression_symbol_head_ne <;> decide

/-- Negative control: identical rows have identical physical identity. -/
example (tail : List Atom) :
    morkSupportKey (.expression (.symbol "mm-compressed-stack" :: tail)) =
      morkSupportKey (.expression (.symbol "mm-compressed-stack" :: tail)) :=
  rfl

#print axioms morkUtf8NatBytes_injective
#print axioms compactSymbolBytes_append_injective_left
#print axioms morkCompactKey_expression_symbol_prefix
#print axioms morkSupportKey_expression_symbol_head_ne
#print axioms morkSupportKey_expression_symbol_head_ne_any_arity
#print axioms morkSupportKey_expression_symbol_head_ne_any_arity_of_shapes
#print axioms morkSupportKey_expression_symbol_head_ne_supported_exec
#print axioms morkSupportKey_exec_two_symbol_location_ne
#print axioms morkSupportKey_exec_two_symbol_location_ne_of_shapes
#print axioms morkSupportKey_ne_of_total_lexLt
#print axioms morkSupportContains_morkInsertSupport_self
#print axioms mem_of_morkSupportContains_of_key_reflection
#print axioms mem_morkEraseSupport_of_mem_of_key_ne
#print axioms mem_of_eq_morkEraseSupport
#print axioms atomsWithin_of_eq_morkEraseSupport
#print axioms morkEraseSupport_atomsWithin_key_reflects_of_fresh
#print axioms morkSupportContains_morkEraseSupport_of_key_ne
#print axioms morkSupportContains_morkUnionSupport_of_contains
#print axioms morkSupportContains_morkUnionSupport_of_mem_staged
#print axioms morkSupportContains_morkSubtractSupport_of_keys_ne

end Mettapedia.Languages.ProcessCalculi.MORK
