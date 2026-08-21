import Mettapedia.GSLT.LanguageDef.FiniteSupportBitVecCompilation

/-!
# Certified finite-apartness compilation to a dense bit matrix

A locally finite native type theory can present an unordered apartness relation
over a generated key inventory.  This module compiles that relation to one
packed support row per dense key slot.  Runtime checks then use only bounded
slot lookup and bit membership.

Admission is fail-closed for relation endpoints and for the two supports being
compared.  The refinement theorem proves that the dense matrix accepts exactly
the same pairs as the source relation.  The construction assumes no particular
meaning for keys or apartness.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteApartnessMatrixCompilation

open FiniteEnvironmentCompilation
open FiniteSupportBitVecCompilation

universe uKey

variable {Key : Type uKey} [DecidableEq Key]

/-- Source apartness is an unordered finite relation. -/
def pairAllowed? (pairs : List (Key × Key)) (left right : Key) : Bool :=
  pairs.contains (left, right) || pairs.contains (right, left)

/-- Relation-lifted apartness of two finite supports.  This is stronger than
ordinary set disjointness: every cross-pair must be licensed by the active
relation. -/
def SupportsApart (pairs : List (Key × Key))
    (left right : List Key) : Prop :=
  ∀ leftKey ∈ left, ∀ rightKey ∈ right,
    pairAllowed? pairs leftKey rightKey = true

/-- All keys mentioned by a source apartness declaration. -/
def pairKeys (pairs : List (Key × Key)) : List Key :=
  pairs.flatMap fun pair => [pair.1, pair.2]

/-- Executable admission for relation endpoints. -/
def pairsSupported? (inventory : Inventory Key)
    (pairs : List (Key × Key)) : Bool :=
  supported? inventory (pairKeys pairs)

/-- Apartness is irreflexive.  The generated matrix is symmetric by
construction, while self-pairs are rejected at admission just as they are by
the native relational proof runtime. -/
def pairsIrreflexive? (pairs : List (Key × Key)) : Bool :=
  pairs.all fun pair => decide (pair.1 ≠ pair.2)

/-- Complete local admission predicate for a bounded apartness relation. -/
def relationAdmitted? (inventory : Inventory Key)
    (pairs : List (Key × Key)) : Bool :=
  pairsSupported? inventory pairs && pairsIrreflexive? pairs

/-- The source keys allowed to occur opposite one fixed key. -/
def partners (inventory : Inventory Key) (pairs : List (Key × Key))
    (left : Key) : List Key :=
  inventory.keys.filter fun right => pairAllowed? pairs left right

/-- A dense apartness carrier has one inventory-width row per inventory slot. -/
abbrev PackedApartnessMatrix (inventory : Inventory Key) :=
  inventory.Slot → PackedSupport inventory

/-- Compile the unordered source relation into symmetric dense rows. -/
def encodeMatrix (inventory : Inventory Key) (pairs : List (Key × Key)) :
    PackedApartnessMatrix inventory :=
  fun left => encode inventory (partners inventory pairs (inventory.reify left))

/-- Query the dense matrix through source keys.  Undeclared keys fail closed. -/
def decodePair (inventory : Inventory Key)
    (matrix : PackedApartnessMatrix inventory) (left right : Key) : Bool :=
  match inventory.resolve? left with
  | none => false
  | some leftSlot => decodeMember inventory (matrix leftSlot) right

/-- Every generated matrix row is supported by construction. -/
theorem partners_supported
    (inventory : Inventory Key) (pairs : List (Key × Key)) (left : Key) :
    supported? inventory (partners inventory pairs left) = true := by
  rw [supported?_eq_true_iff]
  intro key member
  exact (List.mem_filter.mp member).1

/-- One compiled matrix lookup is exactly the source relation whenever both
query keys belong to the generated inventory. -/
theorem decodePair_encodeMatrix
    (inventory : Inventory Key) (pairs : List (Key × Key))
    (left right : Key) (leftDeclared : left ∈ inventory.keys)
    (rightDeclared : right ∈ inventory.keys) :
    decodePair inventory (encodeMatrix inventory pairs) left right =
      pairAllowed? pairs left right := by
  obtain ⟨leftSlot, selected⟩ :=
    (inventory.exists_resolve?_eq_some_iff left).2 leftDeclared
  have reified :=
    (inventory.resolve?_eq_some_iff left leftSlot).1 selected
  simp only [decodePair, selected, encodeMatrix]
  rw [decodeMember_encode inventory
    (partners inventory pairs (inventory.reify leftSlot))
    (partners_supported inventory pairs (inventory.reify leftSlot)) right]
  rw [reified]
  simp [partners, List.contains_eq_mem, rightDeclared]

/-- Source observation for two finite supports. -/
def supportsApart? (pairs : List (Key × Key))
    (left right : List Key) : Bool :=
  left.all fun leftKey =>
    right.all fun rightKey => pairAllowed? pairs leftKey rightKey

/-- The executable source observation decides relation-lifted apartness. -/
theorem supportsApart?_eq_true_iff (pairs : List (Key × Key))
    (left right : List Key) :
    supportsApart? pairs left right = true ↔
      SupportsApart pairs left right := by
  simp [supportsApart?, SupportsApart]

/-- Dense-matrix observation for the same two supports. -/
def packedSupportsApart? (inventory : Inventory Key)
    (matrix : PackedApartnessMatrix inventory)
    (left right : List Key) : Bool :=
  left.all fun leftKey =>
    right.all fun rightKey => decodePair inventory matrix leftKey rightKey

/-- Packed subset test used by the native runtime: every set bit in
`candidate` must also occur in `allowed`.  The C loop computes the equivalent
word operation `candidate & ~allowed == 0`. -/
def packedCoveredBy? (inventory : Inventory Key)
    (candidate allowed : PackedSupport inventory) : Bool :=
  candidate &&& ~~~allowed == BitVec.zero inventory.keys.length

/-- Pointwise meaning of the packed row-inclusion algorithm. -/
def PackedSupportsApart (inventory : Inventory Key)
    (matrix : PackedApartnessMatrix inventory)
    (left right : PackedSupport inventory) : Prop :=
  ∀ leftSlot : inventory.Slot,
    left.getLsbD leftSlot.val = true →
      ∀ rightSlot : inventory.Slot,
        right.getLsbD rightSlot.val = true →
          (matrix leftSlot).getLsbD rightSlot.val = true

/-- Executable dense support/apartness test matching the native runtime: scan
the set bits of the left support and require the complete right support to be
covered by each selected matrix row. -/
def packedSupportsApartBits? (inventory : Inventory Key)
    (matrix : PackedApartnessMatrix inventory)
    (left right : PackedSupport inventory) : Bool :=
  (List.finRange inventory.keys.length).all fun leftSlot =>
    !left.getLsbD leftSlot.val ||
      packedCoveredBy? inventory right (matrix leftSlot)

omit [DecidableEq Key] in
/-- Packed row inclusion is exactly pointwise bit inclusion. -/
theorem packedCoveredBy?_eq_true_iff (inventory : Inventory Key)
    (candidate allowed : PackedSupport inventory) :
    packedCoveredBy? inventory candidate allowed = true ↔
      ∀ slot : inventory.Slot,
        candidate.getLsbD slot.val = true →
          allowed.getLsbD slot.val = true := by
  rw [packedCoveredBy?, beq_iff_eq]
  constructor
  · intro zero slot candidateSet
    have observed := congrArg
      (fun bits : PackedSupport inventory => bits.getLsbD slot.val) zero
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not] at observed
    simp [slot.isLt, candidateSet] at observed
    simpa [BitVec.getLsbD_eq_getElem slot.isLt] using observed
  · intro covered
    apply BitVec.eq_of_getLsbD_eq
    intro index inRange
    let slot : inventory.Slot := ⟨index, inRange⟩
    change
      (candidate &&& ~~~allowed).getLsbD slot.val =
        (BitVec.zero inventory.keys.length).getLsbD slot.val
    rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
    by_cases candidateSet : candidate.getLsbD slot.val = true
    · have allowedSet := covered slot candidateSet
      simp [slot.isLt, candidateSet, allowedSet]
    · have candidateClear := Bool.eq_false_of_not_eq_true candidateSet
      rw [BitVec.getLsbD_eq_getElem slot.isLt] at candidateClear ⊢
      simp [candidateClear]

omit [DecidableEq Key] in
/-- The executable row-inclusion loop decides its pointwise meaning. -/
theorem packedSupportsApartBits?_eq_true_iff
    (inventory : Inventory Key)
    (matrix : PackedApartnessMatrix inventory)
    (left right : PackedSupport inventory) :
    packedSupportsApartBits? inventory matrix left right = true ↔
      PackedSupportsApart inventory matrix left right := by
  rw [packedSupportsApartBits?, List.all_eq_true]
  constructor
  · intro checked leftSlot leftSet rightSlot rightSet
    have row := checked leftSlot (List.mem_finRange leftSlot)
    rw [Bool.or_eq_true] at row
    rcases row with leftClear | covered
    · rw [BitVec.getLsbD_eq_getElem leftSlot.isLt] at leftSet
      rw [BitVec.getLsbD_eq_getElem leftSlot.isLt] at leftClear
      simp [leftSet] at leftClear
    · exact
        (packedCoveredBy?_eq_true_iff inventory right (matrix leftSlot)).1
          covered rightSlot rightSet
  · intro apart leftSlot _
    by_cases leftSet : left.getLsbD leftSlot.val = true
    · rw [Bool.or_eq_true]
      exact Or.inr
        ((packedCoveredBy?_eq_true_iff inventory right (matrix leftSlot)).2
          (apart leftSlot leftSet))
    · have leftClear := Bool.eq_false_of_not_eq_true leftSet
      rw [Bool.or_eq_true, BitVec.getLsbD_eq_getElem leftSlot.isLt]
      rw [BitVec.getLsbD_eq_getElem leftSlot.isLt] at leftClear
      exact Or.inl (by simpa using leftClear)

/-- The matrix check is exact on admitted supports. -/
theorem packedSupportsApart?_encodeMatrix
    (inventory : Inventory Key) (pairs : List (Key × Key))
    (left right : List Key)
    (leftAccepted : supported? inventory left = true)
    (rightAccepted : supported? inventory right = true) :
    packedSupportsApart? inventory (encodeMatrix inventory pairs) left right =
      supportsApart? pairs left right := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro packed
    rw [packedSupportsApart?, List.all_eq_true] at packed
    rw [supportsApart?, List.all_eq_true]
    intro leftKey leftMember
    have leftDeclared :=
      (supported?_eq_true_iff inventory left).1
        leftAccepted leftKey leftMember
    have packedRow := packed leftKey leftMember
    rw [List.all_eq_true] at packedRow ⊢
    intro rightKey rightMember
    have rightDeclared :=
      (supported?_eq_true_iff inventory right).1
        rightAccepted rightKey rightMember
    simpa [decodePair_encodeMatrix inventory pairs leftKey rightKey
      leftDeclared rightDeclared] using packedRow rightKey rightMember
  · intro source
    rw [supportsApart?, List.all_eq_true] at source
    rw [packedSupportsApart?, List.all_eq_true]
    intro leftKey leftMember
    have leftDeclared :=
      (supported?_eq_true_iff inventory left).1
        leftAccepted leftKey leftMember
    have sourceRow := source leftKey leftMember
    rw [List.all_eq_true] at sourceRow ⊢
    intro rightKey rightMember
    have rightDeclared :=
      (supported?_eq_true_iff inventory right).1
        rightAccepted rightKey rightMember
    simpa [decodePair_encodeMatrix inventory pairs leftKey rightKey
      leftDeclared rightDeclared] using sourceRow rightKey rightMember

/-- The packed-support row-inclusion loop is exact for compiled supports and
the compiled symmetric relation.  This is the theorem corresponding to the
native loop over `right & ~apartness[left]`. -/
theorem packedSupportsApartBits?_encodeMatrix
    (inventory : Inventory Key) (pairs : List (Key × Key))
    (left right : List Key)
    (leftAccepted : supported? inventory left = true)
    (rightAccepted : supported? inventory right = true) :
    packedSupportsApartBits? inventory (encodeMatrix inventory pairs)
        (encode inventory left) (encode inventory right) =
      supportsApart? pairs left right := by
  rw [Bool.eq_iff_iff,
    packedSupportsApartBits?_eq_true_iff,
    supportsApart?_eq_true_iff]
  constructor
  · intro packed leftKey leftMember rightKey rightMember
    have leftDeclared :=
      (supported?_eq_true_iff inventory left).1
        leftAccepted leftKey leftMember
    have rightDeclared :=
      (supported?_eq_true_iff inventory right).1
        rightAccepted rightKey rightMember
    obtain ⟨leftSlot, leftSelected⟩ :=
      (inventory.exists_resolve?_eq_some_iff leftKey).2 leftDeclared
    obtain ⟨rightSlot, rightSelected⟩ :=
      (inventory.exists_resolve?_eq_some_iff rightKey).2 rightDeclared
    have leftReified :=
      (inventory.resolve?_eq_some_iff leftKey leftSlot).1 leftSelected
    have rightReified :=
      (inventory.resolve?_eq_some_iff rightKey rightSlot).1 rightSelected
    have leftSet :
        (encode inventory left).getLsbD leftSlot.val = true := by
      rw [encode_getLsbD, leftReified]
      simpa [List.contains_eq_mem] using leftMember
    have rightSet :
        (encode inventory right).getLsbD rightSlot.val = true := by
      rw [encode_getLsbD, rightReified]
      simpa [List.contains_eq_mem] using rightMember
    have matrixSet := packed leftSlot leftSet rightSlot rightSet
    have decoded :
        decodePair inventory (encodeMatrix inventory pairs)
            leftKey rightKey = true := by
      simpa [decodePair, leftSelected, decodeMember, rightSelected]
        using matrixSet
    rwa [decodePair_encodeMatrix inventory pairs leftKey rightKey
      leftDeclared rightDeclared] at decoded
  · intro source leftSlot leftSet rightSlot rightSet
    have leftMember : inventory.reify leftSlot ∈ left := by
      rw [encode_getLsbD] at leftSet
      simpa [List.contains_eq_mem] using leftSet
    have rightMember : inventory.reify rightSlot ∈ right := by
      rw [encode_getLsbD] at rightSet
      simpa [List.contains_eq_mem] using rightSet
    have relationSet := source (inventory.reify leftSlot) leftMember
      (inventory.reify rightSlot) rightMember
    have decoded :
        decodePair inventory (encodeMatrix inventory pairs)
            (inventory.reify leftSlot) (inventory.reify rightSlot) = true := by
      rw [decodePair_encodeMatrix inventory pairs
        (inventory.reify leftSlot) (inventory.reify rightSlot)
        (List.get_mem inventory.keys leftSlot)
        (List.get_mem inventory.keys rightSlot)]
      exact relationSet
    simpa [decodePair, decodeMember] using decoded

/-- An admitted source relation retains the exact compiler result. -/
structure AdmittedApartness (inventory : Inventory Key) where
  pairs : List (Key × Key)
  matrix : PackedApartnessMatrix inventory
  compile_eq :
    (if relationAdmitted? inventory pairs then
        some (encodeMatrix inventory pairs)
      else none) = some matrix

/-- Fail-closed partial compiler for finite apartness declarations. -/
def compileMatrix? (inventory : Inventory Key) (pairs : List (Key × Key)) :
    Option (PackedApartnessMatrix inventory) :=
  if relationAdmitted? inventory pairs then some (encodeMatrix inventory pairs)
  else none

/-- Matrix compilation succeeds exactly when all endpoints are declared and
the source relation is irreflexive. -/
theorem compileMatrix?_isSome_eq_relationAdmitted?
    (inventory : Inventory Key) (pairs : List (Key × Key)) :
    (compileMatrix? inventory pairs).isSome =
      relationAdmitted? inventory pairs := by
  unfold compileMatrix?
  cases relationAdmitted? inventory pairs <;> rfl

/-- Package a successful finite-apartness admission. -/
def admitApartness (inventory : Inventory Key) (pairs : List (Key × Key)) :
    Option (AdmittedApartness inventory) :=
  match accepted : compileMatrix? inventory pairs with
  | none => none
  | some matrix => some { pairs, matrix, compile_eq := accepted }

/-- Dense apartness lowering as a composable computed realization.  Its
observation is bounded by the generated inventory, matching the runtime ABI. -/
def matrixRealization (inventory : Inventory Key) :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedApartness inventory)
      (PackedApartnessMatrix inventory)
      (inventory.Slot → inventory.Slot → Bool) where
  compile := fun _ admitted => admitted.matrix
  observeSource := fun _ admitted left right =>
    pairAllowed? admitted.pairs (inventory.reify left) (inventory.reify right)
  observeArtifact := fun _ matrix left right =>
    (matrix left).getLsbD right.val
  adequate := by
    intro _ admitted
    have admittedRelation :
        relationAdmitted? inventory admitted.pairs = true := by
      have compiledSome :
          (compileMatrix? inventory admitted.pairs).isSome = true := by
        unfold compileMatrix?
        rw [admitted.compile_eq]
        rfl
      rwa [compileMatrix?_isSome_eq_relationAdmitted?] at compiledSome
    have accepted : pairsSupported? inventory admitted.pairs = true := by
      simpa [relationAdmitted?] using
        (show pairsSupported? inventory admitted.pairs = true ∧
            pairsIrreflexive? admitted.pairs = true by
          simpa [relationAdmitted?] using admittedRelation).1
    have matrixEq : admitted.matrix = encodeMatrix inventory admitted.pairs := by
      have compileEq := admitted.compile_eq
      rw [admittedRelation] at compileEq
      exact Option.some.inj compileEq.symm
    funext left right
    have rightDeclared : inventory.reify right ∈ inventory.keys :=
      List.get_mem inventory.keys right
    rw [matrixEq]
    unfold encodeMatrix
    rw [encode_getLsbD]
    simp [partners, List.contains_eq_mem, rightDeclared]

/-! ## Independent witnesses and rejection boundary -/

private inductive ProofName where
  | x | y | z
deriving DecidableEq

private def proofInventory : Inventory ProofName where
  keys := [.x, .y, .z]
  nodup := by decide

/-- A proof-like symmetric apartness relation compiles and is observed in both
orientations without storing both source pairs. -/
example :
    let matrix := encodeMatrix proofInventory [(.x, .y), (.y, .z)]
    decodePair proofInventory matrix .y .x = true ∧
      decodePair proofInventory matrix .x .z = false := by
  decide

/-- Packed supports use the same row-inclusion check as the native runtime. -/
example :
    let pairs : List (ProofName × ProofName) := [(.x, .y), (.y, .z)]
    let matrix := encodeMatrix proofInventory pairs
    packedSupportsApartBits? proofInventory matrix
        (encode proofInventory [.x]) (encode proofInventory [.y]) = true ∧
      packedSupportsApartBits? proofInventory matrix
        (encode proofInventory [.x]) (encode proofInventory [.z]) = false := by
  decide

/-- Ordinary support disjointness does not imply declared apartness. -/
example :
    SupportsDisjoint ([.x] : List ProofName) [.z] ∧
      ¬ SupportsApart ([(.x, .y)] : List (ProofName × ProofName))
        [.x] [.z] := by
  simp [SupportsDisjoint, SupportsApart, pairAllowed?]

private inductive LexicalClass where
  | digit | letter | delimiter | whitespace
deriving DecidableEq

private def lexicalInventory : Inventory LexicalClass where
  keys := [.digit, .letter, .delimiter, .whitespace]
  nodup := by decide

/-- A parser-like character-class exclusion table uses the same matrix
compiler and support theorem. -/
example :
    let pairs : List (LexicalClass × LexicalClass) :=
      [(.letter, .delimiter), (.digit, .whitespace)]
    packedSupportsApart? lexicalInventory
        (encodeMatrix lexicalInventory pairs)
        [.letter, .digit] [.delimiter, .whitespace] = false := by
  decide

private inductive Resource where
  | channelA | channelB | lockA | lockB
deriving DecidableEq

private def resourceInventory : Inventory Resource where
  keys := [.channelA, .channelB, .lockA, .lockB]
  nodup := by decide

/-- A graph/process-like independence relation supplies a second structurally
unrelated positive use. -/
example :
    let pairs : List (Resource × Resource) :=
      [(.channelA, .lockB), (.channelB, .lockA)]
    supportsApart? pairs [.channelA, .channelB] [.lockB] = false ∧
      decodePair resourceInventory (encodeMatrix resourceInventory pairs)
        .channelA .lockB = true := by
  decide

private inductive ExtendedKey where
  | known | absent
deriving DecidableEq

private def restrictedInventory : Inventory ExtendedKey where
  keys := [.known]
  nodup := by decide

/-- A relation mentioning a key absent from the generated inventory is
rejected before a matrix is retained. -/
example :
    (compileMatrix? restrictedInventory [(.known, .absent)]).isSome = false := by
  decide

/-- A self-pair violates irreflexivity even when its endpoint is declared. -/
example :
    (compileMatrix? restrictedInventory [(.known, .known)]).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.FiniteApartnessMatrixCompilation
