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

/-- All keys mentioned by a source apartness declaration. -/
def pairKeys (pairs : List (Key × Key)) : List Key :=
  pairs.flatMap fun pair => [pair.1, pair.2]

/-- Executable admission for relation endpoints. -/
def pairsSupported? (inventory : Inventory Key)
    (pairs : List (Key × Key)) : Bool :=
  supported? inventory (pairKeys pairs)

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

/-- Dense-matrix observation for the same two supports. -/
def packedSupportsApart? (inventory : Inventory Key)
    (matrix : PackedApartnessMatrix inventory)
    (left right : List Key) : Bool :=
  left.all fun leftKey =>
    right.all fun rightKey => decodePair inventory matrix leftKey rightKey

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

/-- An admitted source relation retains the exact compiler result. -/
structure AdmittedApartness (inventory : Inventory Key) where
  pairs : List (Key × Key)
  matrix : PackedApartnessMatrix inventory
  compile_eq :
    (if pairsSupported? inventory pairs then some (encodeMatrix inventory pairs)
      else none) = some matrix

/-- Fail-closed partial compiler for finite apartness declarations. -/
def compileMatrix? (inventory : Inventory Key) (pairs : List (Key × Key)) :
    Option (PackedApartnessMatrix inventory) :=
  if pairsSupported? inventory pairs then some (encodeMatrix inventory pairs)
  else none

/-- Matrix compilation succeeds exactly when every declared endpoint belongs
to the local finite inventory. -/
theorem compileMatrix?_isSome_eq_pairsSupported?
    (inventory : Inventory Key) (pairs : List (Key × Key)) :
    (compileMatrix? inventory pairs).isSome = pairsSupported? inventory pairs := by
  unfold compileMatrix?
  cases pairsSupported? inventory pairs <;> rfl

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
    have accepted : pairsSupported? inventory admitted.pairs = true := by
      have compiledSome :
          (compileMatrix? inventory admitted.pairs).isSome = true := by
        unfold compileMatrix?
        rw [admitted.compile_eq]
        rfl
      rwa [compileMatrix?_isSome_eq_pairsSupported?] at compiledSome
    have matrixEq : admitted.matrix = encodeMatrix inventory admitted.pairs := by
      have compileEq := admitted.compile_eq
      rw [accepted] at compileEq
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

end Mettapedia.GSLT.LanguageDef.FiniteApartnessMatrixCompilation
