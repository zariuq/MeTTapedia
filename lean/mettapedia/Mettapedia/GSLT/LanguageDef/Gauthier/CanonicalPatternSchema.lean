import Mettapedia.GSLT.LanguageDef.Gauthier.RoleIndexedAntiUnification

/-!
# Canonical identities for role-indexed program schemas

An anti-unification hole carries the concrete pair of programs that created it.
That is the correct trusted memo key, but not a stable external identity: swapping
the two inputs changes every memo key even though it leaves the generalized
schema unchanged up to renaming.

This module gives schemas an executable first-occurrence identity.  A hole is
represented by its role and the position of its first occurrence in the
preorder hole stream.  Repeated holes therefore retain their sharing, while a
bijective renaming of concrete memo keys cannot change the exported schema.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema

open Mettapedia.GSLT.LanguageDef.GauthierE1
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification

/-- A name-independent schema descriptor.  The natural number is the position of
the hole's first occurrence in the preorder hole stream. -/
inductive SchemaPattern where
  | hole : HoleRole → Nat → SchemaPattern
  | node : Nat → List SchemaPattern → SchemaPattern
  deriving Repr

mutual

/-- Executable structural equality for canonical schema terms. -/
def schemaPatternDecEq : (left right : SchemaPattern) → Decidable (left = right)
  | .hole leftRole leftIndex, .hole rightRole rightIndex =>
      match decEq leftRole rightRole with
      | isFalse hrole => isFalse (fun equality =>
          hrole (SchemaPattern.hole.inj equality).1)
      | isTrue hrole =>
          match decEq leftIndex rightIndex with
          | isFalse hindex => isFalse (fun equality =>
              hindex (SchemaPattern.hole.inj equality).2)
          | isTrue hindex => isTrue (by simp [hrole, hindex])
  | .hole _ _, .node _ _ => isFalse (by intro equality; cases equality)
  | .node _ _, .hole _ _ => isFalse (by intro equality; cases equality)
  | .node leftOp leftChildren, .node rightOp rightChildren =>
      match decEq leftOp rightOp with
      | isFalse hop => isFalse (fun equality =>
          hop (SchemaPattern.node.inj equality).1)
      | isTrue hop =>
          match schemaPatternListDecEq leftChildren rightChildren with
          | isFalse hchildren => isFalse (fun equality =>
              hchildren (SchemaPattern.node.inj equality).2)
          | isTrue hchildren => isTrue (by simp [hop, hchildren])
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf; omega

/-- Executable structural equality for vectors of canonical schemas. -/
def schemaPatternListDecEq :
    (left right : List SchemaPattern) → Decidable (left = right)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro equality; cases equality)
  | _ :: _, [] => isFalse (by intro equality; cases equality)
  | left :: lefts, right :: rights =>
      match schemaPatternDecEq left right with
      | isFalse hhead => isFalse (fun equality =>
          hhead (List.cons.inj equality).1)
      | isTrue hhead =>
          match schemaPatternListDecEq lefts rights with
          | isFalse htail => isFalse (fun equality =>
              htail (List.cons.inj equality).2)
          | isTrue htail => isTrue (by simp [hhead, htail])
termination_by left right => sizeOf left + sizeOf right
decreasing_by all_goals simp_wf; omega

end


instance : DecidableEq SchemaPattern := schemaPatternDecEq

mutual

/-- Concrete memo keys in preorder occurrence order, including repetitions. -/
def holeOccurrences : Pattern → List HoleKey
  | .hole key => [key]
  | .node _ children => holeOccurrencesList children

/-- Concrete memo keys in a forest, in preorder occurrence order. -/
def holeOccurrencesList : List Pattern → List HoleKey
  | [] => []
  | head :: tail => holeOccurrences head ++ holeOccurrencesList tail

end

mutual

/-- Replace every concrete memo key by the position of its first occurrence in
one declared occurrence stream. -/
def schemaWith (occurrences : List HoleKey) : Pattern → SchemaPattern
  | .hole key => .hole key.role (occurrences.idxOf key)
  | .node op children => .node op (schemaListWith occurrences children)

/-- Name-erasure over a forest of patterns. -/
def schemaListWith (occurrences : List HoleKey) :
    List Pattern → List SchemaPattern
  | [] => []
  | head :: tail =>
      schemaWith occurrences head :: schemaListWith occurrences tail

end


@[simp] theorem schemaListWith_length (occurrences : List HoleKey)
    (patterns : List Pattern) :
    (schemaListWith occurrences patterns).length = patterns.length := by
  induction patterns with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [schemaListWith, List.length_cons, inductionHypothesis]

/-- Executable canonical identity of a role-indexed pattern. -/
def canonicalSchema (pattern : Pattern) : SchemaPattern :=
  schemaWith (holeOccurrences pattern) pattern

/-- Renaming concrete keys maps the complete occurrence stream pointwise. -/
theorem holeOccurrences_renameHoles (rename : HoleKey → HoleKey)
    (pattern : Pattern) :
    holeOccurrences (renameHoles rename pattern) =
      (holeOccurrences pattern).map rename := by
  exact Pattern.rec
    (motive_1 := fun pattern =>
      holeOccurrences (renameHoles rename pattern) =
        (holeOccurrences pattern).map rename)
    (motive_2 := fun patterns =>
      holeOccurrencesList (patterns.map (renameHoles rename)) =
        (holeOccurrencesList patterns).map rename)
    (fun key => by simp [renameHoles, holeOccurrences])
    (fun op children childrenResult => by
      simp only [renameHoles, holeOccurrences]
      exact childrenResult)
    (by rfl)
    (fun head tail headResult tailResult => by
      simp only [List.map_cons, holeOccurrencesList, List.map_append]
      rw [headResult, tailResult])
    pattern

/-- `idxOf` is invariant under an injective change of names. -/
theorem idxOf_map_injective {α β : Type*}
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (rename : α → β) (injective : Function.Injective rename)
    (needle : α) (values : List α) :
    (values.map rename).idxOf (rename needle) = values.idxOf needle := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      by_cases equal : needle = head
      · subst head
        simp
      · have renamed_ne : rename needle ≠ rename head := fun h =>
          equal (injective h)
        have head_ne : head ≠ needle := Ne.symm equal
        have renamed_head_ne : rename head ≠ rename needle := Ne.symm renamed_ne
        have renamed_beq : (rename head == rename needle) = false :=
          beq_false_of_ne renamed_head_ne
        have head_beq : (head == needle) = false := beq_false_of_ne head_ne
        simp only [List.map_cons, List.idxOf_cons, renamed_beq, head_beq,
          cond_false, inductionHypothesis]

/-- `idxOf` is invariant when a map is injective only on the list being
mapped.  This is the exact finite-support statement needed by canonical
schema normalization. -/
theorem idxOf_map_injectiveOn {α β : Type*}
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (rename : α → β) (needle : α) (values : List α)
    (needle_mem : needle ∈ values)
    (injectiveOn : ∀ left ∈ values, ∀ right ∈ values,
      rename left = rename right → left = right) :
    (values.map rename).idxOf (rename needle) = values.idxOf needle := by
  induction values with
  | nil => simp at needle_mem
  | cons head tail inductionHypothesis =>
      by_cases equal : needle = head
      · subst head
        simp
      · have needle_tail : needle ∈ tail := by
          simpa [equal] using needle_mem
        have renamed_ne : rename head ≠ rename needle := by
          intro renamed_equal
          exact equal (injectiveOn head (by simp) needle (by simp [needle_tail])
            renamed_equal).symm
        have head_ne : head ≠ needle := Ne.symm equal
        have renamed_beq : (rename head == rename needle) = false :=
          beq_false_of_ne renamed_ne
        have head_beq : (head == needle) = false := beq_false_of_ne head_ne
        have tail_injective : ∀ left ∈ tail, ∀ right ∈ tail,
            rename left = rename right → left = right := by
          intro left left_mem right right_mem
          exact injectiveOn left (by simp [left_mem]) right (by simp [right_mem])
        have tail_result := inductionHypothesis needle_tail tail_injective
        simp only [List.map_cons, List.idxOf_cons, renamed_beq, head_beq,
          cond_false, tail_result]

/-- Record, at every occurrence, the position of that value's first
occurrence. -/
def firstOccurrenceIndices {α : Type*} [BEq α] (values : List α) : List Nat :=
  values.map (fun value => values.idxOf value)

/-- First-occurrence indexing is itself stable under first-occurrence
indexing. -/
theorem idxOf_firstOccurrenceIndices {α : Type*}
    [BEq α] [LawfulBEq α] (needle : α) (values : List α)
    (needle_mem : needle ∈ values) :
    (firstOccurrenceIndices values).idxOf (values.idxOf needle) =
      values.idxOf needle := by
  apply idxOf_map_injectiveOn (fun value => values.idxOf value)
    needle values needle_mem
  intro left left_mem right _ equal
  exact (List.idxOf_inj left_mem).mp equal

/-! ## Executable normalization and idempotence -/

abbrev SchemaHole := HoleRole × Nat

mutual

/-- Hole labels of a schema in preorder occurrence order. -/
def schemaOccurrences : SchemaPattern → List SchemaHole
  | .hole role index => [(role, index)]
  | .node _ children => schemaOccurrencesList children

/-- Hole labels of a schema forest in preorder occurrence order. -/
def schemaOccurrencesList : List SchemaPattern → List SchemaHole
  | [] => []
  | head :: tail => schemaOccurrences head ++ schemaOccurrencesList tail

end

mutual

/-- Reindex a schema relative to one declared occurrence stream. -/
def normalizeWith (occurrences : List SchemaHole) :
    SchemaPattern → SchemaPattern
  | .hole role index => .hole role (occurrences.idxOf (role, index))
  | .node op children => .node op (normalizeListWith occurrences children)

/-- Reindex a forest of schemas relative to one occurrence stream. -/
def normalizeListWith (occurrences : List SchemaHole) :
    List SchemaPattern → List SchemaPattern
  | [] => []
  | head :: tail =>
      normalizeWith occurrences head :: normalizeListWith occurrences tail

end


/-- Executable normalization of an externally supplied schema. -/
def normalizeSchema (schema : SchemaPattern) : SchemaPattern :=
  normalizeWith (schemaOccurrences schema) schema

/-- Name erasure maps a pattern's occurrence stream pointwise. -/
theorem schemaOccurrences_schemaWith (occurrences : List HoleKey)
    (pattern : Pattern) :
    schemaOccurrences (schemaWith occurrences pattern) =
      (holeOccurrences pattern).map
        (fun key => (key.role, occurrences.idxOf key)) := by
  exact Pattern.rec
    (motive_1 := fun pattern =>
      schemaOccurrences (schemaWith occurrences pattern) =
        (holeOccurrences pattern).map
          (fun key => (key.role, occurrences.idxOf key)))
    (motive_2 := fun patterns =>
      schemaOccurrencesList (schemaListWith occurrences patterns) =
        (holeOccurrencesList patterns).map
          (fun key => (key.role, occurrences.idxOf key)))
    (fun key => by simp [schemaWith, schemaOccurrences, holeOccurrences])
    (fun _ _ childrenResult => by
      simpa [schemaWith, schemaOccurrences, holeOccurrences] using childrenResult)
    (by rfl)
    (fun _ _ headResult tailResult => by
      simp only [schemaListWith, schemaOccurrencesList, holeOccurrencesList,
        List.map_append]
      rw [headResult, tailResult])
    pattern

/-- Reindexing a name-erased subtree against a containing occurrence stream
does not change it. -/
theorem normalizeWith_schemaWith_of_holes_mem (occurrences : List HoleKey) :
    ∀ (pattern : Pattern),
      (∀ key ∈ holeOccurrences pattern, key ∈ occurrences) →
      normalizeWith
          (occurrences.map
            (fun key => (key.role, occurrences.idxOf key)))
          (schemaWith occurrences pattern) =
        schemaWith occurrences pattern := by
  apply Pattern.rec
    (motive_1 := fun pattern =>
      (∀ key ∈ holeOccurrences pattern, key ∈ occurrences) →
        normalizeWith
            (occurrences.map
              (fun key => (key.role, occurrences.idxOf key)))
            (schemaWith occurrences pattern) =
          schemaWith occurrences pattern)
    (motive_2 := fun patterns =>
      (∀ key ∈ holeOccurrencesList patterns, key ∈ occurrences) →
        normalizeListWith
            (occurrences.map
              (fun key => (key.role, occurrences.idxOf key)))
            (schemaListWith occurrences patterns) =
          schemaListWith occurrences patterns)
  · intro key holes_mem
    have key_mem : key ∈ occurrences := holes_mem key (by simp [holeOccurrences])
    have injectiveOn : ∀ left ∈ occurrences, ∀ right ∈ occurrences,
        (left.role, occurrences.idxOf left) =
            (right.role, occurrences.idxOf right) →
          left = right := by
      intro left left_mem right _ equal
      exact (List.idxOf_inj left_mem).mp (congrArg Prod.snd equal)
    have index_eq := idxOf_map_injectiveOn
      (fun item : HoleKey => (item.role, occurrences.idxOf item))
      key occurrences key_mem injectiveOn
    simpa [schemaWith, normalizeWith] using index_eq
  · intro _ _ childrenResult holes_mem
    simpa [schemaWith, normalizeWith] using childrenResult holes_mem
  · intro _
    rfl
  · intro head tail headResult tailResult holes_mem
    have head_mem : ∀ key ∈ holeOccurrences head, key ∈ occurrences := by
      intro key key_mem
      exact holes_mem key (by
        simp only [holeOccurrencesList, List.mem_append]
        exact Or.inl key_mem)
    have tail_mem : ∀ key ∈ holeOccurrencesList tail, key ∈ occurrences := by
      intro key key_mem
      exact holes_mem key (by
        simp only [holeOccurrencesList, List.mem_append]
        exact Or.inr key_mem)
    simp only [schemaListWith, normalizeListWith, List.cons.injEq]
    exact ⟨headResult head_mem, tailResult tail_mem⟩

/-- Canonical schema identity is a genuine normal form: normalizing it again
is observationally inert. -/
theorem normalizeSchema_canonicalSchema (pattern : Pattern) :
    normalizeSchema (canonicalSchema pattern) = canonicalSchema pattern := by
  rw [normalizeSchema, canonicalSchema,
    schemaOccurrences_schemaWith (holeOccurrences pattern) pattern]
  exact normalizeWith_schemaWith_of_holes_mem (holeOccurrences pattern)
    pattern (fun key key_mem => key_mem)

/-! ## Alpha-equivalence completeness -/

mutual

/-- Structural alpha-equivalence relative to two declared occurrence streams.
It requires the same operator tree, the same role at each hole, and the same
first-occurrence coordinate.  It does not mention `canonicalSchema`. -/
inductive AlphaSame (leftOccurrences rightOccurrences : List HoleKey) :
    Pattern → Pattern → Prop where
  | hole {leftKey rightKey : HoleKey} :
      leftKey.role = rightKey.role →
      leftOccurrences.idxOf leftKey = rightOccurrences.idxOf rightKey →
      AlphaSame leftOccurrences rightOccurrences (.hole leftKey) (.hole rightKey)
  | node {op : Nat} {leftChildren rightChildren : List Pattern} :
      AlphaSameChildren leftOccurrences rightOccurrences
        leftChildren rightChildren →
      AlphaSame leftOccurrences rightOccurrences
        (.node op leftChildren) (.node op rightChildren)

inductive AlphaSameChildren
    (leftOccurrences rightOccurrences : List HoleKey) :
    List Pattern → List Pattern → Prop where
  | nil : AlphaSameChildren leftOccurrences rightOccurrences [] []
  | cons {leftHead rightHead : Pattern} {leftTail rightTail : List Pattern} :
      AlphaSame leftOccurrences rightOccurrences leftHead rightHead →
      AlphaSameChildren leftOccurrences rightOccurrences leftTail rightTail →
      AlphaSameChildren leftOccurrences rightOccurrences
        (leftHead :: leftTail) (rightHead :: rightTail)

end


/-- Alpha-equivalence of complete patterns: operator/role structure and hole
sharing agree, while concrete memo keys may differ. -/
def AlphaEquivalent (left right : Pattern) : Prop :=
  AlphaSame (holeOccurrences left) (holeOccurrences right) left right

mutual

/-- Structural alpha-equivalence implies equality after name erasure. -/
theorem schemaWith_eq_of_alphaSame
    {leftOccurrences rightOccurrences : List HoleKey}
    {left right : Pattern}
    (same : AlphaSame leftOccurrences rightOccurrences left right) :
    schemaWith leftOccurrences left = schemaWith rightOccurrences right := by
  cases same with
  | hole role_eq index_eq =>
      simp only [schemaWith, SchemaPattern.hole.injEq]
      exact ⟨role_eq, index_eq⟩
  | node children_same =>
      simp only [schemaWith, SchemaPattern.node.injEq, true_and]
      exact schemaListWith_eq_of_alphaSameChildren children_same

/-- Forest counterpart of `schemaWith_eq_of_alphaSame`. -/
theorem schemaListWith_eq_of_alphaSameChildren
    {leftOccurrences rightOccurrences : List HoleKey}
    {left right : List Pattern}
    (same : AlphaSameChildren leftOccurrences rightOccurrences left right) :
    schemaListWith leftOccurrences left =
      schemaListWith rightOccurrences right := by
  cases same with
  | nil => rfl
  | cons head_same tail_same =>
      simp only [schemaListWith, List.cons.injEq]
      exact ⟨schemaWith_eq_of_alphaSame head_same,
        schemaListWith_eq_of_alphaSameChildren tail_same⟩

end


mutual

/-- Equality of erased schemas reconstructs structural alpha-equivalence. -/
def alphaSameOfSchemaWithEq
    (leftOccurrences rightOccurrences : List HoleKey) :
    (left right : Pattern) →
      schemaWith leftOccurrences left = schemaWith rightOccurrences right →
      AlphaSame leftOccurrences rightOccurrences left right
  | .hole leftKey, .hole rightKey, equal =>
      AlphaSame.hole
        (SchemaPattern.hole.inj equal).1
        (SchemaPattern.hole.inj equal).2
  | .hole _, .node _ _, equal => nomatch equal
  | .node _ _, .hole _, equal => nomatch equal
  | .node leftOp leftChildren, .node rightOp rightChildren, equal => by
      have op_eq : leftOp = rightOp := (SchemaPattern.node.inj equal).1
      subst rightOp
      exact AlphaSame.node (alphaSameChildrenOfSchemaListWithEq
        leftOccurrences rightOccurrences leftChildren rightChildren
        (SchemaPattern.node.inj equal).2)

/-- Forest counterpart of `alphaSameOfSchemaWithEq`. -/
def alphaSameChildrenOfSchemaListWithEq
    (leftOccurrences rightOccurrences : List HoleKey) :
    (left right : List Pattern) →
      schemaListWith leftOccurrences left =
          schemaListWith rightOccurrences right →
      AlphaSameChildren leftOccurrences rightOccurrences left right
  | [], [], _ => AlphaSameChildren.nil
  | [], _ :: _, equal => nomatch equal
  | _ :: _, [], equal => nomatch equal
  | leftHead :: leftTail, rightHead :: rightTail, equal =>
      AlphaSameChildren.cons
        (alphaSameOfSchemaWithEq leftOccurrences rightOccurrences
          leftHead rightHead (List.cons.inj equal).1)
        (alphaSameChildrenOfSchemaListWithEq leftOccurrences rightOccurrences
          leftTail rightTail (List.cons.inj equal).2)

end


/-- Canonical identity is complete for the independent structural notion of
alpha-equivalence, not merely invariant under a chosen renaming. -/
theorem canonicalSchema_eq_iff_alphaEquivalent (left right : Pattern) :
    canonicalSchema left = canonicalSchema right ↔
      AlphaEquivalent left right := by
  constructor
  · exact alphaSameOfSchemaWithEq
      (holeOccurrences left) (holeOccurrences right) left right
  · exact schemaWith_eq_of_alphaSame

/-! ## Reconstruction from a canonical schema and its occurrence dictionary -/

mutual

/-- Reconstruct a concrete pattern from a schema and the occurrence stream
that supplied its first-occurrence indices.  Role mismatches fail closed. -/
def reconstructWith (occurrences : List HoleKey) :
    SchemaPattern → Option Pattern
  | .hole role index =>
      match occurrences[index]? with
      | some key => if key.role = role then some (.hole key) else none
      | none => none
  | .node op children =>
      (reconstructListWith occurrences children).map (Pattern.node op)

/-- Reconstruct a forest of concrete patterns, failing if any child fails. -/
def reconstructListWith (occurrences : List HoleKey) :
    List SchemaPattern → Option (List Pattern)
  | [] => some []
  | head :: tail =>
      match reconstructWith occurrences head,
          reconstructListWith occurrences tail with
      | some rebuiltHead, some rebuiltTail =>
          some (rebuiltHead :: rebuiltTail)
      | _, _ => none

end


/-- A name-erased pattern reconstructs exactly when its holes are contained
in the supplied occurrence dictionary. -/
theorem reconstructWith_schemaWith_of_holes_mem (occurrences : List HoleKey) :
    ∀ (pattern : Pattern),
      (∀ key ∈ holeOccurrences pattern, key ∈ occurrences) →
      reconstructWith occurrences (schemaWith occurrences pattern) =
        some pattern := by
  apply Pattern.rec
    (motive_1 := fun pattern =>
      (∀ key ∈ holeOccurrences pattern, key ∈ occurrences) →
        reconstructWith occurrences (schemaWith occurrences pattern) =
          some pattern)
    (motive_2 := fun patterns =>
      (∀ key ∈ holeOccurrencesList patterns, key ∈ occurrences) →
        reconstructListWith occurrences (schemaListWith occurrences patterns) =
          some patterns)
  · intro key holes_mem
    have key_mem : key ∈ occurrences := holes_mem key (by simp [holeOccurrences])
    have get_key : occurrences[occurrences.idxOf key]? = some key :=
      List.getElem?_idxOf key_mem
    simp only [schemaWith, reconstructWith, get_key]
    simp
  · intro op _ childrenResult holes_mem
    simp only [schemaWith, reconstructWith]
    rw [childrenResult holes_mem]
    rfl
  · intro _
    rfl
  · intro head tail headResult tailResult holes_mem
    have head_mem : ∀ key ∈ holeOccurrences head, key ∈ occurrences := by
      intro key key_mem
      exact holes_mem key (by
        simp only [holeOccurrencesList, List.mem_append]
        exact Or.inl key_mem)
    have tail_mem : ∀ key ∈ holeOccurrencesList tail, key ∈ occurrences := by
      intro key key_mem
      exact holes_mem key (by
        simp only [holeOccurrencesList, List.mem_append]
        exact Or.inr key_mem)
    simp only [schemaListWith, reconstructListWith]
    rw [headResult head_mem, tailResult tail_mem]

/-- A canonical schema plus its occurrence dictionary is lossless. -/
theorem reconstructWith_canonicalSchema (pattern : Pattern) :
    reconstructWith (holeOccurrences pattern) (canonicalSchema pattern) =
      some pattern := by
  exact reconstructWith_schemaWith_of_holes_mem (holeOccurrences pattern)
    pattern (fun key key_mem => key_mem)

/-- Negative reconstruction fixture: the dictionary role must agree with the
typed schema role. -/
theorem reconstructWith_role_mismatch :
    reconstructWith [⟨.code, zero, one⟩] (.hole .value 0) = none := by
  rfl

/-- Negative reconstruction fixture: an out-of-range canonical coordinate
fails instead of inventing a hole. -/
theorem reconstructWith_out_of_range :
    reconstructWith [] (.hole .root 0) = none := by
  rfl

/-- Applying an injective, role-preserving rename before erasing names cannot
change the resulting schema. -/
theorem schemaWith_renameHoles
    (rename : HoleKey → HoleKey) (injective : Function.Injective rename)
    (role_preserving : ∀ key, (rename key).role = key.role)
    (occurrences : List HoleKey) (pattern : Pattern) :
    schemaWith (occurrences.map rename) (renameHoles rename pattern) =
      schemaWith occurrences pattern := by
  exact Pattern.rec
    (motive_1 := fun pattern =>
      schemaWith (occurrences.map rename) (renameHoles rename pattern) =
        schemaWith occurrences pattern)
    (motive_2 := fun patterns =>
      schemaListWith (occurrences.map rename)
          (patterns.map (renameHoles rename)) =
        schemaListWith occurrences patterns)
    (fun key => by
      simp only [renameHoles, schemaWith, SchemaPattern.hole.injEq]
      exact ⟨role_preserving key,
        idxOf_map_injective rename injective key occurrences⟩)
    (fun op children childrenResult => by
      simp only [renameHoles, schemaWith, SchemaPattern.node.injEq,
        true_and]
      exact childrenResult)
    (by rfl)
    (fun _ _ headResult tailResult => by
      simp only [List.map_cons, schemaListWith, List.cons.injEq]
      exact ⟨headResult, tailResult⟩)
    pattern

/-- Canonical schema identity is invariant under every injective,
role-preserving concrete-hole rename. -/
theorem canonicalSchema_renameHoles
    (rename : HoleKey → HoleKey) (injective : Function.Injective rename)
    (role_preserving : ∀ key, (rename key).role = key.role)
    (pattern : Pattern) :
    canonicalSchema (renameHoles rename pattern) = canonicalSchema pattern := by
  rw [canonicalSchema, canonicalSchema, holeOccurrences_renameHoles]
  exact schemaWith_renameHoles rename injective role_preserving
    (holeOccurrences pattern) pattern

@[simp] theorem swapHoleKey_involutive (key : HoleKey) :
    swapHoleKey (swapHoleKey key) = key := by
  cases key
  rfl

theorem swapHoleKey_injective : Function.Injective swapHoleKey := by
  intro left right equal
  have := congrArg swapHoleKey equal
  simpa using this

@[simp] theorem swapHoleKey_role (key : HoleKey) :
    (swapHoleKey key).role = key.role := rfl

/-- Swapping the two programs supplied to anti-unification cannot alter the
canonical schema identity. -/
theorem canonicalSchema_lgg_comm (sig : Signature σ) (role : HoleRole)
    (left right : Prog) :
    canonicalSchema (lgg sig role left right) =
      canonicalSchema (lgg sig role right left) := by
  rw [← renameHoles_swap_lgg]
  exact canonicalSchema_renameHoles swapHoleKey swapHoleKey_injective
    swapHoleKey_role _

/-- Input swapping yields alpha-equivalent patterns, even though their raw
memo keys differ. -/
theorem lgg_alphaEquivalent_comm (sig : Signature σ) (role : HoleRole)
    (left right : Prog) :
    AlphaEquivalent (lgg sig role left right) (lgg sig role right left) :=
  (canonicalSchema_eq_iff_alphaEquivalent _ _).mp
    (canonicalSchema_lgg_comm sig role left right)

/-! ## Role preservation -/

mutual

/-- The existing role contract transported to name-independent schemas. -/
inductive SchemaRolesCorrect (sig : Signature σ) :
    HoleRole → SchemaPattern → Prop where
  | hole {role actualRole : HoleRole} {index : Nat} :
      actualRole = role → SchemaRolesCorrect sig role (.hole actualRole index)
  | node {role : HoleRole} {op : Nat} {children : List SchemaPattern}
      {entry : Entry σ} :
      entryAt sig op = some entry →
      children.length = entry.arity →
      SchemaRolesCorrectChildren sig entry 0 children →
      SchemaRolesCorrect sig role (.node op children)

inductive SchemaRolesCorrectChildren (sig : Signature σ) :
    Entry σ → Nat → List SchemaPattern → Prop where
  | nil {entry : Entry σ} {index : Nat} :
      SchemaRolesCorrectChildren sig entry index []
  | cons {entry : Entry σ} {index : Nat}
      {head : SchemaPattern} {tail : List SchemaPattern} :
      SchemaRolesCorrect sig (childHoleRole entry index) head →
      SchemaRolesCorrectChildren sig entry (index + 1) tail →
      SchemaRolesCorrectChildren sig entry index (head :: tail)

end

/-- Erasing concrete hole names preserves every code/value role obligation. -/
theorem schemaWith_rolesCorrect {sig : Signature σ} {role : HoleRole}
    {pattern : Pattern} (occurrences : List HoleKey)
    (correct : RolesCorrect sig role pattern) :
    SchemaRolesCorrect sig role (schemaWith occurrences pattern) := by
  exact RolesCorrect.rec
    (motive_1 := fun role pattern _ =>
      SchemaRolesCorrect sig role (schemaWith occurrences pattern))
    (motive_2 := fun entry index patterns _ =>
      SchemaRolesCorrectChildren sig entry index
        (schemaListWith occurrences patterns))
    (fun equal => SchemaRolesCorrect.hole equal)
    (fun hentry hlength _ childrenResult =>
      SchemaRolesCorrect.node hentry (by simpa using hlength) childrenResult)
    SchemaRolesCorrectChildren.nil
    (fun _ _ headResult tailResult =>
      SchemaRolesCorrectChildren.cons headResult tailResult)
    correct

/-- Well-formed anti-unification inputs therefore produce a role-correct
canonical schema. -/
theorem canonicalSchema_lgg_rolesCorrect {sig : Signature σ} {role : HoleRole}
    {left right : Prog} (left_wellFormed : WellFormed sig left)
    (right_wellFormed : WellFormed sig right) :
    SchemaRolesCorrect sig role (canonicalSchema (lgg sig role left right)) := by
  exact schemaWith_rolesCorrect (holeOccurrences (lgg sig role left right))
    (lgg_rolesCorrect left_wellFormed right_wellFormed)

/-! ## Positive and negative identity examples -/

def swappedRawLeft : Pattern := lgg orgMemoSignature .root zero one
def swappedRawRight : Pattern := lgg orgMemoSignature .root one zero

/-- Concrete LGG memo keys remember input orientation, so raw pattern equality
is not a stable schema identity. -/
theorem swapped_lgg_raw_ne : swappedRawLeft ≠ swappedRawRight := by
  simp [swappedRawLeft, swappedRawRight, lgg, zero, one]

/-- Canonical identity removes exactly that irrelevant orientation. -/
theorem swapped_lgg_canonical_eq :
    canonicalSchema swappedRawLeft = canonicalSchema swappedRawRight := by
  exact canonicalSchema_lgg_comm orgMemoSignature .root zero one

/-- Deliberately unsound projection used only for the role-erasure
counterexample. -/
def eraseRoles : SchemaPattern → SchemaPattern
  | .hole _ index => .hole .root index
  | .node op children => .node op (children.map eraseRoles)

/-- Code and value holes are distinct typed schemas.  Erasing their roles
collapses them, demonstrating why role-blind schema keys are unsound. -/
theorem role_erasure_identifies_distinct_schemas :
    (SchemaPattern.hole .code 0 ≠ SchemaPattern.hole .value 0) ∧
      eraseRoles (.hole .code 0) = eraseRoles (.hole .value 0) := by
  constructor
  · intro equality
    have role_eq : HoleRole.code = HoleRole.value :=
      (SchemaPattern.hole.inj equality).1
    cases role_eq
  · simp only [eraseRoles]

#print axioms idxOf_map_injective
#print axioms idxOf_map_injectiveOn
#print axioms normalizeSchema_canonicalSchema
#print axioms canonicalSchema_eq_iff_alphaEquivalent
#print axioms reconstructWith_canonicalSchema
#print axioms canonicalSchema_renameHoles
#print axioms canonicalSchema_lgg_comm
#print axioms lgg_alphaEquivalent_comm
#print axioms schemaWith_rolesCorrect
#print axioms canonicalSchema_lgg_rolesCorrect
#print axioms swapped_lgg_raw_ne
#print axioms swapped_lgg_canonical_eq
#print axioms role_erasure_identifies_distinct_schemas

end Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
