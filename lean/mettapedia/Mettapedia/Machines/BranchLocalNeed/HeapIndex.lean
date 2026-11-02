import Mettapedia.Machines.BranchLocalNeed.ReferenceSemantics
import Mathlib.Tactic

/-!
# Persistent bounded index for reference Need heaps

The reference Need heap deliberately exposes an extensional finite-map view
and a persistent semantic update spine.  A native snapshot may additionally
carry an immutable radix index from stable cell keys to the newest frame.
The index is derived: lookup agrees with the semantic heap, while the update
spine remains the authority for lineage, ancestry, promotion, and replay.

Source cell identities remain unbounded. A partial assignment gives native
keys only to the cells represented in a particular heap. Injectivity applies
to assigned keys, not to every possible source identity.

Keys have exactly sixteen hexadecimal digits, matching an internal 64-bit
cell key. The uncompressed reference `Trie` examines exactly seventeen nodes
on a successful lookup. `CompressedTrie` models the compressed native
candidate: leaves retain full keys, branches retain their actual split
positions, and skipped unary levels incur no node examinations. Its lookup
and insertion bounds follow from the maintained compression invariant.
Both representations instantiate the same heap-refinement lookup view.
These are representation models, not compiled-C verification.
-/

namespace Mettapedia.Machines.BranchLocalNeed.NeedHeapIndex

open NeedReference

abbrev Digit := Fin 16

/-- A 64-bit internal key represented without hashing or collisions. -/
abbrev Key := { path : List Digit // path.length = 16 }

/-- A persistent radix trie.  `value` permits the generic list-key proofs;
reference's fixed-width keys place values only at depth sixteen. -/
inductive Trie (α : Type*) where
  | node (value : Option α) (children : Digit → Option (Trie α))

namespace Trie

variable {α : Type*}

def empty : Trie α :=
  .node none (fun _ => none)

def lookup : Trie α → List Digit → Option α
  | .node value _, [] => value
  | .node _ children, digit :: rest =>
      match children digit with
      | none => none
      | some child => child.lookup rest

def insert : Trie α → List Digit → α → Trie α
  | .node _ children, [], value =>
      .node (some value) children
  | .node here children, digit :: rest, value =>
      let child := (children digit).getD empty
      .node here
        (Function.update children digit
          (some (child.insert rest value)))

@[simp] theorem lookup_empty (path : List Digit) :
    (empty : Trie α).lookup path = none := by
  cases path <;> rfl

@[simp] theorem lookup_insert_self
    (trie : Trie α) (path : List Digit) (value : α) :
    (trie.insert path value).lookup path = some value := by
  induction path generalizing trie with
  | nil =>
      cases trie
      rfl
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          simp only [insert, lookup, Function.update_self]
          exact ih _

theorem lookup_insert_other
    (trie : Trie α) {inserted queried : List Digit} (value : α)
    (hDifferent : queried ≠ inserted) :
    (trie.insert inserted value).lookup queried = trie.lookup queried := by
  induction inserted generalizing trie queried with
  | nil =>
      cases queried with
      | nil => exact False.elim (hDifferent rfl)
      | cons digit rest =>
          cases trie
          rfl
  | cons insertedDigit insertedRest ih =>
      cases queried with
      | nil =>
          cases trie
          rfl
      | cons queriedDigit queriedRest =>
          cases trie with
          | node here children =>
              by_cases hDigit : queriedDigit = insertedDigit
              · subst queriedDigit
                have hRest : queriedRest ≠ insertedRest := by
                  intro hEqual
                  exact hDifferent (congrArg (List.cons insertedDigit) hEqual)
                cases hChild : children insertedDigit with
                | none =>
                    simp [insert, lookup, hChild, ih empty hRest]
                | some child =>
                    simp [insert, lookup, hChild, ih child hRest]
              · simp [insert, lookup, Function.update, hDigit]

/-- Lookup work counts node examinations and can stop at an absent child. -/
def lookupSteps : Trie α → List Digit → Nat
  | .node _ _, [] => 1
  | .node _ children, digit :: rest =>
      1 +
        match children digit with
        | none => 0
        | some child => child.lookupSteps rest

theorem lookupSteps_le (trie : Trie α) (path : List Digit) :
    trie.lookupSteps path ≤ path.length + 1 := by
  induction path generalizing trie with
  | nil =>
      cases trie
      simp [lookupSteps]
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          cases hChild : children digit with
          | none => simp [lookupSteps, hChild]
          | some child =>
              simp only [lookupSteps, hChild, List.length_cons]
              have hBound := ih child
              omega

theorem lookupSteps_insert_self
    (trie : Trie α) (path : List Digit) (value : α) :
    (trie.insert path value).lookupSteps path = path.length + 1 := by
  induction path generalizing trie with
  | nil =>
      cases trie
      rfl
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          simp only [insert, lookupSteps, Function.update_self,
            List.length_cons]
          rw [ih]
          omega

def lookupKey (trie : Trie α) (key : Key) : Option α :=
  trie.lookup key.1

def insertKey (trie : Trie α) (key : Key) (value : α) : Trie α :=
  trie.insert key.1 value

@[simp] theorem lookupKey_insert_self
    (trie : Trie α) (key : Key) (value : α) :
    (trie.insertKey key value).lookupKey key = some value :=
  lookup_insert_self trie key.1 value

theorem lookupKey_insert_other
    (trie : Trie α) {inserted queried : Key} (value : α)
    (hDifferent : queried ≠ inserted) :
    (trie.insertKey inserted value).lookupKey queried =
      trie.lookupKey queried := by
  apply lookup_insert_other
  intro hPaths
  exact hDifferent (Subtype.ext hPaths)

theorem lookupKey_insert (trie : Trie α) (key : Key) (value : α) (queried : Key) :
    (trie.insertKey key value).lookupKey queried =
      if queried = key then some value else trie.lookupKey queried := by
  by_cases same : queried = key
  · subst queried
    simp
  · simpa only [if_neg same] using lookupKey_insert_other trie value same

theorem lookupKey_steps_le (trie : Trie α) (key : Key) :
    trie.lookupSteps key.1 ≤ 17 := by
  simpa [key.2] using lookupSteps_le trie key.1

theorem lookupKey_insert_steps
    (trie : Trie α) (key : Key) (value : α) :
    (trie.insertKey key value).lookupSteps key.1 = 17 := by
  simpa [insertKey, key.2] using lookupSteps_insert_self trie key.1 value

end Trie

namespace Key

/-- The most significant digit has position zero. Out-of-range positions are
totalized only for the raw representation; valid branches use positions < 16. -/
def digit (key : Key) (position : Nat) : Digit :=
  key.1[position]?.getD 0

/-- Exact equality of the digits before a branching position. -/
def Agree (left right : Key) (before : Nat) : Prop :=
  ∀ position : Fin before, left.digit position = right.digit position

instance (left right : Key) (before : Nat) : Decidable (Agree left right before) :=
  inferInstanceAs (Decidable (∀ position : Fin before,
    left.digit position = right.digit position))

@[simp] theorem Agree.refl (key : Key) (before : Nat) : Agree key key before :=
  fun _ => rfl

theorem Agree.symm {left right : Key} {before : Nat} (agree : Agree left right before) :
    Agree right left before :=
  fun position => (agree position).symm

theorem Agree.trans {left middle right : Key} {before : Nat}
    (leftAgree : Agree left middle before) (rightAgree : Agree middle right before) :
    Agree left right before :=
  fun position => (leftAgree position).trans (rightAgree position)

theorem Agree.mono {left right : Key} {before shorter : Nat}
    (agree : Agree left right before) (bound : shorter ≤ before) :
    Agree left right shorter :=
  fun position => agree ⟨position.1, lt_of_lt_of_le position.2 bound⟩

theorem Agree.at {left right : Key} {before position : Nat}
    (agree : Agree left right before) (bound : position < before) :
    left.digit position = right.digit position :=
  agree ⟨position, bound⟩

theorem Agree.succ {left right : Key} {before : Nat}
    (agree : Agree left right before) (last : left.digit before = right.digit before) :
    Agree left right (before + 1) := by
  intro position
  by_cases earlier : position.1 < before
  · exact agree.at earlier
  · have same : position.1 = before := by omega
    simpa [same] using last

theorem ext_digits {left right : Key}
    (same : Agree left right 16) : left = right := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [left.2, right.2])
  intro position leftBound rightBound
  have equal := same.at (position := position) (by omega)
  simpa [digit, leftBound, rightBound] using equal

/-- The first differing nibble, or sixteen for equal full keys. -/
def divergence (left right : Key) : Nat :=
  ((List.range 16).find? fun position =>
    decide (left.digit position ≠ right.digit position)).getD 16

theorem divergence_spec (left right : Key) :
    left.divergence right ≤ 16 ∧ Agree left right (left.divergence right) ∧
      (left.divergence right < 16 →
        left.digit (left.divergence right) ≠ right.digit (left.divergence right)) := by
  unfold divergence
  cases found : (List.range 16).find? (fun position =>
      decide (left.digit position ≠ right.digit position)) with
  | none =>
      have absent := List.find?_range_eq_none.mp found
      simp only [Option.getD_none]
      refine ⟨le_rfl, ?_, by omega⟩
      intro position
      simpa using absent position.1 position.2
  | some position =>
      have first := List.find?_range_eq_some.mp found
      simp only [Option.getD_some]
      refine ⟨by simpa using Nat.le_of_lt (List.mem_range.mp first.2.1), ?_, ?_⟩
      · intro earlier
        simpa using first.2.2 earlier.1 earlier.2
      · intro _
        simpa using first.1

@[simp] theorem divergence_eq_sixteen_iff (left right : Key) :
    left.divergence right = 16 ↔ left = right := by
  have spec := divergence_spec left right
  constructor
  · intro full
    exact ext_digits (full ▸ spec.2.1)
  · intro same
    subst right
    by_contra shorter
    exact spec.2.2 (by omega) rfl

@[simp] theorem divergence_self (key : Key) : key.divergence key = 16 :=
  (divergence_eq_sixteen_iff key key).mpr rfl

theorem Agree.le_divergence {left right : Key} {before : Nat}
    (agree : Agree left right before) (bound : before ≤ 16) :
    before ≤ left.divergence right := by
  by_contra tooShort
  have less : left.divergence right < before := by omega
  exact (divergence_spec left right).2.2 (by omega) (agree.at less)

end Key

/-- A path-compressed persistent radix tree. Absence of the entire tree is
represented by `Option`; every represented subtree is nonempty. Branches
retain a full representative key and the position of their first branching
digit, rather than materializing their unary prefix. -/
inductive CompressedTrie (α : Type*) where
  | leaf (key : Key) (value : α)
  | branch (representative : Key) (depth : Nat)
      (children : Digit → Option (CompressedTrie α))

namespace CompressedTrie

variable {α : Type*}

def representative : CompressedTrie α → Key
  | .leaf key _ => key
  | .branch key _ _ => key

/-- Sixteen is the leaf sentinel; valid internal depths are smaller. -/
def depth : CompressedTrie α → Nat
  | .leaf _ _ => 16
  | .branch _ position _ => position

mutual
  def Contains : CompressedTrie α → Key → Prop
    | .leaf key _, queried => queried = key
    | .branch _ _ children, queried =>
        ∃ digit, containsOption (children digit) queried

  def containsOption : Option (CompressedTrie α) → Key → Prop
    | none, _ => False
    | some child, queried => child.Contains queried
end

@[simp] theorem contains_branch (key queried : Key) (position : Nat)
    (children : Digit → Option (CompressedTrie α)) :
    (.branch key position children : CompressedTrie α).Contains queried ↔
      ∃ digit child, children digit = some child ∧ child.Contains queried := by
  simp only [Contains]
  constructor
  · rintro ⟨digit, present⟩
    cases childRead : children digit with
    | none => simp [childRead, containsOption] at present
    | some child => exact ⟨digit, child, childRead, by simpa [childRead, containsOption] using present⟩
  · rintro ⟨digit, child, childRead, present⟩
    exact ⟨digit, by simpa [childRead, containsOption] using present⟩

def AllKeys (tree : CompressedTrie α) (property : Key → Prop) : Prop :=
  ∀ key, tree.Contains key → property key

/- Representatives are actual descendant keys. Distinct occupied slots rule
out unary branches; the route law checks the entire skipped prefix and the
selected branching digit. Strict depth growth bounds all root-to-leaf paths. -/
mutual
  def WellFormed : CompressedTrie α → Prop
    | .leaf _ _ => True
    | .branch key position children =>
        position < 16 ∧
        (∃ child, children (key.digit position) = some child ∧ child.representative = key) ∧
        (∃ left right, left ≠ right ∧ (children left).isSome ∧ (children right).isSome) ∧
        ∀ digit, wellFormedChild key position digit (children digit)

  def wellFormedChild (key : Key) (position : Nat) (digit : Digit) :
      Option (CompressedTrie α) → Prop
    | none => True
    | some child =>
        child.WellFormed ∧ position < child.depth ∧
          child.AllKeys (fun descendant =>
            Key.Agree descendant key position ∧ descendant.digit position = digit)
end

mutual
  def lookup : CompressedTrie α → Key → Option α
    | .leaf key value, queried => if queried = key then some value else none
    | .branch key position children, queried =>
        if Key.Agree queried key position then
          lookupOption (children (queried.digit position)) queried
        else none

  def lookupOption : Option (CompressedTrie α) → Key → Option α
    | none, _ => none
    | some child, queried => child.lookup queried
end

/-- A fresh branch shares the old subtree and adds exactly one new leaf. -/
def split (tree : CompressedTrie α) (key : Key) (value : α) (position : Nat) :
    CompressedTrie α :=
  .branch tree.representative position
    (Function.update
      (Function.update (fun _ => none) (tree.representative.digit position) (some tree))
      (key.digit position) (some (.leaf key value)))

/- Only the actual branch route is copied. Divergence inside a skipped prefix
creates a branch above the retained subtree. Exact-key replacement preserves
all other leaves and the semantic update history lives outside this index. -/
mutual
  def insert : CompressedTrie α → Key → α → CompressedTrie α
    | tree@(.leaf old _), key, value =>
        let position := key.divergence old
        if position < 16 then tree.split key value position else .leaf key value
    | tree@(.branch old position children), key, value =>
        let divergent := key.divergence old
        if divergent < position then tree.split key value divergent
        else
          let slot := key.digit position
          .branch old position (Function.update children slot
            (some (insertOption (children slot) key value)))

  def insertOption : Option (CompressedTrie α) → Key → α → CompressedTrie α
    | none, key, value => .leaf key value
    | some previous, key, value => previous.insert key value
end

/- Lookup cost counts represented nodes, including a prefix rejection, and
charges no examinations for the unary radix levels that are not represented. -/
mutual
  def lookupSteps : CompressedTrie α → Key → Nat
    | .leaf _ _, _ => 1
    | .branch key position children, queried =>
        if Key.Agree queried key position then
          1 + lookupOptionSteps (children (queried.digit position)) queried
        else 1

  def lookupOptionSteps : Option (CompressedTrie α) → Key → Nat
    | none, _ => 0
    | some child, queried => child.lookupSteps queried
end

@[elab_as_elim] theorem inductionOnChildren (tree : CompressedTrie α)
    {motive : CompressedTrie α → Prop}
    (leaf : ∀ key value, motive (.leaf key value))
    (branch : ∀ key position children,
      (∀ digit child, children digit = some child → motive child) →
      motive (.branch key position children)) : motive tree := by
  apply CompressedTrie.rec (motive_1 := motive)
    (motive_2 := fun option => ∀ child, option = some child → motive child)
    leaf branch _ _ tree
  · intro child impossible
    contradiction
  · intro child proved other same
    cases Option.some.inj same
    exact proved

theorem WellFormed.child {key : Key} {position : Nat}
    {children : Digit → Option (CompressedTrie α)}
    (valid : WellFormed (.branch key position children))
    {digit : Digit} {child : CompressedTrie α} (read : children digit = some child) :
    child.WellFormed ∧ position < child.depth ∧
      child.AllKeys (fun descendant =>
        Key.Agree descendant key position ∧ descendant.digit position = digit) := by
  have routed := valid.2.2.2 digit
  simpa [read, wellFormedChild] using routed

theorem WellFormed.depth_le {tree : CompressedTrie α} (valid : tree.WellFormed) :
    tree.depth ≤ 16 := by
  cases tree with
  | leaf key value => exact le_rfl
  | branch key position children => exact Nat.le_of_lt valid.1

theorem WellFormed.contains_representative {tree : CompressedTrie α}
    (valid : tree.WellFormed) : tree.Contains tree.representative := by
  induction tree using inductionOnChildren with
  | leaf key value => rfl
  | branch key position children ih =>
      obtain ⟨child, read, representativeSame⟩ := valid.2.1
      apply (contains_branch _ _ _ _).mpr
      refine ⟨_, child, read, ?_⟩
      change child.Contains key
      rw [← representativeSame]
      exact ih _ child read (valid.child read).1

theorem WellFormed.allKeys_agree {tree : CompressedTrie α}
    (valid : tree.WellFormed) :
    tree.AllKeys (fun key => Key.Agree key tree.representative tree.depth) := by
  cases tree with
  | leaf key value =>
      intro queried present
      cases present
      exact Key.Agree.refl _ _
  | branch key position children =>
      intro queried present
      obtain ⟨digit, child, read, present⟩ := (contains_branch _ _ _ _).mp present
      exact ((valid.child read).2.2 queried present).1

theorem lookup_some_contains (tree : CompressedTrie α) (queried : Key) (value : α)
    (found : tree.lookup queried = some value) : tree.Contains queried := by
  induction tree using inductionOnChildren with
  | leaf key previous =>
      simpa [lookup, Contains] using (show queried = key from by
        by_contra different
        simp [lookup, different] at found)
  | branch key position children ih =>
      by_cases agree : Key.Agree queried key position
      · cases read : children (queried.digit position) with
        | none => simp [lookup, agree, read, lookupOption] at found
        | some child =>
            apply (contains_branch _ _ _ _).mpr
            exact ⟨_, child, read, ih _ child read
              (by simpa [lookup, agree, read, lookupOption] using found)⟩
      · simp [lookup, agree] at found

theorem lookup_none_of_not_contains (tree : CompressedTrie α) (queried : Key)
    (absent : ¬ tree.Contains queried) : tree.lookup queried = none := by
  cases found : tree.lookup queried with
  | none => rfl
  | some value => exact False.elim (absent (lookup_some_contains tree queried value found))

theorem WellFormed.lookup_some_agree {tree : CompressedTrie α} (valid : tree.WellFormed)
    {queried : Key} {value : α} (found : tree.lookup queried = some value) :
    Key.Agree queried tree.representative tree.depth :=
  valid.allKeys_agree queried (lookup_some_contains tree queried value found)

theorem WellFormed.lookup_none_of_prefix {tree : CompressedTrie α} (valid : tree.WellFormed)
    (queried : Key) {before : Nat} (bound : before ≤ tree.depth)
    (different : ¬ Key.Agree queried tree.representative before) :
    tree.lookup queried = none := by
  apply lookup_none_of_not_contains
  intro present
  exact different ((valid.allKeys_agree queried present).mono bound)

theorem WellFormed.lookup_none_of_digit {tree : CompressedTrie α} (valid : tree.WellFormed)
    (queried : Key) {position : Nat} (bound : position < tree.depth)
    (different : queried.digit position ≠ tree.representative.digit position) :
    tree.lookup queried = none := by
  apply lookup_none_of_not_contains
  intro present
  exact different ((valid.allKeys_agree queried present).at bound)

theorem lookupSteps_le_depth (tree : CompressedTrie α) (valid : tree.WellFormed)
    (queried : Key) : tree.lookupSteps queried ≤ 17 - tree.depth := by
  induction tree using inductionOnChildren with
  | leaf key value => simp [lookupSteps, depth]
  | branch key position children ih =>
      by_cases agree : Key.Agree queried key position
      · cases read : children (queried.digit position) with
        | none =>
            simp only [lookupSteps, if_pos agree, read, lookupOptionSteps, depth]
            have bound := valid.1
            omega
        | some child =>
            have routed := valid.child read
            have bound := ih _ child read routed.1
            have childBound := routed.1.depth_le
            simp only [lookupSteps, if_pos agree, read, lookupOptionSteps, depth]
            omega
      · simp only [lookupSteps, if_neg agree, depth]
        have bound := valid.1
        omega

theorem lookupSteps_le (tree : CompressedTrie α) (valid : tree.WellFormed) (queried : Key) :
    tree.lookupSteps queried ≤ 17 :=
  (lookupSteps_le_depth tree valid queried).trans (Nat.sub_le _ _)

theorem contains_split (tree : CompressedTrie α) (key : Key) (value : α) (position : Nat)
    (different : key.digit position ≠ tree.representative.digit position) (queried : Key) :
    (tree.split key value position).Contains queried ↔ queried = key ∨ tree.Contains queried := by
  rw [split, contains_branch]
  constructor
  · rintro ⟨digit, child, read, present⟩
    by_cases newSlot : digit = key.digit position
    · subst digit
      rw [Function.update_self] at read
      cases Option.some.inj read
      exact Or.inl present
    · rw [Function.update_of_ne newSlot] at read
      by_cases oldSlot : digit = tree.representative.digit position
      · subst digit
        rw [Function.update_self] at read
        cases Option.some.inj read
        exact Or.inr present
      · simp [Function.update_of_ne oldSlot] at read
  · rintro (newKey | oldKey)
    · subst queried
      exact ⟨_, .leaf key value, Function.update_self _ _ _, rfl⟩
    · refine ⟨tree.representative.digit position, tree, ?_, oldKey⟩
      rw [Function.update_of_ne different.symm, Function.update_self]

private theorem contains_branch_at_slot (key queried : Key) (position : Nat)
    (children : Digit → Option (CompressedTrie α)) (slot : Digit) :
    (.branch key position children : CompressedTrie α).Contains queried ↔
      containsOption (children slot) queried ∨
        ∃ digit, digit ≠ slot ∧ containsOption (children digit) queried := by
  simp only [Contains]
  constructor
  · rintro ⟨digit, present⟩
    by_cases selected : digit = slot
    · exact Or.inl (selected ▸ present)
    · exact Or.inr ⟨digit, selected, present⟩
  · rintro (selected | ⟨digit, _, present⟩)
    · exact ⟨slot, selected⟩
    · exact ⟨digit, present⟩

private theorem contains_branch_update (key queried : Key) (position : Nat)
    (children : Digit → Option (CompressedTrie α)) (slot : Digit) (replacement : CompressedTrie α) :
    (CompressedTrie.branch key position (Function.update children slot (some replacement))).Contains queried ↔
      replacement.Contains queried ∨
        ∃ digit, digit ≠ slot ∧ containsOption (children digit) queried := by
  rw [contains_branch_at_slot key queried position _ slot]
  simp only [Function.update_self, containsOption]
  apply or_congr Iff.rfl
  apply exists_congr
  intro digit
  by_cases selected : digit = slot
  · simp [selected]
  · simp [selected]

/-- The physical leaf inventory gains precisely the selected key. This result
does not assume validity of the output; it is proved from the input invariant. -/
theorem contains_insert (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (value : α) (queried : Key) :
    (tree.insert key value).Contains queried ↔ queried = key ∨ tree.Contains queried := by
  induction tree using inductionOnChildren with
  | leaf old previous =>
      by_cases different : key.divergence old < 16
      · simpa only [insert, if_pos different] using
          contains_split (.leaf old previous) key value (key.divergence old)
            ((Key.divergence_spec key old).2.2 different) queried
      · have same : key = old := (Key.divergence_eq_sixteen_iff key old).mp
          (by have bound := (Key.divergence_spec key old).1; omega)
        simp [insert, Contains, same]
  | branch old position children ih =>
      by_cases different : key.divergence old < position
      · have bound : key.divergence old < 16 := lt_trans different valid.1
        simpa only [insert, if_pos different] using
          contains_split (.branch old position children) key value (key.divergence old)
            ((Key.divergence_spec key old).2.2 bound) queried
      · simp only [insert, if_neg different]
        rw [contains_branch_update, contains_branch_at_slot old queried position children
          (key.digit position)]
        have selected :
            (insertOption (children (key.digit position)) key value).Contains queried ↔
              queried = key ∨ containsOption (children (key.digit position)) queried := by
          cases read : children (key.digit position) with
          | none => simp [insertOption, Contains, containsOption]
          | some child =>
              simpa only [insertOption, containsOption] using
                ih _ child read (valid.child read).1
        rw [selected]
        tauto

theorem allKeys_insert (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (value : α) {property : Key → Prop}
    (previous : tree.AllKeys property) (added : property key) :
    (tree.insert key value).AllKeys property := by
  intro queried present
  rcases (contains_insert tree valid key value queried).mp present with same | old
  · exact same ▸ added
  · exact previous queried old

theorem lookup_split (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (value : α) (position : Nat)
    (before : position < tree.depth) (agree : Key.Agree key tree.representative position)
    (different : key.digit position ≠ tree.representative.digit position) (queried : Key) :
    (tree.split key value position).lookup queried =
      if queried = key then some value else tree.lookup queried := by
  by_cases same : queried = key
  · subst queried
    simp [split, lookup, lookupOption, agree]
  · simp only [if_neg same]
    by_cases prefixMatch : Key.Agree queried tree.representative position
    · by_cases newSlot : queried.digit position = key.digit position
      · have absent : tree.lookup queried = none := valid.lookup_none_of_digit queried before
          (by simpa only [newSlot] using different)
        simp [split, lookup, prefixMatch, newSlot, lookupOption, same, absent]
      · by_cases oldSlot : queried.digit position = tree.representative.digit position
        · simp [split, lookup, prefixMatch, oldSlot, different.symm, lookupOption]
        · have absent := valid.lookup_none_of_digit queried before oldSlot
          simp [split, lookup, prefixMatch, Function.update_of_ne newSlot,
            Function.update_of_ne oldSlot, lookupOption, absent]
    · have absent := valid.lookup_none_of_prefix queried (Nat.le_of_lt before) prefixMatch
      simp [split, lookup, prefixMatch, absent]

/-- Immutable insertion has the ordinary finite-map update law, including
replacement of the newest value for an existing exact full key. -/
theorem lookup_insert (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (value : α) (queried : Key) :
    (tree.insert key value).lookup queried =
      if queried = key then some value else tree.lookup queried := by
  induction tree using inductionOnChildren with
  | leaf old previous =>
      by_cases different : key.divergence old < 16
      · simpa only [insert, if_pos different] using
          lookup_split (.leaf old previous) valid key value (key.divergence old) different
            (Key.divergence_spec key old).2.1
            ((Key.divergence_spec key old).2.2 different) queried
      · have same : key = old := (Key.divergence_eq_sixteen_iff key old).mp
          (by have bound := (Key.divergence_spec key old).1; omega)
        by_cases queriedSame : queried = old <;> simp [insert, lookup, same, queriedSame]
  | branch old position children ih =>
      by_cases different : key.divergence old < position
      · have bound : key.divergence old < 16 := lt_trans different valid.1
        simpa only [insert, if_pos different] using
          lookup_split (.branch old position children) valid key value (key.divergence old)
            different (Key.divergence_spec key old).2.1
            ((Key.divergence_spec key old).2.2 bound) queried
      · have keyPrefix : Key.Agree key old position :=
          (Key.divergence_spec key old).2.1.mono (by omega)
        by_cases same : queried = key
        · subst queried
          simp only [insert, if_neg different, lookup, if_pos keyPrefix, Function.update_self,
            lookupOption]
          cases read : children (key.digit position) with
          | none => simp [insertOption, lookup]
          | some child =>
              simpa [insertOption, lookupOption] using
                ih _ child read (valid.child read).1
        · simp only [insert, if_neg different, if_neg same]
          by_cases prefixMatch : Key.Agree queried old position
          · by_cases slot : queried.digit position = key.digit position
            · simp only [lookup, if_pos prefixMatch, slot, Function.update_self, lookupOption]
              cases read : children (key.digit position) with
              | none => simp [insertOption, lookup, lookupOption, same]
              | some child =>
                  simpa only [insertOption, lookupOption, if_neg same] using
                    ih _ child read (valid.child read).1
            · simp [lookup, prefixMatch, Function.update_of_ne slot]
          · simp [lookup, prefixMatch]

@[simp] theorem lookup_insert_self (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (value : α) : (tree.insert key value).lookup key = some value := by
  simp [lookup_insert tree valid]

theorem lookup_insert_other (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (value : α) {queried : Key} (different : queried ≠ key) :
    (tree.insert key value).lookup queried = tree.lookup queried := by
  simp [lookup_insert tree valid, different]

@[simp] theorem representative_insert (tree : CompressedTrie α) (key : Key) (value : α) :
    (tree.insert key value).representative = tree.representative := by
  cases tree with
  | leaf old previous =>
      by_cases different : key.divergence old < 16
      · simp [insert, different, split, representative]
      · have same : key = old := (Key.divergence_eq_sixteen_iff key old).mp
          (by have bound := (Key.divergence_spec key old).1; omega)
        simp [insert, same, representative]
  | branch old position children =>
      by_cases different : key.divergence old < position <;>
        simp [insert, different, split, representative]

theorem depth_insert (tree : CompressedTrie α) (key : Key) (value : α) :
    (tree.insert key value).depth = min tree.depth (key.divergence tree.representative) := by
  cases tree with
  | leaf old previous =>
      by_cases different : key.divergence old < 16
      · simp [insert, different, split, depth, representative,
          Nat.min_eq_right (Nat.le_of_lt different)]
      · have full : key.divergence old = 16 := by
          have bound := (Key.divergence_spec key old).1
          omega
        simp [insert, full, depth, representative]
  | branch old position children =>
      by_cases different : key.divergence old < position
      · simp [insert, different, split, depth, representative,
          Nat.min_eq_right (Nat.le_of_lt different)]
      · have bound : position ≤ key.divergence old := by omega
        simp [insert, different, depth, representative, Nat.min_eq_left bound]

theorem depth_insert_ge (tree : CompressedTrie α) (key : Key) (value : α) {lower : Nat}
    (before : lower ≤ tree.depth) (finite : lower ≤ 16)
    (agree : Key.Agree key tree.representative lower) :
    lower ≤ (tree.insert key value).depth := by
  rw [depth_insert]
  exact le_min before (agree.le_divergence finite)

private theorem wellFormed_branch (key : Key) (position : Nat)
    (children : Digit → Option (CompressedTrie α)) (finite : position < 16)
    (representativePresent : ∃ child,
      children (key.digit position) = some child ∧ child.representative = key)
    (branching : ∃ left right,
      left ≠ right ∧ (children left).isSome ∧ (children right).isSome)
    (routed : ∀ digit child, children digit = some child →
      child.WellFormed ∧ position < child.depth ∧
        child.AllKeys (fun descendant =>
          Key.Agree descendant key position ∧ descendant.digit position = digit)) :
    WellFormed (.branch key position children) := by
  refine ⟨finite, representativePresent, branching, ?_⟩
  intro digit
  cases read : children digit with
  | none => trivial
  | some child => simpa only [wellFormedChild] using routed digit child read

theorem wellFormed_split (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (value : α) (position : Nat)
    (before : position < tree.depth) (agree : Key.Agree key tree.representative position)
    (different : key.digit position ≠ tree.representative.digit position) :
    (tree.split key value position).WellFormed := by
  apply wellFormed_branch
  · exact lt_of_lt_of_le before valid.depth_le
  · refine ⟨tree, ?_, rfl⟩
    rw [Function.update_of_ne different.symm, Function.update_self]
  · refine ⟨key.digit position, tree.representative.digit position, different, ?_, ?_⟩
    · simp only [Function.update_self, Option.isSome_some]
    · rw [Function.update_of_ne different.symm, Function.update_self]
      rfl
  · intro digit child read
    by_cases newSlot : digit = key.digit position
    · subst digit
      rw [Function.update_self] at read
      cases Option.some.inj read
      refine ⟨trivial, lt_of_lt_of_le before valid.depth_le, ?_⟩
      intro descendant present
      cases present
      exact ⟨agree, rfl⟩
    · rw [Function.update_of_ne newSlot] at read
      by_cases oldSlot : digit = tree.representative.digit position
      · subst digit
        rw [Function.update_self] at read
        cases Option.some.inj read
        refine ⟨valid, before, ?_⟩
        intro descendant present
        have shared := valid.allKeys_agree descendant present
        exact ⟨shared.mono (Nat.le_of_lt before), shared.at before⟩
      · simp [Function.update_of_ne oldSlot] at read

private theorem isSome_update {β : Type*} (children : Digit → Option β)
    (slot digit : Digit) (replacement : β) (present : (children digit).isSome) :
    (Function.update children slot (some replacement) digit).isSome := by
  by_cases selected : digit = slot
  · subst digit
    simp
  · simpa only [Function.update_of_ne selected] using present

/-- Compression invariants are preserved by the actual insertion algorithm.
In particular, representatives remain actual descendants through the local
representative-child law, and no unary branch is introduced. -/
theorem wellFormed_insert (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (value : α) : (tree.insert key value).WellFormed := by
  induction tree using inductionOnChildren with
  | leaf old previous =>
      by_cases different : key.divergence old < 16
      · simpa only [insert, if_pos different] using
          wellFormed_split (.leaf old previous) valid key value (key.divergence old) different
            (Key.divergence_spec key old).2.1
            ((Key.divergence_spec key old).2.2 different)
      · simp only [insert, if_neg different, WellFormed]
  | branch old position children ih =>
      by_cases different : key.divergence old < position
      · have finite : key.divergence old < 16 := lt_trans different valid.1
        simpa only [insert, if_pos different] using
          wellFormed_split (.branch old position children) valid key value (key.divergence old)
            different (Key.divergence_spec key old).2.1
            ((Key.divergence_spec key old).2.2 finite)
      · have keyPrefix : Key.Agree key old position :=
          (Key.divergence_spec key old).2.1.mono (by omega)
        simp only [insert, if_neg different]
        apply wellFormed_branch old position _ valid.1
        · obtain ⟨child, read, representativeSame⟩ := valid.2.1
          by_cases selected : old.digit position = key.digit position
          · refine ⟨insertOption (children (key.digit position)) key value, ?_, ?_⟩
            · rw [selected, Function.update_self]
            · rw [← selected, read, insertOption, representative_insert, representativeSame]
          · exact ⟨child, by rw [Function.update_of_ne selected, read], representativeSame⟩
        · obtain ⟨left, right, distinct, leftPresent, rightPresent⟩ := valid.2.2.1
          exact ⟨left, right, distinct, isSome_update _ _ _ _ leftPresent,
            isSome_update _ _ _ _ rightPresent⟩
        · intro digit child read
          by_cases selected : digit = key.digit position
          · subst digit
            rw [Function.update_self] at read
            cases Option.some.inj read
            cases previousRead : children (key.digit position) with
            | none =>
                simp only [insertOption]
                refine ⟨trivial, valid.1, ?_⟩
                intro descendant present
                cases present
                exact ⟨keyPrefix, rfl⟩
            | some previous =>
                simp only [insertOption]
                have previousRoute := valid.child previousRead
                have representativeRoute := previousRoute.2.2 previous.representative
                  previousRoute.1.contains_representative
                have keyChildPrefix : Key.Agree key previous.representative (position + 1) :=
                  (keyPrefix.trans representativeRoute.1.symm).succ representativeRoute.2.symm
                refine ⟨ih _ previous previousRead previousRoute.1, ?_, ?_⟩
                · have nextDepth := depth_insert_ge previous key value
                    (Nat.succ_le_iff.mpr previousRoute.2.1) (by have bound := valid.1; omega)
                    keyChildPrefix
                  omega
                · exact allKeys_insert previous previousRoute.1 key value previousRoute.2.2
                    ⟨keyPrefix, rfl⟩
          · rw [Function.update_of_ne selected] at read
            exact valid.child read

theorem lookupOption_insertOption (root : Option (CompressedTrie α))
    (valid : ∀ tree, root = some tree → tree.WellFormed)
    (key : Key) (value : α) (queried : Key) :
    (insertOption root key value).lookup queried =
      if queried = key then some value else lookupOption root queried := by
  cases root with
  | none => simp [insertOption, lookup, lookupOption]
  | some tree =>
      simpa only [insertOption, lookupOption] using
        lookup_insert tree (valid tree rfl) key value queried

theorem wellFormed_insertOption (root : Option (CompressedTrie α))
    (valid : ∀ tree, root = some tree → tree.WellFormed) (key : Key) (value : α) :
    (insertOption root key value).WellFormed := by
  cases root with
  | none => trivial
  | some tree => exact wellFormed_insert tree (valid tree rfl) key value

mutual
  /-- Number of new index nodes allocated by immutable insertion. A split
  allocates a branch and leaf and retains the entire old subtree. -/
  def insertNodes : CompressedTrie α → Key → Nat
    | .leaf old _, key => if key.divergence old < 16 then 2 else 1
    | .branch old position children, key =>
        if key.divergence old < position then 2
        else 1 + insertOptionNodes (children (key.digit position)) key

  def insertOptionNodes : Option (CompressedTrie α) → Key → Nat
    | none, _ => 1
    | some tree, key => tree.insertNodes key
end

theorem insertNodes_le_lookupSteps (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) : tree.insertNodes key ≤ tree.lookupSteps key + 1 := by
  induction tree using inductionOnChildren with
  | leaf old previous =>
      by_cases different : key.divergence old < 16 <;> simp [insertNodes, lookupSteps, different]
  | branch old position children ih =>
      by_cases different : key.divergence old < position
      · have rejected : ¬ Key.Agree key old position := by
          intro agree
          have before := agree.le_divergence (Nat.le_of_lt valid.1)
          omega
        simp [insertNodes, different, lookupSteps, rejected]
      · have keyPrefix : Key.Agree key old position :=
          (Key.divergence_spec key old).2.1.mono (by omega)
        simp only [insertNodes, if_neg different, lookupSteps, if_pos keyPrefix]
        cases read : children (key.digit position) with
        | none => simp [insertOptionNodes, lookupOptionSteps]
        | some child =>
            have bound := ih _ child read (valid.child read).1
            simp only [insertOptionNodes, lookupOptionSteps]
            omega

/-- A route already sharing `lower` digits has at most the remaining radix
budget for copied nodes, including a possible new splitting branch and leaf. -/
theorem insertNodes_le_from (tree : CompressedTrie α) (valid : tree.WellFormed)
    (key : Key) (lower : Nat) (before : lower ≤ tree.depth) (finite : lower ≤ 16)
    (agree : Key.Agree key tree.representative lower) :
    tree.insertNodes key ≤ 17 - lower := by
  induction tree using inductionOnChildren generalizing lower with
  | leaf old previous =>
      by_cases different : key.divergence old < 16
      · have shared : lower ≤ key.divergence old := agree.le_divergence finite
        simp only [insertNodes, if_pos different]
        omega
      · simp only [insertNodes, if_neg different]
        omega
  | branch old position children ih =>
      by_cases different : key.divergence old < position
      · simp only [insertNodes, if_pos different]
        have rootBound : position < 16 := valid.1
        change lower ≤ position at before
        omega
      · have keyPrefix : Key.Agree key old position :=
          (Key.divergence_spec key old).2.1.mono (by omega)
        simp only [insertNodes, if_neg different]
        cases read : children (key.digit position) with
        | none =>
            simp only [insertOptionNodes]
            have rootBound : position < 16 := valid.1
            change lower ≤ position at before
            omega
        | some child =>
            simp only [insertOptionNodes]
            have routed := valid.child read
            have representativeRoute := routed.2.2 child.representative
              routed.1.contains_representative
            have keyChildPrefix : Key.Agree key child.representative (position + 1) :=
              (keyPrefix.trans representativeRoute.1.symm).succ representativeRoute.2.symm
            have childBound := ih _ child read routed.1 (position + 1)
              (Nat.succ_le_iff.mpr routed.2.1) (by have bound := valid.1; omega) keyChildPrefix
            change lower ≤ position at before
            have rootBound : position < 16 := valid.1
            omega

theorem insertNodes_le (tree : CompressedTrie α) (valid : tree.WellFormed) (key : Key) :
    tree.insertNodes key ≤ 17 := by
  apply insertNodes_le_from tree valid key 0 (Nat.zero_le _) (by decide)
  intro position
  exact Fin.elim0 position

namespace Controls

private def zeroKey : Key := ⟨List.replicate 16 0, by simp⟩
private def lastOneKey : Key := ⟨List.replicate 15 0 ++ [1], by simp⟩
private def prefixOneKey : Key := ⟨1 :: List.replicate 15 0, by simp⟩

private def first : CompressedTrie Nat := .leaf zeroKey 10
private def second : CompressedTrie Nat := first.insert lastOneKey 20
private def updated : CompressedTrie Nat := second.insert zeroKey 70

private theorem first_valid : first.WellFormed := trivial
private theorem second_valid : second.WellFormed := wellFormed_insert first first_valid _ _

theorem late_split_and_exact_values :
    second.depth = 15 ∧ second.lookup zeroKey = some 10 ∧
      second.lookup lastOneKey = some 20 ∧ second.lookupSteps zeroKey = 2 := by
  decide

theorem newest_value_preserves_sibling_and_old_snapshot :
    updated.WellFormed ∧ updated.lookup zeroKey = some 70 ∧
      updated.lookup lastOneKey = some 20 ∧ first.lookup zeroKey = some 10 := by
  refine ⟨wellFormed_insert second second_valid _ _, ?_⟩
  decide

theorem skipped_prefix_miss_examines_one_node :
    second.lookup prefixOneKey = none ∧ second.lookupSteps prefixOneKey = 1 := by
  decide

theorem single_leaf_and_replacement_allocate_one_node :
    first.lookupSteps zeroKey = 1 ∧ first.insertNodes zeroKey = 1 ∧
      first.insertNodes lastOneKey = 2 := by
  decide

theorem unary_branch_is_invalid :
    ¬ WellFormed (.branch zeroKey 0 (fun digit =>
      if digit = 0 then some first else none)) := by
  intro valid
  obtain ⟨left, right, distinct, leftPresent, rightPresent⟩ := valid.2.2.1
  have leftZero : left = 0 := by
    by_contra different
    simp [different] at leftPresent
  have rightZero : right = 0 := by
    by_contra different
    simp [different] at rightPresent
  exact distinct (leftZero.trans rightZero.symm)

theorem wrong_representative_child_is_invalid :
    ¬ WellFormed (.branch zeroKey 15
      (Function.update (Function.update (fun _ => none) 0
        (some (.leaf lastOneKey 10))) 1 (some first))) := by
  intro valid
  obtain ⟨child, read, same⟩ := valid.2.1
  have selected : zeroKey.digit 15 = 0 := by decide
  rw [selected] at read
  simp only [Function.update_of_ne (by decide : (0 : Digit) ≠ 1), Function.update_self] at read
  cases Option.some.inj read
  exact (by decide : lastOneKey ≠ zeroKey) same

end Controls

end CompressedTrie

section HeapRefinement

variable {Origin Value StableFault : Type*}

/-- The derived index is observed only through exact-key lookup. The same
contract covers compressed and uncompressed representations; the heap's
persistent semantic update spine is independent of either representation. -/
def Consistent
    (keyOf : CellId → Option Key)
    (heap : Heap Origin Value StableFault)
    (lookupKey : Key → Option (CellRecord Origin Value StableFault)) : Prop :=
  ∀ cell, (keyOf cell).bind lookupKey = heap.lookup cell

/-- A finite native key space need distinguish only its assigned source cells. -/
def AssignedKeysUnique (keyOf : CellId → Option Key) : Prop :=
  ∀ {left right key}, keyOf left = some key → keyOf right = some key → left = right

/-- Availability is a semantic premise. A native allocator must derive it
from its finite assignment inventory; arbitrary function-valued assignments
do not provide a decision procedure. -/
def KeyAvailable (keyOf : CellId → Option Key) (key : Key) : Prop :=
  ∀ cell, keyOf cell ≠ some key

def assignKey (keyOf : CellId → Option Key) (cell : CellId) (key : Key) :
    CellId → Option Key :=
  Function.update keyOf cell (some key)

@[simp] theorem assignKey_same (keyOf : CellId → Option Key) (cell : CellId) (key : Key) :
    assignKey keyOf cell key cell = some key :=
  Function.update_self _ _ _

theorem assignKey_other (keyOf : CellId → Option Key) (cell : CellId) (key : Key)
    {other : CellId} (distinct : other ≠ cell) :
    assignKey keyOf cell key other = keyOf other :=
  Function.update_of_ne distinct _ _

theorem assignKey_preserves_unique {keyOf : CellId → Option Key}
    (unique : AssignedKeysUnique keyOf) {cell : CellId} {key : Key}
    (available : KeyAvailable keyOf key) :
    AssignedKeysUnique (assignKey keyOf cell key) := by
  intro left right selected leftRead rightRead
  by_cases leftSame : left = cell
  · subst left
    rw [assignKey_same] at leftRead
    have selectedSame : selected = key := (Option.some.inj leftRead).symm
    subst selected
    by_cases rightSame : right = cell
    · exact rightSame.symm
    · rw [assignKey_other keyOf cell key rightSame] at rightRead
      exact False.elim (available right rightRead)
  · rw [assignKey_other keyOf cell key leftSame] at leftRead
    by_cases rightSame : right = cell
    · subst right
      rw [assignKey_same] at rightRead
      have selectedSame : selected = key := (Option.some.inj rightRead).symm
      subst selected
      exact False.elim (available left leftRead)
    · rw [assignKey_other keyOf cell key rightSame] at rightRead
      exact unique leftRead rightRead

theorem empty_keys_unique : AssignedKeysUnique (fun _ => none) := by
  intro left right key impossible
  contradiction

theorem empty_consistent
    {lookupKey : Key → Option (CellRecord Origin Value StableFault)} :
    Consistent (fun _ => none) (Heap.empty : Heap Origin Value StableFault)
      lookupKey := by
  intro cell
  rfl

theorem lookup_refines
    {keyOf : CellId → Option Key}
    {heap : Heap Origin Value StableFault}
    {lookupKey : Key → Option (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap lookupKey)
    (cell : CellId) :
    (keyOf cell).bind lookupKey = heap.lookup cell :=
  consistent cell

theorem unassigned_lookup_none {keyOf : CellId → Option Key}
    {heap : Heap Origin Value StableFault}
    {lookupKey : Key → Option (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap lookupKey) {cell : CellId}
    (unassigned : keyOf cell = none) : heap.lookup cell = none := by
  simpa [unassigned] using (consistent cell).symm

theorem setKnownCache_preserves_consistency
    {keyOf : CellId → Option Key}
    (unique : AssignedKeysUnique keyOf)
    {heap : Heap Origin Value StableFault}
    {before after : Key → Option (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap before)
    (cell : CellId) (key : Key) (assigned : keyOf cell = some key)
    (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault)
    (updated : ∀ queried, after queried =
      if queried = key then some { record with cache := state } else before queried) :
    Consistent keyOf
      (heap.setKnownCache cell record state)
      after := by
  intro other
  by_cases hCell : other = cell
  · subst other
    simp [assigned, updated]
  · rw [Heap.setKnownCache_preserves_other _ _ _ hCell, ← consistent other]
    cases otherRead : keyOf other with
    | none => rfl
    | some otherKey =>
        simp only [Option.bind_some]
        have different : otherKey ≠ key := by
          intro same
          subst otherKey
          exact hCell (unique otherRead assigned)
        exact (updated otherKey).trans (if_neg different)

theorem allocate_preserves_consistency
    {keyOf : CellId → Option Key}
    {heap next : Heap Origin Value StableFault}
    {before after : Key → Option (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap before)
    {cell : CellId} {key : Key} {origin : Origin}
    (available : KeyAvailable keyOf key)
    (allocated : heap.allocate? cell origin = some next)
    (updated : ∀ queried, after queried =
      if queried = key then some { origin := origin, cache := Cache.suspended }
      else before queried) :
    Consistent (assignKey keyOf cell key) next after := by
  intro other
  by_cases hCell : other = cell
  · subst other
    simp only [assignKey_same, Option.bind_some, updated]
    exact (Heap.allocate?_lookup_same allocated).symm
  · rw [assignKey_other keyOf cell key hCell,
      Heap.allocate?_preserves_other allocated hCell, ← consistent other]
    cases otherRead : keyOf other with
    | none => rfl
    | some otherKey =>
        simp only [Option.bind_some]
        have different : otherKey ≠ key := by
          intro same
          subst otherKey
          exact available other otherRead
        exact (updated otherKey).trans (if_neg different)

end HeapRefinement

namespace Controls

private def first : CellId := ⟨7, [], 1, 0⟩
private def second : CellId := ⟨7, [0], 1, 0⟩
private def unallocated : CellId := ⟨7, [1], 1, 0⟩
private def firstKey : Key := ⟨List.replicate 16 0, by simp⟩
private def secondKey : Key := ⟨List.replicate 16 1, by simp⟩

private theorem second_ne_first : second ≠ first := by decide
private theorem secondKey_ne_firstKey : secondKey ≠ firstKey := by decide

private def firstHeap : Heap Nat Nat Nat where
  current := Function.update (fun _ => none) first (some ⟨10, .suspended⟩)
  spine := [.allocate first 10]

private def secondHeap : Heap Nat Nat Nat where
  current := Function.update firstHeap.current second (some ⟨20, .suspended⟩)
  spine := .allocate second 20 :: firstHeap.spine

private def firstAssignment : CellId → Option Key :=
  assignKey (fun _ => none) first firstKey

private def secondAssignment : CellId → Option Key :=
  assignKey firstAssignment second secondKey

private def firstIndex : Trie (CellRecord Nat Nat Nat) :=
  Trie.empty.insertKey firstKey ⟨10, .suspended⟩

private def secondIndex : Trie (CellRecord Nat Nat Nat) :=
  firstIndex.insertKey secondKey ⟨20, .suspended⟩

private theorem first_allocated :
    (Heap.empty : Heap Nat Nat Nat).allocate? first 10 = some firstHeap := rfl

private theorem second_allocated :
    firstHeap.allocate? second 20 = some secondHeap := by
  simp only [Heap.allocate?, Heap.lookup, firstHeap,
    Function.update_of_ne second_ne_first]
  rfl

private theorem first_available : KeyAvailable (fun _ => none) firstKey := by
  intro cell
  simp

private theorem second_available : KeyAvailable firstAssignment secondKey := by
  intro cell
  by_cases same : cell = first
  · subst cell
    simpa [firstAssignment] using secondKey_ne_firstKey.symm
  · simp [firstAssignment, assignKey_other _ _ _ same]

theorem two_cells_consistent : Consistent secondAssignment secondHeap secondIndex.lookupKey := by
  have firstConsistent : Consistent firstAssignment firstHeap firstIndex.lookupKey :=
    allocate_preserves_consistency empty_consistent first_available first_allocated
      (Trie.lookupKey_insert _ _ _)
  exact allocate_preserves_consistency firstConsistent second_available second_allocated
    (Trie.lookupKey_insert _ _ _)

theorem two_cells_unique : AssignedKeysUnique secondAssignment :=
  assignKey_preserves_unique (assignKey_preserves_unique empty_keys_unique first_available)
    second_available

theorem sibling_births_have_distinct_keys :
    secondAssignment first = some firstKey ∧ secondAssignment second = some secondKey ∧
      firstKey ≠ secondKey := by
  simp [secondAssignment, firstAssignment,
    assignKey_other _ _ _ second_ne_first.symm, secondKey_ne_firstKey.symm]

theorem unallocated_reads_none : secondHeap.lookup unallocated = none :=
  unassigned_lookup_none two_cells_consistent (by
    simp [secondAssignment, firstAssignment, assignKey,
      show unallocated ≠ first by decide, show unallocated ≠ second by decide])

theorem cache_update_preserves_two_cells :
    Consistent secondAssignment
      (secondHeap.setKnownCache first ⟨10, .suspended⟩ (.value 70))
      (secondIndex.insertKey firstKey ⟨10, .value 70⟩).lookupKey :=
  setKnownCache_preserves_consistency two_cells_unique two_cells_consistent first firstKey
    sibling_births_have_distinct_keys.1 ⟨10, .suspended⟩ (.value 70)
    (Trie.lookupKey_insert _ _ _)

private def compressedFirst : CompressedTrie (CellRecord Nat Nat Nat) :=
  CompressedTrie.insertOption none firstKey ⟨10, .suspended⟩

private def compressedSecond : CompressedTrie (CellRecord Nat Nat Nat) :=
  compressedFirst.insert secondKey ⟨20, .suspended⟩

private theorem empty_compressed_valid :
    ∀ tree, (none : Option (CompressedTrie (CellRecord Nat Nat Nat))) = some tree →
      tree.WellFormed := by
  intro tree impossible
  contradiction

private theorem compressedFirst_valid : compressedFirst.WellFormed :=
  CompressedTrie.wellFormed_insertOption none empty_compressed_valid _ _

private theorem compressedSecond_valid : compressedSecond.WellFormed :=
  CompressedTrie.wellFormed_insert compressedFirst compressedFirst_valid _ _

/-- Both key assignments and both semantic allocation steps are shared with
the uncompressed consumer; only the exact-key lookup implementation changes. -/
theorem compressed_two_cells_consistent :
    Consistent secondAssignment secondHeap compressedSecond.lookup := by
  have firstConsistent : Consistent firstAssignment firstHeap compressedFirst.lookup :=
    allocate_preserves_consistency empty_consistent first_available first_allocated
      (CompressedTrie.lookupOption_insertOption none empty_compressed_valid _ _)
  exact allocate_preserves_consistency firstConsistent second_available second_allocated
    (CompressedTrie.lookup_insert compressedFirst compressedFirst_valid _ _)

theorem compressed_cache_update_preserves_two_cells :
    Consistent secondAssignment
      (secondHeap.setKnownCache first ⟨10, .suspended⟩ (.value 70))
      (compressedSecond.insert firstKey ⟨10, .value 70⟩).lookup :=
  setKnownCache_preserves_consistency two_cells_unique compressed_two_cells_consistent
    first firstKey sibling_births_have_distinct_keys.1 ⟨10, .suspended⟩ (.value 70)
    (CompressedTrie.lookup_insert compressedSecond compressedSecond_valid _ _)

theorem compressed_unallocated_reads_none : secondHeap.lookup unallocated = none :=
  unassigned_lookup_none compressed_two_cells_consistent (by
    simp [secondAssignment, firstAssignment, assignKey,
      show unallocated ≠ first by decide, show unallocated ≠ second by decide])

theorem reused_key_is_unavailable : ¬ KeyAvailable firstAssignment firstKey := by
  intro available
  exact available first (assignKey_same _ _ _)

theorem collision_breaks_consistency :
    ¬ Consistent (assignKey firstAssignment second firstKey) secondHeap
      (firstIndex.insertKey firstKey ⟨20, .suspended⟩).lookupKey := by
  intro consistent
  have wrong := consistent first
  have firstStill : assignKey firstAssignment second firstKey first = some firstKey := by
    rw [assignKey_other _ _ _ second_ne_first.symm]
    exact assignKey_same _ _ _
  have observed : secondHeap.lookup first = some ⟨10, .suspended⟩ := by
    simp [Heap.lookup, secondHeap, firstHeap, second_ne_first.symm]
  rw [firstStill, Option.bind_some, Trie.lookupKey_insert_self, observed] at wrong
  have impossible : (20 : Nat) = 10 := congrArg (fun record => record.origin)
    (Option.some.inj wrong)
  omega

theorem collision_also_breaks_compressed_consistency :
    ¬ Consistent (assignKey firstAssignment second firstKey) secondHeap
      (compressedFirst.insert firstKey ⟨20, .suspended⟩).lookup := by
  intro consistent
  have wrong := consistent first
  have firstStill : assignKey firstAssignment second firstKey first = some firstKey := by
    rw [assignKey_other _ _ _ second_ne_first.symm]
    exact assignKey_same _ _ _
  have observed : secondHeap.lookup first = some ⟨10, .suspended⟩ := by
    simp [Heap.lookup, secondHeap, firstHeap, second_ne_first.symm]
  rw [firstStill, Option.bind_some,
    CompressedTrie.lookup_insert_self _ compressedFirst_valid, observed] at wrong
  have impossible : (20 : Nat) = 10 := congrArg (fun record => record.origin)
    (Option.some.inj wrong)
  omega

end Controls

end Mettapedia.Machines.BranchLocalNeed.NeedHeapIndex
