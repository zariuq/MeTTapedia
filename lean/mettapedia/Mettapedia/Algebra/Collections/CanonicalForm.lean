import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lex
import Mathlib.Data.Sum.Order
import Mathlib.Logic.Relation
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Canonical forms of nested collections

A collection value is a tree. Leaves are atoms; a node has a kind and an
ordered list of children. A kind's laws (`KindLaws`) say what the order and the
repetitions of its children mean: `commutative` forgets the order, and
`idempotent` absorbs a later repetition of a child. The four combinations are
the four kinds of finite collection:

| commutative | idempotent | kind | children of the normal form |
|---|---|---|---|
| no | no | list (and expression) | as written |
| no | yes | insertion-ordered set | first occurrences, in order (`dedupFirst`) |
| yes | no | bag | sorted |
| yes | yes | set | first occurrences, sorted |

The laws act among the children of any node, at any depth (`Step`); equality
of values is the equivalence they generate (`Conv`).

* **Normal forms decide equality of values.** Normalizing bottom-up, with the
  children of commutative kinds sorted by an injective key, gives syntactically
  equal results exactly for equal values (`normalize_eq_iff`), recursively for
  nested collections. Any injective key decides equality.
* **Printing needs a key that is a function of the value.** Ordering children
  by their printed token sequences (`Term.serialize`, an injective printer)
  gives `canonical`, whose print depends only on the value and separates
  different values (`serialize_canonical_eq_iff`). An interning key, which
  numbers terms in the order a run first built them, also decides equality,
  yet two runs that built the same atoms in different orders print one bag
  differently (`Controls.intern_order_prints_history`).
* **Reading inverts printing.** Each kind has its own opening and closing
  token. A reader that checks each closing token against its opening reads
  every printed term back, at any depth (`Term.parseTerm_serialize`,
  `Term.read_serialize`), and refuses a closing token of another kind
  (`Controls.read_checks_closings`). On a flat collection of atoms the
  canonical order is the order of the atoms (`canonical_bag_leaves`,
  `canonical_set_leaves`), and two flat literals are equal exactly when their
  multisets, or their sets, are (`conv_bag_leaves_iff`, `conv_set_leaves_iff`).
* **Insertion-ordered sets.** `dedupFirst` satisfies the left-regular band laws
  `x x = x` and `x y x = x y` (`dedupFirst_idempotent`, `dedupFirst_band`).
  Absorbing later repetitions is the idempotent, non-commutative case of the
  theorem above.
* **Nothing is flattened.** No law removes a node or changes its kind: a bag
  inside a bag is not spliced, a singleton is not its element, and kinds are
  not identified (`Controls.no_flattening`). An expression is the lawless kind
  with its head as first child, so wrapped constructors are not conflated
  (`Controls.wrapped_not_conflated`).
* **Typing.** Types are atom types, homogeneous collections of a kind, and
  positional tuples (`Ty`, `HasType`). Every law preserves every type
  (`Step.hasType_iff`, `hasType_normalize_iff`), because only lawless kinds
  have tuple types. One ordered node is a tuple or a list according to its
  type (`Controls.tuple_or_list_by_typing`); positional typing is not
  invariant under permutation (`Controls.positional_not_permutable`), and a
  singleton law would break typing (`Controls.singleton_law_breaks_typing`).
* **Open terms.** Instantiation needs one renormalization and no more
  (`normalize_bind_normalize`). An open normal form is not stable under
  instantiation: instances of a variable and an atom may compare in either
  order, and instances of distinct variables may coincide
  (`Controls.instance_unsorted`, `Controls.instance_collapses`). Open normal
  forms decide equality in every instance exactly when the occurring
  variables can be instantiated injectively by atoms that do not occur
  (`conv_iff_forall_instances`), which infinitely many atoms always allow
  (`conv_iff_forall_instances_of_infinite`); over one atom, the open sets
  `{x, y}` and `{x}` agree in every instance (`Controls.few_atoms_identify`).

`GSLT.LanguageDef.BagNormalForm.normalForm_eq_of_equationEquiv` proves the
forward half of such a theorem for MeTTaIL patterns under a bag theory whose
laws may also flatten nested bags and collapse singletons, and its section half
needs a bare-representation premise. The kinds here have no law that changes a
node's kind or removes a node, so both halves hold and every type is
preserved with no representation premise.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.CanonicalForm

universe u v w x

/-- The laws of the children of one kind of node. -/
structure KindLaws where
  /-- The order of the children is forgotten. -/
  commutative : Bool
  /-- A later repetition of a child is absorbed. -/
  idempotent : Bool
  deriving DecidableEq, Repr

namespace KindLaws

/-- Lists, and expressions: order and repetition are kept. -/
def list : KindLaws := ⟨false, false⟩

/-- Insertion-ordered sets: first occurrences, in order. -/
def insertionOrderedSet : KindLaws := ⟨false, true⟩

/-- Bags: order forgotten, multiplicity kept. -/
def bag : KindLaws := ⟨true, false⟩

/-- Sets: order and multiplicity forgotten. -/
def set : KindLaws := ⟨true, true⟩

end KindLaws

/-- Nested collection terms: atoms at the leaves; a node is a kind with an
ordered list of children. -/
inductive Term (K : Type u) (α : Type v) : Type (max u v) where
  | leaf : α → Term K α
  | node : K → List (Term K α) → Term K α

namespace Term

variable {K : Type u} {α : Type v} {β : Type w} {γ : Type x}

/-- Induction with a hypothesis for every child of a node. -/
@[elab_as_elim]
theorem induction {motive : Term K α → Prop} (leaf : ∀ a, motive (.leaf a))
    (node : ∀ k children, (∀ child ∈ children, motive child) → motive (.node k children))
    (t : Term K α) : motive t :=
  Term.rec (motive_1 := motive) (motive_2 := fun children => ∀ child ∈ children, motive child)
    leaf node (fun _ member => by cases member)
    (fun head tail headHolds tailHolds child member => by
      rcases List.mem_cons.mp member with rfl | inTail
      · exact headHolds
      · exact tailHolds child inTail) t

mutual
  def map (f : α → β) : Term K α → Term K β
    | .leaf a => .leaf (f a)
    | .node k children => .node k (mapList f children)

  def mapList (f : α → β) : List (Term K α) → List (Term K β)
    | [] => []
    | t :: ts => map f t :: mapList f ts
end

@[simp] theorem mapList_eq (f : α → β) (ts : List (Term K α)) :
    mapList f ts = ts.map (map f) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [mapList, ih]

@[simp] theorem map_leaf (f : α → β) (a : α) : (Term.leaf a : Term K α).map f = .leaf (f a) :=
  rfl

@[simp] theorem map_node (f : α → β) (k : K) (children : List (Term K α)) :
    (Term.node k children).map f = .node k (children.map (map f)) := by
  simp [map]

theorem map_map (f : α → β) (g : β → γ) (t : Term K α) :
    (t.map f).map g = t.map (g ∘ f) := by
  induction t using Term.induction with
  | leaf a => rfl
  | node k children ih =>
      simp only [map_node, List.map_map, node.injEq, true_and]
      exact List.map_congr_left fun child member => ih child member

theorem map_id' (t : Term K α) : t.map id = t := by
  induction t using Term.induction with
  | leaf a => rfl
  | node k children ih =>
      simp only [map_node, node.injEq, true_and]
      exact (List.map_congr_left fun child member => ih child member).trans (List.map_id _)

mutual
  /-- The atoms at the leaves, in order. -/
  def leaves : Term K α → List α
    | .leaf a => [a]
    | .node _ children => leavesList children

  def leavesList : List (Term K α) → List α
    | [] => []
    | t :: ts => leaves t ++ leavesList ts
end

@[simp] theorem leavesList_eq (ts : List (Term K α)) :
    leavesList ts = ts.flatMap leaves := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [leavesList, ih]

@[simp] theorem leaves_leaf (a : α) : (Term.leaf a : Term K α).leaves = [a] := rfl

@[simp] theorem leaves_node (k : K) (children : List (Term K α)) :
    (Term.node k children).leaves = children.flatMap leaves := by
  simp [leaves]

/-- A map is determined by its values at the leaves. -/
theorem map_congr {f g : α → β} (t : Term K α) (agree : ∀ a ∈ t.leaves, f a = g a) :
    t.map f = t.map g := by
  induction t using Term.induction with
  | leaf a => simp [agree a (by simp)]
  | node k children ih =>
      simp only [map_node, node.injEq, true_and]
      apply List.map_congr_left
      intro child member
      exact ih child member fun a inChild =>
        agree a (by simpa using ⟨child, member, inChild⟩)

theorem map_injective {f : α → β} (injective : Function.Injective f) :
    Function.Injective (map (K := K) f) := by
  intro s
  induction s using Term.induction with
  | leaf a =>
      intro t same
      cases t with
      | leaf b => simp only [map_leaf, leaf.injEq] at same; rw [injective same]
      | node k children => simp at same
  | node k children ih =>
      intro t same
      cases t with
      | leaf b => simp at same
      | node k' children' =>
          simp only [map_node, node.injEq] at same
          obtain ⟨rfl, same⟩ := same
          congr 1
          induction children generalizing children' with
          | nil => cases children' with
            | nil => rfl
            | cons _ _ => simp at same
          | cons head tail inner =>
              cases children' with
              | nil => simp at same
              | cons head' tail' =>
                  simp only [List.map_cons, List.cons.injEq] at same
                  rw [ih head (by simp) same.1,
                    inner (fun child member => ih child (by simp [member])) tail' same.2]

mutual
  /-- Substitution of terms for leaves. -/
  def bind (σ : α → Term K β) : Term K α → Term K β
    | .leaf a => σ a
    | .node k children => .node k (bindList σ children)

  def bindList (σ : α → Term K β) : List (Term K α) → List (Term K β)
    | [] => []
    | t :: ts => bind σ t :: bindList σ ts
end

@[simp] theorem bindList_eq (σ : α → Term K β) (ts : List (Term K α)) :
    bindList σ ts = ts.map (bind σ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [bindList, ih]

@[simp] theorem bind_leaf (σ : α → Term K β) (a : α) : (Term.leaf a : Term K α).bind σ = σ a :=
  rfl

@[simp] theorem bind_node (σ : α → Term K β) (k : K) (children : List (Term K α)) :
    (Term.node k children).bind σ = .node k (children.map (bind σ)) := by
  simp [bind]

/-- Renaming leaves is substitution of leaves. -/
theorem map_eq_bind (f : α → β) (t : Term K α) : t.map f = t.bind (fun a => .leaf (f a)) := by
  induction t using Term.induction with
  | leaf a => rfl
  | node k children ih =>
      simp only [map_node, bind_node, node.injEq, true_and]
      exact List.map_congr_left fun child member => ih child member

end Term

/-! ## Printing as tokens -/

/-- The tokens of a printed collection term. -/
inductive Token (K : Type u) (α : Type v) : Type (max u v) where
  | opening : K → Token K α
  | closing : K → Token K α
  | atom : α → Token K α
  deriving DecidableEq

namespace Term

variable {K : Type u} {α : Type v}

mutual
  /-- The printed form of a term: a node is its kind's opening token, its
  children, and its kind's closing token. -/
  def serialize : Term K α → List (Token K α)
    | .leaf a => [.atom a]
    | .node k children => .opening k :: (serializeList children ++ [.closing k])

  def serializeList : List (Term K α) → List (Token K α)
    | [] => []
    | t :: ts => serialize t ++ serializeList ts
end

@[simp] theorem serialize_leaf (a : α) : (Term.leaf a : Term K α).serialize = [.atom a] := rfl

@[simp] theorem serialize_node (k : K) (children : List (Term K α)) :
    (Term.node k children).serialize = .opening k :: (serializeList children ++ [.closing k]) := by
  simp [serialize]

@[simp] theorem serializeList_nil : serializeList ([] : List (Term K α)) = [] := rfl

@[simp] theorem serializeList_cons (t : Term K α) (ts : List (Term K α)) :
    serializeList (t :: ts) = t.serialize ++ serializeList ts := rfl

/-- A printed term never starts with a closing token. -/
theorem serialize_head (t : Term K α) :
    ∃ token rest, t.serialize = token :: rest ∧ ∀ k, token ≠ .closing k := by
  cases t with
  | leaf a => exact ⟨.atom a, [], rfl, by simp⟩
  | node k children => exact ⟨.opening k, _, serialize_node k children, by simp⟩

/-- Printing is a prefix code: a printed term is recovered from the front of
any token sequence that starts with it. -/
theorem serialize_append_inj (s : Term K α) :
    ∀ (t : Term K α) (rest rest' : List (Token K α)),
      s.serialize ++ rest = t.serialize ++ rest' → s = t ∧ rest = rest' := by
  induction s using Term.induction with
  | leaf a =>
      intro t rest rest' same
      cases t with
      | leaf b =>
          simp only [serialize_leaf, List.cons_append, List.nil_append, List.cons.injEq,
            Token.atom.injEq] at same
          exact ⟨by rw [same.1], same.2⟩
      | node k children => simp at same
  | node k children ih =>
      intro t rest rest' same
      cases t with
      | leaf b => simp at same
      | node k' children' =>
          simp only [serialize_node, List.cons_append, List.append_assoc, List.cons.injEq,
            Token.opening.injEq] at same
          obtain ⟨rfl, same⟩ := same
          suffices list : ∀ (cs ds : List (Term K α)) (r r' : List (Token K α)),
              (∀ child ∈ cs, ∀ (t : Term K α) (rest rest' : List (Token K α)),
                child.serialize ++ rest = t.serialize ++ rest' → child = t ∧ rest = rest') →
              serializeList cs ++ Token.closing k :: r = serializeList ds ++ Token.closing k :: r' →
                cs = ds ∧ r = r' by
            obtain ⟨rfl, rfl⟩ := list children children' rest rest' ih same
            exact ⟨rfl, rfl⟩
          intro cs
          induction cs with
          | nil =>
              intro ds r r' _ same
              cases ds with
              | nil => simpa using same
              | cons d ds =>
                  obtain ⟨token, tail, printed, notClosing⟩ := serialize_head d
                  simp only [serializeList_nil, List.nil_append, serializeList_cons, printed,
                    List.cons_append, List.append_assoc, List.cons.injEq] at same
                  exact absurd same.1.symm (notClosing k)
          | cons c cs inner =>
              intro ds r r' heads same
              cases ds with
              | nil =>
                  obtain ⟨token, tail, printed, notClosing⟩ := serialize_head c
                  simp only [serializeList_cons, printed, List.cons_append, List.append_assoc,
                    serializeList_nil, List.nil_append, List.cons.injEq] at same
                  exact absurd same.1 (notClosing k)
              | cons d ds =>
                  simp only [serializeList_cons, List.append_assoc] at same
                  obtain ⟨rfl, tails⟩ := heads c (by simp) d _ _ same
                  obtain ⟨rfl, rfl⟩ := inner ds r r'
                    (fun child member => heads child (by simp [member])) tails
                  exact ⟨rfl, rfl⟩

theorem serialize_injective : Function.Injective (serialize (K := K) (α := α)) := by
  intro s t same
  exact (serialize_append_inj s t [] [] (by simpa using same)).1

instance [DecidableEq K] [DecidableEq α] : DecidableEq (Term K α) := fun s t =>
  decidable_of_iff (s.serialize = t.serialize) serialize_injective.eq_iff

theorem one_le_length_serialize (t : Term K α) : 1 ≤ t.serialize.length := by
  obtain ⟨token, rest, printed, _⟩ := serialize_head t
  simp [printed]

@[simp] theorem length_serializeList (ts : List (Term K α)) :
    (serializeList ts).length = (ts.map fun t => t.serialize.length).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [ih]

variable [DecidableEq K]

mutual
  /-- Read one printed term from the front of the input. The fuel bounds the
  nesting of the reading; the length of the input always suffices. -/
  def parseTerm : ℕ → List (Token K α) → Option (Term K α × List (Token K α))
    | 0, _ => none
    | _ + 1, .atom a :: rest => some (.leaf a, rest)
    | n + 1, .opening k :: rest =>
        (parseChildren k n rest).map fun read => (.node k read.1, read.2)
    | _ + 1, _ => none

  /-- Read children up to the closing token of the kind `k`; a closing token of
  another kind is refused. -/
  def parseChildren (k : K) : ℕ → List (Token K α) → Option (List (Term K α) × List (Token K α))
    | 0, _ => none
    | n + 1, tokens =>
        match tokens with
        | .closing k' :: rest => if k' = k then some ([], rest) else none
        | _ =>
            match parseTerm n tokens with
            | some (child, rest) =>
                (parseChildren k n rest).map fun read => (child :: read.1, read.2)
            | none => none
end

/-- **Reading inverts printing**, for nested terms of every kind, given fuel at
least the printed length. -/
theorem parseTerm_serialize (t : Term K α) :
    ∀ (fuel : ℕ) (rest : List (Token K α)), t.serialize.length ≤ fuel →
      parseTerm fuel (t.serialize ++ rest) = some (t, rest) := by
  induction t using Term.induction with
  | leaf a =>
      intro fuel rest enough
      obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by simp at enough; omega⟩
      rfl
  | node k children ih =>
      intro fuel rest enough
      suffices list : ∀ (cs : List (Term K α)),
          (∀ child ∈ cs, ∀ (fuel : ℕ) (rest : List (Token K α)),
            child.serialize.length ≤ fuel →
              parseTerm fuel (child.serialize ++ rest) = some (child, rest)) →
          ∀ (n : ℕ) (rest : List (Token K α)), (serializeList cs).length + 1 ≤ n →
            parseChildren k n (serializeList cs ++ Token.closing k :: rest) = some (cs, rest) by
        simp only [serialize_node, List.length_cons, List.length_append, List.length_nil]
          at enough
        obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
        simp only [serialize_node, List.cons_append, List.append_assoc, List.nil_append,
          parseTerm]
        rw [list children ih n rest (by omega)]
        rfl
      intro cs
      induction cs with
      | nil =>
          intro _ n rest enough
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at enough; omega⟩
          simp [parseChildren]
      | cons c cs inner =>
          intro heads n rest enough
          have cLength := one_le_length_serialize c
          simp only [serializeList_cons, List.length_append] at enough
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          obtain ⟨token, tail, printed, notClosing⟩ := serialize_head c
          have childRead := heads c (by simp) m (serializeList cs ++ Token.closing k :: rest)
            (by omega)
          have restRead := inner (fun child member => heads child (by simp [member])) m rest
            (by omega)
          rw [serializeList_cons, List.append_assoc, printed, List.cons_append]
          rw [printed, List.cons_append] at childRead
          cases token with
          | closing k' => exact absurd rfl (notClosing k')
          | atom a =>
              simp only [parseChildren, childRead, restRead, Option.map_some]
          | opening k' =>
              simp only [parseChildren, childRead, restRead, Option.map_some]

/-- Read a whole printed term: one term and nothing after it. -/
def read (tokens : List (Token K α)) : Option (Term K α) :=
  match parseTerm tokens.length tokens with
  | some (t, []) => some t
  | _ => none

theorem read_serialize (t : Term K α) : read t.serialize = some t := by
  have parsed := parseTerm_serialize t t.serialize.length [] le_rfl
  rw [List.append_nil] at parsed
  simp [read, parsed]

end Term

namespace Token

variable {K : Type u} {α : Type v}

/-- Tokens embedded in a lexicographic sum, which orders them. -/
def embed : Token K α → K ⊕ₗ (K ⊕ₗ α)
  | .opening k => _root_.toLex (Sum.inl k)
  | .closing k => _root_.toLex (Sum.inr (_root_.toLex (Sum.inl k)))
  | .atom a => _root_.toLex (Sum.inr (_root_.toLex (Sum.inr a)))

theorem embed_injective : Function.Injective (embed (K := K) (α := α)) := by
  intro first second same
  cases first <;> cases second <;> simp_all [embed]

instance [LinearOrder K] [LinearOrder α] : LinearOrder (Token K α) :=
  LinearOrder.lift' embed embed_injective

end Token

/-! ## First occurrences -/

section Dedup

variable {β : Type w} [DecidableEq β]

/-- The first occurrence of each element, in order. -/
def dedupFirst : List β → List β
  | [] => []
  | a :: l => a :: (dedupFirst l).filter (fun b => decide (b ≠ a))

@[simp] theorem dedupFirst_nil : dedupFirst ([] : List β) = [] := rfl

theorem dedupFirst_cons (a : β) (l : List β) :
    dedupFirst (a :: l) = a :: (dedupFirst l).filter (fun b => decide (b ≠ a)) := rfl

@[simp] theorem mem_dedupFirst {b : β} {l : List β} : b ∈ dedupFirst l ↔ b ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [dedupFirst_cons, List.mem_cons, List.mem_filter, ih, List.mem_cons]
      by_cases same : b = a <;> simp [same]

theorem nodup_dedupFirst (l : List β) : (dedupFirst l).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [dedupFirst_cons, List.nodup_cons]
      exact ⟨by simp [List.mem_filter], ih.filter _⟩

theorem dedupFirst_of_nodup {l : List β} (nodup : l.Nodup) : dedupFirst l = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.nodup_cons] at nodup
      rw [dedupFirst_cons, ih nodup.2, List.filter_eq_self.mpr]
      intro b member
      simpa using fun same : b = a => nodup.1 (same ▸ member)

/-- The first occurrences of a concatenation: those of the first part, then
those of the second part that the first part lacks. -/
theorem dedupFirst_append (l₁ l₂ : List β) :
    dedupFirst (l₁ ++ l₂) =
      dedupFirst l₁ ++ (dedupFirst l₂).filter (fun b => decide (b ∉ l₁)) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
      rw [List.cons_append, dedupFirst_cons, ih, dedupFirst_cons, List.filter_append,
        List.filter_filter, List.cons_append]
      congr 2
      apply List.filter_congr
      intro b _
      by_cases same : b = a <;> simp [same]

/-- A later repetition of an element already present is absorbed. -/
theorem dedupFirst_append_cons_of_mem {l₁ : List β} {a : β} (member : a ∈ l₁) (l₂ : List β) :
    dedupFirst (l₁ ++ a :: l₂) = dedupFirst (l₁ ++ l₂) := by
  rw [dedupFirst_append, dedupFirst_append, dedupFirst_cons, List.filter_cons,
    if_neg (by simpa using member), List.filter_filter]
  congr 1
  apply List.filter_congr
  intro b _
  by_cases inside : b ∈ l₁
  · simp [inside]
  · have different : b ≠ a := fun same => inside (same ▸ member)
    simp [inside, different]

theorem dedupFirst_absorb (before middle after : List β) (a : β) :
    dedupFirst (before ++ a :: (middle ++ a :: after)) =
      dedupFirst (before ++ a :: (middle ++ after)) := by
  have regroup : ∀ rest : List β, before ++ a :: (middle ++ rest) =
      (before ++ a :: middle) ++ rest := by simp
  rw [regroup, regroup, dedupFirst_append_cons_of_mem (by simp)]

/-- **The left-regular band law** `x y x = x y`. -/
theorem dedupFirst_band (first second : List β) :
    dedupFirst (first ++ second ++ first) = dedupFirst (first ++ second) := by
  rw [dedupFirst_append (first ++ second) first, List.filter_eq_nil_iff.mpr, List.append_nil]
  intro b member
  have inFirst : b ∈ first := mem_dedupFirst.mp member
  simp [inFirst]

theorem dedupFirst_idempotent (l : List β) : dedupFirst (l ++ l) = dedupFirst l := by
  simpa using dedupFirst_band l []

theorem dedupFirst_perm {l l' : List β} (perm : l.Perm l') :
    (dedupFirst l).Perm (dedupFirst l') :=
  (List.perm_ext_iff_of_nodup (nodup_dedupFirst l) (nodup_dedupFirst l')).mpr fun b => by
    simpa using perm.mem_iff

end Dedup

/-! ## Sorting by a key -/

section Sorting

variable {β : Type w} {κ : Type x} [LinearOrder κ]

/-- Sort by a key. -/
def sortBy (key : β → κ) (l : List β) : List β :=
  l.insertionSort (fun first second => key first ≤ key second)

theorem sortBy_perm (key : β → κ) (l : List β) : (sortBy key l).Perm l :=
  List.perm_insertionSort _ l

theorem sortBy_pairwise (key : β → κ) (l : List β) :
    (sortBy key l).Pairwise (fun first second => key first ≤ key second) := by
  have : Std.Total (fun first second : β => key first ≤ key second) :=
    ⟨fun first second => le_total _ _⟩
  have : IsTrans β (fun first second => key first ≤ key second) :=
    ⟨fun _ _ _ firstLe secondLe => le_trans firstLe secondLe⟩
  exact List.pairwise_insertionSort _ l

/-- With an injective key, sorting depends only on the multiset sorted. -/
theorem sortBy_eq_of_perm {key : β → κ} (injective : Function.Injective key) {l l' : List β}
    (perm : l.Perm l') : sortBy key l = sortBy key l' := by
  have : Std.Antisymm (fun first second : β => key first ≤ key second) :=
    ⟨fun _ _ firstLe secondLe => injective (le_antisymm firstLe secondLe)⟩
  exact List.Perm.eq_of_pairwise' (sortBy_pairwise key l) (sortBy_pairwise key l')
    (((sortBy_perm key l).trans perm).trans (sortBy_perm key l').symm)

end Sorting

/-! ## The laws and the normal form -/

section Normalize

variable {K : Type u} {α : Type v}

/-- One law, applied among the children of a node or inside a child. -/
inductive Step (laws : K → KindLaws) : Term K α → Term K α → Prop
  /-- Commutative kinds: two adjacent children trade places. -/
  | swap {k : K} (commutative : (laws k).commutative = true) (before after : List (Term K α))
      (first second : Term K α) :
      Step laws (.node k (before ++ first :: second :: after))
        (.node k (before ++ second :: first :: after))
  /-- Idempotent kinds: a later repetition of a child is absorbed. -/
  | absorb {k : K} (idempotent : (laws k).idempotent = true)
      (before middle after : List (Term K α)) (child : Term K α) :
      Step laws (.node k (before ++ child :: (middle ++ child :: after)))
        (.node k (before ++ child :: (middle ++ after)))
  /-- A law inside a child. -/
  | inside (k : K) (before after : List (Term K α)) {first second : Term K α} :
      Step laws first second →
        Step laws (.node k (before ++ first :: after)) (.node k (before ++ second :: after))

/-- The equality of collection values: the equivalence generated by the laws. -/
def Conv (laws : K → KindLaws) : Term K α → Term K α → Prop :=
  Relation.EqvGen (Step laws)

namespace Conv

variable {laws : K → KindLaws}

theorem refl (t : Term K α) : Conv laws t t := Relation.EqvGen.refl t

theorem symm {s t : Term K α} (conv : Conv laws s t) : Conv laws t s :=
  Relation.EqvGen.symm _ _ conv

theorem trans {s t r : Term K α} (first : Conv laws s t) (second : Conv laws t r) :
    Conv laws s r :=
  Relation.EqvGen.trans _ _ _ first second

theorem of_step {s t : Term K α} (step : Step laws s t) : Conv laws s t :=
  Relation.EqvGen.rel _ _ step

/-- Convertible children give convertible nodes. -/
theorem inside (k : K) (before after : List (Term K α)) {first second : Term K α}
    (conv : Conv laws first second) :
    Conv laws (.node k (before ++ first :: after)) (.node k (before ++ second :: after)) := by
  induction conv with
  | rel _ _ step => exact of_step (.inside k before after step)
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Childwise convertible lists give convertible nodes. -/
theorem children (k : K) {cs ds : List (Term K α)} (related : List.Forall₂ (Conv laws) cs ds) :
    ∀ before : List (Term K α), Conv laws (.node k (before ++ cs)) (.node k (before ++ ds)) := by
  induction related with
  | nil => intro before; exact refl _
  | @cons c d cs ds head _ ih =>
      intro before
      have rest := ih (before ++ [d])
      simp only [List.append_assoc, List.singleton_append] at rest
      exact (inside k before cs head).trans rest

/-- In a commutative kind, permuted children give convertible nodes. -/
theorem perm {k : K} (commutative : (laws k).commutative = true) {cs ds : List (Term K α)}
    (permuted : cs.Perm ds) :
    ∀ before : List (Term K α), Conv laws (.node k (before ++ cs)) (.node k (before ++ ds)) := by
  induction permuted with
  | nil => intro before; exact refl _
  | cons head _ ih =>
      intro before
      simpa using ih (before ++ [head])
  | swap first second rest =>
      intro before
      exact of_step (.swap commutative before rest second first)
  | trans _ _ ih₁ ih₂ => intro before; exact (ih₁ before).trans (ih₂ before)

end Conv

variable [DecidableEq K] [DecidableEq α]

/-- In an idempotent kind, children convert to their first occurrences. -/
theorem Conv.dedupFirst_children {laws : K → KindLaws} {k : K}
    (idempotent : (laws k).idempotent = true) (cs : List (Term K α)) :
    ∀ before : List (Term K α), Conv laws (.node k (before ++ cs))
      (.node k (before ++ (dedupFirst cs).filter (fun c => decide (c ∉ before)))) := by
  induction cs with
  | nil => intro before; simpa using Conv.refl _
  | cons a cs ih =>
      intro before
      by_cases present : a ∈ before
      · obtain ⟨front, back, split⟩ := List.mem_iff_append.mp present
        have absorbed : Conv laws (.node k (before ++ a :: cs)) (.node k (before ++ cs)) := by
          have step := Step.absorb (laws := laws) idempotent front back cs a
          subst split
          simpa using Conv.of_step step
        refine absorbed.trans ((ih before).trans ?_)
        rw [dedupFirst_cons, List.filter_cons, if_neg (by simpa using present),
          List.filter_filter]
        have agree : (dedupFirst cs).filter (fun c => decide (c ∉ before) && decide (c ≠ a)) =
            (dedupFirst cs).filter (fun c => decide (c ∉ before)) := by
          apply List.filter_congr
          intro c _
          by_cases inside : c ∈ before
          · simp [inside]
          · have different : c ≠ a := fun same => inside (same ▸ present)
            simp [inside, different]
        rw [agree]
        exact Conv.refl _
      · have rest := ih (before ++ [a])
        simp only [List.append_assoc, List.singleton_append] at rest
        refine rest.trans ?_
        rw [dedupFirst_cons, List.filter_cons, if_pos (by simpa using present),
          List.filter_filter]
        have agree : (dedupFirst cs).filter (fun c => decide (c ∉ before ++ [a])) =
            (dedupFirst cs).filter (fun c => decide (c ∉ before) && decide (c ≠ a)) := by
          apply List.filter_congr
          intro c _
          by_cases same : c = a <;> simp [same]
        rw [agree]
        exact Conv.refl _

variable {κ : Type w} [LinearOrder κ]

/-- The children an idempotent kind keeps: their first occurrences. -/
def keep (laws : K → KindLaws) (k : K) (children : List (Term K α)) : List (Term K α) :=
  if (laws k).idempotent then dedupFirst children else children

/-- The children of a normal node of kind `k`, from normal children. -/
def arrange (laws : K → KindLaws) (key : Term K α → κ) (k : K)
    (children : List (Term K α)) : List (Term K α) :=
  if (laws k).commutative then sortBy key (keep laws k children) else keep laws k children

mutual
  /-- The normal form: children first, then each node arranged by its kind. -/
  def normalize (laws : K → KindLaws) (key : Term K α → κ) : Term K α → Term K α
    | .leaf a => .leaf a
    | .node k children => .node k (arrange laws key k (normalizeList laws key children))

  def normalizeList (laws : K → KindLaws) (key : Term K α → κ) :
      List (Term K α) → List (Term K α)
    | [] => []
    | t :: ts => normalize laws key t :: normalizeList laws key ts
end

variable (laws : K → KindLaws) (key : Term K α → κ)

@[simp] theorem normalizeList_eq (ts : List (Term K α)) :
    normalizeList laws key ts = ts.map (normalize laws key) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [normalizeList, ih]

@[simp] theorem normalize_leaf (a : α) : normalize laws key (.leaf a : Term K α) = .leaf a := rfl

@[simp] theorem normalize_node (k : K) (children : List (Term K α)) :
    normalize laws key (.node k children) =
      .node k (arrange laws key k (children.map (normalize laws key))) := by
  simp [normalize]

theorem Conv.arrange_children (k : K) (cs : List (Term K α)) :
    Conv laws (.node k cs) (.node k (arrange laws key k cs)) := by
  have kept : Conv laws (.node k cs) (.node k (keep laws k cs)) := by
    unfold keep
    split
    · next idempotent => simpa using Conv.dedupFirst_children idempotent cs []
    · exact Conv.refl _
  unfold arrange
  split
  · next commutative =>
      have sorted := Conv.perm commutative (sortBy_perm key (keep laws k cs)).symm []
      simp only [List.nil_append] at sorted
      exact kept.trans sorted
  · exact kept

/-- **Every term converts to its normal form.** -/
theorem conv_normalize (t : Term K α) : Conv laws t (normalize laws key t) := by
  induction t using Term.induction with
  | leaf a => exact Conv.refl _
  | node k children ih =>
      rw [normalize_node]
      have inner : Conv laws (.node k children) (.node k (children.map (normalize laws key))) := by
        simpa using Conv.children k (List.forall₂_map_right_iff.mpr
          (List.forall₂_same.mpr fun child member => ih child member)) []
      exact inner.trans (Conv.arrange_children laws key k _)

variable {laws key}

theorem arrange_perm (injective : Function.Injective key) {k : K}
    (commutative : (laws k).commutative = true) {cs ds : List (Term K α)}
    (permuted : cs.Perm ds) : arrange laws key k cs = arrange laws key k ds := by
  unfold arrange keep
  simp only [commutative, if_true]
  split
  · exact sortBy_eq_of_perm injective (dedupFirst_perm permuted)
  · exact sortBy_eq_of_perm injective permuted

theorem arrange_absorb {k : K} (idempotent : (laws k).idempotent = true)
    (before middle after : List (Term K α)) (child : Term K α) :
    arrange laws key k (before ++ child :: (middle ++ child :: after)) =
      arrange laws key k (before ++ child :: (middle ++ after)) := by
  unfold arrange keep
  simp only [idempotent, if_true, dedupFirst_absorb]

/-- Each law preserves the normal form. -/
theorem normalize_of_step (injective : Function.Injective key) {s t : Term K α}
    (step : Step laws s t) : normalize laws key s = normalize laws key t := by
  induction step with
  | swap commutative before after first second =>
      simp only [normalize_node, List.map_append, List.map_cons]
      rw [arrange_perm injective commutative]
      exact List.Perm.append_left _ (List.Perm.swap _ _ _)
  | absorb idempotent before middle after child =>
      simp only [normalize_node, List.map_append, List.map_cons]
      rw [arrange_absorb idempotent]
  | inside k before after _ ih =>
      simp only [normalize_node, List.map_append, List.map_cons, ih]

/-- **Normal forms decide the equality of collection values**: two terms have
the same normal form exactly when the laws convert one into the other, at any
depth, for every injective key. -/
theorem normalize_eq_iff (injective : Function.Injective key) {s t : Term K α} :
    normalize laws key s = normalize laws key t ↔ Conv laws s t := by
  constructor
  · intro same
    exact (conv_normalize laws key s).trans (same ▸ (conv_normalize laws key t).symm)
  · intro conv
    induction conv with
    | rel _ _ step => exact normalize_of_step injective step
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem normalize_normalize (injective : Function.Injective key) (t : Term K α) :
    normalize laws key (normalize laws key t) = normalize laws key t :=
  (normalize_eq_iff injective).mpr (conv_normalize laws key t).symm

end Normalize

/-! ## Canonical forms: ordered by the printed form -/

section Canonical

variable {K : Type u} {α : Type v} [LinearOrder K] [LinearOrder α]

/-- The canonical form: children ordered by their printed token sequences. -/
def canonical (laws : K → KindLaws) (t : Term K α) : Term K α :=
  normalize laws Term.serialize t

theorem canonical_eq_iff (laws : K → KindLaws) {s t : Term K α} :
    canonical laws s = canonical laws t ↔ Conv laws s t :=
  normalize_eq_iff Term.serialize_injective

/-- **The canonical print is a function of the value**, and it separates
different values. -/
theorem serialize_canonical_eq_iff (laws : K → KindLaws) {s t : Term K α} :
    (canonical laws s).serialize = (canonical laws t).serialize ↔ Conv laws s t :=
  Term.serialize_injective.eq_iff.trans (canonical_eq_iff laws)

instance (laws : K → KindLaws) : DecidableRel (Conv (α := α) laws) := fun s t =>
  decidable_of_iff (canonical laws s = canonical laws t) (canonical_eq_iff laws)

theorem Token.atom_le_atom_iff (a b : α) : (Token.atom a : Token K α) ≤ Token.atom b ↔ a ≤ b := by
  change Token.embed (Token.atom a : Token K α) ≤ Token.embed (Token.atom b) ↔ a ≤ b
  simp [Token.embed]

theorem Token.atom_lt_atom_iff (a b : α) : (Token.atom a : Token K α) < Token.atom b ↔ a < b := by
  change Token.embed (Token.atom a : Token K α) < Token.embed (Token.atom b) ↔ a < b
  simp [Token.embed]

theorem serialize_leaf_le_iff (a b : α) :
    (Term.leaf a : Term K α).serialize ≤ (Term.leaf b).serialize ↔ a ≤ b := by
  simp only [Term.serialize_leaf]
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, List.cons_lt_cons_iff]
  simp [Token.atom_lt_atom_iff]

/-- On atoms, the printed order is the order of the atoms. -/
theorem sortBy_serialize_leaves (l : List α) :
    sortBy Term.serialize (l.map (Term.leaf (K := K))) =
      (l.insertionSort (· ≤ ·)).map Term.leaf := by
  have : Std.Antisymm (fun first second : Term K α => first.serialize ≤ second.serialize) :=
    ⟨fun _ _ firstLe secondLe => Term.serialize_injective (le_antisymm firstLe secondLe)⟩
  apply List.Perm.eq_of_pairwise' (sortBy_pairwise _ _)
  · rw [List.pairwise_map]
    exact (List.pairwise_insertionSort (· ≤ ·) l).imp fun ordered =>
      (serialize_leaf_le_iff _ _).mpr ordered
  · exact (sortBy_perm _ _).trans ((List.perm_insertionSort _ l).map _).symm

theorem dedupFirst_map {β γ : Type*} [DecidableEq β] [DecidableEq γ] {f : β → γ}
    (injective : Function.Injective f) (l : List β) :
    dedupFirst (l.map f) = (dedupFirst l).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.map_cons, dedupFirst_cons, ih, dedupFirst_cons, List.map_cons, List.filter_map]
      congr 2
      apply List.filter_congr
      intro b _
      simp [injective.eq_iff]

/-- A flat bag of atoms prints sorted by the atoms. -/
theorem canonical_bag_leaves (laws : K → KindLaws) {k : K} (bag : laws k = KindLaws.bag)
    (l : List α) :
    canonical laws (.node k (l.map .leaf)) = .node k ((l.insertionSort (· ≤ ·)).map .leaf) := by
  simp only [canonical, normalize_node, List.map_map, Function.comp_def, normalize_leaf]
  simp only [arrange, keep, bag, KindLaws.bag, if_true, if_false, Bool.false_eq_true]
  exact congrArg _ (sortBy_serialize_leaves l)

/-- A flat set of atoms prints its distinct atoms sorted. -/
theorem canonical_set_leaves (laws : K → KindLaws) {k : K} (set : laws k = KindLaws.set)
    (l : List α) :
    canonical laws (.node k (l.map .leaf)) =
      .node k (((dedupFirst l).insertionSort (· ≤ ·)).map .leaf) := by
  simp only [canonical, normalize_node, List.map_map, Function.comp_def, normalize_leaf]
  simp only [arrange, keep, set, KindLaws.set, if_true]
  rw [show (l.map fun a => (Term.leaf a : Term K α)) = l.map Term.leaf from rfl,
    dedupFirst_map (fun _ _ same => by cases same; rfl)]
  exact congrArg _ (sortBy_serialize_leaves _)

/-- **Flat bag literals are equal exactly when their multisets are.** -/
theorem conv_bag_leaves_iff (laws : K → KindLaws) {k : K} (bag : laws k = KindLaws.bag)
    (first second : List α) :
    Conv laws (.node k (first.map .leaf)) (.node k (second.map .leaf)) ↔
      (first : Multiset α) = second := by
  rw [← canonical_eq_iff, canonical_bag_leaves laws bag, canonical_bag_leaves laws bag,
    Term.node.injEq, Multiset.coe_eq_coe]
  simp only [true_and]
  constructor
  · intro same
    have sorted := List.map_injective_iff.mpr (fun _ _ equal => Term.leaf.inj equal) same
    have firstSorted := List.perm_insertionSort (fun x y : α => x ≤ y) first
    rw [sorted] at firstSorted
    exact firstSorted.symm.trans (List.perm_insertionSort _ second)
  · intro permuted
    have : Std.Antisymm (fun first second : α => first ≤ second) :=
      ⟨fun _ _ firstLe secondLe => le_antisymm firstLe secondLe⟩
    rw [List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ first)
      (List.pairwise_insertionSort _ second)
      (((List.perm_insertionSort _ first).trans permuted).trans
        (List.perm_insertionSort _ second).symm)]

/-- **Flat set literals are equal exactly when their sets are.** -/
theorem conv_set_leaves_iff (laws : K → KindLaws) {k : K} (set : laws k = KindLaws.set)
    (first second : List α) :
    Conv laws (.node k (first.map .leaf)) (.node k (second.map .leaf)) ↔
      first.toFinset = second.toFinset := by
  rw [← canonical_eq_iff, canonical_set_leaves laws set, canonical_set_leaves laws set,
    Term.node.injEq]
  simp only [true_and]
  have : Std.Antisymm (fun first second : α => first ≤ second) :=
    ⟨fun _ _ firstLe secondLe => le_antisymm firstLe secondLe⟩
  constructor
  · intro same
    have sorted := List.map_injective_iff.mpr (fun _ _ equal => Term.leaf.inj equal) same
    have firstSorted := List.perm_insertionSort (fun x y : α => x ≤ y) (dedupFirst first)
    rw [sorted] at firstSorted
    have permuted : (dedupFirst first).Perm (dedupFirst second) :=
      firstSorted.symm.trans (List.perm_insertionSort _ _)
    ext a
    simpa using permuted.mem_iff (a := a)
  · intro same
    have permuted : (dedupFirst first).Perm (dedupFirst second) := by
      rw [List.perm_ext_iff_of_nodup (nodup_dedupFirst _) (nodup_dedupFirst _)]
      intro a
      simpa using congrArg (a ∈ ·) same
    rw [List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _)
      (List.pairwise_insertionSort _ _)
      (((List.perm_insertionSort _ _).trans permuted).trans (List.perm_insertionSort _ _).symm)]

end Canonical

/-! ## Interning keys -/

section Interning

variable {K : Type u} {α : Type v} [LinearOrder K] [LinearOrder α]

/-- Number terms by their first position in a run's construction history;
terms the run never built come after, ordered by their printed form. -/
def internKey (history : List (Term K α)) (t : Term K α) : ℕ ×ₗ List (Token K α) :=
  toLex (history.idxOf t, t.serialize)

theorem internKey_injective (history : List (Term K α)) :
    Function.Injective (internKey history) := by
  intro s t same
  exact Term.serialize_injective (congrArg Prod.snd (toLex.injective same))

end Interning

/-! ## Typing: homogeneous collections and positional tuples -/

section Typing

/-- Types of collection values: atom types, homogeneous collections of a kind,
and positional tuples. -/
inductive Ty (K : Type u) (B : Type v) : Type (max u v) where
  | base : B → Ty K B
  | coll : K → Ty K B → Ty K B
  | tuple : List (Ty K B) → Ty K B

variable {K : Type u} {α : Type v} {B : Type w}

mutual
  /-- A node of any kind types as a homogeneous collection of that kind; a node
  of a kind with no laws may instead type as a positional tuple. -/
  inductive HasType (laws : K → KindLaws) (atomType : α → B) : Term K α → Ty K B → Prop
    | leaf (a : α) : HasType laws atomType (.leaf a) (.base (atomType a))
    | coll (k : K) (children : List (Term K α)) (element : Ty K B) :
        (∀ child ∈ children, HasType laws atomType child element) →
          HasType laws atomType (.node k children) (.coll k element)
    | tuple (k : K) (lawless : laws k = ⟨false, false⟩) (children : List (Term K α))
        (types : List (Ty K B)) :
        HasTypes laws atomType children types →
          HasType laws atomType (.node k children) (.tuple types)

  /-- Children typed position by position. -/
  inductive HasTypes (laws : K → KindLaws) (atomType : α → B) :
      List (Term K α) → List (Ty K B) → Prop
    | nil : HasTypes laws atomType [] []
    | cons {child : Term K α} {children : List (Term K α)} {type : Ty K B}
        {types : List (Ty K B)} :
        HasType laws atomType child type → HasTypes laws atomType children types →
          HasTypes laws atomType (child :: children) (type :: types)
end

variable {laws : K → KindLaws} {atomType : α → B}

theorem HasTypes.append_cons_iff {before after : List (Term K α)} {child : Term K α}
    {types : List (Ty K B)} :
    HasTypes laws atomType (before ++ child :: after) types ↔
      ∃ typesBefore type typesAfter, types = typesBefore ++ type :: typesAfter ∧
        HasTypes laws atomType before typesBefore ∧ HasType laws atomType child type ∧
          HasTypes laws atomType after typesAfter := by
  induction before generalizing types with
  | nil =>
      constructor
      · intro typed
        cases typed with
        | cons head tail => exact ⟨[], _, _, rfl, .nil, head, tail⟩
      · rintro ⟨typesBefore, type, typesAfter, rfl, before, head, tail⟩
        cases before
        exact .cons head tail
  | cons first rest ih =>
      constructor
      · intro typed
        cases typed with
        | cons head tail =>
            obtain ⟨typesBefore, type, typesAfter, rfl, before, middle, after⟩ := ih.mp tail
            exact ⟨_ :: typesBefore, type, typesAfter, rfl, .cons head before, middle, after⟩
      · rintro ⟨typesBefore, type, typesAfter, rfl, before, middle, after⟩
        cases before with
        | cons head tail =>
            exact .cons head (ih.mpr ⟨_, type, typesAfter, rfl, tail, middle, after⟩)

/-- **The laws preserve every type.**  A tuple type is positional, and only
kinds with no laws have tuple types. -/
theorem Step.hasType_iff {s t : Term K α} (step : Step laws s t) (type : Ty K B) :
    HasType laws atomType s type ↔ HasType laws atomType t type := by
  induction step generalizing type with
  | @swap k commutative before after first second =>
      have members : ∀ c, c ∈ before ++ first :: second :: after ↔
          c ∈ before ++ second :: first :: after := by
        intro c; simp only [List.mem_append, List.mem_cons]; tauto
      constructor
      · intro typed
        cases typed with
        | coll _ _ element children =>
            exact .coll _ _ element fun c member => children c ((members c).mpr member)
        | tuple _ lawless => simp [lawless] at commutative
      · intro typed
        cases typed with
        | coll _ _ element children =>
            exact .coll _ _ element fun c member => children c ((members c).mp member)
        | tuple _ lawless => simp [lawless] at commutative
  | @absorb k idempotent before middle after child =>
      have members : ∀ c, c ∈ before ++ child :: (middle ++ child :: after) ↔
          c ∈ before ++ child :: (middle ++ after) := by
        intro c; simp only [List.mem_append, List.mem_cons]; tauto
      constructor
      · intro typed
        cases typed with
        | coll _ _ element children =>
            exact .coll _ _ element fun c member => children c ((members c).mpr member)
        | tuple _ lawless => simp [lawless] at idempotent
      · intro typed
        cases typed with
        | coll _ _ element children =>
            exact .coll _ _ element fun c member => children c ((members c).mp member)
        | tuple _ lawless => simp [lawless] at idempotent
  | inside k before after _ ih =>
      constructor
      · intro typed
        cases typed with
        | coll _ _ element children =>
            refine .coll _ _ element fun c member => ?_
            rcases List.mem_append.mp member with inBefore | inRest
            · exact children c (List.mem_append_left _ inBefore)
            · rcases List.mem_cons.mp inRest with rfl | inAfter
              · exact (ih element).mp (children _ (by simp))
              · exact children c (by simp [inAfter])
        | tuple _ lawless _ types typedChildren =>
            obtain ⟨typesBefore, type, typesAfter, rfl, typedBefore, typedChild, typedAfter⟩ :=
              HasTypes.append_cons_iff.mp typedChildren
            exact .tuple _ lawless _ _ (HasTypes.append_cons_iff.mpr
              ⟨typesBefore, type, typesAfter, rfl, typedBefore, (ih type).mp typedChild,
                typedAfter⟩)
      · intro typed
        cases typed with
        | coll _ _ element children =>
            refine .coll _ _ element fun c member => ?_
            rcases List.mem_append.mp member with inBefore | inRest
            · exact children c (List.mem_append_left _ inBefore)
            · rcases List.mem_cons.mp inRest with rfl | inAfter
              · exact (ih element).mpr (children _ (by simp))
              · exact children c (by simp [inAfter])
        | tuple _ lawless _ types typedChildren =>
            obtain ⟨typesBefore, type, typesAfter, rfl, typedBefore, typedChild, typedAfter⟩ :=
              HasTypes.append_cons_iff.mp typedChildren
            exact .tuple _ lawless _ _ (HasTypes.append_cons_iff.mpr
              ⟨typesBefore, type, typesAfter, rfl, typedBefore, (ih type).mpr typedChild,
                typedAfter⟩)

theorem Conv.hasType_iff {s t : Term K α} (conv : Conv laws s t) (type : Ty K B) :
    HasType laws atomType s type ↔ HasType laws atomType t type := by
  induction conv generalizing type with
  | rel _ _ step => exact step.hasType_iff type
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact (ih type).symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact (ih₁ type).trans (ih₂ type)

/-- Normalization preserves every type. -/
theorem hasType_normalize_iff [DecidableEq K] [DecidableEq α] {κ : Type x} [LinearOrder κ]
    (key : Term K α → κ) (t : Term K α) (type : Ty K B) :
    HasType laws atomType (normalize laws key t) type ↔ HasType laws atomType t type :=
  ((conv_normalize laws key t).hasType_iff type).symm

end Typing

/-! ## Open terms: instantiation -/

section Open

variable {K : Type u} {α : Type v} {β : Type w} {laws : K → KindLaws}

theorem Step.map (f : α → β) {s t : Term K α} (step : Step laws s t) :
    Step laws (s.map f) (t.map f) := by
  induction step with
  | swap commutative before after first second =>
      simpa using Step.swap commutative (before.map (Term.map f)) (after.map (Term.map f))
        (first.map f) (second.map f)
  | absorb idempotent before middle after child =>
      simpa using Step.absorb idempotent (before.map (Term.map f)) (middle.map (Term.map f))
        (after.map (Term.map f)) (child.map f)
  | inside k before after _ ih =>
      simpa using Step.inside k (before.map (Term.map f)) (after.map (Term.map f)) ih

theorem Step.bind (σ : α → Term K β) {s t : Term K α} (step : Step laws s t) :
    Step laws (s.bind σ) (t.bind σ) := by
  induction step with
  | swap commutative before after first second =>
      simpa using Step.swap commutative (before.map (Term.bind σ)) (after.map (Term.bind σ))
        (first.bind σ) (second.bind σ)
  | absorb idempotent before middle after child =>
      simpa using Step.absorb idempotent (before.map (Term.bind σ)) (middle.map (Term.bind σ))
        (after.map (Term.bind σ)) (child.bind σ)
  | inside k before after _ ih =>
      simpa using Step.inside k (before.map (Term.bind σ)) (after.map (Term.bind σ)) ih

namespace Conv

/-- Renaming leaves preserves equality of values. -/
theorem map (f : α → β) {s t : Term K α} (conv : Conv laws s t) :
    Conv laws (s.map f) (t.map f) := by
  induction conv with
  | rel _ _ step => exact of_step (step.map f)
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Substitution preserves equality of values. -/
theorem bind (σ : α → Term K β) {s t : Term K α} (conv : Conv laws s t) :
    Conv laws (s.bind σ) (t.bind σ) := by
  induction conv with
  | rel _ _ step => exact of_step (step.bind σ)
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Substituting equal values gives equal values. -/
theorem bind_congr {σ τ : α → Term K β} (pointwise : ∀ a, Conv laws (σ a) (τ a))
    (t : Term K α) : Conv laws (t.bind σ) (t.bind τ) := by
  induction t using Term.induction with
  | leaf a => exact pointwise a
  | node k children ih =>
      simp only [Term.bind_node]
      simpa using Conv.children k (List.forall₂_map_left_iff.mpr
        (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun child member =>
          ih child member))) []

/-- Renaming reflects equality of values when it can be undone on the leaves
that occur. -/
theorem of_map {f : α → β} (g : β → α) {s t : Term K α}
    (undo : ∀ a ∈ s.leaves ++ t.leaves, g (f a) = a) (conv : Conv laws (s.map f) (t.map f)) :
    Conv laws s t := by
  have back := conv.map g
  rw [Term.map_map, Term.map_map,
    Term.map_congr (f := g ∘ f) s (g := id)
      (fun a member => undo a (List.mem_append_left _ member)),
    Term.map_congr (f := g ∘ f) t (g := id)
      (fun a member => undo a (List.mem_append_right _ member)),
    Term.map_id', Term.map_id'] at back
  exact back

end Conv

/-- **Instantiation needs one renormalization, and no more.**  The normal form
of an instance is computed from the normal form of the open term. -/
theorem normalize_bind_normalize [DecidableEq K] [DecidableEq α] [DecidableEq β]
    {κ κ' : Type x} [LinearOrder κ] [LinearOrder κ'] (laws : K → KindLaws)
    (key : Term K α → κ) {key' : Term K β → κ'} (injective' : Function.Injective key')
    (σ : α → Term K β) (t : Term K α) :
    normalize laws key' ((normalize laws key t).bind σ) = normalize laws key' (t.bind σ) :=
  (normalize_eq_iff injective').mpr ((conv_normalize laws key t).symm.bind σ)

/-- **Open normal forms decide equality in every instance** when the
variables that occur can be instantiated injectively by atoms that do not
occur. -/
theorem conv_iff_forall_instances {A : Type v} {V : Type w} (s t : Term K (A ⊕ V))
    (σ₀ : V → A)
    (injectiveOn : ∀ v w, Sum.inr v ∈ s.leaves ++ t.leaves → Sum.inr w ∈ s.leaves ++ t.leaves →
      σ₀ v = σ₀ w → v = w)
    (fresh : ∀ v, Sum.inr v ∈ s.leaves ++ t.leaves → Sum.inl (σ₀ v) ∉ s.leaves ++ t.leaves) :
    (∀ σ : V → A, Conv laws (s.map (Sum.elim id σ)) (t.map (Sum.elim id σ))) ↔
      Conv laws s t := by
  constructor
  · intro instances
    classical
    let undo : A → A ⊕ V := fun a =>
      if found : ∃ v, Sum.inr v ∈ s.leaves ++ t.leaves ∧ σ₀ v = a then Sum.inr found.choose
      else Sum.inl a
    refine Conv.of_map undo ?_ (instances σ₀)
    intro leaf member
    cases leaf with
    | inl a =>
        have absent : ¬ ∃ v, Sum.inr v ∈ s.leaves ++ t.leaves ∧ σ₀ v = a := by
          rintro ⟨v, occurs, rfl⟩
          exact fresh v occurs member
        simp only [Sum.elim_inl, id_eq, undo, dif_neg absent]
    | inr v =>
        have found : ∃ w, Sum.inr w ∈ s.leaves ++ t.leaves ∧ σ₀ w = σ₀ v := ⟨v, member, rfl⟩
        simp only [Sum.elim_inr, undo, dif_pos found, Sum.inr.injEq]
        exact injectiveOn _ _ found.choose_spec.1 member found.choose_spec.2
  · intro conv σ
    exact conv.map _

/-- With infinitely many atoms, the variables that occur can always be
instantiated injectively by atoms that do not occur. -/
theorem exists_fresh_instantiation {A : Type v} {V : Type w} [Infinite A]
    (leaves : List (A ⊕ V)) :
    ∃ σ₀ : V → A, (∀ v w, Sum.inr v ∈ leaves → Sum.inr w ∈ leaves → σ₀ v = σ₀ w → v = w) ∧
      ∀ v, Sum.inr v ∈ leaves → Sum.inl (σ₀ v) ∉ leaves := by
  classical
  let atoms : Finset A := (leaves.filterMap Sum.getLeft?).toFinset
  let occurring : Finset V := (leaves.filterMap Sum.getRight?).toFinset
  have unused : ((↑atoms : Set A)ᶜ).Infinite := atoms.finite_toSet.infinite_compl
  let fresh : ℕ ↪ ((↑atoms : Set A)ᶜ : Set A) := Set.Infinite.natEmbedding _ unused
  let σ₀ : V → A := fun v =>
    if occurs : v ∈ occurring then (fresh (occurring.equivFin ⟨v, occurs⟩)).val
    else (fresh 0).val
  have mem_occurring : ∀ v, Sum.inr v ∈ leaves → v ∈ occurring := fun v member => by
    simp only [occurring, List.mem_toFinset, List.mem_filterMap]
    exact ⟨Sum.inr v, member, rfl⟩
  refine ⟨σ₀, ?_, ?_⟩
  · intro v w vOccurs wOccurs same
    have vIn := mem_occurring v vOccurs
    have wIn := mem_occurring w wOccurs
    simp only [σ₀, dif_pos vIn, dif_pos wIn] at same
    have indices := fresh.injective (Subtype.ext same)
    have pairs := occurring.equivFin.injective (Fin.ext indices)
    exact congrArg Subtype.val pairs
  · intro v _ member
    have outside : σ₀ v ∉ atoms := by
      have inComplement : σ₀ v ∈ ((↑atoms : Set A)ᶜ : Set A) := by
        simp only [σ₀]
        split
        · exact (fresh _).property
        · exact (fresh 0).property
      simpa using inComplement
    apply outside
    simp only [atoms, List.mem_toFinset, List.mem_filterMap]
    exact ⟨Sum.inl (σ₀ v), member, rfl⟩

/-- With infinitely many atoms, open normal forms decide equality in every
instance. -/
theorem conv_iff_forall_instances_of_infinite {A : Type v} {V : Type w} [Infinite A]
    (s t : Term K (A ⊕ V)) :
    (∀ σ : V → A, Conv laws (s.map (Sum.elim id σ)) (t.map (Sum.elim id σ))) ↔
      Conv laws s t := by
  obtain ⟨σ₀, injectiveOn, fresh⟩ := exists_fresh_instantiation (s.leaves ++ t.leaves)
  exact conv_iff_forall_instances s t σ₀ injectiveOn fresh

end Open

namespace Controls

/-- One kind of each law set. -/
inductive Kind where
  | list | orderedSet | bag | set
  deriving DecidableEq, Repr

/-- A code ordering the control kinds. -/
def Kind.code : Kind → ℕ
  | .list => 0 | .orderedSet => 1 | .bag => 2 | .set => 3

instance : LinearOrder Kind :=
  LinearOrder.lift' Kind.code (by
    intro first second
    cases first <;> cases second <;> simp [Kind.code])

/-- The laws of each control kind. -/
def laws : Kind → KindLaws
  | .list => .list
  | .orderedSet => .insertionOrderedSet
  | .bag => .bag
  | .set => .set

/-- Control terms over natural-number atoms. -/
abbrev T := Term Kind ℕ

/-- A leaf. -/
def lf (n : ℕ) : T := .leaf n

/-- The canonical forms of `2 1 2` under each kind. -/
theorem canonical_examples :
    canonical laws (.node .list [lf 2, lf 1, lf 2] : T) = .node .list [lf 2, lf 1, lf 2] ∧
      canonical laws (.node .orderedSet [lf 2, lf 1, lf 2] : T) =
        .node .orderedSet [lf 2, lf 1] ∧
      canonical laws (.node .bag [lf 2, lf 1, lf 2] : T) = .node .bag [lf 1, lf 2, lf 2] ∧
      canonical laws (.node .set [lf 2, lf 1, lf 2] : T) = .node .set [lf 1, lf 2] := by
  decide

/-- Lists keep order and repetition. -/
theorem list_keeps_order :
    ¬ Conv laws (.node .list [lf 1, lf 2] : T) (.node .list [lf 2, lf 1]) ∧
      ¬ Conv laws (.node .list [lf 1, lf 1] : T) (.node .list [lf 1]) := by
  decide

/-- Insertion-ordered sets absorb later repetitions and keep first-occurrence
order. -/
theorem orderedSet_keeps_first_order :
    Conv laws (.node .orderedSet [lf 2, lf 1, lf 2] : T) (.node .orderedSet [lf 2, lf 1]) ∧
      ¬ Conv laws (.node .orderedSet [lf 1, lf 2] : T) (.node .orderedSet [lf 2, lf 1]) := by
  decide

/-- Bags forget order and keep multiplicity. -/
theorem bag_keeps_multiplicity :
    Conv laws (.node .bag [lf 1, lf 2] : T) (.node .bag [lf 2, lf 1]) ∧
      ¬ Conv laws (.node .bag [lf 1, lf 1] : T) (.node .bag [lf 1]) := by
  decide

/-- Sets forget order and multiplicity, and nothing else. -/
theorem set_forgets_both :
    Conv laws (.node .set [lf 1, lf 2, lf 1] : T) (.node .set [lf 2, lf 1]) ∧
      ¬ Conv laws (.node .set [lf 1] : T) (.node .set [lf 1, lf 2]) := by
  decide

/-- The laws act at depth: a set of two equal bags written differently is a
singleton set. -/
theorem nested_laws_act_inside :
    Conv laws (.node .set [.node .bag [lf 1, lf 2], .node .bag [lf 2, lf 1]] : T)
      (.node .set [.node .bag [lf 1, lf 2]]) := by
  decide

/-- Nothing is flattened: a bag inside a bag is not spliced, a singleton is not
its element, and kinds are not identified. -/
theorem no_flattening :
    ¬ Conv laws (.node .bag [.node .bag [lf 1, lf 2], lf 3] : T) (.node .bag [lf 1, lf 2, lf 3]) ∧
      ¬ Conv laws (.node .bag [lf 1] : T) (lf 1) ∧
      ¬ Conv laws (.node .bag [lf 1, lf 2] : T) (.node .set [lf 1, lf 2]) := by
  decide

/-- **Wrapped constructors are not conflated.**  An expression is the
lawless kind with its head as first child.  The laws act inside a wrapper,
two different heads around equal bags are different values, and a wrapped bag
is not the bare bag. -/
theorem wrapped_not_conflated :
    Conv laws (.node .list [lf 100, .node .bag [lf 1, lf 2]] : T)
        (.node .list [lf 100, .node .bag [lf 2, lf 1]]) ∧
      ¬ Conv laws (.node .list [lf 100, .node .bag [lf 1, lf 2]] : T)
        (.node .list [lf 101, .node .bag [lf 1, lf 2]]) ∧
      ¬ Conv laws (.node .list [lf 100, .node .bag [lf 1, lf 2]] : T)
        (.node .bag [lf 1, lf 2]) := by
  decide

/-- Atom types for the typing controls: `1` has one type, every other atom
the other. -/
def atomType (n : ℕ) : Bool := n == 1

/-- **Tuple or list is decided by typing.**  One ordered node of atoms of two
types has a positional tuple type and no homogeneous list type; a node of
atoms of one type has a list type. -/
theorem tuple_or_list_by_typing :
    HasType laws atomType (.node .list [lf 1, lf 2] : T) (.tuple [.base true, .base false]) ∧
      (¬ ∃ element, HasType laws atomType (.node .list [lf 1, lf 2] : T) (.coll .list element)) ∧
      HasType laws atomType (.node .list [lf 2, lf 3] : T) (.coll .list (.base false)) := by
  refine ⟨HasType.tuple (laws := laws) (atomType := atomType) Kind.list rfl _ _
    (.cons (.leaf 1) (.cons (.leaf 2) .nil)), ?_, ?_⟩
  · rintro ⟨element, typed⟩
    cases typed with
    | coll _ _ _ children =>
        have first := children (lf 1) (by simp)
        have second := children (lf 2) (by simp)
        cases first
        cases second
  · refine .coll _ _ _ fun child member => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .leaf 2
    · exact .leaf 3

/-- Positional typing is not invariant under permutation, which is why only
kinds with no laws have tuple types. -/
theorem positional_not_permutable :
    HasTypes laws atomType ([lf 1, lf 2] : List T) [.base true, .base false] ∧
      ¬ HasTypes laws atomType ([lf 2, lf 1] : List T) [.base true, .base false] := by
  refine ⟨.cons (.leaf 1) (.cons (.leaf 2) .nil), ?_⟩
  intro typed
  cases typed with
  | cons head _ => cases head

/-- **A singleton law would break typing**: a one-element bag is not its
element, and they have different types. -/
theorem singleton_law_breaks_typing :
    HasType laws atomType (.node .bag [lf 1] : T) (.coll .bag (.base true)) ∧
      ¬ HasType laws atomType (lf 1) (.coll .bag (.base true)) := by
  refine ⟨.coll _ _ _ fun child member => ?_, fun typed => by cases typed⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  exact .leaf 1

/-- A closing token of another kind is refused, and a printed term reads back. -/
theorem read_checks_closings :
    Term.read ([.opening .bag, .atom 1, .closing .set] : List (Token Kind ℕ)) = none ∧
      Term.read ((.node .bag [lf 1, .node .set [lf 2]] : T).serialize) =
        some (.node .bag [lf 1, .node .set [lf 2]]) := by
  decide

/-- **An interning key decides equality but prints history.**  Two runs that
built `1` and `2` in opposite orders give the same bag two different normal
forms. -/
theorem intern_order_prints_history :
    normalize laws (internKey [lf 1, lf 2]) (.node .bag [lf 2, lf 1] : T) =
        .node .bag [lf 1, lf 2] ∧
      normalize laws (internKey [lf 2, lf 1]) (.node .bag [lf 2, lf 1] : T) =
        .node .bag [lf 2, lf 1] ∧
      Conv laws (.node .bag [lf 1, lf 2] : T) (.node .bag [lf 2, lf 1]) := by
  refine ⟨by decide, by decide, ?_⟩
  exact Conv.of_step (Step.swap (k := Kind.bag) rfl [] [] (lf 1) (lf 2))

/-- Leaves of open terms: atoms on the left, variables on the right, coded
injectively into the naturals to order them. -/
def code : ℕ ⊕ ℕ → ℕ := Sum.elim (fun a => 2 * a) (fun v => 2 * v + 1)

theorem code_injective : Function.Injective code := by
  intro first second same
  cases first <;> cases second <;> simp [code] at same <;> first | rfl | omega | (congr 1; omega)

/-- A key for open terms. -/
def openKey (t : Term Kind (ℕ ⊕ ℕ)) : List (Token Kind ℕ) := (t.map code).serialize

/-- An instance of an open normal form need not be sorted: the variable sorted
before the atom `5` is instantiated by `7`. -/
theorem instance_unsorted :
    normalize laws openKey (.node .bag [.leaf (Sum.inl 5), .leaf (Sum.inr 0)]) =
        .node .bag [.leaf (Sum.inr 0), .leaf (Sum.inl 5)] ∧
      canonical laws ((Term.node Kind.bag [.leaf (Sum.inr 0), .leaf (Sum.inl 5)]).map
          (Sum.elim id fun _ => 7)) ≠
        (Term.node Kind.bag [.leaf (Sum.inr 0), .leaf (Sum.inl 5)]).map
          (Sum.elim id fun _ => 7) := by
  decide

/-- An instance of an open set may collapse: two distinct variables
instantiated by one atom. -/
theorem instance_collapses :
    canonical laws ((Term.node Kind.set [.leaf (Sum.inr 0), .leaf (Sum.inr 1)] :
        Term Kind (ℕ ⊕ ℕ)).map (Sum.elim id fun _ => 3)) = .node .set [lf 3] ∧
      canonical laws ((Term.node Kind.set [.leaf (Sum.inr 0), .leaf (Sum.inr 1)] :
        Term Kind (ℕ ⊕ ℕ)).map (Sum.elim id fun v => v)) = .node .set [lf 0, lf 1] := by
  decide

/-- **With too few atoms, different open values agree in every instance.**
Over one atom, the open sets `{x, y}` and `{x}` have the same instances. -/
theorem few_atoms_identify :
    (∀ σ : Bool → Unit, Conv laws
      ((Term.node Kind.set [.leaf (Sum.inr true), .leaf (Sum.inr false)] :
        Term Kind (Unit ⊕ Bool)).map (Sum.elim id σ))
      ((Term.node Kind.set [.leaf (Sum.inr true)] : Term Kind (Unit ⊕ Bool)).map
        (Sum.elim id σ))) ∧
      ¬ Conv laws (Term.node Kind.set [.leaf (Sum.inr true), .leaf (Sum.inr false)] :
          Term Kind (Unit ⊕ Bool)) (Term.node Kind.set [.leaf (Sum.inr true)]) := by
  refine ⟨fun σ => ?_, fun conv => ?_⟩
  · exact Conv.of_step (Step.absorb (k := Kind.set) rfl [] [] [] (.leaf ()))
  · have mapped := conv.map (Sum.elim (fun _ => (0 : ℕ)) fun b => if b then 1 else 2)
    revert mapped
    decide

end Controls

end Mettapedia.Algebra.Collections.CanonicalForm
