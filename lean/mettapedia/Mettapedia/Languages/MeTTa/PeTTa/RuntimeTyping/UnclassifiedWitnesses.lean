import Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.CanonicalTypes
import Mettapedia.Cybernetics.DistinctionCalculus.ConstructionMiddle

/-!
# The witness of an undeclared symbol, read through the contracts' observers

Every ground PeTTa value has a canonical proper type (`CanonicalTypes`). A symbol
without a proper declaration needs one too, and there are two candidate policies:

* `merged`: one witness, `UnclassifiedSymbol`, for every such symbol, callable or not;
* `split`: a symbol that `get-metatype` reports as `Grounded` (a registered callable)
  has its own witness, `UnclassifiedGrounded`; the others keep `UnclassifiedSymbol`.

Contracts observe a value through the checking patterns `Symbol`, `Grounded` and
`Expression`, the primitive tests, host types and each declared type (`Reading`). Two
values are *apart* when some reading tells them apart. Apartness is an exclusion
relation of the distinction calculus, and its concepts (`Exclusion.IsConcept`) are the
classes that no reading splits.

* **Split witnesses are exactly the observers' classes**
  (`split_extent_eq_conceptOf`): the members of the split witness of an undeclared
  symbol are precisely the values that no reading tells apart from it.
* **The merged witness is a concept, but not the class of any member**
  (`merged_extent_eq_union`, `merged_extent_isConcept`, `merged_extent_ne_conceptOf`):
  it is the union of the two split classes, and `get-metatype` splits it.
* **The witness decides the checking pattern** (`split_metatype_of_witness`): under the
  split policy every built-in witness fixes the metatype of its members; under the
  merged policy no table from witnesses to metatypes exists
  (`merged_no_metatype_table`).
* **Coverage and the unshared-parameter waiver hold under both policies**
  (`ground_typed`, `waive_joint_iff_on_ground`).
* **Only one kind of sharing changes** (`share_split_iff`): the split policy refuses
  exactly the merged sharings between undeclared symbols of different metatypes, such
  as `+` and `foo` (`Control.plus_and_foo`).
* **Edits.** Under the split policy the witness of an undeclared symbol changes exactly
  when its metatype does (`split_witness_eq_iff`). The merged witness never follows a
  definition edit, although the metatype does (`Control.definition_edit`). Under both
  policies a new declaration can withdraw a shared witness
  (`Control.declaration_withdraws_sharing`): that non-monotonicity comes from replacing
  the canonical witness by a declared one, not from the policy. Naming either
  unclassified witness in a declaration adds no distinction
  (`witness_reading_adds_no_distinction`).

Readings of expression structure are left out: they are constant on symbols, so they
do not change any class of symbols. Nominal facts about primitive values are outside
this fragment, as in `CanonicalTypes`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.UnclassifiedWitnesses

open Set
open Mettapedia.Logic.ConstraintTypes
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion

/-- What contracts see of a program state: which symbols are callable (registered
natives and symbols with equations) and which proper types each symbol is declared to
have. -/
structure World where
  callable : String → Bool
  declared : String → String → Prop

/-- The metatypes a checking pattern can require. -/
inductive Meta where
  | symbol | grounded | expression
  deriving DecidableEq

/-- `get-metatype` on a ground value: numbers, strings, booleans and callable symbols
are `Grounded`, other symbols `Symbol`, native lists `Expression`; a host value has
none of the three. -/
def metatype (w : World) : Atom → Option Meta
  | .symbol s => if w.callable s then some .grounded else some .symbol
  | .grounded (.int _) => some .grounded
  | .grounded (.string _) => some .grounded
  | .grounded (.bool _) => some .grounded
  | .grounded (.custom _ _) => none
  | .expression _ => some .expression
  | .var _ => none

/-- How a symbol without a proper declaration is classified. -/
inductive Policy where
  /-- One witness for every such symbol, callable or not. -/
  | merged
  /-- A callable symbol has its own witness. -/
  | split
  deriving DecidableEq

/-- Proper type names of the canonical fragment, with both unclassified witnesses. -/
inductive Name where
  | number | string | bool
  | unclassifiedSymbol | unclassifiedGrounded
  | host (typeName : String)
  | nominal (typeName : String)
  deriving DecidableEq

abbrev PType := SymbolicTypes.Closed Name CanonicalTypes.Former CanonicalTypes.typeArity

/-- The witness of a symbol without a proper declaration. -/
def witnessOf : Policy → World → String → Name
  | .merged, _, _ => .unclassifiedSymbol
  | .split, w, s => if w.callable s then .unclassifiedGrounded else .unclassifiedSymbol

/-- Canonical membership under a policy. -/
inductive Member (policy : Policy) (w : World) : Atom → PType → Prop where
  | number (n : Int) : Member policy w (.grounded (.int n)) (.closed .number)
  | string (s : String) : Member policy w (.grounded (.string s)) (.closed .string)
  | bool (b : Bool) : Member policy w (.grounded (.bool b)) (.closed .bool)
  | host (typeName data : String) :
      Member policy w (.grounded (.custom typeName data)) (.closed (.host typeName))
  | unclassified (s : String) (undeclared : ∀ typeName, ¬ w.declared s typeName) :
      Member policy w (.symbol s) (.closed (witnessOf policy w s))
  | nominal (s typeName : String) (annotation : w.declared s typeName) :
      Member policy w (.symbol s) (.closed (.nominal typeName))
  | tuple (elements : List Atom) (types : Fin elements.length → PType)
      (each : ∀ i, Member policy w (elements.get i) (types i)) :
      Member policy w (.expression elements) (.app (.tuple elements.length) types)

/-! ## Coverage under both policies -/

mutual
theorem ground_typed (policy : Policy) (w : World) :
    (atom : Atom) → CanonicalTypes.Ground atom → ∃ type, Member policy w atom type
  | .symbol s, _ => by
      by_cases annotated : ∃ typeName, w.declared s typeName
      · obtain ⟨typeName, annotation⟩ := annotated
        exact ⟨_, .nominal s typeName annotation⟩
      · exact ⟨_, .unclassified s (fun typeName annotation => annotated ⟨typeName, annotation⟩)⟩
  | .var _, ground => False.elim ground
  | .grounded (.int n), _ => ⟨_, .number n⟩
  | .grounded (.string s), _ => ⟨_, .string s⟩
  | .grounded (.bool b), _ => ⟨_, .bool b⟩
  | .grounded (.custom typeName data), _ => ⟨_, .host typeName data⟩
  | .expression elements, ground => by
      obtain ⟨types, each⟩ := ground_typed_list policy w elements ground
      exact ⟨_, .tuple elements types each⟩

theorem ground_typed_list (policy : Policy) (w : World) :
    (elements : List Atom) → CanonicalTypes.GroundList elements →
      ∃ types : Fin elements.length → PType, ∀ i, Member policy w (elements.get i) (types i)
  | [], _ => ⟨Fin.elim0, fun i => i.elim0⟩
  | atom :: rest, ⟨ground, groundRest⟩ => by
      obtain ⟨type, member⟩ := ground_typed policy w atom ground
      obtain ⟨types, each⟩ := ground_typed_list policy w rest groundRest
      refine ⟨Fin.cons type types, fun i => ?_⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using member
      · simpa using each j
end

open CheckingPatterns PatternContracts UnsharedParameters in
/-- The unshared-parameter law holds under either policy: a parameter that is the whole
check of one input and occurs nowhere else imposes no check on a ground argument. -/
theorem waive_joint_iff_on_ground (policy : Policy) {Kind : Type}
    {sig : CheckingPatterns.Signature Kind} {Context P : Type} [DecidableEq P]
    {valueKind : Kind} {n : Nat}
    (model : Model sig (fun _ => Atom) Context Name CanonicalTypes.Former CanonicalTypes.typeArity)
    (world : Context → World)
    (canonical : ∀ context atom type, Member policy (world context) atom type →
      model.member (s := valueKind) context atom type)
    (before after : Context) (arguments : Fin n → Atom) (value : Atom)
    (declaration : Declaration sig P Name CanonicalTypes.Former CanonicalTypes.typeArity valueKind n)
    (slot : Fin n) (parameter : P)
    (unshared : Unshared declaration slot parameter) (ground : CanonicalTypes.Ground (arguments slot)) :
    Joint model before after arguments value (waive declaration slot) ↔
      Joint model before after arguments value declaration := by
  obtain ⟨type, member⟩ := ground_typed policy (world before) (arguments slot) ground
  exact waive_joint_iff model before after arguments value declaration slot parameter unshared
    ⟨type, canonical before (arguments slot) type member⟩

/-! ## Membership in a closed name -/

theorem member_closed_iff (policy : Policy) (w : World) (x : Atom) (name : Name) :
    Member policy w x (.closed name) ↔
      (name = .number ∧ ∃ n, x = .grounded (.int n)) ∨
      (name = .string ∧ ∃ s, x = .grounded (.string s)) ∨
      (name = .bool ∧ ∃ b, x = .grounded (.bool b)) ∨
      (∃ t data, name = .host t ∧ x = .grounded (.custom t data)) ∨
      (∃ s, x = .symbol s ∧ (∀ t, ¬ w.declared s t) ∧ name = witnessOf policy w s) ∨
      (∃ s t, x = .symbol s ∧ w.declared s t ∧ name = .nominal t) := by
  constructor
  · intro member
    cases member with
    | number n => exact Or.inl ⟨rfl, n, rfl⟩
    | string s => exact Or.inr (Or.inl ⟨rfl, s, rfl⟩)
    | bool b => exact Or.inr (Or.inr (Or.inl ⟨rfl, b, rfl⟩))
    | host t data => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, data, rfl, rfl⟩)))
    | unclassified s undeclared =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, rfl, undeclared, rfl⟩))))
    | nominal s t annotation =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨s, t, rfl, annotation, rfl⟩))))
  · rintro (⟨rfl, n, rfl⟩ | ⟨rfl, s, rfl⟩ | ⟨rfl, b, rfl⟩ | ⟨t, data, rfl, rfl⟩ |
        ⟨s, rfl, undeclared, rfl⟩ | ⟨s, t, rfl, annotation, rfl⟩)
    · exact .number n
    · exact .string s
    · exact .bool b
    · exact .host t data
    · exact .unclassified s undeclared
    · exact .nominal s t annotation

theorem witnessOf_ne_nominal (policy : Policy) (w : World) (s t : String) :
    witnessOf policy w s ≠ .nominal t := by
  cases policy <;> simp only [witnessOf] <;> (try split) <;> simp

/-- The values a closed name admits. -/
def extent (policy : Policy) (w : World) (name : Name) : Set Atom :=
  {x | Member policy w x (.closed name)}

/-- A witness of an undeclared symbol admits exactly the undeclared symbols with the
same witness. -/
theorem mem_extent_witnessOf (policy : Policy) (w : World) (s : String) (y : Atom) :
    y ∈ extent policy w (witnessOf policy w s) ↔
      ∃ t, y = .symbol t ∧ (∀ T, ¬ w.declared t T) ∧ witnessOf policy w t = witnessOf policy w s := by
  simp only [extent, mem_ofPred_eq, member_closed_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨t, rfl, undeclared, h⟩ | ⟨_, T, _, _, h⟩)
    · cases policy <;> simp only [witnessOf] at h <;> (try split at h) <;> simp at h
    · cases policy <;> simp only [witnessOf] at h <;> (try split at h) <;> simp at h
    · cases policy <;> simp only [witnessOf] at h <;> (try split at h) <;> simp at h
    · cases policy <;> simp only [witnessOf] at h <;> (try split at h) <;> simp at h
    · exact ⟨t, rfl, undeclared, h.symm⟩
    · exact absurd h (witnessOf_ne_nominal policy w s T)
  · rintro ⟨t, rfl, undeclared, h⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, rfl, undeclared, h.symm⟩))))

/-! ## Observers -/

/-- The readings a contract makes of a value without naming an unclassified witness:
each metatype pattern, the primitive tests, each host type and each declared type. -/
inductive Reading where
  | pattern (m : Option Meta)
  | number | string | bool
  | host (typeName : String)
  | declared (typeName : String)

/-- Each reading as a proposition about a value. -/
def read (w : World) : Reading → Atom → Prop
  | .pattern m, x => metatype w x = m
  | .number, x => ∃ n, x = .grounded (.int n)
  | .string, x => ∃ s, x = .grounded (.string s)
  | .bool, x => ∃ b, x = .grounded (.bool b)
  | .host t, x => ∃ data, x = .grounded (.custom t data)
  | .declared t, x => ∃ s, x = .symbol s ∧ w.declared s t

/-- Two values are apart when some reading tells them apart. -/
def Apart (w : World) (x y : Atom) : Prop := ∃ i, read w i x ≠ read w i y

/-- Two values are indistinguishable when every reading agrees. -/
def Indist (w : World) (x y : Atom) : Prop := ∀ i, read w i x = read w i y

theorem not_apart_iff (w : World) (x y : Atom) : ¬ Apart w x y ↔ Indist w x y := by
  simp [Apart, Indist]

theorem apart_symm (w : World) (x y : Atom) : Apart w x y → Apart w y x := by
  rintro ⟨i, h⟩
  exact ⟨i, Ne.symm h⟩

theorem apart_irrefl (w : World) (x : Atom) : ¬ Apart w x x := by
  rintro ⟨i, h⟩
  exact h rfl

theorem not_apart_trans (w : World) (x y z : Atom) :
    ¬ Apart w x y → ¬ Apart w y z → ¬ Apart w x z := by
  simp only [not_apart_iff]
  intro first second i
  exact (first i).trans (second i)

/-- The concept of a value is the class of values no reading tells apart from it. -/
theorem conceptOf_eq (w : World) (x : Atom) :
    conceptOf (Apart w) x = {y | Indist w x y} := by
  rw [conceptOf_eq_of_transitive (apart_symm w) (apart_irrefl w) (not_apart_trans w)]
  ext y
  simp [not_apart_iff]

theorem metatype_symbol_eq_iff (w : World) (s t : String) :
    metatype w (.symbol s) = metatype w (.symbol t) ↔ w.callable s = w.callable t := by
  cases hs : w.callable s <;> cases ht : w.callable t <;> simp [metatype, hs, ht]

theorem witnessOf_split_eq_iff (w : World) (s t : String) :
    witnessOf .split w s = witnessOf .split w t ↔ w.callable s = w.callable t := by
  cases hs : w.callable s <;> cases ht : w.callable t <;> simp [witnessOf, hs, ht]

/-- Undeclared symbols with the same callability are indistinguishable. -/
theorem indist_of_undeclared (w : World) (s t : String)
    (undeclaredS : ∀ T, ¬ w.declared s T) (undeclaredT : ∀ T, ¬ w.declared t T)
    (same : w.callable s = w.callable t) : Indist w (.symbol s) (.symbol t) := by
  intro i
  cases i with
  | pattern m => simp only [read, (metatype_symbol_eq_iff w s t).2 same]
  | number => simp [read]
  | string => simp [read]
  | bool => simp [read]
  | host T => simp [read]
  | declared T => simp [read, undeclaredS, undeclaredT]

/-- A value no reading tells apart from an undeclared symbol is an undeclared symbol
with the same callability. -/
theorem undeclared_of_indist (w : World) (s : String) (undeclaredS : ∀ T, ¬ w.declared s T)
    (y : Atom) (same : Indist w (.symbol s) y) :
    ∃ t, y = .symbol t ∧ (∀ T, ¬ w.declared t T) ∧ w.callable t = w.callable s := by
  have sameMeta : metatype w y = metatype w (.symbol s) :=
    cast (same (.pattern (metatype w (.symbol s)))) rfl
  have notNumber := same .number
  have notString := same .string
  have notBool := same .bool
  cases y with
  | symbol t =>
      refine ⟨t, rfl, fun T declaredT => ?_, ?_⟩
      · have h := same (.declared T)
        simp only [read, Atom.symbol.injEq, exists_eq_left'] at h
        exact undeclaredS T (h ▸ declaredT)
      · exact ((metatype_symbol_eq_iff w t s).1 sameMeta)
  | var v =>
      exfalso
      cases hs : w.callable s <;> simp [metatype, hs] at sameMeta
  | grounded g =>
      exfalso
      cases g with
      | int n => simp [read] at notNumber
      | string u => simp [read] at notString
      | bool b => simp [read] at notBool
      | custom T data => cases hs : w.callable s <;> simp [metatype, hs] at sameMeta
  | expression elements =>
      exfalso
      cases hs : w.callable s <;> simp [metatype, hs] at sameMeta

/-! ## The split policy: witnesses are the observers' classes -/

/-- **Under the split policy, the witness of an undeclared symbol is exactly the class
of values that no reading tells apart from it.** -/
theorem split_extent_eq_conceptOf (w : World) (s : String) (undeclaredS : ∀ T, ¬ w.declared s T) :
    extent .split w (witnessOf .split w s) = conceptOf (Apart w) (.symbol s) := by
  rw [conceptOf_eq]
  ext y
  rw [mem_extent_witnessOf, mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl, undeclaredT, h⟩
    exact indist_of_undeclared w s t undeclaredS undeclaredT
      ((witnessOf_split_eq_iff w t s).1 h).symm
  · intro same
    obtain ⟨t, rfl, undeclaredT, h⟩ := undeclared_of_indist w s undeclaredS y same
    exact ⟨t, rfl, undeclaredT, (witnessOf_split_eq_iff w t s).2 h⟩

theorem split_extent_isConcept (w : World) (s : String) (undeclaredS : ∀ T, ¬ w.declared s T) :
    IsConcept (Apart w) (extent .split w (witnessOf .split w s)) := by
  rw [split_extent_eq_conceptOf w s undeclaredS]
  exact isConcept_conceptOf (apart_symm w) _

/-- The metatype each built-in witness fixes. -/
def metaOfWitness : Name → Option Meta
  | .number | .string | .bool => some .grounded
  | .unclassifiedSymbol => some .symbol
  | .unclassifiedGrounded => some .grounded
  | .host _ => none
  | .nominal _ => none

/-- **Under the split policy every built-in witness fixes the metatype of its members**,
so a checking pattern on a value with a known built-in witness is a table lookup. -/
theorem split_metatype_of_witness (w : World) (x : Atom) (name : Name)
    (builtin : ∀ t, name ≠ .nominal t) (member : Member .split w x (.closed name)) :
    metatype w x = metaOfWitness name := by
  rcases (member_closed_iff _ _ _ _).1 member with
    ⟨rfl, n, rfl⟩ | ⟨rfl, u, rfl⟩ | ⟨rfl, b, rfl⟩ | ⟨T, data, rfl, rfl⟩ |
    ⟨s, rfl, _, rfl⟩ | ⟨s, T, rfl, _, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · cases hs : w.callable s <;> simp [metatype, witnessOf, metaOfWitness, hs]
  · exact absurd rfl (builtin T)

/-- Every tuple witness admits only expressions, under either policy. -/
theorem metatype_of_tuple (policy : Policy) (w : World) (x : Atom) (length : Nat)
    (types : Fin (CanonicalTypes.typeArity (.tuple length)) → PType)
    (member : Member policy w x (.app (.tuple length) types)) :
    metatype w x = some .expression := by
  cases member
  rfl

/-! ## The merged policy: a concept that a reading splits -/

theorem merged_extent_eq_union (w : World) :
    extent .merged w .unclassifiedSymbol =
      extent .split w .unclassifiedSymbol ∪ extent .split w .unclassifiedGrounded := by
  ext y
  simp only [extent, mem_union, mem_ofPred_eq, member_closed_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨t, rfl, undeclared, _⟩ | ⟨_, _, _, _, h⟩)
    · cases h
    · cases h
    · cases h
    · cases h
    · cases ht : w.callable t
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨t, rfl, undeclared, by simp [witnessOf, ht]⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨t, rfl, undeclared, by simp [witnessOf, ht]⟩)))))
    · cases h
  · rintro ((⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨t, rfl, undeclared, _⟩ | ⟨_, _, _, _, h⟩) |
        (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨t, rfl, undeclared, _⟩ | ⟨_, _, _, _, h⟩))
    all_goals first
      | cases h
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨t, rfl, undeclared, rfl⟩))))

theorem split_unclassified_saturated (w : World) (name : Name) :
    Saturated (Apart w) (extent .split w name) := by
  intro x member y notApart
  have member' := member
  simp only [extent, mem_ofPred_eq, member_closed_iff] at member'
  rcases member' with ⟨rfl, n, rfl⟩ | ⟨rfl, u, rfl⟩ | ⟨rfl, b, rfl⟩ | ⟨T, data, rfl, rfl⟩ |
    ⟨s, rfl, undeclaredS, rfl⟩ | ⟨s, T, rfl, annotation, rfl⟩
  · obtain ⟨k, rfl⟩ : ∃ k, y = Atom.grounded (.int k) :=
      cast ((not_apart_iff w _ _).1 notApart .number)
        (⟨n, rfl⟩ : ∃ k, Atom.grounded (.int n) = .grounded (.int k))
    exact .number k
  · obtain ⟨k, rfl⟩ : ∃ k, y = Atom.grounded (.string k) :=
      cast ((not_apart_iff w _ _).1 notApart .string)
        (⟨u, rfl⟩ : ∃ k, Atom.grounded (.string u) = .grounded (.string k))
    exact .string k
  · obtain ⟨k, rfl⟩ : ∃ k, y = Atom.grounded (.bool k) :=
      cast ((not_apart_iff w _ _).1 notApart .bool)
        (⟨b, rfl⟩ : ∃ k, Atom.grounded (.bool b) = .grounded (.bool k))
    exact .bool k
  · obtain ⟨k, rfl⟩ : ∃ k, y = Atom.grounded (.custom T k) :=
      cast ((not_apart_iff w _ _).1 notApart (.host T))
        (⟨data, rfl⟩ : ∃ k, Atom.grounded (.custom T data) = .grounded (.custom T k))
    exact .host T k
  · have inConcept : y ∈ conceptOf (Apart w) (.symbol s) := by
      rw [conceptOf_eq]
      exact (not_apart_iff w _ _).1 notApart
    rw [← split_extent_eq_conceptOf w s undeclaredS] at inConcept
    exact inConcept
  · obtain ⟨t, rfl, declaredT⟩ : ∃ t, y = Atom.symbol t ∧ w.declared t T :=
      cast ((not_apart_iff w _ _).1 notApart (.declared T))
        (⟨s, rfl, annotation⟩ : ∃ t, Atom.symbol s = .symbol t ∧ w.declared t T)
    exact .nominal t T declaredT

/-- **The merged witness is a type the readings can see**: a concept, since it is a
union of classes. -/
theorem merged_extent_isConcept (w : World) :
    IsConcept (Apart w) (extent .merged w .unclassifiedSymbol) := by
  apply isConcept_of_saturated (apart_symm w) (apart_irrefl w)
  rw [merged_extent_eq_union]
  intro x member y notApart
  rcases member with inSymbol | inGrounded
  · exact Or.inl (split_unclassified_saturated w _ x inSymbol y notApart)
  · exact Or.inr (split_unclassified_saturated w _ x inGrounded y notApart)

/-- **But it is not the class of any member** once both kinds of undeclared symbol
exist: `get-metatype` tells a callable member apart from a plain one. -/
theorem merged_extent_ne_conceptOf (w : World) (s c : String)
    (undeclaredS : ∀ T, ¬ w.declared s T) (undeclaredC : ∀ T, ¬ w.declared c T)
    (plain : w.callable s = false) (callable : w.callable c = true) :
    Atom.symbol s ∈ extent .merged w .unclassifiedSymbol ∧
      Atom.symbol c ∈ extent .merged w .unclassifiedSymbol ∧
      Apart w (.symbol s) (.symbol c) ∧
      (∀ x ∈ extent .merged w .unclassifiedSymbol,
        extent .merged w .unclassifiedSymbol ≠ conceptOf (Apart w) x) := by
  have memS : Atom.symbol s ∈ extent .merged w .unclassifiedSymbol := .unclassified s undeclaredS
  have memC : Atom.symbol c ∈ extent .merged w .unclassifiedSymbol := .unclassified c undeclaredC
  have apart : Apart w (.symbol s) (.symbol c) := by
    refine ⟨.pattern (some .symbol), ?_⟩
    simp [read, metatype, plain, callable]
  refine ⟨memS, memC, apart, fun x member equal => ?_⟩
  have inS : Atom.symbol s ∈ conceptOf (Apart w) x := equal ▸ memS
  have inC : Atom.symbol c ∈ conceptOf (Apart w) x := equal ▸ memC
  rw [conceptOf_eq, mem_ofPred_eq] at inS inC
  exact (not_apart_iff w _ _).2 (fun i => ((inS i).symm.trans (inC i))) apart

/-- **Under the merged policy no table from witnesses to metatypes exists** once both
kinds of undeclared symbol exist. -/
theorem merged_no_metatype_table (w : World) (s c : String)
    (undeclaredS : ∀ T, ¬ w.declared s T) (undeclaredC : ∀ T, ¬ w.declared c T)
    (plain : w.callable s = false) (callable : w.callable c = true) :
    ¬ ∃ table : Name → Option Meta, ∀ x name, (∀ t, name ≠ .nominal t) →
        Member .merged w x (.closed name) → metatype w x = table name := by
  rintro ⟨table, decides⟩
  have forS := decides (.symbol s) .unclassifiedSymbol (by simp) (.unclassified s undeclaredS)
  have forC := decides (.symbol c) .unclassifiedSymbol (by simp) (.unclassified c undeclaredC)
  simp [metatype, plain, callable] at forS forC
  rw [← forS] at forC
  cases forC

/-! ## Sharing a witness -/

/-- Two values share a proper witness: a shared parameter admits them together. -/
def Share (policy : Policy) (w : World) (x y : Atom) : Prop :=
  ∃ type, Member policy w x type ∧ Member policy w y type

theorem share_symbols_iff (policy : Policy) (w : World) (s t : String) :
    Share policy w (.symbol s) (.symbol t) ↔
      ((∀ T, ¬ w.declared s T) ∧ (∀ T, ¬ w.declared t T) ∧ witnessOf policy w s = witnessOf policy w t) ∨
      ∃ T, w.declared s T ∧ w.declared t T := by
  constructor
  · rintro ⟨type, memberS, memberT⟩
    cases memberS with
    | unclassified _ undeclaredS =>
        rcases (member_closed_iff _ _ _ _).1 memberT with
          ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨t', ht, undeclaredT, h⟩ | ⟨_, T, _, _, h⟩
        · cases policy <;> simp only [witnessOf] at h <;> (try split at h) <;> simp at h
        · cases policy <;> simp only [witnessOf] at h <;> (try split at h) <;> simp at h
        · cases policy <;> simp only [witnessOf] at h <;> (try split at h) <;> simp at h
        · cases policy <;> simp only [witnessOf] at h <;> (try split at h) <;> simp at h
        · cases ht
          exact Or.inl ⟨undeclaredS, undeclaredT, h⟩
        · exact absurd h (witnessOf_ne_nominal policy w s T)
    | nominal _ T declaredS =>
        rcases (member_closed_iff _ _ _ _).1 memberT with
          ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩ | ⟨t', T', ht, declaredT, h⟩
        · cases h
        · cases h
        · cases h
        · cases h
        · exact absurd h.symm (witnessOf_ne_nominal policy w _ T)
        · cases ht
          cases h
          exact Or.inr ⟨T, declaredS, declaredT⟩
  · rintro (⟨undeclaredS, undeclaredT, same⟩ | ⟨T, declaredS, declaredT⟩)
    · have memberT := Member.unclassified (policy := policy) (w := w) t undeclaredT
      rw [← same] at memberT
      exact ⟨_, .unclassified s undeclaredS, memberT⟩
    · exact ⟨_, .nominal s T declaredS, .nominal t T declaredT⟩

/-- **The split policy refuses exactly the merged sharings between undeclared symbols of
different metatypes**; every other sharing of symbols is unchanged. -/
theorem share_split_iff (w : World) (s t : String) :
    Share .split w (.symbol s) (.symbol t) ↔
      Share .merged w (.symbol s) (.symbol t) ∧
        ((∃ T, w.declared s T ∧ w.declared t T) ∨ metatype w (.symbol s) = metatype w (.symbol t)) := by
  rw [share_symbols_iff, share_symbols_iff, metatype_symbol_eq_iff, witnessOf_split_eq_iff]
  simp only [witnessOf, and_true]
  constructor
  · rintro (⟨undeclaredS, undeclaredT, same⟩ | common)
    · exact ⟨Or.inl ⟨undeclaredS, undeclaredT⟩, Or.inr same⟩
    · exact ⟨Or.inr common, Or.inl common⟩
  · rintro ⟨undeclared | common, common' | same⟩
    · exact Or.inr common'
    · exact Or.inl ⟨undeclared.1, undeclared.2, same⟩
    · exact Or.inr common
    · exact Or.inr common

/-! ## Edits -/

/-- **Under the split policy the witness of an undeclared symbol changes exactly when
its metatype does.** -/
theorem split_witness_eq_iff (w w' : World) (s : String) :
    witnessOf .split w s = witnessOf .split w' s ↔ metatype w (.symbol s) = metatype w' (.symbol s) := by
  cases hs : w.callable s <;> cases hs' : w'.callable s <;> simp [witnessOf, metatype, hs, hs']

/-- The merged witness depends on no definition. -/
theorem merged_witness_constant (w w' : World) (s : String) :
    witnessOf .merged w s = witnessOf .merged w' s := rfl

/-- Naming an unclassified witness in a declaration adds no distinction: membership in
it agrees on indistinguishable values, under either policy. -/
theorem witness_reading_adds_no_distinction (policy : Policy) (w : World) (name : Name)
    (unclassifiedName : name = .unclassifiedSymbol ∨ name = .unclassifiedGrounded)
    (x y : Atom) (same : Indist w x y) :
    x ∈ extent policy w name ↔ y ∈ extent policy w name := by
  have saturated : Saturated (Apart w) (extent policy w name) := by
    cases policy with
    | split => exact split_unclassified_saturated w name
    | merged =>
        rcases unclassifiedName with rfl | rfl
        · intro a member b notApart
          rw [merged_extent_eq_union] at member ⊢
          rcases member with inSymbol | inGrounded
          · exact Or.inl (split_unclassified_saturated w _ a inSymbol b notApart)
          · exact Or.inr (split_unclassified_saturated w _ a inGrounded b notApart)
        · intro a member
          exfalso
          simp only [extent, mem_ofPred_eq, member_closed_iff] at member
          rcases member with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩ <;>
            simp [witnessOf] at h
  exact ⟨fun member => saturated x member y ((not_apart_iff w x y).2 same),
    fun member => saturated y member x ((not_apart_iff w y x).2 (fun i => (same i).symm))⟩

/-! ## Controls -/

namespace Control

/-- `+` is callable, `foo` and `bar` are plain symbols, nothing is declared. -/
def base : World where
  callable s := s == "+"
  declared _ _ := False

/-- The same program after `bar` gains an equation. -/
def defined : World where
  callable s := s == "+" || s == "bar"
  declared _ _ := False

/-- The base program after `(: foo Colour)` is added. -/
def declaredFoo : World where
  callable s := s == "+"
  declared s t := s = "foo" ∧ t = "Colour"

/-- `(same + foo)`: the merged policy admits a pair that `get-metatype` tells apart;
the split policy refuses it. -/
theorem plus_and_foo :
    Share .merged base (.symbol "+") (.symbol "foo") ∧
      ¬ Share .split base (.symbol "+") (.symbol "foo") ∧
      Apart base (.symbol "+") (.symbol "foo") := by
  refine ⟨?_, ?_, ?_⟩
  · exact (share_symbols_iff _ _ _ _).2 (Or.inl ⟨by simp [base], by simp [base], rfl⟩)
  · rw [share_symbols_iff]
    simp [witnessOf, base]
  · exact ⟨.pattern (some .grounded), by simp [read, metatype, base]⟩

/-- A definition edit changes the metatype of `bar` but not its merged witness; the split
witness follows the metatype. -/
theorem definition_edit :
    metatype base (.symbol "bar") ≠ metatype defined (.symbol "bar") ∧
      witnessOf .merged base "bar" = witnessOf .merged defined "bar" ∧
      witnessOf .split base "bar" ≠ witnessOf .split defined "bar" ∧
      Share .merged defined (.symbol "bar") (.symbol "foo") ∧
      Apart defined (.symbol "bar") (.symbol "foo") := by
  refine ⟨by simp [metatype, base, defined], rfl, by simp [witnessOf, base, defined], ?_, ?_⟩
  · exact (share_symbols_iff _ _ _ _).2 (Or.inl ⟨by simp [defined], by simp [defined], rfl⟩)
  · exact ⟨.pattern (some .grounded), by simp [read, metatype, defined]⟩

/-- Under either policy a new declaration can withdraw a shared witness: `(same foo bar)`
is admitted before `(: foo Colour)` and refused after it. -/
theorem declaration_withdraws_sharing (policy : Policy) :
    Share policy base (.symbol "foo") (.symbol "bar") ∧
      ¬ Share policy declaredFoo (.symbol "foo") (.symbol "bar") := by
  constructor
  · refine (share_symbols_iff _ _ _ _).2 (Or.inl ⟨by simp [base], by simp [base], ?_⟩)
    cases policy <;> simp [witnessOf, base]
  · rw [share_symbols_iff]
    simp [declaredFoo]

end Control

end Mettapedia.Languages.MeTTa.PeTTa.RuntimeTyping.UnclassifiedWitnesses
