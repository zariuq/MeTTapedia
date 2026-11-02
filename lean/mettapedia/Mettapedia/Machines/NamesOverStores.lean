import Mettapedia.Machines.ShapeCutComposition

/-!
# Content names across storage representations

A codec preserves a declared term carrier, not an unspecified semantic
congruence. A chosen home gives a canonical name in the disjoint union of
stores. Other decodable codes may be aliases. Changing homes can change names;
retaining old stores preserves their meanings but does not preserve canonical
comparison. A checked directory relocation instead preserves every name.

These are logical interfaces and concrete shape/record instances. They do not
establish constant-time comparison, native pointer validity, concurrent
publication, or rho-calculus quotation laws. Content names are distinct from
the occurrence IDs of PersistentOccurrenceSegments.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NamesOverStores

variable {Term Store Name Place : Type} {Code : Store → Type}

structure Codec (Term Code : Type) where
  encode : Term → Code
  decode : Code → Option Term
  roundtrip : ∀ t, decode (encode t) = some t

theorem Codec.encode_injective {C : Type} (c : Codec Term C) :
    Function.Injective c.encode := by
  intro x y equal
  have := congrArg c.decode equal
  simpa only [c.roundtrip, Option.some.injEq] using this

/-- Raw codes have a store tag; this alone does not exclude aliases. -/
abbrev Address (Code : Store → Type) := Sigma Code

def decode (family : ∀ s, Codec Term (Code s)) (a : Address Code) : Option Term :=
  (family a.1).decode a.2

def name (family : ∀ s, Codec Term (Code s)) (home : Term → Store)
    (t : Term) : Address Code := ⟨home t, (family (home t)).encode t⟩

@[simp] theorem decode_name (family : ∀ s, Codec Term (Code s))
    (home : Term → Store) (t : Term) : decode family (name family home t) = some t :=
  (family (home t)).roundtrip t

theorem name_injective (family : ∀ s, Codec Term (Code s)) (home : Term → Store) :
    Function.Injective (name family home) := by
  intro x y same
  have := congrArg (decode family) same
  simpa only [decode_name, Option.some.injEq] using this

theorem name_eq_iff (family : ∀ s, Codec Term (Code s)) (home : Term → Store)
    (x y : Term) : name family home x = name family home y ↔ x = y :=
  (name_injective family home).eq_iff

/-- Comparison by raw name is complete only on the canonical image. -/
theorem canonical_decode_injective (family : ∀ s, Codec Term (Code s))
    (home : Term → Store) :
    Set.InjOn (decode family) (Set.range (name family home)) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ equal
  have : x = y := by simpa only [decode_name, Option.some.injEq] using equal
  subst y
  rfl

/-- A changed home necessarily changes the raw store-qualified name. -/
theorem changed_home_changes_name (family : ∀ s, Codec Term (Code s))
    (before after : Term → Store) (t : Term) (different : before t ≠ after t) :
    name family before t ≠ name family after t := by
  intro equal
  exact different (congrArg Sigma.fst equal)

def recordCodec (Term : Type) : Codec Term Term := ⟨id, some, fun _ => rfl⟩

def shapeCodec {α : Type} (cut : ShapeStore.Cut α) :
    Codec (ShapeStore.Tm α) (ShapeStore.Row α) :=
  ⟨cut.d, ShapeStore.reassemble, cut.sec⟩

/-- A store may encode only an admitted part of the term carrier. -/
structure CodecOn (Term Code : Type) where
  accepts : Term → Prop
  encode : {t : Term // accepts t} → Code
  decode : Code → Option Term
  roundtrip : ∀ t, decode (encode t) = some t.val

structure AdmittedNaming (Term : Type) {Store : Type} (Code : Store → Type) where
  stores : ∀ s, CodecOn Term (Code s)
  home : Term → Store
  eligible : ∀ t, (stores (home t)).accepts t

def AdmittedNaming.name (naming : AdmittedNaming Term Code) (t : Term) : Address Code :=
  ⟨naming.home t, (naming.stores (naming.home t)).encode ⟨t, naming.eligible t⟩⟩

def AdmittedNaming.read (naming : AdmittedNaming Term Code) (a : Address Code) : Option Term :=
  (naming.stores a.1).decode a.2

@[simp] theorem AdmittedNaming.read_name (naming : AdmittedNaming Term Code) (t : Term) :
    naming.read (naming.name t) = some t :=
  (naming.stores (naming.home t)).roundtrip ⟨t, naming.eligible t⟩

theorem AdmittedNaming.name_injective (naming : AdmittedNaming Term Code) :
    Function.Injective naming.name := by
  intro x y same
  have h := congrArg naming.read same
  simpa only [naming.read_name, Option.some.injEq] using h

/-- Concrete S1 instance: one table per skeleton, with just the ordered hole
values as its row code. Admission excludes terms assigned another skeleton. -/
def shapeTableNaming {α : Type} (cut : ShapeStore.Cut α) :
    AdmittedNaming (ShapeStore.Tm α) (fun _ : ShapeStore.Skel α => List (ShapeStore.Tm α)) where
  stores := fun skeleton =>
    { accepts := fun t => (cut.d t).1 = skeleton
      encode := fun t => (cut.d t.val).2
      decode := fun values => ShapeStore.reassemble (skeleton, values)
      roundtrip := by
        rintro ⟨t, chosen⟩
        change ShapeStore.reassemble (skeleton, (cut.d t).2) = some t
        rw [← chosen]
        exact cut.sec t }
  home := fun t => (cut.d t).1
  eligible := fun _ => rfl

theorem shapeTableNaming_code {α : Type} (cut : ShapeStore.Cut α) (t : ShapeStore.Tm α) :
    (shapeTableNaming cut).name t = ⟨(cut.d t).1, (cut.d t).2⟩ := rfl

/-- A re-cut preserves decoding, but does not promise equality of raw codes. -/
theorem shape_recut {α : Type} (a b : ShapeStore.Cut α) (t : ShapeStore.Tm α) :
    (shapeCodec a).decode ((shapeCodec a).encode t) =
      (shapeCodec b).decode ((shapeCodec b).encode t) := by
  rw [(shapeCodec a).roundtrip, (shapeCodec b).roundtrip]

/-! ## Routing-only evolution -/

/-- Keep the old address space and add a new one. The old and new store types
may differ; neither existing names nor old decoding are rewritten. -/
def extend (old : Name → Option Term) (new : Place → Option Term) :
    Sum Name Place → Option Term
  | .inl n => old n
  | .inr p => new p

theorem extend_old (old : Name → Option Term) (new : Place → Option Term) (n : Name) :
    extend old new (.inl n) = old n := rfl

theorem extension_preserves_observers {Result : Type}
    (old : Name → Option Term) (new : Place → Option Term)
    (observe : Option Term → Result) (n : Name) :
    observe (extend old new (.inl n)) = observe (old n) := rfl

/-! ## Stable names with moving placements -/

abbrev Directory (Name Place : Type) := Name → Option Place

def resolve (read : Place → Option Term) (directory : Directory Name Place)
    (n : Name) : Option Term := (directory n).bind read

/-- Publication succeeds only if the new placement decodes to the existing
live value. Missing old names and undecodable targets are refused. -/
def relocate [DecidableEq Name] [DecidableEq Term]
    (read : Place → Option Term) (directory : Directory Name Place)
    (n : Name) (target : Place) : Option (Directory Name Place) :=
  match resolve read directory n, read target with
  | some old, some fresh =>
      if old = fresh then some (Function.update directory n (some target)) else none
  | _, _ => none

theorem relocate_preserves [DecidableEq Name] [DecidableEq Term]
    (read : Place → Option Term) (directory next : Directory Name Place)
    (n : Name) (target : Place)
    (accepted : relocate read directory n target = some next) :
    resolve read next = resolve read directory := by
  unfold relocate at accepted
  split at accepted <;> try contradiction
  rename_i old fresh hold hfresh
  split at accepted <;> try contradiction
  rename_i equal
  cases accepted
  funext queried
  by_cases same : queried = n
  · subst queried
    simp [resolve, hfresh, ← equal, ← hold]
  · simp [resolve, Function.update_of_ne same]

def relocateMany [DecidableEq Name] [DecidableEq Term]
    (read : Place → Option Term) :
    List (Name × Place) → Directory Name Place → Option (Directory Name Place)
  | [], directory => some directory
  | (n, target) :: rest, directory =>
      (relocate read directory n target).bind (relocateMany read rest)

theorem relocateMany_preserves [DecidableEq Name] [DecidableEq Term]
    (read : Place → Option Term) (moves : List (Name × Place))
    (directory next : Directory Name Place)
    (accepted : relocateMany read moves directory = some next) :
    resolve read next = resolve read directory := by
  induction moves generalizing directory with
  | nil =>
      have : directory = next := Option.some.inj accepted
      subst next
      rfl
  | cons move rest ih =>
      simp only [relocateMany] at accepted
      obtain ⟨middle, changed, restAccepted⟩ := Option.bind_eq_some_iff.mp accepted
      exact (ih middle restAccepted).trans
        (relocate_preserves read directory middle move.1 move.2 changed)

theorem relocate_preserves_observers [DecidableEq Name] [DecidableEq Term]
    {Result : Type} (read : Place → Option Term) (directory next : Directory Name Place)
    (n : Name) (target : Place) (observe : (Name → Option Term) → Result)
    (accepted : relocate read directory n target = some next) :
    observe (resolve read next) = observe (resolve read directory) := by
  rw [relocate_preserves read directory next n target accepted]

/-- Name-preserving relocation cannot introduce new aliases among names. -/
theorem relocate_preserves_unique [DecidableEq Name] [DecidableEq Term]
    (read : Place → Option Term) (directory next : Directory Name Place)
    (n : Name) (target : Place)
    (unique : ∀ x y t, resolve read directory x = some t →
      resolve read directory y = some t → x = y)
    (accepted : relocate read directory n target = some next) :
    ∀ x y t, resolve read next x = some t → resolve read next y = some t → x = y := by
  rw [relocate_preserves read directory next n target accepted]
  exact unique

namespace Controls

def duplicateFamily (_ : Bool) : Codec Nat Nat := recordCodec Nat

theorem two_stores_alias :
    decode duplicateFamily ⟨false, 7⟩ = decode duplicateFamily ⟨true, 7⟩ ∧
    (⟨false, 7⟩ : Address (fun _ : Bool => Nat)) ≠ ⟨true, 7⟩ := by decide

theorem routing_keeps_meaning_not_canonical_comparison :
    name duplicateFamily (fun _ => false) 7 ≠ name duplicateFamily (fun _ => true) 7 ∧
    decode duplicateFamily (name duplicateFamily (fun _ => false) 7) =
      decode duplicateFamily (name duplicateFamily (fun _ => true) 7) := by decide

def placements : Bool → Option Nat := fun _ => some 7
def directory : Nat → Option Bool := fun n => if n = 0 then some false else none

example : relocate placements directory 0 true =
    some (Function.update directory 0 (some true)) := by simp [relocate, resolve, placements, directory]

example : relocate placements directory 1 true = none := by decide

/-- Overwriting a physical slot without redirecting holders retargets a name. -/
theorem overwritten_slot_retargets :
    resolve (fun _ : Bool => some 8) directory 0 ≠ resolve placements directory 0 := by decide

example : relocate (fun b : Bool => some (if b then 8 else 7)) directory 0 true = none := by decide

end Controls

#print axioms name_injective
#print axioms canonical_decode_injective
#print axioms relocateMany_preserves
#print axioms relocate_preserves_unique

end Mettapedia.Machines.NamesOverStores
