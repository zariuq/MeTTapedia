import Mettapedia.Machines.NameSupplies.SharedSupplies
import Mettapedia.Algorithms.Collections.StableKeyEncoding

/-!
# Portable exact names and local handles

An issuer coordinate distinguishes separately provisioned roots. Within one
root, the share discipline supplies the stamp. The wire format stores both,
and uses a prefix code for trees. Runtime handles index the retained names;
the same portable name can have different handles in different processes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies.PortableNames

open Mettapedia.Algorithms.Collections.StableKeyEncoding

/-- An issuer designates an incarnation of a root, not a worker. A new root
must use a different issuer or restore the previous supply state. -/
structure Name where
  issuer : ℕ
  stamp : ShareName
  deriving DecidableEq, Repr

private def writeShare : Share → List ℕ
  | .none => [0]
  | .all => [1]
  | .node left right => 2 :: (writeShare left ++ writeShare right)

private def readShare : ℕ → List ℕ → Option (Share × List ℕ)
  | fuel + 1, tag :: tokens =>
    match tag with
    | 0 => some (.none, tokens)
    | 1 => some (.all, tokens)
    | 2 => do
      let (left, rest) ← readShare fuel tokens
      let (right, rest) ← readShare fuel rest
      pure (.node left right, rest)
    | _ => none
  | _, _ => none

private theorem read_write (share : Share) (rest : List ℕ) (fuel : ℕ)
    (enough : (writeShare share).length ≤ fuel) :
    readShare fuel (writeShare share ++ rest) = some (share, rest) := by
  induction share generalizing fuel rest with
  | none =>
      cases fuel with
      | zero => simp [writeShare] at enough
      | succ fuel => rfl
  | all =>
      cases fuel with
      | zero => simp [writeShare] at enough
      | succ fuel => rfl
  | node left right leftRead rightRead =>
      cases fuel with
      | zero => simp [writeShare] at enough
      | succ fuel =>
          simp only [writeShare, List.length_cons, List.length_append] at enough
          simp [writeShare, readShare, List.append_assoc,
            leftRead (writeShare right ++ rest) fuel (by omega), rightRead rest fuel (by omega)]

def serialize (name : Name) : List ℕ :=
  name.issuer :: name.stamp.2 :: writeShare name.stamp.1

def deserialize : List ℕ → Option Name
  | issuer :: clock :: tokens => do
      let (share, rest) ← readShare tokens.length tokens
      if rest.isEmpty then some ⟨issuer, (share, clock)⟩ else none
  | _ => none

theorem deserialize_serialize (name : Name) : deserialize (serialize name) = some name := by
  cases name with
  | mk issuer stamp =>
    obtain ⟨share, clock⟩ := stamp
    have decoded := read_write share [] (writeShare share).length (le_refl _)
    simp [serialize, deserialize, List.append_nil] at decoded ⊢
    simp [decoded]

theorem serialize_injective : Function.Injective serialize := by
  intro first second equal
  have decoded := congrArg deserialize equal
  simpa only [deserialize_serialize, Option.some.injEq] using decoded

/-- The local table uses the first retained slot of a name. Interning an
already retained name reuses that slot. -/
def intern (keys : List Name) (name : Name) : List Name × ℕ :=
  (extend keys name, keys.idxOf name)

def importName (keys : List Name) (tokens : List ℕ) : Option (List Name × ℕ) :=
  (deserialize tokens).map (intern keys)

def exportName (keys : List Name) (handle : ℕ) : Option (List ℕ) :=
  keys[handle]?.map serialize

theorem export_import (keys : List Name) (name : Name) :
    exportName (intern keys name).1 (intern keys name).2 = some (serialize name) := by
  have hit := List.getElem?_idxOf (mem_extend_self keys name)
  rw [extend_idxOf] at hit
  simp [exportName, intern, hit]

/-- The round trip uses the same legal local handle, even when the two
processes happen to assign different indices to the wire name. -/
theorem import_export (keys : List Name) (unique : keys.Nodup) (handle : ℕ)
    (live : handle < keys.length) :
    (exportName keys handle).bind (importName keys) = some (keys, handle) := by
  let name := keys[handle]
  have found : name ∈ keys := List.getElem_mem live
  simp [exportName, List.getElem?_eq_getElem live, importName, deserialize_serialize, intern, name,
    extend, found, unique.idxOf_getElem]

theorem same_handle_iff (keys : List Name) (first second : Name)
    (present : first ∈ keys) :
    keys.idxOf first = keys.idxOf second ↔ first = second :=
  List.idxOf_inj present

theorem intern_fresh_iff (keys : List Name) (name : Name) :
    (intern keys name).2 = keys.length ↔ name ∉ keys :=
  List.idxOf_eq_length_iff

theorem malformed_tree : deserialize [5, 0, 2, 1] = none := by decide

private theorem drawn_prefix (pool : Pool ShareSupply ShareName) (events : List (Operation ShareSupply)) :
    pool.drawn <+: (pool.run shareDiscipline events).drawn := by
  induction events generalizing pool with
  | nil => exact List.prefix_refl _
  | cons event events ih =>
      exact (List.prefix_append pool.drawn (event.names shareDiscipline)).trans (ih (pool.step shareDiscipline event))

/-- Retain the wire names issued by this pool through its actual fork, join
and draw operations. Earlier handles still export the same bytes. A live
supply's next wire name is absent, so its import gets a fresh local handle. -/
theorem fork_join_import (issuer : ℕ) (pool : Pool ShareSupply ShareName)
    (shared : WellShared pool) (events : List (Operation ShareSupply))
    (valid : pool.Valid shareDiscipline events) (keys : List Name) (unique : keys.Nodup)
    (recorded : ∀ key ∈ keys, key.issuer = issuer → key.stamp ∈ pool.drawn)
    (supply : ShareSupply) (live : supply ∈ (pool.run shareDiscipline events).live) :
    let final := pool.run shareDiscipline events
    let retained := (encode keys (final.drawn.map (Name.mk issuer))).1
    let next := Name.mk issuer (shareDiscipline.draw supply).1
    retained.Nodup ∧
      (∀ index, index < keys.length → exportName retained index = exportName keys index) ∧
      importName retained (serialize next) = some (retained ++ [next], retained.length) := by
  dsimp only
  let final := pool.run shareDiscipline events
  let retained := (encode keys (final.drawn.map (Name.mk issuer))).1
  let next := Name.mk issuer (shareDiscipline.draw supply).1
  have keepsPrefix := encode_prefix keys (final.drawn.map (Name.mk issuer))
  have nextUnused : next ∉ retained := by
    intro present
    have absent := next_name_fresh (wellShared_run pool shared events valid) live
    apply absent
    rcases (encode_membership keys _ next).mp present with earlier | inserted
    · exact (drawn_prefix pool events).subset (recorded next earlier rfl)
    · obtain ⟨stamp, used, same⟩ := List.mem_map.mp inserted
      have stampEq := congrArg Name.stamp same
      change next.stamp ∈ final.drawn
      rw [← stampEq]
      exact used
  refine ⟨encode_nodup _ _ unique, ?_, ?_⟩
  · intro index bounded
    change exportName retained index = exportName keys index
    obtain ⟨tail, keeps⟩ := keepsPrefix
    change keys ++ tail = retained at keeps
    simp [← keeps, exportName, List.getElem?_append, bounded]
  · change importName retained (serialize next) = some (retained ++ [next], retained.length)
    simp [importName, deserialize_serialize, intern, extend, nextUnused]

/-- Persisting the exact keys in slot order preserves the local dictionary
on restart as well as the wire identities across machines. -/
theorem restart_dictionary (keys : List Name) :
    (keys.map serialize).mapM deserialize = some keys := by
  induction keys with
  | nil => rfl
  | cons name keys ih => simp [List.mapM_cons, deserialize_serialize, ih]

/-- Persist the next draw coordinate, which includes the issuer and the
clock. A restart can retain the issuer when it restores this coordinate. -/
theorem restart_next_draw (issuer : ℕ) (supply : ShareSupply) :
    (deserialize (serialize ⟨issuer, (supply.share, supply.clock)⟩)).map
      (fun name => (name.issuer, shareDiscipline.draw ⟨name.stamp.1, name.stamp.2⟩)) =
      some (issuer, shareDiscipline.draw supply) := by
  rw [deserialize_serialize]
  cases supply
  rfl

/-- The root clock implements counting while preserving the same wire format
used by split shares. Distinct issuers also cannot name the same wire object. -/
theorem process_counters (issuer first second : ℕ) :
    Name.mk issuer (shareDiscipline.draw ⟨.all, first⟩).1 =
      Name.mk issuer (shareDiscipline.draw ⟨.all, second⟩).1 ↔ first = second := by
  simp [shareDiscipline]

theorem issuers_distinct (first second : Name) (apart : first.issuer ≠ second.issuer) :
    serialize first ≠ serialize second := fun h => apart (congrArg Name.issuer (serialize_injective h))

#print axioms deserialize_serialize
#print axioms export_import
#print axioms import_export
#print axioms fork_join_import
#print axioms restart_dictionary
#print axioms restart_next_draw
#print axioms process_counters
#print axioms issuers_distinct
#print axioms malformed_tree

end Mettapedia.Machines.NameSupplies.PortableNames
