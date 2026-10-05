import Mettapedia.Machines.ResourceOwnership

/-!
# Relocation as an observation-preserving relation on the reachable graph

A collector renames live objects and removes garbage; a copy transports a
residual into independent storage.  Neither is a total bijection of heaps:
renaming is an injection on reachable objects, and removing garbage sends
heaps that differ only in garbage to one heap.  The common contract is a
relation, derived here from four premises on the finite resource heaps of
`ResourceOwnership`.

* **A relocation session** (`LiveRelocation`): an address map on the reachable
  graph that is injective there (each reachable source object has one image,
  and distinct objects with equal contents stay distinct), transports every
  reachable cell with its references and payload, and relocates the
  registered root fields.  It does not constrain unreachable addresses.
* **Reachability is preserved and reflected** (`LiveRelocation.live_forward`,
  `LiveRelocation.live_reflect`), given valid registered roots.
* **Complete root-path observations correspond**: every successful source walk
  from a reachable object has its image (`LiveRelocation.walk_forward`), and
  every successful destination walk from a relocated reachable object is the
  image of a source walk (`LiveRelocation.walk_reflect`).  Aliases are
  preserved and reflected (`LiveRelocation.aliases_iff`); identity is kept
  (`LiveRelocation.distinct_stay_distinct`).
* **Instances** (`LiveRelocation.ofRelocation`, `LiveRelocation.ofCollect`,
  `LiveRelocation.comp`): every injective copy of `ResourceOwnership`, exact
  collection with the identity map, and their composites.  Collection relates
  two heaps that differ only in garbage to one heap, so the relation is not a
  bijection (a control).

Root discovery, the authority to read a physical address, the currency of a
cached observation and concurrent mutation are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction

open Mettapedia.Machines.ResourceOwnership

variable {Address Destination Third Value Value' Value'' Owner : Type}
  [DecidableEq Address] [DecidableEq Destination] [DecidableEq Third] [DecidableEq Owner]

/-- **A relocation session on the reachable graph.** -/
structure LiveRelocation (source : Heap Address Value) (roots : Roots Owner Address)
    (destination : Heap Destination Value') (roots' : Roots Owner Destination) where
  address : Address → Destination
  payload : Value → Value'
  /-- Distinct reachable objects keep distinct images. -/
  injective : ∀ {first second : Address}, Live source roots first → Live source roots second →
    address first = address second → first = second
  /-- Every reachable cell is transported with its references and payload. -/
  lookup_eq : ∀ {a : Address}, Live source roots a →
    destination.lookup (address a) = (source.lookup a).map (Cell.relocate address payload)
  /-- The registered root fields are relocated. -/
  roots_eq : roots' = roots.image fun pair => (pair.1, address pair.2)

namespace LiveRelocation

variable {source : Heap Address Value} {roots : Roots Owner Address}
  {destination : Heap Destination Value'} {roots' : Roots Owner Destination}
  (session : LiveRelocation source roots destination roots')

theorem rootAddresses_eq :
    rootAddresses roots' = (rootAddresses roots).image session.address := by
  calc rootAddresses roots'
      = rootAddresses (roots.image fun pair => (pair.1, session.address pair.2)) :=
        congrArg rootAddresses session.roots_eq
    _ = _ := by
        simp only [rootAddresses, Finset.image_image]
        rfl

/-- **Reachable objects stay reachable.** -/
theorem live_forward {a : Address} (live : Live source roots a) :
    Live destination roots' (session.address a) := by
  induction live with
  | @root a rooted =>
      have here : Live source roots a := .root rooted
      obtain ⟨cell, found⟩ := (source.allocated_iff a).mp rooted.1
      refine .root ⟨(destination.allocated_iff _).mpr ⟨cell.relocate session.address session.payload, ?_⟩, ?_⟩
      · rw [session.lookup_eq here, found]
        rfl
      · rw [session.rootAddresses_eq]
        exact Finset.mem_image.mpr ⟨a, rooted.2, rfl⟩
  | @step a b prior edge ih =>
      obtain ⟨cell, found, reference⟩ := edge
      refine .step ih ⟨cell.relocate session.address session.payload, ?_, ?_⟩
      · rw [session.lookup_eq prior, found]
        rfl
      · exact Finset.mem_image.mpr ⟨b, reference, rfl⟩

/-- **Every reachable destination object is the image of a reachable source
object**, given valid registered roots. -/
theorem live_reflect (valid : ValidRoots source roots) {a' : Destination}
    (live : Live destination roots' a') : ∃ a, Live source roots a ∧ session.address a = a' := by
  induction live with
  | @root a' rooted =>
      have registered := rooted.2
      rw [session.rootAddresses_eq] at registered
      obtain ⟨a, member, rfl⟩ := Finset.mem_image.mp registered
      obtain ⟨pair, present, same⟩ := Finset.mem_image.mp member
      refine ⟨a, .root ⟨same ▸ valid pair present, member⟩, rfl⟩
  | @step a' b' _ edge ih =>
      obtain ⟨a, live, rfl⟩ := ih
      obtain ⟨cell', found, reference⟩ := edge
      rw [session.lookup_eq live] at found
      obtain ⟨cell, sourceFound, rfl⟩ := Option.map_eq_some_iff.mp found
      obtain ⟨b, present, rfl⟩ := Finset.mem_image.mp reference
      exact ⟨b, live_step source roots live sourceFound present, rfl⟩

theorem live_iff (valid : ValidRoots source roots) (a' : Destination) :
    Live destination roots' a' ↔ ∃ a, Live source roots a ∧ session.address a = a' :=
  ⟨session.live_reflect valid, fun ⟨_, live, same⟩ => same ▸ session.live_forward live⟩

omit [DecidableEq Owner] in
/-- The endpoint of a successful walk from a reachable object is reachable. -/
theorem walk_endpoint_live {a endpoint : Address} {cell : Cell Address Value} (path : List Address)
    (live : Live source roots a) (success : walk source a path = some (endpoint, cell)) :
    Live source roots endpoint := by
  induction path generalizing a with
  | nil =>
      cases found : source.lookup a with
      | none => simp [walk, found] at success
      | some here =>
          simp only [walk, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
          exact success.1 ▸ live
  | cons next rest ih =>
      cases found : source.lookup a with
      | none => simp [walk, found] at success
      | some here =>
          simp only [walk, found, Option.bind_some] at success
          split at success
          next reference => exact ih (live_step source roots live found reference) success
          next _ => cases success

/-- **Every successful source walk from a reachable object has its image.** -/
theorem walk_forward {a endpoint : Address} {cell : Cell Address Value} (path : List Address)
    (live : Live source roots a) (success : walk source a path = some (endpoint, cell)) :
    walk destination (session.address a) (path.map session.address) =
      some (session.address endpoint, cell.relocate session.address session.payload) := by
  induction path generalizing a with
  | nil =>
      cases found : source.lookup a with
      | none => simp [walk, found] at success
      | some here =>
          simp only [walk, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
          obtain ⟨rfl, rfl⟩ := success
          simp [walk, session.lookup_eq live, found]
  | cons next rest ih =>
      cases found : source.lookup a with
      | none => simp [walk, found] at success
      | some here =>
          simp only [walk, found, Option.bind_some] at success
          split at success
          next reference =>
            have image : session.address next ∈
                (here.relocate session.address session.payload).references :=
              Finset.mem_image.mpr ⟨next, reference, rfl⟩
            simp only [List.map_cons, walk, session.lookup_eq live, found, Option.map_some,
              Option.bind_some, if_pos image]
            exact ih (live_step source roots live found reference) success
          next _ => cases success

/-- **Every successful destination walk from a relocated reachable object is
the image of a source walk.** -/
theorem walk_reflect {a : Address} {endpoint' : Destination} {cell' : Cell Destination Value'}
    (path' : List Destination) (live : Live source roots a)
    (success : walk destination (session.address a) path' = some (endpoint', cell')) :
    ∃ path endpoint cell, path.map session.address = path' ∧
      walk source a path = some (endpoint, cell) ∧ session.address endpoint = endpoint' ∧
        cell.relocate session.address session.payload = cell' := by
  induction path' generalizing a with
  | nil =>
      simp only [walk, session.lookup_eq live, Option.map_map] at success
      obtain ⟨cell, found, same⟩ := Option.map_eq_some_iff.mp success
      simp only [Function.comp_apply, Prod.mk.injEq] at same
      exact ⟨[], a, cell, rfl, by simp [walk, found], same.1, same.2⟩
  | cons next' rest' ih =>
      simp only [walk, session.lookup_eq live] at success
      cases found : source.lookup a with
      | none => simp [found] at success
      | some here =>
          simp only [found, Option.map_some, Option.bind_some] at success
          split at success
          next reference =>
            obtain ⟨next, present, rfl⟩ := Finset.mem_image.mp reference
            obtain ⟨path, endpoint, cell, mapped, walked, address, relocated⟩ :=
              ih (live_step source roots live found present) success
            refine ⟨next :: path, endpoint, cell, by simp [mapped], ?_, address, relocated⟩
            simp [walk, found, present, walked]
          next _ => cases success

/-- **Aliases are preserved and reflected**: two destination paths from
relocated reachable objects meet exactly when two source paths that they image
meet. -/
theorem aliases_iff {a b : Address} (liveA : Live source roots a) (liveB : Live source roots b)
    (left' right' : List Destination) :
    Aliases destination (session.address a) left' (session.address b) right' ↔
      ∃ left right, left.map session.address = left' ∧ right.map session.address = right' ∧
        Aliases source a left b right := by
  constructor
  · rintro ⟨endpoint', leftWalk, rightWalk⟩
    obtain ⟨⟨leftEnd', leftCell'⟩, leftSuccess, rfl⟩ := Option.map_eq_some_iff.mp leftWalk
    obtain ⟨⟨rightEnd', rightCell'⟩, rightSuccess, same⟩ := Option.map_eq_some_iff.mp rightWalk
    obtain ⟨left, leftEnd, leftCell, leftMapped, leftSource, leftAddress, _⟩ :=
      session.walk_reflect left' liveA leftSuccess
    obtain ⟨right, rightEnd, rightCell, rightMapped, rightSource, rightAddress, _⟩ :=
      session.walk_reflect right' liveB rightSuccess
    have equal : rightEnd = leftEnd :=
      session.injective (walk_endpoint_live right liveB rightSource)
        (walk_endpoint_live left liveA leftSource)
        (rightAddress.trans (same.trans leftAddress.symm))
    refine ⟨left, right, leftMapped, rightMapped, leftEnd, by simp [leftSource], ?_⟩
    simp [rightSource, equal]
  · rintro ⟨left, right, rfl, rfl, endpoint, leftWalk, rightWalk⟩
    obtain ⟨⟨leftEnd, leftCell⟩, leftSuccess, rfl⟩ := Option.map_eq_some_iff.mp leftWalk
    obtain ⟨⟨rightEnd, rightCell⟩, rightSuccess, same⟩ := Option.map_eq_some_iff.mp rightWalk
    refine ⟨session.address leftEnd, ?_, ?_⟩
    · simp [session.walk_forward left liveA leftSuccess]
    · simp only at same
      simp [session.walk_forward right liveB rightSuccess, same]

/-- **Distinct reachable objects stay distinct**, whatever their contents. -/
theorem distinct_stay_distinct {a b : Address} (liveA : Live source roots a)
    (liveB : Live source roots b) (different : a ≠ b) : session.address a ≠ session.address b :=
  fun same => different (session.injective liveA liveB same)

/-! ## Instances -/

omit [DecidableEq Owner] in
/-- Relocating a cell by the identity maps keeps it. -/
theorem relocate_id (cell : Cell Address Value) : cell.relocate id id = cell := by
  cases cell
  simp [Cell.relocate]

/-- **Every injective copy is a relocation session**, for any roots. -/
def ofRelocation (copy : Relocation source destination) (roots : Roots Owner Address) :
    LiveRelocation source roots destination (copy.roots roots) where
  address := copy.address
  payload := copy.payload
  injective _ _ same := copy.injective same
  lookup_eq _ := copy.lookup_eq _
  roots_eq := rfl

/-- **Exact collection is a relocation session** with the identity map. -/
noncomputable def ofCollect (source : Heap Address Value) (roots : Roots Owner Address) :
    LiveRelocation source roots (collect source roots) roots where
  address := id
  payload := id
  injective _ _ same := same
  lookup_eq {a} live := by
    show (collect source roots).lookup a = _
    rw [lookup_collect_of_live source roots live]
    cases source.lookup _ <;> simp [relocate_id]
  roots_eq := by
    ext pair
    simp

omit [DecidableEq Owner] [DecidableEq Address] in
theorem relocate_comp (first : Address → Destination) (firstPayload : Value → Value')
    (second : Destination → Third) (secondPayload : Value' → Value'') (cell : Cell Address Value) :
    (cell.relocate first firstPayload).relocate second secondPayload =
      cell.relocate (second ∘ first) (secondPayload ∘ firstPayload) := by
  simp [Cell.relocate, Finset.image_image]

/-- **Relocation sessions compose.** -/
def comp {third : Heap Third Value''} {roots'' : Roots Owner Third}
    (second : LiveRelocation destination roots' third roots'') :
    LiveRelocation source roots third roots'' where
  address := second.address ∘ session.address
  payload := second.payload ∘ session.payload
  injective liveA liveB same :=
    session.injective liveA liveB
      (second.injective (session.live_forward liveA) (session.live_forward liveB) same)
  lookup_eq live := by
    simp only [Function.comp_apply]
    rw [second.lookup_eq (session.live_forward live), session.lookup_eq live, Option.map_map]
    congr 1
    funext cell
    exact relocate_comp _ _ _ _ cell
  roots_eq := by
    calc roots'' = roots'.image (fun pair => (pair.1, second.address pair.2)) := second.roots_eq
      _ = (roots.image fun pair => (pair.1, session.address pair.2)).image
            (fun pair => (pair.1, second.address pair.2)) :=
          congrArg (fun current : Roots Owner Destination =>
            current.image fun pair => (pair.1, second.address pair.2)) session.roots_eq
      _ = _ := by
          rw [Finset.image_image]
          rfl

end LiveRelocation

end Mettapedia.GSLT.Distinction
