import Mettapedia.SetTheory.ValuesAndLocations.Readings
import Mettapedia.SetTheory.ValuesAndLocations.Reuse
import Mettapedia.SetTheory.ValuesAndLocations.Persistent
import Mettapedia.SetTheory.ValuesAndLocations.StepReuse
import Mettapedia.SetTheory.ValuesAndLocations.Occurrences

/-!
# Values and locations

`{a b}` can be read as a value (a set or a bag) or as the contents of a location (a space). The
modules here make the two readings exact, connect them, and prove when a runtime may implement the
value reading by updating in place.

* `Readings`: the value reading (order invisible, repetition invisible in sets and counted in bags,
  when adding changes nothing); the location reading (a store with allocation, writes and
  revisions; two spaces with equal contents are two locations; no identity by contents; the
  revision contract along every run); the snapshot as the bridge from locations to values; set
  and bag locations.
* `Reuse`: a heap of cells under roots. Writing in place carries out the value semantics exactly
  when every other root that references the cell would see no change; for bags, exactly when no
  other root references it (a reference count of one). The implementation that tests this before
  reusing a cell refines the value semantics on every program, and updates a set held by one name
  in place without allocating.
* `Persistent`: a binary trie with path copying: every old version stays valid, and an insert
  allocates one node per bit of its key and one more.
* `StepReuse`: in the occurrence store of the interaction step, a step that takes the atom holding
  a value may reuse its cell for the successor when nothing else references it; a step that keeps
  the atom may not, and neither may a take whose old value a name still holds.
* `Occurrences`: occurrences, bags and sets as two forgetful maps; a set store is one whose labels
  name its occurrences; matching a bag pattern modulo associativity and commutativity is choosing
  a witness, which one pass checks.
-/
