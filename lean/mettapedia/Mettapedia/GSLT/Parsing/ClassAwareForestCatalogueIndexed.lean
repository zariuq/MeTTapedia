import Mettapedia.GSLT.Parsing.ClassAwareCatalogueValidation
import Mettapedia.GSLT.Parsing.ClassAwareChartIndex
import Std.Data.HashMap.Lemmas

/-!
# Catalogue rounds over hashed families and caches

`ClassAwareForestCatalogue.catalogue?` finds the families of every key by
scanning the whole forest and finds cached trees by searching the cache list,
in every round. The rounds below group the families by parent key once and
read each round's cache through a hash table built once per round. The rounds,
their order and their convergence test are unchanged, and each definition is
proved equal to the original.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareForestCatalogueIndexed

open ClassAwarePackedForest ClassAwarePackedForestKBest
open ClassAwareParserPackCertificate ClassAwareParserPackCorrespondence
open PackedForestCatalogue PackedForestSelection ClassAwareForestCatalogue

/-- Families grouped by parent key; each group keeps forest order. -/
def familyTable (forest : Forest) : Std.HashMap NodeKey (List Family) :=
  forest.families.foldr (fun family table =>
    table.insert family.parent (family :: table.getD family.parent [])) {}

theorem foldr_family_getD (families : List Family) (key : NodeKey) :
    (families.foldr (fun family table =>
        table.insert family.parent (family :: table.getD family.parent []))
      ({} : Std.HashMap NodeKey (List Family))).getD key [] =
      families.filter fun family => family.parent == key := by
  induction families with
  | nil => simp
  | cons first rest ih =>
    rw [List.foldr_cons, Std.HashMap.getD_insert, List.filter_cons]
    by_cases same : first.parent = key
    · subst same
      simp [ih]
    · have different : (first.parent == key) = false := by simpa using same
      simp only [different, Bool.false_eq_true, if_false, ih]

theorem familyTable_getD (forest : Forest) (key : NodeKey) :
    (familyTable forest).getD key [] = familiesAt forest key :=
  foldr_family_getD forest.families key

/-- A cache as a hash table. The first entry for a key wins, as in `lookup`. -/
def cacheTable (cache : Store) : Std.HashMap NodeKey (List Tree) :=
  cache.foldr (fun entry table => table.insert entry.1 entry.2) {}

theorem cacheTable_getD (cache : Store) (key : NodeKey) :
    (cacheTable cache).getD key [] = lookup cache key := by
  induction cache with
  | nil => simp [cacheTable, lookup]
  | cons first rest ih =>
    simp only [cacheTable, List.foldr_cons, Std.HashMap.getD_insert] at ih ⊢
    by_cases same : first.1 = key
    · subst same
      simp [lookup]
    · have different : (first.1 == key) = false := by simpa using same
      simp only [different, Bool.false_eq_true, if_false, ih, lookup, List.find?_cons,
        decide_eq_false same]

def nextIndexed (table : Std.HashMap NodeKey (List Family)) (allow : Family → Bool)
    (cache : Std.HashMap NodeKey (List Tree)) (key : NodeKey) : List Tree :=
  (table.getD key []).flatMap fun family =>
    if allow family then
      (combinations ((nodeChildren family.children).map fun child => cache.getD child [])).map
        (.node family)
    else []

theorem nextIndexed_eq (forest : Forest) (allow : Family → Bool) (cache : Store) (key : NodeKey) :
    nextIndexed (familyTable forest) allow (cacheTable cache) key =
      next (familiesAt forest) (fun family => nodeChildren family.children) allow (lookup cache) key := by
  simp only [nextIndexed, next, familyTable_getD, cacheTable_getD]

def roundIndexed (table : Std.HashMap NodeKey (List Family)) (allow : Family → Bool)
    (keys : List NodeKey) (cache : Store) : Store :=
  let current := cacheTable cache
  snapshot keys (nextIndexed table allow current)

theorem roundIndexed_eq (forest : Forest) (allow : Family → Bool) (keys : List NodeKey) (cache : Store) :
    roundIndexed (familyTable forest) allow keys cache =
      PackedForestCatalogue.round (familiesAt forest) (fun family => nodeChildren family.children)
        allow keys cache := by
  simp only [roundIndexed, PackedForestCatalogue.round]
  congr 1
  funext key
  exact nextIndexed_eq forest allow cache key

def finishIndexed? (table : Std.HashMap NodeKey (List Family)) (allow : Family → Bool)
    (keys : List NodeKey) : Nat → Store → Option Store
  | 0, _ => none
  | rounds + 1, cache =>
    let updated := roundIndexed table allow keys cache
    if updated = cache then some cache else finishIndexed? table allow keys rounds updated

theorem finishIndexed?_eq (forest : Forest) (allow : Family → Bool) (keys : List NodeKey) :
    ∀ (rounds : Nat) (cache : Store),
      finishIndexed? (familyTable forest) allow keys rounds cache =
        PackedForestCatalogue.finish? (familiesAt forest) (fun family => nodeChildren family.children)
          allow keys rounds cache
  | 0, _ => rfl
  | rounds + 1, cache => by
    simp only [finishIndexed?, PackedForestCatalogue.finish?, roundIndexed_eq,
      finishIndexed?_eq forest allow keys rounds]

def keysIndexed (forest : Forest) : List NodeKey :=
  Mettapedia.Util.LinearHash.eraseDupsFast (forest.roots ++ forest.families.map Family.parent)

theorem keysIndexed_eq (forest : Forest) : keysIndexed forest = ClassAwareForestCatalogue.keys forest :=
  Mettapedia.Util.LinearHash.eraseDupsFast_eq _

def catalogueIndexed? (forest : Forest) (allow : Family → Bool) (rounds : Nat) : Option Store :=
  finishIndexed? (familyTable forest) allow (keysIndexed forest) rounds []

theorem catalogueIndexed?_eq (forest : Forest) (allow : Family → Bool) (rounds : Nat) :
    catalogueIndexed? forest allow rounds = ClassAwareForestCatalogue.catalogue? forest allow rounds := by
  simp only [catalogueIndexed?, ClassAwareForestCatalogue.catalogue?, PackedForestCatalogue.catalogue?,
    keysIndexed_eq, finishIndexed?_eq]

def certificatesIndexed? (forest : Forest) (allow : Family → Bool) (key : NodeKey) (rounds : Nat) :
    Option (List Certificate) :=
  (catalogueIndexed? forest allow rounds).map fun store => (lookup store key).filterMap restore

def validateIndexed? (forest : Forest) (allow : Family → Bool) (key : NodeKey) (rounds : Nat)
    (native : List Certificate) : Option Bool :=
  (certificatesIndexed? forest allow key rounds).map fun reference => decide (native.Perm reference)

theorem validateIndexed?_eq (forest : Forest) (allow : Family → Bool) (key : NodeKey) (rounds : Nat)
    (native : List Certificate) :
    validateIndexed? forest allow key rounds native =
      ClassAwareCatalogueValidation.validate? forest allow key rounds native := by
  simp only [validateIndexed?, certificatesIndexed?, ClassAwareCatalogueValidation.validate?,
    ClassAwareCatalogueValidation.certificates?, catalogueIndexed?_eq]

#print axioms catalogueIndexed?_eq
#print axioms validateIndexed?_eq

end Mettapedia.GSLT.Parsing.ClassAwareForestCatalogueIndexed
