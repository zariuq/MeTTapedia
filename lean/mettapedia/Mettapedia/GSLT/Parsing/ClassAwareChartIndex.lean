import Mettapedia.GSLT.Parsing.ClassAwarePackedForestSaturation
import Mettapedia.Util.LinearHash
import Mettapedia.Util.ListBuckets

/-! A cursor index for reference-chart consequence enumeration. Every bucket
is constructed from the same recognized keys, and indexed enumeration is
proved equal to the original list implementation, including alternative order. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartIndex

open ClassAwarePackedForest ClassAwarePackedForestSaturation
open ClassAwareParserPackCorrespondence ClassAwareParserPackEnumeration ParserProfileSemantics

deriving instance Hashable for TerminalMatcher
deriving instance Hashable for NodeKey
deriving instance Hashable for ProductionRef
deriving instance Hashable for ChildRef
deriving instance Hashable for Family

def recognizedKeys (forest : Forest) : List NodeKey :=
  Mettapedia.Util.LinearHash.eraseDupsFast (forest.families.map Family.parent)

theorem recognizedKeys_exact (forest : Forest) : recognizedKeys forest = recognizedNodeKeys forest :=
  Mettapedia.Util.LinearHash.eraseDupsFast_eq _

structure Index where
  keys : List NodeKey
  buckets : Array (List NodeKey)

def build (keys : List NodeKey) (bound : Nat) : Index :=
  ⟨keys, Mettapedia.Util.ListBuckets.build NodeKey.start (bound + 1) keys⟩

def lookup (index : Index) (sort : String) (start : Nat) : List NodeKey :=
  match index.buckets[start]? with
  | some bucket => bucket.filter (fun key => key.resultSort == sort)
  | none => index.keys.filter (fun key => key.resultSort == sort && key.start == start)

theorem lookup_build (keys : List NodeKey) (bound : Nat) (sort : String) (start : Nat) :
    lookup (build keys bound) sort start =
      keys.filter (fun key => key.resultSort == sort && key.start == start) := by
  by_cases inside : start < bound + 1
  · simp [lookup, build, Mettapedia.Util.ListBuckets.build_eq, inside, List.filter_filter, Bool.and_comm]
  · simp [lookup, build, Mettapedia.Util.ListBuckets.build_eq, inside]

def items (index : Index) (profile : ParserProfileLayer) (input : List Nat) :
    List PackItem → Nat → List RecognizedItemsRow
  | [], cursor => [⟨cursor, []⟩]
  | .terminal matcher :: rest, cursor =>
    match terminalMatch? profile input matcher cursor with
    | none => []
    | some (middle, _) => (items index profile input rest middle).map fun tail =>
      ⟨tail.stop, .terminal matcher cursor middle :: tail.children⟩
  | .nonterminal sort :: rest, cursor =>
    (lookup index sort cursor).flatMap fun key =>
      (items index profile input rest key.stop).map fun tail =>
        ⟨tail.stop, .node key :: tail.children⟩

theorem items_exact (forest : Forest) (profile : ParserProfileLayer) (input : List Nat)
    (bound : Nat) (body : List PackItem) (start : Nat) :
    items (build (recognizedNodeKeys forest) bound) profile input body start =
      enumerateRecognizedItems forest profile input body start := by
  induction body generalizing start with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | terminal matcher =>
      simp only [items, enumerateRecognizedItems]
      cases terminalMatch? profile input matcher start with
      | none => rfl
      | some result => cases result; simp only [ih]
    | nonterminal sort => simp only [items, enumerateRecognizedItems, lookup_build, ih]

def structuralFamilies (forest : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat) : List Family :=
  let index := build (recognizedKeys forest) input.length
  (List.finRange plan.structural.length).flatMap fun position =>
    let production := plan.structural.get position
    (List.range (input.length + 1)).flatMap fun start =>
      (items index profile input production.items start).map fun body =>
        ⟨⟨production.resultSort, start, body.stop⟩, .structural position.val, body.children⟩

theorem structuralFamilies_exact (forest : Forest) (profile : ParserProfileLayer)
    (plan : CompiledParserPackPlan) (input : List Nat) :
    structuralFamilies forest profile plan input = expectedStructuralFamilies forest profile plan input := by
  simp only [structuralFamilies, expectedStructuralFamilies, recognizedKeys_exact, items_exact]

end Mettapedia.GSLT.Parsing.ClassAwareChartIndex
