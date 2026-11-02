import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxPacketInverse
import Mettapedia.GSLT.Parsing.ClassAwarePackedForest

/-! Declared source policies are checked independently on every family of
the replayed certificate. Selection does not alter the retained forest or
identify distinct derivations with equal output. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection

open Mettapedia.GSLT.Parsing
open ClassAwarePackedForest ClassAwareParserPackCertificate
open ScalarSyntaxCore SourceSyntax

def allows (filters : List FamilyFilter) (input : List Nat) (family : Family) : Bool :=
  filters.all (FamilyFilter.allows family.parent.resultSort
    ((input.drop family.parent.start).take (family.parent.stop - family.parent.start))
    (input.drop family.parent.stop))

mutual
  def selected (allow : Family → Bool) (sort : String) : Certificate → Bool
    | certificate@(.lexical _ _ _ _) => allow (certificateFamily sort certificate)
    | certificate@(.structural _ _ _ body) =>
        allow (certificateFamily sort certificate) && selectedItems allow body

  def selectedItems (allow : Family → Bool) : ItemsCertificate → Bool
    | .nil _ => true
    | .terminal _ _ _ rest => selectedItems allow rest
    | .nonterminal sort _ _ head rest => selected allow sort head && selectedItems allow rest
end

mutual
  theorem selected_exact (allow : Family → Bool) (sort : String) (certificate : Certificate) :
      selected allow sort certificate = (certificateFamilies sort certificate).all allow := by
    cases certificate with
    | lexical => simp only [selected, certificateFamilies, List.all_cons, List.all_nil, Bool.and_true]
    | structural _ _ _ body => simp only [selected, certificateFamilies, List.all_cons, selectedItems_exact allow body]

  theorem selectedItems_exact (allow : Family → Bool) (certificate : ItemsCertificate) :
      selectedItems allow certificate = (itemsFamilies certificate).all allow := by
    cases certificate with
    | nil => rfl
    | terminal _ _ _ rest => exact selectedItems_exact allow rest
    | nonterminal sort _ _ head rest =>
      simp only [selectedItems, itemsFamilies, List.all_append, selected_exact allow sort head, selectedItems_exact allow rest]
end

theorem selected_iff (allow : Family → Bool) (sort : String) (certificate : Certificate) :
    selected allow sort certificate = true ↔
      ∀ family ∈ certificateFamilies sort certificate, allow family = true := by
  rw [selected_exact, List.all_eq_true]

theorem selected_append (first second : List FamilyFilter) (input : List Nat) (sort : String)
    (certificate : Certificate) :
    selected (allows (first ++ second) input) sort certificate =
      (selected (allows first input) sort certificate && selected (allows second input) sort certificate) := by
  apply Bool.eq_iff_iff.mpr
  simp only [selected_iff, allows, List.all_append, Bool.and_eq_true, forall_and]

theorem selected_commute (first second : List FamilyFilter) (input : List Nat) (sort : String)
    (certificate : Certificate) :
    selected (allows (first ++ second) input) sort certificate =
      selected (allows (second ++ first) input) sort certificate := by
  rw [selected_append, selected_append, Bool.and_comm]

def read? (description : Description) (parser : Parser description) (shape : Shape description)
    (filters : List FamilyFilter) (input : List Nat) (sort : String) (packet : SourcePacket.Packet) :
    Option (Reading description parser shape input sort 0 input.length) := do
  let reading ← SourcePacketCertificate.readPacket? description parser shape input sort packet
  if selected (allows filters input) sort reading.certificate then some reading else none

@[simp] theorem read?_nil (description : Description) (parser : Parser description) (shape : Shape description)
    (input : List Nat) (sort : String) (packet : SourcePacket.Packet) :
    read? description parser shape [] input sort packet =
      SourcePacketCertificate.readPacket? description parser shape input sort packet := by
  simp [read?, selected_exact, allows]

theorem read?_isSome (description : Description) (parser : Parser description) (shape : Shape description)
    (filters : List FamilyFilter) (input : List Nat) (sort : String) (packet : SourcePacket.Packet) :
    (read? description parser shape filters input sort packet).isSome =
      match SourcePacketCertificate.propose? parser.plan input sort packet with
      | none => false
      | some certificate =>
          (readCertificate? description parser shape input sort 0 input.length certificate).isSome &&
            selected (allows filters input) sort certificate := by
  unfold read? SourcePacketCertificate.readPacket?
  cases proposed : SourcePacketCertificate.propose? parser.plan input sort packet with
  | none => rfl
  | some certificate =>
    dsimp only [Bind.bind, Option.bind]
    cases read : readCertificate? description parser shape input sort 0 input.length certificate with
    | none => rfl
    | some reading =>
      dsimp only [Option.bind]
      rw [readCertificate?_certificate read]
      cases selected (allows filters input) sort certificate <;> rfl

theorem read?_selected {description : Description} {parser : Parser description} {shape : Shape description}
    {filters : List FamilyFilter} {input : List Nat} {sort : String} {packet : SourcePacket.Packet}
    {reading : Reading description parser shape input sort 0 input.length}
    (accepted : read? description parser shape filters input sort packet = some reading) :
    SourcePacketCertificate.readPacket? description parser shape input sort packet = some reading ∧
      ∀ family ∈ certificateFamilies sort reading.certificate, allows filters input family = true := by
  obtain ⟨actual, replayed, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i selected
    cases Option.some.inj accepted
    exact ⟨replayed, (selected_iff _ _ _).mp selected⟩
  · cases accepted

theorem read?_complete {description : Description} {parser : Parser description} {shape : Shape description}
    {filters : List FamilyFilter} {input : List Nat} {sort : String} {packet : SourcePacket.Packet}
    {reading : Reading description parser shape input sort 0 input.length}
    (replayed : SourcePacketCertificate.readPacket? description parser shape input sort packet = some reading)
    (policy : ∀ family ∈ certificateFamilies sort reading.certificate, allows filters input family = true) :
    read? description parser shape filters input sort packet = some reading := by
  simp [read?, replayed, (selected_iff _ _ _).mpr policy]

#print axioms selected_exact
#print axioms selected_append
#print axioms selected_commute
#print axioms read?_selected
#print axioms read?_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection
