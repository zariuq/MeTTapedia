import Mettapedia.GSLT.Parsing.ClassAwareCatalogueValidation

/-! Complete catalogues retain alternatives and repeated child choices.
Missing results, substituted duplicates, and unfinished cyclic extraction
remain distinguishable outcomes. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Parsing.ClassAwareCatalogueValidation.Controls

open ClassAwarePackedForest ClassAwareParserPackCertificate

def root : NodeKey := ⟨"Root", 0, 1⟩
def leaf (position : Nat) : Family := ⟨root, .lexical position, [.terminal (.char 97) 0 1]⟩
def forest : Forest := ⟨[root], [leaf 0, leaf 1]⟩
def proof (position : Nat) : Certificate := .lexical position (.char 97) 0 1

theorem both_alternatives : validate? forest (fun _ => true) root 3 [proof 0, proof 1] = some true := by decide_cbv
theorem reversed_order : validate? forest (fun _ => true) root 3 [proof 1, proof 0] = some true := by decide_cbv
theorem missing_alternative : validate? forest (fun _ => true) root 3 [proof 0] = some false := by decide_cbv
theorem duplicate_cannot_replace_alternative :
    validate? forest (fun _ => true) root 3 [proof 0, proof 0] = some false := by decide_cbv
theorem extra_duplicate_refused :
    validate? forest (fun _ => true) root 3 [proof 0, proof 1, proof 1] = some false := by decide_cbv
theorem selected_alternative :
    validate? forest (fun family => family.production == .lexical 1) root 3 [proof 1] = some true := by decide_cbv
theorem no_rounds_pending : validate? forest (fun _ => true) root 0 [] = none := rfl

def cycle : Family := ⟨root, .structural 2, [.node root]⟩
def cyclic : Forest := ⟨[root], [leaf 0, cycle]⟩

theorem growing_cycle_pending : validate? cyclic (fun _ => true) root 5 [proof 0] = none := by decide_cbv
theorem rejected_cycle_finite :
    validate? cyclic (fun family => family.production != .structural 2) root 3 [proof 0] = some true := by decide_cbv
theorem unproductive_cycle_complete :
    validate? ⟨[root], [cycle]⟩ (fun _ => true) root 3 [] = some true := by decide_cbv

end Mettapedia.GSLT.Parsing.ClassAwareCatalogueValidation.Controls
