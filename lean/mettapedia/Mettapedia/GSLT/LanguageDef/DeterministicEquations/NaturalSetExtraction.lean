import Mettapedia.GSLT.LanguageDef.DeterministicEquations.EliminationExtraction
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalSetLibrary
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalMembershipProgram

/-! # Checked finite-set library programs

Canonical union is extracted from shared sorted insertion. Membership reuses
the existing natural-list program through the exact sorted-set codec. The
bridges are standard-library lowering laws, not guest checker callbacks.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Library

open Mettapedia.Languages.MM0.Presentation.ComputationalContext

extract_candidate insertProgram from insertNatural
prepare_extraction insertProgram
certify_extraction insertProgram from insertNatural as insert_computes

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``insertNatural
    programName := ``insertProgram
    certificateName := ``insert_computes }

extract_candidate unionProgram from unionNaturals
prepare_extraction unionProgram
certify_extraction unionProgram from unionNaturals as union_computes

theorem set_union_computes (left right : Finset Nat) :
    Applies unionProgram productDivisionHost
      "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Library.unionProgram"
      [encodeDependencies left, encodeDependencies right]
      (encodeDependencies (natSetUnion left right)) := by
  simpa only [encodeDependencies, encodeNaturals, encodeList, natSetUnion,
    unionNaturals_canonical] using
    union_computes (left.sort (· ≤ ·)) (right.sort (· ≤ ·))

def memberHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Library.memberProgram"

def memberProgram : Program :=
  [⟨"set-member", memberHead, [.var "index", .var "values"],
    named "nik:nat-member" [.var "index", .var "values"]⟩] ++ naturalMembershipProgram

private theorem membership_hosts :
    computationalHost.AgreesOn productDivisionHost naturalMembershipProgram.calledHeads := by
  apply productDivisionHost_agrees
  intro head member
  have allChecked : naturalMembershipProgram.calledHeads.all
      (fun name => (naturalProduct? name).isNone) = true := by decide
  have checked := List.all_eq_true.mp allChecked head member
  cases selected : naturalProduct? head with
  | none => rfl
  | some operation => simp [selected] at checked

theorem set_member_computes (index : Nat) (values : Finset Nat) :
    Applies memberProgram productDivisionHost memberHead
      [natural index, encodeDependencies values] (boolean (natSetMember index values)) := by
  have memberRun := (Applies.host_iff naturalMembershipProgram membership_hosts
    "nik:nat-member" (by decide) _ _).mp
      (natural_membership_computes index (values.sort (· ≤ ·)))
  have retained : Applies memberProgram productDivisionHost "nik:nat-member"
      [natural index, encodeDependencies values] (boolean (natSetMember index values)) := by
    have framed := linked_computes naturalMembershipProgram
      [⟨"set-member", memberHead, [.var "index", .var "values"],
        named "nik:nat-member" [.var "index", .var "values"]⟩] [] productDivisionHost
      (by decide) (by decide) "nik:nat-member" (by decide) _ _ memberRun
    simpa only [memberProgram, List.append_nil, encodeDependencies, encodeNaturals,
      natSetMember_sorted] using framed
  refine Applies.equation (equation := memberProgram[0])
    (environment := [("index", natural index), ("values", encodeDependencies values)])
    (by rfl) (by rfl) ?_
  exact evaluate_call (by decide) (by decide)
    (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) retained

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``natSetUnion
    programName := ``unionProgram
    certificateName := ``set_union_computes }
  registerDependency {
    sourceName := ``natSetMember
    programName := ``memberProgram
    certificateName := ``set_member_computes }

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Library
