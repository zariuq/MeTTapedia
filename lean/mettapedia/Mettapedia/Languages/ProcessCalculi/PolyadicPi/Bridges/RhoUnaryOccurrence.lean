import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryPairInversion

/-!
# Original occurrence indices for concrete unary compiler phases

The actual matcher removes an input occurrence and an output occurrence
from the remaining list. The same indices select source activities. Their
residual list is unchanged, including equal duplicate activities, and its
rendering is the matcher residue. Source parallel permutation gives the
corresponding exact exposed source redex.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryOccurrence

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryRoles RhoUnaryPairInversion
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

def input {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) : Activity Γ :=
  activities[selected.inputIndex]'(by simpa [headers] using selected.inputBound)

def output {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) : Activity Γ :=
  (activities.eraseIdx selected.inputIndex)[selected.outputIndex]'
    (by simpa [headers, List.eraseIdx_map] using selected.outputBound)

def residue {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) : List (Activity Γ) :=
  (activities.eraseIdx selected.inputIndex).eraseIdx selected.outputIndex

theorem input_header {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) :
    (input selected).header world = .input selected.inputChannel selected.body := by
  simpa [input, headers] using selected.inputEq

theorem output_header {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) :
    (output selected).header world = .output selected.outputChannel selected.payload := by
  simpa [output, headers, List.eraseIdx_map] using selected.outputEq

theorem residue_headers {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) :
    selected.residue = headers world (residue selected) := by
  simp only [Selection.residue, residue, headers, List.eraseIdx_map]

theorem permutation {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) :
    activities.Perm (input selected :: output selected :: residue selected) := by
  have inputBound : selected.inputIndex < activities.length := by
    simpa [headers] using selected.inputBound
  have outputBound : selected.outputIndex < (activities.eraseIdx selected.inputIndex).length := by
    simpa [headers, List.eraseIdx_map] using selected.outputBound
  exact ((List.Perm.cons (input selected) (List.getElem_cons_eraseIdx_perm outputBound)).trans
    (List.getElem_cons_eraseIdx_perm inputBound)).symm

theorem source_permutation {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) :
    StructuralEq (source activities) (source (input selected :: output selected :: residue selected)) := by
  exact ScopedActiveFrontier.parallel_perm ((permutation selected).map Activity.source)

theorem residue_member {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) {activity : Activity Γ}
    (member : activity ∈ residue selected) : activity ∈ activities :=
  List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx member)

theorem contractum_eq {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) :
    selected.contractum = Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.parallel
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.semanticCommSubst selected.body selected.payload ::
        (headers world (residue selected)).map Header.pattern) := by
  rw [Selection.contractum, residue_headers]

def _root_.Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion.Header.content : Header → Pattern
  | .input _ body | .output _ body => body

/-- Original activities retain the exact suspended body and emitted payload
selected by the actual matcher. -/
theorem contractum_content {Γ : Ctx sig} {world : World Γ 0} {activities : List (Activity Γ)}
    (selected : Selection (headers world activities)) :
    selected.contractum = Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoScopedServers.parallel
      (Mettapedia.Languages.ProcessCalculi.RhoCalculus.semanticCommSubst
        ((input selected).header world).content ((output selected).header world).content ::
        (headers world (residue selected)).map Header.pattern) := by
  rw [input_header, output_header, contractum_eq]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryOccurrence
