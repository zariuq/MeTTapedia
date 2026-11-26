import Mettapedia.Machines.TIsa.Derivation.SymbolicIndex
import Mettapedia.Machines.TIsa.Derivation.SymbolicSelectionSearch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.OneAfterAnother

/-!
# Enumerating symbolic ports from postings

The take and read ports use the candidate list of their own opened
patterns. Indexed enumeration leaves the unifier and all-solutions
test unchanged. In particular, its filtering does not treat the
current knowledge as the only possible source of bindings.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicIndexedPorts

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.OneFrame (ext Terms)
open SymbolicFiring (World act PreparedOpening)
open FirstOrderTerms (Head)
open SymbolicIndex (compatible)

variable {σ : LPSignature} {K : Type*} [BEq K] [Hashable K]

private def snapshot (label : ℕ → Term σ) (available : List ℕ) : List (ℕ × Term σ) :=
  available.map fun i => (i, label i)

private def hits (encode : Head σ → K) (width : ℕ) (index : SymbolicIndex.Index σ K)
    (p : Term σ) : List ℕ := (SymbolicIndex.lookup p encode width index).map Prod.fst

def ports (encode : Head σ → K) (width : ℕ) (label : ℕ → Term σ) (available : List ℕ)
    (takes reads : List (Term σ)) : List (List ℕ × List ℕ) :=
  let index := SymbolicIndex.build encode width (snapshot label available)
  let candidate := hits encode width index
  ((AnswerTable.choices candidate takes).filter fun taken => decide taken.Nodup).flatMap fun taken =>
    (AnswerTable.choices (fun p => (candidate p).filter fun i => !(taken.contains i)) reads).map
      fun read => (taken, read)

variable [LawfulBEq K]

private theorem mem_hits (encode : Head σ → K) (width : ℕ) (label : ℕ → Term σ) (available : List ℕ)
    (pattern : Term σ) (i : ℕ) :
    i ∈ hits encode width (SymbolicIndex.build encode width (snapshot label available)) pattern ↔
      i ∈ available ∧ compatible encode width pattern (label i) = true := by
  unfold hits
  rw [((SymbolicIndex.lookup_perm_filter pattern encode width (snapshot label available)).map Prod.fst).mem_iff]
  constructor
  · intro found
    obtain ⟨_, hit, same⟩ := List.mem_map.mp found
    obtain ⟨inSnapshot, key⟩ := List.mem_filter.mp hit
    obtain ⟨j, listed, rfl⟩ := List.mem_map.mp inSnapshot
    exact ⟨same ▸ listed, same ▸ key⟩
  · rintro ⟨listed, key⟩
    exact List.mem_map.mpr ⟨(i, label i), List.mem_filter.mpr
      ⟨List.mem_map.mpr ⟨i, listed, rfl⟩, key⟩, rfl⟩

private theorem paired_with_eligibility {P I : Type*} (localTest : I → Prop) (keyTest : P → I → Prop)
    (patterns : List P) (ids : List I) :
    List.Forall₂ (fun p i => localTest i ∧ keyTest p i) patterns ids ↔
      (∀ i ∈ ids, localTest i) ∧ List.Forall₂ keyTest patterns ids := by
  constructor
  · intro paired
    have flipped := (List.forall₂_and_left (p := localTest) (R := fun i p => keyTest p i) ids patterns).mp paired.flip
    exact ⟨flipped.1, flipped.2.flip⟩
  · rintro ⟨listed, paired⟩
    exact ((List.forall₂_and_left (p := localTest) (R := fun i p => keyTest p i) ids patterns).mpr
      ⟨listed, paired.flip⟩).flip

theorem mem_ports (encode : Head σ → K) (width : ℕ) (label : ℕ → Term σ) (available : List ℕ)
    (takes reads : List (Term σ)) (takeIds readIds : List ℕ) :
    (takeIds, readIds) ∈ ports encode width label available takes reads ↔
      (takeIds, readIds) ∈ SymbolicFiring.portChoices available takes.length reads.length ∧
      List.Forall₂ (fun p i => compatible encode width p (label i) = true) takes takeIds ∧
      List.Forall₂ (fun p i => compatible encode width p (label i) = true) reads readIds := by
  let candidate := hits encode width (SymbolicIndex.build encode width (snapshot label available))
  let keyTest := fun p i => compatible encode width p (label i) = true
  have takeKey (ids : List ℕ) : ids ∈ AnswerTable.choices candidate takes ↔
      (∀ i ∈ ids, i ∈ available) ∧ List.Forall₂ keyTest takes ids := by
    rw [AnswerTable.mem_choices, ← paired_with_eligibility]
    exact ⟨fun pair => pair.imp (fun p i h => (mem_hits encode width label available p i).mp h),
      fun pair => pair.imp (fun p i h => (mem_hits encode width label available p i).mpr h)⟩
  have readKey (taken ids : List ℕ) :
      ids ∈ AnswerTable.choices (fun p => (candidate p).filter fun i => !taken.contains i) reads ↔
      (∀ i ∈ ids, i ∈ available ∧ i ∉ taken) ∧ List.Forall₂ keyTest reads ids := by
    have one (p : Term σ) (i : ℕ) : i ∈ (candidate p).filter (fun i => !taken.contains i) ↔
        (i ∈ available ∧ i ∉ taken) ∧ keyTest p i := by
      rw [List.mem_filter, mem_hits]
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, keyTest]
      tauto
    rw [AnswerTable.mem_choices, ← paired_with_eligibility]
    exact ⟨fun pair => pair.imp (fun p i h => (one p i).mp h),
      fun pair => pair.imp (fun p i h => (one p i).mpr h)⟩
  constructor
  · intro published
    change (takeIds, readIds) ∈ ((AnswerTable.choices candidate takes).filter fun t => decide t.Nodup).flatMap
      (fun t => (AnswerTable.choices (fun p => (candidate p).filter fun i => !t.contains i) reads).map
        (fun r => (t, r))) at published
    obtain ⟨chosen, takes, inside⟩ := List.mem_flatMap.mp published
    obtain ⟨observed, reads, same⟩ := List.mem_map.mp inside
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    obtain ⟨taken, distinct⟩ := List.mem_filter.mp takes
    obtain ⟨takeFrom, takePaired⟩ := (takeKey _).mp taken
    obtain ⟨readFrom, readPaired⟩ := (readKey _ _).mp reads
    exact ⟨(SymbolicFiring.portChoices_iff _ _ _ _ _).mpr
      ⟨takePaired.length_eq.symm, readPaired.length_eq.symm, of_decide_eq_true distinct, takeFrom, readFrom⟩,
      takePaired, readPaired⟩
  · rintro ⟨geometry, takePaired, readPaired⟩
    obtain ⟨_, _, distinct, takeFrom, readFrom⟩ := (SymbolicFiring.portChoices_iff _ _ _ _ _).mp geometry
    change (takeIds, readIds) ∈ ((AnswerTable.choices candidate takes).filter fun t => decide t.Nodup).flatMap
      (fun t => (AnswerTable.choices (fun p => (candidate p).filter fun i => !t.contains i) reads).map
        (fun r => (t, r)))
    exact List.mem_flatMap.mpr ⟨takeIds,
      List.mem_filter.mpr ⟨(takeKey _).mpr ⟨takeFrom, takePaired⟩, decide_eq_true distinct⟩,
      List.mem_map.mpr ⟨readIds, (readKey _ _).mpr ⟨readFrom, readPaired⟩, rfl⟩⟩

omit [Hashable K] [LawfulBEq K] in
private theorem portPairs (encode : Head σ → K) (width : ℕ) (label : ℕ → Term σ)
    (patterns : List (Term σ)) (ids : List ℕ) (arity : patterns.length = ids.length)
    (safe : ∀ e ∈ patterns.zipWith (fun p i => (p, label i)) ids, compatible encode width e.1 e.2 = true) :
    List.Forall₂ (fun p i => compatible encode width p (label i) = true) patterns ids := by
  apply List.forall₂_iff_zip.mpr
  refine ⟨arity, ?_⟩
  intro p i present
  have attached : (p, label i) ∈ patterns.zipWith (fun p i => (p, label i)) ids := by
    change (p, label i) ∈ patterns.zipWith (Function.curry (fun e => (e.1, label e.2))) ids
    rw [← List.map_zip_eq_zipWith]
    exact List.mem_map.mpr ⟨(p, i), present, rfl⟩
  exact safe _ attached

variable {program : RuleSyntax.Program (Terms (Term σ))} {before : World σ ℕ}

/-- Every firing of the selected opening is still proposed. Membership
starts with physical identities; it does not deduplicate equal atoms. -/
theorem admitted_ports_found (encode : Head σ → K) (width : ℕ) (opened : PreparedOpening (program := program) before)
    (available : List ℕ) (visible : available.toFinset = before.present) (taken reads : List ℕ)
    (seen : List (Finset ℕ))
    (admitted : ({opened.withPorts taken reads with seen := seen}).Admits (act σ) before) :
    (taken, reads) ∈ ports encode width before.label available
      (opened.template.opened (act σ)).take (opened.template.opened (act σ)).read := by
  let f := {opened.withPorts taken reads with seen := seen}
  have body : f.opened (act σ) = opened.template.opened (act σ) := rfl
  have takeIds : f.selection.taken = taken := rfl
  have readIds : f.selection.read = reads := rfl
  have row : f.row (act σ) before = before.label :=
    funext (RuleSyntax.JointFirings.row_one (FirstOrder.action σ) before f)
  have takeWidth : (f.opened (act σ)).take.length = taken.length := by
    change (f.rule.body.take.map f.opening.applyTerm).length = _
    rw [List.length_map]
    exact admitted.1.2.2.2.1
  have readWidth : (f.opened (act σ)).read.length = reads.length := by
    change (f.rule.body.read.map f.opening.applyTerm).length = _
    rw [List.length_map]
    exact admitted.1.2.2.2.2.1
  apply (mem_ports _ _ _ _ _ _ _ _).mpr
  refine ⟨?_, portPairs encode width _ _ _ takeWidth (fun e h => ?_),
    portPairs encode width _ _ _ readWidth (fun e h => ?_)⟩
  · have listed := opened.admitted_ports_listed available visible taken reads seen admitted
    simpa only [RuleSyntax.Firing.opened, RuleInstance.map, List.length_map] using listed
  · apply SymbolicIndex.matching_compatible encode width f admitted
    apply List.mem_append_left
    simpa only [RuleSyntax.Firing.matching, row, body, takeIds] using h
  · apply SymbolicIndex.matching_compatible encode width f admitted
    apply List.mem_append_right
    simpa only [RuleSyntax.Firing.matching, row, body, readIds] using h

namespace Examples

private abbrev atoms : LPSignature where
  constants := ℕ
  vars := ℕ
  relationSymbols := Empty
  relationArity := fun _ => 0
  functionSymbols := Empty
  functionArity := nofun

private def key : Head atoms → ℕ
  | .inl c => c
  | .inr f => nomatch f

private def labels : ℕ → Term atoms
  | 1 => .const 7
  | 2 => .var 4
  | _ => .const 8

private def seven : Term atoms := .const 7

theorem an_unknown_is_available_to_both_read_ports :
    (([1], [2, 2]) : List ℕ × List ℕ) ∈ ports key 0 labels [1, 2, 3] [seven] [seven, seven] := by
  apply (mem_ports _ _ _ _ _ _ _ _).mpr
  refine ⟨(SymbolicFiring.portChoices_iff _ _ _ _ _).mpr ?_, .cons rfl .nil, .cons rfl (.cons rfl .nil)⟩
  simp

theorem a_conflicting_constant_is_not_a_candidate :
    (([3], []) : List ℕ × List ℕ) ∉ ports key 0 labels [1, 2, 3] [seven] [] := by
  intro found
  have matching := ((mem_ports _ _ _ _ _ _ _ _).mp found).2.1
  cases matching with
  | cons contradicted _ =>
    have wrong : compatible key 0 seven (labels 3) = false := rfl
    exact Bool.noConfusion (wrong.symm.trans contradicted)

end Examples

end Mettapedia.Machines.TIsa.Derivation.SymbolicIndexedPorts
