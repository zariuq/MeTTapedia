import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction

/-!
# Complete occurrence-sensitive COMM firings

A firing selects an input position and an output position after removing
that input. Equal messages at different positions retain different firing
addresses. The whole residue and semantic substitution result are retained,
and every public closed step has such a firing. The address space is finite
for each supplied source bag, even though the complete reaction family is
not a singleton or a finite list of ground rules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction

/-- Exact source occurrences, the complete ground rule and both matches. -/
structure Firing (source : Bag) where
  inputIndex : Fin (ordered source.1).length
  outputIndex : Fin ((ordered source.1).eraseIdx inputIndex.val).length
  rule : GroundComm
  inputAt : (ordered source.1)[inputIndex.val] = input rule.inputChannel rule.body
  outputAt : ((ordered source.1).eraseIdx inputIndex.val)[outputIndex.val] =
    output rule.outputChannel rule.payload

namespace Firing

variable {source : Bag}

def tail (firing : Firing source) : List Pattern :=
  ((ordered source.1).eraseIdx firing.inputIndex.val).eraseIdx firing.outputIndex.val

theorem tail_primes (firing : Firing source) :
    ∀ pattern ∈ firing.tail, IsPrime pattern := by
  intro pattern membership
  exact ordered_prime source (mem_of_mem_eraseIdx_eraseIdx membership)

def residue (firing : Firing source) : Bag :=
  ⟨(firing.tail : Multiset Pattern), fun _ membership =>
    firing.tail_primes _ (by simpa using membership)⟩

def target (firing : Firing source) : Bag := append firing.rule.reactum firing.residue

theorem source_readout (firing : Firing source) :
    source = append firing.rule.redex firing.residue := by
  apply Subtype.ext
  have permutation : List.Perm (ordered source.1)
      (input firing.rule.inputChannel firing.rule.body ::
        output firing.rule.outputChannel firing.rule.payload :: firing.tail) := by
    have perm : List.Perm (ordered source.1)
        ((ordered source.1)[firing.inputIndex.val] ::
          ((ordered source.1).eraseIdx firing.inputIndex.val)[firing.outputIndex.val] ::
            firing.tail) :=
      ((List.getElem_cons_eraseIdx_perm firing.outputIndex.isLt).cons _ |>.trans
        (List.getElem_cons_eraseIdx_perm firing.inputIndex.isLt)).symm
    rwa [firing.inputAt, firing.outputAt] at perm
  rw [← ordered_multiset source.1]
  change (ordered source.1 : Multiset Pattern) =
    ([input firing.rule.inputChannel firing.rule.body,
      output firing.rule.outputChannel firing.rule.payload] : List Pattern) +
      (firing.tail : Multiset Pattern)
  rw [Multiset.coe_add]
  exact Multiset.coe_eq_coe.mpr permutation

theorem reaction (firing : Firing source) : Reaction source firing.target :=
  ⟨firing.rule, firing.residue, firing.source_readout, rfl⟩

theorem public_step (firing : Firing source) :
    rhoLanguageDefGSLT.Step (toProcess source) (toProcess firing.target) :=
  reaction_public firing.reaction

/-- The unnormalized endpoint retains the exact ordered unmatched occurrences. -/
def presentation (firing : Firing source) : RhoProcess :=
  ofList (firing.rule.result.1 :: firing.tail) (fun pattern membership => by
    rcases List.mem_cons.mp membership with rfl | membership
    · exact firing.rule.result.2
    · exact (firing.tail_primes pattern membership).1)

theorem presentation_inventory (firing : Firing source) :
    fromProcess firing.presentation = firing.target := by
  apply Subtype.ext
  unfold presentation
  rw [fromProcess_cons_primes firing.rule.result _ _ firing.tail_primes]
  rfl

theorem whole_target_readout (firing : Firing source) :
    toProcess firing.target = firing.presentation.canonicalize := by
  rw [← firing.presentation_inventory, toProcess_fromProcess]

theorem source_length (firing : Firing source) : 2 ≤ (ordered source.1).length := by
  have remaining := firing.outputIndex.isLt
  have removed := List.length_eraseIdx_add_one firing.inputIndex.isLt
  omega

/-- The compiled primitive step agrees at these exact occurrence positions. -/
theorem selected_step (firing : Firing source) :
    RhoStepAt 1 (toProcess source).1 firing.presentation.1 := by
  rw [toProcess_pattern, collapseBag_eq_bag_of_length_ge_two firing.source_length]
  have step := rhoStepAt_one_comm firing.inputIndex.isLt firing.outputIndex.isLt
    firing.inputAt firing.outputAt
    ((rhoCanonicalEquivalent_iff _ _).mpr firing.rule.channels)
  rw [apply_commBindingsAt firing.rule.body_typed firing.rule.payload_typed] at step
  exact step

def address (firing : Firing source) :
    Σ position : Fin (ordered source.1).length,
      Fin ((ordered source.1).eraseIdx position.val).length :=
  ⟨firing.inputIndex, firing.outputIndex⟩

end Firing

theorem groundComm_ext {first second : GroundComm}
    (inputEqual : input first.inputChannel first.body = input second.inputChannel second.body)
    (outputEqual : output first.outputChannel first.payload =
      output second.outputChannel second.payload) : first = second := by
  have inputFields : first.inputChannel = second.inputChannel ∧ first.body = second.body := by
    simpa [input] using inputEqual
  have outputFields : first.outputChannel = second.outputChannel ∧ first.payload = second.payload := by
    simpa [output] using outputEqual
  cases first
  cases second
  rcases inputFields with ⟨rfl, rfl⟩
  rcases outputFields with ⟨rfl, rfl⟩
  rfl

theorem Firing.address_injective (source : Bag) :
    Function.Injective (Firing.address (source := source)) := by
  intro first second equal
  cases first with
  | mk i j rule inputAt outputAt =>
    cases second with
    | mk i' j' rule' inputAt' outputAt' =>
      have indices : i = i' := congrArg Sigma.fst equal
      subst i'
      have outputs : j = j' := eq_of_heq (Sigma.mk.inj_iff.mp equal).2
      subst j'
      have rules : rule = rule' := groundComm_ext
        (inputAt.symm.trans inputAt') (outputAt.symm.trans outputAt')
      subst rule'
      rfl

instance (source : Bag) : Finite (Firing source) :=
  Finite.of_injective _ (Firing.address_injective source)

/-- Every independently authored reaction has actual selected occurrences. -/
theorem reaction_has_firing {source target : Bag} (reaction : Reaction source target) :
    ∃ firing : Firing source, firing.target = target := by
  obtain ⟨rule, residue, sourceEquation, targetEquation⟩ := reaction
  have permutation : List.Perm (ordered source.1)
      (input rule.inputChannel rule.body ::
        output rule.outputChannel rule.payload :: ordered residue.1) := by
    apply Multiset.coe_eq_coe.mp
    rw [ordered_multiset]
    change source.1 = ([input rule.inputChannel rule.body,
      output rule.outputChannel rule.payload] ++ ordered residue.1 : List Pattern)
    rw [← Multiset.coe_add, ordered_multiset]
    exact congrArg Subtype.val sourceEquation
  obtain ⟨i, iBound, j, jBound, inputAt, outputAt, tailPermutation⟩ := locate_pair permutation
  let firing : Firing source := ⟨⟨i, iBound⟩, ⟨j, jBound⟩, rule, inputAt, outputAt⟩
  have sameResidue : firing.residue = residue := by
    apply Subtype.ext
    change (((ordered source.1).eraseIdx i).eraseIdx j : Multiset Pattern) = residue.1
    rw [← ordered_multiset residue.1]
    exact Multiset.coe_eq_coe.mpr tailPermutation
  exact ⟨firing, by
    change append rule.reactum firing.residue = target
    rw [sameResidue, ← targetEquation]⟩

theorem reaction_iff_firing (source target : Bag) :
    Reaction source target ↔ ∃ firing : Firing source, firing.target = target := by
  constructor
  · exact reaction_has_firing
  · rintro ⟨firing, rfl⟩
    exact firing.reaction

/-- A fixed canonical source has finitely many complete result bags. This
does not identify firings that select different duplicate occurrences. -/
theorem reaction_targets_finite (source : Bag) :
    Set.Finite {target : Bag | Reaction source target} := by
  have targets : {target : Bag | Reaction source target} =
      Set.range (Firing.target (source := source)) := by
    ext target
    exact reaction_iff_firing source target
  rw [targets]
  exact Set.finite_range _

/-- Every public saturated closed step, with its precise endpoint, has an
occurrence-sensitive firing; conversely every supplied firing really executes. -/
theorem publicStep_iff_firing (source target : RhoProcess) :
    rhoLanguageDefGSLT.Step source target ↔
      ∃ firing : Firing (fromProcess source), firing.target = fromProcess target := by
  rw [publicStep_iff, reaction_iff_firing]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionOccurrences
