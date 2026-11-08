import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationModuloFirings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObservationCoherence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsQuantumAggregation

/-!
# Interference read modulo the knowledge

The end of a history, read by a client whose escaped identities are `E`, is its configuration class
up to equivalence modulo the knowledge (`moduloEnd`). The **modulo readout** of a region
(`moduloReadout`) adds amplitudes over the causal histories with one such end, over the quantum
layer's own regions, causal classes and amplitudes.

* **Coarser than the nominal end** (`moduloEnd_empty_of_nominalEnd`): for a client that has seen
  nothing, two classes with one nominal end (the same solutions and the same bag of syntactic
  labels) have one end modulo the knowledge. The converse fails (`ModuloInterference.labelled_rows`).
* **A firing and its alternative under a fresh name** (`fresh_alternative_moduloEquivalent_iff`):
  their results are equivalent modulo the knowledge exactly when neither name has escaped. A fresh
  alternative keeps the made row's label syntactically, so on such pairs rows modulo the knowledge
  and private equivalence agree.

## The superposed pair of R27 and R33 (`ModuloInterference`)

Over the quantum layer's own `Superpose` alternatives and `shifted` amplitudes:

* **The verdict is unchanged** (`superposed_modulo_iff`): the two histories have one end modulo the
  knowledge exactly when neither row `20` nor `21` has escaped. Their labels are the same constant,
  so comparing rows modulo the knowledge identifies nothing that the syntactic labels kept apart.
* **The readouts** (`superposed_modulo_private`, `superposed_modulo_escaped`): with the amplitudes
  `1` and `-1`, the modulo readout is `0` for a client that has seen neither row, as the nominal
  readout is (`AggregationControls.Superposed.nominal_interferes`), and `2` once the row `20` has
  escaped.

## Where rows modulo the knowledge differ (`labelled_rows`)

Under the knowledge `X = Y`, two histories that take one token and make the row `20 : X` or the
row `21 : Y` end in states that are equivalent modulo the knowledge and not privately equivalent.
With the amplitudes `1` and `-1` they read `0` modulo the knowledge, and `2` with syntactic labels:
the syntactic labels report a record that no permitted probe can read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open AnnotatedRuns.AmplitudeRuns
open GuardFreeProcessOrders (SameUpTo)
open Mettapedia.Algebra.RationalComplexAmplitude (Amplitude born born_formula)

universe uT uS uO

/-! ## Ends modulo the knowledge -/

section Ends

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T) (E : Finset O)

/-- **The end of a configuration class modulo the knowledge**, for a client whose escaped identities
are `E`. -/
def moduloEnd : ConfigurationClass A O → Quotient (moduloSetoid A label E) :=
  Quotient.lift (fun C => Quotient.mk (moduloSetoid A label E) C) fun _ _ same =>
    Quotient.sound (PrivatelyEquivalent.modulo (PrivatelyEquivalent.of_sameUpTo same))

omit [DecidableEq O] in
theorem moduloEnd_mk (C : Configuration T O) :
    moduloEnd A label E (ConfigurationClass.mk A C) = Quotient.mk (moduloSetoid A label E) C := rfl

omit [DecidableEq O] in
theorem moduloEnd_mk_eq_iff (C D : Configuration T O) :
    moduloEnd A label E (ConfigurationClass.mk A C) = moduloEnd A label E (ConfigurationClass.mk A D) ↔
      ModuloEquivalent A label E C D :=
  ⟨fun same => Quotient.exact same, fun h => Quotient.sound h⟩

/-- **Coarser than the nominal end**: for a client that has seen nothing, one nominal end gives one
end modulo the knowledge. -/
theorem moduloEnd_empty_of_nominalEnd (x y : ConfigurationClass A O)
    (same : nominalEnd A label x = nominalEnd A label y) :
    moduloEnd A label ∅ x = moduloEnd A label ∅ y := by
  induction x using Quotient.inductionOn with
  | h C =>
    induction y using Quotient.inductionOn with
    | h D =>
      change nominalEnd A label (ConfigurationClass.mk A C) =
        nominalEnd A label (ConfigurationClass.mk A D) at same
      rw [nominalEnd_mk, nominalEnd_mk, Prod.mk.injEq] at same
      exact (moduloEnd_mk_eq_iff A label ∅ C D).mpr (PrivatelyEquivalent.modulo
        ((privatelyEquivalent_empty_iff A label C D).mpr ⟨Quotient.exact same.1, same.2⟩))

open Classical in
/-- **The modulo readout of a region**: the causal histories that end in `Q`, each with the end of
the class it reaches modulo the knowledge. -/
noncomputable def moduloReadout (amp : Firing T S O → Amplitude) (catalogue : List (Firing T S O))
    (budget : ℕ) (root : Configuration T O) (Q : ConfigurationClass A O → Prop) : ℚ :=
  endReadout (fun trace => moduloEnd A label E (classEnd A label root trace))
    (classAmplitude A label amp root) (regionBranches A label catalogue budget root Q)

end Ends

/-! ## Fresh alternatives -/

section Alternatives

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {label : O → T} {E : Finset O}
  {f : Firing T S O} {C : Configuration T O} {r r' : O}

/-- **A firing and its alternative under a fresh name are equivalent modulo the knowledge exactly
when neither name has escaped.** -/
theorem fresh_alternative_moduloEquivalent_iff (valid : f.Valid A label C)
    (made : r ∈ f.selection.made) (absent : r' ∉ C.present) (same : label r' = label r)
    (new : r' ∉ f.names) :
    ModuloEquivalent A label E (f.result label C) ((f.rename (Equiv.swap r r')).result label C) ↔
      r ∉ E ∧ r' ∉ E := by
  have notMade : r' ∉ f.selection.made := fun inMade => new (by simp [Firing.names, inMade])
  constructor
  · intro h
    refine ⟨fun seen => ?_, fun seen' => ?_⟩
    · have here : r ∈ (f.result label C).present := result_present_iff.mpr (Or.inr made)
      have there := (h.escaped_iff seen).mp here
      rw [fresh_alternative_result valid made absent same] at there
      obtain ⟨a, member, moved⟩ := Finset.mem_map.mp there
      have isR' : a = r' := by
        rw [Equiv.coe_toEmbedding, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at moved
        exact moved
      rw [isR'] at member
      rcases result_present_iff.mp member with ⟨present, -⟩ | inMade
      · exact absent present
      · exact notMade inMade
    · have there : r' ∈ ((f.rename (Equiv.swap r r')).result label C).present := by
        rw [fresh_alternative_result valid made absent same]
        exact Finset.mem_map.mpr ⟨r, result_present_iff.mpr (Or.inr made), by simp⟩
      rcases result_present_iff.mp ((h.escaped_iff seen').mpr there) with ⟨present, -⟩ | inMade
      · exact absent present
      · exact notMade inMade
  · rintro ⟨unseen, unseen'⟩
    exact PrivatelyEquivalent.modulo (fresh_alternative_equivalent valid made absent same unseen unseen')

end Alternatives

/-! ## The superposed pair, and rows that only the knowledge identifies -/

namespace ModuloInterference

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label zeros)
open AnnotatedRunBranchCollection.Controls.Superpose (root first second alternatives first_valid
  branches branches_distinct)
open AmplitudeControls (everything regionBranches_everything)
open AmplitudeControls.Superposed (shifted superposed_cancel)

theorem second_is_alternative : first.rename (Equiv.swap 20 21) = second := by
  simp [first, second, Firing.rename, renameSelection, Equiv.swap_apply_of_ne_of_ne]

theorem classEnd_single (g : Firing (Term signature) (Subst signature) ℕ) :
    classEnd A label root (Quot.mk _ [g]) = ConfigurationClass.mk A (g.result label root) := rfl

/-- **The superposed pair has one end modulo the knowledge exactly when neither row has
escaped**, for every client. -/
theorem superposed_modulo_iff (E : Finset ℕ) :
    moduloEnd A label E (classEnd A label root (Quot.mk _ [first])) =
        moduloEnd A label E (classEnd A label root (Quot.mk _ [second])) ↔ 20 ∉ E ∧ 21 ∉ E := by
  rw [classEnd_single, classEnd_single, moduloEnd_mk_eq_iff, ← second_is_alternative]
  exact fresh_alternative_moduloEquivalent_iff first_valid (by simp [first]) (by decide) rfl
    (by simp [Firing.names, first, sighted])

/-- **The verdict is the private one**: on the superposed pair, ends modulo the knowledge and private
ends agree for every client. -/
theorem superposed_same_verdict (E : Finset ℕ) :
    moduloEnd A label E (classEnd A label root (Quot.mk _ [first])) =
        moduloEnd A label E (classEnd A label root (Quot.mk _ [second])) ↔
      PrivatelyEquivalent A label E (first.result label root) (second.result label root) := by
  rw [superposed_modulo_iff, ← second_is_alternative]
  exact (fresh_alternative_equivalent_iff (r := 20) (r' := 21) first_valid (by simp [first]) (by decide) rfl
    (by simp [Firing.names, first, sighted])).symm

/-- **Private rows interfere modulo the knowledge**: the amplitudes `1` and `-1` read `0`. -/
theorem superposed_modulo_private :
    moduloReadout A label ∅ shifted alternatives 1 root everything = 0 := by
  classical
  have nonempty : (regionBranches A label alternatives 1 root everything).Nonempty := by
    rw [regionBranches_everything, branches]
    exact Finset.insert_nonempty _ _
  have shared : ∀ trace ∈ regionBranches A label alternatives 1 root everything,
      moduloEnd A label ∅ (classEnd A label root trace) =
        moduloEnd A label ∅ (classEnd A label root (Quot.mk _ [first])) := by
    intro trace member
    rw [regionBranches_everything, branches, Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · rfl
    · exact ((superposed_modulo_iff ∅).mpr ⟨Finset.notMem_empty _, Finset.notMem_empty _⟩).symm
  have coherent : moduloReadout A label ∅ shifted alternatives 1 root everything =
      born (regionalAmplitude A label shifted alternatives 1 root everything) := by
    unfold moduloReadout regionalAmplitude
    convert endReadout_of_one_end (classAmplitude A label shifted root) nonempty shared
  rw [coherent, superposed_cancel.2.1]
  exact (Mettapedia.Algebra.RationalComplexAmplitude.born_zero_iff 0).mpr rfl

/-- **An escaped row records the alternative modulo the knowledge**: the amplitudes `1` and `-1`
read `2`. -/
theorem superposed_modulo_escaped :
    moduloReadout A label {20} shifted alternatives 1 root everything = 2 := by
  classical
  have recorded : Set.InjOn (fun trace => moduloEnd A label {20} (classEnd A label root trace))
      (regionBranches A label alternatives 1 root everything) := by
    intro x inX y inY same
    rw [regionBranches_everything, branches, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at inX inY
    have apart := fun ends => (superposed_modulo_iff {20}).mp ends |>.1 (Finset.mem_singleton_self 20)
    rcases inX with rfl | rfl <;> rcases inY with rfl | rfl
    · rfl
    · exact absurd same apart
    · exact absurd same.symm apart
    · rfl
  have classical' : moduloReadout A label {20} shifted alternatives 1 root everything =
      incoherent (branchAmplitudes A label shifted alternatives 1 root everything) := by
    rw [incoherent_branchAmplitudes]
    unfold moduloReadout
    convert endReadout_of_injOn (classAmplitude A label shifted root) recorded
  rw [classical', superposed_cancel.2.2.1]

/-- **The nominal readout and the modulo readout agree on the superposed pair** for a client that
has seen nothing: both read `0`. -/
theorem superposed_nominal_agrees :
    nominalReadout A label shifted alternatives 1 root everything =
      moduloReadout A label ∅ shifted alternatives 1 root everything := by
  rw [AggregationControls.Superposed.nominal_interferes.1, superposed_modulo_private]

/-! ### Rows that only the knowledge identifies -/

open ModuloControls (X Y X_ne_Y knowsXY)

/-- The token `9` under the knowledge `X = Y`. -/
def tokenXY : Configuration (Term signature) ℕ := ⟨knowsXY, {9}⟩

/-- Take the token and make the row `o` with the label `t`. -/
def makeRow (t : Term signature) (o : ℕ) : Firing (Term signature) (Subst signature) ℕ :=
  ⟨⟨[.const 2], [], [], [], [t]⟩, [], ⟨[9], [], [o]⟩⟩

theorem makeRow_valid {t : Term signature} {o : ℕ} (labelled : ModuloControls.label o = t)
    (fresh : o ≠ 9) : (makeRow t o).Valid A ModuloControls.label tokenXY := by
  refine ⟨⟨by simp [makeRow], by simp [makeRow], rfl, rfl, by simp [makeRow, labelled], ?_, ⟨zeros, ?_⟩,
    by simp [makeRow]⟩, by simp [makeRow]⟩
  · refine ⟨by simp [Selection.commit, makeRow, tokenXY], by simp [Selection.commit, makeRow],
      by simp [Selection.commit, makeRow], ?_, by simp [Selection.commit]⟩
    simp [Selection.commit, makeRow, tokenXY, fresh]
  · intro e member
    simp only [Selection.problem, Selection.equations, makeRow, tokenXY, knowsXY,
      List.zipWith_cons_cons, List.zipWith_nil_left, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl

/-- The end of each history, after the row `20 : X` or the row `21 : Y`. -/
def rowEnd : Bool → Configuration (Term signature) ℕ
  | false => (makeRow X 20).result ModuloControls.label tokenXY
  | true => (makeRow Y 21).result ModuloControls.label tokenXY

theorem rowEnd_equations (b : Bool) :
    (rowEnd b).equations = knowsXY ++ [(.const 2, ModuloControls.label 9)] := by
  cases b <;> rfl

theorem rowEnd_present_false : (rowEnd false).present = {20} := by decide

theorem rowEnd_present_true : (rowEnd true).present = {21} := by decide

/-- **The two ends are equivalent modulo the knowledge**, for a client that has seen nothing. -/
theorem rowEnds_modulo : ModuloEquivalent A ModuloControls.label ∅ (rowEnd false) (rowEnd true) := by
  refine (moduloEquivalent_iff A ModuloControls.label ∅ _ _).mpr ⟨?_, fun o member =>
    absurd member (Finset.notMem_empty o), ?_⟩
  · rw [rowEnd_equations, rowEnd_equations]
    exact fun _ => Iff.rfl
  · rw [rowEnd_present_false, rowEnd_present_true, Finset.singleton_val, Finset.singleton_val,
      Multiset.map_singleton, Multiset.map_singleton]
    refine congrArg (fun c => ({c} : Multiset _)) (Quotient.sound fun σ solved => ?_)
    rw [rowEnd_equations, SubstitutionAction.models_append] at solved
    exact solved.1 (X, Y) (List.mem_singleton_self _)

/-- **They are not privately equivalent**: the labels `X` and `Y` differ syntactically. -/
theorem rowEnds_not_private : ¬ PrivatelyEquivalent A ModuloControls.label ∅ (rowEnd false) (rowEnd true) := by
  intro h
  have bags := h.labels_eq
  rw [rowEnd_present_false, rowEnd_present_true, Finset.singleton_val, Finset.singleton_val,
    Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at bags
  exact X_ne_Y bags

open Classical in
/-- **Rows modulo the knowledge interfere where syntactic labels report a record**: both histories
are admitted at the token, and with the amplitudes `1` and `-1` their ends read `0` modulo the
knowledge and `2` with the private ends. -/
theorem labelled_rows :
    (makeRow X 20).Valid A ModuloControls.label tokenXY ∧
      (makeRow Y 21).Valid A ModuloControls.label tokenXY ∧
      Coherence.weight (fun _ => ()) (fun b => Quotient.mk (moduloSetoid A ModuloControls.label ∅) (rowEnd b))
        Coherence.Controls.opposite Finset.univ () = 0 ∧
      Coherence.weight (fun _ => ()) (fun b => Quotient.mk (privateSetoid A ModuloControls.label ∅) (rowEnd b))
        Coherence.Controls.opposite Finset.univ () = 2 := by
  refine ⟨makeRow_valid rfl (by decide), makeRow_valid rfl (by decide), ?_, ?_⟩
  · rw [Coherence.weight_pair_shared (fun b => Quotient.mk (moduloSetoid A ModuloControls.label ∅) (rowEnd b))
      (Quotient.sound rowEnds_modulo)]
    norm_num [Coherence.Controls.opposite, born_formula]
  · rw [Coherence.weight_pair_apart (fun b => Quotient.mk (privateSetoid A ModuloControls.label ∅) (rowEnd b))
      (fun same => rowEnds_not_private (Quotient.exact same))]
    rw [← Coherence.weight_pair_apart id (by decide) Coherence.Controls.opposite]
    exact Coherence.Controls.discard_is_not_forgetting.1

end ModuloInterference

#print axioms moduloEnd_mk_eq_iff
#print axioms moduloEnd_empty_of_nominalEnd
#print axioms fresh_alternative_moduloEquivalent_iff
#print axioms ModuloInterference.superposed_modulo_iff
#print axioms ModuloInterference.superposed_same_verdict
#print axioms ModuloInterference.superposed_modulo_private
#print axioms ModuloInterference.superposed_modulo_escaped
#print axioms ModuloInterference.superposed_nominal_agrees
#print axioms ModuloInterference.rowEnds_modulo
#print axioms ModuloInterference.rowEnds_not_private
#print axioms ModuloInterference.labelled_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
