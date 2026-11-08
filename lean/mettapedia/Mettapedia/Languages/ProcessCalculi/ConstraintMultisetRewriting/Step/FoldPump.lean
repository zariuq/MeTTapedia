import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CanonicalFirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsSeparationFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsPeak

/-!
# The affine pump

A loop body that runs from `C` and ends in `C ⊗ δ` is pumped: it runs again beside what it already
made, and after `n` rounds the run ends in `C` beside `n` renamed copies of `δ`, whose labels are `n`
times the labels of `δ` (`affine_pump`). A positive balance alone never gives this; every
accumulated frame must keep the body admissible. The hypotheses say exactly that, for every round:

* **queries and guards**: every firing of the body is query-free (no predicate query, equation guards
  only), so it is blind to every frame;
* **tells**: `δ` carries no knowledge, so the knowledge of every accumulated frame is entailed;
* **freshness**: for every finite set of identities a label-keeping renaming fixes the start and moves
  what the body makes off that set (`supply`). Over the natural numbers it is a swap with an unused
  identity (`PumpControls.producer_supply`);
* **beside**: `δ` avoids the start's occurrences.

The first-order step has no authority layer, so no authority condition arises here.

## Controls (`PumpControls`)

* **Pumped** (`producer_pumps`): making one occurrence from the empty configuration pumps to `n`
  occurrences, for every `n`.
* **Refused** (`absent_guard_stops`): a rule that makes `b` while requiring `b` absent fires once from
  the empty configuration and is then refused, under every renaming of what it makes; its absence
  guard is not an equation, so it is not query-free.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open GuardFreeProcessOrders (SameUpTo)
open SeparationRuns (QueryFree Triple Separable tensor_congr follow_present_subset_space)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- What a renamed word makes is the renaming of what it makes. -/
theorem madeBy_rename (π : O ≃ O) :
    ∀ w : List (Firing T S O), madeBy (w.map (Firing.rename π)) = (madeBy w).map π.toEmbedding
  | [] => by simp [madeBy]
  | f :: w => by
      rw [List.map_cons, madeBy_cons, madeBy_cons, madeBy_rename π w, Finset.map_union]
      congr 1
      exact toFinset_rename (π := π) f.selection.made

omit [DecidableEq O] in
theorem renameConfiguration_tensor [DecidableEq O] (π : O ≃ O) (C D : Configuration T O) :
    renameConfiguration π (tensor C D) = tensor (renameConfiguration π C) (renameConfiguration π D) := by
  simp [renameConfiguration, tensor, Finset.map_union]

section Pump

variable (A : SubstitutionAction T S) (label : O → T)

/-- **The affine pump.** A query-free body that runs from `C` and ends in `C ⊗ δ`, with `δ` without
knowledge and beside `C`, and a supply of fresh renamings, runs `n` times in a row: after `n` rounds the
run ends in `C` beside a frame without knowledge whose labels are `n` times those of `δ`. -/
theorem affine_pump {w : List (Firing T S O)} {C δ : Configuration T O}
    (free : ∀ f ∈ w, QueryFree f) (runs : Executable A label C w)
    (ends : SameUpTo A (follow label C w) (tensor C δ)) (spatial : A.Equivalent δ.equations [])
    (beside : Disjoint C.present δ.present)
    (supply : ∀ F : Finset O, ∃ π : O ≃ O, (∀ o, label (π o) = label o) ∧
      C.present.map π.toEmbedding = C.present ∧ Disjoint (madeBy (w.map (Firing.rename π))) F) :
    ∀ n : ℕ, ∃ (u : List (Firing T S O)) (E : Configuration T O),
      Executable A label C u ∧ SameUpTo A (follow label C u) (tensor C E) ∧
        A.Equivalent E.equations [] ∧ Disjoint C.present E.present ∧
        E.present.val.map label = n • δ.present.val.map label := by
  have consistent : A.Consistent C.equations := executable_append_left A label C [] w runs
  have made : δ.present ⊆ madeBy w := by
    intro o member
    have there : o ∈ (follow label C w).present := by
      rw [ends.2]
      exact Finset.mem_union_right _ member
    rcases Finset.mem_union.mp (follow_present_subset_space label C w there) with old | new
    · exact absurd old (Finset.disjoint_right.mp beside member)
    · exact new
  intro n
  induction n with
  | zero =>
      refine ⟨[], unitConfiguration, consistent, ?_, fun _ => Iff.rfl, Finset.disjoint_empty_right _, ?_⟩
      · rw [tensor_unit_right]
        exact SameUpTo.refl A C
      · simp [unitConfiguration]
  | succ n ih =>
      obtain ⟨u, E, uRuns, uEnds, eKnows, eBeside, eLabels⟩ := ih
      obtain ⟨π, keeps, fixes, apart⟩ := supply (C.present ∪ E.present)
      have start : renameConfiguration π C = C := by
        show Configuration.mk C.equations (C.present.map π.toEmbedding) = C
        rw [fixes]
      have separable : Separable A C E := by
        refine ⟨eBeside, ?_⟩
        obtain ⟨σ, solved⟩ := consistent
        exact ⟨σ, (A.models_append σ _ _).mpr ⟨solved, (eKnows σ).mpr (A.models_nil σ)⟩⟩
      have triple : Triple A label (fun D => D = C) w (fun D => SameUpTo A D (tensor C δ)) := by
        rintro _ rfl
        exact ⟨runs, ends⟩
      obtain ⟨framedRuns, framedEnds, -⟩ := SeparationRuns.frame_rule_renamed A label triple free
        (R := fun D => D = E) (by rintro _ rfl; exact eKnows) rfl rfl separable π keeps fixes
        (apart.mono_right Finset.subset_union_right)
      have copy : Disjoint (δ.present.map π.toEmbedding) (C.present ∪ E.present) := by
        refine apart.mono_left ?_
        rw [madeBy_rename]
        exact Finset.map_subset_map.mpr made
      refine ⟨u ++ w.map (Firing.rename π), tensor (renameConfiguration π δ) E,
        executable_append' A label C u _ uRuns ((executable_congr A label _ uEnds).mpr framedRuns), ?_, ?_,
        ?_, ?_⟩
      · rw [follow_append']
        refine (follow_congr A label _ uEnds).trans A (framedEnds.trans A ?_)
        have renamed := tensor_congr A (Observation.sameUpTo_rename A π ends) (SameUpTo.refl A E)
        rw [renameConfiguration_tensor, start, tensor_assoc] at renamed
        exact renamed
      · intro σ
        show A.Models σ (δ.equations ++ E.equations) ↔ A.Models σ []
        rw [A.models_append, spatial σ, eKnows σ]
        exact and_self_iff
      · show Disjoint C.present (δ.present.map π.toEmbedding ∪ E.present)
        exact Finset.disjoint_union_right.mpr
          ⟨(copy.mono_right Finset.subset_union_left).symm, eBeside⟩
      · show (δ.present.map π.toEmbedding ∪ E.present).val.map label = (n + 1) • δ.present.val.map label
        rw [← Finset.disjUnion_eq_union _ _ (copy.mono_right Finset.subset_union_right),
          Finset.disjUnion_val, Multiset.map_add, Observation.labels_rename keeps, eLabels, succ_nsmul,
          add_comm]

end Pump

/-! ## Controls -/

namespace PumpControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open EscapeControls (blank)
open CanonicalControls (producer producer_valid_iff producer_present producer_equations blankStart)

/-- **Freshness over the natural numbers**: a swap with an unused identity. -/
theorem producer_supply (F : Finset ℕ) :
    ∃ π : ℕ ≃ ℕ, (∀ o, blank (π o) = blank o) ∧ blankStart.present.map π.toEmbedding = blankStart.present ∧
      Disjoint (madeBy ([producer 0].map (Firing.rename π))) F := by
  obtain ⟨m, unused⟩ := Infinite.exists_notMem_finset F
  refine ⟨Equiv.swap 0 m, fun _ => rfl, rfl, ?_⟩
  simpa [madeBy, Firing.rename, renameSelection, producer] using unused

/-- **Pumped**: making one occurrence pumps to `n` occurrences, for every `n`. -/
theorem producer_pumps (n : ℕ) :
    ∃ (u : List (Firing (Term signature) (Subst signature) ℕ)) (E : Configuration (Term signature) ℕ),
      Executable A blank blankStart u ∧ SameUpTo A (follow blank blankStart u) (tensor blankStart E) ∧
        E.present.card = n := by
  have runs : Executable A blank blankStart [producer 0] :=
    ⟨(producer_valid_iff rfl 0).mpr (Finset.notMem_empty 0), by
      refine ⟨Subst.id signature, fun e member => ?_⟩
      rw [producer_equations] at member
      cases member⟩
  have ends : SameUpTo A (follow blank blankStart [producer 0]) (tensor blankStart ⟨[], {0}⟩) := by
    refine ⟨fun σ => ?_, ?_⟩
    · show A.Models σ ((producer 0).result blank blankStart).equations ↔ A.Models σ ([] ++ [])
      rw [producer_equations]
      exact Iff.rfl
    · show ((producer 0).result blank blankStart).present = ∅ ∪ {0}
      rw [producer_present]
      rfl
  obtain ⟨u, E, uRuns, uEnds, -, -, labels⟩ := affine_pump A blank
    (fun f member => by
      obtain rfl := List.mem_singleton.mp member
      exact ⟨rfl, fun _ inside => by simp [producer] at inside⟩)
    runs ends (fun _ => Iff.rfl) (Finset.disjoint_empty_left _) producer_supply n
  refine ⟨u, E, uRuns, uEnds, ?_⟩
  have counted := congrArg Multiset.card labels
  simpa using counted

/-- Every occurrence labelled `1`. -/
def marked : ℕ → Term signature := fun _ => .const 1

/-- Makes occurrence `o`, labelled `1`, requiring that no `1` is present. -/
def once (o : ℕ) : Firing (Term signature) (Subst signature) ℕ :=
  ⟨⟨[], [], [], [.absent (.const 1)], [.const 1]⟩, [], ⟨[], [], [o]⟩⟩

theorem once_valid : (once 7).Valid A marked blankStart := by
  refine ⟨⟨by simp [once], by simp [once], rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, fun e member => by simp [Selection.problem, Selection.equations, once, blankStart] at member⟩,
    ?_⟩, by simp [once]⟩
  intro check member σ _
  obtain rfl : check = .absent (.const 1) := by simpa [once] using member
  intro o present
  simp [blankStart] at present

/-- **Refused**: the rule fires once from the empty configuration and is then refused, whatever
occurrence it would make; a positive balance does not pump it. -/
theorem absent_guard_stops :
    (once 7).Valid A marked blankStart ∧ (∀ o, ¬ (once o).Valid A marked ((once 7).result marked blankStart)) ∧
      ¬ QueryFree (once 7) := by
  refine ⟨once_valid, fun o valid => ?_, fun free => ?_⟩
  · have holds := valid.firing.checks (.absent (.const 1)) (by simp [once]) (Subst.id signature)
      (fun e member => by
        simp [Selection.problem, Selection.equations, Firing.result, Selection.result, once, blankStart] at member)
    exact holds 7 (by decide) rfl
  · obtain ⟨left, right, same⟩ := free.guards (.absent (.const 1)) (by simp [once])
    cases same

end PumpControls

#print axioms madeBy_rename
#print axioms renameConfiguration_tensor
#print axioms affine_pump
#print axioms PumpControls.producer_supply
#print axioms PumpControls.producer_pumps
#print axioms PumpControls.once_valid
#print axioms PumpControls.absent_guard_stops

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
