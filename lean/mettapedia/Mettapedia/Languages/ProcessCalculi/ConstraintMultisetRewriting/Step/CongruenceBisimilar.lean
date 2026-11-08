import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CongruenceParallel

/-!
# Bisimilarity of the ordinary step is a congruence for disjoint parallel composition

The ordinary step labelled by rules (`Semantic.ruleOffers`) offers every semantic firing under its
rule. Among them is, for every configuration `F`, the firing that **is** the context `F`: it tells
the knowledge of `F` and makes its occurrences (`contextFiring`). Fired at `C` with the occurrences of
`F` absent, it leaves exactly the parallel composition `C ⊗ F` (`contextFiring_result`). So a
bisimulation already answers every context, and bisimilarity of the ordinary step is a congruence.

The argument uses three properties of a program labelled by rules (`ContextClosed`): a firing
offered under a rule has that rule, the firing of every context is offered, and renamings that keep
labels keep the program. The ordinary step has them (`ruleOffers_closed`), and so has the raw step
of the reflection layer (`rawOffers_closed`).

* **Renaming** (`bisimilar_rename_of_closed`, `ruleBisimilar_rename`): a renaming that keeps labels
  relates bisimilar configurations.
* **Congruence** (`bisimilar_tensor_of_closed`, `ruleBisimilar_tensor`): if `C` and `D` are
  bisimilar, then `C ⊗ F` and `D ⊗ F` are, for every `F` whose occurrences are disjoint from those
  of `C` and `D`, whatever its knowledge. If the composite knowledge is consistent, `C` fires the
  context, the counterpart at `D` makes occurrences with the labels of `F`, and a renaming onto
  those of `F` relates its result to `D ⊗ F`. If it is inconsistent at `C`, it is at `D` too, and
  neither composite moves. No fresh supply of identities is needed.
* **Both sides** (`bisimilar_tensor₂_of_closed`, `ruleBisimilar_tensor₂`): bisimilar parts compose
  to bisimilar wholes, given the disjointness that each composition needs.
* **The raw step** (`rawBisimilar_tensor`): its bisimilarity is a congruence as well. The congruence
  of bisimilarity does not need regions that read through solutions; what needs them is that
  equivalence modulo the knowledge be contained in bisimilarity
  (`Observation.ModuloEquivalent.semantic_bisimilar`, against `SemanticControls.syntactic_collision`).

## Why programs are different

A program offers only some firings, usually not the context's: closed bisimilarity of a program is
not a congruence (`Observation.CongruenceControls.closed_not_congruence`). The ordinary step can fire
every context itself; an open system can only receive contexts at its ports (`Race.OpenBisimilar`,
`Race.TriggeredProgram.minimalBisimilar_iff`).

## Disjointness is needed (`overlap_bisimilar_control`)

`{0}` and `{1}`, both labelled `τ`, are bisimilar. The context `{1}` is disjoint from the first and not
from the second; the composites hold two rows against one, and the rule that takes two rows of `τ`
fires only at the first.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Observation (finset_map_eq_self)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {label : O → T}

/-! ## The firing that is a context -/

section Context

variable (label) in
/-- The rule of a context: tell its knowledge, make rows with the labels of its occurrences. -/
noncomputable def contextRule (F : Configuration T O) : RuleInstance T :=
  ⟨[], [], F.equations, [], F.present.toList.map label⟩

variable (label) in
/-- **The firing that is a context**: it tells the knowledge of `F` and makes its occurrences. -/
noncomputable def contextFiring (F : Configuration T O) : Firing T S O :=
  ⟨contextRule label F, [], ⟨[], [], F.present.toList⟩⟩

omit [DecidableEq O] in
/-- The information of a firing of the context rule is the composite knowledge. -/
theorem problem_context (selection : Selection O) (C F : Configuration T O) :
    selection.problem label (contextRule label F) C = C.equations ++ F.equations := by
  simp [Selection.problem, Selection.equations, contextRule]

/-- **The context firing is admitted** when its occurrences are absent and the composite knowledge
is consistent. -/
theorem contextFiring_valid {C F : Configuration T O} (apart : Disjoint C.present F.present)
    (consistent : A.Consistent (C.equations ++ F.equations)) :
    (contextFiring (S := S) label F).Valid A label C := by
  refine ⟨⟨List.nodup_nil, F.present.nodup_toList, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · simp [contextFiring, Selection.commit]
  · simp [contextFiring, Selection.commit]
  · simp [contextFiring, Selection.commit]
  · show Disjoint F.present.toList.toFinset C.present
    rw [Finset.toList_toFinset]
    exact apart.symm
  · simp [contextFiring, Selection.commit]
  · show A.Consistent ((⟨[], [], F.present.toList⟩ : Selection O).problem label (contextRule label F) C)
    rw [problem_context]
    exact consistent
  · intro check member
    simp [contextFiring, contextRule] at member
  · intro query member
    simp [contextFiring] at member

/-- **Firing the context is composing with it.** -/
theorem contextFiring_result (C F : Configuration T O) :
    (contextFiring (S := S) label F).result label C = AnnotatedRuns.tensor C F := by
  show (⟨(⟨[], [], F.present.toList⟩ : Selection O).problem label (contextRule label F) C,
      fire C.present ((⟨[], [], F.present.toList⟩ : Selection O).commit (T := T))⟩ :
      Configuration T O) = ⟨C.equations ++ F.equations, C.present ∪ F.present⟩
  rw [problem_context]
  congr 1
  ext o
  simp [MeTTaCalculus.OccurrenceCommits.mem_fire, Selection.commit]

/-- **A firing of the context rule needs the composite knowledge to be consistent.** -/
theorem consistent_of_contextRule {C F : Configuration T O} {g : Firing T S O}
    (rule : g.rule = contextRule label F) (valid : g.Valid A label C) :
    A.Consistent (C.equations ++ F.equations) := by
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  rw [rule, problem_context] at solved
  exact ⟨σ, solved⟩

/-- **A configuration with inconsistent knowledge does not move.** -/
theorem no_moves_of_inconsistent {L : Type*} {offers : L → Firing T S O → Prop}
    {C : Configuration T O} (inconsistent : ¬ A.Consistent C.equations) {ℓ : L}
    {D : Configuration T O} : ¬ Race.Moves A label offers C ℓ D := by
  rintro ⟨f, -, valid, -⟩
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  exact inconsistent ⟨σ, Observation.problem_refines label f.selection f.rule σ solved⟩

end Context

/-! ## Programs labelled by rules that are closed under contexts -/

section Closed

variable (label) in
/-- **A program labelled by rules and closed under contexts**: every firing it offers under a rule
has that rule, it offers the firing of every context, and renamings that keep labels keep it. -/
structure ContextClosed (offers : RuleInstance T → Firing T S O → Prop) : Prop where
  rule : ∀ r f, offers r f → f.rule = r
  context : ∀ F : Configuration T O, offers (contextRule label F) (contextFiring label F)
  rename : ∀ π : O ≃ O, (∀ o, label (π o) = label o) → ∀ r f, offers r f → offers r (f.rename π)

omit [DecidableEq O] in
/-- **The ordinary step labelled by rules is closed under contexts.** -/
theorem ruleOffers_closed : ContextClosed label (ruleOffers (O := O) A) :=
  ⟨fun _ _ offered => offered.1, fun _ => ⟨rfl, isSemantic_of_queries_nil rfl⟩,
    fun π _ _ _ offered => ⟨offered.1, isSemantic_rename π offered.2⟩⟩

/-- **The raw step labelled by rules**, the reflection layer: every firing under its rule. -/
def rawOffers (r : RuleInstance T) (f : Firing T S O) : Prop := f.rule = r

omit [DecidableEq O] in
/-- **The raw step labelled by rules is closed under contexts.** -/
theorem rawOffers_closed : ContextClosed label (rawOffers (T := T) (S := S) (O := O)) :=
  ⟨fun _ _ offered => offered, fun _ => rfl, fun _ _ _ _ offered => offered⟩

variable {offers : RuleInstance T → Firing T S O → Prop}

/-- **A renaming that keeps labels relates bisimilar configurations** of a program closed under
contexts. -/
theorem bisimilar_rename_of_closed (closed : ContextClosed label offers) {π : O ≃ O}
    (keeps : ∀ o, label (π o) = label o) (C : Configuration T O) :
    Race.Bisimilar A label offers C (renameConfiguration π C) := by
  refine ⟨fun X Y => ∃ ρ : O ≃ O, (∀ o, label (ρ o) = label o) ∧ Y = renameConfiguration ρ X,
    ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, π, keeps, rfl⟩
  · rintro (X : Configuration T O) Y ⟨ρ, kept, rfl⟩ r X' ⟨f, offered, valid, rfl⟩
    exact ⟨_, ⟨f.rename ρ, closed.rename ρ kept r f offered, (Firing.valid_rename A kept f X).mpr valid,
      rfl⟩, ρ, kept, Firing.result_rename kept f X⟩
  · rintro (X : Configuration T O) Y ⟨ρ, kept, rfl⟩ r Y' ⟨g, offered, valid, rfl⟩
    have keptSymm : ∀ o, label (ρ.symm o) = label o := fun o => by
      have moved := kept (ρ.symm o)
      rw [Equiv.apply_symm_apply] at moved
      exact moved.symm
    have back : renameConfiguration ρ.symm (renameConfiguration ρ X) = X := by
      rw [← Observation.renameConfiguration_trans, Equiv.self_trans_symm,
        Observation.renameConfiguration_refl]
    have validBack : (g.rename ρ.symm).Valid A label X := by
      have moved := (Firing.valid_rename A keptSymm g (renameConfiguration ρ X)).mpr valid
      rwa [back] at moved
    refine ⟨(g.rename ρ.symm).result label X, ⟨g.rename ρ.symm, closed.rename ρ.symm keptSymm r g offered,
      validBack, rfl⟩, ρ, kept, ?_⟩
    have resultBack := Firing.result_rename keptSymm g (renameConfiguration ρ X)
    rw [back] at resultBack
    rw [resultBack, ← Observation.renameConfiguration_trans, Equiv.symm_trans_self,
      Observation.renameConfiguration_refl]

/-- **Bisimilarity of a program closed under contexts is a congruence for disjoint parallel
composition**, whatever the context's knowledge. -/
theorem bisimilar_tensor_of_closed (closed : ContextClosed label offers) {C D : Configuration T O}
    (h : Race.Bisimilar A label offers C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present) :
    Race.Bisimilar A label offers (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) := by
  by_cases consistent : A.Consistent (C.equations ++ F.equations)
  · have moved : Race.Moves A label offers C (contextRule label F) (AnnotatedRuns.tensor C F) :=
      ⟨contextFiring label F, closed.context F, contextFiring_valid apartC consistent,
        (contextFiring_result C F).symm⟩
    obtain ⟨R, bisimulation, related⟩ := h
    obtain ⟨D', ⟨g, offered, valid, rfl⟩, related'⟩ :=
      bisimulation.1 related (contextRule label F) moved
    have rule := closed.rule _ g offered
    have first : Race.Bisimilar A label offers (AnnotatedRuns.tensor C F) (g.result label D) :=
      ⟨R, bisimulation, related'⟩
    have takenNil : g.selection.taken = [] := by
      have lengths := valid.firing.take_length
      rw [rule] at lengths
      exact List.eq_nil_of_length_eq_zero lengths.symm
    have outputs : g.selection.made.map label = F.present.toList.map label := by
      have produced := valid.firing.outputs
      rw [rule] at produced
      exact produced
    have fresh : Disjoint g.selection.made.toFinset D.present := valid.firing.occurrences.fresh
    have resultEq : g.result label D =
        ⟨D.equations ++ F.equations, D.present ∪ g.selection.made.toFinset⟩ := by
      show (⟨g.selection.problem label g.rule D, fire D.present (g.selection.commit (T := T))⟩ :
        Configuration T O) = _
      rw [rule, problem_context]
      congr 1
      ext o
      simp [MeTTaCalculus.OccurrenceCommits.mem_fire, Selection.commit, takenNil]
    have bags : g.selection.made.toFinset.val.map label = F.present.val.map label := by
      rw [List.toFinset_val, valid.firing.output_distinct.dedup, Multiset.map_coe, outputs,
        ← Multiset.map_coe, Finset.coe_toList]
    obtain ⟨π, priv, onto, support⟩ := Observation.exists_supported_map (E := ∅) _ rfl
      (fun o member => absurd member (Finset.notMem_empty o)) bags
    have fixD : ∀ o ∈ D.present, π o = o := fun o inD =>
      support o (fun inMade => Finset.disjoint_left.mp fresh inMade inD)
        (fun inF => Finset.disjoint_left.mp apartD inD inF)
    have renamed : renameConfiguration π (g.result label D) = AnnotatedRuns.tensor D F := by
      rw [resultEq]
      show (⟨D.equations ++ F.equations, (D.present ∪ g.selection.made.toFinset).map π.toEmbedding⟩ :
        Configuration T O) = ⟨D.equations ++ F.equations, D.present ∪ F.present⟩
      rw [Finset.map_union, finset_map_eq_self π fixD, onto]
    have second := bisimilar_rename_of_closed (A := A) closed priv.keeps (g.result label D)
    rw [renamed] at second
    exact (Race.system A label offers).bisimilar_trans first second
  · have inconsistentD : ¬ A.Consistent (D.equations ++ F.equations) := by
      intro consistentD
      have moved : Race.Moves A label offers D (contextRule label F) (AnnotatedRuns.tensor D F) :=
        ⟨contextFiring label F, closed.context F, contextFiring_valid apartD consistentD,
          (contextFiring_result D F).symm⟩
      obtain ⟨R, bisimulation, related⟩ := h
      obtain ⟨C', ⟨g, offered, valid, -⟩, -⟩ := bisimulation.2.1 related (contextRule label F) moved
      exact consistent (consistent_of_contextRule (closed.rule _ g offered) valid)
    exact Race.bisimilar_of_halted (fun _ _ => no_moves_of_inconsistent consistent)
      (fun _ _ => no_moves_of_inconsistent inconsistentD)

/-- Composition is commutative up to the solutions of the knowledge. -/
theorem tensor_comm_sameUpTo (C F : Configuration T O) :
    SameUpTo A (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor F C) := by
  refine ⟨fun σ => ?_, Finset.union_comm _ _⟩
  show A.Models σ (C.equations ++ F.equations) ↔ A.Models σ (F.equations ++ C.equations)
  rw [A.models_append, A.models_append]
  exact and_comm

/-- **Bisimilar parts compose to bisimilar wholes**, given the disjointness of each composition. -/
theorem bisimilar_tensor₂_of_closed (closed : ContextClosed label offers) {C D F G : Configuration T O}
    (left : Race.Bisimilar A label offers C D) (right : Race.Bisimilar A label offers F G)
    (apartCF : Disjoint C.present F.present) (apartDF : Disjoint D.present F.present)
    (apartDG : Disjoint D.present G.present) :
    Race.Bisimilar A label offers (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D G) :=
  (Race.system A label offers).bisimilar_trans (bisimilar_tensor_of_closed closed left F apartCF apartDF)
    ((Race.system A label offers).bisimilar_trans
      (Race.bisimilar_of_sameUpTo A label offers (tensor_comm_sameUpTo D F))
      ((Race.system A label offers).bisimilar_trans
        (bisimilar_tensor_of_closed closed right D apartDF.symm apartDG.symm)
        (Race.bisimilar_of_sameUpTo A label offers (tensor_comm_sameUpTo G D))))

end Closed

/-! ## The ordinary step and the raw step -/

/-- **A renaming that keeps labels relates bisimilar configurations of the ordinary step.** -/
theorem ruleBisimilar_rename {π : O ≃ O} (keeps : ∀ o, label (π o) = label o) (C : Configuration T O) :
    Race.Bisimilar A label (ruleOffers A) C (renameConfiguration π C) :=
  bisimilar_rename_of_closed ruleOffers_closed keeps C

/-- **Bisimilarity of the ordinary step is a congruence for disjoint parallel composition**, whatever
the context's knowledge. -/
theorem ruleBisimilar_tensor {C D : Configuration T O} (h : Race.Bisimilar A label (ruleOffers A) C D)
    (F : Configuration T O) (apartC : Disjoint C.present F.present)
    (apartD : Disjoint D.present F.present) :
    Race.Bisimilar A label (ruleOffers A) (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) :=
  bisimilar_tensor_of_closed ruleOffers_closed h F apartC apartD

/-- **Bisimilar parts of the ordinary step compose to bisimilar wholes.** -/
theorem ruleBisimilar_tensor₂ {C D F G : Configuration T O}
    (left : Race.Bisimilar A label (ruleOffers A) C D) (right : Race.Bisimilar A label (ruleOffers A) F G)
    (apartCF : Disjoint C.present F.present) (apartDF : Disjoint D.present F.present)
    (apartDG : Disjoint D.present G.present) :
    Race.Bisimilar A label (ruleOffers A) (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D G) :=
  bisimilar_tensor₂_of_closed ruleOffers_closed left right apartCF apartDF apartDG

/-- **Bisimilarity of the raw step is a congruence too**: the congruence does not need regions that
read through solutions. -/
theorem rawBisimilar_tensor {C D : Configuration T O}
    (h : Race.Bisimilar A label (rawOffers (S := S)) C D) (F : Configuration T O)
    (apartC : Disjoint C.present F.present) (apartD : Disjoint D.present F.present) :
    Race.Bisimilar A label (rawOffers (S := S)) (AnnotatedRuns.tensor C F) (AnnotatedRuns.tensor D F) :=
  bisimilar_tensor_of_closed rawOffers_closed h F apartC apartD

/-! ## Disjointness is needed -/

section Overlap

variable (A) (τ : T)

/-- The rule that takes two rows of `τ`. -/
def takeTwo : RuleInstance T := ⟨[τ, τ], [], [], [], []⟩

/-- **A context present at one side breaks the congruence.** -/
theorem overlap_bisimilar_control :
    Race.Bisimilar A (fun _ : ℕ => τ) (ruleOffers A) ⟨[], {0}⟩ ⟨[], {1}⟩ ∧
      Disjoint ({0} : Finset ℕ) {1} ∧
      ¬ Race.Bisimilar A (fun _ : ℕ => τ) (ruleOffers A) (AnnotatedRuns.tensor ⟨[], {0}⟩ ⟨[], {1}⟩)
        (AnnotatedRuns.tensor ⟨[], {1}⟩ ⟨[], {1}⟩) := by
  refine ⟨?_, by decide, ?_⟩
  · have renamed := ruleBisimilar_rename (A := A) (label := fun _ : ℕ => τ) (π := Equiv.swap 0 1)
      (fun _ => rfl) ⟨[], {0}⟩
    have moved : renameConfiguration (Equiv.swap 0 1) (⟨[], {0}⟩ : Configuration T ℕ) = ⟨[], {1}⟩ := by
      show (⟨[], ({0} : Finset ℕ).map (Equiv.swap 0 1).toEmbedding⟩ : Configuration T ℕ) = ⟨[], {1}⟩
      rw [Finset.map_singleton, Equiv.coe_toEmbedding, Equiv.swap_apply_left]
    rwa [moved] at renamed
  · let f : Firing T S ℕ := ⟨takeTwo τ, [], ⟨[0, 1], [], []⟩⟩
    have ground : Race.Ground (fun _ : ℕ => τ) f :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, show ([0, 1] : List ℕ).Nodup by decide, List.nodup_nil⟩
    refine Race.not_bisimilar_of_sat (φ := .dia (takeTwo τ) .top) (Race.sat_dia.mpr ⟨_, ⟨f,
      ⟨rfl, isSemantic_of_queries_nil rfl⟩, (ground.valid_iff A Race.reflexive_nil).mpr
        (of_decide_eq_true rfl), rfl⟩, Race.sat_top _⟩) ?_
    rintro ⟨D', ⟨g, ⟨rule, -⟩, valid, -⟩, -⟩
    have lengths := valid.firing.take_length
    rw [rule] at lengths
    have inside : g.selection.taken.toFinset ⊆ ({1} ∪ {1} : Finset ℕ) :=
      valid.firing.occurrences.taken_subset
    have counted := Finset.card_le_card inside
    rw [List.toFinset_card_of_nodup valid.firing.take_distinct, ← lengths] at counted
    simp [takeTwo] at counted

end Overlap

#print axioms problem_context
#print axioms contextFiring_valid
#print axioms contextFiring_result
#print axioms consistent_of_contextRule
#print axioms no_moves_of_inconsistent
#print axioms ruleOffers_closed
#print axioms rawOffers_closed
#print axioms bisimilar_rename_of_closed
#print axioms bisimilar_tensor_of_closed
#print axioms tensor_comm_sameUpTo
#print axioms bisimilar_tensor₂_of_closed
#print axioms ruleBisimilar_rename
#print axioms ruleBisimilar_tensor
#print axioms ruleBisimilar_tensor₂
#print axioms rawBisimilar_tensor
#print axioms overlap_bisimilar_control

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic
