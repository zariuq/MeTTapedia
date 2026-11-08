import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResolutionAnswers

/-!
# Tabling modulo variants, from the step's own equivalences

Two calls are **variants** when they are equal up to a renaming of their variables. Variant tabling
reuses the answers computed for one call for every variant of it, renamed. This module derives that
reuse from the step.

## A renaming of variables is a frame automorphism

In the one-frame category of a substitution action, a renaming of variables `π` is an isomorphism
of the one frame: the substitution of `π`, with the substitution of `π⁻¹` as inverse
(`renamingIso`). A renaming of occurrence identities `κ` **covers** `π` when it carries every
label to its renamed label (`Covers`). Together they rename configurations (`renameVars`) and give
an **isomorphism of states** of the interface (`variantStateIso`), the notion the step's transport
and independence are stated over. Private equivalence is the case where the frame isomorphism is
the identity (`AnnotatedRuns.sameStateIso`); a variant moves the frame (`renamingIso_moves`).

## The step is equivariant

* A resolution firing renamed along a covering pair is admitted at the renamed configuration exactly
  when the firing is admitted at the configuration (`resolve_rename_valid`), and its result is the
  renamed result (`resolve_rename_result`).
* Hence resolution runs are carried along renamings (`rename_run`), and so are their answers:
  `τ` answers the renamed configuration exactly when `τ ∘ π` answers the configuration
  (`answers_rename`). The **answer instances** of a call, the instances of the call term at answers,
  are the same for a call and its renaming (`answerInstances_rename`).

## Variant equivalence

`VariantEquivalent C D`: a covering pair renames `C` to a configuration with the same solutions and
the same occurrences as `D`. It contains **private equivalence** (`PrivatelyEquivalent.variant`):
private renamings are the variant equivalences along the identity renaming of variables. It is
reflexive and symmetric (`VariantEquivalent.refl`, `VariantEquivalent.symm`).

* **Variant tabling is sound and complete** (`VariantEquivalent.answers`,
  `VariantEquivalent.answerInstances`): variant-equivalent calls have answers related by the
  variable renaming, and the same answer instances once the call term is renamed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open GuardFreeProcessOrders (SameUpTo)
open Interface (Frames Transport)

universe uO

variable {sig : LPSignature}

/-! ## Renamings of variables -/

/-- Composing with a renaming and then its inverse changes nothing. -/
theorem comp_permSubst_symm (τ : Subst sig) (π : Equiv.Perm sig.vars) :
    (τ ∘ₛ permSubst π.symm) ∘ₛ permSubst π = τ := by
  funext v
  show τ.applyTerm (.var (π.symm (π v))) = τ v
  rw [Equiv.symm_apply_apply]
  rfl

theorem comp_permSubst_symm' (τ : Subst sig) (π : Equiv.Perm sig.vars) :
    (τ ∘ₛ permSubst π) ∘ₛ permSubst π.symm = τ := by
  have twice := comp_permSubst_symm τ π.symm
  rwa [Equiv.symm_symm] at twice

theorem rename_injective (π : Equiv.Perm sig.vars) : Function.Injective (rename (sig := sig) π) :=
  fun s t same => by rw [← rename_symm_rename π s, same, rename_symm_rename]

/-- **A renaming of variables is an isomorphism of the one frame.** -/
def renamingIso (π : Equiv.Perm sig.vars) :
    (Frames.ofSubstitution (A sig)).Iso PUnit.unit PUnit.unit where
  hom := permSubst π
  inv := permSubst π.symm
  inv_hom t := rename_symm_rename π t
  hom_inv t := rename_rename_symm π t

/-- **A renaming that moves a variable moves the frame**: its isomorphism does not act as the
identity, unlike the frame part of a private renaming. -/
theorem renamingIso_moves {π : Equiv.Perm sig.vars} {v : sig.vars} (moved : π v ≠ v) :
    (Frames.ofSubstitution (A sig)).act (a := PUnit.unit) (b := PUnit.unit) (renamingIso π).hom
      (.var v) ≠ .var v :=
  fun same => moved (Term.var.inj same)

/-- Unification under the knowledge is carried along renamings. -/
theorem unifiable_rename (π : Equiv.Perm sig.vars) (K : EquationStore (Term sig)) (s t : Term sig) :
    Unifiable ((A sig).applyStore (permSubst π) K) (rename π s) (rename π t) ↔ Unifiable K s t := by
  constructor
  · rintro ⟨τ, solved, same⟩
    refine ⟨τ ∘ₛ permSubst π, ((A sig).models_applyStore _ _ K).mp solved, ?_⟩
    rw [Subst.applyTerm_comp, Subst.applyTerm_comp]
    exact same
  · rintro ⟨τ, solved, same⟩
    refine ⟨τ ∘ₛ permSubst π.symm, ((A sig).models_applyStore _ _ K).mpr ?_, ?_⟩
    · show (A sig).Models ((τ ∘ₛ permSubst π.symm) ∘ₛ permSubst π) K
      rw [comp_permSubst_symm]
      exact solved
    · rw [rename, rename, ← Subst.applyTerm_comp, ← Subst.applyTerm_comp, comp_permSubst_symm]
      exact same

variable {O : Type uO} [DecidableEq O] (label : O → Term sig)

/-- **A renaming of occurrence identities covers a renaming of variables** when it carries every
label to the renamed label. -/
def Covers (π : Equiv.Perm sig.vars) (κ : O ≃ O) : Prop := ∀ o, label (κ o) = rename π (label o)

omit [DecidableEq O] in
theorem Covers.symm {π : Equiv.Perm sig.vars} {κ : O ≃ O} (covers : Covers label π κ) :
    Covers label π.symm κ.symm := by
  intro o
  have here := covers (κ.symm o)
  rw [Equiv.apply_symm_apply] at here
  rw [here, rename_symm_rename]

omit [DecidableEq O] in
/-- Label-keeping renamings cover the identity renaming. -/
theorem covers_refl {κ : O ≃ O} (keeps : ∀ o, label (κ o) = label o) :
    Covers label (Equiv.refl sig.vars) κ := by
  intro o
  rw [keeps, rename, permSubst_refl, Subst.applyTerm_id]

/-- **A configuration renamed**: its knowledge along the renaming of variables, its occurrences
along the covering renaming. -/
def renameVars (π : Equiv.Perm sig.vars) (κ : O ≃ O) (C : Configuration (Term sig) O) :
    Configuration (Term sig) O :=
  ⟨(A sig).applyStore (permSubst π) C.equations, C.present.map κ.toEmbedding⟩

omit [DecidableEq O] in
theorem renameVars_symm (π : Equiv.Perm sig.vars) (κ : O ≃ O) (C : Configuration (Term sig) O) :
    renameVars π.symm κ.symm (renameVars π κ C) = C := by
  obtain ⟨equations, present⟩ := C
  simp only [renameVars, SubstitutionAction.applyStore, List.map_map, Finset.map_map,
    Configuration.mk.injEq]
  refine ⟨?_, ?_⟩
  · conv_rhs => rw [← List.map_id equations]
    refine List.map_congr_left fun e _ => ?_
    exact Prod.ext (rename_symm_rename π e.1) (rename_symm_rename π e.2)
  · rw [← Equiv.trans_toEmbedding, Equiv.self_trans_symm, Equiv.refl_toEmbedding, Finset.map_refl]

variable {label}

/-- **A variant is an isomorphism of states of the interface**: the renaming of variables is the
frame isomorphism, the covering renaming carries the occurrences. -/
def variantStateIso (π : Equiv.Perm sig.vars) (κ : O ≃ O) (C : Configuration (Term sig) O) :
    (firstOrder (A sig) label).StateIso C (renameVars π κ C) where
  frame := renamingIso π
  knowledge := fun _ _ => Iff.rfl
  rename := κ
  present := rfl

/-- **A renamed resolution firing is admitted at the renamed configuration** exactly when the
firing is admitted at the configuration. -/
theorem resolve_rename_valid {π : Equiv.Perm sig.vars} {κ : O ≃ O} (covers : Covers label π κ)
    (C : Configuration (Term sig) O) (o : O) (c : Clause sig) (ρ : Equiv.Perm sig.vars) (made : List O) :
    (resolve (κ o) c (ρ.trans π) (made.map κ)).Valid (A sig) label (renameVars π κ C) ↔
      (resolve o c ρ made).Valid (A sig) label C := by
  rw [resolve_valid_iff, resolve_valid_iff]
  have labels : (made.map κ).map label = (made.map label).map (rename π) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun r _ => covers r
  have body : c.body.map (rename (ρ.trans π)) = (c.body.map (rename ρ)).map (rename π) := by
    rw [List.map_map]
    exact List.map_congr_left fun b _ => rename_trans ρ π b
  refine and_congr (List.nodup_map_iff κ.injective) (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · rw [labels, body]
    exact (List.map_injective_iff.mpr (rename_injective π)).eq_iff
  · exact Finset.mem_map' κ.toEmbedding
  · constructor
    · intro fresh r member present
      exact fresh (κ r) (List.mem_map_of_mem member) (Finset.mem_map' κ.toEmbedding |>.mpr present)
    · intro fresh r member present
      obtain ⟨r₀, member₀, rfl⟩ := List.mem_map.mp member
      exact fresh r₀ member₀ ((Finset.mem_map' κ.toEmbedding).mp present)
  · show Unifiable ((A sig).applyStore (permSubst π) C.equations) _ _ ↔ _
    rw [covers, rename_trans]
    exact unifiable_rename π C.equations _ _

/-- **The renamed firing's result is the renamed result.** -/
theorem resolve_rename_result {π : Equiv.Perm sig.vars} {κ : O ≃ O} (covers : Covers label π κ)
    (C : Configuration (Term sig) O) (o : O) (c : Clause sig) (ρ : Equiv.Perm sig.vars) (made : List O) :
    (resolve (κ o) c (ρ.trans π) (made.map κ)).result label (renameVars π κ C) =
      renameVars π κ ((resolve o c ρ made).result label C) := by
  rw [resolve_result, resolve_result]
  simp only [renameVars, Configuration.mk.injEq]
  refine ⟨?_, ?_⟩
  · simp only [SubstitutionAction.applyStore, List.map_append, List.map_cons, List.map_nil]
    rw [covers, rename_trans]
    rfl
  · simp only [Finset.map_union, Finset.map_sdiff, Finset.map_singleton, AnnotatedRuns.toFinset_rename,
      Equiv.coe_toEmbedding]

/-! ## Runs and answers are carried along renamings -/

/-- A run carried along an equality of its start. -/
def Run.transfer {s t : Configuration (Term sig) O} (same : s = t)
    (r : (firstOrder (A sig) label).Run s) : (firstOrder (A sig) label).Run t :=
  same ▸ r

theorem Run.last_transfer {s t : Configuration (Term sig) O} (same : s = t)
    (r : (firstOrder (A sig) label).Run s) : (Run.transfer same r).last = r.last := by
  subst same
  rfl

theorem Run.word_transfer {s t : Configuration (Term sig) O} (same : s = t)
    (r : (firstOrder (A sig) label).Run s) : (Run.transfer same r).word = r.word := by
  subst same
  rfl

/-- **Resolution runs are carried along renamings.** -/
theorem rename_run (prog : Program sig) {π : Equiv.Perm sig.vars} {κ : O ≃ O}
    (covers : Covers label π κ) {C : Configuration (Term sig) O}
    (r : (firstOrder (A sig) label).Run C) (resolving : ∀ x ∈ r.word, IsResolution prog x.2) :
    ∃ r' : (firstOrder (A sig) label).Run (renameVars π κ C),
      (∀ x ∈ r'.word, IsResolution prog x.2) ∧ r'.last = renameVars π κ r.last ∧
        r'.word.length = r.word.length := by
  induction r with
  | nil C => exact ⟨.nil _, fun x member => absurd member List.not_mem_nil, rfl, rfl⟩
  | @cons C f admitted rest ih =>
      obtain ⟨rest', restResolving, restLast, restLength⟩ :=
        ih fun x member => resolving x (List.mem_cons_of_mem _ member)
      obtain ⟨o, c, ρ, made, member, rfl⟩ := resolving ⟨C, f⟩ List.mem_cons_self
      have admitted' : (firstOrder (A sig) label).Admits (s := renameVars π κ C)
          (resolve (κ o) c (ρ.trans π) (made.map κ)) :=
        (resolve_rename_valid covers C o c ρ made).mpr admitted
      have same : (firstOrder (A sig) label).result _ admitted' =
          renameVars π κ ((firstOrder (A sig) label).result _ admitted) :=
        resolve_rename_result covers C o c ρ made
      refine ⟨.cons _ admitted' (Run.transfer same.symm rest'), ?_, ?_, ?_⟩
      · intro x inWord
        rcases List.mem_cons.mp inWord with rfl | later
        · exact ⟨κ o, c, ρ.trans π, made.map κ, member, rfl⟩
        · rw [Run.word_transfer] at later
          exact restResolving x later
      · show (Run.transfer same.symm rest').last = _
        rw [Run.last_transfer]
        exact restLast
      · show (Run.transfer same.symm rest').word.length + 1 = rest.word.length + 1
        rw [Run.word_transfer]
        exact congrArg (· + 1) restLength

variable (label) in
/-- **The answers of a configuration**: the solutions of the final knowledge of its complete
resolution runs. -/
def Answers (prog : Program sig) (C : Configuration (Term sig) O) : Set (Subst sig) :=
  {τ | ∃ r : (firstOrder (A sig) label).Run C, (∀ x ∈ r.word, IsResolution prog x.2) ∧
    r.last.present = ∅ ∧ (A sig).Models τ r.last.equations}

variable (label) in
/-- **The answer instances of a call**: the instances of the call term at the answers. -/
def AnswerInstances (prog : Program sig) (C : Configuration (Term sig) O) (t : Term sig) :
    Set (Term sig) :=
  {u | ∃ τ ∈ Answers label prog C, u = τ.applyTerm t}

/-- **Answers are carried along renamings**: `τ` answers the renamed configuration exactly when
`τ ∘ π` answers the configuration. -/
theorem answers_rename (prog : Program sig) {π : Equiv.Perm sig.vars} {κ : O ≃ O}
    (covers : Covers label π κ) (C : Configuration (Term sig) O) (τ : Subst sig) :
    τ ∈ Answers label prog (renameVars π κ C) ↔ τ ∘ₛ permSubst π ∈ Answers label prog C := by
  constructor
  · rintro ⟨r, resolving, complete, solved⟩
    obtain ⟨r', resolving', last', -⟩ := rename_run prog (covers.symm) r resolving
    have back := renameVars_symm π κ C
    refine ⟨Run.transfer back r', ?_, ?_, ?_⟩
    · intro x member
      rw [Run.word_transfer] at member
      exact resolving' x member
    · rw [Run.last_transfer, last']
      show r.last.present.map κ.symm.toEmbedding = ∅
      rw [complete, Finset.map_empty]
    · rw [Run.last_transfer, last']
      show (A sig).Models _ ((A sig).applyStore (permSubst π.symm) r.last.equations)
      rw [(A sig).models_applyStore]
      show (A sig).Models ((τ ∘ₛ permSubst π) ∘ₛ permSubst π.symm) _
      rw [comp_permSubst_symm']
      exact solved
  · rintro ⟨r, resolving, complete, solved⟩
    obtain ⟨r', resolving', last', -⟩ := rename_run prog covers r resolving
    refine ⟨r', resolving', ?_, ?_⟩
    · rw [last']
      show r.last.present.map κ.toEmbedding = ∅
      rw [complete, Finset.map_empty]
    · rw [last']
      exact ((A sig).models_applyStore _ _ _).mpr solved

/-- **A call and its renaming have the same answer instances.** -/
theorem answerInstances_rename (prog : Program sig) {π : Equiv.Perm sig.vars} {κ : O ≃ O}
    (covers : Covers label π κ) (C : Configuration (Term sig) O) (t : Term sig) :
    AnswerInstances label prog (renameVars π κ C) (rename π t) = AnswerInstances label prog C t := by
  ext u
  constructor
  · rintro ⟨τ, answer, rfl⟩
    refine ⟨τ ∘ₛ permSubst π, (answers_rename prog covers C τ).mp answer, ?_⟩
    rw [Subst.applyTerm_comp]
  · rintro ⟨τ, answer, rfl⟩
    refine ⟨τ ∘ₛ permSubst π.symm, (answers_rename prog covers C _).mpr ?_, ?_⟩
    · rw [comp_permSubst_symm]
      exact answer
    · rw [rename, ← Subst.applyTerm_comp, comp_permSubst_symm]

/-! ## Configurations with the same solutions and occurrences have the same answers -/

/-- Moving a run along an isomorphism of the one-frame transport keeps its firings. -/
theorem moveRun_word {C D : Configuration (Term sig) O}
    (i : (firstOrderTransport (A sig) label).Iso C D) (r : (firstOrder (A sig) label).Run C) :
    ((firstOrderTransport (A sig) label).moveRun i r).word.map Sigma.snd = r.word.map Sigma.snd := by
  induction r generalizing D with
  | nil => rfl
  | cons f admitted rest ih =>
      show f :: ((firstOrderTransport (A sig) label).moveRun _ rest).word.map Sigma.snd =
        f :: rest.word.map Sigma.snd
      rw [ih]

/-- **Configurations with the same solutions and the same occurrences have the same answers.** -/
theorem answers_congr (prog : Program sig) {C D : Configuration (Term sig) O}
    (same : SameUpTo (A sig) C D) (τ : Subst sig) :
    τ ∈ Answers label prog C → τ ∈ Answers label prog D := by
  rintro ⟨r, resolving, complete, solved⟩
  let i : (firstOrderTransport (A sig) label).Iso C D := ⟨same⟩
  obtain ⟨⟨ends⟩⟩ := Transport.Similar.same_last (Transport.Similar.moveRun i r)
  refine ⟨(firstOrderTransport (A sig) label).moveRun i r, ?_, ?_, ?_⟩
  · intro x member
    have inFirings : x.2 ∈ ((firstOrderTransport (A sig) label).moveRun i r).word.map Sigma.snd :=
      List.mem_map_of_mem member
    rw [moveRun_word] at inFirings
    obtain ⟨y, inWord, sameFiring⟩ := List.mem_map.mp inFirings
    rw [← sameFiring]
    exact resolving y inWord
  · rw [← ends.2]
    exact complete
  · exact (ends.1 τ).mp solved

/-! ## Variant equivalence -/

variable (label) in
/-- **Variant equivalence**: a covering pair of renamings carries the first configuration to one
with the same solutions and the same occurrences as the second. -/
def VariantEquivalent (C D : Configuration (Term sig) O) : Prop :=
  ∃ (π : Equiv.Perm sig.vars) (κ : O ≃ O), Covers label π κ ∧ SameUpTo (A sig) (renameVars π κ C) D

omit [DecidableEq O] in
theorem renameVars_refl_same (κ : O ≃ O) (C : Configuration (Term sig) O) :
    SameUpTo (A sig) (renameVars (Equiv.refl sig.vars) κ C) (AnnotatedRuns.renameConfiguration κ C) := by
  refine ⟨fun τ => ?_, rfl⟩
  show (A sig).Models τ ((A sig).applyStore (permSubst (Equiv.refl sig.vars)) C.equations) ↔
    (A sig).Models τ C.equations
  rw [(A sig).models_applyStore, permSubst_refl]
  exact Iff.rfl

omit [DecidableEq O] in
/-- **Private equivalence is variant equivalence along the identity renaming of variables.** -/
theorem PrivatelyEquivalent.variant {E : Finset O} {C D : Configuration (Term sig) O}
    (h : Observation.PrivatelyEquivalent (A sig) label E C D) : VariantEquivalent label C D := by
  obtain ⟨κ, priv, same⟩ := h
  exact ⟨Equiv.refl _, κ, covers_refl label priv.keeps,
    GuardFreeProcessOrders.SameUpTo.trans (A sig) (renameVars_refl_same κ C) same⟩

omit [DecidableEq O] in
theorem VariantEquivalent.refl (C : Configuration (Term sig) O) : VariantEquivalent label C C :=
  PrivatelyEquivalent.variant (E := ∅) (Observation.PrivatelyEquivalent.refl C)

/-- **Variant-equivalent calls have answers related by the renaming of variables.** -/
theorem VariantEquivalent.answers (prog : Program sig) {C D : Configuration (Term sig) O}
    (h : VariantEquivalent label C D) :
    ∃ π : Equiv.Perm sig.vars, ∀ τ : Subst sig,
      τ ∈ Answers label prog D ↔ τ ∘ₛ permSubst π ∈ Answers label prog C := by
  obtain ⟨π, κ, covers, same⟩ := h
  refine ⟨π, fun τ => ?_⟩
  rw [← answers_rename prog covers C τ]
  exact ⟨answers_congr prog (AnnotatedRuns.sameUpTo_symm (A sig) same) τ, answers_congr prog same τ⟩

/-- **Variant tabling**: variant-equivalent calls have the same answer instances once the call term
is renamed, so the table of one call answers every variant of it. -/
theorem VariantEquivalent.answerInstances (prog : Program sig) {C D : Configuration (Term sig) O}
    (h : VariantEquivalent label C D) :
    ∃ π : Equiv.Perm sig.vars, ∀ t : Term sig,
      AnswerInstances label prog D (rename π t) = AnswerInstances label prog C t := by
  obtain ⟨π, κ, covers, same⟩ := h
  refine ⟨π, fun t => ?_⟩
  rw [← answerInstances_rename prog covers C t]
  ext u
  constructor
  · rintro ⟨τ, answer, rfl⟩
    exact ⟨τ, answers_congr prog (AnnotatedRuns.sameUpTo_symm (A sig) same) τ answer, rfl⟩
  · rintro ⟨τ, answer, rfl⟩
    exact ⟨τ, answers_congr prog same τ answer, rfl⟩

omit [DecidableEq O] in
theorem VariantEquivalent.symm {C D : Configuration (Term sig) O} (h : VariantEquivalent label C D) :
    VariantEquivalent label D C := by
  obtain ⟨π, κ, covers, same⟩ := h
  refine ⟨π.symm, κ.symm, covers.symm, ?_⟩
  have moved : SameUpTo (A sig) (renameVars π.symm κ.symm D)
      (renameVars π.symm κ.symm (renameVars π κ C)) := by
    refine ⟨fun τ => ?_, ?_⟩
    · show (A sig).Models τ ((A sig).applyStore _ D.equations) ↔
        (A sig).Models τ ((A sig).applyStore _ (renameVars π κ C).equations)
      rw [(A sig).models_applyStore, (A sig).models_applyStore]
      exact (same.1 _).symm
    · show D.present.map _ = (renameVars π κ C).present.map _
      rw [same.2]
  rw [renameVars_symm] at moved
  exact moved

#print axioms comp_permSubst_symm
#print axioms comp_permSubst_symm'
#print axioms rename_injective
#print axioms renamingIso
#print axioms renamingIso_moves
#print axioms unifiable_rename
#print axioms Covers.symm
#print axioms covers_refl
#print axioms renameVars_symm
#print axioms variantStateIso
#print axioms resolve_rename_valid
#print axioms resolve_rename_result
#print axioms rename_run
#print axioms answers_rename
#print axioms answerInstances_rename
#print axioms moveRun_word
#print axioms answers_congr
#print axioms PrivatelyEquivalent.variant
#print axioms VariantEquivalent.refl
#print axioms VariantEquivalent.answers
#print axioms VariantEquivalent.answerInstances
#print axioms VariantEquivalent.symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution
