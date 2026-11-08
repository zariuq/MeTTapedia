import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResolutionTabling

/-!
# Tabling modulo the knowledge

Equivalence modulo the knowledge (`Observation.ModuloEquivalent`) relates configurations by a
renaming of occurrences that keeps labels up to what the knowledge entails. It is a bisimulation of
the one-frame step (`Observation.ModuloEquivalent.bisimulation`). For resolution runs:

* **A counterpart of a resolution firing is a resolution firing** (`resolution_of_rule`): an
  admitted firing with the rule of a resolution firing, its predicate queries dropped, is the
  resolution firing of the same clause and renaming on its selected goal, with the same result.
* **Configurations equivalent modulo the knowledge have the same answers**
  (`ModuloEquivalent.answers_subset`, `ModuloEquivalent.answers_eq`), when the renamed body goals
  have fresh identities (`BodySupply`).
* **Variants modulo the knowledge** (`ModuloVariant`): a covering pair of renamings carries the first
  configuration to one equivalent modulo the knowledge to the second. It contains variant equivalence
  (`VariantEquivalent.moduloVariant`), and its calls have answers related by the renaming of
  variables (`ModuloVariant.answers`), so a table keyed by this equivalence answers every call it
  identifies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution

open Mettapedia.Logic.LP
open AnnotatedRuns (Firing firstOrder)
open GuardFreeProcessOrders (SameUpTo)
open Observation (ModuloEquivalent)

universe uO

variable {sig : LPSignature} {O : Type uO} [DecidableEq O] {label : O → Term sig}

/-- The firing without its predicate queries. -/
def dropQueries (g : Firing (Term sig) (Subst sig) O) : Firing (Term sig) (Subst sig) O :=
  ⟨g.rule, [], g.selection⟩

/-- **A counterpart of a resolution firing is a resolution firing**: an admitted firing with the
rule of a resolution firing, its predicate queries dropped, is the resolution firing of the same
clause and renaming on its selected goal, and is admitted. -/
theorem resolution_of_rule {D : Configuration (Term sig) O} {g : Firing (Term sig) (Subst sig) O}
    {o : O} {c : Clause sig} {ρ : Equiv.Perm sig.vars} {made : List O}
    (rule : g.rule = (resolve o c ρ made).rule) (valid : g.Valid (A sig) label D) :
    ∃ x : O, dropQueries g = resolve x c ρ g.selection.made ∧ (dropQueries g).Valid (A sig) label D := by
  have takes := valid.firing.take_length
  have reads := valid.firing.read_length
  rw [rule] at takes reads
  obtain ⟨x, single⟩ := List.length_eq_one_iff.mp takes.symm
  have none : g.selection.read = [] := List.eq_nil_of_length_eq_zero reads.symm
  refine ⟨x, ?_, valid.firing, fun _ member => absurd member List.not_mem_nil⟩
  obtain ⟨rule', queries, ⟨taken, read, made'⟩⟩ := g
  simp only at rule single none
  subst rule single none
  rfl

/-- **Configurations equivalent modulo the knowledge have the same answers**, one inclusion: a
complete resolution run from the first is matched, firing by firing, by a complete resolution run
from the second whose final knowledge has the same solutions. -/
theorem ModuloEquivalent.answers_subset (prog : Program sig)
    (supply : BodySupply label prog) {E : Finset O}
    {C : Configuration (Term sig) O} (r : (firstOrder (A sig) label).Run C)
    (resolving : ∀ x ∈ r.word, IsResolution prog x.2) (complete : r.last.present = ∅)
    {τ : Subst sig} (solved : (A sig).Models τ r.last.equations) :
    ∀ {D : Configuration (Term sig) O}, ModuloEquivalent (A sig) label E C D →
      τ ∈ Answers label prog D := by
  induction r with
  | nil C =>
      intro D h
      have empty : D.present = ∅ := Finset.card_eq_zero.mp
        (h.card_eq ▸ Finset.card_eq_zero.mpr complete)
      exact ⟨.nil D, fun x member => absurd member List.not_mem_nil, empty, (h.solutions τ).mp solved⟩
  | @cons C f admitted rest ih =>
      intro D h
      obtain ⟨o, c, ρ, made, member, rfl⟩ := resolving ⟨C, f⟩ List.mem_cons_self
      obtain ⟨-, outputs, -, -, -⟩ := (resolve_valid_iff label C o c ρ made).mp admitted
      have fresh : ∀ r ∈ made, ∀ G : Finset O, ∃ x, x ∉ G ∧ label x = label r := by
        intro r inMade G
        have inLabels : label r ∈ c.body.map (rename ρ) := by
          rw [← outputs]
          exact List.mem_map_of_mem inMade
        obtain ⟨b, inBody, labelled⟩ := List.mem_map.mp inLabels
        rw [← labelled]
        exact supply c member b inBody ρ G
      obtain ⟨g, rule, gValid, results⟩ := h.bisimulation admitted
        (fun _ inQueries => absurd inQueries List.not_mem_nil) fresh
      obtain ⟨x, isResolution, valid⟩ := resolution_of_rule rule gValid
      obtain ⟨r', resolving', complete', solved'⟩ :=
        ih (fun y inWord => resolving y (List.mem_cons_of_mem _ inWord)) complete solved results
      refine ⟨.cons (dropQueries g) valid r', ?_, complete', solved'⟩
      intro y inWord
      rcases List.mem_cons.mp inWord with rfl | later
      · exact ⟨x, c, ρ, g.selection.made, member, isResolution⟩
      · exact resolving' y later

/-- **Configurations equivalent modulo the knowledge have the same answers.** -/
theorem ModuloEquivalent.answers_eq (prog : Program sig)
    (supply : BodySupply label prog) {E : Finset O}
    {C D : Configuration (Term sig) O} (h : ModuloEquivalent (A sig) label E C D) :
    Answers label prog C = Answers label prog D := by
  ext τ
  constructor
  · rintro ⟨r, resolving, complete, solved⟩
    exact ModuloEquivalent.answers_subset prog supply r resolving complete solved h
  · rintro ⟨r, resolving, complete, solved⟩
    exact ModuloEquivalent.answers_subset prog supply r resolving complete solved h.symm

variable (label) in
/-- **Variants modulo the knowledge**: a covering pair of renamings carries the first configuration to
one equivalent, modulo the knowledge and relative to the escaped identities `E`, to the second. -/
def ModuloVariant (E : Finset O) (C D : Configuration (Term sig) O) : Prop :=
  ∃ (π : Equiv.Perm sig.vars) (κ : O ≃ O), Covers label π κ ∧
    ModuloEquivalent (A sig) label E (renameVars π κ C) D

omit [DecidableEq O] in
/-- **Variant equivalence is a variant modulo the knowledge.** -/
theorem VariantEquivalent.moduloVariant {E : Finset O} {C D : Configuration (Term sig) O}
    (h : VariantEquivalent label C D) : ModuloVariant label E C D := by
  obtain ⟨π, κ, covers, same⟩ := h
  exact ⟨π, κ, covers, Observation.PrivatelyEquivalent.modulo (Observation.PrivatelyEquivalent.of_sameUpTo same)⟩

/-- **Tabling modulo the knowledge**: calls that are variants modulo the knowledge have answers
related by the renaming of variables. -/
theorem ModuloVariant.answers (prog : Program sig)
    (supply : BodySupply label prog) {E : Finset O}
    {C D : Configuration (Term sig) O} (h : ModuloVariant label E C D) :
    ∃ π : Equiv.Perm sig.vars, ∀ τ : Subst sig,
      τ ∈ Answers label prog D ↔ τ ∘ₛ permSubst π ∈ Answers label prog C := by
  obtain ⟨π, κ, covers, equivalent⟩ := h
  refine ⟨π, fun τ => ?_⟩
  rw [← answers_rename prog covers C τ, ModuloEquivalent.answers_eq prog supply equivalent]

#print axioms resolution_of_rule
#print axioms ModuloEquivalent.answers_subset
#print axioms ModuloEquivalent.answers_eq
#print axioms VariantEquivalent.moduloVariant
#print axioms ModuloVariant.answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Resolution
