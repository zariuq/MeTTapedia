import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualSubstitution

/-!
# Supported instances of the actual guarded rewriting step

Ambient substitution acts on the values gathered and produced by a step and on
its pattern interfaces. Schematic bodies stay in their own parameter contexts.
The proof preserves take multiplicities and shared reads. State checks remain
checks: their transport is an explicit obligation. In the check-free fragment
the supported instance theorem needs no further condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type} [DecidableEq Head] [DecidableEq V]

def substituteCheck (target : Nat) (σ : Nat → Term Head)
    (check : Check V (Term Head) (Pattern Head V)) : Check V (Term Head) (Pattern Head V) :=
  ⟨check.pattern.substitute target σ, check.holds⟩

def substituteRule (target : Nat) (σ : Nat → Term Head)
    (rule : Rule V (Term Head) (Pattern Head V)) : Rule V (Term Head) (Pattern Head V) where
  take := rule.take.map (Pattern.substitute target σ)
  read := rule.read.map (Pattern.substitute target σ)
  checks := rule.checks.map (substituteCheck target σ)
  produce := rule.produce.map (Pattern.substitute target σ)

theorem solves_substitute {assignment : Subst V (Term Head)} {p : Pattern Head V} {t : Term Head}
    (solved : layer.Solves assignment p t) {target : Nat} (σ : Nat → Term Head)
    (permitted : ∀ i < p.scope, Term.supportedAt target (σ i) = true) :
    layer.Solves assignment (p.substitute target σ) (Term.substituteMany σ t) :=
  (solves_iff _ _ _).mpr (Pattern.inst_substitute ((solves_iff _ _ _).mp solved) σ permitted)

theorem solves_list_substitute {assignment : Subst V (Term Head)}
    {patterns : List (Pattern Head V)} {terms : List (Term Head)}
    (solved : List.Forall₂ (layer.Solves assignment) patterns terms)
    {target : Nat} (σ : Nat → Term Head)
    (permitted : ∀ p ∈ patterns, ∀ i < p.scope, Term.supportedAt target (σ i) = true) :
    List.Forall₂ (layer.Solves assignment) (patterns.map (Pattern.substitute target σ))
      (terms.map (Term.substituteMany σ)) := by
  induction solved with
  | nil => exact .nil
  | @cons p t ps ts head tail ih =>
    exact .cons (solves_substitute head σ (permitted p (by simp)))
      (ih (fun q member => permitted q (by simp [member])))

theorem template_substitute {assignment : Subst V (Term Head)}
    {patterns : List (Pattern Head V)} {terms : List (Term Head)}
    (applied : instTemplate layer assignment patterns = some terms)
    {target : Nat} (σ : Nat → Term Head)
    (permitted : ∀ p ∈ patterns, ∀ i < p.scope, Term.supportedAt target (σ i) = true) :
    instTemplate layer assignment (patterns.map (Pattern.substitute target σ)) =
      some (terms.map (Term.substituteMany σ)) := by
  induction patterns generalizing terms with
  | nil => simpa [instTemplate] using applied
  | cons p rest ih =>
    simp only [instTemplate, List.mapM_cons, layer] at applied
    cases head : p.inst assignment with
    | none => simp [head] at applied
    | some t =>
      cases tail : rest.mapM (fun q => q.inst assignment) with
      | none => simp [head, tail] at applied
      | some ts =>
        have same : t :: ts = terms := by simpa [head, tail] using applied
        subst terms
        have headMapped := Pattern.inst_substitute head σ (permitted p (by simp))
        have tailMapped := ih tail (fun q member => permitted q (by simp [member]))
        change ((p.substitute target σ) :: rest.map (Pattern.substitute target σ)).mapM
          (fun q => q.inst assignment) = _
        rw [List.mapM_cons, headMapped]
        change (instTemplate layer assignment (rest.map (Pattern.substitute target σ))).bind
          (fun tail => some (Term.substituteMany σ t :: tail)) = _
        rw [tailMapped]
        rfl

/-- The check obligation concerns the actual observed bags after substitution.
Scope support alone does not establish it for absence, counts or data predicates. -/
def ChecksTransport (rule : Rule V (Term Head) (Pattern Head V))
    (before : Multiset (Term Head)) (target : Nat) (σ : Nat → Term Head) : Prop :=
  ∀ assignment, BindsOnlyGathers layer rule assignment → ∀ check ∈ rule.checks,
    check.holds assignment (matchesIn layer assignment check.pattern before) →
      check.holds assignment (matchesIn layer assignment (check.pattern.substitute target σ)
        (before.map (Term.substituteMany σ)))

/-- Supported instances preserve the actual take/read/check/make step. -/
theorem step_substitute {rule : Rule V (Term Head) (Pattern Head V)}
    {before after : Multiset (Term Head)} (step : Step layer rule before after)
    {target : Nat} (σ : Nat → Term Head)
    (permitted : ∀ p ∈ rule.take ++ rule.read ++ rule.produce,
      ∀ i < p.scope, Term.supportedAt target (σ i) = true)
    (checks : ChecksTransport rule before target σ) :
    Step layer (substituteRule target σ rule)
      (before.map (Term.substituteMany σ)) (after.map (Term.substituteMany σ)) := by
  obtain ⟨assignment, frame, taken, kept, made, binds, takes, reads, inputEq, checked, produces, outputEq⟩ := step
  let f := Term.substituteMany σ
  refine ⟨assignment, frame.map f, taken.map f, kept.map f, made.map f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v outside
    apply binds v
    intro p member
    have mappedMember : p.substitute target σ ∈
        (substituteRule target σ rule).take ++ (substituteRule target σ rule).read := by
      simpa only [substituteRule, ← List.map_append] using List.mem_map.mpr ⟨p, member, rfl⟩
    simpa only [layer, Pattern.substitute_vars] using outside (p.substitute target σ) mappedMember
  · obtain ⟨terms, solved, same⟩ := takes
    refine ⟨terms.map f, solves_list_substitute solved σ ?_, ?_⟩
    · intro p member
      exact permitted p (by simp [member])
    · simpa using congrArg (Multiset.map f) same
  · obtain ⟨terms, solved, bounded, covered⟩ := reads
    refine ⟨terms.map f, solves_list_substitute solved σ ?_, ?_, ?_⟩
    · intro p member
      exact permitted p (by simp [member])
    · simpa using Multiset.map_le_map (f := f) bounded
    · intro t member
      obtain ⟨u, source, rfl⟩ := List.mem_map.mp member
      exact Multiset.mem_map.mpr ⟨u, covered u source, rfl⟩
  · simpa [f] using congrArg (Multiset.map f) inputEq
  · intro check member
    change check ∈ rule.checks.map (substituteCheck target σ) at member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    exact checks assignment binds original originalMember (checked original originalMember)
  · apply template_substitute produces σ
    intro p member
    exact permitted p (by simp [member])
  · simpa [f] using congrArg (Multiset.map f) outputEq

/-- No additional state obligation is needed for a rule with no checks. -/
theorem step_substitute_without_checks {rule : Rule V (Term Head) (Pattern Head V)}
    {before after : Multiset (Term Head)} (step : Step layer rule before after)
    (noChecks : rule.checks = []) {target : Nat} (σ : Nat → Term Head)
    (permitted : ∀ p ∈ rule.take ++ rule.read ++ rule.produce,
      ∀ i < p.scope, Term.supportedAt target (σ i) = true) :
    Step layer (substituteRule target σ rule)
      (before.map (Term.substituteMany σ)) (after.map (Term.substituteMany σ)) := by
  apply step_substitute step σ permitted
  intro assignment binds check member
  rw [noChecks] at member
  cases member

namespace SupportedStepControls

def variablePattern : Pattern Nat Nat := ⟨1, .idx 0⟩
def collapsedPattern : Pattern Nat Nat := variablePattern.substitute 0 (fun _ => Controls.seven)

theorem variable_covers (assignment : Subst Nat (Term Nat)) (t : Term Nat) :
    layer.Covers assignment variablePattern t ↔ t = .idx 0 := by
  constructor
  · rintro ⟨result, step⟩
    have applied := (solves_iff result variablePattern t).mp step.solves
    have same : (Term.idx 0 : Term Nat) = t := by
      simpa [Pattern.inst, variablePattern, TreePat.inst, Term.supportedAt] using applied
    exact same.symm
  · rintro rfl
    exact ⟨assignment, Extends.refl _, fun _ _ => rfl, (solves_iff _ _ _).mpr rfl⟩

theorem collapsed_covers (assignment : Subst Nat (Term Nat)) (t : Term Nat) :
    layer.Covers assignment collapsedPattern t ↔ t = Controls.seven := by
  constructor
  · rintro ⟨result, step⟩
    have applied := (solves_iff result collapsedPattern t).mp step.solves
    have raw : collapsedPattern.inst result = some Controls.seven := rfl
    exact (Option.some.inj (raw.symm.trans applied)).symm
  · rintro rfl
    exact ⟨assignment, Extends.refl _, fun _ _ => rfl, (solves_iff _ _ _).mpr rfl⟩

theorem absent_before (assignment : Subst Nat (Term Nat)) :
    matchesIn layer assignment variablePattern {Controls.seven} = 0 := by
  simp [matchesIn, semRegion_eq_true, variable_covers, Controls.seven]

theorem present_after (assignment : Subst Nat (Term Nat)) :
    matchesIn layer assignment collapsedPattern {Controls.seven} = {Controls.seven} := by
  simp [matchesIn, semRegion_eq_true, collapsed_covers]

def absenceRule : Rule Nat (Term Nat) (Pattern Nat Nat) where
  take := []
  read := []
  checks := [Check.absent variablePattern]
  produce := []

/-- A support-respecting contraction can create a match and invalidate absence. -/
theorem support_alone_does_not_transport_absence :
    ¬ChecksTransport absenceRule {Controls.seven} 0 (fun _ => Controls.seven) := by
  intro transport
  have allowed := transport (fun _ => none) (by intro v _; rfl)
    (Check.absent variablePattern) (by simp [absenceRule]) (absent_before _)
  change matchesIn layer (fun _ => none) collapsedPattern
    (({Controls.seven} : Multiset (Term Nat)).map (Term.substituteMany (fun _ => Controls.seven))) = 0 at allowed
  have unchanged : Term.substituteMany (fun _ => Controls.seven) Controls.seven = Controls.seven := rfl
  rw [Multiset.map_singleton, unchanged, present_after] at allowed
  have impossible := congrArg Multiset.card allowed
  simp at impossible

/-- A concrete instance of the unrestricted application law on the real step. -/
theorem specialize_closed_instance :
    Step layer (substituteRule 0 (fun _ => Controls.seven) Controls.specialize)
      {Controls.seven} {Controls.seven, Controls.seven} := by
  have mapped := step_substitute_without_checks Controls.specialize_step rfl
    (fun _ => Controls.seven) (target := 0) (by intro p _ i _; rfl)
  simpa [Term.substituteMany_idx, Controls.seven, Term.substituteMany,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.SingleSort.encode,
    Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.parallelSubstitute,
    Mettapedia.GSLT.LanguageDef.SortedSignatureIndexedABT.Term.Fields.parallelSubstitute,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.SingleSort.encodeFields,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.SingleSort.decode,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.SingleSort.decodeFields] using mapped

end SupportedStepControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
