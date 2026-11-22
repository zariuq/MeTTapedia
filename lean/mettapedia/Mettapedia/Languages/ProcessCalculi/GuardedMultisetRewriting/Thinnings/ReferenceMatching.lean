import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ReferenceInstantiation
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.SharedRecovery
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualMatcher

/-!
# Reconciliation of contextual captures on references

An existing assignment is checked by shared grafting and canonical reference
equality. A fresh assignment is recovered by shared inverse renaming. Store
extensions preserve all earlier captures and assignments. The executable
reference pass agrees with the existing contextual reconciliation operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.ScopedApplication
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type} [DecidableEq Head] [DecidableEq V]

omit [DecidableEq Head] in
theorem canonical_update {store : Store Head} {assignment : Subst V Ref}
    (valid : CanonSubst store assignment) (name : V) {body : Ref} (bodyValid : CanonRef store body) :
    CanonSubst store (Function.update assignment name (some body)) := by
  intro v r assigned
  by_cases same : v = name
  · subst v
    have equal : body = r := by simpa using assigned
    simpa [equal] using bodyValid
  · exact valid v r (by simpa [Function.update, same] using assigned)

def solveOccurrenceR (store : Store Head) (occurrence : Occurrence Head V) (target : Ref)
    (assignment : Subst V Ref) : Store Head × Option (Subst V Ref) :=
  match assignment occurrence.name with
  | none =>
      let recovered := SharedApplication.recoverR store occurrence.arity occurrence.arguments target
      (recovered.1, recovered.2.map fun body => Function.update assignment occurrence.name (some body))
  | some _ =>
      let applied := atOccurrenceR store assignment occurrence
      (applied.1, applied.2.bind fun actual => if actual = target then some assignment else none)

theorem solveOccurrenceR_spec (store : Store Head) (canonical : Canonical store)
    (occurrence : Occurrence Head V) (target : Ref) (validTarget : CanonRef store target)
    (assignment : Subst V Ref) (validAssignment : CanonSubst store assignment) :
    store <+: (solveOccurrenceR store occurrence target assignment).1 ∧
      Canonical (solveOccurrenceR store occurrence target assignment).1 ∧
      (∀ result, (solveOccurrenceR store occurrence target assignment).2 = some result →
        CanonSubst (solveOccurrenceR store occurrence target assignment).1 result) ∧
      (solveOccurrenceR store occurrence target assignment).2.map
          (unfoldSubst (solveOccurrenceR store occurrence target assignment).1) =
        solveOccurrence occurrence (unfold store target) (unfoldSubst store assignment) := by
  cases assigned : assignment occurrence.name with
  | none =>
    obtain ⟨grows, nextCanonical, bodies, semantic⟩ :=
      SharedApplication.recoverR_spec store canonical occurrence.arity occurrence.arguments target validTarget
    simp only [solveOccurrenceR, assigned]
    refine ⟨grows, nextCanonical, ?_, ?_⟩
    · intro result accepted
      obtain ⟨body, recovered, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact canonical_update (validAssignment.prefix grows) occurrence.name (bodies body recovered)
    · simp only [solveOccurrence, unfoldSubst, assigned, Option.map_none]
      rw [← semantic]
      cases recovered : (SharedApplication.recoverR store occurrence.arity occurrence.arguments target).2 with
      | none => simp
      | some body =>
        simp only [Option.map_some]
        rw [unfoldSubst_update, unfoldSubst_prefix canonical.topo grows validAssignment]
  | some body =>
    obtain ⟨grows, nextCanonical, bodies, semantic⟩ := atOccurrenceR_spec store canonical assignment validAssignment occurrence
    have old : unfoldSubst store assignment occurrence.name = some (unfold store body) := by
      simp [unfoldSubst, assigned]
    simp only [solveOccurrenceR, assigned]
    refine ⟨grows, nextCanonical, ?_, ?_⟩
    · intro result accepted
      cases applied : (atOccurrenceR store assignment occurrence).2 with
      | none => simp [applied] at accepted
      | some actual =>
        simp only [applied, Option.bind_some] at accepted
        split at accepted
        · cases accepted
          exact validAssignment.prefix grows
        · cases accepted
    · simp only [solveOccurrence, old]
      have forward : (atOccurrenceR store assignment occurrence).2.map
          (unfold (atOccurrenceR store assignment occurrence).1) =
          graft occurrence.arity occurrence.arguments (unfold store body) := by
        simpa [Pattern.atOccurrence, old] using semantic
      cases applied : (atOccurrenceR store assignment occurrence).2 with
      | none =>
        have refused : graft occurrence.arity occurrence.arguments (unfold store body) = none := by
          simpa [applied] using forward.symm
        simp [refused]
      | some actual =>
        have produced : graft occurrence.arity occurrence.arguments (unfold store body) =
            some (unfold (atOccurrenceR store assignment occurrence).1 actual) := by
          simpa [applied] using forward.symm
        have same : actual = target ↔
            unfold (atOccurrenceR store assignment occurrence).1 actual = unfold store target := by
          rw [← unfold_prefix canonical.topo grows validTarget.valid]
          exact (unfold_eq_iff nextCanonical (bodies actual applied) (validTarget.prefix grows)).symm
        by_cases equal : actual = target
        · simp [equal, produced, unfoldSubst_prefix canonical.topo grows validAssignment,
            unfold_prefix canonical.topo grows validTarget.valid]
        · simp [equal, produced, mt same.mpr equal]

def reconcileR : List (Occurrence Head V) → Store Head → Subst (Occurrence Head V) Ref →
    Subst V Ref → Store Head × Option (Subst V Ref)
  | [], store, _, assignment => (store, some assignment)
  | occurrence :: rest, store, targets, assignment =>
      match targets occurrence with
      | none => (store, none)
      | some target =>
          let solved := solveOccurrenceR store occurrence target assignment
          match solved.2 with
          | none => (solved.1, none)
          | some next => reconcileR rest solved.1 targets next

theorem reconcileR_spec (occurrences : List (Occurrence Head V)) (store : Store Head)
    (canonical : Canonical store) (targets : Subst (Occurrence Head V) Ref)
    (validTargets : CanonSubst store targets) (assignment : Subst V Ref)
    (validAssignment : CanonSubst store assignment) :
    store <+: (reconcileR occurrences store targets assignment).1 ∧
      Canonical (reconcileR occurrences store targets assignment).1 ∧
      (∀ result, (reconcileR occurrences store targets assignment).2 = some result →
        CanonSubst (reconcileR occurrences store targets assignment).1 result) ∧
      (reconcileR occurrences store targets assignment).2.map
          (unfoldSubst (reconcileR occurrences store targets assignment).1) =
        reconcile occurrences (unfoldSubst store targets) (unfoldSubst store assignment) := by
  induction occurrences generalizing store assignment with
  | nil =>
    refine ⟨List.prefix_refl _, canonical, ?_, rfl⟩
    intro result same
    cases same
    exact validAssignment
  | cons occurrence rest ih =>
    cases found : targets occurrence with
    | none =>
      simp only [reconcileR, found]
      refine ⟨List.prefix_refl _, canonical, ?_, ?_⟩
      · intro result impossible; cases impossible
      · simp [reconcile, unfoldSubst, found]
    | some target =>
      obtain ⟨grows, nextCanonical, results, semantic⟩ := solveOccurrenceR_spec store canonical occurrence target
        (validTargets occurrence target found) assignment validAssignment
      have selected : unfoldSubst store targets occurrence = some (unfold store target) := by
        simp [unfoldSubst, found]
      simp only [reconcileR, found]
      cases solved : (solveOccurrenceR store occurrence target assignment).2 with
      | none =>
        refine ⟨grows, nextCanonical, ?_, ?_⟩
        · intro result impossible; cases impossible
        · have refused : solveOccurrence occurrence (unfold store target) (unfoldSubst store assignment) = none := by
            simpa [solved] using semantic.symm
          simp [reconcile, selected, refused]
      | some next =>
        obtain ⟨more, finalCanonical, finalAssignment, tail⟩ :=
          ih _ nextCanonical (validTargets.prefix grows) next (results next solved)
        refine ⟨grows.trans more, finalCanonical, finalAssignment, ?_⟩
        have head : solveOccurrence occurrence (unfold store target) (unfoldSubst store assignment) =
            some (unfoldSubst (solveOccurrenceR store occurrence target assignment).1 next) := by
          simpa [solved] using semantic.symm
        rw [tail, unfoldSubst_prefix canonical.topo grows validTargets]
        simp [reconcile, selected, head]

/-- The complete contextual capture path uses references throughout. -/
def matchContextR (store : Store Head) (pattern : Pattern Head V)
    (assignment : Subst V Ref) (target : Ref) : Store Head × Option (Subst V Ref) :=
  if Scope.check target pattern.scope then
    match matchR pattern.tree store (fun _ => none) target with
    | none => (store, none)
    | some targets => reconcileR (occurrences pattern.tree) store targets assignment
  else (store, none)

/-- Store growth and canonicality accompany exact agreement with contextual matching. -/
theorem matchContextR_spec (store : Store Head) (canonical : Canonical store)
    (pattern : Pattern Head V) (assignment : Subst V Ref) (validAssignment : CanonSubst store assignment)
    (target : Ref) (validTarget : CanonRef store target) :
    store <+: (matchContextR store pattern assignment target).1 ∧
      Canonical (matchContextR store pattern assignment target).1 ∧
      (∀ result, (matchContextR store pattern assignment target).2 = some result →
        CanonSubst (matchContextR store pattern assignment target).1 result) ∧
      (matchContextR store pattern assignment target).2.map
          (unfoldSubst (matchContextR store pattern assignment target).1) =
        match? pattern (unfoldSubst store assignment) (unfold store target) := by
  by_cases inScope : Scope.check target pattern.scope = true
  · have scopedTarget : Term.supportedAt pattern.scope (unfold store target) = true := by
      rwa [Scope.check_spec canonical validTarget]
    obtain ⟨validCaptures, structural⟩ := matchR_spec pattern.tree store (fun _ => none) target canonical
      (by intro o r impossible; cases impossible) validTarget
    change (matchR pattern.tree store (fun _ => none) target).map (unfoldSubst store) =
      matchT pattern.tree (fun _ => none) (unfold store target) at structural
    cases captured : matchR pattern.tree store (fun _ => none) target with
    | none =>
      have absent : matchT pattern.tree (fun _ => none) (unfold store target) = none := by
        simpa [captured] using structural.symm
      simp only [matchContextR, inScope, ↓reduceIte, captured]
      refine ⟨List.prefix_refl _, canonical, ?_, ?_⟩
      · intro result impossible; cases impossible
      · simp [match?, scopedTarget, absent]
    | some targets =>
      have found : matchT pattern.tree (fun _ => none) (unfold store target) =
          some (unfoldSubst store targets) := by simpa [captured] using structural.symm
      have reconciled := reconcileR_spec (occurrences pattern.tree) store canonical targets
        (validCaptures targets captured) assignment validAssignment
      simpa [matchContextR, inScope, captured, match?, scopedTarget, found] using reconciled
  · simp only [matchContextR, inScope]
    refine ⟨List.prefix_refl _, canonical, ?_, ?_⟩
    · intro result impossible; cases impossible
    · simp [match?, Scope.check_spec canonical validTarget, inScope]

theorem matchContextR_sound {store : Store Head} (canonical : Canonical store)
    {pattern : Pattern Head V} {assignment : Subst V Ref} (validAssignment : CanonSubst store assignment)
    {target : Ref} (validTarget : CanonRef store target) {result : Subst V Ref}
    (matched : (matchContextR store pattern assignment target).2 = some result) :
    layer.Step (unfoldSubst store assignment) pattern (unfold store target)
      (unfoldSubst (matchContextR store pattern assignment target).1 result) := by
  apply match_sound
  have exactResult := (matchContextR_spec store canonical pattern assignment validAssignment target validTarget).2.2.2
  simpa [matched] using exactResult.symm

theorem matchContextR_complete {store : Store Head} (canonical : Canonical store)
    {pattern : Pattern Head V} (input : pattern.Input) {assignment : Subst V Ref}
    (validAssignment : CanonSubst store assignment) {target : Ref} (validTarget : CanonRef store target)
    {solution : Subst V (Term Head)}
    (solved : layer.Step (unfoldSubst store assignment) pattern (unfold store target) solution) :
    ∃ result, (matchContextR store pattern assignment target).2 = some result ∧
      unfoldSubst (matchContextR store pattern assignment target).1 result = solution := by
  apply Option.map_eq_some_iff.mp
  rw [(matchContextR_spec store canonical pattern assignment validAssignment target validTarget).2.2.2,
    match_complete input solved]

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
