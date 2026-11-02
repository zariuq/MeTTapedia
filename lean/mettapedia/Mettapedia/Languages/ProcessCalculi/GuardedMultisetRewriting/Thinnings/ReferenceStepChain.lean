import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ReferenceMatching
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ReferenceTemplates

/-!
# Contextual gather chains and exact query regions

Gather matching threads the canonical store because recovering a parameter
body can add shared nodes. All selected input references retain their meaning.
Completeness is required only at the actual input patterns, not at arbitrary
output templates with compound argument spines.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type} [DecidableEq Head] [DecidableEq V]

def matchList? : List (Pattern Head V) → Subst V (Term Head) → List (Term Head) → Option (Subst V (Term Head))
  | [], assignment, [] => some assignment
  | pattern :: rest, assignment, target :: targets =>
      (match? pattern assignment target).bind fun next => matchList? rest next targets
  | _, _, _ => none

theorem matchList_exact : ∀ (patterns : List (Pattern Head V))
    (assignment result : Subst V (Term Head)) (targets : List (Term Head)),
    (∀ p ∈ patterns, p.Input) →
      (matchList? patterns assignment targets = some result ↔ StepChain layer assignment patterns targets result)
  | [], assignment, result, [], _ => by
      simp only [matchList?, Option.some.injEq]
      constructor
      · rintro rfl; exact .nil _
      · intro chain; cases chain; rfl
  | [], _, _, _ :: _, _ => by
      constructor
      · intro impossible; cases impossible
      · intro chain; cases chain
  | _ :: _, _, _, [], _ => by
      constructor
      · intro impossible; cases impossible
      · intro chain; cases chain
  | pattern :: rest, assignment, result, target :: targets, input => by
      have first := input pattern (by simp)
      have others := fun p member => input p (List.mem_cons_of_mem pattern member)
      constructor
      · intro matched
        cases head : match? pattern assignment target with
        | none => simp [matchList?, head] at matched
        | some next =>
          have tail : matchList? rest next targets = some result := by simpa [matchList?, head] using matched
          exact .cons (match_sound head) ((matchList_exact rest next result targets others).mp tail)
      · intro chain
        cases chain with
        | cons step restChain =>
          simp only [matchList?, match_complete first step, Option.bind_some]
          exact (matchList_exact rest _ result targets others).mpr restChain

def matchListContextR : List (Pattern Head V) → Store Head → Subst V Ref → List Ref →
    Store Head × Option (Subst V Ref)
  | [], store, assignment, [] => (store, some assignment)
  | pattern :: rest, store, assignment, target :: targets =>
      let head := matchContextR store pattern assignment target
      match head.2 with
      | none => (head.1, none)
      | some next => matchListContextR rest head.1 next targets
  | _, store, _, _ => (store, none)

theorem matchListContextR_spec : ∀ (patterns : List (Pattern Head V))
    (store : Store Head) (assignment : Subst V Ref) (targets : List Ref),
    Canonical store → CanonSubst store assignment → (∀ r ∈ targets, CanonRef store r) →
      store <+: (matchListContextR patterns store assignment targets).1 ∧
      Canonical (matchListContextR patterns store assignment targets).1 ∧
      (∀ result, (matchListContextR patterns store assignment targets).2 = some result →
        CanonSubst (matchListContextR patterns store assignment targets).1 result) ∧
      (matchListContextR patterns store assignment targets).2.map
          (unfoldSubst (matchListContextR patterns store assignment targets).1) =
        matchList? patterns (unfoldSubst store assignment) (targets.map (unfold store))
  | [], store, assignment, [], canonical, validAssignment, _ => by
      refine ⟨List.prefix_refl _, canonical, ?_, rfl⟩
      intro result same
      cases same
      exact validAssignment
  | [], store, _, _ :: _, canonical, _, _ => by
      refine ⟨List.prefix_refl _, canonical, ?_, rfl⟩
      intro result impossible; cases impossible
  | _ :: _, store, _, [], canonical, _, _ => by
      refine ⟨List.prefix_refl _, canonical, ?_, rfl⟩
      intro result impossible; cases impossible
  | pattern :: rest, store, assignment, target :: targets, canonical, validAssignment, validTargets => by
      obtain ⟨grows, nextCanonical, assignments, semantic⟩ :=
        matchContextR_spec store canonical pattern assignment validAssignment target (validTargets target (by simp))
      simp only [matchListContextR]
      cases head : (matchContextR store pattern assignment target).2 with
      | none =>
        refine ⟨grows, nextCanonical, ?_, ?_⟩
        · intro result impossible; cases impossible
        · have refused : match? pattern (unfoldSubst store assignment) (unfold store target) = none := by
            simpa [head] using semantic.symm
          simp [matchList?, refused]
      | some next =>
        obtain ⟨more, finalCanonical, results, tail⟩ := matchListContextR_spec rest _ next targets nextCanonical
          (assignments next head) (fun r member => (validTargets r (by simp [member])).prefix grows)
        refine ⟨grows.trans more, finalCanonical, results, ?_⟩
        have produced : match? pattern (unfoldSubst store assignment) (unfold store target) =
            some (unfoldSubst (matchContextR store pattern assignment target).1 next) := by simpa [head] using semantic.symm
        have sameTargets : targets.map (unfold (matchContextR store pattern assignment target).1) =
            targets.map (unfold store) := by
          apply List.map_congr_left
          intro r member
          exact unfold_prefix canonical.topo grows (validTargets r (by simp [member])).valid
        rw [tail, sameTargets]
        simp [matchList?, produced]

theorem region_reference_exact {store : Store Head} (canonical : Canonical store)
    {pattern : Pattern Head V} (input : pattern.Input) {assignment : Subst V Ref}
    (validAssignment : CanonSubst store assignment) {target : Ref} (validTarget : CanonRef store target) :
    (matchContextR store pattern assignment target).2.isSome = true ↔
      layer.Covers (unfoldSubst store assignment) pattern (unfold store target) := by
  constructor
  · intro matched
    obtain ⟨result, found⟩ := Option.isSome_iff_exists.mp matched
    exact ⟨_, matchContextR_sound canonical validAssignment validTarget found⟩
  · rintro ⟨solution, solved⟩
    obtain ⟨result, found, _⟩ := matchContextR_complete canonical input validAssignment validTarget solved
    rw [found]
    rfl

/-- Native existence tests compute exactly the region used by the actual guarded rewriting check. -/
theorem matchesIn_contextual_shared {store : Store Head} (canonical : Canonical store)
    {assignment : Subst V Ref} (validAssignment : CanonSubst store assignment)
    (pattern : Pattern Head V) (input : pattern.Input) {bag : Multiset Ref}
    (validBag : ∀ r ∈ bag, CanonRef store r) :
    (bag.filter fun r => (matchContextR store pattern assignment r).2.isSome).map (unfold store) =
      matchesIn layer (unfoldSubst store assignment) pattern (bag.map (unfold store)) := by
  rw [matchesIn, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro r member
  simp only [Function.comp_def, semRegion_eq_true]
  exact region_reference_exact canonical input validAssignment (validBag r member)

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
