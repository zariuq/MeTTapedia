import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ReferenceInstantiation
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.TemplateInstantiation

/-!
# Contextual templates use the common shared constructor traversal

The contextual resolver discharges the same primitive contract as plain
substitution. The whole template is built by `instantiateByR`, then its
enclosing scope is checked on the result reference. Output lists retain
duplicate values as distinct list occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {Head V : Type} [DecidableEq Head]

def contextualResolver (assignment : Subst V Ref) : VariableResolver Head (Occurrence Head V) :=
  fun occurrence store => atOccurrenceR store assignment occurrence

theorem contextualResolver_correct (store : Store Head) (canonical : Canonical store)
    (assignment : Subst V Ref) (valid : CanonSubst store assignment) :
    ResolverCorrect store (contextualResolver assignment) (Pattern.atOccurrence (unfoldSubst store assignment)) := by
  intro larger grows largerCanonical occurrence
  have correct := atOccurrenceR_spec larger largerCanonical assignment (valid.prefix grows) occurrence
  rw [unfoldSubst_prefix canonical.topo grows valid] at correct
  exact correct

def instantiateContextR (store : Store Head) (pattern : Pattern Head V) (assignment : Subst V Ref) :
    Store Head × Option Ref :=
  let raw := instantiateByR (contextualResolver assignment) pattern.tree store
  (raw.1, raw.2.bind fun result => if Scope.check result pattern.scope then some result else none)

theorem instantiateContextR_spec (store : Store Head) (canonical : Canonical store)
    (pattern : Pattern Head V) (assignment : Subst V Ref) (valid : CanonSubst store assignment) :
    store <+: (instantiateContextR store pattern assignment).1 ∧
      Canonical (instantiateContextR store pattern assignment).1 ∧
      (∀ result, (instantiateContextR store pattern assignment).2 = some result →
        CanonRef (instantiateContextR store pattern assignment).1 result) ∧
      (instantiateContextR store pattern assignment).2.map
          (unfold (instantiateContextR store pattern assignment).1) = pattern.inst (unfoldSubst store assignment) := by
  obtain ⟨grows, finalCanonical, refs, semantic⟩ := instantiateByR_spec store (contextualResolver assignment)
    (Pattern.atOccurrence (unfoldSubst store assignment)) (contextualResolver_correct store canonical assignment valid)
    pattern.tree store (List.prefix_refl _) canonical
  unfold instantiateContextR
  dsimp only
  refine ⟨grows, finalCanonical, ?_, ?_⟩
  · intro result accepted
    cases raw : (instantiateByR (contextualResolver assignment) pattern.tree store).2 with
    | none => simp [raw] at accepted
    | some value =>
      simp only [raw, Option.bind_some] at accepted
      split at accepted
      · have same : value = result := Option.some.inj accepted
        subst result
        exact refs value raw
      · cases accepted
  · unfold Pattern.inst
    rw [← semantic]
    cases raw : (instantiateByR (contextualResolver assignment) pattern.tree store).2 with
    | none => simp
    | some value =>
      simp only [Option.map_some, Option.bind_some]
      change (if Scope.check value pattern.scope then some value else none).map
          (unfold (instantiateByR (contextualResolver assignment) pattern.tree store).1) =
        (if Term.supportedAt pattern.scope
          (unfold (instantiateByR (contextualResolver assignment) pattern.tree store).1 value)
          then some (unfold (instantiateByR (contextualResolver assignment) pattern.tree store).1 value) else none)
      rw [Scope.check_spec finalCanonical (refs value raw)]
      split_ifs <;> rfl

def instantiateTemplatesR : List (Pattern Head V) → Store Head → Subst V Ref →
    Store Head × Option (List Ref)
  | [], store, _ => (store, some [])
  | pattern :: rest, store, assignment =>
      let head := instantiateContextR store pattern assignment
      match head.2 with
      | none => (head.1, none)
      | some value =>
          let tail := instantiateTemplatesR rest head.1 assignment
          (tail.1, tail.2.map (value :: ·))

variable [DecidableEq V]

theorem instantiateTemplatesR_spec (patterns : List (Pattern Head V)) (store : Store Head)
    (canonical : Canonical store) (assignment : Subst V Ref) (valid : CanonSubst store assignment) :
    store <+: (instantiateTemplatesR patterns store assignment).1 ∧
      Canonical (instantiateTemplatesR patterns store assignment).1 ∧
      (∀ results, (instantiateTemplatesR patterns store assignment).2 = some results →
        ∀ result ∈ results, CanonRef (instantiateTemplatesR patterns store assignment).1 result) ∧
      (instantiateTemplatesR patterns store assignment).2.map
          (List.map (unfold (instantiateTemplatesR patterns store assignment).1)) =
        instTemplate layer (unfoldSubst store assignment) patterns := by
  induction patterns generalizing store with
  | nil =>
    refine ⟨List.prefix_refl _, canonical, ?_, rfl⟩
    intro results accepted
    cases accepted
    simp
  | cons pattern rest ih =>
    obtain ⟨grows, nextCanonical, refs, semantic⟩ := instantiateContextR_spec store canonical pattern assignment valid
    simp only [instantiateTemplatesR]
    cases head : (instantiateContextR store pattern assignment).2 with
    | none =>
      refine ⟨grows, nextCanonical, ?_, ?_⟩
      · intro results impossible; cases impossible
      · have refused : pattern.inst (unfoldSubst store assignment) = none := by simpa [head] using semantic.symm
        simp [instTemplate, layer, refused]
    | some value =>
      obtain ⟨more, finalCanonical, children, tail⟩ := ih _ nextCanonical (valid.prefix grows)
      refine ⟨grows.trans more, finalCanonical, ?_, ?_⟩
      · intro results accepted
        obtain ⟨others, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
        intro result member
        rcases List.mem_cons.mp member with same | member
        · subst result
          exact (refs value head).prefix more
        · exact children others found result member
      · have produced : pattern.inst (unfoldSubst store assignment) =
            some (unfold (instantiateContextR store pattern assignment).1 value) := by simpa [head] using semantic.symm
        rw [unfoldSubst_prefix canonical.topo grows valid] at tail
        change Option.map (List.map (unfold (instantiateTemplatesR rest _ assignment).1))
          ((instantiateTemplatesR rest _ assignment).2.map (value :: ·)) = _
        unfold instTemplate
        rw [List.mapM_cons]
        change _ = (pattern.inst (unfoldSubst store assignment)).bind fun x =>
          (instTemplate layer (unfoldSubst store assignment) rest).bind fun xs => some (x :: xs)
        rw [produced, ← tail]
        cases result : (instantiateTemplatesR rest (instantiateContextR store pattern assignment).1 assignment).2 with
        | none => rfl
        | some values =>
          simp only [Option.map_some, Option.bind_some, List.map_cons,
            unfold_prefix nextCanonical.topo more (refs value head).valid]

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
