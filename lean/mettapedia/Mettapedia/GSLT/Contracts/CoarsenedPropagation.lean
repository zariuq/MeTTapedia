import Mettapedia.Logic.LP.PropositionalChainer

/-!
# Projecting a positive recursive cache to a coarser theory

An identifying map of facts sends every old derivation to a
derivation of the projected ground rules. It can enable new proofs:
a premise previously missing at its precise spelling can be
supplied by an equivalent fact. The projected cache is therefore
a sound warm start, not necessarily the answer or a complete delta.

Grounding of new rules is a separate obligation. This profile permits
extra rules after the change if every transported old rule remains
valid. It does not apply to rebinding a comparison arbitrarily, to a
negative guard, or to consuming occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.CoarsenedPropagation

open Mettapedia.Logic.LP

variable {Old New : Type*} [DecidableEq Old] [DecidableEq New]

def mapRule (projection : Old → New) (rule : PropRule Old) : PropRule New :=
  ⟨rule.premises.image projection, projection rule.head⟩

def mapProgram (projection : Old → New) (program : PropProgram Old) : PropProgram New :=
  program.image (mapRule projection)

omit [DecidableEq Old] in
theorem derivable_projects (projection : Old → New) {before : PropProgram Old} {after : PropProgram New}
    {oldBase : Finset Old} (rulesPreserved : mapProgram projection before ⊆ after)
    {fact : Old} (derivation : Derivable before oldBase fact) :
    Derivable after (oldBase.image projection) (projection fact) := by
  induction derivation with
  | fact base => exact .fact (Finset.mem_image_of_mem _ base)
  | @rule rule declared _ ih =>
      apply Derivable.rule (r := mapRule projection rule)
        (rulesPreserved (Finset.mem_image_of_mem _ declared))
      intro premise appears
      obtain ⟨raw, used, rfl⟩ := Finset.mem_image.mp appears
      exact ih raw used

variable [Fintype Old] [Fintype New]

theorem projected_cache_sound (projection : Old → New)
    {before : PropProgram Old} {after : PropProgram New} (oldBase : Finset Old)
    (rulesPreserved : mapProgram projection before ⊆ after) :
    (saturate before oldBase).image projection ⊆ saturate after (oldBase.image projection) := by
  intro fact present
  obtain ⟨raw, derived, rfl⟩ := Finset.mem_image.mp present
  exact (saturate_iff_derivable _ _ _).mpr
    (derivable_projects projection rulesPreserved ((saturate_iff_derivable _ _ _).mp derived))

/-- No information is assumed stable just because the new key happens
to equal the old one. Reuse is justified by transporting the actual
old proof rules, then saturating on the new profile. -/
theorem warm_start_exact (projection : Old → New) {before : PropProgram Old} {after : PropProgram New}
    (oldBase : Finset Old) (rulesPreserved : mapProgram projection before ⊆ after) :
    saturate after ((saturate before oldBase).image projection) =
      saturate after (oldBase.image projection) := by
  apply Finset.Subset.antisymm
  · intro fact member
    exact derivable_subset_of_closed after _ _
      (projected_cache_sound projection oldBase rulesPreserved)
      (fun _ allowed ready => rule_closed_saturate _ _ allowed ready) _ (saturate_sound _ _ _ member)
  · intro fact member
    apply derivable_subset_of_closed after _ _
      (fun raw base => saturate_contains_facts _ _
        (Finset.image_subset_image (saturate_contains_facts before oldBase) base))
      (fun _ allowed ready => rule_closed_saturate _ _ allowed ready) _ (saturate_sound _ _ _ member)

/-- Merely rekeying the cache is valid precisely when it is already
closed under the target rules. This also identifies a semantic test
for a certificate that no new joins have appeared. -/
theorem rekey_only_exact_iff (projection : Old → New)
    {before : PropProgram Old} {after : PropProgram New}
    (oldBase : Finset Old) (rulesPreserved : mapProgram projection before ⊆ after) :
    (saturate before oldBase).image projection = saturate after (oldBase.image projection) ↔
      ∀ rule ∈ after, rule.premises ⊆ (saturate before oldBase).image projection →
        rule.head ∈ (saturate before oldBase).image projection := by
  constructor
  · intro equal
    rw [equal]
    exact fun _ allowed ready => rule_closed_saturate _ _ allowed ready
  · intro isClosed
    apply Finset.Subset.antisymm (projected_cache_sound projection oldBase rulesPreserved)
    intro fact member
    exact derivable_subset_of_closed after _ _
      (Finset.image_subset_image (saturate_contains_facts before oldBase)) isClosed
      _ (saturate_sound _ _ _ member)

namespace Controls

private def rewriteToKey : Fin 3 → Bool
  | 0 => false
  | 1 => false
  | _ => true

private def follow : PropProgram (Fin 3) := {⟨{0}, 2⟩}
private def oldFacts : Finset (Fin 3) := {1}

theorem identifying_inputs_can_enable_a_new_rule :
    true ∉ (saturate follow oldFacts).image rewriteToKey ∧
      true ∈ saturate (mapProgram rewriteToKey follow) (oldFacts.image rewriteToKey) := by
  decide +kernel

theorem restarting_projected_cache_finds_the_new_fact :
    true ∈ saturate (mapProgram rewriteToKey follow) ((saturate follow oldFacts).image rewriteToKey) := by
  rw [warm_start_exact rewriteToKey oldFacts (Finset.Subset.refl _)]
  exact identifying_inputs_can_enable_a_new_rule.2

end Controls

#print axioms derivable_projects
#print axioms projected_cache_sound
#print axioms warm_start_exact
#print axioms rekey_only_exact_iff
#print axioms Controls.identifying_inputs_can_enable_a_new_rule
#print axioms Controls.restarting_projected_cache_finds_the_new_fact

end Mettapedia.GSLT.Contracts.CoarsenedPropagation
