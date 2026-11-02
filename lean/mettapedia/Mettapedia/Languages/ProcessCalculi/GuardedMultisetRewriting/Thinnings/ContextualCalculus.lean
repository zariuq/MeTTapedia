import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualSharedStep
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel

/-!
# Contextual reference execution uses the guarded rewriting calculus and its authority

Both structural readings use the contextual term layer in the stated
alpha-only profile. The reference implementation preserves and reflects its
process steps. The existing rights and theorem-space theorems consequently
apply to this implementation without introducing a proof interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel
  (AllDerivable Derivable InstalledInfers)

universe uN
variable {Head V : Type} {N : Type uN} [DecidableEq Head] [DecidableEq V]

def contextualCalculus (space : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Head → N) : Calculus V (Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Head) (Pattern Head V) N where
  asValues := layer
  asSyntax := layer
  finer := fun _ _ same => same
  space := space

theorem contextualCalculus_layer (space : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Head → N) (contract : Contract) :
    (contextualCalculus (V := V) space).readers.layer contract = layer := by cases contract <;> rfl

variable {space : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Head → N}

def ProcessInputs (process : (contextualCalculus (V := V) space).Process) : Prop :=
  ∀ installed ∈ process.rules, ruleInputCheck installed.2 = true

def SharedProcessStep (process : (contextualCalculus (V := V) space).Process)
    (store : Store Head) (bag : Multiset Ref) (finalStore : Store Head) (finalBag : Multiset Ref) : Prop :=
  ∃ installed ∈ process.rules, SharedStep installed.2 store bag finalStore finalBag

theorem sharedProcessStep_sound {process : (contextualCalculus (V := V) space).Process}
    (inputs : ProcessInputs process) {store finalStore : Store Head} {bag finalBag : Multiset Ref}
    (canonical : Canonical store) (validBag : ∀ r ∈ bag, CanonRef store r)
    (step : SharedProcessStep process store bag finalStore finalBag) :
    store <+: finalStore ∧ Canonical finalStore ∧ (∀ r ∈ finalBag, CanonRef finalStore r) ∧
      process.Step (trees store bag) (trees finalStore finalBag) := by
  obtain ⟨installed, member, execution⟩ := step
  obtain ⟨grows, finalCanonical, outputs, core⟩ :=
    sharedStep_sound ((ruleInputCheck_iff _).mp (inputs installed member)) canonical validBag execution
  refine ⟨grows, finalCanonical, outputs, installed, member, ?_⟩
  rw [contextualCalculus_layer]
  exact core

theorem sharedProcessStep_complete {process : (contextualCalculus (V := V) space).Process}
    (inputs : ProcessInputs process) {store : Store Head} {bag : Multiset Ref}
    (canonical : Canonical store) (validBag : ∀ r ∈ bag, CanonRef store r) {after : Multiset (Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Head)}
    (step : process.Step (trees store bag) after) :
    ∃ finalStore finalBag, SharedProcessStep process store bag finalStore finalBag ∧
      trees finalStore finalBag = after := by
  obtain ⟨installed, member, execution⟩ := step
  rw [contextualCalculus_layer] at execution
  obtain ⟨finalStore, finalBag, shared, same⟩ :=
    sharedStep_complete ((ruleInputCheck_iff _).mp (inputs installed member)) canonical validBag execution
  exact ⟨finalStore, finalBag, ⟨installed, member, shared⟩, same⟩

theorem sharedProcessStep_no_make_without_send [DecidableEq N]
    {process : (contextualCalculus (V := V) space).Process} (inputs : ProcessInputs process)
    {store finalStore : Store Head} {bag finalBag : Multiset Ref}
    (canonical : Canonical store) (validBag : ∀ r ∈ bag, CanonRef store r)
    (step : SharedProcessStep process store bag finalStore finalBag)
    {destination : N} (denied : process.rights destination .send = false) :
    snapshot space destination (trees finalStore finalBag) ≤ snapshot space destination (trees store bag) :=
  Calculus.Process.Step.no_make_without_send (sharedProcessStep_sound inputs canonical validBag step).2.2.2 denied

theorem sharedProcessStep_allDerivable [DecidableEq N]
    {process : (contextualCalculus (V := V) space).Process} (inputs : ProcessInputs process)
    {store finalStore : Store Head} {bag finalBag : Multiset Ref}
    (canonical : Canonical store) (validBag : ∀ r ∈ bag, CanonRef store r)
    (step : SharedProcessStep process store bag finalStore finalBag)
    {theorems : N} {initial : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Head → Prop}
    (validBefore : AllDerivable (contextualCalculus (V := V) space) theorems
      (Derivable initial (InstalledInfers (contextualCalculus (V := V) space) theorems process.rules))
      (trees store bag)) :
    AllDerivable (contextualCalculus (V := V) space) theorems
      (Derivable initial (InstalledInfers (contextualCalculus (V := V) space) theorems process.rules))
      (trees finalStore finalBag) :=
  Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel.Calculus.Process.Step.allDerivable
    (sharedProcessStep_sound inputs canonical validBag step).2.2.2 validBefore

namespace CalculusControls

def source : Store Nat × Ref := encodeR [] (.idx 0 : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Nat)

theorem source_canonical : Canonical source.1 := (encodeR_spec [] canonical_nil _).2.1
theorem source_valid : CanonRef source.1 source.2 := (encodeR_spec [] canonical_nil _).2.2.1
theorem source_tree : unfold source.1 source.2 = .idx 0 := encodeR_unfold canonical_nil _

theorem contextual_step_has_shared_realization :
    ∃ store bag, SharedStep Controls.specialize source.1 {source.2} store bag ∧
      trees store bag = {Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.idx 0, Controls.seven} := by
  apply sharedStep_complete ((ruleInputCheck_iff _).mp InputControls.compound_output_does_not_restrict_rule_input)
    source_canonical
  · intro r member
    have same : r = source.2 := by simpa using member
    subst r
    exact source_valid
  · simpa [trees, source_tree] using Controls.specialize_step

def allRights : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Rights Unit := fun _ _ => true
def noRights : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Rights Unit := fun _ _ => false

theorem specialize_formed : (contextualCalculus (V := Nat) (fun _ : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Nat => ())).Formed
    allRights .data Controls.specialize := by
  constructor <;> intro pattern member assignment term evidence <;> rfl

theorem specialize_requires_send :
    ¬(contextualCalculus (V := Nat) (fun _ : Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term Nat => ())).Formed
      noRights .data Controls.specialize := by
  intro formed
  have allowed := formed.produce (Controls.hole 0 1 [Controls.seven]) (by simp [Controls.specialize])
    Controls.assignment Controls.seven Controls.compound_application
  simp [noRights] at allowed

end CalculusControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualPatterns
