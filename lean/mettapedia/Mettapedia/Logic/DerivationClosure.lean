import Mettapedia.Logic.Derivation
import Mathlib.Order.Closure
import Mathlib.Order.FixedPoints

/-!
# Finitary rule closure and respectful coinduction

The existing derivation syntax constructs the least predicate containing seeds
and closed under a rule predicate. No second proof tree is introduced.

A local progression lemma checks each rule against every structurally closed
candidate: premises must both belong to that candidate and progress into it.
Rule induction then proves respectfulness, greatest-fixed-point closure and
sound coinduction up to the constructed closure. The local lemma is a genuine
operational obligation, not an assumed congruence of the greatest fixed point.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryClosure

universe u

variable {J : Type u} (rules : List J → J → Prop)

/-- Seed judgments are nullary rule instances; all other rules remain unchanged. -/
def seededRules (seeds : J → Prop) (premises : List J) (conclusion : J) : Prop :=
  (premises = [] ∧ seeds conclusion) ∨ rules premises conclusion

/-- Actual finite derivability, reusing the canonical derivation syntax. -/
def close (seeds : J → Prop) : J → Prop := Derives (seededRules rules seeds)

/-- Structural closure is checked against the declared rules, not bisimilarity. -/
def Closed (candidate : J → Prop) : Prop :=
  ∀ premises conclusion, rules premises conclusion →
    (∀ premise ∈ premises, candidate premise) → candidate conclusion

theorem seeds_le_close (seeds : J → Prop) : seeds ≤ close rules seeds := by
  intro judgment seed
  exact Derives.node [] judgment (Or.inl ⟨rfl, seed⟩) (by simp)

theorem close_closed (seeds : J → Prop) : Closed rules (close rules seeds) := by
  intro premises conclusion rule derivations
  exact Derives.node premises conclusion (Or.inr rule) derivations

theorem close_mono : Monotone (close rules) := by
  intro first second included judgment derivation
  apply Derives.mono (rules := seededRules rules first) ?_ derivation
  intro premises conclusion rule
  rcases rule with ⟨empty, seed⟩ | rule
  · exact Or.inl ⟨empty, included conclusion seed⟩
  · exact Or.inr rule

/-- The universal property follows from derivation induction. -/
theorem close_le {seeds candidate : J → Prop} (included : seeds ≤ candidate)
    (closed : Closed rules candidate) : close rules seeds ≤ candidate := by
  apply Derives.least candidate
  intro premises conclusion rule children
  rcases rule with ⟨_, seed⟩ | rule
  · exact included conclusion seed
  · exact closed premises conclusion rule children

theorem close_idempotent (seeds : J → Prop) :
    close rules (close rules seeds) = close rules seeds := by
  apply le_antisymm
  · exact close_le rules le_rfl (close_closed rules seeds)
  · exact seeds_le_close rules (close rules seeds)

/-- A real closure operator with its leastness and idempotence proved. -/
def operator : ClosureOperator (J → Prop) where
  toFun := close rules
  monotone' := close_mono rules
  le_closure' := seeds_le_close rules
  idempotent' := close_idempotent rules

variable (progress : (J → Prop) →o (J → Prop))

/-- The rule-level condition: structural membership and progression of every
premise suffice for progression of the conclusion, at any closed candidate. -/
def LocallyRespectful : Prop :=
  ∀ candidate, Closed rules candidate →
    ∀ premises conclusion, rules premises conclusion →
      (∀ premise ∈ premises, candidate premise) →
      (∀ premise ∈ premises, progress candidate premise) → progress candidate conclusion

/-- Rule induction derives respectfulness; candidate membership is retained
alongside progression, so exposing a premise does not fabricate its membership. -/
theorem respectful (localRules : LocallyRespectful rules progress)
    {first second : J → Prop} (included : first ≤ second)
    (advances : first ≤ progress second) :
    close rules first ≤ progress (close rules second) := by
  have both : close rules first ≤ fun judgment =>
      close rules second judgment ∧ progress (close rules second) judgment := by
    intro judgment derivation
    apply Derives.least (rules := seededRules rules first)
      (fun conclusion => close rules second conclusion ∧
        progress (close rules second) conclusion) ?_ derivation
    intro premises conclusion rule children
    rcases rule with ⟨_, seed⟩ | rule
    · exact ⟨seeds_le_close rules second conclusion (included conclusion seed),
        progress.monotone (seeds_le_close rules second) conclusion (advances conclusion seed)⟩
    · exact ⟨close_closed rules second premises conclusion rule
        (fun premise member => (children premise member).1),
        localRules _ (close_closed rules second) premises conclusion rule
          (fun premise member => (children premise member).1)
          (fun premise member => (children premise member).2)⟩
  exact fun judgment derivation => (both judgment derivation).2

/-- The greatest fixed point is closed under the actual finite rule closure. -/
theorem close_gfp_le (localRules : LocallyRespectful rules progress) :
    close rules progress.gfp ≤ progress.gfp := by
  apply progress.le_gfp
  apply respectful rules progress localRules le_rfl
  rw [progress.map_gfp]

/-- Coinduction up to finite rule closure is sound only after the local
operational obligation has been discharged. -/
theorem coinduction_up_to (localRules : LocallyRespectful rules progress)
    {seeds : J → Prop} (advances : seeds ≤ progress (close rules seeds)) :
    close rules seeds ≤ progress.gfp := by
  apply progress.le_gfp
  have closed := respectful rules progress localRules (seeds_le_close rules seeds) advances
  simpa only [close_idempotent] using closed

/-- A retained certificate checked by the existing replay interface can be
consumed directly by the coinductive construction. -/
theorem certificate_sound_up_to (localRules : LocallyRespectful rules progress)
    {seeds : J → Prop} (advances : seeds ≤ progress (close rules seeds))
    (witnesses : RuleWitness (seededRules rules seeds))
    (certificate : Derivation J witnesses.W) (accepted : certificate.valid witnesses = true) :
    progress.gfp certificate.concl :=
  coinduction_up_to rules progress localRules advances certificate.concl
    (certificate.valid_sound witnesses accepted)

#print axioms respectful
#print axioms close_gfp_le
#print axioms coinduction_up_to
#print axioms certificate_sound_up_to

end Mettapedia.Logic.FinitaryClosure
