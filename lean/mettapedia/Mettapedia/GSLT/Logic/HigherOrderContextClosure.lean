import Mettapedia.GSLT.Logic.HigherOrderBisimulation
import Mettapedia.Logic.DerivationClosure

/-!
# Finite contextual evidence for higher-order bisimulation

Interface-indexed state pairs are judgments of the existing finite derivation
calculus. Progression still uses the original transitions, observations and
process-bearing labels. Packing the dependent family into judgments does not
introduce another operational semantics.

Contextual closure and checked coinductive certificates are sound after the
local constructor-replay obligation is proved. That obligation is not supplied
by positivity, a signature declaration, or a presumed congruence theorem.
-/

set_option autoImplicit false

open Mettapedia.Logic

namespace Mettapedia.GSLT.HigherOrderBisimulation


universe uInterface uState uSkeleton uAtom

variable {Interface : Type uInterface} {State : Interface → Type uState}
  {vocabulary : Vocabulary.{uInterface, uSkeleton} Interface}

/-- A pair retains the interface shared by its two states. -/
abbrev Judgment (State : Interface → Type uState) :=
  (interface : Interface) × (State interface × State interface)

def pack (relation : RelationFamily State) : Judgment State → Prop :=
  fun pair => relation pair.1 pair.2.1 pair.2.2

def unpack (candidate : Judgment State → Prop) : RelationFamily State :=
  fun interface left right => candidate ⟨interface, left, right⟩

@[simp] theorem unpack_pack (relation : RelationFamily State) :
    unpack (pack relation) = relation := rfl

@[simp] theorem pack_unpack (candidate : Judgment State → Prop) :
    pack (unpack candidate) = candidate := rfl

namespace System

variable (system : System vocabulary State)

/-- The same progression operator evaluated at packed state-pair judgments. -/
def progressOnJudgments : (Judgment State → Prop) →o (Judgment State → Prop) where
  toFun candidate := pack (system.progress (unpack candidate))
  monotone' := by
    intro first second included pair related
    exact system.progress_mono (fun interface left right => included ⟨interface, left, right⟩)
      pair.1 pair.2.1 pair.2.2 related

/-- The two fixed points agree by coinduction in both directions. -/
theorem gfp_iff_bisimilar (pair : Judgment State) :
    system.progressOnJudgments.gfp pair ↔ system.Bisimilar pair.1 pair.2.1 pair.2.2 := by
  constructor
  · intro related
    apply system.coinduction (relation := unpack system.progressOnJudgments.gfp) ?_
      pair.1 pair.2.1 pair.2.2 related
    intro interface left right pairRelated
    change system.progressOnJudgments system.progressOnJudgments.gfp
      ⟨interface, left, right⟩
    rw [system.progressOnJudgments.map_gfp]
    exact pairRelated
  · intro related
    apply system.progressOnJudgments.le_gfp (a := pack system.Bisimilar) ?_ pair related
    intro judgment pairRelated
    exact system.bisimilar_unfold.mp pairRelated

/-- The generic finite closure is a congruence only under actual local replay. -/
theorem finite_closure_bisimilar (rules : List (Judgment State) → Judgment State → Prop)
    (localRules : FinitaryClosure.LocallyRespectful rules system.progressOnJudgments)
    {pair : Judgment State}
    (derivation : FinitaryClosure.close rules (pack system.Bisimilar) pair) :
    system.Bisimilar pair.1 pair.2.1 pair.2.2 := by
  have included : pack system.Bisimilar ≤ system.progressOnJudgments.gfp :=
    fun judgment related => (system.gfp_iff_bisimilar judgment).mpr related
  exact (system.gfp_iff_bisimilar pair).mp
    (FinitaryClosure.close_gfp_le rules system.progressOnJudgments localRules pair
      (FinitaryClosure.close_mono rules included pair derivation))

/-- Retained, independently replayed finite evidence can discharge an up-to
method against the actual higher-order transition system. -/
theorem certificate_bisimilar (rules : List (Judgment State) → Judgment State → Prop)
    (localRules : FinitaryClosure.LocallyRespectful rules system.progressOnJudgments)
    {seeds : Judgment State → Prop}
    (advances : seeds ≤ system.progressOnJudgments (FinitaryClosure.close rules seeds))
    (witnesses : RuleWitness (FinitaryClosure.seededRules rules seeds))
    (certificate : Derivation (Judgment State) witnesses.W)
    (accepted : certificate.valid witnesses = true) :
    system.Bisimilar certificate.concl.1 certificate.concl.2.1 certificate.concl.2.2 :=
  (system.gfp_iff_bisimilar certificate.concl).mp
    (FinitaryClosure.certificate_sound_up_to rules system.progressOnJudgments
      localRules advances witnesses certificate accepted)

end System

#print axioms System.gfp_iff_bisimilar
#print axioms System.finite_closure_bisimilar
#print axioms System.certificate_bisimilar

end Mettapedia.GSLT.HigherOrderBisimulation
