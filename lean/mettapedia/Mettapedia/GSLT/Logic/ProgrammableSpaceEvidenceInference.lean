import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceConsumers
import Mettapedia.GSLT.Core.ProgrammableSpaceInference

/-!
# Retained derivations have exactly the persistent inference support

The source adapter uses the authored rule-list positions as rule instances and
the actual input-origin image as seeds. Soundness erases a retained derivation
to the inference closure. Completeness constructs finite typed premise tuples
inside `Nonempty`; it does not select a derivation for each provable fact.

Consequently every fair persistent run has exactly the fact support of the
retained derivations. This support theorem says nothing about how many proofs
were generated, which proof was generated first, or whether their origins are
disjoint.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence

attribute [local instance] Finite.membership

open Core.ProgrammableSpaceInference

universe u v w
variable {Atom : Type u} {Origin : Type v}

def Source.theory (source : Source Atom Origin) : Theory Atom source.RuleIndex where
  seeds := Set.range source.input
  rule := source.rule

private theorem finiteWitnesses : ∀ {count : Nat} (family : Fin count → Type w),
    (∀ index, Nonempty (family index)) → Nonempty (∀ index, family index)
  | 0, family, _ => ⟨fun index => Fin.elim0 index⟩
  | count + 1, family, inhabited => by
      obtain ⟨first⟩ := inhabited 0
      obtain ⟨rest⟩ := finiteWitnesses (fun index : Fin count => family index.succ)
        (fun index => inhabited index.succ)
      exact ⟨Fin.cases first rest⟩

theorem Derivation.inference {source : Source Atom Origin} {atom : Atom}
    (proof : Derivation source atom) : source.theory.Derivable atom := by
  apply proof.sound source.theory.Derivable
  · intro origin
    exact .seed ⟨origin, rfl⟩
  · intro index premises
    apply Theory.Derivable.rule index
    intro premise member
    obtain ⟨position, same⟩ := List.mem_iff_get.mp member
    exact same ▸ premises position

theorem retained_of_inference {source : Source Atom Origin} {atom : Atom}
    (proof : source.theory.Derivable atom) : Nonempty (Derivation source atom) := by
  induction proof with
  | seed present =>
      obtain ⟨origin, rfl⟩ := present
      exact ⟨.input origin⟩
  | rule index premises inductionHypothesis =>
      obtain ⟨retained⟩ := finiteWitnesses
        (fun position : source.PremiseIndex index => Derivation source (source.premise index position))
        (fun position => inductionHypothesis _ (List.get_mem _ position))
      exact ⟨.rule index retained⟩

theorem retained_iff_inference (source : Source Atom Origin) (atom : Atom) :
    Nonempty (Derivation source atom) ↔ source.theory.Derivable atom :=
  ⟨fun ⟨proof⟩ => proof.inference, retained_of_inference⟩

theorem factValue_image (source : Source Atom Origin) (atom : Atom) :
    (∃ value : Facts source, factValue source value = atom) ↔ source.theory.Derivable atom := by
  constructor
  · rintro ⟨value, same⟩
    induction value using Quotient.inductionOn with
    | h receipt => exact same ▸ receipt.2.inference
  · intro proof
    obtain ⟨retained⟩ := retained_of_inference proof
    exact ⟨observeFact source ⟨atom, retained⟩, rfl⟩

theorem fair_eventually_iff_retained (source : Source Atom Origin) (run : Run source.theory)
    (fair : run.RuleInstanceFair) (atom : Atom) :
    (∃ tick, atom ∈ run.facts tick) ↔ Nonempty (Derivation source atom) :=
  (run.eventually_iff_derivable fair atom).trans (retained_iff_inference source atom).symm

end Mettapedia.GSLT.ProgrammableSpaceEvidence
