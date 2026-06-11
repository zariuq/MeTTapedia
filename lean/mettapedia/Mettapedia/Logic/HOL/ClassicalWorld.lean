import Mettapedia.Logic.HOL.ClassicalExcludedMiddle
import Mettapedia.Logic.HOL.WitnessedWorld
import Mettapedia.Logic.HOL.WorldEquality

/-!
# The classical canonical world

Assembling everything: a consistent theory `witnessLimit T enum ∪ EMSchema`
(parameter-free base `T`, surjective body enumeration) extends — via the Lindenbaum
maximal extension — to a full `ClosedTheorySet.World` over `WithParams Const`, i.e. a
**complete, prime, ∃-witnessed, ∀-counterexampled** theory.  This is the canonical
classical world the 2-valued term model is built over.

* prime/complete/closed from `maximal_*`;
* `exists_witness` from the witness axioms in `witnessLimit`;
* `all_counterexample` from completeness + closed EM + `provable_all_of_emAll_dne`
  (the `emdne_all` route) + the ∃-witness of `¬φ`.
-/

namespace Mettapedia.Logic.HOL

open Mettapedia.Logic.HOL.WithParams ClosedTheorySet

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- **The classical canonical world.**  A consistent classical theory
`witnessLimit T enum ∪ EMSchema` (parameter-free base, surjective body enumeration)
yields a full `World` containing `T` and the excluded-middle schema. -/
theorem exists_classical_world {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const) (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const)
      (witnessLimit T enum ∪ EMSchema Const)) :
    ∃ W : ClosedTheorySet.World (WithParams Const),
      (∀ ψ ∈ T, ψ ∈ W.carrier) ∧ (∀ ψ ∈ EMSchema Const, ψ ∈ W.carrier) ∧
      (∀ χ : ClosedFormula (WithParams Const),
        χ ∈ W.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ W.carrier) := by
  classical
  obtain ⟨M, hHM, hMcons, hMmax⟩ :=
    exists_maximal_consistent_extension (Const := WithParams Const) hCons
  have hClosed : DeductivelyClosed (Const := WithParams Const) M :=
    maximal_deductivelyClosed hMcons hMmax
  have hComplete : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M :=
    fun χ => maximal_complete hMmax hClosed χ
  -- membership transports
  have hWLsub : ∀ {ψ}, ψ ∈ witnessLimit T enum → ψ ∈ M :=
    fun hψ => hHM (Set.mem_union_left _ hψ)
  have hEMsub : ∀ ψ ∈ EMSchema Const, ψ ∈ M :=
    fun ψ hψ => hHM (Set.mem_union_right _ hψ)
  -- consistency contradiction
  have hConsViol : ∀ {χ : ClosedFormula (WithParams Const)},
      χ ∈ M → (.not χ : ClosedFormula (WithParams Const)) ∈ M → False :=
    fun hχ hnχ => hMcons (provable_bot_of_not (provable_of_mem hnχ) (provable_of_mem hχ))
  -- existence property (reused for `φ` and `¬φ`)
  have hWit : ∀ {σ' : Ty Base} {ψ : Formula (WithParams Const) [σ']},
      (.ex ψ : ClosedFormula (WithParams Const)) ∈ M →
        ∃ t : ClosedTerm (WithParams Const) σ', instantiate (Base := Base) t ψ ∈ M := by
    intro σ' ψ hex
    obtain ⟨k, hax⟩ := exists_witnessAxiom T enum ⟨σ', ψ⟩ (henum ⟨σ', ψ⟩)
    refine ⟨.const (param σ' k), ?_⟩
    exact hClosed (provable_mp (provable_of_mem (hWLsub hax)) (provable_of_mem hex))
  refine ⟨{ carrier := M, closed := hClosed, consistent := hMcons,
            prime_or := fun h => maximal_prime_or hClosed hComplete h,
            exists_witness := fun hex => hWit hex,
            all_counterexample := ?_ },
          fun ψ hψ => hWLsub (subset_witnessLimit T enum hψ), hEMsub, hComplete⟩
  -- all_counterexample
  intro σ' ψ hnotall
  have hnall : (.not (.all ψ) : ClosedFormula (WithParams Const)) ∈ M :=
    (hComplete (.all ψ)).resolve_left hnotall
  have hemc : (Term.or (.ex (.not ψ)) (.not (.ex (.not ψ))) : ClosedFormula (WithParams Const)) ∈ M :=
    hEMsub _ (emClosed_mem (.ex (.not ψ)))
  rcases maximal_prime_or hClosed hComplete hemc with hex | hnex
  · obtain ⟨t, ht⟩ := hWit hex
    exact ⟨t, fun hin => hConsViol hin ht⟩
  · exfalso
    have hdne : (.all (.not (.not ψ)) : ClosedFormula (WithParams Const)) ∈ M :=
      hClosed (provable_allNotNot_of_notEx (provable_of_mem hnex))
    have hemall : (.all (Term.or ψ (.not ψ)) : ClosedFormula (WithParams Const)) ∈ M :=
      hEMsub _ (emAll_mem ψ)
    have hallψ : (.all ψ : ClosedFormula (WithParams Const)) ∈ M :=
      hClosed (provable_all_of_emAll_dne (provable_of_mem hemall) (provable_of_mem hdne))
    exact hConsViol hallψ hnall

end Mettapedia.Logic.HOL
