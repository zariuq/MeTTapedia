import Mettapedia.GSLT.Causality.DoCalculus.IdentifyDeriv
import Mettapedia.GSLT.Causality.DoCalculus.Derivation

/-!
# The reduced outcome: the missing checker step behind `identify`'s exchange

Rule 2 and rule 3 of the checker (`Deriv.rule2`, `Deriv.rule3`) ask `FiniteDSeparation.check` for
the outcome set as written, and the checker refuses whenever the outcome meets the conditioning
set (it requires them disjoint). The mass expressions at both ends of either rule only read the
outcome through its union with the intervention and conditioning sets. So the outcome can be
reduced by those sets before the check, and the ends are unchanged.

* **The reduced rules** (`rule2Reduced`, `rule3Reduced`): derived steps, built from `Deriv.rule2`
  and `Deriv.rule3` by `Deriv.rewriteEq`, whose checker runs on the outcome minus the intervention
  and conditioning sets.
* **Grok's stuck instance closes** (`gap_identify_is_deriv`). On `A → B` with outcome `A`,
  intervention `B` and conditioning `A`, the parent test of `identify` answers while the checker of
  `Deriv.rule2` refuses (`gap_parents_accept_rule2_refuses`). The reduced outcome is empty, the
  reduced checker accepts, and the reduced rule 2 joins the query to `identify`'s do-free answer,
  with Grok's `deriv_gDenote` giving the semantic equation under the derivation's positivity.
  The reduced rule 3 likewise accepts the deletion the plain checker refuses
  (`gap_reduced_rule3_accepts`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus.IdentifyDerivation

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
open Mettapedia.GSLT.Causality.DoCalculus

variable {V : Type} [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V) [DecidableRel graph.edges]

omit [Fintype V] in
theorem union_reduced (intervention outcome exchanged conditioning : Finset V) :
    intervention ∪ (outcome \ (intervention ∪ conditioning)) ∪ exchanged ∪ conditioning =
      intervention ∪ outcome ∪ exchanged ∪ conditioning := by
  ext v
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

omit [Fintype V] in
theorem union_reduced' (intervention outcome conditioning : Finset V) :
    intervention ∪ (outcome \ (intervention ∪ conditioning)) ∪ conditioning =
      intervention ∪ outcome ∪ conditioning := by
  ext v
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- **Rule 2 with the reduced outcome**: the checker runs on the outcome minus the intervention and
conditioning sets; the ends are those of `Deriv.rule2` for the full outcome. -/
def rule2Reduced (intervention outcome exchanged conditioning : Finset V)
    (hcheck : FiniteDSeparation.check (gout graph intervention exchanged)
      (rule2Profile (outcome \ (intervention ∪ conditioning)) exchanged
        (intervention ∪ conditioning)) = true) :
    Deriv graph
      (.cond (intervention ∪ exchanged)
        (intervention ∪ outcome ∪ exchanged ∪ conditioning)
        (intervention ∪ exchanged ∪ conditioning))
      (.cond intervention
        (intervention ∪ outcome ∪ exchanged ∪ conditioning)
        (intervention ∪ exchanged ∪ conditioning)) :=
  .rewriteEq (by rw [union_reduced]) (by rw [union_reduced])
    (.rule2 intervention (outcome \ (intervention ∪ conditioning)) exchanged conditioning hcheck)

/-- **Rule 3 with the reduced outcome.** -/
def rule3Reduced (intervention outcome deleted conditioning : Finset V)
    (hcheck : FiniteDSeparation.check (rule3Graph graph intervention deleted conditioning)
      (rule3Profile (outcome \ (intervention ∪ conditioning)) deleted
        (intervention ∪ conditioning)) = true) :
    Deriv graph
      (.cond (intervention ∪ deleted)
        (intervention ∪ outcome ∪ conditioning)
        (intervention ∪ conditioning))
      (.cond intervention
        (intervention ∪ outcome ∪ conditioning)
        (intervention ∪ conditioning)) :=
  .rewriteEq (by rw [union_reduced']) (by rw [union_reduced'])
    (.rule3 intervention (outcome \ (intervention ∪ conditioning)) deleted conditioning hcheck)

/-! ## Grok's stuck instance -/

/-- **The reduced checker accepts the exchange on `A → B`**, where the plain one refuses. -/
theorem gap_reduced_rule2_accepts :
    FiniteDSeparation.check (gout gapGraph (∅ : Finset GapV) gapB)
        (rule2Profile (gapA \ ((∅ : Finset GapV) ∪ gapA)) gapB ((∅ : Finset GapV) ∪ gapA)) = true ∧
      FiniteDSeparation.check (gout gapGraph (∅ : Finset GapV) gapB)
        (rule2Profile gapA gapB ((∅ : Finset GapV) ∪ gapA)) = false := by
  decide

/-- **The reduced checker accepts the deletion on `A → B`**, where the plain one refuses. -/
theorem gap_reduced_rule3_accepts :
    FiniteDSeparation.check (rule3Graph gapGraph (∅ : Finset GapV) gapB gapA)
        (rule3Profile (gapA \ ((∅ : Finset GapV) ∪ gapA)) gapB ((∅ : Finset GapV) ∪ gapA)) = true ∧
      FiniteDSeparation.check (rule3Graph gapGraph (∅ : Finset GapV) gapB gapA)
        (rule3Profile gapA gapB ((∅ : Finset GapV) ∪ gapA)) = false := by
  decide

/-- The query of the stuck instance, in the form of the open statement. -/
def gapQuery : MassExpr GapV := .cond gapB (gapB ∪ gapA ∪ gapA) (gapB ∪ gapA)

/-- **The derivation of the stuck instance**: the reduced rule 2, from the query to `identify`'s
do-free answer. -/
def gapDeriv : Deriv gapGraph gapQuery (exchangeResult gapA gapB gapA) :=
  .rewriteEq
    (condSetEq (by decide) (by decide) (by decide))
    (by
      simp only [exchangeResult]
      exact condSetEq (by decide) (by decide) (by decide))
    (rule2Reduced gapGraph ∅ gapA gapB gapA gap_reduced_rule2_accepts.1)

variable {β : Type}
variable [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
variable [MeasurableSingletonClass β] [StandardBorelSpace β]
variable [StandardBorelSpace (GapV → β)]

/-- **Grok's stuck instance of "every do-free answer of `identify` ends a `Deriv`" closes**: at
fuel 1, `identify` answers the do-free exchange, and `gapDeriv` joins the query to that answer, so
the two have one `gDenote` wherever the derivation's positivity holds. -/
theorem gap_identify_is_deriv (hAcyclic : gapGraph.IsAcyclic) :
    identify gapGraph 1 [GapV.a, GapV.b] (∅ : Finset GapV) gapA gapB gapA =
        .doFree (exchangeResult gapA gapB gapA) ∧
      ∀ (cpt : (network (β := β) gapGraph hAcyclic).DiscreteCPT) (anchor : GapV → β),
        Positive gapGraph hAcyclic gapDeriv cpt anchor →
          gDenote gapGraph hAcyclic cpt anchor gapQuery =
            gDenote gapGraph hAcyclic cpt anchor (exchangeResult gapA gapB gapA) :=
  ⟨gap_identify_exchanges, fun cpt anchor hpos =>
    deriv_gDenote gapGraph hAcyclic gapDeriv cpt anchor hpos⟩

#print axioms union_reduced
#print axioms union_reduced'
#print axioms gap_reduced_rule2_accepts
#print axioms gap_reduced_rule3_accepts
#print axioms gap_identify_is_deriv

end Mettapedia.GSLT.Causality.DoCalculus.IdentifyDerivation
