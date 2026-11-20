import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteControls
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedCongruence

/-!
# The bag presentation inside the tree's corrected semantics modulo the bag laws

The step is the one-match step of the three-rule `program` at the one frame of structural substitution
on patterns, with the five choices stated in `FiniteComm` (a bag store, one match, guards asked after the
firing's own tells, a fixed set of rules beside the store, one store of knowledge). `FiniteHosting`
relates it to `BagComm`, the manuscript's COMM on a bag of parallel parts. Here `BagComm` is related to the
tree's own relational semantics of the manuscript modulo the bag laws, `Corrected.BagCommStep`: COMM, PAR
and EQUIV with alpha-equivalence and the bag laws as the equivalence, without REFL.

* `bagComm_bagCommStep`: from a process whose parallel skeleton is binary (`components P = parts P`: the
  tree's flattening of parallel bags agrees with the binary one), every `BagComm` step of its parts is a
  step of `Corrected.BagCommStep Corrected.conventional`, to a process whose parts are the target bag.
* `communication_corrected`: hence every communication of the finite program, at a state that represents
  the parts of such a process, at a ground-unifiable bag, is a step of the tree's corrected semantics
  modulo the bag laws.
* `example_corrected`: the manuscript's example, `for((0) <- @0)0 | for(y <- @0)y`, is such a process, and
  its COMM is such a step.

What is not shown: the converse, that every `Corrected.BagCommStep` from such a process is a `BagComm` step
of its parts. Its equivalence compares closed forms, so the converse needs the dotted reducts of
alpha-equivalent redexes to be alpha-equivalent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor par pZero nQuote applyDot)
open MeTTaCalculus.Corrected (components components_par components_pZero components_pFor
  components_of_mem_components bagEq_iff BagEq BagCommStep conventional)
open Comm (Tm X E)

/-- The right-nested parallel composition of a list, ending in `0`. -/
def parList : List Pattern → Pattern
  | [] => pZero
  | p :: ps => par p (parList ps)

theorem parts_parList : ∀ (L : List Pattern), (∀ c ∈ L, parts c = [c]) → parts (parList L) = L
  | [], _ => parts_pZero
  | p :: ps, leaves => by
      rw [parList, parts_par, leaves p (by simp), parts_parList ps fun c member => leaves c (by simp [member])]
      rfl

theorem components_parList : ∀ (L : List Pattern), (∀ c ∈ L, components c = [c]) →
    components (parList L) = L
  | [], _ => components_pZero
  | p :: ps, leaves => by
      rw [parList, components_par, leaves p (by simp),
        components_parList ps fun c member => leaves c (by simp [member])]
      rfl

/-- **A source step of the bag presentation is a step of the tree's corrected semantics modulo the bag
laws.** From a process whose parallel skeleton is binary, every `BagComm` step of its parts is a step of
`Corrected.BagCommStep Corrected.conventional`, to a process whose parts are the target bag. -/
theorem bagComm_bagCommStep {P : Pattern} {M' : Multiset Pattern} (binary : components P = parts P)
    (step : BagComm (parts P : Multiset Pattern) M') :
    ∃ P' : Pattern, BagCommStep conventional P P' ∧ (parts P' : Multiset Pattern) = M' := by
  generalize source : (parts P : Multiset Pattern) = M at step
  obtain ⟨t, u, x, A, B, bs, rest, gp, convention, -⟩ := step
  have restList : ((rest.toList : List Pattern) : Multiset Pattern) = rest := Multiset.coe_toList rest
  have bagList : (parts P : Multiset Pattern) = ((pFor t x A :: pFor u x B :: rest.toList : List Pattern) :
      Multiset Pattern) := by
    rw [source]
    conv_lhs => rw [← restList]
    rfl
  have inParts : ∀ c ∈ rest.toList, c ∈ parts P := by
    intro c member
    have inside : c ∈ (parts P : Multiset Pattern) := by
      rw [bagList]
      exact Multiset.mem_coe.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
    exact Multiset.mem_coe.mp inside
  have leavesComponents : ∀ c ∈ rest.toList, components c = [c] := fun c member =>
    components_of_mem_components P c (binary ▸ inParts c member)
  have leavesParts : ∀ c ∈ rest.toList, parts c = [c] := fun c member =>
    parts_of_mem_parts P c (inParts c member)
  let before : Pattern := par (par (pFor t x A) (pFor u x B)) (parList rest.toList)
  let after : Pattern := par (par (applyDot bs A) (applyDot bs B)) (parList rest.toList)
  have similar : BagEq P before := by
    rw [bagEq_iff]
    apply List.Perm.map
    have componentsBefore : components before = pFor t x A :: pFor u x B :: rest.toList := by
      show components (par (par (pFor t x A) (pFor u x B)) (parList rest.toList)) = _
      rw [components_par, components_par, components_pFor, components_pFor,
        components_parList _ leavesComponents]
      rfl
    rw [componentsBefore, binary]
    exact Multiset.coe_eq_coe.mp bagList
  have fires : BagCommStep conventional before after :=
    .parallel (parList rest.toList)
      (.comm t u x A B bs (Comm.principal_of_groundPrincipal gp) convention)
  refine ⟨after, .congruence similar fires (BagEq.refl after), ?_⟩
  show (parts (par (par (applyDot bs A) (applyDot bs B)) (parList rest.toList)) : Multiset Pattern) = _
  rw [parts_par, parts_par, parts_parList _ leavesParts, ← Multiset.coe_add, ← Multiset.coe_add, restList]

/-- **Every communication of the finite program is a step of the tree's corrected semantics modulo the bag
laws**, at a state that represents the parts of a process whose parallel skeleton is binary, when the bag
is ground-unifiable. -/
theorem communication_corrected {s s' : State Tm ℕ} {P : Pattern}
    (represented : Represents s (parts P : Multiset Pattern)) (binary : components P = parts P)
    (grounded : GroundUnifiable (parts P : Multiset Pattern)) (fires : Communicates s s') :
    ∃ P' : Pattern, BagCommStep conventional P P' ∧ Represents s' (parts P' : Multiset Pattern) := by
  obtain ⟨comp, represented⟩ := represented
  obtain ⟨M', step, represented'⟩ := communication_sound represented grounded fires
  obtain ⟨P', corrected, same⟩ := bagComm_bagCommStep binary step
  exact ⟨P', corrected, same ▸ represented'⟩

/-- **The manuscript's example, in the tree's corrected semantics modulo the bag laws.** Its parallel
skeleton is binary, and its COMM is a step of `Corrected.BagCommStep conventional` to a process whose parts
are those of the manuscript's reduct. -/
theorem example_corrected : components Comm.Controls.source = parts Comm.Controls.source ∧
    ∃ P' : Pattern, BagCommStep conventional Comm.Controls.source P' ∧
      (parts P' : Multiset Pattern) = (parts Comm.Controls.reduct : Multiset Pattern) := by
  have binary : components Comm.Controls.source = parts Comm.Controls.source := by decide +kernel
  exact ⟨binary, bagComm_bagCommStep binary Controls.example_bagComm⟩

#print axioms parts_parList
#print axioms components_parList
#print axioms bagComm_bagCommStep
#print axioms communication_corrected
#print axioms example_corrected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.FiniteProgram
