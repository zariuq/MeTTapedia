import Mettapedia.AutoBooks.Codex.Henkin1950.CanonicalAssignments
import Mettapedia.AutoBooks.Codex.Henkin1950.CompleteTheories

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Canonical truth-by-membership layer for Henkin pp. 86-87.

Henkin evaluates an open formula under a variable assignment by replacing its
free variables with chosen closed representatives and then checking membership
of the resulting closed formula in the complete consistent theory. This file
packages that paper-facing relation and proves the quantifier clauses that are
already available before representative-independence is fully established.
-/

/-- Closed-formula derivability specializes universal sentences to closed
instances. -/
theorem provable_specialize_closed
    {T : ClosedTheorySet} {σ : HTy} {φ : Formula [σ]} {t : ClosedTerm σ}
    (hAll : SetProvable T (.all φ : Sentence)) :
    SetProvable T (instantiate t φ) := by
  rcases hAll with ⟨Δ, hΔ, hAll⟩
  exact ⟨Δ, hΔ, .allE t hAll⟩

/-- Closed-formula derivability introduces existential sentences from closed
instances. -/
theorem provable_exists_closed
    {T : ClosedTheorySet} {σ : HTy} {φ : Formula [σ]} {t : ClosedTerm σ}
    (hInst : SetProvable T (instantiate t φ)) :
    SetProvable T (.ex φ : Sentence) := by
  rcases hInst with ⟨Δ, hΔ, hInst⟩
  exact ⟨Δ, hΔ, .exI t hInst⟩

/-- Close the body of a one-variable-open formula by replacing only the outer
context variables using the chosen representatives of `ν`. The bound variable
remains free. -/
noncomputable def closeBody
    (ν : ClassAssignment T Γ) (φ : Formula (σ :: Γ)) : Formula [σ] :=
  subst
    (Subst.lift (Base := Atom) (Const := Primitive)
      (ClassAssignment.chooseRepresentatives ν))
    φ

@[simp] theorem closeFormula_all
    (ν : ClassAssignment T Γ) (φ : Formula (σ :: Γ)) :
    ClassAssignment.closeFormula ν (.all φ) =
      (.all (closeBody ν φ) : Sentence) :=
  rfl

@[simp] theorem closeFormula_ex
    (ν : ClassAssignment T Γ) (φ : Formula (σ :: Γ)) :
    ClassAssignment.closeFormula ν (.ex φ) =
      (.ex (closeBody ν φ) : Sentence) :=
  rfl

/-- Closing under an extended class assignment is the same concrete closed-term
substitution as closing with the extended chosen representative assignment. -/
@[simp] theorem classAssignment_closeTerm_extend
    (ν : ClassAssignment T Γ) (c : TermClass T σ) (φ : Term (σ :: Γ) τ) :
    ClassAssignment.closeTerm (ClassAssignment.extend ν c) φ =
      Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm
        (RepresentativeAssignment.extend
          (ClassAssignment.chooseRepresentatives ν)
          (ClassAssignment.representative c))
        φ := by
  unfold ClassAssignment.closeTerm
  unfold Mettapedia.AutoBooks.Codex.Henkin1950.closeTerm
  apply subst_ext
  intro α v
  simp

/-- Paper-facing canonical truth relation: an open formula is true under a
quotient-valued class assignment when its closed representative-substitution
belongs to the theory. -/
def Holds (T : ClosedTheorySet) (ν : ClassAssignment T Γ) (φ : Formula Γ) : Prop :=
  ClassAssignment.closeFormula ν φ ∈ T

/-- Universal canonical truth specializes to every closed instance of the
closed body. -/
theorem holds_all_specialize
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : ClassAssignment T Γ)
    {σ : HTy} {φ : Formula (σ :: Γ)}
    (hAll : Holds T ν (.all φ)) (t : ClosedTerm σ) :
    instantiate t (closeBody ν φ) ∈ T := by
  have hAllMem : (.all (closeBody ν φ) : Sentence) ∈ T := by
    simpa [Holds] using hAll
  exact hT.closed <|
    provable_specialize_closed
      (T := T)
      (φ := closeBody ν φ)
      (t := t)
      (Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
        (Const := Primitive) hAllMem)

/-- In particular, a universally true formula holds under every extension by a
quotient class, using its chosen representative. -/
theorem holds_all_specialize_representative
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : ClassAssignment T Γ)
    {σ : HTy} {φ : Formula (σ :: Γ)}
    (hAll : Holds T ν (.all φ)) (c : TermClass T σ) :
    Holds T (ClassAssignment.extend ν c) φ := by
  have hInst :
      instantiate (ClassAssignment.representative c) (closeBody ν φ) ∈ T :=
    holds_all_specialize hT ν hAll (ClassAssignment.representative c)
  have hClosed : ClassAssignment.closeTerm (ClassAssignment.extend ν c) φ ∈ T := by
    simpa [closeBody] using hInst
  simpa [Holds, ClassAssignment.closeFormula] using hClosed

/-- A closed witness instance yields existential canonical truth. -/
theorem holds_ex_of_closed_witness
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : ClassAssignment T Γ)
    {σ : HTy} {φ : Formula (σ :: Γ)}
    {t : ClosedTerm σ}
    (ht : instantiate t (closeBody ν φ) ∈ T) :
    Holds T ν (.ex φ) := by
  have hExProv : SetProvable T (.ex (closeBody ν φ) : Sentence) :=
    provable_exists_closed
      (T := T)
      (φ := closeBody ν φ)
      (t := t)
      (Mettapedia.Logic.HOL.ClosedTheorySet.provable_of_mem
        (Const := Primitive) ht)
  have hExMem : (.ex (closeBody ν φ) : Sentence) ∈ T := hT.closed hExProv
  simpa [Holds] using hExMem

/-- In particular, truth under an extended class assignment yields existential
truth of the original open formula. -/
theorem holds_ex_of_class_witness
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (ν : ClassAssignment T Γ)
    {σ : HTy} {φ : Formula (σ :: Γ)}
    (c : TermClass T σ)
    (hc : Holds T (ClassAssignment.extend ν c) φ) :
    Holds T ν (.ex φ) := by
  have hClosed : ClassAssignment.closeTerm (ClassAssignment.extend ν c) φ ∈ T := by
    simpa [Holds, ClassAssignment.closeFormula] using hc
  have hInst :
      instantiate (ClassAssignment.representative c) (closeBody ν φ) ∈ T := by
    simpa [closeBody] using hClosed
  exact holds_ex_of_closed_witness hT ν hInst

/-- Henkin's witness property gives the forward existential clause for the
canonical truth relation. -/
theorem holds_ex_iff_exists_closed_witness
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (ν : ClassAssignment T Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    Holds T ν (.ex φ) ↔ ∃ t : ClosedTerm σ, instantiate t (closeBody ν φ) ∈ T := by
  constructor
  · intro hExHolds
    have hExMem : (.ex (closeBody ν φ) : Sentence) ∈ T := by
      simpa [Holds] using hExHolds
    rcases hEx (φ := closeBody ν φ) hExMem with ⟨t, ht⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact holds_ex_of_closed_witness hT ν ht

/-- Henkin's counterexample property gives the universal clause for the
canonical truth relation, still phrased over closed-term instances rather than
quotient classes. -/
theorem holds_all_iff_forall_closed_instances
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hAll : UniversalCounterexampleClosed T)
    (ν : ClassAssignment T Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    Holds T ν (.all φ) ↔
      ∀ t : ClosedTerm σ, instantiate t (closeBody ν φ) ∈ T := by
  constructor
  · intro hAllHolds t
    exact holds_all_specialize hT ν hAllHolds t
  · intro hInstances
    by_contra hNotAll
    have hAllNotMem : (.all (closeBody ν φ) : Sentence) ∉ T := by
      simpa [Holds] using hNotAll
    rcases hAll (φ := closeBody ν φ) hAllNotMem with ⟨t, ht⟩
    exact ht (hInstances t)

end Mettapedia.AutoBooks.Codex.Henkin1950
