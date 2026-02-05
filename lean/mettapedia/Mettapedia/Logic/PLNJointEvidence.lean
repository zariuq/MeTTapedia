import Mettapedia.Logic.CompletePLN
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNWorldModel

/-!
# PLN Joint Evidence Semantics (Dirichlet over Worlds)

This module prototypes the **theoretically correct** way to "pass evidence around" for PLN:

*Evidence is not a per-link Beta posterior.*  Instead, the exact conjugate-prior evidence for a
finite collection of propositions is a **Dirichlet posterior over complete worlds**.

Concretely, for `n` binary propositions there are `2^n` complete worlds.  A Dirichlet posterior is
parameterized by nonnegative "counts" `α : Fin (2^n) → ℝ≥0∞`.

From this joint evidence, we can derive (exactly, by marginalization):
- evidence for a proposition `A` (a Beta posterior for `P(A)`)
- evidence for a link `A ⟹ B` (a Beta posterior for `P(B|A)`)

This avoids heuristic confidence/weight propagation rules (e.g. `min`) entirely:
derived links get their evidence from the *same underlying joint evidence*.

This file is intentionally small: it provides the core extraction operations and the key
"revision commutes with extraction" lemmas.  It is a good substrate for a complete PLN proof
calculus whose judgments carry joint evidence.
-/

namespace Mettapedia.Logic.PLNJointEvidence

open scoped ENNReal

open Mettapedia.Logic.CompletePLN
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel

/-! ## Joint evidence over `n` binary propositions -/

/-- Joint (Dirichlet) evidence over `n` binary propositions:
nonnegative "counts" for each of the `2^n` complete worlds. -/
abbrev JointEvidence (n : ℕ) : Type := Fin (2 ^ n) → ℝ≥0∞

namespace JointEvidence

variable {n : ℕ}

/-! ### Revision (independent evidence addition)

`JointEvidence n` is a function type, so it inherits the standard pointwise additive structure.
Revision is `+` (adding Dirichlet pseudo-counts worldwise). -/

/-! ### Generic counting over worlds -/

/-- Total evidence mass (Dirichlet total concentration). -/
noncomputable def total (E : JointEvidence n) : ℝ≥0∞ :=
  Finset.univ.sum E

/-- Count of worlds satisfying a Boolean predicate. -/
noncomputable def countWorld (E : JointEvidence n) (P : Fin (2 ^ n) → Bool) : ℝ≥0∞ :=
  Finset.univ.sum fun w => if P w then E w else 0

theorem countWorld_add (E₁ E₂ : JointEvidence n) (P : Fin (2 ^ n) → Bool) :
    countWorld (n := n) (E := E₁ + E₂) P =
      countWorld (n := n) (E := E₁) P + countWorld (n := n) (E := E₂) P := by
  classical
  unfold countWorld
  -- Split the integrand and use `Finset.sum_add_distrib`.
  have h :
      (fun w => if P w then (E₁ w + E₂ w) else 0) =
        (fun w => (if P w then E₁ w else 0) + (if P w then E₂ w else 0)) := by
    funext w
    by_cases hP : P w <;> simp [hP]
  -- Rewrite with `h`, then distribute the sum.
  simp [h, Finset.sum_add_distrib]

/-! ### Derived Evidence for propositions and links -/

/-- Evidence for a proposition `A` (Beta parameters for `P(A)`), extracted from joint evidence. -/
noncomputable def propEvidence (E : JointEvidence n) (A : Fin n) : Evidence :=
  ⟨countWorld (n := n) (E := E) (fun w => worldToAssignment n w A),
   countWorld (n := n) (E := E) (fun w => !(worldToAssignment n w A))⟩

/-- Evidence for a link `A ⟹ B` (Beta parameters for `P(B|A)`), extracted from joint evidence. -/
noncomputable def linkEvidence (E : JointEvidence n) (A B : Fin n) : Evidence :=
  ⟨countWorld (n := n) (E := E) (fun w => worldToAssignment n w A && worldToAssignment n w B),
   countWorld (n := n) (E := E) (fun w => worldToAssignment n w A && !(worldToAssignment n w B))⟩

/-! ### World-model interface instance -/

instance instEvidenceType : EvidenceType (JointEvidence n) where

theorem propEvidence_add (E₁ E₂ : JointEvidence n) (A : Fin n) :
    propEvidence (n := n) (E := E₁ + E₂) A =
      propEvidence (n := n) (E := E₁) A + propEvidence (n := n) (E := E₂) A := by
  ext <;> simp [propEvidence, countWorld_add, Evidence.hplus_def]

theorem linkEvidence_add (E₁ E₂ : JointEvidence n) (A B : Fin n) :
    linkEvidence (n := n) (E := E₁ + E₂) A B =
      linkEvidence (n := n) (E := E₁) A B + linkEvidence (n := n) (E := E₂) A B := by
  ext <;> simp [linkEvidence, countWorld_add, Evidence.hplus_def]

noncomputable instance instWorldModel : WorldModel (JointEvidence n) (PLNQuery (Fin n)) where
  evidence E
    | .prop A => JointEvidence.propEvidence (n := n) (E := E) A
    | .link A B => JointEvidence.linkEvidence (n := n) (E := E) A B
  evidence_add E₁ E₂ q := by
    cases q with
    | prop A =>
        simpa using propEvidence_add (n := n) (E₁ := E₁) (E₂ := E₂) A
    | link A B =>
        simpa using linkEvidence_add (n := n) (E₁ := E₁) (E₂ := E₂) A B

/-! ### WTV/STV views (derived; not the core semantics) -/

/-- Proposition view as WTV, using the canonical Evidence→WTV map with prior κ. -/
noncomputable def propWTV (κ : ℝ≥0∞) (E : JointEvidence n) (A : Fin n) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (propEvidence (n := n) (E := E) A)

/-- Link view as WTV, using the canonical Evidence→WTV map with prior κ. -/
noncomputable def linkWTV (κ : ℝ≥0∞) (E : JointEvidence n) (A B : Fin n) : PLNWeightTV.WTV :=
  Evidence.toWTV κ (linkEvidence (n := n) (E := E) A B)

end JointEvidence

end Mettapedia.Logic.PLNJointEvidence
