import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.MatrixBelief

/-!
# Gaussian belief-propagation cavities and scalar Schur elimination

Gaussian variable-to-factor messages are formed by multiplying every incoming
message except the one carried by the destination edge.  In natural
coordinates, multiplication is addition, so the exclusion is a
leave-one-edge cavity: subtract the destination message from the total belief.
This file proves that cavity extraction recovers exactly the other incoming
messages and records why unrestricted subtraction does not preserve proper
Gaussian information.

For a two-variable Gaussian factor, marginalizing the other variable produces
the scalar Schur complement.  The exact completion-of-squares identity below
derives both the outgoing precision and information parameter, proves
positivity under the strict determinant condition, and exposes its singular
and indefinite boundaries.

These results formalize the algebraic content of equations (7)--(8) in
Nabarro, van der Wilk, Davison, and Turner, *Learning in Deep Factor Graphs
with Gaussian Belief Propagation* (ICML 2024).  They do not assert convergence
of loopy Gaussian belief propagation or correctness of nonlinear
relinearization.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

universe uIndex uFactor

namespace GaussianInformation

variable {Index : Type uIndex}

/-! ## Leave-one-edge Gaussian cavities -/

/-- Remove one incoming natural-coordinate message from a total belief.

This operation is defined on the raw information carrier.  Its result is a
proper Gaussian belief only when the remaining precision is positive
definite. -/
noncomputable def cavity
    (belief incoming : GaussianInformation Index) :
    GaussianInformation Index where
  naturalParameter :=
    belief.naturalParameter - incoming.naturalParameter
  precision := belief.precision - incoming.precision

@[simp] theorem cavity_naturalParameter
    (belief incoming : GaussianInformation Index) :
    (cavity belief incoming).naturalParameter =
      belief.naturalParameter - incoming.naturalParameter :=
  rfl

@[simp] theorem cavity_precision
    (belief incoming : GaussianInformation Index) :
    (cavity belief incoming).precision =
      belief.precision - incoming.precision :=
  rfl

/-- Removing the return-edge message from its fusion with all other messages
recovers exactly those other messages. -/
@[simp] theorem cavity_add_left
    (incoming remaining : GaussianInformation Index) :
    cavity (incoming + remaining) incoming = remaining := by
  apply GaussianInformation.ext'
  · funext index
    simp [cavity]
  · ext row column
    simp [cavity]

/-- The recovery theorem is independent of which summand was written first. -/
@[simp] theorem cavity_add_right
    (remaining incoming : GaussianInformation Index) :
    cavity (remaining + incoming) incoming = remaining := by
  rw [add_comm]
  exact cavity_add_left incoming remaining

/-- The total natural-coordinate belief at a variable is the sum of its
incoming factor-to-variable messages. -/
noncomputable def variableBelief
    {Factor : Type uFactor}
    (neighbors : Finset Factor)
    (incoming : Factor → GaussianInformation Index) :
    GaussianInformation Index :=
  ∑ factor ∈ neighbors, incoming factor

/-- Efficient variable-to-factor messaging: form the total belief once, then
remove the message received from the destination factor. -/
noncomputable def variableToFactor
    {Factor : Type uFactor}
    (neighbors : Finset Factor)
    (incoming : Factor → GaussianInformation Index)
    (destination : Factor) :
    GaussianInformation Index :=
  cavity (variableBelief neighbors incoming) (incoming destination)

/-- When the destination is inserted into a set of other neighbors,
leave-one-edge cavity extraction returns precisely the sum over the others. -/
theorem variableToFactor_insert
    {Factor : Type uFactor} [DecidableEq Factor]
    (others : Finset Factor)
    (incoming : Factor → GaussianInformation Index)
    (destination : Factor)
    (hfresh : destination ∉ others) :
    variableToFactor (insert destination others) incoming destination =
      variableBelief others incoming := by
  rw [variableToFactor, variableBelief, Finset.sum_insert hfresh]
  exact cavity_add_left _ _

/-- Properness of the outgoing cavity follows from properness of the
remaining information, not from subtraction alone. -/
theorem variableToFactor_insert_proper
    {Factor : Type uFactor} [DecidableEq Factor]
    [Fintype Index]
    (others : Finset Factor)
    (incoming : Factor → GaussianInformation Index)
    (destination : Factor)
    (hfresh : destination ∉ others)
    (hremaining : (variableBelief others incoming).Proper) :
    (variableToFactor (insert destination others) incoming destination).Proper := by
  rw [variableToFactor_insert others incoming destination hfresh]
  exact hremaining

/-- Subtracting an arbitrary packet can create negative precision, so a raw
cavity is not automatically a proper Gaussian belief. -/
theorem cavity_not_automatically_proper :
    ¬(cavity
        (⟨fun _ : Unit => 0, fun _ _ => 1⟩ :
          GaussianInformation Unit)
        ⟨fun _ : Unit => 0, fun _ _ => 2⟩).Proper := by
  intro hproper
  have hdiag := hproper.diag_pos (i := ())
  norm_num [Proper, cavity] at hdiag

/-- Returning the destination message instead of removing it doubles that
edge's information.  This concrete fixture separates a cavity update from
naive reuse of the total belief. -/
theorem naive_return_edge_double_counts :
    let incoming : GaussianInformation Unit :=
      ⟨fun _ => 2, fun _ _ => 3⟩
    let remaining : GaussianInformation Unit :=
      ⟨fun _ => 5, fun _ _ => 7⟩
    cavity (incoming + remaining) incoming = remaining ∧
      incoming + remaining + incoming =
        ⟨fun _ => 9, fun _ _ => 13⟩ := by
  dsimp
  constructor
  · exact cavity_add_left _ _
  · apply GaussianInformation.ext' <;> funext <;> norm_num

end GaussianInformation

/-! ## Scalar two-variable Schur message -/

/-- Information-form energy of one symmetric two-variable Gaussian factor.
The precision matrix is `[[a,b],[b,c]]` and the natural parameter is
`(ηx,ηy)`. -/
noncomputable def scalarPairEnergy
    (a b c ηx ηy x y : ℝ) : ℝ :=
  (a * x ^ 2 + 2 * b * x * y + c * y ^ 2) / 2 - ηx * x - ηy * y

/-- Conditional optimizer of the eliminated coordinate for fixed `x`. -/
noncomputable def scalarConditionalOther
    (b c ηy x : ℝ) : ℝ :=
  (ηy - b * x) / c

/-- Precision of the outgoing scalar Gaussian message after eliminating the
other coordinate. -/
noncomputable def scalarSchurPrecision (a b c : ℝ) : ℝ :=
  a - b ^ 2 / c

/-- Natural parameter of the outgoing scalar Gaussian message after
eliminating the other coordinate. -/
noncomputable def scalarSchurInformation
    (b c ηx ηy : ℝ) : ℝ :=
  ηx - b * ηy / c

/-- Reduced one-variable information-form energy, omitting the constant that
does not depend on `x`. -/
noncomputable def scalarSchurEnergy
    (a b c ηx ηy x : ℝ) : ℝ :=
  scalarSchurPrecision a b c * x ^ 2 / 2 -
    scalarSchurInformation b c ηx ηy * x

/-- Exact completion of squares for scalar Gaussian elimination. -/
theorem scalarPairEnergy_eq_schur_add_square
    (a b c ηx ηy x y : ℝ) (hc : c ≠ 0) :
    scalarPairEnergy a b c ηx ηy x y =
      scalarSchurEnergy a b c ηx ηy x -
        ηy ^ 2 / (2 * c) +
        c / 2 * (y - scalarConditionalOther b c ηy x) ^ 2 := by
  unfold scalarPairEnergy scalarSchurEnergy scalarSchurPrecision
    scalarSchurInformation scalarConditionalOther
  field_simp [hc]
  ring

/-- Evaluating at the conditional optimizer leaves exactly the Schur-reduced
energy and its constant offset. -/
theorem scalarPairEnergy_at_conditionalOther
    (a b c ηx ηy x : ℝ) (hc : c ≠ 0) :
    scalarPairEnergy a b c ηx ηy x
        (scalarConditionalOther b c ηy x) =
      scalarSchurEnergy a b c ηx ηy x - ηy ^ 2 / (2 * c) := by
  rw [scalarPairEnergy_eq_schur_add_square _ _ _ _ _ _ _ hc]
  ring

/-- With positive eliminated precision, conditional substitution minimizes
the pair energy at every fixed value of the retained coordinate. -/
theorem scalarPairEnergy_conditionalOther_le
    (a b c ηx ηy x y : ℝ) (hc : 0 < c) :
    scalarPairEnergy a b c ηx ηy x
        (scalarConditionalOther b c ηy x) ≤
      scalarPairEnergy a b c ηx ηy x y := by
  rw [scalarPairEnergy_at_conditionalOther _ _ _ _ _ _ hc.ne']
  rw [scalarPairEnergy_eq_schur_add_square _ _ _ _ _ _ _ hc.ne']
  have hsquare : 0 ≤
      (y - scalarConditionalOther b c ηy x) ^ 2 := sq_nonneg _
  nlinarith

/-- The scalar Schur precision is the determinant divided by the eliminated
precision. -/
theorem scalarSchurPrecision_eq_determinant_div
    (a b c : ℝ) (hc : c ≠ 0) :
    scalarSchurPrecision a b c = (a * c - b ^ 2) / c := by
  unfold scalarSchurPrecision
  field_simp [hc]

/-- A positive eliminated precision and positive determinant give a proper
outgoing scalar precision. -/
theorem scalarSchurPrecision_pos
    (a b c : ℝ) (hc : 0 < c) (hdet : b ^ 2 < a * c) :
    0 < scalarSchurPrecision a b c := by
  rw [scalarSchurPrecision_eq_determinant_div _ _ _ hc.ne']
  exact div_pos (sub_pos.mpr hdet) hc

/-- Concrete positive message: eliminating the second coordinate from
`[[3,1],[1,2]]` yields precision `5/2` and information `7/2`. -/
theorem scalarSchurMessage_positive :
    scalarSchurPrecision 3 1 2 = (5 / 2 : ℝ) ∧
      scalarSchurInformation 1 2 4 1 = (7 / 2 : ℝ) := by
  norm_num [scalarSchurPrecision, scalarSchurInformation]

/-- On the singular determinant boundary, the outgoing precision is zero and
therefore not a proper one-dimensional Gaussian message. -/
theorem scalarSchurPrecision_singular_boundary :
    scalarSchurPrecision 1 1 1 = 0 := by
  norm_num [scalarSchurPrecision]

/-- An indefinite pair precision can produce a negative outgoing precision. -/
theorem scalarSchurPrecision_indefinite_boundary :
    scalarSchurPrecision 1 2 1 = -3 := by
  norm_num [scalarSchurPrecision]

#print axioms GaussianInformation.cavity_add_left
#print axioms GaussianInformation.variableToFactor_insert
#print axioms GaussianInformation.variableToFactor_insert_proper
#print axioms GaussianInformation.cavity_not_automatically_proper
#print axioms GaussianInformation.naive_return_edge_double_counts
#print axioms scalarPairEnergy_eq_schur_add_square
#print axioms scalarPairEnergy_at_conditionalOther
#print axioms scalarPairEnergy_conditionalOther_le
#print axioms scalarSchurPrecision_pos
#print axioms scalarSchurMessage_positive
#print axioms scalarSchurPrecision_singular_boundary
#print axioms scalarSchurPrecision_indefinite_boundary

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
