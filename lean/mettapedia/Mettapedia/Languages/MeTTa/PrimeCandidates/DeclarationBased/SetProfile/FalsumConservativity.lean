import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Models
import Mettapedia.Logic.HOL.ProofSyntaxModuloConservativity

/-!
# The definition of `Falsum` is conservative

The profile with `Falsum` defined computes modulo
`definedEquations = falsumEquation :: sourceEquations`. The signature's
definition is the closed definition `Falsum := ∀p. p` (`falsumEquation_eq`):
its body is a closed core term of type `prop` that does not mention `Falsum`,
and `Falsum` occurs in no equation of `add` or `pow`
(`sourceEquations_avoid_falsum`). The theorem for closed definitions applies:

* **conservativity** (`falsum_definition_conservative`): a sequent that does not
  mention `Falsum` has a proof modulo `definedEquations` iff it has one modulo
  `sourceEquations`; likewise for conversion articles
  (`falsum_conversion_conservative`);
* **unfolding** (`falsum_definition_unfolds`): a core sequent has a proof modulo
  `definedEquations` iff its unfolding, with `Falsum` replaced by `∀p. p`
  (`unfoldFalsum`), has one modulo `sourceEquations`. The unfolded proof is the
  translation of the given one, rule by rule (`unfoldFalsumProof`).

Occurrences of `Falsum` are decided by computation (`noFalsum`, `noFalsumHyps`).

**Controls.**

* Positive: ex falso `∀r. Falsum → r` mentions `Falsum`. Its unfolding is
  `∀r. (∀p. p) → r`; one has a proof with the definition exactly when the other
  has one without it, and both do (`exFalso_unfolds`).
* Negative: `Falsum` unfolds to `∀p. p`, which is false in the numbers
  (`falsumDefiniens_not_derivable`), so `Falsum` has no proof modulo
  `definedEquations` (`falsum_not_derivable`).
* The conservativity is for sequents without `Falsum`. `Falsum → ∀p. p` has no
  proof modulo `sourceEquations` and one modulo `definedEquations`
  (`ExecutableModel.CodeModel.old_formula_gains_a_proof`), while its unfolding
  has one in both.

**The negative controls of the profile, with `Falsum` defined**, each derived
from its version modulo `sourceEquations` through the theorem:
`Models.no_wrong_conclusion_defined`, `Models.induction_needed_defined` and
`Models.no_altered_article_defined`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile

open Mettapedia.Logic

/-! ## The closed definition and its unfolding -/

/-- `∀p. p`, the body of the definition of `Falsum`. -/
def falsumDefiniens : HOL.ClosedFormula SetConst := .all (σ := .prop) (.var .vz)

/-- The signature's definition is the closed definition `Falsum := ∀p. p`. -/
theorem falsumEquation_eq :
    falsumEquation = HOL.DefiningEquation.ofDefinition .falsum falsumDefiniens :=
  rfl

/-- The unfolding of `Falsum`: `Falsum` goes to `∀p. p`, every other constant to
itself. -/
def unfoldFalsum : {τ : HOL.Ty SetBase} → SetConst τ → HOL.ClosedTerm SetConst τ
  | _, .falsum => falsumDefiniens
  | _, symbol => .const symbol

/-- Every constant is `Falsum`, or a constant other than `Falsum`. -/
theorem falsum_dichotomy {τ : HOL.Ty SetBase} (symbol : SetConst τ) :
    HOL.NoConstOccurrence SetConst.falsum (.const symbol : HOL.ClosedTerm SetConst τ) ∨
      (⟨τ, symbol⟩ : (τ : HOL.Ty SetBase) × SetConst τ) = ⟨.prop, .falsum⟩ := by
  cases symbol with
  | falsum => exact .inr rfl
  | _ => exact .inl (.const_diff_type (fun same => by cases same) _)

theorem unfoldFalsum_unfolds : HOL.Unfolds SetConst.falsum falsumDefiniens unfoldFalsum where
  self := rfl
  other := by
    intro τ symbol avoids
    cases symbol with
    | falsum =>
        cases avoids with
        | const_diff_type differ => exact absurd rfl differ
        | const_same_ne _ differ => exact absurd rfl differ
    | _ => rfl
  dichotomy := falsum_dichotomy

theorem falsumDefiniens_core : falsumDefiniens.isCore = true := rfl

theorem falsumDefiniens_avoids : HOL.NoConstOccurrence SetConst.falsum falsumDefiniens :=
  .all .var

/-! ## Deciding occurrences of `Falsum` -/

/-- Whether a constant is `Falsum`. -/
def isFalsum : {τ : HOL.Ty SetBase} → SetConst τ → Bool
  | _, .falsum => true
  | _, _ => false

theorem isFalsum_sound {τ : HOL.Ty SetBase} (symbol : SetConst τ)
    (other : isFalsum symbol = false) :
    HOL.NoConstOccurrence SetConst.falsum (.const symbol : HOL.ClosedTerm SetConst τ) := by
  rcases falsum_dichotomy symbol with avoids | same
  · exact avoids
  · cases same
    cases other

/-- A term without `Falsum`, checked by computation. -/
theorem noFalsum {Γ : HOL.Ctx SetBase} {τ : HOL.Ty SetBase} {X : HOL.Term SetConst Γ τ}
    (checked : X.anyConst isFalsum = false) : HOL.NoConstOccurrence SetConst.falsum X :=
  HOL.noConstOccurrence_of_anyConst isFalsum_sound X checked

/-- Hypotheses without `Falsum`, checked by computation. -/
theorem noFalsumHyps {Γ : HOL.Ctx SetBase} {Δ : List (HOL.Formula SetConst Γ)}
    (checked : Δ.all (!·.anyConst isFalsum) = true) :
    ∀ δ ∈ Δ, HOL.NoConstOccurrence SetConst.falsum δ :=
  HOL.hypsAvoid_of_anyConst isFalsum_sound checked

/-- `Falsum` occurs in no equation of `add` or `pow`. -/
theorem sourceEquations_avoid_falsum : HOL.EquationsAvoid SetConst.falsum sourceEquations :=
  HOL.equationsAvoid_of_anyConst isFalsum_sound (by decide)

/-! ## Conservativity -/

/-- **The definition of `Falsum` is conservative.** A sequent that does not
mention `Falsum` has a proof modulo the equations with the definition iff it has
one modulo the equations of `add` and `pow`. -/
theorem falsum_definition_conservative {Γ : HOL.Ctx SetBase}
    {Δ : List (HOL.Formula SetConst Γ)} {φ : HOL.Formula SetConst Γ}
    (hypsAvoid : ∀ δ ∈ Δ, HOL.NoConstOccurrence SetConst.falsum δ)
    (avoids : HOL.NoConstOccurrence SetConst.falsum φ) :
    Nonempty (HOL.ProofSyntaxModulo definedEquations Δ φ) ↔
      Nonempty (HOL.ProofSyntaxModulo sourceEquations Δ φ) :=
  HOL.ProofSyntaxModulo.definition_conservative unfoldFalsum_unfolds falsumDefiniens_avoids
    sourceEquations_avoid_falsum hypsAvoid avoids

/-- Conversion articles between terms without `Falsum` are conservative. -/
theorem falsum_conversion_conservative {Γ : HOL.Ctx SetBase} {τ : HOL.Ty SetBase}
    {l r : HOL.Term SetConst Γ τ} (leftAvoids : HOL.NoConstOccurrence SetConst.falsum l)
    (rightAvoids : HOL.NoConstOccurrence SetConst.falsum r) :
    HOL.CoreConversion definedEquations l r ↔ HOL.CoreConversion sourceEquations l r :=
  HOL.CoreConversion.definition_conservative unfoldFalsum_unfolds falsumDefiniens_avoids
    sourceEquations_avoid_falsum leftAvoids rightAvoids

/-- The unfolding of a proof modulo the equations with the definition: every
rule kept, every sequent unfolded. -/
def unfoldFalsumProof {Γ : HOL.Ctx SetBase} {Δ : List (HOL.Formula SetConst Γ)}
    {φ : HOL.Formula SetConst Γ} (proof : HOL.ProofSyntaxModulo definedEquations Δ φ) :
    HOL.ProofSyntaxModulo sourceEquations (Δ.map (HOL.substConst unfoldFalsum))
      (HOL.substConst unfoldFalsum φ) :=
  HOL.ProofSyntaxModulo.unfoldDefinition unfoldFalsum_unfolds falsumDefiniens_core
    falsumDefiniens_avoids sourceEquations_avoid_falsum proof

/-- **Unfolding.** A core sequent has a proof modulo the equations with the
definition iff its unfolding has one modulo the equations of `add` and `pow`. -/
theorem falsum_definition_unfolds {Γ : HOL.Ctx SetBase} {Δ : List (HOL.Formula SetConst Γ)}
    {φ : HOL.Formula SetConst Γ} (hypsCore : ∀ δ ∈ Δ, δ.isCore = true)
    (core : φ.isCore = true) :
    Nonempty (HOL.ProofSyntaxModulo definedEquations Δ φ) ↔
      Nonempty (HOL.ProofSyntaxModulo sourceEquations (Δ.map (HOL.substConst unfoldFalsum))
        (HOL.substConst unfoldFalsum φ)) :=
  HOL.ProofSyntaxModulo.definition_unfold_iff unfoldFalsum_unfolds falsumDefiniens_core
    falsumDefiniens_avoids sourceEquations_avoid_falsum hypsCore core

/-! ## Controls of the unfolding -/

/-- `∀r. (∀p. p) → r`. -/
def exFalsoUnfolded : HOL.Formula SetConst [] :=
  .all (σ := .prop) (.imp (.all (σ := .prop) (.var .vz)) (.var .vz))

theorem exFalsoStatement_unfolds :
    HOL.substConst unfoldFalsum exFalsoStatement = exFalsoUnfolded :=
  rfl

/-- **Positive control: ex falso.** `∀r. Falsum → r` mentions `Falsum`. It has a
proof modulo the equations with the definition exactly when its unfolding
`∀r. (∀p. p) → r` has one modulo the equations of `add` and `pow`, and the
unfolding of `exFalso` is one. -/
theorem exFalso_unfolds :
    (Nonempty (HOL.ProofSyntaxModulo definedEquations [] exFalsoStatement) ↔
        Nonempty (HOL.ProofSyntaxModulo sourceEquations [] exFalsoUnfolded)) ∧
      Nonempty (HOL.ProofSyntaxModulo sourceEquations [] exFalsoUnfolded) := by
  have unfolds := falsum_definition_unfolds (Δ := []) (φ := exFalsoStatement)
    (fun _ listed => absurd listed List.not_mem_nil) rfl
  rw [exFalsoStatement_unfolds] at unfolds
  exact ⟨unfolds, ⟨exFalsoStatement_unfolds ▸ unfoldFalsumProof exFalso⟩⟩

/-- `∀p. p` has no proof modulo the equations of `add` and `pow`: it is false in
the numbers. -/
theorem falsumDefiniens_not_derivable :
    ¬ Nonempty (HOL.ProofSyntaxModulo sourceEquations [] falsumDefiniens) := by
  rintro ⟨proof⟩
  have holds := Models.proof_sound Models.naturals proof
    (Models.equationsHold Models.naturals_lawful) (fun _ listed => absurd listed List.not_mem_nil)
  exact holds (ULift.up False) trivial

/-- **Negative control: `Falsum`.** `Falsum` unfolds to `∀p. p`, so it has no proof
modulo the equations with the definition. -/
theorem falsum_not_derivable :
    ¬ Nonempty (HOL.ProofSyntaxModulo definedEquations []
      (.const .falsum : HOL.ClosedFormula SetConst)) := fun proof =>
  falsumDefiniens_not_derivable
    ((falsum_definition_unfolds (fun _ listed => absurd listed List.not_mem_nil) rfl).mp proof)

/-! ## The negative controls of the profile with `Falsum` defined -/

namespace Models

/-- **Wrong conclusion, with `Falsum` defined**, from `no_wrong_conclusion` by the
conservativity of the definition. -/
theorem no_wrong_conclusion_defined :
    ¬ Nonempty (HOL.ProofSyntaxModulo definedEquations zeroAddAssumptions wrongStatement) :=
  fun proof => no_wrong_conclusion
    ((falsum_definition_conservative (noFalsumHyps (by decide)) (noFalsum (by decide))).mp proof)

/-- **Induction cannot be dropped, with `Falsum` defined**, from `induction_needed`. -/
theorem induction_needed_defined :
    ¬ Nonempty (HOL.ProofSyntaxModulo definedEquations [reflAxiom, substAxiom]
      zeroAddStatement) :=
  fun proof => induction_needed
    ((falsum_definition_conservative (noFalsumHyps (by decide)) (noFalsum (by decide))).mp proof)

/-- **No altered article, with `Falsum` defined**, from `no_altered_article`. -/
theorem no_altered_article_defined :
    ¬ HOL.CoreConversion definedEquations (Γ := [numTy]) (addT zeroT (sucT (.var .vz)))
      (sucT (sucT (addT zeroT (.var .vz)))) :=
  fun conversion => no_altered_article
    ((falsum_conversion_conservative (noFalsum (by decide)) (noFalsum (by decide))).mp conversion)

end Models

#print axioms unfoldFalsum_unfolds
#print axioms sourceEquations_avoid_falsum
#print axioms falsum_definition_conservative
#print axioms falsum_conversion_conservative
#print axioms falsum_definition_unfolds
#print axioms exFalso_unfolds
#print axioms falsum_not_derivable
#print axioms Models.no_wrong_conclusion_defined
#print axioms Models.induction_needed_defined
#print axioms Models.no_altered_article_defined

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile
