import Mettapedia.TypeTheory.Calculi.NativeDependent.PresheafInterpretation

/-!
# Coherence of generated quantifier substitution

Syntactic substitution trees retain their administrative nodes. Their
interpretations nevertheless obey identity and composition on every
actual proof section. Substitution under a Pi binder uses its canonical
formation comparison, and reindexing an abstraction gives the abstraction
of the body through the actual lifted syntactic substitution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.SubstitutionCoherence

open _root_.CategoryTheory
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafPi
open Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution
open ObjectInterpretation PresheafInterpretation

universe u w
variable {C : Type u} [Category.{u} C]
variable {Constant Predicate : Type u}
variable (D : Cᵒᵖ ⥤ Type u) (constants : Constant → D.sections)
variable (predicates : Predicate → DisplayedFamily.{u, u, u, u} D)

set_option backward.isDefEq.respectTransparency false in
theorem family_identity {n : Nat} (formula : Formula Constant Predicate n) :
    family D constants predicates (.substitute formula ObjectSubstitution.identity) =
      family D constants predicates formula := by
  change reindexDisplayed (substitution D constants ObjectSubstitution.identity) _ = _
  rw [substitution_identity, reindexDisplayed_id]

set_option backward.isDefEq.respectTransparency false in
theorem family_compose {n m k : Nat} (formula : Formula Constant Predicate k)
    (earlier : ObjectSubstitution Constant n m) (later : ObjectSubstitution Constant m k) :
    family D constants predicates (.substitute (.substitute formula later) earlier) =
      family D constants predicates (.substitute formula (ObjectSubstitution.compose earlier later)) := by
  change reindexDisplayed (substitution D constants earlier)
    (reindexDisplayed (substitution D constants later) _) = _
  rw [← reindexDisplayed_comp, ← substitution_compose]
  rfl

variable {Declaration : (n : Nat) → Formula Constant Predicate n → Type w}
variable (declarations : ∀ {n : Nat} {formula : Formula Constant Predicate n},
  Declaration n formula → (family D constants predicates formula).sections)

set_option backward.isDefEq.respectTransparency false in
theorem proof_identity {n : Nat} {formula : Formula Constant Predicate n}
    (body : Proof Declaration n formula) :
    HEq (proof D constants predicates declarations
      (.substitute body ObjectSubstitution.identity))
      (proof D constants predicates declarations body) := by
  change HEq (reindexDisplayedSection (substitution D constants ObjectSubstitution.identity)
    (family D constants predicates formula) (proof D constants predicates declarations body)) _
  rw [substitution_identity]
  exact heq_of_eq (reindexDisplayedSection_id _ _)

set_option backward.isDefEq.respectTransparency false in
theorem proof_compose {n m k : Nat} {formula : Formula Constant Predicate k}
    (body : Proof Declaration k formula)
    (earlier : ObjectSubstitution Constant n m) (later : ObjectSubstitution Constant m k) :
    HEq (proof D constants predicates declarations (.substitute (.substitute body later) earlier))
      (proof D constants predicates declarations
        (.substitute body (ObjectSubstitution.compose earlier later))) := by
  change HEq (reindexDisplayedSection (substitution D constants earlier)
    (reindexDisplayed (substitution D constants later) (family D constants predicates formula))
      (reindexDisplayedSection (substitution D constants later) (family D constants predicates formula)
        (proof D constants predicates declarations body)))
    (reindexDisplayedSection (substitution D constants (ObjectSubstitution.compose earlier later))
      (family D constants predicates formula) (proof D constants predicates declarations body))
  rw [substitution_compose]
  exact heq_of_eq (reindexDisplayedSection_comp (substitution D constants later)
    (family D constants predicates formula) (substitution D constants earlier)
    (proof D constants predicates declarations body)).symm

set_option backward.isDefEq.respectTransparency false in
/-- Native Pi transport and syntactic lifting agree on the complete
natural function section, rather than only on one returned value. -/
theorem abstraction_substitution {n m : Nat}
    {body : Formula Constant Predicate (m + 1)}
    (bodyProof : Proof Declaration (m + 1) body) (replacements : ObjectSubstitution Constant n m) :
    HEq (reindexFunction (substitution D constants replacements)
      (objectFamily D (context D m)) (family D constants predicates body)
      (proof D constants predicates declarations (.lam bodyProof)))
    (proof D constants predicates declarations
      (.lam (.substitute bodyProof (ObjectSubstitution.lift replacements)))) := by
  change HEq (reindexFunction (substitution D constants replacements)
    (objectFamily D (context D m)) (family D constants predicates body)
      (lamDisplayed (proof D constants predicates declarations bodyProof)))
    (lamDisplayed (reindexDisplayedSection
      (substitution D constants (ObjectSubstitution.lift replacements))
        (family D constants predicates body) (proof D constants predicates declarations bodyProof)))
  rw [reindexFunction_lam, substitution_lift]

end Mettapedia.TypeTheory.Calculi.NativeDependent.SubstitutionCoherence
