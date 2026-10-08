import Mettapedia.Logic.HostingStyles.JudgmentsAsTypes

/-!
# Where the obligations on a framework's conversion are used

Adequacy up to conversion is usually derived from three properties of the
framework's computation rule.  This module states each as an explicit
hypothesis at the one place it is used.  `JudgmentsAsTypes` proves the same
conclusions for this framework without assuming them, by a model and a
logical relation; the statements here record what the usual route needs.

* **Confluence** (`Confluent`) is used to show that a conversion class holds
  at most one normal term (`normal_unique_of_confluent`), hence at most one
  encoded derivation (`encodeTerm_eq_of_conv_of_confluent`).  Without it,
  conversion between two canonical forms would not be decidable by
  inspection.
* **Termination**, in the form that every term of a judgment's type reduces
  to a canonical form (`Normalizing`), is used to show that every term of a
  judgment's type is convertible to the encoding of a derivation
  (`conv_encodeTerm_of_normalizing`).
* **Preservation of types** is what makes the previous statement meaningful:
  the canonical form reached must have the type started from.  In this
  framework a step relates two terms of one type by construction (`Step` is a
  relation on `Tm signature holes context type`), so the obligation is
  discharged by the typing of substitution and does not appear as a
  hypothesis.  In a framework with untyped terms and a typing relation it is
  the hypothesis that the reduct of a typed term has the same type.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Framework

namespace Framework

variable {B : Type} {signature : Signature B} {Hole : Type} {holes : Hole → Ty B}

/-- Reduction: finitely many steps. -/
abbrev Reduces {context : List (Ty B)} {type : Ty B}
    (first second : Tm signature holes context type) : Prop :=
  Relation.ReflTransGen Step first second

/-- **Confluence** of the declared computation rule: two reducts of one term
have a common reduct. -/
def Confluent (signature : Signature B) {Hole : Type} (holes : Hole → Ty B) : Prop :=
  ∀ {context : List (Ty B)} {type : Ty B} (origin first second : Tm signature holes context type),
    Reduces origin first → Reduces origin second →
      ∃ common, Reduces first common ∧ Reduces second common

/-- Under confluence, convertible terms have a common reduct. -/
theorem common_reduct_of_conv (confluent : Confluent signature holes)
    {context : List (Ty B)} {type : Ty B} {first second : Tm signature holes context type}
    (convertible : Conv first second) : ∃ common, Reduces first common ∧ Reduces second common := by
  induction convertible with
  | rel first second step => exact ⟨second, .single step, .refl⟩
  | refl term => exact ⟨term, .refl, .refl⟩
  | symm _ _ _ ih =>
      obtain ⟨common, left, right⟩ := ih
      exact ⟨common, right, left⟩
  | trans _ middle _ _ _ ihFirst ihSecond =>
      obtain ⟨leftCommon, firstLeft, middleLeft⟩ := ihFirst
      obtain ⟨rightCommon, middleRight, secondRight⟩ := ihSecond
      obtain ⟨common, leftJoin, rightJoin⟩ :=
        confluent middle leftCommon rightCommon middleLeft middleRight
      exact ⟨common, firstLeft.trans leftJoin, secondRight.trans rightJoin⟩

/-- A normal term reduces only to itself. -/
theorem Normal.eq_of_reduces {context : List (Ty B)} {type : Ty B}
    {term next : Tm signature holes context type} (normal : Normal term)
    (reduces : Reduces term next) : next = term := by
  induction reduces with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      exact (normal _ step).elim

/-- **Where confluence is used**: a conversion class holds at most one normal
term. -/
theorem normal_unique_of_confluent (confluent : Confluent signature holes)
    {context : List (Ty B)} {type : Ty B} {first second : Tm signature holes context type}
    (firstNormal : Normal first) (secondNormal : Normal second) (convertible : Conv first second) :
    first = second := by
  obtain ⟨common, firstReduces, secondReduces⟩ := common_reduct_of_conv confluent convertible
  rw [← firstNormal.eq_of_reduces firstReduces, secondNormal.eq_of_reduces secondReduces]

end Framework

namespace RuleSignature

variable {J : Type} {P : RuleSignature J} (finitary : P.Finitary)

/-- The usual route to "conversion identifies no two derivations", with
confluence as an explicit hypothesis: two encoded derivations are normal, so
if convertible they are the same term, and the encoding of terms is
injective. -/
theorem Finitary.encodeTerm_eq_of_conv_of_confluent
    (confluent : Confluent finitary.signature (noHoles (B := J))) {j : J} {first second : P.Proof j}
    (convertible : Conv (finitary.encodeTerm first) (finitary.encodeTerm second)) :
    first = second := by
  have terms := normal_unique_of_confluent confluent (finitary.encodeTerm_normal first)
    (finitary.encodeTerm_normal second) convertible
  have reads := congrArg finitary.readback terms
  rwa [Finitary.readback_encodeTerm, Finitary.readback_encodeTerm] at reads

/-- **Termination**, in the form adequacy uses: every term of a judgment's
type reduces to a canonical form of that type. -/
def Finitary.Normalizing : Prop :=
  ∀ {j : J} (term : Closed finitary.signature (.base j)),
    ∃ normal : Nf finitary.signature (noHoles (B := J)) [] (.base j), Reduces term normal.toTm

/-- **Where termination is used**: every term of a judgment's type is
convertible to the encoding of a derivation. -/
theorem Finitary.conv_encodeTerm_of_normalizing (normalizing : finitary.Normalizing) {j : J}
    (term : Closed finitary.signature (.base j)) :
    ∃ proof : P.Proof j, Conv term (finitary.encodeTerm proof) := by
  obtain ⟨normal, reduces⟩ := normalizing term
  obtain ⟨proof, rfl⟩ := finitary.encodeNf_surjective normal
  refine ⟨proof, ?_⟩
  rw [← Finitary.toTm_encodeNf]
  exact Relation.ReflTransGen.rec (motive := fun next _ => Conv term next) (.refl _)
    (fun _ step ih => .trans _ _ _ ih (.rel _ _ step)) reduces

end RuleSignature

#print axioms Framework.normal_unique_of_confluent
#print axioms RuleSignature.Finitary.encodeTerm_eq_of_conv_of_confluent
#print axioms RuleSignature.Finitary.conv_encodeTerm_of_normalizing

end Mettapedia.Logic.HostingStyles
