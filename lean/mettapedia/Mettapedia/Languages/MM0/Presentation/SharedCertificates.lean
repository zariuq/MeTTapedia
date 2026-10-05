import Mettapedia.Languages.MM0.Presentation.ServiceProgram
import Mettapedia.Languages.MM0.Kernel.SharedAdmission

/-!
# Checked local certificates in the MM0 service

Each saved entry is accepted by the joined program in its preceding scope.
The root uses exactly those checked conclusions. Cut relates this execution
contract to the original theory and admission system, without expanding the
runtime's shared evidence. Physical MeTTa execution remains a separate claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.SharedCertificates

open Kernel Calculus ComputationalCalculus
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

abbrev Certificate (theory : Theory) := CompactProof (family theory).Leaf

def Accepted (theory : Theory) (context : Context) (hypotheses : List Preterm)
    (expression : Preterm) (certificate : Certificate theory) : Prop :=
  Applies Service.program dataEqualityHost "mm0:certificate"
    (request theory (derivesJ context hypotheses expression) certificate) (.sym "True")

private theorem certificate_called : "mm0:certificate" ∈ calculusProgram.calledHeads := by
  decide +kernel

theorem Accepted.derives {theory : Theory} {context : Context} {hypotheses : List Preterm}
    {expression : Preterm} {certificate : Certificate theory}
    (accepted : Accepted theory context hypotheses expression certificate) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      context hypotheses expression :=
  derives_of_returned theory
    ((Service.calculus_returns _ certificate_called _ _).mp accepted)

theorem certificate_exists {theory : Theory} {context : Context} {hypotheses : List Preterm}
    {expression : Preterm}
    (derived : Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      context hypotheses expression) :
    ∃ certificate, Accepted theory context hypotheses expression certificate := by
  obtain ⟨certificate, returned⟩ := returned_of_derives theory derived
  exact ⟨certificate, (Service.calculus_returns _ certificate_called _ _).mpr returned⟩

inductive StoreChecked (theory : Theory) (context : Context) (hypotheses : List Preterm) :
    List (Preterm × Certificate theory) → Prop where
  | nil : StoreChecked theory context hypotheses []
  | record {before : List (Preterm × Certificate theory)} {expression : Preterm}
      {certificate : Certificate theory} :
      StoreChecked theory context hypotheses before →
      Accepted theory context (hypotheses ++ before.map Prod.fst) expression certificate →
      StoreChecked theory context hypotheses (before ++ [(expression, certificate)])

theorem StoreChecked.sound {theory : Theory} {context : Context} {hypotheses : List Preterm}
    {saved : List (Preterm × Certificate theory)}
    (checked : StoreChecked theory context hypotheses saved) :
    ∀ expression ∈ saved.map Prod.fst,
      Derives theory.termSignature theory.definitionSignature theory.theoremSignature
        context hypotheses expression := by
  induction checked with
  | nil => intro expression member; cases member
  | @record before expression certificate _ accepted ih =>
      have justified := (derives_with_checked_facts_iff ih).mp accepted.derives
      intro fact member
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with original | rfl
      · exact ih _ original
      · exact justified

theorem StoreChecked.root_derives {theory : Theory} {context : Context}
    {hypotheses : List Preterm} {saved : List (Preterm × Certificate theory)}
    (checked : StoreChecked theory context hypotheses saved)
    {expression : Preterm} {certificate : Certificate theory}
    (accepted : Accepted theory context (hypotheses ++ saved.map Prod.fst) expression certificate) :
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature
      context hypotheses expression :=
  (derives_with_checked_facts_iff checked.sound).mp accepted.derives

/-- The checked certificate store authorizes publication in the existing
kernel. The ordinary witness is existential evidence, not a runtime expansion. -/
theorem StoreChecked.authorizes {theory : Theory} {index : Nat} {declaration : TheoremDecl}
    {dummies : List Nat} (formed : SharedProof.Formation theory index declaration dummies)
    {saved : List (Preterm × Certificate theory)}
    (checked : StoreChecked theory (Admission.proofContext declaration dummies)
      declaration.hypotheses saved)
    {certificate : Certificate theory}
    (accepted : Accepted theory (Admission.proofContext declaration dummies)
      (declaration.hypotheses ++ saved.map Prod.fst) declaration.conclusion certificate) :
    ∃ witness, Admission.Authorized theory (.theoremDecl index declaration dummies witness) := by
  obtain ⟨witness, justified⟩ := (checked.root_derives accepted).certificate_exists
  exact ⟨witness, .theoremDecl formed.fresh formed.statement formed.dummySorts justified⟩

theorem original_hypothesis_has_certificate (context : Context) (expression : Preterm) :
    ∃ certificate, Accepted {} context [expression] expression certificate :=
  certificate_exists (.hypothesis (by simp))

theorem checked_store_cannot_create_first_theorem (context : Context)
    {saved : List (Preterm × Certificate {})}
    (checked : StoreChecked {} context [] saved)
    {expression : Preterm} {certificate : Certificate {}}
    (accepted : Accepted {} context ([].append (saved.map Prod.fst)) expression certificate) :
    False := by
  have derived := checked.root_derives accepted
  apply no_derivation_without_hypotheses_or_theorems
    (Theory.termSignature {}) (Theory.definitionSignature {}) context expression
  have empty : ({} : Theory).theoremSignature = fun _ => none := rfl
  rw [empty] at derived
  exact derived

end Mettapedia.Languages.MM0.Presentation.SharedCertificates
