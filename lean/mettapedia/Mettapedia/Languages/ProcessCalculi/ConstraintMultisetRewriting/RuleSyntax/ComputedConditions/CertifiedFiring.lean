import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Executable

/-!
# Checking evidence for a proposed firing

The relations of a program remain propositions. To realize a particular
firing, a proposer supplies an instantiation and one certificate per
condition. Each certificate is checked against the relation name and the
instantiated input and output. The result retains the submitted evidence.

A checker needs a soundness theorem for the theory and assumptions from
which it accepts evidence. It can check individual certificates without
enumerating the relation's graph.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.CertifiedFiring

open NamesOnTheStep (Expr)
open Presentation.Schematic (inst equationsOf exists_zip_of_mem)
open RuleSyntax.Machines (rowRule)

universe u

abbrev Checker (Evidence : Type u) := ℕ → List Expr → Expr → Evidence → Bool

/-- A submitted instantiation with evidence in the order of the conditions. -/
structure Certificate (Evidence : Type u) where
  bindings : List (ℕ × Expr)
  evidence : List Evidence

def Certificate.assignment {Evidence : Type u} (certificate : Certificate Evidence) (name : ℕ) : Expr :=
  (certificate.bindings.lookup name).getD (.sym 0)

/-- Compute the proposed result and retain the full certificate on success. -/
def verify {Evidence : Type u} (check : Checker Evidence) (schema : Executable.Schema)
    (source : Expr) (certificate : Certificate Evidence) : Option (Expr × Certificate Evidence) :=
  let θ := certificate.assignment
  if inst θ schema.left = source ∧ schema.conditions.length = certificate.evidence.length ∧
      ∀ p ∈ schema.conditions.zip certificate.evidence,
        check p.1.name (p.1.arguments.map (inst θ)) (inst θ p.1.value) p.2 = true then
    some (inst θ schema.right, certificate)
  else none

/-- Successful certificate checking gives an actual firing in the relational
semantics and retains the evidence used for that firing. -/
theorem verify_sound {Evidence : Type u} {R : Relations} (check : Checker Evidence)
    (sound : ∀ name arguments value proof, check name arguments value proof = true → R name arguments value)
    {schema : Executable.Schema} {source result : Expr} {certificate retained : Certificate Evidence}
    (accepted : verify check schema source certificate = some (result, retained)) :
    RelationStep R schema.rule {source} {result} ∧ retained = certificate := by
  dsimp only [verify] at accepted
  split at accepted
  · rename_i holds
    obtain ⟨left, length, evidence⟩ := holds
    cases accepted
    refine ⟨⟨certificate.assignment, 0, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · simpa [Executable.Schema.rule, rowRule] using left
    · simp [Executable.Schema.rule, rowRule]
    · simp [Executable.Schema.rule, rowRule, equationsOf]
    · intro c member
      obtain ⟨proof, paired⟩ := exists_zip_of_mem length member
      exact sound _ _ _ proof (evidence (c, proof) paired)
    · simp [Executable.Schema.rule, rowRule]
  · cases accepted

namespace Controls

def schema : Executable.Schema :=
  ⟨.var 0, [{ name := 1, arguments := [.var 0], value := .var 1 }], .var 1⟩

def checker : Checker ℕ
  | 1, [x], y, proof => decide (x = .sym proof ∧ y = .sym (proof + 1))
  | _, _, _, _ => false

def proposal (proof : ℕ) : Certificate ℕ := ⟨[(0, .sym 4), (1, .sym 5)], [proof]⟩

theorem accepts_receipt :
    verify checker schema (.sym 4) (proposal 4) = some (.sym 5, proposal 4) := by rfl

theorem rejects_receipt_for_other_arguments :
    verify checker schema (.sym 4) (proposal 5) = none := by rfl

end Controls

#print axioms verify_sound
#print axioms Controls.accepts_receipt
#print axioms Controls.rejects_receipt_for_other_arguments

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.CertifiedFiring
