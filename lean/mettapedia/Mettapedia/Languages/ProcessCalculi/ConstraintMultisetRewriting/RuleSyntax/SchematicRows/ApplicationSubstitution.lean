import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Substitution

/-!
# Uniform DTL derivations over a retained interface

Typed application is preserved by substitution. A change of caller model that
agrees on every stored datum's ambient terms preserves derivability as well.
These are derived laws of the hypothesis and application constructors, not an
assumed generalization oracle. They supply the logical premise for closing
fresh result variables while retaining all shared captures.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSemantics

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax

theorem Derives.source_congr (judgmentTag arrowTag : Nat) (data : Data)
    (first second : Subst rowSig)
    (agrees : ∀ row ∈ data, ∀ term ∈ row.ambientTerms,
      first.applyTerm term = second.applyTerm term)
    {value : Tm} (derivation : Derives judgmentTag arrowTag data first value) :
    Derives judgmentTag arrowTag data second value := by
  induction derivation with
  | hypothesis assumed =>
    obtain ⟨row, member, reading⟩ := assumed
    exact .hypothesis ⟨row, member,
      (Row.readsAt_source_congr X (a := PUnit.unit) (b := PUnit.unit) row first second
        (agrees row member) _).mp reading⟩
  | apply _ _ major minor => exact .apply major minor

theorem Derives.substitute (judgmentTag arrowTag : Nat) (data : Data) (source : Subst rowSig)
    {value : Tm} (derivation : Derives judgmentTag arrowTag data source value)
    (later : Subst rowSig) :
    Derives judgmentTag arrowTag data (later.comp source) (later.applyTerm value) := by
  induction derivation with
  | hypothesis assumed =>
    obtain ⟨row, member, reading⟩ := assumed
    exact .hypothesis ⟨row, member,
      Row.readsAt_postcompose X (a := PUnit.unit) (b := PUnit.unit) (c := PUnit.unit)
        row source later _ reading⟩
  | apply _ _ major minor =>
    simp only [apply_judgment, apply_arrow] at major minor
    simpa only [apply_judgment, apply_app] using Derives.apply major minor

theorem Derives.uniform (judgmentTag arrowTag : Nat) (data : Data) (source later : Subst rowSig)
    (fixes : ∀ row ∈ data, ∀ term ∈ row.ambientTerms,
      later.applyTerm (source.applyTerm term) = source.applyTerm term)
    {value : Tm} (derivation : Derives judgmentTag arrowTag data source value) :
    Derives judgmentTag arrowTag data source (later.applyTerm value) := by
  have instantiated := derivation.substitute judgmentTag arrowTag data source later
  apply instantiated.source_congr judgmentTag arrowTag data (later.comp source) source
  intro row member term inside
  rw [Subst.applyTerm_comp]
  exact fixes row member term inside

/-- A closure pins the whole retained interface, rather than guessing that
an unescaped arbitrary hypothesis was universally derived. -/
def generalized (context : List Tm) (value : Tm) : Closure (OneFrame.Terms Tm) PUnit.unit :=
  ⟨⟨PUnit.unit, [], context, value⟩, context⟩

theorem generalized_reading_derivable (judgmentTag arrowTag : Nat) (data : Data)
    (context : List Tm) (covers : ∀ row ∈ data, ∀ term ∈ row.ambientTerms, term ∈ context)
    {value : Tm} (derivation : Derives judgmentTag arrowTag data (Subst.id rowSig) value)
    (source : Subst rowSig) (answer : Tm)
    (reading : (generalized context value).ReadsAt X (b := PUnit.unit) source answer) :
    Derives judgmentTag arrowTag data source answer := by
  dsimp only [generalized, Closure.ReadsAt] at reading
  obtain ⟨locals, _, captures, output⟩ := reading
  have agrees : ∀ row ∈ data, ∀ term ∈ row.ambientTerms,
      locals.applyTerm term = source.applyTerm term := by
    intro row member term inside
    exact (List.forall₂_same.mp captures) term (covers row member term inside)
  have instantiated : Derives judgmentTag arrowTag data locals (locals.applyTerm value) :=
    derivation.substitute judgmentTag arrowTag data (Subst.id rowSig) locals
  have result := instantiated.source_congr judgmentTag arrowTag data locals source agrees
  exact output ▸ result

theorem generalized_reads_instance (context : List Tm) (value : Tm) (source : Subst rowSig) :
    (generalized context value).ReadsAt X (b := PUnit.unit) source (source.applyTerm value) := by
  refine ⟨source, ?_, List.forall₂_same.mpr (fun _ _ => rfl), rfl⟩
  intro equation member
  cases member

#print axioms Derives.source_congr
#print axioms Derives.substitute
#print axioms Derives.uniform
#print axioms generalized_reading_derivable
#print axioms generalized_reads_instance

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSemantics
