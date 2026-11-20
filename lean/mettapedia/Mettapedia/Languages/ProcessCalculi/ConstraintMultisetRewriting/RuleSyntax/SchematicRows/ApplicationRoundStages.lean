import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationPairRounds

/-!
# One complete occurrence-pair round realizes the immediate consequence operator

The snapshot includes every ordered pair, including two independently opened
uses of the same schematic occurrence. It is finite even when the reading set
of those rows is infinite. One actual protected run covers exactly the next
logical stage. This is a selected semantic scheduling policy, not an engine
default or an implementation of an existential guard oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax
open ApplicationSemantics (consequence)
open StepWeb.KernelRounds (immediate)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O]

noncomputable def snapshotPairs (s : Store O) : List (O × O) :=
  s.present.toList ×ˢ s.present.toList

omit [DecidableEq O] in
theorem mem_snapshotPairs (s : Store O) (pair : O × O) :
    pair ∈ snapshotPairs s ↔ pair.1 ∈ s.present ∧ pair.2 ∈ s.present := by
  rcases pair with ⟨major, minor⟩
  simp only [snapshotPairs, List.mem_product, Finset.mem_toList]

omit [DecidableEq O] in
theorem immediate_pairFamilies (s : Store O) (caller : Subst rowSig) :
    immediate (consequence judgmentTag arrowTag) (storeReadings s caller) =
      storeReadings s caller ∪
        pairFamilies judgmentTag arrowTag s caller (snapshotPairs s) := by
  ext value
  constructor
  · rintro (old | ⟨application, premises, produced⟩)
    · exact Or.inl old
    · obtain ⟨major, majorPresent, majorReading⟩ := premises
        (judgment judgmentTag application.function (arrow arrowTag application.domain application.codomain))
        (by simp [consequence])
      obtain ⟨minor, minorPresent, minorReading⟩ := premises
        (judgment judgmentTag application.argument application.domain) (by simp [consequence])
      refine Or.inr ((mem_pairFamilies judgmentTag arrowTag s caller (snapshotPairs s) value).mpr
        ⟨(major, minor), (mem_snapshotPairs s (major, minor)).mpr ⟨majorPresent, minorPresent⟩,
          application.function, application.argument, application.domain, application.codomain,
          majorReading, minorReading, ?_⟩)
      exact Finset.mem_singleton.mp produced
  · rintro (old | new)
    · exact Or.inl old
    · obtain ⟨pair, selected, function, argument, domain, codomain, first, second, rfl⟩ :=
        (mem_pairFamilies judgmentTag arrowTag s caller (snapshotPairs s) value).mp new
      have present := (mem_snapshotPairs s pair).mp selected
      refine Or.inr ⟨⟨function, argument, domain, codomain⟩, ?_, ?_⟩
      · intro premise member
        simp only [consequence, Finset.mem_insert, Finset.mem_singleton] at member
        rcases member with rfl | rfl
        · exact ⟨pair.1, present.1, first⟩
        · exact ⟨pair.2, present.2, second⟩
      · exact Finset.mem_singleton_self _

variable [Infinite O]

theorem application_round_exists (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) :
    ∃ execution : ProtectedRun judgmentTag arrowTag s caller,
      storeReadings execution.run.last execution.source =
        immediate (consequence judgmentTag arrowTag) (storeReadings s caller) := by
  obtain ⟨execution, exactResult⟩ := pairs_run_exists (snapshotPairs s) s caller known
    (fun pair member => (mem_snapshotPairs s pair).mp member)
  exact ⟨execution, exactResult.trans (immediate_pairFamilies s caller).symm⟩

#print axioms mem_snapshotPairs
#print axioms immediate_pairFamilies
#print axioms application_round_exists

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
