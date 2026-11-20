import Mettapedia.Languages.MeTTa.PeTTa.AtomFreshNamespaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericProtocol

/-!
# Constructed Atom openings for direct and held schematic reads

The rule and datum receive independent namespaces above the source's actual
finite support. This supplies the existing read protocol's freshness premise,
including open ordinary rows, retained equations and captured arguments.
The datum's private variables do not become caller variables merely because
the schema is stored. Matching and admission remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AtomSchematicReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open RuleSyntax OneFrame JointFirings
open SchematicRows HeldReadGenericSources
open AtomFreshNamespaces (X E opening sourceTerms supportBound)

variable {O R : Type*} (ordinary : RuleSyntax.State (Terms Atom) O) (rows : Finset R)
  (closures : R → Closure (Terms Atom) ordinary.frame)

noncomputable def bound : Nat :=
  let source := (mixed ordinary rows closures).scope
  supportBound (sourceTerms source.knowledge source.present source.label)

noncomputable def direct (selected : R) (output : O) :=
  HeldReadGenericFirings.direct ordinary rows closures (E := E) selected PUnit.unit
    (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1) output

/-- Joint freshness is constructed, rather than assumed for the selected
schema. Its own equations and parameter terms remain in the scope probe. -/
theorem direct_fresh (selected : R) (output : O) :
    (direct ordinary rows closures selected output).Fresh X := by
  rcases ordinary with ⟨frame, knowledge, present, label⟩
  cases frame
  let ordinary : RuleSyntax.State (Terms Atom) O := ⟨PUnit.unit, knowledge, present, label⟩
  let source := (mixed ordinary rows closures).scope
  let firing := direct ordinary rows closures selected output
  let datumMember : OneMember atomAction Atom (Set.univ : Program (Terms Atom)) :=
    ⟨RowUse.scopeRule (closures selected), Set.mem_univ _, opening (bound ordinary rows closures) 1,
      ⟨[], [], []⟩, []⟩
  let family := [(0, firing.scopeMember), (1, datumMember)]
  have distinct : (family.map Prod.fst).Nodup := by
    change ([0, 1] : List Nat).Nodup
    decide +kernel
  have correct : ∀ entry ∈ family,
      entry.2.opening = opening (supportBound (sourceTerms source.knowledge source.present source.label))
        entry.1 := by
    intro entry inside
    simp only [family, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  have fresh := AtomFreshNamespaces.fresh_from_support source.knowledge source.present source.label
    family distinct correct
  have members : firing.scopeBag.members = family.map Prod.snd := by
    simp [firing, direct, HeldReadGenericFirings.direct, Firing.scopeBag, Firing.scopeMember,
      Firing.uses, Firing.takenUses, Firing.readUses, RowUse.scopeMember, datumMember, family]
  change (⟨PUnit.unit, firing.scopeBag.members⟩ :
    Bag Atom E (Set.univ : Program (Terms Atom)) PUnit.unit).Fresh X source
  rw [members]
  exact fresh

open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (Subst subst)

/-- Every denotational closure reading constructs a model of the actual
direct firing's information. Captures are shared with the caller, while the
two local openings may be instantiated independently. -/
theorem direct_model_of_reading (selected : R) (output : O) (caller : Subst)
    (present : selected ∈ rows) (known : X.Models (b := PUnit.unit) caller ordinary.knowledge) (value : Atom)
    (reading : (closures selected).ReadsAt X (b := PUnit.unit) caller value) :
    ∃ assignment : Subst,
      X.Models (b := PUnit.unit) assignment ((direct ordinary rows closures selected output).information X) ∧
      (∀ term, (mixed ordinary rows closures).scope.Mentions term →
        subst assignment term = subst caller term) ∧
      subst assignment (subst (opening (bound ordinary rows closures) 0)
        (closures selected).schema.value) = value := by
  obtain ⟨localAssignment, localKnown, captures, result⟩ := reading
  have independent := direct_fresh ordinary rows closures selected output PUnit.unit caller
  obtain ⟨assignment, together⟩ := independent localAssignment localAssignment
  have kept (term : Atom) (mentioned : (mixed ordinary rows closures).scope.Mentions term) :
      subst assignment term = subst caller term := by
    have actual := together.1.1 term mentioned
    change subst assignment (subst Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty term) =
      subst caller term at actual
    simpa only [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_empty] using actual
  have copied := together.1.2 (closures selected).schema.value
    (by
      change (closures selected).schema.value ∈
        (HeldReadGenericFirings.copyRule (closures selected).schema).terms
      simp [HeldReadGenericFirings.copyRule, Rule.terms])
  have materialized := together.2 (closures selected).schema.value
    (by simp [RowUse.scopeRule, Rule.terms])
  change subst assignment (subst (opening (bound ordinary rows closures) 0)
    (closures selected).schema.value) = subst localAssignment (closures selected).schema.value at copied
  change subst assignment (subst (opening (bound ordinary rows closures) 1)
    (closures selected).schema.value) = subst localAssignment (closures selected).schema.value at materialized
  change subst localAssignment (closures selected).schema.value = value at result
  refine ⟨assignment, ?_, kept, copied.trans result⟩
  change X.Models (b := PUnit.unit) assignment
    ((HeldReadGenericFirings.direct ordinary rows closures (E := E) selected PUnit.unit
      (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
      output).information X)
  rw [HeldReadGenericFirings.direct_information (E := E) ordinary rows closures selected PUnit.unit
    (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1) X output,
    Interface.Frames.models_append]
  refine ⟨?_, ?_⟩
  · unfold HeldReadGenericFirings.datumInformation
    rw [Interface.Frames.models_append, Interface.Frames.models_append]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro equation inside
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
      have left := kept original.1 (Or.inl (List.mem_map_of_mem member))
      have right := kept original.2 (Or.inr (Or.inl (List.mem_map_of_mem member)))
      change subst assignment (subst Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty original.1) =
        subst assignment (subst Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty original.2)
      rw [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_empty,
        Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_empty, left, right]
      exact known original member
    · intro equation inside
      obtain ⟨original, member, rfl⟩ := List.mem_map.mp inside
      have left := together.2 original.1
        (by simp [RowUse.scopeRule, Rule.terms, List.mem_map_of_mem member])
      have right := together.2 original.2
        (by simp [RowUse.scopeRule, Rule.terms, List.mem_map_of_mem member])
      exact left.trans ((localKnown original member).trans right.symm)
    · intro equation inside
      have aligned : List.Forall₂
          (fun parameter argument => X.E (X.act (b := PUnit.unit) assignment parameter)
            (X.act (b := PUnit.unit) assignment argument))
          ((closures selected).schema.params.map (X.act (b := PUnit.unit)
            (opening (bound ordinary rows closures) 1)))
          ((closures selected).args.map (X.act (b := PUnit.unit)
            (E.weaken (a := ordinary.frame) PUnit.unit))) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        apply List.forall₂_iff_zip.mpr
        refine ⟨captures.length_eq, ?_⟩
        intro parameter argument paired
        have parameterInside := (List.of_mem_zip paired).1
        have argumentInside := (List.of_mem_zip paired).2
        have parameterRead := together.2 parameter
          (by simp [RowUse.scopeRule, Rule.terms, parameterInside])
        have argumentRead := kept argument
          ((HeldReadGenericSources.scope_mentions_iff ordinary rows closures argument).mpr
            (Or.inr ⟨selected, present, argumentInside⟩))
        have capture := List.forall₂_zip captures paired
        change subst assignment (subst (opening (bound ordinary rows closures) 1) parameter) =
          subst assignment (subst Mettapedia.Languages.MeTTa.SubstitutionAlgebra.empty argument)
        rw [Mettapedia.Languages.MeTTa.SubstitutionAlgebra.subst_empty, argumentRead]
        exact parameterRead.trans capture
      exact List.forall₂_zip aligned inside
  · intro equation inside
    obtain rfl := List.mem_singleton.mp inside
    exact copied.trans materialized.symm

variable [DecidableEq O] [DecidableEq R]

/-- The concrete openings also make both existing held-read microsteps fresh.
No groundness restriction is introduced during materialization or consumption. -/
theorem stages_fresh (selected : R) (temporary output : O)
    (ambient : Set (HeldReadEncoding.Code (Terms Atom))) (present : selected ∈ rows) :
    (HeldReadGenericFirings.datum ordinary rows closures (E := E) selected PUnit.unit
      (opening (bound ordinary rows closures) 1) temporary).Fresh X ∧
    (HeldReadGenericFirings.consumer ordinary rows closures (E := E) selected PUnit.unit
      (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
      X temporary output).Fresh X :=
  HeldReadGenericFirings.staged_fresh_of_direct (E := E) X ordinary rows closures selected PUnit.unit
    (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
    temporary output ambient present (direct_fresh ordinary rows closures selected output)

/-- After constructing the openings, the remaining obligations are exactly
capture arity, physical availability, a new output occurrence and consistent
matching information. Freshness is no longer an assumed solver certificate. -/
theorem direct_admits_iff (selected : R) (output : O) :
    (direct ordinary rows closures selected output).Admits X ↔
      (closures selected).WellFormed ∧ selected ∈ rows ∧ output ∉ ordinary.present ∧
        X.Solvable ((direct ordinary rows closures selected output).information X) := by
  constructor
  · intro admitted
    exact (HeldReadGenericFirings.direct_admission_data (E := E) X ordinary rows closures
      selected PUnit.unit (opening (bound ordinary rows closures) 0)
      (opening (bound ordinary rows closures) 1) output admitted).2
  · rintro ⟨wellFormed, present, outputFresh, solvable⟩
    refine ⟨HeldReadGenericFirings.direct_shapes (E := E) X ordinary rows closures selected PUnit.unit
      (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
      output (direct_fresh ordinary rows closures selected output) wellFormed,
      HeldReadGenericFirings.direct_enabled (E := E) ordinary rows closures selected PUnit.unit
        (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
        output present outputFresh, solvable, ?_⟩
    intro target assignment _
    exact HeldReadGenericFirings.direct_holds (E := E) X ordinary rows closures selected PUnit.unit
      (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
      output assignment

/-- A consistent concrete read has an actual two-event held execution. The
persistent schemas survive and its private materialization occurrence does not.
Chronological events are retained rather than equated with one silent step. -/
theorem execution_of_solvable (selected : R) (temporary output : O)
    (ambient : Set (HeldReadEncoding.Code (Terms Atom)))
    (available : Sum.inr (HeldReadGenericFirings.consumeRule (closures selected).schema) ∈ ambient)
    (wellFormed : (closures selected).WellFormed) (present : selected ∈ rows)
    (outputFresh : output ∉ ordinary.present) (temporaryFresh : temporary ∉ ordinary.present)
    (different : temporary ≠ output)
    (solvable : X.Solvable ((direct ordinary rows closures selected output).information X)) :
    ∃ run : (HeldReadGenericFirings.protocolMachine (E := E) (O := O) (R := R) X ambient).Run
        (hosted ordinary rows closures),
      run.word.length = 2 ∧
      run.last = (HeldReadGenericFirings.consumer ordinary rows closures (E := E) selected PUnit.unit
        (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
        X temporary output).result X ∧
      run.last.present = ordinary.present ∪ {output} ∧ run.last.rules = rows ∧
        temporary ∉ run.last.present :=
  HeldReadGenericFirings.execution_of_direct (E := E) X ordinary rows closures selected PUnit.unit
    (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
    temporary output ambient available temporaryFresh different
    ((direct_admits_iff ordinary rows closures selected output).mpr
      ⟨wellFormed, present, outputFresh, solvable⟩)

/-- An independently supplied closure reading is realized by a concrete
two-event execution with the same final value and a model of its final
information. Neither a ground store nor a pre-assumed admitted run is used. -/
theorem execution_of_reading (selected : R) (temporary output : O)
    (ambient : Set (HeldReadEncoding.Code (Terms Atom)))
    (available : Sum.inr (HeldReadGenericFirings.consumeRule (closures selected).schema) ∈ ambient)
    (present : selected ∈ rows) (outputFresh : output ∉ ordinary.present)
    (temporaryFresh : temporary ∉ ordinary.present) (different : temporary ≠ output)
    (caller : Subst) (known : X.Models (b := PUnit.unit) caller ordinary.knowledge) (value : Atom)
    (reading : (closures selected).ReadsAt X (b := PUnit.unit) caller value) :
    ∃ (run : (HeldReadGenericFirings.protocolMachine (E := E) (O := O) (R := R) X ambient).Run
        (hosted ordinary rows closures)) (assignment : Subst),
      run.word.length = 2 ∧ X.Models (b := PUnit.unit) assignment run.last.knowledge ∧
      subst assignment (run.last.label output) = value ∧
      run.last.present = ordinary.present ∪ {output} ∧ run.last.rules = rows ∧
        temporary ∉ run.last.present := by
  obtain ⟨assignment, solved, _, outputValue⟩ := direct_model_of_reading ordinary rows closures
    selected output caller present known value reading
  obtain ⟨run, length, last, presentAfter, rulesAfter, privateAbsent⟩ :=
    execution_of_solvable ordinary rows closures selected temporary output ambient available
      (Closure.wellFormed_of_readsAt X _ caller reading) present outputFresh temporaryFresh different
      ⟨PUnit.unit, assignment, solved⟩
  refine ⟨run, assignment, length, ?_, ?_, presentAfter, rulesAfter, privateAbsent⟩
  · rw [last]
    change X.Models (b := PUnit.unit) assignment
      ((HeldReadGenericFirings.consumer ordinary rows closures (E := E) selected PUnit.unit
        (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1)
        X temporary output).information X)
    rw [HeldReadGenericFirings.information_eq (E := E) X ordinary rows closures selected PUnit.unit
      (opening (bound ordinary rows closures) 0) (opening (bound ordinary rows closures) 1) temporary output]
    exact solved
  · rw [last, HeldReadGenericFirings.consumer_output_label (E := E) X ordinary rows closures
      selected PUnit.unit (opening (bound ordinary rows closures) 0)
      (opening (bound ordinary rows closures) 1) temporary output]
    exact outputValue

end Mettapedia.Languages.MeTTa.PeTTa.AtomSchematicReads
