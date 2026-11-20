import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeInstanceFields
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore

/-!
# Certificate origins in the original prepared field program

Every made row of the actual twenty-nine-schema program is a field cell.
A live certificate after any admitted firing therefore retains its old
occurrence identity and payload under the actual frame pullback. The same
holds over finite runs. This is a boundary of the prepared program; it adds
no certificate producer, request protocol or native consumer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativePreparedCertificateOrigins

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeFieldSchema InterpretedFrames NativeInstanceFields

attribute [local irreducible] NativeClauseData.signature

universe w u

variable {ops : Operations} (table : Fin 29 → Syntax ops)
  (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (domains : model.InhabitedDomains)
  (profile : NativeInstanceFields.Profile table model)

abbrev Certificate := Σ index : Fin 29, Locals table model profile index

abbrev nativeStep (O : Type u) [DecidableEq O] :=
  (RuleSyntax.step (frames (NativeInstanceFields.Value table model profile)) O extensions
    (NativeInstanceFields.program table model domains profile)).toStep

variable {O : Type u} [DecidableEq O]

omit [DecidableEq O] in
/-- This follows from actual program membership and opened templates,
without a supplied certificate-production condition. -/
theorem opened_produce_not_certificate
    {state : RuleSyntax.State (Terms (NativeInstanceFields.Value table model profile)) O}
    (firing : RuleSyntax.Firing O extensions (NativeInstanceFields.program table model domains profile) state.frame)
    {term : Terms (NativeInstanceFields.Value table model profile) (extensions.target firing.ext)}
    (member : term ∈ (firing.opened (frames (NativeInstanceFields.Value table model profile))).produce)
    (environment : (extensions.target firing.ext).Carrier) (certificate : Certificate table model profile) :
    term environment ≠ Sum.inr certificate := by
  rcases firing with ⟨rule, memberRule, extension, opening, selection, seen⟩
  change ∃ index, (NativeInstanceFields.schema table model domains profile index).rule = rule at memberRule
  obtain ⟨index, rfl⟩ := memberRule
  change term ∈ (((table index).writes.map
    (NativeInstanceFields.cell table model domains profile index (table index).after)).map
      (fun term => Function.comp term opening)) at member
  rw [List.map_map] at member
  obtain ⟨field, _, same⟩ := List.mem_map.mp member
  rw [← same]
  intro impossible
  cases impossible

/-- The payload and physical identity both come from the old state.
The statement holds at every environment, hence also at every satisfying
result point. It imposes no canonical-opening or ground-state restriction. -/
theorem firing_certificate_origin
    {state : RuleSyntax.State (Terms (NativeInstanceFields.Value table model profile)) O}
    (firing : RuleSyntax.Firing O extensions (NativeInstanceFields.program table model domains profile) state.frame)
    (admitted : (nativeStep table model domains profile O).Admits (s := state) firing)
    (environment : (extensions.target firing.ext).Carrier) (occurrence : O)
    (certificate : Certificate table model profile)
    (present : occurrence ∈ (firing.result (frames (NativeInstanceFields.Value table model profile)) state).present)
    (labelled : (firing.result (frames (NativeInstanceFields.Value table model profile)) state).label
      occurrence environment = Sum.inr certificate) :
    occurrence ∈ state.present ∧ occurrence ∉ firing.selection.taken ∧ occurrence ∉ firing.selection.made ∧
      state.label occurrence (extensions.weaken firing.ext environment) = Sum.inr certificate := by
  have shapes : firing.Shapes (frames (NativeInstanceFields.Value table model profile)) state := admitted.1
  have notMade : occurrence ∉ firing.selection.made := by
    intro made
    have lengths : firing.selection.made.length =
        (firing.opened (frames (NativeInstanceFields.Value table model profile))).produce.length := by
      simpa only [RuleSyntax.Firing.opened, RuleInstance.map, List.length_map] using shapes.2.2.2.2.2.1.symm
    obtain ⟨term, inside⟩ := RuleSyntax.SetStore.zip_left lengths made
    have same := congrFun (firing.result_label_made (X := frames (NativeInstanceFields.Value table model profile)) shapes inside) environment
    exact opened_produce_not_certificate table model domains profile firing (List.of_mem_zip inside).2
      environment certificate (same.symm.trans labelled)
  have retained : occurrence ∈ state.present \ firing.selection.taken.toFinset := by
    change occurrence ∈ (state.present \ firing.selection.taken.toFinset) ∪ firing.selection.made.toFinset at present
    rcases Finset.mem_union.mp present with old | made
    · exact old
    · exact False.elim (notMade (List.mem_toFinset.mp made))
  have same := congrFun (firing.result_label_other (X := frames (NativeInstanceFields.Value table model profile)) notMade) environment
  exact ⟨(Finset.mem_sdiff.mp retained).1,
    fun taken => (Finset.mem_sdiff.mp retained).2 (List.mem_toFinset.mpr taken), notMade, same.symm.trans labelled⟩

/-- No actual finite run can create a certificate identity or change the
payload of a retained certificate along its frame morphism. -/
theorem run_certificate_origin :
    ∀ {state : RuleSyntax.State (Terms (NativeInstanceFields.Value table model profile)) O}
      (run : (nativeStep table model domains profile O).Run state)
      (environment : run.last.frame.Carrier) (occurrence : O) (certificate : Certificate table model profile),
      occurrence ∈ run.last.present → run.last.label occurrence environment = Sum.inr certificate →
        occurrence ∈ state.present ∧ state.label occurrence (run.toLast environment) = Sum.inr certificate
  | _, .nil _, environment, occurrence, certificate, present, labelled => ⟨present, labelled⟩
  | state, .cons firing admitted rest, environment, occurrence, certificate, present, labelled => by
      obtain ⟨atMiddle, readMiddle⟩ := run_certificate_origin rest environment occurrence certificate present labelled
      have origin := firing_certificate_origin table model domains profile firing admitted
        (rest.toLast environment) occurrence certificate atMiddle readMiddle
      exact ⟨origin.1, origin.2.2.2⟩

omit [DecidableEq O] in
/-- At an actual prepared snapshot every later certificate has the sole
original certificate identity and its original index, locals and effect. -/
theorem snapshot_run_certificate_origin (index : Fin 29)
    (values : Locals table model profile index) (generation : Field → Nat)
    (run : (nativeStep table model domains profile NativeFieldExecution.Occurrence).Run
      (NativeInstanceFields.snapshot table model domains profile index values generation))
    (environment : run.last.frame.Carrier) (occurrence : NativeFieldExecution.Occurrence)
    (certificate : Certificate table model profile)
    (present : occurrence ∈ run.last.present)
    (labelled : run.last.label occurrence environment = Sum.inr certificate) :
    occurrence = NativeFieldExecution.certificate ∧ certificate = ⟨index, values⟩ := by
  obtain ⟨_, original⟩ := run_certificate_origin table model domains profile run environment occurrence certificate present labelled
  cases occurrence with
  | inl field => cases original
  | inr token =>
      cases token
      exact ⟨rfl, (Sum.inr.inj original).symm⟩

omit [DecidableEq O] in
/-- Removing the actual certificate cannot be repaired by any finite run
of these field schemas. No producer rule occurs in this program. -/
theorem withoutCertificate_run_no_certificate (index : Fin 29)
    (values : Locals table model profile index) (generation : Field → Nat)
    (run : (nativeStep table model domains profile NativeFieldExecution.Occurrence).Run
      (NativeInstanceFields.withoutCertificate table model domains profile index values generation))
    (environment : run.last.frame.Carrier) (occurrence : NativeFieldExecution.Occurrence)
    (certificate : Certificate table model profile) (present : occurrence ∈ run.last.present) :
    run.last.label occurrence environment ≠ Sum.inr certificate := by
  intro labelled
  obtain ⟨oldPresent, original⟩ := run_certificate_origin table model domains profile run environment occurrence certificate present labelled
  cases occurrence with
  | inl field => cases original
  | inr token =>
      cases token
      simp [NativeInstanceFields.withoutCertificate, NativeFieldExecution.certificate] at oldPresent

omit [DecidableEq O] in
/-- Conditional positive control: the actual case guard and profile check
earn a one-firing run, and its certificate is retained. This does not assert
a new closed HOL case or implement certificate production. -/
theorem prepared_guarded_run_retains_certificate (index : Fin 29)
    (values : Locals table model profile index) (generation : Field → Nat)
    (guard : (model.denote (table index).guard values.1).down)
    (permitted : profile.holds index values.1 values.2) :
    ∃ run : (nativeStep table model domains profile NativeFieldExecution.Occurrence).Run
        (NativeInstanceFields.snapshot table model domains profile index values generation),
      run.word.length = 1 ∧ NativeFieldExecution.certificate ∈ run.last.present ∧
        ∀ environment : run.last.frame.Carrier,
          run.last.label NativeFieldExecution.certificate environment = Sum.inr (⟨index, values⟩ : Certificate table model profile) := by
  let selected := NativeInstanceFields.firing table model domains profile index generation
  let initial := NativeInstanceFields.snapshot table model domains profile index values generation
  have admitted : (nativeStep table model domains profile NativeFieldExecution.Occurrence).Admits (s := initial) selected :=
    (NativeInstanceFields.admitted_iff table model domains profile index values generation).mpr ⟨guard, permitted⟩
  have notTaken : NativeFieldExecution.certificate ∉ selected.selection.taken := by
    change NativeFieldExecution.certificate ∉ (table index).writes.map (NativeFieldExecution.row generation)
    intro inside
    obtain ⟨field, _, same⟩ := List.mem_map.mp inside
    cases same
  have notMade : NativeFieldExecution.certificate ∉ selected.selection.made := by
    change NativeFieldExecution.certificate ∉ (table index).writes.map (NativeFieldExecution.nextRow generation)
    intro inside
    obtain ⟨field, _, same⟩ := List.mem_map.mp inside
    cases same
  refine ⟨.cons selected admitted (.nil _), rfl, ?_, ?_⟩
  · change NativeFieldExecution.certificate ∈
      (initial.present \ selected.selection.taken.toFinset) ∪ selected.selection.made.toFinset
    apply Finset.mem_union_left
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, fun inside => notTaken (List.mem_toFinset.mp inside)⟩
  · intro environment
    exact congrFun (RuleSyntax.Firing.result_label_other
      (X := frames (NativeInstanceFields.Value table model profile)) (s := initial) selected notMade) environment

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativePreparedCertificateOrigins
