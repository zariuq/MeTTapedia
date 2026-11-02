import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessGuardCuts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessResources
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.List.TakeDrop

/-!
# Finite contextual event certificates with explicit equation cuts

An event is identified independently of its checking enumeration. Its cut is
a list of preceding event identities, whose actual per-use equations are
joined with the incoming constraints and its own delta. Guard admission uses
that reconstructed cut and the event's original watched world.

Compilation from prepared contextual schedules is exact and recovers the
original source endpoint when the cuts are accepted. Arbitrary event
enumeration is allowed for checking; constructing a different contextual
execution order still requires transporting activations and helper families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion

variable {S : Signature} {Local O V : Type} {locals : Local → MetaArity S}
  {declarations : V → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

structure CutProcess (locals : Local → MetaArity S) (O : Type)
    (declarations : V → MetaArity S) (Γ : Ctx S) (sort : S.Srt) where
  size : Nat
  event : Fin size → Event locals (O := O) declarations Γ sort
  cut : Fin size → List (Fin size)
  incoming : EquationStore (Term (signature S declarations) Γ sort)

namespace CutProcess

def problem (process : CutProcess locals O declarations Γ sort) (identity : Fin process.size) :
    EquationStore (Term (signature S declarations) Γ sort) :=
  process.incoming ++ addedAll ((process.cut identity).map process.event) ++ (process.event identity).added

def Admitted (process : CutProcess locals O declarations Γ sort) : Prop :=
  ∀ identity, ∀ check ∈ (process.event identity).rule.checks,
    ContextualGuardSemantics.Ask locals (process.problem identity)
      (process.event identity).guardRows (process.event identity).guardWorld check

def CheckEnumeration (process : CutProcess locals O declarations Γ sort)
    (enumeration : List (Fin process.size)) : Prop :=
  ∀ identity ∈ enumeration, ∀ check ∈ (process.event identity).rule.checks,
    ContextualGuardSemantics.Ask locals (process.problem identity)
      (process.event identity).guardRows (process.event identity).guardWorld check

theorem checking_order_does_not_change_admission
    (process : CutProcess locals O declarations Γ sort)
    {first second : List (Fin process.size)} (reordered : first.Perm second) :
    process.CheckEnumeration first ↔ process.CheckEnumeration second := by
  constructor
  · intro checked identity member
    exact checked identity (reordered.symm.subset member)
  · intro checked identity member
    exact checked identity (reordered.subset member)

theorem complete_enumeration_iff (process : CutProcess locals O declarations Γ sort)
    (enumeration : List (Fin process.size)) (complete : ∀ identity, identity ∈ enumeration) :
    process.CheckEnumeration enumeration ↔ process.Admitted := by
  constructor
  · intro checked identity
    exact checked identity (complete identity)
  · intro checked identity _member
    exact checked identity

def fromCatalogue (incoming : EquationStore (Term (signature S declarations) Γ sort))
    (catalogue : List (Event locals (O := O) declarations Γ sort)) : CutProcess locals O declarations Γ sort where
  size := catalogue.length
  event := catalogue.get
  cut identity := List.ofFn (Fin.castLE (Nat.le_of_lt identity.isLt))
  incoming := incoming

theorem catalogue_cut_views (incoming : EquationStore (Term (signature S declarations) Γ sort))
    (catalogue : List (Event locals (O := O) declarations Γ sort)) (identity : Fin catalogue.length) :
    (((fromCatalogue incoming catalogue).cut identity).map (fromCatalogue incoming catalogue).event) =
      catalogue.take identity.val := by
  change (List.ofFn (Fin.castLE (Nat.le_of_lt identity.isLt))).map catalogue.get = _
  rw [List.map_ofFn]
  exact Fin.ofFn_take_get catalogue (Nat.le_of_lt identity.isLt)

theorem original_problem_from_cut
    (incoming : EquationStore (Term (signature S declarations) Γ sort))
    (catalogue : List (Event locals (O := O) declarations Γ sort))
    (cuts : OriginalCuts incoming catalogue) (identity : Fin catalogue.length) :
    (fromCatalogue incoming catalogue).problem identity = (catalogue.get identity).problem := by
  unfold problem
  rw [catalogue_cut_views]
  have split : catalogue = catalogue.take identity.val ++
      catalogue.get identity :: catalogue.drop (identity.val + 1) := by
    rw [List.cons_get_drop_succ, List.take_append_drop]
  rw [split] at cuts
  exact cuts.at_cut.symm

theorem admitted_iff_original_catalogue
    (incoming : EquationStore (Term (signature S declarations) Γ sort))
    (catalogue : List (Event locals (O := O) declarations Γ sort))
    (cuts : OriginalCuts incoming catalogue) :
    (fromCatalogue incoming catalogue).Admitted ↔ Checked locals catalogue := by
  constructor
  · intro admitted event member
    obtain ⟨identity, rfl⟩ := List.mem_iff_get.mp member
    intro check present
    have asked := admitted identity check present
    rw [original_problem_from_cut incoming catalogue cuts identity] at asked
    exact asked
  · intro checked identity check present
    rw [original_problem_from_cut incoming catalogue cuts identity]
    exact checked (catalogue.get identity) (List.get_mem _ _) check present

end CutProcess

variable [DecidableEq O] [DecidableEq Local]
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

def cutProcess {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) : CutProcess locals O target.declarations Γ sort :=
  CutProcess.fromCatalogue (incomingProblem certificate) (events certificate)

theorem cut_process_acceptance_exact {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) :
    (cutProcess certificate).Admitted ↔ ContextualSchedulePromotion.Checked locals certificate.questions :=
  (CutProcess.admitted_iff_original_catalogue _ _ (original_cuts_preserved certificate)).trans
    (events_checked_iff certificate)

theorem accepted_cut_process_has_original_execution {source target : Endpoint locals O Γ sort}
    (certificate : Certificate locals source target) (accepted : (cutProcess certificate).Admitted) :
    ∃ path : Quiver.Path source target,
      ContextualExecution.selections path = certificate.selections ∧
        ContextualExecution.fuels path = certificate.fuels := by
  have checked := (cut_process_acceptance_exact certificate).mp accepted
  exact ⟨certificate.realize checked, Certificate.realize_selections certificate checked,
    Certificate.realize_fuels certificate checked⟩

theorem actual_execution_supplies_an_accepted_cut_process {source target : Endpoint locals O Γ sort}
    (path : Quiver.Path source target) :
    ∃ certificate : Certificate locals source target,
      (cutProcess certificate).Admitted ∧
        certificate.selections = ContextualExecution.selections path ∧
        certificate.fuels = ContextualExecution.fuels path := by
  obtain ⟨certificate, checked, selected, spent⟩ := Certificate.recover path
  exact ⟨certificate, (cut_process_acceptance_exact certificate).mpr checked, selected, spent⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProcessCatalogue
