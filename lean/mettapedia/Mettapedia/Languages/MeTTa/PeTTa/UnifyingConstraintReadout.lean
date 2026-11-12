import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanConstraintAdmission
import Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout
import Mettapedia.Logic.LP.MutualInstantiation

/-!
# Actual source solver and solved runtime bindings have the same joint readout

The runtime environment earns its most-general property from the proved
constraint presentation. The independent source solver supplies its existing
MGU theorem. Their actual representatives therefore differ only by uniform
variable renamings, including observations shared across several values.
Display labels remain distinct from executable identities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open EagerDFS
open OutputPlan.ConstraintAdmission

theorem encode_environment (bindings : Subst) (term : Atom) :
    Destination.encode (Unifying.resolve bindings term) =
      Mettapedia.Logic.LP.Subst.applyTerm (environment bindings) (Destination.encode term) := by
  calc
    Destination.encode (Unifying.resolve bindings term) =
        Destination.encode (Destination.read (environment bindings) term) :=
      congrArg Destination.encode (read_environment bindings term).symm
    _ = Mettapedia.Logic.LP.Subst.applyTerm (environment bindings) (Destination.encode term) :=
      encode_read _ _

theorem environment_factorizes_models (bindings : Subst) (model : Destination.Environment)
    (solved : Destination.Solves model (presentation bindings)) :
    (environment bindings).moreGeneral model := by
  refine ⟨model,?_⟩
  intro name
  have absorbed := absorbs_of_solves model bindings solved (.var name)
  have encoded := congrArg Destination.encode absorbed
  rw [encode_read,encode_read,encode_environment] at encoded
  simp only [Destination.encode,Mettapedia.Logic.LP.Subst.applyTerm_var] at encoded
  exact encoded.symm

theorem environment_is_most_general (constraints : Destination.Equations) (bindings : Subst)
    (represented : Represents constraints bindings) (valid : Unifying.Idempotent bindings) :
    Destination.Solves (environment bindings) constraints ∧
      ∀ model, Destination.Solves model constraints → (environment bindings).moreGeneral model := by
  exact ⟨(represented _).mpr (environment_models_presentation bindings valid),
    fun model solved => environment_factorizes_models bindings model ((represented _).mp solved)⟩

theorem source_runtime_mgus (constraints : Destination.Equations) (bindings : Subst)
    (model : Destination.Environment) (represented : Represents constraints bindings)
    (valid : Unifying.Idempotent bindings) (resolved : Destination.resolve constraints = some model) :
    model.moreGeneral (environment bindings) ∧ (environment bindings).moreGeneral model := by
  obtain ⟨nativeSolved,nativeGeneral⟩ := environment_is_most_general constraints bindings represented valid
  exact ⟨Mettapedia.Logic.LP.unifyTotal_mgu (Destination.equations constraints) model resolved
      (environment bindings) ((Destination.solves_iff_unifies _ _).mp nativeSolved),
    nativeGeneral model (Destination.resolve_sound resolved)⟩

theorem decode_rename (names : String → String) (term : Destination.Value) :
    Destination.decode (Mettapedia.Logic.LP.UnificationRenaming.rename names term) =
      Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming.rename names (Destination.decode term) := by
  induction term with
  | var name => rfl
  | const scalar => cases scalar <;> rfl
  | app head children ih =>
      simp only [Mettapedia.Logic.LP.UnificationRenaming.rename_app,Destination.decode,
        Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming.rename,
        Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming.list_eq_map]
      apply congrArg Atom.expression
      apply List.ext_getElem
      · simp
      · intro index firstBound secondBound
        simp only [List.getElem_ofFn,List.getElem_map,ih]

/-- One pair of maps serves every observation, preserving sharing with
other returned values, saved callers and stored terms in the same bundle. -/
theorem source_runtime_renamings (constraints : Destination.Equations) (bindings : Subst)
    (model : Destination.Environment) (represented : Represents constraints bindings)
    (valid : Unifying.Idempotent bindings) (resolved : Destination.resolve constraints = some model) :
    ∃ names inverse : String → String, ∀ term,
      Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming.rename names (Destination.read model term) =
          Unifying.resolve bindings term ∧
        Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming.rename inverse (Unifying.resolve bindings term) =
          Destination.read model term := by
  obtain ⟨one,two⟩ := source_runtime_mgus constraints bindings model represented valid resolved
  obtain ⟨names,inverse,allTerms⟩ :=
    Mettapedia.Logic.LP.MutualInstantiation.mutually_general_renamings model (environment bindings) one two
  refine ⟨names,inverse,?_⟩
  intro term
  have forward := congrArg Destination.decode (allTerms (Destination.encode term)).1
  have backward := congrArg Destination.decode (allTerms (Destination.encode term)).2
  rw [decode_rename] at forward backward
  change Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming.rename names (Destination.read model term) =
    Destination.read (environment bindings) term at forward
  change Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming.rename inverse (Destination.read (environment bindings) term) =
    Destination.read model term at backward
  rw [read_environment] at forward backward
  exact ⟨forward,backward⟩

theorem source_runtime_readout_variant (constraints : Destination.Equations) (bindings : Subst)
    (model : Destination.Environment) (represented : Represents constraints bindings)
    (valid : Unifying.Idempotent bindings) (resolved : Destination.resolve constraints = some model) (term : Atom) :
    Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming.Variant
      (Destination.read model term) (Unifying.resolve bindings term) := by
  obtain ⟨names,inverse,allTerms⟩ := source_runtime_renamings constraints bindings model represented valid resolved
  exact ⟨names,inverse,(allTerms term).1,(allTerms term).2⟩

theorem source_runtime_joint_readout (constraints : Destination.Equations) (bindings : Subst)
    (model : Destination.Environment) (represented : Represents constraints bindings)
    (valid : Unifying.Idempotent bindings) (resolved : Destination.resolve constraints = some model)
    (observations : List Atom) :
    Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint (observations.map (Destination.read model)) =
      Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint (observations.map (Unifying.resolve bindings)) := by
  have variant := source_runtime_readout_variant constraints bindings model represented valid resolved (.expression observations)
  rw [read_expression,resolve_expression] at variant
  exact (Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint_equal_iff_variant _ _).mpr variant

theorem gate_joint_readout (before : Destination.Equations) (bindings bound : Subst) (left right : Atom)
    (represented : Represents before bindings) (valid : Unifying.Idempotent bindings)
    (unified : Unifying.unify bindings left (Unifying.resolve bindings right) = .ok bound)
    (model : Destination.Environment)
    (resolved : Destination.resolve (before ++ [(left,right)]) = some model) (observations : List Atom) :
    Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint (observations.map (Destination.read model)) =
      Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout.joint (observations.map (Unifying.resolve bound)) := by
  exact source_runtime_joint_readout (before ++ [(left,right)]) bound model
    (represents_after_gate before bindings bound left right represented valid unified)
    (Unifying.unifyTerms_sound _ bindings bound left (Unifying.resolve bindings right) valid unified).1 resolved observations

end Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation
