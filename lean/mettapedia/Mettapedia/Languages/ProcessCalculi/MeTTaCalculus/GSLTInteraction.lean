import Mettapedia.GSLT.LanguageDef.SemanticCategory
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedControls
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedResidual
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CorrectedReflection

/-!
# MeTTa-calculus as an interactive GSLT

The MeTTa-calculus authors its `COMM` relation as a rewrite over a bare
parallel hash-bag.  This module selects that exact sort, constructor, and
rewrite through the generic interactive-GSLT interface.  The selected contact
data form a structural boundary.

The behavioral theory `mettaCalcGSLT` is the corrected relational semantics
`Corrected.Step Corrected.uniform`: the manuscript's COMM, PAR, EQUIV and
REFL, with the variable convention on COMM and the uniform dot (a principal
binding list that names every pattern variable), over the processes of the
calculus fragment, with alpha-equivalence as its equations. The corrected
executable step computes it: every executable reduct that is a calculus
process is a step (`executable_step_to_mettaCalcGSLT`), on the closing
fragment every step is an executable reduct up to alpha
(`closing_step_executes`), and on guard-free patterns every step is an
executable reduct up to renaming its residual names
(`uniform_step_executes_up_to_renaming`). Modulo the bag laws, with REFL
quoting the canonical representative of its reduct, `mettaCalcBagGSLT` makes
the order of a parallel composition unobservable, and the step with canonical
reflection is complete for it on the closing fragment
(`closing_bag_step_executes`). An
executable reduct can also keep a guard of a continuation in closed form,
with codes for its bound variables; such a reduct is not itself a term of the
GSLT.

The theory presented from the authored definition by the generic engine has
closed ground terms as its carrier, which contain no pattern variable; it can
express neither binding nor the capture the correction removes, so it is not
used as the behavioral theory here.

Persistent space observation and linear contact remain distinct access modes,
as proved in `SpaceChannelBoundary` and `SpaceInteraction`.
-/

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.GSLTInteraction

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm (pvars)

/-- The exact validated five-field MeTTa-calculus definition. -/
def mettaCalcValidatedLanguageDef : ValidatedLanguageDef :=
  ⟨mettaCalc, mettaCalc_validate_eq_nil⟩

/-- The authored process sort. -/
def mettaCalcProcessSort : DeclaredSort mettaCalcValidatedLanguageDef :=
  ⟨mettaCalc.types[0], by
    change List.Mem mettaCalc.types[0] mettaCalc.types
    exact List.getElem_mem (by simp [mettaCalc])⟩

/-- The authored bare hash-bag constructor used by `pPar`. -/
def mettaCalcParallelConstructor :
    DeclaredConstructor mettaCalcValidatedLanguageDef :=
  ⟨mettaCalc.terms[1], by
    change List.Mem mettaCalc.terms[1] mettaCalc.terms
    exact List.getElem_mem (by simp [mettaCalc])⟩

/-- The authored symmetric communication rewrite. -/
def mettaCalcCommRewrite : DeclaredRewrite mettaCalcValidatedLanguageDef :=
  ⟨mettaCalc.rewrites[0], by
    change List.Mem mettaCalc.rewrites[0] mettaCalc.rewrites
    exact List.getElem_mem (by simp [mettaCalc])⟩

/-- The MeTTa-calculus interaction selection, retaining the sole authored
language definition verbatim. -/
def mettaCalcInteractivePresentation : InteractivePresentation where
  presentation := mettaCalcValidatedLanguageDef
  interactingSort := mettaCalcProcessSort
  contactConstructor := mettaCalcParallelConstructor
  interactionRewrite := mettaCalcCommRewrite
  contactRepresentation := .collection .hashBag
  representsContact := by rfl
  interactionHeaded := by
    simp [InteractionHeaded, mettaCalcCommRewrite, mettaCalc, commSymRule]

/-- The processes of the calculus fragment. -/
abbrev CalcProc := { process : Pattern // Corrected.calcTerm process = true }

/-- Alpha-equivalence of calculus processes: equal closed forms. -/
def alphaSetoid : Setoid CalcProc where
  r left right := Corrected.AlphaEq left.1 right.1
  iseqv := ⟨fun process => Corrected.AlphaEq.refl process.1, fun same => same.symm,
    fun first second => first.trans second⟩

/-- **The behavioral GSLT of the MeTTa-calculus**: calculus processes,
alpha-equivalence as `E`, and the corrected relational step, with the
variable convention and the uniform dot on COMM, as `R`. The interactive
presentation above only selects its contact interface. -/
def mettaCalcGSLT : GSLT where
  Term := CalcProc
  equations := alphaSetoid
  rewrites source target := Corrected.Step Corrected.uniform source.1 target.1
  rewrites_resp_left := by
    intro source source' target same step
    exact ⟨target, .congruence (Corrected.AlphaEq.symm same) step (Corrected.AlphaEq.refl _),
      Corrected.AlphaEq.refl _⟩
  rewrites_resp_right := by
    intro source target target' step same
    exact .congruence (Corrected.AlphaEq.refl _) step same

/-- Every reduct of the corrected executable step that is a calculus process
is a step of the GSLT. -/
theorem executable_step_to_mettaCalcGSLT {source target : CalcProc}
    (executes : target.1 ∈ Corrected.cstep source.1) :
    mettaCalcGSLT.Step source target :=
  Corrected.cstep_sound_uniform source.2 executes

/-- On the closing fragment every relational step is a reduct of the corrected
executable step, up to alpha. Outside it the manuscript's dot depends on which
most general unifier is chosen, and no converse is asserted. -/
theorem closing_step_executes {source target : CalcProc}
    (step : Corrected.Step Corrected.closing source.1 target.1) :
    ∃ reduct ∈ Corrected.cstep source.1, Corrected.AlphaEq reduct target.1 :=
  Corrected.cstep_complete step

/-- On guard-free patterns, every step of the GSLT is a reduct of the corrected
executable step up to renaming its residual names: the renaming fixes every
free name of the source and is injective on the reduct's fresh names. -/
theorem uniform_step_executes_up_to_renaming {source target : CalcProc}
    (step : Corrected.Step Corrected.uniformCalc source.1 target.1) :
    ∃ reduct ∈ Corrected.cstep source.1, ∃ ρ : String → String,
      (∀ z ∈ pvars (Corrected.close source.1), ρ z = z) ∧
      (∀ a ∈ pvars reduct, ∀ b ∈ pvars reduct, a ∉ pvars (Corrected.close source.1) →
        b ∉ pvars (Corrected.close source.1) → ρ a = ρ b → a = b) ∧
      Corrected.AlphaEq (Corrected.rename ρ reduct) target.1 :=
  Corrected.cstep_complete_residual step

/-! ## Modulo the bag laws -/

/-- Equality modulo the bag laws, on calculus processes. -/
def bagSetoid : Setoid CalcProc where
  r left right := Corrected.BagEq left.1 right.1
  iseqv := ⟨fun process => Corrected.BagEq.refl process.1, fun same => same.symm,
    fun first second => first.trans second⟩

/-- **The MeTTa-calculus modulo the bag laws**: calculus processes, the bag laws
as `E`, and the relational semantics with the uniform dot and with REFL quoting
the canonical representative of its reduct as `R`. The order of a parallel
composition is unobservable, its multiplicity is not. -/
def mettaCalcBagGSLT : GSLT where
  Term := CalcProc
  equations := bagSetoid
  rewrites source target := Corrected.CanonicalBagStep Corrected.uniform source.1 target.1
  rewrites_resp_left := by
    intro source source' target same step
    exact ⟨target, .congruence (Corrected.BagEq.symm same) step (Corrected.BagEq.refl _),
      Corrected.BagEq.refl _⟩
  rewrites_resp_right := by
    intro source target target' step same
    exact .congruence (Corrected.BagEq.refl _) step same

/-- Every reduct of the step with canonical reflection that is a calculus
process is a step of the bag-law GSLT. -/
theorem executable_step_to_mettaCalcBagGSLT {source target : CalcProc}
    (executes : target.1 ∈ Corrected.cstepCanon source.1) :
    mettaCalcBagGSLT.Step source target :=
  Corrected.cstepCanon_sound_uniform source.2 executes

/-- On the closing fragment every step of the bag-law semantics, REFL included,
is a reduct of the step with canonical reflection, up to the bag laws. -/
theorem closing_bag_step_executes {source target : CalcProc}
    (step : Corrected.CanonicalBagStep Corrected.closing source.1 target.1) :
    ∃ reduct ∈ Corrected.cstepCanon source.1, Corrected.BagEq reduct target.1 :=
  Corrected.cstepCanon_complete step

/-- The two orders of a composition are one term of the bag-law GSLT, and two
equivalent reflected processes reach the same listener. -/
theorem mettaCalcBagGSLT_order_unobservable (p q : Pattern) :
    Corrected.BagEq (par p q) (par q p) ∧
      Corrected.listener demoChan (par p q) = Corrected.listener demoChan (par q p) :=
  ⟨Corrected.BagEq.par_comm p q, Corrected.reflect_listener_canonical demoChan (Corrected.BagEq.par_comm p q)⟩

/-- Positive control: the canary communicates in the GSLT, to `@0 | a`. -/
theorem mettaCalcGSLT_canary :
    mettaCalcGSLT.Step ⟨demoCommSource, by decide +kernel⟩
      ⟨par (nQuote pZero) (.fvar "a"), by decide +kernel⟩ :=
  executable_step_to_mettaCalcGSLT (by decide +kernel)

/-- Negative control: the capturing reduct `@0 | @0` of the naive reading is
not a step of the GSLT. -/
theorem mettaCalcGSLT_no_capture :
    ¬ mettaCalcGSLT.Step ⟨demoCommSource, by decide +kernel⟩ ⟨demoCommCapture, by decide +kernel⟩ :=
  fun step => Corrected.Controls.capture_not_conventional_step (step.mono Corrected.uniform_conventional)

/-- No step starts from a process whose closed form is inert. -/
theorem step_source_not_inert {admit : Corrected.Admission} {source target : Pattern}
    (step : Corrected.Step admit source target) : Corrected.close source ≠ pZero := by
  induction step with
  | comm t u x A B bs _ _ =>
      intro inert
      unfold Corrected.close at inert
      rw [Corrected.closeIn_par] at inert
      simp [par, pPar, pZero] at inert
  | parallel surrounding _ _ =>
      intro inert
      unfold Corrected.close at inert
      rw [Corrected.closeIn_par] at inert
      simp [par, pPar, pZero] at inert
  | congruence before _ _ ih =>
      exact fun inert => ih ((show Corrected.close _ = Corrected.close _ from before).symm.trans inert)
  | reflect x _ _ =>
      intro inert
      unfold Corrected.close at inert
      rw [Corrected.closeIn_pReflect] at inert
      simp [pReflect, pZero] at inert

/-- Negative control: the inert process is a normal form of the GSLT. -/
theorem mettaCalcGSLT_inert : mettaCalcGSLT.IsNormalForm ⟨pZero, by decide +kernel⟩ := by
  rintro ⟨target, step⟩
  exact step_source_not_inert step (Corrected.closeIn_pZero [])

theorem mettaCalc_contact_constructor_label :
    mettaCalcInteractivePresentation.contactConstructor.1.label = "MPar" := by
  rfl

theorem mettaCalc_interaction_rewrite_name :
    mettaCalcInteractivePresentation.interactionRewrite.1.name = "CommSym" := by
  rfl

/-- Positive control: symmetric `COMM` is selected as collection contact. -/
theorem mettaCalc_comm_interaction_headed :
    InteractionHeaded
      mettaCalcInteractivePresentation.contactRepresentation
      mettaCalcInteractivePresentation.contactConstructor.1
      mettaCalcInteractivePresentation.interactionRewrite.1.left :=
  mettaCalcInteractivePresentation.interactionHeaded

/-- Negative control: procedural reflection is not itself a contact source. -/
theorem mettaCalc_reflection_not_interaction_headed (name process : Pattern) :
    ¬ InteractionHeaded
      mettaCalcInteractivePresentation.contactRepresentation
      mettaCalcInteractivePresentation.contactConstructor.1
      (pReflect name process) := by
  simp [mettaCalcInteractivePresentation, pReflect, InteractionHeaded]

/-! ## Exact commonality and exact difference with rho -/

/-- MeTTa-calculus and rho select the same bare hash-bag representation for
binary contact.  This is a shared interaction shape, not an identification of
their rewrite rules. -/
theorem mettaCalc_rho_contact_representation_agrees :
    mettaCalcInteractivePresentation.contactRepresentation =
      rhoInteractivePresentation.contactRepresentation := by
  rfl

/-- The selected interactions remain different authored rules: symmetric
unification contact is not rho's asymmetric input/output communication. -/
theorem mettaCalc_rho_interaction_rewrites_distinct :
    mettaCalcInteractivePresentation.interactionRewrite.1.name ≠
      rhoInteractivePresentation.interactionRewrite.1.name := by
  rw [mettaCalc_interaction_rewrite_name]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.GSLTInteraction
