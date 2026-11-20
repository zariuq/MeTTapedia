import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationRoundStages
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationClosure

/-!
# One coherent execution realizes all DTL stages and their limit

Every finite prefix extends the preceding actual run, at one retained caller
interpretation. Its reading set is exactly the corresponding immediate-
consequence stage. The union of this one chain, rather than a union of
unrelated existential executions, is exactly DTL derivability.

The scheduling construction is semantic and explicitly selected. It stops
processing pairs when its set of readings is closed. This is not a decidable
native saturation test, physical termination of the occurrence-bag machine,
or a claim about chronological or multiplicity observers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSemantics (Derives consequence hypotheses forwardClosure)
open StepWeb.KernelRounds (immediate stage finiteProofs)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] [Infinite O]

noncomputable def protectedRound (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) :
    ProtectedRun judgmentTag arrowTag s caller := by
  classical
  exact if immediate (consequence judgmentTag arrowTag) (storeReadings s caller) = storeReadings s caller
    then ProtectedRun.start known
    else Classical.choose (application_round_exists s caller known)

theorem protectedRound_exact (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) :
    storeReadings (protectedRound (judgmentTag := judgmentTag) (arrowTag := arrowTag) s caller known).run.last
        (protectedRound (judgmentTag := judgmentTag) (arrowTag := arrowTag) s caller known).source =
      immediate (consequence judgmentTag arrowTag) (storeReadings s caller) := by
  classical
  unfold protectedRound
  split_ifs with fixed
  · exact fixed.symm
  · exact Classical.choose_spec (application_round_exists s caller known)

theorem protectedRound_closed (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (fixed : immediate (consequence judgmentTag arrowTag) (storeReadings s caller) = storeReadings s caller) :
    protectedRound (judgmentTag := judgmentTag) (arrowTag := arrowTag) s caller known = ProtectedRun.start known := by
  classical
  simp only [protectedRound, if_pos fixed]

noncomputable def saturationPrefix (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) :
    Nat → ProtectedRun judgmentTag arrowTag s caller
  | 0 => ProtectedRun.start known
  | n + 1 =>
      let first := saturationPrefix judgmentTag arrowTag s caller known n
      first.append (protectedRound first.run.last first.source first.known)

theorem saturationPrefix_extends (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) (n : Nat) :
    ∃ rest : (machine judgmentTag arrowTag O).Run
        (saturationPrefix judgmentTag arrowTag s caller known n).run.last,
      (saturationPrefix judgmentTag arrowTag s caller known (n + 1)).run =
        (saturationPrefix judgmentTag arrowTag s caller known n).run.append rest := by
  exact ⟨(protectedRound (judgmentTag := judgmentTag) (arrowTag := arrowTag)
    (saturationPrefix judgmentTag arrowTag s caller known n).run.last
    (saturationPrefix judgmentTag arrowTag s caller known n).source
    (saturationPrefix judgmentTag arrowTag s caller known n).known).run, rfl⟩

theorem saturationPrefix_exact (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) (n : Nat) :
    storeReadings (saturationPrefix judgmentTag arrowTag s caller known n).run.last
        (saturationPrefix judgmentTag arrowTag s caller known n).source =
      stage (consequence judgmentTag arrowTag) (storeReadings s caller) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change storeReadings
        ((saturationPrefix judgmentTag arrowTag s caller known n).append
          (protectedRound _ _ _)).run.last
        ((saturationPrefix judgmentTag arrowTag s caller known n).append
          (protectedRound _ _ _)).source =
      immediate (consequence judgmentTag arrowTag)
        (stage (consequence judgmentTag arrowTag) (storeReadings s caller) n)
    rw [ProtectedRun.append_last, ProtectedRun.append_source, protectedRound_exact, ih]

def saturationReadings (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) : Set Tm :=
  {value | ∃ n, value ∈ storeReadings (saturationPrefix judgmentTag arrowTag s caller known n).run.last
    (saturationPrefix judgmentTag arrowTag s caller known n).source}

theorem saturationReadings_eq_finiteProofs (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) :
    saturationReadings judgmentTag arrowTag s caller known =
      finiteProofs (consequence judgmentTag arrowTag) (storeReadings s caller) := by
  ext value
  change (∃ n, value ∈ storeReadings _ _) ↔ ∃ n, value ∈ stage _ _ n
  simp_rw [saturationPrefix_exact]

omit [DecidableEq O] [Infinite O] in
theorem storeReadings_eq_hypotheses (s : Store O) (caller : Subst rowSig) :
    storeReadings s caller = hypotheses (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller := by
  ext value
  exact (hypothesis_occurrence s caller value).symm

theorem saturationReadings_eq_forwardClosure (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) :
    saturationReadings judgmentTag arrowTag s caller known =
      forwardClosure judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller := by
  rw [saturationReadings_eq_finiteProofs, storeReadings_eq_hypotheses]
  exact StepWeb.KernelRounds.finiteProofs_eq_target _ _

theorem saturationReadings_iff_derives (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge) (value : Tm) :
    value ∈ saturationReadings judgmentTag arrowTag s caller known ↔
      Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) caller value := by
  rw [saturationReadings_eq_forwardClosure]
  exact ApplicationSemantics.forward_closure_iff_derives _ _ _ _ _

#print axioms protectedRound_exact
#print axioms protectedRound_closed
#print axioms saturationPrefix_extends
#print axioms saturationPrefix_exact
#print axioms saturationReadings_eq_forwardClosure
#print axioms saturationReadings_iff_derives

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
