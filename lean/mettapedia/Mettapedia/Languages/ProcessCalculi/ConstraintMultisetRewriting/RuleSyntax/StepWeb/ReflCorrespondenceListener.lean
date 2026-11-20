import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondenceExample

/-!
# The listener's canonical form, at the name frame: what holds without it

Step 1′'s COMM at the name frame (`ReflNames.comm_one_firing_name`) asks the patterns to be canonical
(`bagCanon t = t`); the corrected REFL's listener quotes `canonicalBag R`, which wraps one component and is then not
canonical (`Controls.listener_canonical_form`). For patterns WITHOUT variables nothing has to be read off a unifier,
and the hypothesis is not needed:

* `comm_ground_name`: two rows that read as inputs with one and the same ground pattern communicate at the name
  frame at every fresh opening, and every solution reads the made rows as the represented continuations;
* `listener_meets_as_written`: the corrected listener of the example's reduct and a partner that writes its quote as
  written communicate at the name frame.

What stays separated is the partner that writes the listener's quote differently but equal modulo the bag laws:
the name frame meets it, the corrected semantics (which compares as written) does not
(`Controls.listener_canonical_form`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus (pFor pZero tProc demoChan)
open MeTTaOperationsComm (psubst PSubst pvars)
open FiniteProgram (predot predot_pFor program exists_fresh_opening)
open OneFrame (embed)
open ReflNames (NameLaws nameAction QN QNE commAtN comm_admits_name comm_reads_name fresh_name nameLaws_of_eq)

variable {O : Type*}

/-- **COMM between one ground pattern at the name frame**: no canonical form is needed. -/
theorem comm_ground_name [DecidableEq O] (label : O → Pattern) (t channel A B : Pattern) (ground : pvars t = [])
    (C : Configuration Pattern O) (first second made₁ made₂ : O)
    (readsFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (predot (pFor t channel A))))
    (readsSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (predot (pFor t channel B))))
    (distinct : first ≠ second) (madeDistinct : made₁ ≠ made₂)
    (present₁ : first ∈ C.present) (present₂ : second ∈ C.present)
    (fresh₁ : made₁ ∉ C.present) (fresh₂ : made₂ ∉ C.present)
    {σ₀ : PSubst} (known : nameAction.Models σ₀ C.equations)
    {ρ : PSubst} (opensFreshly : (commAtN ρ first second made₁ made₂).Fresh QN (embed label C)) :
    (RuleSyntax.step QN O QNE program).Admits (s := embed label C) (commAtN ρ first second made₁ made₂) ∧
      ∀ σ : PSubst, nameAction.Models σ ((commAtN ρ first second made₁ made₂).result QN (embed label C)).knowledge →
        NameLaws (psubst σ (((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₁))
            (psubst σ (predot A)) ∧
          NameLaws (psubst σ (((commAtN ρ first second made₁ made₂).result QN (embed label C)).label made₂))
            (psubst σ (predot B)) := by
  have rowFirst : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label first)) (psubst σ (pFor t (predot channel) (predot A))) := fun σ known' => by
    have read := readsFirst σ known'
    rw [predot_pFor, ground, FiniteProgram.dotted_nil] at read
    exact read
  have rowSecond : ∀ σ : PSubst, nameAction.Models σ C.equations →
      NameLaws (psubst σ (label second)) (psubst σ (pFor t (predot channel) (predot B))) := fun σ known' => by
    have read := readsSecond σ known'
    rw [predot_pFor, ground, FiniteProgram.dotted_nil] at read
    exact read
  refine ⟨comm_admits_name label t t (predot channel) (predot A) (predot B) C first second made₁ made₂ rowFirst
    rowSecond distinct madeDistinct present₁ present₂ fresh₁ fresh₂ known (ReflNames.NameLaws.refl _) opensFreshly,
    fun σ solved => ?_⟩
  obtain ⟨-, -, body₁, body₂⟩ := comm_reads_name label t t (predot channel) (predot channel) (predot A) (predot B) C
    first second made₁ made₂ rowFirst rowSecond madeDistinct ρ solved
  exact ⟨body₁, body₂⟩

/-- The corrected listener of the example's reduct and a partner writing its quote as written. -/
def listenerRows : ℕ → Pattern := fun _ => MeTTaCalculus.Corrected.listener demoChan exampleReduct

/-- **The corrected listener meets a partner that writes its quote as written**, at the name frame. -/
theorem listener_meets_as_written :
    ∃ ρ : PSubst,
      (RuleSyntax.step QN ℕ QNE program).Admits (s := embed listenerRows Comm.Controls.start) (commAtN ρ 0 1 2 3) := by
  obtain ⟨ρ, opensFreshly⟩ := exists_fresh_opening listenerRows Comm.Controls.start 0 1 2 3
  have shape : listenerRows 0 = predot (pFor (tProc (MeTTaCalculus.Corrected.canonicalBag exampleReduct)) demoChan pZero) := by
    decide +kernel
  refine ⟨ρ, (comm_ground_name listenerRows (tProc (MeTTaCalculus.Corrected.canonicalBag exampleReduct)) demoChan pZero
    pZero (by decide +kernel) Comm.Controls.start 0 1 2 3 (fun σ _ => nameLaws_of_eq (congrArg (psubst σ) shape))
    (fun σ _ => nameLaws_of_eq (congrArg (psubst σ) shape)) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (σ₀ := fun _ => none)
    (fun _ member => absurd member List.not_mem_nil) (fresh_name opensFreshly)).1⟩

#print axioms comm_ground_name
#print axioms listener_meets_as_written

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
