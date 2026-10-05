import Mettapedia.Languages.MM0.Presentation.CalculusAdmission

/-!
# Controls for the MM0 calculus

One theory declares a provable sort, a constant of that sort and an axiom
asserting the constant; a second theory has the same sort and constant but no
axiom. The calculus is the same for both. The axiom's statement has an
accepted certificate in the first theory and none in the second, and a computed
leaf claiming the missing axiom is rejected.

Admission builds the first theory from the empty one, and then admits a theorem
whose proof applies the axiom; a theorem whose witness points at a missing
hypothesis is refused.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.Calculus.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.Languages.MM0.Kernel

def constant : Preterm := .term 0

def axiomDecl : TheoremDecl := ⟨[], [], constant⟩

/-- A provable sort, a constant of it, and an axiom asserting the constant. -/
def withAxiom : Theory :=
  { sorts := [(0, { provable := true })]
    terms := [(0, ⟨[], 0, ∅⟩)]
    theorems := [(0, axiomDecl)] }

/-- The same sort and constant, without the axiom. -/
def withoutAxiom : Theory :=
  { sorts := [(0, { provable := true })]
    terms := [(0, ⟨[], 0, ∅⟩)] }

theorem axiom_instance :
    TheoremDecl.Instantiates withAxiom.termSignature [] axiomDecl [] ⟨[], constant⟩ :=
  (TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp (by decide)

/-- **Positive control**: the axiom's statement has an accepted certificate. -/
theorem axiom_certified : (mm0 withAxiom).Accepts (derivesJ [] [] constant) :=
  (accepts_iff_derives [] [] constant).mpr
    (.theoremApp (index := 0) (declaration := axiomDecl) (arguments := []) rfl axiom_instance .nil)

/-- Without theorems and hypotheses, the kernel derives nothing. -/
theorem nothing_derivable {signature : TermSignature} {definitions : Definition.Signature}
    {context : Context} : ∀ {expression : Preterm},
    Derives signature definitions (fun _ => none) context [] expression → False
  | _, .hypothesis member => by cases member
  | _, .theoremApp lookup _ _ => by cases lookup
  | _, .conversion _ derived => nothing_derivable derived

/-- **Negative control**: without the axiom, no certificate is accepted. -/
theorem without_axiom_uncertified : ¬ (mm0 withoutAxiom).Accepts (derivesJ [] [] constant) :=
  fun accepted => nothing_derivable ((accepts_iff_derives [] [] constant).mp accepted)

/-- **Trust control**: an implementation that answers the missing axiom's
lookup is not trusted, because the judgment it returns is not a fact. -/
theorem lookup_inventing_axiom_untrusted :
    ¬ (mm0 withoutAxiom).ReturnsFacts
      (fun (_ : Unit) => some (theoremJ 0 axiomDecl)) := by
  refine AuthoredCalculus.not_returnsFacts_of_wrong (query := ()) rfl ?_
  intro holds
  rcases (family_fact_iff withoutAxiom _).mp holds with
    ⟨index, declaration, found, _⟩ | ⟨_, _, _, _, _, same⟩ | ⟨_, _, _, _, same⟩
  · cases found
  · simp [theoremJ, jTheorem, instanceJ, jInstance] at same
  · simp [theoremJ, jTheorem, convertsJ, jConverts] at same

/-- **Negative control**: a computed leaf claiming the missing axiom is
rejected, whatever fuel it names. -/
theorem missing_axiom_leaf_rejected (fuel : Nat) :
    check formMM0 (family withoutAxiom).evaluate (theoremJ 0 axiomDecl)
      (.computed ⟨Operation.lookup, ⟨(0 : Nat), axiomDecl, fuel⟩⟩) = false :=
  absent_output_rejects _ _
    (AuthoredFamily.evaluate_eq_none (F := family withoutAxiom) (index := Operation.lookup)
      (leaf := ⟨(0 : Nat), axiomDecl, fuel⟩) (fun found => by cases found))
    _

/-! ## Admission -/

def provableSort : Admission := .sort 0 { provable := true }
def constantTerm : Admission := .term 0 ⟨[], 0, ∅⟩
def theAxiom : Admission := .axiomDecl 0 axiomDecl

/-- **Positive admission control**: the sort, the constant and the axiom are
admitted in order, giving the theory with the axiom. -/
theorem axiom_theory_admitted :
    Calculus.Admission.Runs {} [provableSort, constantTerm, theAxiom] withAxiom := by
  refine .cons (.intro ((Calculus.Admission.authorized_iff _ _).mpr
    ((Admission.check_iff _ _).mp (by decide)))) ?_
  refine .cons (.intro ((Calculus.Admission.authorized_iff _ _).mpr
    ((Admission.check_iff _ _).mp (by decide)))) ?_
  exact .cons (.intro ((Calculus.Admission.authorized_iff _ _).mpr
    ((Admission.check_iff _ _).mp (by decide)))) (.nil _)

/-- A theorem restating the axiom, proved by applying it. -/
def restated : Admission := .theoremDecl 1 axiomDecl [] (.theoremApp 0 [] [])

/-- **Positive control**: the restated theorem is admitted; its proof is
accepted by the shared checker. -/
theorem restated_admitted : Calculus.Admission.Authorized withAxiom restated :=
  (Calculus.Admission.authorized_iff _ _).mpr
    (.theoremDecl rfl ((TheoremDecl.check_iff _ _ _).mp (by decide))
      (fun _ member => by cases member)
      (.theoremApp (index := 0) (declaration := axiomDecl) (arguments := [])
        (instantiation := ⟨[], constant⟩) rfl axiom_instance .nil))

/-- A theorem whose witness uses a hypothesis that does not exist. -/
def unproved : Admission := .theoremDecl 1 axiomDecl [] (.hyp 0)

/-- **Negative control**: the theorem is refused. -/
theorem unproved_refused : ¬ Calculus.Admission.Authorized withAxiom unproved := by
  intro authorized
  cases (Calculus.Admission.authorized_iff _ _).mp authorized with
  | theoremDecl _ _ _ checked =>
      cases checked with
      | hyp found => simp [Admission.proofContext, axiomDecl] at found

end Mettapedia.Languages.MM0.Presentation.Calculus.Controls
