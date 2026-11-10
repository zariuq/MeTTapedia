import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Semantic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ResolutionModulo
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CompletionFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceExperiments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypingContracts

/-!
# The existing calculi are ordinary

Every calculus built so far on the one-frame step fires semantic firings, so equivalence modulo the
knowledge is a congruence for each of them (`Semantic`, `Observation.ModuloEquivalent.semantic_*`).

* **Resolution** (`resolve_isSemantic`, `isSemantic_of_isResolution`): a resolution firing has no
  query. A resolution run is a run of the ordinary step with the same end (`resolutionRun`,
  `resolutionRun_last`).
* **Superposition and completion run in the guarded step.** A guard is a predicate of the solution;
  it reads no label. The congruence extends to guarded firings
  (`Observation.ModuloEquivalent.guarded_firing`), and the guarded step restricted to semantic
  firings is the ordinary guarded step (`semanticGuarded`).
  * Superposition (`unifyFiring_isSemantic`, `supFiring_isSemantic`, `eqResFiring_isSemantic`,
    `eqFactFiring_isSemantic`, `resolutionFiring_isSemantic`): every inference firing has no query.
  * Saturation and completion (`clauseFiring_isSemantic`, `inferFiring_isSemantic`,
    `simplifyFiring_isSemantic`, `move_isSemantic`): no query. They also run over the syntactic
    action, whose solutions identify only equal terms, where every firing is semantic
    (`isSemantic_syntactic`).
* **Races** (`isSemantic_of_ground`, `isSemantic_of_pure`, `triggered_isSemantic`): ground and pure firings
  have no query, so the race programs' firings are semantic.
* **Typing** (`tellFiring_isSemantic`): typing firings tell and check and have no query; the call
  firings are tell firings. The dependent-frame typing firings (`TypingStates`) have no query
  position at all.

## A family that reads syntactically

The run layer's census controls read labels syntactically. The region of persistent atoms tests the
raw constant `9` (`AnnotatedRuns.Controls.persistent`), and the solution that sends the variable `0`
to `9` identifies two terms the region separates (`persistent_not_semantic`). Its labels are ground
in those controls, so their behaviour does not depend on it, but as firings they belong to the
reflection layer. Read through the solution, the same test is semantic (`persistentThrough`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic

open AnnotatedRuns

universe uT uS uO

/-! ## Resolution -/

section Resolution

open Mettapedia.Logic.LP
open Resolution (resolve IsResolution)

variable {sig : LPSignature} {O : Type uO}

/-- **A resolution firing is semantic**: it has no query. -/
theorem resolve_isSemantic [DecidableEq sig.vars] [DecidableEq O]
    (A : SubstitutionAction (Term sig) (Subst sig)) (o : O) (c : Resolution.Clause sig)
    (ρ : Equiv.Perm sig.vars) (made : List O) : IsSemantic A (resolve o c ρ made) :=
  isSemantic_of_queries_nil rfl

theorem isSemantic_of_isResolution [DecidableEq sig.vars] [DecidableEq O]
    (A : SubstitutionAction (Term sig) (Subst sig)) {prog : Resolution.Program sig}
    {f : Firing (Term sig) (Subst sig) O} (resolving : IsResolution prog f) : IsSemantic A f := by
  obtain ⟨o, c, ρ, made, -, rfl⟩ := resolving
  exact isSemantic_of_queries_nil rfl

/-- **A resolution run is a run of the ordinary step.** -/
def resolutionRun [DecidableEq sig.vars] [DecidableEq O] {label : O → Term sig}
    {prog : Resolution.Program sig} {C : Configuration (Term sig) O}
    (r : (firstOrder (Resolution.A sig) label).Run C) (resolving : ∀ x ∈ r.word, IsResolution prog x.2) :
    (semanticStep (Resolution.A sig) label).Run C :=
  liftRun r fun x member => isSemantic_of_isResolution (Resolution.A sig) (resolving x member)

theorem resolutionRun_last [DecidableEq sig.vars] [DecidableEq O] {label : O → Term sig}
    {prog : Resolution.Program sig} {C : Configuration (Term sig) O}
    (r : (firstOrder (Resolution.A sig) label).Run C) (resolving : ∀ x ∈ r.word, IsResolution prog x.2) :
    (resolutionRun r resolving).last = r.last :=
  liftRun_last r fun x member => isSemantic_of_isResolution (Resolution.A sig) (resolving x member)

end Resolution

/-! ## Guarded firings -/

section Guarded

open Superposition (GuardedFiring guarded)

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- **The ordinary guarded step**: the guarded step restricted to firings whose queries read through
solutions. -/
abbrev semanticGuarded [DecidableEq O] (A : SubstitutionAction T S) (label : O → T) :=
  Race.restrict (guarded A label).toStep (fun _ f => IsSemantic A f.firing)

end Guarded

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)
open Semantic
open Superposition (GuardedFiring guarded)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} {A : SubstitutionAction T S} {label : O → T}
  {E : Finset O}

/-- **Equivariance modulo the knowledge for guarded firings.** Guards are predicates of the solution
and read no label. At equivalent states, along a renaming supported on the present occurrences, a
guarded firing whose queries read through solutions and its renaming are admitted together in the
guarded step, and their results are equivalent, when the made identities are absent from both
states. -/
theorem ModuloEquivalent.guarded_firing [DecidableEq O] {C D : Configuration T O}
    (h : ModuloEquivalent A label E C D) (f : GuardedFiring T S O)
    (avoids : ∀ r ∈ f.firing.selection.made, r ∉ C.present ∧ r ∉ D.present)
    (reads : IsSemantic A f.firing) :
    ∃ π : O ≃ O, ((guarded A label).Admits (s := D) ⟨f.firing.rename π, f.guards⟩ ↔
        (guarded A label).Admits (s := C) f) ∧
      ModuloEquivalent A label E (f.firing.result label C) ((f.firing.rename π).result label D) := by
  obtain ⟨π, k, same, support⟩ := h.supported
  have fixesMade : ∀ r ∈ f.firing.selection.made, π r = r := fun r member =>
    support r (avoids r member).1 (avoids r member).2
  obtain ⟨admits, results⟩ := modulo_step k same fixesMade reads
  have first : A.Equivalent ((f.firing.rename π).selection.problem label f.firing.rule D)
      ((f.firing.rename π).selection.problem label f.firing.rule (renameConfiguration π C)) := by
    rw [GuardFreeProcessOrders.problem_eq, GuardFreeProcessOrders.problem_eq]
    exact GuardFreeProcessOrders.equivalent_append A (fun σ => (same.1 σ).symm) _
  have second : (f.firing.rename π).selection.problem label f.firing.rule (renameConfiguration π C) =
      f.firing.selection.problem (fun o => label (π o)) f.firing.rule C :=
    problem_rename_comp π f.firing.selection f.firing.rule C
  have third : A.Equivalent (f.firing.selection.problem (fun o => label (π o)) f.firing.rule C)
      (f.firing.selection.problem label f.firing.rule C) :=
    problem_relabel (C := C) k.keeps f.firing.selection f.firing.rule
  have problems : ∀ σ, A.Models σ ((f.firing.rename π).selection.problem label f.firing.rule D) ↔
      A.Models σ (f.firing.selection.problem label f.firing.rule C) := fun σ => by
    rw [first σ, second]
    exact third σ
  refine ⟨π, ⟨fun admitted => ⟨admits.mp admitted.1, fun σ solved => admitted.2 σ ((problems σ).mpr solved)⟩,
    fun admitted => ⟨admits.mpr admitted.1, fun σ solved => admitted.2 σ ((problems σ).mp solved)⟩⟩,
    results⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic

open AnnotatedRuns

universe uT uS uO

/-! ## Superposition, saturation and completion -/

section Superposition

open Mettapedia.Logic.LP
open Superposition (GuardedFiring clauseFiring unifyFiring supFiring eqResFiring eqFactFiring
  resolutionFiring inferFiring simplifyFiring syntactic StableOrder ClauseCode NLit NClause
  GroundSimplification)

variable {sig : LPSignature} {O : Type uO}

theorem unifyFiring_isSemantic [DecidableEq O] (A : SubstitutionAction (Term sig) (Subst sig))
    (reads : List (O × Term sig)) (l u : Term sig) (made : O) (concl : Term sig)
    (G : Subst sig → Prop) : IsSemantic A (unifyFiring reads l u made concl G).firing :=
  isSemantic_of_queries_nil rfl

theorem supFiring_isSemantic [DecidableEq O] (A : SubstitutionAction (Term sig) (Subst sig))
    (ord : StableOrder sig) (code : ClauseCode sig) (side main : O × Term sig) (made : O)
    (c : FirstOrderRewriting.Context sig) (u l r : Term sig) (D' : NClause sig) (L : NLit sig)
    (C' : NClause sig) : IsSemantic A (supFiring ord code side main made c u l r D' L C').firing :=
  isSemantic_of_queries_nil rfl

theorem eqResFiring_isSemantic [DecidableEq O] (A : SubstitutionAction (Term sig) (Subst sig))
    (ord : StableOrder sig) (code : ClauseCode sig) (main : O × Term sig) (made : O) (L : NLit sig)
    (C' : NClause sig) : IsSemantic A (eqResFiring ord code main made L C').firing :=
  isSemantic_of_queries_nil rfl

theorem eqFactFiring_isSemantic [DecidableEq O] (A : SubstitutionAction (Term sig) (Subst sig))
    (ord : StableOrder sig) (code : ClauseCode sig) (main : O × Term sig) (made : O)
    (L L' : NLit sig) (C' : NClause sig) : IsSemantic A (eqFactFiring ord code main made L L' C').firing :=
  isSemantic_of_queries_nil rfl

theorem resolutionFiring_isSemantic [DecidableEq O] (A : SubstitutionAction (Term sig) (Subst sig))
    (ord : StableOrder sig) (code : ClauseCode sig) (top : Term sig) (side main : O × Term sig)
    (made : O) (P Q : Term sig) (D' C' : NClause sig) :
    IsSemantic A (resolutionFiring ord code top side main made P Q D' C').firing :=
  isSemantic_of_queries_nil rfl

theorem clauseFiring_isSemantic {T : Type uT} (A : SubstitutionAction T Unit)
    (takes reads makes : List (O × T)) (guard : Prop) :
    IsSemantic A (clauseFiring takes reads makes guard).firing :=
  isSemantic_of_queries_nil rfl

theorem inferFiring_isSemantic [LinearOrder (GroundTerm sig)]
    (A : SubstitutionAction (Superposition.Clause (GroundTerm sig)) Unit) (side : Option (O × Superposition.Clause (GroundTerm sig)))
    (main : O × Superposition.Clause (GroundTerm sig)) (made : O) (concl : Superposition.Clause (GroundTerm sig)) :
    IsSemantic A (inferFiring side main made concl).firing :=
  isSemantic_of_queries_nil rfl

theorem simplifyFiring_isSemantic [LinearOrder (GroundTerm sig)] [GroundSimplification sig]
    (A : SubstitutionAction (Superposition.Clause (GroundTerm sig)) Unit) (taken : O × Superposition.Clause (GroundTerm sig))
    (reads makes : List (O × Superposition.Clause (GroundTerm sig))) :
    IsSemantic A (simplifyFiring taken reads makes).firing :=
  isSemantic_of_queries_nil rfl

/-- **Over the syntactic action every firing is semantic**: its solutions identify only equal
terms. -/
theorem isSemantic_syntactic {T : Type uT} (f : Firing T Unit O) : IsSemantic (syntactic T) f :=
  isSemantic_of_faithful (A := syntactic T) (fun _ _ _ solved => solved) f

/-- **A completion move is semantic.** -/
theorem move_isSemantic [Preorder (GroundTerm sig)] (A : SubstitutionAction (Completion.Item sig) Unit)
    (m : Completion.Move sig O) : IsSemantic A m.firing.firing :=
  isSemantic_of_queries_nil rfl

end Superposition

/-! ## Races -/

section Races

variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- **A ground firing is semantic.** -/
theorem isSemantic_of_ground [DecidableEq O] (A : SubstitutionAction T S) {label : O → T}
    {f : Firing T S O} (ground : Race.Ground label f) : IsSemantic A f :=
  isSemantic_of_queries_nil ground.queries

/-- **A pure firing is semantic.** -/
theorem isSemantic_of_pure [DecidableEq O] (A : SubstitutionAction T S) {f : Firing T S O}
    (pure : Race.Pure f) : IsSemantic A f :=
  isSemantic_of_queries_nil pure.queries

/-- **The triggered race pair's firings are semantic.** -/
theorem triggered_isSemantic (A : SubstitutionAction T S) (τ : T) :
    ∀ x ∈ Race.Triggered.alphabet (S := S) τ, IsSemantic A x.2 := fun x member =>
  isSemantic_of_ground A (Race.Triggered.ground τ x member)

end Races

/-! ## Typing -/

section Typing

/-- **A typing firing that tells is semantic**; the call firings are such firings. -/
theorem tellFiring_isSemantic {Ctx V A' Q C Sym : Type} {typeArity : C → Nat} {valueArity : Sym → Nat}
    {reserved : Q → Prop} {O : Type} [DecidableEq O]
    (act : SubstitutionAction (TypingFirings.Term Ctx V A' Q C Sym typeArity valueArity)
      (TypingFirings.Instantiation V A' Q C Sym typeArity valueArity reserved))
    (tells : EquationStore (TypingFirings.Term Ctx V A' Q C Sym typeArity valueArity)) :
    IsSemantic act (TypingFirings.tellFiring (O := O) (reserved := reserved) tells) :=
  isSemantic_of_queries_nil rfl

end Typing

/-! ## A family that reads syntactically -/

section Census

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)

/-- The census query of the run layer's controls: no persistent atom. -/
def persistentQuery : PredicateQueryAdmission.Query (Term signature) (Subst signature) ℕ :=
  PredicateQueryAdmission.Query.fixed AnnotatedRuns.Controls.noPersistent

/-- **The census controls read labels syntactically**: the solution that sends every variable to the
constant `9` identifies the variable `0` with `9`, and the region of persistent atoms holds only the
second. -/
theorem persistent_not_semantic : ¬ ReadsThroughSolutions A persistentQuery := by
  intro reads
  have identified : A.Solves (fun _ => Term.const 9) (Term.var 0, Term.const 9) := rfl
  have same := reads (fun _ => Term.const 9) identified
  exact absurd same (by decide)

/-- **Read through the solution, the same test is semantic.** -/
def persistentThrough : SemanticQuery A ℕ :=
  throughSolutions A AnnotatedRuns.Controls.persistent (fun same => congrArg AnnotatedRuns.Controls.persistent same) ∅

end Census

#print axioms resolve_isSemantic
#print axioms isSemantic_of_isResolution
#print axioms resolutionRun_last
#print axioms Observation.ModuloEquivalent.guarded_firing
#print axioms unifyFiring_isSemantic
#print axioms supFiring_isSemantic
#print axioms eqResFiring_isSemantic
#print axioms eqFactFiring_isSemantic
#print axioms resolutionFiring_isSemantic
#print axioms clauseFiring_isSemantic
#print axioms inferFiring_isSemantic
#print axioms simplifyFiring_isSemantic
#print axioms isSemantic_syntactic
#print axioms move_isSemantic
#print axioms isSemantic_of_ground
#print axioms isSemantic_of_pure
#print axioms triggered_isSemantic
#print axioms tellFiring_isSemantic
#print axioms persistent_not_semantic
#print axioms persistentThrough

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Semantic
