import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramDefinitions

/-!
# Program runs are runs of the candidate step's interface

A translated run, kept as data (`TranslatedRun`), is a run of R80's ordinary step
(`Semantic.semanticStep`), an instance of `Interface.Step` (`TranslatedRun.toRun`), with the same end
(`TranslatedRun.toRun_last`). Every translated path has such a run (`exists_run`). So the interface's
general laws hold for programs:

* **knowledge only refines** along a program run: every solution of the last knowledge is a solution
  of the first (`program_models_start`, from `Interface.Step.Run.models_start`; the one-frame
  morphism of a run acts as the identity, `toLast_apply`);
* **site accounts are functors** out of a program's runs (`program_account_append`, from
  `Interface.Step.Run.account_append`).

For the program core, from the rows of a program: the source reaches `W` exactly when an interface
run of the ordinary step reaches a configuration representing `W` (`program_interface_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramTranslation

open ProgramRows

variable {ι : Type*} (schema : ι → Schema)

/-- A run of translated firings, as data. -/
inductive TranslatedRun : Config → ℕ → Type _
  | nil (C : Config) (n : ℕ) : TranslatedRun C n
  | cons {C : Config} {n : ℕ} (i : ι) (taken read : List Occ)
      (valid : ((schema i).firing n taken read).Valid A Occ.label C)
      (rest : TranslatedRun (((schema i).firing n taken read).result Occ.label C) (n + 1)) :
      TranslatedRun C n

namespace TranslatedRun

variable {schema}

/-- The configuration and next scope a run ends at. -/
noncomputable def last : {C : Config} → {n : ℕ} → TranslatedRun schema C n → Config × ℕ
  | C, n, .nil _ _ => (C, n)
  | _, _, .cons _ _ _ _ rest => rest.last

/-- **A translated run is a run of the ordinary step.** -/
noncomputable def toRun : {C : Config} → {n : ℕ} → TranslatedRun schema C n →
    (Semantic.semanticStep A Occ.label).Run C
  | C, _, .nil _ _ => .nil C
  | _, n, .cons i taken read valid rest =>
      .cons ⟨(schema i).firing n taken read, firing_isSemantic _ n taken read⟩ valid rest.toRun

theorem toRun_last : ∀ {C : Config} {n : ℕ} (r : TranslatedRun schema C n), r.toRun.last = r.last.1
  | _, _, .nil _ _ => rfl
  | _, _, .cons _ _ _ _ rest => toRun_last rest

theorem path : ∀ {C : Config} {n : ℕ} (r : TranslatedRun schema C n),
    Relation.ReflTransGen (Translated schema) (C, n) r.last
  | _, _, .nil _ _ => .refl
  | _, _, .cons i taken read valid rest => Relation.ReflTransGen.head (.fire i taken read valid) rest.path

end TranslatedRun

/-- **Every translated path is a translated run.** -/
theorem exists_run {p q : Config × ℕ} (path : Relation.ReflTransGen (Translated schema) p q) :
    Nonempty {r : TranslatedRun schema p.1 p.2 // r.last = q} := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨⟨.nil q.1 q.2, rfl⟩⟩
  | head step _ ih =>
      obtain ⟨r, hr⟩ := ih
      cases step with
      | fire i taken read valid => exact ⟨⟨.cons i taken read valid r, hr⟩⟩

/-- The one-frame morphism of a run of the ordinary step acts as the identity. -/
theorem toLast_apply : ∀ {C : Config} (r : (Semantic.semanticStep A Occ.label).Run C) (t : Tm),
    A.apply r.toLast t = t
  | _, .nil _, t => A.apply_identity t
  | _, .cons _ _ rest, t => by
      change A.apply (A.compose rest.toLast (A.compose A.identity A.identity)) t = t
      rw [A.apply_compose, A.apply_compose, A.apply_identity, A.apply_identity, toLast_apply rest t]

/-- **Knowledge only refines along a program run**, by the interface's `Run.models_start`. -/
theorem program_models_start {C : Config} {n : ℕ} (r : TranslatedRun schema C n)
    (σ : Mettapedia.Logic.LP.Subst rows) (solved : A.Models σ r.last.1.equations) :
    A.Models σ C.equations := by
  have start := Interface.Step.Run.models_start r.toRun (b := PUnit.unit) σ (by
    rw [TranslatedRun.toRun_last]
    exact solved)
  intro e member
  have composite := start e member
  change A.apply (A.compose σ r.toRun.toLast) e.1 = A.apply (A.compose σ r.toRun.toLast) e.2 at composite
  rw [A.apply_compose, A.apply_compose, toLast_apply, toLast_apply] at composite
  exact composite

/-- **Site accounts are functors out of program runs**, by the interface's `Run.account_append`. -/
theorem program_account_append {M : Type*} [Monoid M]
    (grade : (t : Config) → Semantic.SemanticFiring A Occ → M) {C : Config} {n : ℕ}
    (r : TranslatedRun schema C n) (later : (Semantic.semanticStep A Occ.label).Run r.toRun.last) :
    (r.toRun.append later).account grade = r.toRun.account grade * later.account grade :=
  Interface.Step.Run.account_append grade r.toRun later

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramTranslation

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program

open ProgramRows ProgramTranslation

/-- **The program core on the interface**: from the rows of a program, the source reaches `W` exactly
when a run of the ordinary step, made of translated firings, reaches a configuration representing
`W`. -/
theorem program_interface_iff (l : List Sx) (W : Multiset Sx) :
    Relation.ReflTransGen Step (l : Multiset Sx) W ↔
      ∃ r : TranslatedRun schema (initial l) 1, Represents r.toRun.last W r.last.2 := by
  rw [program_execution_iff]
  constructor
  · rintro ⟨q, path, rep⟩
    obtain ⟨⟨r, rfl⟩⟩ := exists_run schema path
    exact ⟨r, by rw [TranslatedRun.toRun_last]; exact rep⟩
  · rintro ⟨r, rep⟩
    rw [TranslatedRun.toRun_last] at rep
    exact ⟨r.last, r.path, rep⟩

#print axioms ProgramTranslation.TranslatedRun.toRun_last
#print axioms ProgramTranslation.exists_run
#print axioms ProgramTranslation.toLast_apply
#print axioms ProgramTranslation.program_models_start
#print axioms ProgramTranslation.program_account_append
#print axioms program_interface_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Program
