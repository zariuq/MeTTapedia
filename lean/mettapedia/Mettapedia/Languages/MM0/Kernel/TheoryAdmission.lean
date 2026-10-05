import Mettapedia.Languages.MM0.Kernel.DeclarationAdmission
import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# Sequential admission of fully supplied MM0 declarations

Each proof and definition body is checked against the preceding environment.
Identifiers are explicit and fresh within their namespace. Axioms are explicit
theory assumptions; matching them to a separate specification is an additional
source-boundary obligation, not inferred from payload validity.

Definitions here have bodies, as in an implementation/proof file. Matching
omitted specification bodies and auxiliary declarations is handled separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel

structure Theory where
  sorts : List (Nat × SortInfo) := []
  terms : List (Nat × TermDecl) := []
  definitions : List (Nat × Definition.Body) := []
  theorems : List (Nat × TheoremDecl) := []

namespace Theory

def sortSignature (theory : Theory) : SortSignature := fun index => theory.sorts.lookup index
def termSignature (theory : Theory) : TermSignature := fun index => theory.terms.lookup index
def definitionSignature (theory : Theory) : Definition.Signature :=
  fun index => theory.definitions.lookup index
def theoremSignature (theory : Theory) : TheoremSignature := fun index => theory.theorems.lookup index

end Theory

inductive Admission where
  | sort (index : Nat) (info : SortInfo)
  | term (index : Nat) (declaration : TermDecl)
  | definition (index : Nat) (declaration : TermDecl) (body : Definition.Body)
  | axiomDecl (index : Nat) (declaration : TheoremDecl)
  | theoremDecl (index : Nat) (declaration : TheoremDecl) (dummies : List Nat) (proof : ProofWitness)

namespace Admission

def proofContext (declaration : TheoremDecl) (dummies : List Nat) : Context :=
  declaration.arguments ++ dummies.map Binder.bound

/-- The precise prerequisites of this particular declaration and its evidence. -/
inductive Authorized (theory : Theory) : Admission → Prop where
  | sort {index : Nat} {info : SortInfo} : theory.sortSignature index = none →
      Authorized theory (.sort index info)
  | term {index : Nat} {declaration : TermDecl} : theory.termSignature index = none →
      TermDecl.Admissible theory.sortSignature declaration →
      Authorized theory (.term index declaration)
  | definition {index : Nat} {declaration : TermDecl} {body : Definition.Body} :
      theory.termSignature index = none → theory.definitionSignature index = none →
      TermDecl.Admissible theory.sortSignature declaration →
      Definition.AdmissibleBody theory.sortSignature theory.termSignature declaration body →
      Authorized theory (.definition index declaration body)
  | axiomDecl {index : Nat} {declaration : TheoremDecl} : theory.theoremSignature index = none →
      TheoremDecl.Admissible theory.sortSignature theory.termSignature declaration →
      Authorized theory (.axiomDecl index declaration)
  | theoremDecl {index : Nat} {declaration : TheoremDecl} {dummies : List Nat} {proof : ProofWitness} :
      theory.theoremSignature index = none →
      TheoremDecl.Admissible theory.sortSignature theory.termSignature declaration →
      (∀ sort ∈ dummies, ∃ info, theory.sortSignature sort = some info ∧
        info.strict = false ∧ info.free = false) →
      ProofWitness.Checks theory.termSignature theory.definitionSignature theory.theoremSignature
        (proofContext declaration dummies) declaration.hypotheses proof declaration.conclusion →
      Authorized theory (.theoremDecl index declaration dummies proof)

def check (theory : Theory) : Admission → Bool
  | .sort index _ => (theory.sortSignature index).isNone
  | .term index declaration => (theory.termSignature index).isNone &&
      TermDecl.check theory.sortSignature declaration
  | .definition index declaration body => (theory.termSignature index).isNone &&
      (theory.definitionSignature index).isNone && TermDecl.check theory.sortSignature declaration &&
      Definition.checkBody theory.sortSignature theory.termSignature declaration body
  | .axiomDecl index declaration => (theory.theoremSignature index).isNone &&
      TheoremDecl.check theory.sortSignature theory.termSignature declaration
  | .theoremDecl index declaration dummies proof => (theory.theoremSignature index).isNone &&
      TheoremDecl.check theory.sortSignature theory.termSignature declaration &&
      Definition.checkDummySorts theory.sortSignature dummies &&
      ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
        (proofContext declaration dummies) declaration.hypotheses proof declaration.conclusion

theorem check_iff (theory : Theory) (admission : Admission) :
    check theory admission = true ↔ Authorized theory admission := by
  cases admission with
  | sort index info =>
      simp only [check, Option.isNone_iff_eq_none]
      exact ⟨Authorized.sort, fun h => by cases h; assumption⟩
  | term index declaration =>
      simp only [check, Bool.and_eq_true, Option.isNone_iff_eq_none, TermDecl.check_iff]
      exact ⟨fun ⟨fresh, valid⟩ => .term fresh valid, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
  | definition index declaration body =>
      simp only [check, Bool.and_eq_true, Option.isNone_iff_eq_none,
        TermDecl.check_iff, Definition.checkBody_iff]
      exact ⟨fun ⟨⟨⟨fresh, freshBody⟩, valid⟩, body⟩ => .definition fresh freshBody valid body,
        fun h => by cases h; exact ⟨⟨⟨‹_›, ‹_›⟩, ‹_›⟩, ‹_›⟩⟩
  | axiomDecl index declaration =>
      simp only [check, Bool.and_eq_true, Option.isNone_iff_eq_none, TheoremDecl.check_iff]
      exact ⟨fun ⟨fresh, valid⟩ => .axiomDecl fresh valid, fun h => by cases h; exact ⟨‹_›, ‹_›⟩⟩
  | theoremDecl index declaration dummies proof =>
      simp only [check, Bool.and_eq_true, Option.isNone_iff_eq_none, TheoremDecl.check_iff,
        Definition.checkDummySorts_iff, ProofWitness.check_iff]
      exact ⟨fun ⟨⟨⟨fresh, valid⟩, dummies⟩, proof⟩ => .theoremDecl fresh valid dummies proof,
        fun h => by cases h; exact ⟨⟨⟨‹_›, ‹_›⟩, ‹_›⟩, ‹_›⟩⟩

/-- Candidate storage update. Only `Theory.step?` checks authorization. -/
def insert (theory : Theory) : Admission → Theory
  | .sort index info => { theory with sorts := (index, info) :: theory.sorts }
  | .term index declaration => { theory with terms := (index, declaration) :: theory.terms }
  | .definition index declaration body =>
      { theory with
        terms := (index, declaration) :: theory.terms
        definitions := (index, body) :: theory.definitions }
  | .axiomDecl index declaration => { theory with theorems := (index, declaration) :: theory.theorems }
  | .theoremDecl index declaration _ _ =>
      { theory with theorems := (index, declaration) :: theory.theorems }

end Admission

namespace Theory

inductive Step (before : Theory) (admission : Admission) : Theory → Prop where
  | intro : Admission.Authorized before admission → Step before admission (admission.insert before)

def step? (theory : Theory) (admission : Admission) : Option Theory :=
  if admission.check theory then some (admission.insert theory) else none

theorem step_eq_some_iff (before after : Theory) (admission : Admission) :
    step? before admission = some after ↔ Step before admission after := by
  constructor
  · intro success
    unfold step? at success
    split at success
    next accepted =>
      have same := Option.some.inj success
      subst after
      exact .intro ((Admission.check_iff _ _).mp accepted)
    next => cases success
  · intro checked
    cases checked with
    | intro authorized => simp [step?, (Admission.check_iff _ _).mpr authorized]

/-- The supplied theorem proof is justified using the preceding theory,
not the state in which its conclusion has already been inserted. -/
theorem Step.theorem_justified {before after : Theory} {index : Nat}
    {declaration : TheoremDecl} {dummies : List Nat} {proof : ProofWitness}
    (step : Step before (.theoremDecl index declaration dummies proof) after) :
    Derives before.termSignature before.definitionSignature before.theoremSignature
      (Admission.proofContext declaration dummies) declaration.hypotheses declaration.conclusion := by
  cases step with
  | intro authorized =>
      cases authorized with
      | theoremDecl _ _ _ checked => exact checked.derives

/-- A theory extension preserves every earlier table entry. -/
structure Extends (before after : Theory) : Prop where
  sorts : ∀ index info, before.sortSignature index = some info → after.sortSignature index = some info
  terms : ∀ index declaration, before.termSignature index = some declaration →
    after.termSignature index = some declaration
  definitions : ∀ index body, before.definitionSignature index = some body →
    after.definitionSignature index = some body
  theorems : ∀ index declaration, before.theoremSignature index = some declaration →
    after.theoremSignature index = some declaration

theorem Extends.refl (theory : Theory) : Extends theory theory :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem Extends.trans {first middle last : Theory}
    (left : Extends first middle) (right : Extends middle last) : Extends first last :=
  ⟨fun i x h => right.sorts i x (left.sorts i x h),
    fun i x h => right.terms i x (left.terms i x h),
    fun i x h => right.definitions i x (left.definitions i x h),
    fun i x h => right.theorems i x (left.theorems i x h)⟩

private theorem lookup_cons_preserves {α : Type} (entries : List (Nat × α))
    (index : Nat) (entry : α) (fresh : entries.lookup index = none)
    (old : Nat) (value : α) (known : entries.lookup old = some value) :
    ((index, entry) :: entries).lookup old = some value := by
  have different : old ≠ index := by
    intro same
    subst old
    rw [fresh] at known
    cases known
  have unequal : (old == index) = false := by simp [different]
  simpa [List.lookup_cons, unequal] using known

theorem Step.extends {before after : Theory} {admission : Admission}
    (step : Step before admission after) : Extends before after := by
  cases step with
  | intro authorized =>
      cases authorized with
      | sort fresh =>
          exact ⟨lookup_cons_preserves _ _ _ fresh, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩
      | term fresh _ =>
          exact ⟨fun _ _ h => h, lookup_cons_preserves _ _ _ fresh, fun _ _ h => h, fun _ _ h => h⟩
      | definition fresh freshBody _ _ =>
          exact ⟨fun _ _ h => h, lookup_cons_preserves _ _ _ fresh,
            lookup_cons_preserves _ _ _ freshBody, fun _ _ h => h⟩
      | axiomDecl fresh _ =>
          exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, lookup_cons_preserves _ _ _ fresh⟩
      | theoremDecl fresh _ _ _ =>
          exact ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, lookup_cons_preserves _ _ _ fresh⟩

inductive Runs : Theory → List Admission → Theory → Prop where
  | nil (theory : Theory) : Runs theory [] theory
  | cons {before middle after : Theory} {head : Admission} {tail : List Admission} :
      Step before head middle → Runs middle tail after → Runs before (head :: tail) after

theorem Runs.extends {before after : Theory} {admissions : List Admission}
    (runs : Runs before admissions after) : Extends before after := by
  induction runs with
  | nil theory => exact .refl theory
  | cons step _ ih => exact step.extends.trans ih

def run? : Theory → List Admission → Option Theory
  | theory, [] => some theory
  | theory, admission :: remaining => do
      let next ← step? theory admission
      run? next remaining

theorem run_eq_some_iff (before after : Theory) (admissions : List Admission) :
    run? before admissions = some after ↔ Runs before admissions after := by
  induction admissions generalizing before with
  | nil =>
      constructor
      · intro same
        have same := Option.some.inj same
        subst before
        exact .nil _
      · intro runs
        cases runs
        rfl
  | cons head tail ih =>
      constructor
      · intro success
        cases step : step? before head with
        | none => simp [run?, step] at success
        | some middle =>
            have rest : run? middle tail = some after := by simpa [run?, step] using success
            exact .cons ((step_eq_some_iff _ _ _).mp step) ((ih middle).mp rest)
      · intro runs
        cases runs with
        | cons first rest =>
            simp [run?, (step_eq_some_iff _ _ _).mpr first, (ih _).mpr rest]

theorem run_append (initial : Theory) (first second : List Admission) :
    run? initial (first ++ second) = (run? initial first).bind (fun next => run? next second) := by
  induction first generalizing initial with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, run?]
      cases next : step? initial head <;> simp [ih]

end Theory

end Mettapedia.Languages.MM0.Kernel
