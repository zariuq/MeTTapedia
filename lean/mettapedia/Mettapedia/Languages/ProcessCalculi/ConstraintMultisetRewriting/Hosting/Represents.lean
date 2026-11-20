import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Freshness

/-!
# The representation of an alternative by a state of the step

A state of the step **represents** an alternative of the source (`Represents P n b s a`) when:
* its rows are the alternative's row `a` and the equation rows `0, …, m - 1` (`present`);
* **the alternative's row reads as the alternative**: into every frame `B`, the instances of row `a`
  under the solutions of the knowledge are exactly the encoded alternative under the solutions of
  its store (`reads`). This is a statement about readings, not about syntax: the knowledge may
  carry equations about the rules' own unknowns, and openings may choose any fresh names;
* every equation row reads as an instance of the equation's left side (`rows`), and its instances are
  independent of the alternative's row (`independent`): so "no equation row matches" is exactly "no
  equation matches";
* on the source side, the alternative's data depend only on names made before scope `n`
  (`fresh`), and it has no pending shared cell.

`represents_after` is the whole preservation argument for every firing that takes the alternative's
row and makes one row: given how the rule transforms readings (`transfer`), the result represents the
next alternative. It uses only `simple_restrict` and `simple_amalgamate`.

`start_represents`: the start of a query represents its initial alternative, for every query whose
names are unopened.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {Ty : Type}

/-- States of the step at the contextual frames. -/
abbrev HostState (S : Signature) := RuleSyntax.State (RuleSyntax.Contextual.Terms S) ℕ

/-- **The readings of a row**: its instances into the frame `B` under the solutions of the knowledge. -/
def rowReads (s : HostState S) (o : ℕ) (B : Interface.Frames.Frame S) (q : Observation S B.arity) : Prop :=
  ∃ σ : Assignment s.frame.arity B.arity,
    (Interface.Frames.contextual S).Models σ s.knowledge ∧ instantiateObservation σ (s.label o) = q

/-- **The readings of an alternative**: its encoding into the frame `B` under the solutions of its
store. -/
def branchReads (b : Branch κ Γ star Ty) (B : Interface.Frames.Frame S) (q : Observation S B.arity) :
    Prop :=
  ∃ σ : Assignment (fam κ) B.arity, Models σ b.store ∧ observe (encBranch N (instantiate σ) b) = q

/-- An equation row read as an instance of the equation's left side. -/
def eqnRow (e : SourceLanguage.Equation κ Γ star Ty) {B : Interface.Frames.Frame S}
    (θ : Assignment (fam κ) B.arity) : Observation S B.arity :=
  observe (eqnN N (instantiate θ e.lhs))

/-- The data of a branch depend only on names made before `n`. -/
def BranchBelow (n : ℕ) (b : Branch κ Γ star Ty) : Prop :=
  StoreBelow n b.store ∧ (∀ t ∈ focusData b.focus, DependsBelow n t) ∧
    ∀ fr ∈ b.frames, ∀ t ∈ frameData fr, DependsBelow n t

theorem BranchBelow.mono {n n' : ℕ} {b : Branch κ Γ star Ty} (below : BranchBelow n b) (le : n ≤ n') :
    BranchBelow n' b :=
  ⟨below.1.mono le, fun t member => DependsBelow.mono (below.2.1 t member) le,
    fun fr member t inside => DependsBelow.mono (below.2.2 fr member t inside) le⟩

/-- **A state represents an alternative**, with its alternative's row `a`. -/
structure Represents (P : SourceLanguage.Program κ Γ star Ty) (n : ℕ) (b : Branch κ Γ star Ty)
    (s : HostState S) (a : ℕ) : Prop where
  notRow : P.equations.length ≤ a
  present : s.present = insert a (Finset.range P.equations.length)
  reads : ∀ (B : Interface.Frames.Frame S) (q : Observation S B.arity), rowReads s a B q ↔ branchReads N b B q
  rows : ∀ (B : Interface.Frames.Frame S) (σ : Assignment s.frame.arity B.arity),
    (Interface.Frames.contextual S).Models σ s.knowledge → ∀ (i : ℕ) (hi : i < P.equations.length),
      ∃ θ : Assignment (fam κ) B.arity, instantiateObservation σ (s.label i) = eqnRow N (P.equations.get ⟨i, hi⟩) θ
  independent : ∀ (B : Interface.Frames.Frame S) (σ : Assignment s.frame.arity B.arity),
    (Interface.Frames.contextual S).Models σ s.knowledge → ∀ (i : ℕ) (hi : i < P.equations.length)
      (θ : Assignment (fam κ) B.arity), ∃ σ' : Assignment s.frame.arity B.arity,
        (Interface.Frames.contextual S).Models σ' s.knowledge ∧
        instantiateObservation σ' (s.label a) = instantiateObservation σ (s.label a) ∧
        instantiateObservation σ' (s.label i) = eqnRow N (P.equations.get ⟨i, hi⟩) θ
  fresh : BranchBelow n b
  noPending : b.pending = []

/-! ## Readings after a simple firing -/

section After

variable {Prog : RuleSyntax.Program (RuleSyntax.Contextual.Terms S)} {s : HostState S}
  {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog s.frame}
  {o o' : ℕ} {pat out : Observation S f.rule.locals.arity}

/-- **The made row's readings** are the rule's made row under the instantiations of the rule's
unknowns that solve its tells and send its take pattern to a reading of the taken row. -/
theorem rowReads_result (simple : Simple f o o' pat out)
    (shapes : f.Shapes (Interface.Frames.contextual S) s) (present : o ∈ s.present)
    (B : Interface.Frames.Frame S) (q : Observation S B.arity) :
    rowReads (f.result (Interface.Frames.contextual S) s) o' B q ↔
      ∃ h : Assignment f.rule.locals.arity B.arity, rowReads s o B (instantiateObservation h pat) ∧
        (Interface.Frames.contextual S).Models h f.rule.body.tell ∧ instantiateObservation h out = q := by
  constructor
  · rintro ⟨u, solved, rfl⟩
    obtain ⟨known, told, matched⟩ := simple_restrict simple u solved
    refine ⟨Assignment.compose u f.opening, ⟨_, known, matched.symm⟩, told, ?_⟩
    rw [simple_label_made simple shapes, instantiateObservation_comp]
  · rintro ⟨h, ⟨g, known, matched⟩, told, rfl⟩
    obtain ⟨u, solved, onOut, _⟩ := simple_amalgamate simple shapes.1 present g h known told matched.symm
    exact ⟨u, solved, by rw [simple_label_made simple shapes, onOut]⟩

end After

/-! ## Preservation of the representation -/

section Preservation

variable {P : SourceLanguage.Program κ Γ star Ty}
  {s : HostState S} {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame}
  {a a' : ℕ} {pat out : Observation S f.rule.locals.arity}

/-- **The representation is preserved** by a firing that takes the alternative's row and makes one
row, whenever the rule transforms the alternative's readings into the next alternative's readings
(`transfer`). -/
theorem represents_after {n n' : ℕ} {b b' : Branch κ Γ star Ty} (rep : Represents N P n b s a)
    (simple : Simple f a a' pat out) (shapes : f.Shapes (Interface.Frames.contextual S) s)
    (madeFresh : a' ∉ s.present)
    (transfer : ∀ (B : Interface.Frames.Frame S) (q : Observation S B.arity),
      (∃ h : Assignment f.rule.locals.arity B.arity, branchReads N b B (instantiateObservation h pat) ∧
        (Interface.Frames.contextual S).Models h f.rule.body.tell ∧ instantiateObservation h out = q) ↔
      branchReads N b' B q)
    (fresh : BranchBelow n' b') (noPending : b'.pending = []) :
    Represents N P n' b' (f.result (Interface.Frames.contextual S) s) a' := by
  have aPresent : a ∈ s.present := by rw [rep.present]; exact Finset.mem_insert_self _ _
  have aNotRow : a ∉ Finset.range P.equations.length := by
    simp only [Finset.mem_range, not_lt]; exact rep.notRow
  have a'NotRow : a' ∉ Finset.range P.equations.length := fun inside =>
    madeFresh (by rw [rep.present]; exact Finset.mem_insert_of_mem inside)
  have rowLabel : ∀ i, i < P.equations.length →
      (f.result (Interface.Frames.contextual S) s).label i = f.row (Interface.Frames.contextual S) s i := by
    intro i small
    apply simple_label_other simple
    intro same
    subst same
    exact a'NotRow (Finset.mem_range.mpr small)
  have readRow : ∀ {B : Interface.Frames.Frame S}
      (u : Assignment ((RuleSyntax.Contextual.declarations S).target f.ext).arity B.arity) (i : ℕ),
      instantiateObservation u (f.row (Interface.Frames.contextual S) s i) =
        instantiateObservation (Assignment.compose u ((RuleSyntax.Contextual.declarations S).weaken f.ext))
          (s.label i) := by
    intro B u i
    exact instantiateObservation_comp _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, fresh, noPending⟩
  · simp only [Finset.mem_range, not_lt] at a'NotRow
    exact a'NotRow
  · rw [simple_present simple, rep.present]
    ext i
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_range]
    constructor
    · rintro (same | ⟨other, same | small⟩)
      · exact .inl same
      · exact absurd same other
      · exact .inr small
    · rintro (same | small)
      · exact .inl same
      · refine .inr ⟨fun same => aNotRow ?_, .inr small⟩
        rw [← same]; exact Finset.mem_range.mpr small
  · intro B q
    rw [rowReads_result simple shapes aPresent]
    rw [← transfer]
    constructor
    · rintro ⟨h, reads, told, made⟩
      exact ⟨h, (rep.reads B _).mp reads, told, made⟩
    · rintro ⟨h, reads, told, made⟩
      exact ⟨h, (rep.reads B _).mpr reads, told, made⟩
  · intro B u solved i small
    obtain ⟨known, _, _⟩ := simple_restrict simple u solved
    obtain ⟨θ, row⟩ := rep.rows B _ known i small
    exact ⟨θ, by rw [rowLabel i small, readRow, row]⟩
  · intro B u solved i small θ
    obtain ⟨known, told, matched⟩ := simple_restrict simple u solved
    obtain ⟨g', known', sameAlt, row⟩ := rep.independent B _ known i small θ
    obtain ⟨u', solved', onOut, onRows, _⟩ := simple_amalgamate simple shapes.1 aPresent g'
      (Assignment.compose u f.opening) known' told (matched.trans sameAlt.symm)
    have iPresent : i ∈ s.present := by
      rw [rep.present]
      exact Finset.mem_insert_of_mem (Finset.mem_range.mpr small)
    refine ⟨u', solved', ?_, ?_⟩
    · rw [simple_label_made simple shapes, onOut, instantiateObservation_comp]
    · rw [rowLabel i small, onRows i iPresent, row]

end Preservation

/-! ## The start -/

section Start

variable (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty)

/-- The initial alternative of a query. -/
def initialBranch : Branch κ Γ star Ty := ⟨[], .eval q, [], []⟩

theorem instantiate_eqnN {V W : Type} {D : V → MetaArity S} {E : W → MetaArity S} (σ : Assignment D E)
    (x : Term (signature S D) Γ star) : instantiate σ (eqnN N x) = eqnN N (instantiate σ x) := by
  rw [eqnN, N.instantiate_node]
  exact congrArg _ (map_vec1 _ _)

/-- Fill the start's frame: the source's names by `σ`, every private copy by `σ` too. -/
def startFill {B : Interface.Frames.Frame S} (σ : Assignment (fam κ) B.arity) :
    Assignment (startArity κ) B.arity
  | .inl x => σ x
  | .inr p => σ p.2

/-- **The start represents the query's initial alternative**, for every query whose names are
unopened. -/
theorem start_represents (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    Represents N P 0 (initialBranch q) (start N P q) P.equations.length := by
  have altLabel : (start N P q).label P.equations.length =
      observe (encAlt N (instantiate queryNames) (.eval q) []) := by
    simp [start, startLabel]
  have readAlt : ∀ {B : Interface.Frames.Frame S} (σ : Assignment (startArity κ) B.arity),
      instantiateObservation σ ((start N P q).label P.equations.length) =
        observe (encAlt N (instantiate (fun x => σ (.inl x))) (.eval q) []) := by
    intro B σ
    rw [altLabel]
    change observe (instantiate σ _) = _
    rw [instantiate_encAlt]
    apply congrArg observe
    apply congrArg (fun g => encAlt N g (.eval q) [])
    funext t
    rw [instantiate_comp]
    apply congrArg (fun ρ => instantiate ρ t)
    funext x
    exact instantiate_generator σ (.inl x)
  have rowLabelAt : ∀ i (hi : i < P.equations.length),
      (start N P q).label i = observe (eqnN N (instantiate (rowNames i) (P.equations.get ⟨i, hi⟩).lhs)) := by
    intro i hi
    simp [start, startLabel, hi]
  have readRowAt : ∀ {B : Interface.Frames.Frame S} (σ : Assignment (startArity κ) B.arity) i
      (hi : i < P.equations.length),
      instantiateObservation σ ((start N P q).label i) =
        eqnRow N (P.equations.get ⟨i, hi⟩) (fun x => σ (.inr (i, x))) := by
    intro B σ i hi
    rw [rowLabelAt i hi]
    change observe (instantiate σ _) = _
    rw [instantiate_eqnN, instantiate_comp]
    apply congrArg (fun ρ => observe (eqnN N (instantiate ρ (P.equations.get ⟨i, hi⟩).lhs)))
    funext x
    exact instantiate_generator σ (.inr (i, x))
  have noKnowledge : ∀ {B : Interface.Frames.Frame S} (σ : Assignment (startArity κ) B.arity),
      (Interface.Frames.contextual S).Models σ (start N P q).knowledge := by
    intro B σ e member
    simp [start] at member
  have noStore : ∀ {B : Interface.Frames.Frame S} (σ : Assignment (fam κ) B.arity),
      Models σ (initialBranch (Ty := Ty) q).store := by
    intro B σ e member
    simp [initialBranch] at member
  refine ⟨le_refl _, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · intro B r
    constructor
    · rintro ⟨σ, _, rfl⟩
      exact ⟨fun x => σ (.inl x), noStore _, (readAlt σ).symm⟩
    · rintro ⟨σ, _, rfl⟩
      refine ⟨startFill σ, noKnowledge _, ?_⟩
      rw [readAlt]
      rfl
  · intro B σ _ i hi
    exact ⟨_, readRowAt σ i hi⟩
  · intro B σ _ i hi θ
    let σ' : Assignment (startArity κ) B.arity := fun y => match y with
      | .inl x => σ (.inl x)
      | .inr p => if p.1 = i then θ p.2 else σ (.inr p)
    refine ⟨σ', noKnowledge _, ?_, ?_⟩
    · rw [readAlt, readAlt]
    · rw [readRowAt σ' i hi]
      congr 1
      funext x
      simp [σ']
  · refine ⟨?_, ?_, ?_⟩
    · intro e member
      simp [initialBranch] at member
    · intro t member
      exact dependsBelow_of_unopened 0 (unopened t member)
    · intro fr member
      simp [initialBranch] at member

end Start

#print axioms rowReads_result
#print axioms represents_after
#print axioms start_represents

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting
