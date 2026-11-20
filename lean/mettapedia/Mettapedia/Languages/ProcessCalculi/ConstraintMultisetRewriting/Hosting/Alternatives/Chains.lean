import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Runs

/-!
# Histories of the step up to fresh names and row identities

A history of `RuleSyntax.step` chooses, at every firing, an extension of the frame, an opening of the
rule's unknowns and identities for the rows it makes. None of these choices is visible in what a row
reads as. This module makes that precise for histories in which every firing takes the row that the
firing before it made (`Chain`), and shows that the histories of a translated program are of that
kind.

* **A firing by a rule** (`FiresAt`): an admitted firing of a program whose rule is `r`, taking one
  row and making one.
* **The transfer of a rule** (`transfer`): for a rule that takes one row and makes one
  (`SimpleRule`), the readings of the made row as a function of the readings of the taken row.
  `fires_reads`: every admitted firing by the rule, whatever its extension, opening and made
  identity, makes a row whose readings are the transfer of the taken row's readings.
* **Chains** (`Chain`): histories labelled by their firings' rules (or by any labelling), each firing
  taking the row the one before it made. `chain_reads`: the readings of the last row of a chain are
  the transfer of the first row's readings along the **word of rules** alone.
* **The histories of a translated program are chains** (`hosted_chain`): from the start of a query
  of the first fragment, every run of the step is a chain whose rows are the alternative's rows, so
  the causal order of a history is linear: no two adjacent firings can be swapped, since the second
  takes the row the first made.
* **The answer of a history is a function of its word of rules** (`same_word_same_answer`): two
  histories with the same word end in states that show the same answer and are finished together.
  So a class of histories up to fresh names, openings, extensions and row identities is a word of
  rules, and its answer is well defined on the class.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {S : Signature}

/-- Rules of programs at the contextual frames. -/
abbrev CRule (S : Signature) := RuleSyntax.Rule (RuleSyntax.Contextual.Terms S)

/-- Programs at the contextual frames. -/
abbrev CProgram (S : Signature) := RuleSyntax.Program (RuleSyntax.Contextual.Terms S)

/-! ## Firings by a rule and the transfer of readings -/

section Transfer

/-- **One firing by the rule `r`**: an admitted firing of `Prog` whose rule is `r`, which takes the
row `o` and makes the row `o'`, with any extension and any opening. -/
def FiresAt (Prog : CProgram S) (r : CRule S) (s : HostState S) (o : ℕ) (s' : HostState S) (o' : ℕ) :
    Prop :=
  ∃ f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) Prog s.frame,
    f.rule = r ∧ f.Admits (Interface.Frames.contextual S) s ∧ f.selection.taken = [o] ∧
      f.selection.made = [o'] ∧ f.result (Interface.Frames.contextual S) s = s'

/-- A rule that takes one row by the pattern `pat`, reads none, and makes the one row `out`. -/
structure SimpleRule (r : CRule S) (pat out : Observation S r.locals.arity) : Prop where
  take : r.body.take = [pat]
  noRead : r.body.read = []
  produce : r.body.produce = [out]

/-- Readings: into every frame, the observations a row reads as. -/
abbrev Readings (S : Signature) := ∀ B : Interface.Frames.Frame S, Observation S B.arity → Prop

/-- **The transfer of a simple rule**: the readings of the row it makes, given the readings of the
row it takes. -/
def transfer (r : CRule S) (R : Readings S) : Readings S := fun B q =>
  ∃ (pat out : Observation S r.locals.arity) (h : Assignment r.locals.arity B.arity),
    SimpleRule r pat out ∧ R B (instantiateObservation h pat) ∧
      (Interface.Frames.contextual S).Models (a := r.locals) (b := B) h r.body.tell ∧
      instantiateObservation h out = q

/-- The transfer along a word of rules, the first rule first. -/
def transferWord (word : List (CRule S)) (R : Readings S) : Readings S :=
  word.foldl (fun R' r => transfer r R') R

theorem transferWord_snoc (word : List (CRule S)) (r : CRule S) (R : Readings S) :
    transferWord (word ++ [r]) R = transfer r (transferWord word R) := by
  simp [transferWord, List.foldl_append]

theorem transfer_congr (r : CRule S) {R R' : Readings S} (same : ∀ B q, R B q ↔ R' B q) :
    ∀ B q, transfer r R B q ↔ transfer r R' B q := by
  intro B q
  constructor
  · rintro ⟨pat, out, h, simple, reads, told, made⟩
    exact ⟨pat, out, h, simple, (same B _).mp reads, told, made⟩
  · rintro ⟨pat, out, h, simple, reads, told, made⟩
    exact ⟨pat, out, h, simple, (same B _).mpr reads, told, made⟩

theorem transferWord_congr (word : List (CRule S)) {R R' : Readings S} (same : ∀ B q, R B q ↔ R' B q) :
    ∀ B q, transferWord word R B q ↔ transferWord word R' B q := by
  induction word using List.reverseRecOn with
  | nil => exact same
  | append_singleton word r ih =>
      intro B q
      rw [transferWord_snoc, transferWord_snoc]
      exact transfer_congr r ih B q

/-- **A firing by a simple rule transfers readings**: whatever its extension, its opening and the
identity of the row it makes, the made row reads exactly as the transfer of the taken row. -/
theorem fires_reads {Prog : CProgram S} {r : CRule S} {pat out : Observation S r.locals.arity}
    (simple : SimpleRule r pat out) {s s' : HostState S} {o o' : ℕ} (fires : FiresAt Prog r s o s' o')
    (B : Interface.Frames.Frame S) (q : Observation S B.arity) :
    rowReads s' o' B q ↔ transfer r (rowReads s o) B q := by
  obtain ⟨f, rfl, admitted, taken, made, rfl⟩ := fires
  have shapes := admitted.1
  have readNil : f.selection.read = [] := by
    have lengths := shapes.2.2.2.2.1
    rw [simple.noRead] at lengths
    exact List.eq_nil_of_length_eq_zero lengths.symm
  have simpleFiring : Simple f o o' pat out :=
    ⟨taken, readNil, made, simple.take, simple.noRead, simple.produce⟩
  have present : o ∈ s.present := admitted.2.1.taken_subset (by simp [Selection.commit, taken])
  rw [rowReads_result simpleFiring shapes present B q]
  constructor
  · rintro ⟨h, reads, told, rfl⟩
    exact ⟨pat, out, h, simple, reads, told, rfl⟩
  · rintro ⟨pat', out', h, simple', reads, told, rfl⟩
    have samePat : pat' = pat := by
      have same := simple'.take.symm.trans simple.take
      simpa using same
    have sameOut : out' = out := by
      have same := simple'.produce.symm.trans simple.produce
      simpa using same
    subst samePat sameOut
    exact ⟨h, reads, told, rfl⟩

end Transfer

/-! ## Chains -/

section Chains

universe uL uL'

variable {L : Type uL} (fires : L → HostState S → ℕ → HostState S → ℕ → Prop)

/-- **A chain**: a history whose every firing takes the row that the firing before it made,
labelled by its firings. -/
inductive Chain : HostState S → ℕ → List L → HostState S → ℕ → Prop
  | nil (s : HostState S) (o : ℕ) : Chain s o [] s o
  | snoc {s : HostState S} {o : ℕ} {word : List L} {s₁ : HostState S} {o₁ : ℕ} {l : L}
      {s₂ : HostState S} {o₂ : ℕ} :
      Chain s o word s₁ o₁ → fires l s₁ o₁ s₂ o₂ → Chain s o (word ++ [l]) s₂ o₂

variable {fires}

theorem Chain.nil_inv {s s' : HostState S} {o o' : ℕ} (chain : Chain fires s o [] s' o') :
    s' = s ∧ o' = o := by
  generalize hw : ([] : List L) = w at chain
  cases chain with
  | nil => exact ⟨rfl, rfl⟩
  | snoc _ _ => simp at hw

theorem Chain.snoc_inv {s s₂ : HostState S} {o o₂ : ℕ} {word : List L} {l : L}
    (chain : Chain fires s o (word ++ [l]) s₂ o₂) :
    ∃ s₁ o₁, Chain fires s o word s₁ o₁ ∧ fires l s₁ o₁ s₂ o₂ := by
  generalize hw : word ++ [l] = w at chain
  cases chain with
  | nil => simp at hw
  | snoc first last =>
      have same := List.append_inj' hw rfl
      simp only [List.cons.injEq, and_true] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨_, _, first, last⟩

theorem Chain.append {s s₁ s₂ : HostState S} {o o₁ o₂ : ℕ} {u : List L} (first : Chain fires s o u s₁ o₁) :
    ∀ {v : List L}, Chain fires s₁ o₁ v s₂ o₂ → Chain fires s o (u ++ v) s₂ o₂ := by
  intro v second
  induction second with
  | nil => simpa using first
  | snoc _ last ih =>
      rw [← List.append_assoc]
      exact .snoc ih last

theorem Chain.split {s s₂ : HostState S} {o o₂ : ℕ} (u v : List L) (chain : Chain fires s o (u ++ v) s₂ o₂) :
    ∃ s₁ o₁, Chain fires s o u s₁ o₁ ∧ Chain fires s₁ o₁ v s₂ o₂ := by
  induction v using List.reverseRecOn generalizing s₂ o₂ with
  | nil => exact ⟨s₂, o₂, by simpa using chain, .nil _ _⟩
  | append_singleton v l ih =>
      rw [← List.append_assoc] at chain
      obtain ⟨s₁, o₁, front, last⟩ := chain.snoc_inv
      obtain ⟨s₀, o₀, first, middle⟩ := ih front
      exact ⟨s₀, o₀, first, .snoc middle last⟩

theorem Chain.single {s s' : HostState S} {o o' : ℕ} {l : L} (fired : fires l s o s' o') :
    Chain fires s o [l] s' o' := by
  simpa using Chain.snoc (Chain.nil (fires := fires) s o) fired

/-- Relabelling a chain. -/
theorem Chain.map {L' : Type uL'} {fires' : L' → HostState S → ℕ → HostState S → ℕ → Prop} (g : L → L')
    (along : ∀ l s o s' o', fires l s o s' o' → fires' (g l) s o s' o') {s s' : HostState S} {o o' : ℕ}
    {word : List L} (chain : Chain fires s o word s' o') : Chain fires' s o (word.map g) s' o' := by
  induction chain with
  | nil => exact .nil _ _
  | snoc _ last ih =>
      rw [List.map_append, List.map_singleton]
      exact .snoc ih (along _ _ _ _ _ last)

end Chains

/-! ## The readings at the end of a chain depend only on its word of rules -/

section Words

/-- The rule of a firing is a rule of the program. -/
theorem firesAt_mem {Prog : CProgram S} {r : CRule S} {s s' : HostState S} {o o' : ℕ}
    (fired : FiresAt Prog r s o s' o') : r ∈ Prog := by
  obtain ⟨f, rfl, _⟩ := fired
  exact f.member

/-- The rules of a chain are rules of the program. -/
theorem chain_rules_mem {Prog : CProgram S} {s s' : HostState S} {o o' : ℕ} {word : List (CRule S)}
    (chain : Chain (FiresAt Prog) s o word s' o') : ∀ r ∈ word, r ∈ Prog := by
  induction chain with
  | nil => intro r member; cases member
  | snoc _ last ih =>
      intro r member
      rcases List.mem_append.mp member with old | new
      · exact ih r old
      · obtain ⟨f, rfl, _⟩ := last
        rw [List.mem_singleton.mp new]
        exact f.member

/-- **The readings of the last row of a chain are the transfer of the first row's readings along
the word of rules**, whatever extensions, openings and made identities the chain's firings chose. -/
theorem chain_reads {Prog : CProgram S} (simple : ∀ r ∈ Prog, ∃ pat out, SimpleRule r pat out)
    {s s' : HostState S} {o o' : ℕ} {word : List (CRule S)} (chain : Chain (FiresAt Prog) s o word s' o') :
    ∀ B q, rowReads s' o' B q ↔ transferWord word (rowReads s o) B q := by
  induction chain with
  | nil => intro B q; exact Iff.rfl
  | snoc first last ih =>
      intro B q
      obtain ⟨pat, out, isSimple⟩ := simple _ (firesAt_mem last)
      rw [fires_reads isSimple last B q, transferWord_snoc]
      exact transfer_congr _ ih B q

end Words

/-! ## The histories of a translated program -/

section Hosted

variable {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

/-- **Every rule of a translation takes one row, reads none and makes one**, and its take pattern
is an alternative's row. -/
theorem translate_simple {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {r : CRule S}
    (member : r ∈ translate N P) :
    ∃ pat out, SimpleRule r pat out ∧
      ∀ {B : Interface.Frames.Frame S} (h : Assignment r.locals.arity B.arity),
        ∃ x y : Term (signature S B.arity) Γ star, instantiateObservation h pat = observe (altN N x y) := by
  rcases (mem_translate N).mp member with control | ⟨e, _, rfl⟩
  · rcases (mem_controlRules N).mp control with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨_, _, ⟨rfl, rfl, rfl⟩, fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩⟩
  · exact ⟨_, _, ⟨rfl, rfl, rfl⟩, fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩⟩

theorem translate_rules_simple {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) :
    ∀ r ∈ translate N P, ∃ pat out, SimpleRule r pat out := fun _ member =>
  let ⟨pat, out, simple, _⟩ := translate_simple N member
  ⟨pat, out, simple⟩

/-- **The alternative's row is unique**: a state represents its alternative with one row. -/
theorem alt_row_unique {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {n n' : ℕ}
    {b b' : Branch κ Γ star Ty} {s : HostState S} {a a' : ℕ} (rep : Represents N P n b s a)
    (rep' : Represents N P n' b' s a') : a = a' := by
  have inside : a ∈ insert a' (Finset.range P.equations.length) := by
    rw [← rep'.present, rep.present]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp inside with same | small
  · exact same
  · exact absurd (Finset.mem_range.mp small) (not_lt.mpr rep.notRow)

/-- **Every firing from a represented state takes the alternative's row.** -/
theorem hosted_takes {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {n : ℕ} {b : Branch κ Γ star Ty}
    {s : HostState S} {a : ℕ} (rep : Represents N P n b s a)
    {f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame}
    (admitted : f.Admits (Interface.Frames.contextual S) s) :
    ∃ a', f.selection.taken = [a] ∧ f.selection.made = [a'] ∧ a' ∉ s.present := by
  obtain ⟨pat, out, simple, altHead⟩ := translate_simple N f.member
  obtain ⟨a', simpleFiring, fresh, _⟩ :=
    admitted_takes_alternative N rep admitted simple.take simple.noRead simple.produce altHead
  exact ⟨a', simpleFiring.taken, simpleFiring.madeOne, fresh⟩

/-- A firing by a rule is a firing of the translated program. -/
theorem fires_of_firesAt {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {r : CRule S}
    {s s' : HostState S} {o o' : ℕ} (fired : FiresAt (translate N P) r s o s' o') : Fires N P s s' := by
  obtain ⟨f, _, admitted, _, _, result⟩ := fired
  exact ⟨f, admitted, result⟩

/-- **A state with no firing**: the end of a complete history. -/
def Terminal {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (s : HostState S) : Prop :=
  ∀ s', ¬ Fires N P s s'

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

/-- **The histories of a translated program are chains.** Every run of the step from the start of a
query of the first fragment is a chain from the query's alternative row: each firing takes the row the
one before it made. Its last row represents an alternative of a configuration that a source run
reaches. -/
theorem hosted_chain (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {s : HostState S}
    (run : Relation.ReflTransGen (Fires N P) (start N P q) s) :
    ∃ (word : List (CRule S)) (a : ℕ), Chain (FiresAt (translate N P)) (start N P q) P.equations.length word s a ∧
      ∃ (C : Config κ Γ star D.Ty) (b : Branch κ Γ star D.Ty),
        Runs D P supply (Config.initial spaces q) C ∧ b ∈ C.branches ∧
          Represents N P C.world.scope b s a ∧ PlainBranch b := by
  induction run with
  | refl =>
      exact ⟨[], _, .nil _ _, _, initialBranch q, .refl, Multiset.mem_singleton_self _,
        start_represents N P q unopened, rfl, .inl ⟨q, rfl, plainQ⟩⟩
  | tail _ fired ih =>
      obtain ⟨word, a, chain, C, b, runs, member, rep, plain⟩ := ih
      obtain ⟨f, admitted, result⟩ := fired
      obtain ⟨pat, out, simpleRule, altHead⟩ := translate_simple N f.member
      obtain ⟨a', simpleFiring, _, _⟩ :=
        admitted_takes_alternative N rep admitted simpleRule.take simpleRule.noRead simpleRule.produce altHead
      obtain ⟨w', bs, b', a'', move, child, rep', plain'⟩ :=
        reflection N (supply := supply) plainP rep plain ⟨f, admitted, result⟩
      have sameRow : a'' = a' := by
        have present := simple_present simpleFiring
        rw [result, rep.present] at present
        have inside : a'' ∈ insert a' ((insert a (Finset.range P.equations.length)).erase a) := by
          rw [← present, rep'.present]
          exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp inside with same | other
        · exact same
        · have kept := Finset.mem_erase.mp other
          rcases Finset.mem_insert.mp kept.2 with same | small
          · exact absurd same kept.1
          · exact absurd (Finset.mem_range.mp small) (not_lt.mpr rep'.notRow)
      subst sameRow
      obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem member
      refine ⟨word ++ [f.rule], a'',
        .snoc chain ⟨f, rfl, admitted, simpleFiring.taken, simpleFiring.madeOne, result⟩,
        ⟨w', bs + rest⟩, b', runs.tail ?_, Multiset.mem_add.mpr (.inl child), rep', plain'⟩
      obtain ⟨world, branches⟩ := C
      simp only at split
      subst split
      exact .move world w' b rest bs (live_of_fires N rep ⟨f, admitted, result⟩) move

/-- **The answer of a history is a function of its word of rules.** Two chains from the start of a
query with the same word of rules end in states that show the same answer and that are finished
together, whatever fresh names, extensions, openings and row identities their firings chose. -/
theorem same_word_same_answer (q : Comp κ Γ star D.Ty) {word : List (CRule S)} {s₁ s₂ : HostState S}
    {a₁ a₂ : ℕ}
    (chain₁ : Chain (FiresAt (translate N P)) (start N P q) P.equations.length word s₁ a₁)
    (chain₂ : Chain (FiresAt (translate N P)) (start N P q) P.equations.length word s₂ a₂) :
    stateAnswer N s₁ a₁ = stateAnswer N s₂ a₂ ∧ (StateFinished N s₁ a₁ ↔ StateFinished N s₂ a₂) := by
  have same : ∀ B q', rowReads s₁ a₁ B q' ↔ rowReads s₂ a₂ B q' := fun B q' =>
    (chain_reads (translate_rules_simple N P) chain₁ B q').trans
      (chain_reads (translate_rules_simple N P) chain₂ B q').symm
  refine ⟨?_, ?_⟩
  · ext g
    simp only [stateAnswer, Set.mem_ofPred_eq]
    exact exists_congr fun B => same B _
  · unfold StateFinished
    constructor
    · rintro ⟨⟨B, q', reads⟩, shape⟩
      exact ⟨⟨B, q', (same B q').mp reads⟩, fun B q' reads => shape B q' ((same B q').mpr reads)⟩
    · rintro ⟨⟨B, q', reads⟩, shape⟩
      exact ⟨⟨B, q', (same B q').mpr reads⟩, fun B q' reads => shape B q' ((same B q').mp reads)⟩

end Hosted

#print axioms fires_reads
#print axioms Chain.split
#print axioms chain_reads
#print axioms translate_simple
#print axioms alt_row_unique
#print axioms hosted_takes
#print axioms hosted_chain
#print axioms same_word_same_answer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives
