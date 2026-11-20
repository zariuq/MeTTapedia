import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.ArrowSteps

/-!
# Every named history of the first fragment has a canonical history with the same word

A named history (`NamedFrom`) fires the rules its names denote with any extension of the frame and
any fresh opening. The canonical firing of a rule (`FiresNamedCanonical`: the extension by the rule's
own declarations, each unknown sent to its own new name) is one of these choices. For a program and
a query of the first fragment (`ret`, `apply`, `choice`, `fail`):

* `canonical_chain_of_named`, `canonical_representative`: **every named history has a canonical
  history with the same word of names**, and the last states of the two histories represent one
  alternative of the source at one world. The last state and the last row may differ. Each named
  firing is reflected to the source's named move of the represented alternative
  (`reflection_named`); the child is live because the firing was admitted (`live_of_named`); the
  move is replayed by the canonical firing from the canonical history's last state
  (`simulation_named_canonical`), making a row that is not present (`freshId`).
* `named_chains_one_alternative`, `namedFrom_one_alternative`: two named histories with one word
  end in states that represent one alternative at one world, since a name selects one child; so
  every canonical history of the word, not only the one built above, is a representative
  (`canonical_every_representative`).
* `canonical_chain_named`: every canonical history is a named history with the same word.
* `firesNamed_of_fires`, `represented_terminal_iff`, `represented_status`: from a represented
  alternative of the fragment every firing is named; the state has no firing exactly when no named
  move of the alternative makes a live child; two states that represent one alternative of the
  fragment at one world show the same answer, are finished together, and have a firing together.
* For classes (`named_word_iff_canonical`, `completeClass_iff_canonical`,
  `finishedClass_iff_canonical`, `classAnswer_eq_canonical`): the words of named histories, the
  complete and the finished classes, and the answers of classes are those of canonical histories;
  so `bag_of_classes` reads the bag of answers off canonical histories (`bag_of_canonical_classes`).
* `fire_simple_fresh`: a firing of a simple rule with any fresh opening, not only the canonical one,
  that takes the alternative's row and makes a row not present, is admitted (given its guard) when
  the rule takes the alternative's readings to a live alternative's readings, and its result
  represents that alternative; `fire_simple_canonical` is the case of the canonical opening.

Nothing here counts histories of the native step.

## Controls (`CanonicalHistoryControls`)

* `possibly_new_endpoint`: the query `(ret one)` has a named history whose firing opens `ret` with
  the datum and the pattern exchanged (`swappedOpening`); no canonical history of its word ends in
  its last state (`swappedEnd_not_canonical`), and its canonical representatives end elsewhere,
  representing the same alternative. `q1_complete_classes`: both sides of
  `completeClass_iff_canonical` on that query, a complete word and a word that is not complete.
* `example_canonical_bag`: the hypotheses of `bag_of_canonical_classes` hold of the run of
  `ExampleChoice`.
* Outside the fragment, the query `(let one (ret one) (ret one))`: its start represents no
  alternative of the fragment (`let_start_represents_no_plain`, by `no_plain_beside_let`), so the
  conclusion of `canonical_representative` fails already for its empty history, whose canonical
  history is the empty one; and its start has a firing although it has no named firing and its
  alternative has no named move (`let_start_no_named_firing`, `let_fires_without_named_move`), so
  outside the fragment `firesNamed_of_fires` and `represented_terminal_iff` fail.
* Outside the fragment by the program: `(f)` with the equation `(= (f) (let one (ret one) (ret one)))`
  has a canonical named history `[eqn 0]` whose last state represents no alternative of the
  fragment (`eqn_let_represents_no_plain`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

section Theory

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

/-! ## Firing a simple rule with any fresh opening -/

/-- **Firing a simple rule with any fresh opening**: a firing that takes the alternative's row by its
one take pattern and makes a row not present, whatever its extension and its fresh opening, is
admitted (given its guard) when the rule transforms the alternative's readings into a live
alternative's readings, and its result represents that alternative. -/
theorem fire_simple_fresh {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {s : HostState S}
    (f : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame)
    {pat out : Observation S f.rule.locals.arity} {a k : ℕ} (simple : Simple f a k pat out)
    (fresh : f.Fresh (Interface.Frames.contextual S) s) (hcollect : f.rule.collect = [])
    (hseen : f.seen = []) {n n' : ℕ} {b b' : Branch κ Γ star Ty} (rep : Represents N P n b s a)
    (moves : ∀ (B : Interface.Frames.Frame S) (q : Observation S B.arity),
      (∃ h : Assignment f.rule.locals.arity B.arity, branchReads N b B (instantiateObservation h pat) ∧
        (Interface.Frames.contextual S).Models h f.rule.body.tell ∧ instantiateObservation h out = q) ↔
      branchReads N b' B q)
    (live : Solvable b'.store) (hk : k ∉ s.present)
    (guard : (Interface.Frames.contextual S).Entails (f.information (Interface.Frames.contextual S) s)
      (fun _ σ => f.Holds (Interface.Frames.contextual S) s σ))
    (below : BranchBelow n' b') (noPending : b'.pending = []) :
    f.Admits (Interface.Frames.contextual S) s ∧
      Represents N P n' b' (f.result (Interface.Frames.contextual S) s) k := by
  have shapes : f.Shapes (Interface.Frames.contextual S) s := by
    refine ⟨fresh, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [simple.taken]; exact List.nodup_singleton a
    · rw [simple.madeOne]; exact List.nodup_singleton k
    · simp only [simple.take, simple.taken, List.length_singleton]
    · simp only [simple.noReadPattern, simple.noRead, List.length_nil]
    · simp only [simple.produce, simple.madeOne, List.length_singleton]
    · simp only [hcollect, hseen, List.length_nil]
  have aPresent : a ∈ s.present := by rw [rep.present]; exact Finset.mem_insert_self _ _
  have enabled : Enabled (fun _ : ℕ => ()) s.present (f.selection.commit (T := Unit)) := by
    have commit : f.selection.commit (T := Unit) = (⟨[a], [], [k]⟩ : Selection ℕ).commit := by
      simp only [Selection.commit, simple.taken, simple.noRead, simple.madeOne]
    rw [commit]
    exact enabled_single aPresent hk
  have solvable : (Interface.Frames.contextual S).Solvable
      (f.information (Interface.Frames.contextual S) s) := by
    obtain ⟨W, target, σ, solved⟩ := live
    have reads : branchReads N b' ⟨W, target⟩ (observe (encBranch N (instantiate σ) b')) :=
      ⟨σ, solved, rfl⟩
    obtain ⟨h, readsB, told, _⟩ := (moves _ _).mpr reads
    obtain ⟨g, known, matched⟩ := (rep.reads _ _).mpr readsB
    obtain ⟨u, solvedU, _⟩ := simple_amalgamate simple fresh aPresent g h known told matched.symm
    exact ⟨_, u, solvedU⟩
  exact ⟨⟨shapes, enabled, solvable, guard⟩,
    represents_after N rep simple shapes hk moves below noPending⟩

/-! ## The canonical representative of a named history -/

section Representatives

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}

/-- **Canonical replay of a named chain.** From a state that represents an alternative of the first
fragment, every named chain is followed, name by name, by a chain of canonical named firings with
the same word, and the last states of the two chains represent one alternative at one world. Each
canonical firing makes a row not present (`freshId`). -/
theorem canonical_chain_of_named (plainP : PlainProgram P) {w₀ : World κ Γ star}
    {b₀ : Branch κ Γ star D.Ty} {s₀ : HostState S} {a₀ : ℕ} (rep₀ : Represents N P w₀.scope b₀ s₀ a₀)
    (plain₀ : PlainBranch b₀) {word : List RuleName} {s : HostState S} {a : ℕ}
    (chain : Chain (FiresNamed N P) s₀ a₀ word s a) :
    ∃ s' a', Chain (FiresNamedCanonical N P) s₀ a₀ word s' a' ∧
      ∃ (w : World κ Γ star) (b : Branch κ Γ star D.Ty),
        Represents N P w.scope b s a ∧ Represents N P w.scope b s' a' ∧ PlainBranch b := by
  induction chain with
  | nil => exact ⟨s₀, a₀, .nil _ _, w₀, b₀, rep₀, rep₀, plain₀⟩
  | snoc _ fired ih =>
      obtain ⟨s₁, a₁, canonical, w, b, rep, rep', plain⟩ := ih
      obtain ⟨w₂, b₂, move, rep₂, plain₂⟩ := reflection_named N plainP rep plain fired
      obtain ⟨s₂, replayed, rep₂', _⟩ := simulation_named_canonical N plainP move rep' plain
        (live_of_named N fired rep₂) (freshId_not_mem s₁)
      exact ⟨s₂, freshId s₁, .snoc canonical replayed, w₂, b₂, rep₂, rep₂', plain₂⟩

/-- **Every named history has a canonical representative with the same word.** For a program and a
query of the first fragment whose names are unopened, every named history from the start has a
canonical history from the start with the same word of names, and the last states of the two
histories represent one alternative of the fragment at one world. The canonical history's last state
and last row may differ from the named history's. -/
theorem canonical_representative (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {word : List RuleName} {s : HostState S} {a : ℕ} (history : NamedFrom N P q word s a) :
    ∃ s' a', Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s' a' ∧
      ∃ (w : World κ Γ star) (b : Branch κ Γ star D.Ty),
        Represents N P w.scope b s a ∧ Represents N P w.scope b s' a' ∧ PlainBranch b :=
  canonical_chain_of_named N plainP (w₀ := ⟨0, 0, fun _ => 0⟩) (start_represents N P q unopened)
    ⟨rfl, .inl ⟨q, rfl, plainQ⟩⟩ history

/-- **One word, one alternative**: from a state that represents an alternative of the first fragment,
two named chains with one word end in states that represent one alternative at one world. A name
selects one child (`NamedMove.unique`). -/
theorem named_chains_one_alternative (plainP : PlainProgram P) {w₀ : World κ Γ star}
    {b₀ : Branch κ Γ star D.Ty} {s₀ : HostState S} {a₀ : ℕ} (rep₀ : Represents N P w₀.scope b₀ s₀ a₀)
    (plain₀ : PlainBranch b₀) (word : List RuleName) :
    ∀ {s₁ s₂ : HostState S} {a₁ a₂ : ℕ}, Chain (FiresNamed N P) s₀ a₀ word s₁ a₁ →
      Chain (FiresNamed N P) s₀ a₀ word s₂ a₂ →
      ∃ (w : World κ Γ star) (b : Branch κ Γ star D.Ty),
        Represents N P w.scope b s₁ a₁ ∧ Represents N P w.scope b s₂ a₂ ∧ PlainBranch b := by
  induction word using List.reverseRecOn with
  | nil =>
      intro s₁ s₂ a₁ a₂ first second
      obtain ⟨rfl, rfl⟩ := first.nil_inv
      obtain ⟨rfl, rfl⟩ := second.nil_inv
      exact ⟨w₀, b₀, rep₀, rep₀, plain₀⟩
  | append_singleton word l ih =>
      intro s₁ s₂ a₁ a₂ first second
      obtain ⟨t₁, c₁, before₁, fired₁⟩ := first.snoc_inv
      obtain ⟨t₂, c₂, before₂, fired₂⟩ := second.snoc_inv
      obtain ⟨w, b, rep₁, rep₂, plain⟩ := ih before₁ before₂
      obtain ⟨w₁, b₁, move₁, rep₁', plain₁⟩ := reflection_named N plainP rep₁ plain fired₁
      obtain ⟨w₂, b₂, move₂, rep₂', _⟩ := reflection_named N plainP rep₂ plain fired₂
      obtain ⟨rfl, rfl⟩ := NamedMove.unique move₁ move₂
      exact ⟨w₁, b₁, rep₁', rep₂', plain₁⟩

/-- **One word, one alternative, from the start**: for a program and a query of the first fragment
whose names are unopened, two named histories with one word end in states that represent one
alternative of the fragment at one world. -/
theorem namedFrom_one_alternative (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {word : List RuleName} {s₁ s₂ : HostState S} {a₁ a₂ : ℕ} (first : NamedFrom N P q word s₁ a₁)
    (second : NamedFrom N P q word s₂ a₂) :
    ∃ (w : World κ Γ star) (b : Branch κ Γ star D.Ty),
      Represents N P w.scope b s₁ a₁ ∧ Represents N P w.scope b s₂ a₂ ∧ PlainBranch b :=
  named_chains_one_alternative N plainP (w₀ := ⟨0, 0, fun _ => 0⟩) (start_represents N P q unopened)
    ⟨rfl, .inl ⟨q, rfl, plainQ⟩⟩ word first second

end Representatives

/-- **Forgetting canonicity**: every chain of canonical named firings is a named chain with the same
word. -/
theorem canonical_chain_named {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {s s' : HostState S}
    {o o' : ℕ} {word : List RuleName} (chain : Chain (FiresNamedCanonical N P) s o word s' o') :
    Chain (FiresNamed N P) s o word s' o' := by
  have forgotten := chain.map (fires' := FiresNamed N P) id
    (fun _ _ _ _ _ fired => FiresNamedCanonical.firesNamed N fired)
  rwa [List.map_id] at forgotten

/-! ## What a represented alternative decides -/

section Status

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}

/-- **Every firing from a represented alternative of the fragment is named**: it is a firing by one
of the names, taking the alternative's row. -/
theorem firesNamed_of_fires {n : ℕ} {b : Branch κ Γ star D.Ty} {s s' : HostState S} {a : ℕ}
    (rep : Represents N P n b s a) (plain : PlainBranch b) (fires : Fires N P s s') :
    ∃ (name : RuleName) (a' : ℕ), FiresNamed N P name s a s' a' := by
  obtain ⟨f, admitted, result⟩ := fires
  obtain ⟨a', taken, made, _⟩ := hosted_takes N rep admitted
  obtain ⟨notStart, notValue⟩ := no_bind_firing N rep plain admitted
  have named : ∃ name, ruleNamed N P name = some f.rule := by
    rcases (mem_translate N).mp f.member with control | ⟨e, eMember, same⟩
    · rcases (mem_controlRules N).mp control with h | h | h | h | h | h
      · exact ⟨.ret, by rw [h]; rfl⟩
      · exact ⟨.unmatched, by rw [h]; rfl⟩
      · exact ⟨.left, by rw [h]; rfl⟩
      · exact ⟨.right, by rw [h]; rfl⟩
      · exact absurd h notStart
      · exact absurd h notValue
    · obtain ⟨i, small, rfl⟩ := List.getElem_of_mem eMember
      exact ⟨.eqn i, by simp [ruleNamed, List.getElem?_eq_getElem small, same]⟩
  obtain ⟨name, hname⟩ := named
  exact ⟨name, a', f.rule, hname, f, rfl, admitted, taken, made, result⟩

/-- **A represented alternative of the fragment decides whether its state has a firing**: the state
has none exactly when no named move of the alternative makes a live child. -/
theorem represented_terminal_iff (plainP : PlainProgram P) {w : World κ Γ star}
    {b : Branch κ Γ star D.Ty} {s : HostState S} {a : ℕ} (rep : Represents N P w.scope b s a)
    (plain : PlainBranch b) :
    Terminal N P s ↔
      ∀ (n : RuleName) (w' : World κ Γ star) (b' : Branch κ Γ star D.Ty),
        NamedMove P w b n w' b' → ¬ Solvable b'.store := by
  constructor
  · intro terminal n w' b' move live
    obtain ⟨s', fired, _, _⟩ := simulation_named N plainP move rep plain live (freshId_not_mem s)
    exact terminal s' (firesNamed_fires N fired)
  · intro none s' fires
    obtain ⟨n, a', fired⟩ := firesNamed_of_fires N rep plain fires
    obtain ⟨w', b', move, rep', _⟩ := reflection_named N plainP rep plain fired
    exact none n w' b' move (live_of_named N fired rep')

/-- **Two states that represent one alternative of the fragment at one world** show the same answer,
are finished together, and have a firing together. -/
theorem represented_status (plainP : PlainProgram P) {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {s₁ s₂ : HostState S} {a₁ a₂ : ℕ} (rep₁ : Represents N P w.scope b s₁ a₁)
    (rep₂ : Represents N P w.scope b s₂ a₂) (plain : PlainBranch b) :
    stateAnswer N s₁ a₁ = stateAnswer N s₂ a₂ ∧ (StateFinished N s₁ a₁ ↔ StateFinished N s₂ a₂) ∧
      (Terminal N P s₁ ↔ Terminal N P s₂) := by
  have same : ∀ B q, rowReads s₁ a₁ B q ↔ rowReads s₂ a₂ B q := fun B q =>
    (rep₁.reads B q).trans (rep₂.reads B q).symm
  refine ⟨?_, ?_, (represented_terminal_iff N plainP rep₁ plain).trans
    (represented_terminal_iff N plainP rep₂ plain).symm⟩
  · ext g
    simp only [stateAnswer, Set.mem_ofPred_eq]
    exact exists_congr fun B => same B _
  · unfold StateFinished
    constructor
    · rintro ⟨⟨B, q, reads⟩, shape⟩
      exact ⟨⟨B, q, (same B q).mp reads⟩, fun B q reads => shape B q ((same B q).mpr reads)⟩
    · rintro ⟨⟨B, q, reads⟩, shape⟩
      exact ⟨⟨B, q, (same B q).mpr reads⟩, fun B q reads => shape B q ((same B q).mp reads)⟩

/-- **A canonical representative with the same status**: every named history from the start has a
canonical history with the same word whose last state shows the same answer, is finished together
with the named history's last state, and has a firing together with it. -/
theorem canonical_representative_status (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {word : List RuleName} {s : HostState S} {a : ℕ} (history : NamedFrom N P q word s a) :
    ∃ s' a', Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s' a' ∧
      stateAnswer N s a = stateAnswer N s' a' ∧ (StateFinished N s a ↔ StateFinished N s' a') ∧
      (Terminal N P s ↔ Terminal N P s') := by
  obtain ⟨s', a', canonical, w, b, rep, rep', plain⟩ :=
    canonical_representative N plainP q plainQ unopened history
  exact ⟨s', a', canonical, represented_status N plainP rep rep' plain⟩

/-- **Every canonical history of the word is a representative**: a named history and any canonical
history with the same word, both from the start, end in states that represent one alternative of the
fragment at one world, show the same answer, are finished together, and have a firing together. -/
theorem canonical_every_representative (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {word : List RuleName} {s s' : HostState S} {a a' : ℕ} (history : NamedFrom N P q word s a)
    (canonical : Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s' a') :
    (∃ (w : World κ Γ star) (b : Branch κ Γ star D.Ty),
      Represents N P w.scope b s a ∧ Represents N P w.scope b s' a' ∧ PlainBranch b) ∧
      stateAnswer N s a = stateAnswer N s' a' ∧ (StateFinished N s a ↔ StateFinished N s' a') ∧
      (Terminal N P s ↔ Terminal N P s') := by
  obtain ⟨w, b, rep, rep', plain⟩ :=
    namedFrom_one_alternative N plainP q plainQ unopened history (canonical_chain_named N canonical)
  exact ⟨⟨w, b, rep, rep', plain⟩, represented_status N plainP rep rep' plain⟩

end Status

/-! ## Classes by canonical histories -/

section Classes

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}

/-- **The words of named histories are the words of canonical histories.** -/
theorem named_word_iff_canonical (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (word : List RuleName) :
    (∃ s a, NamedFrom N P q word s a) ↔
      ∃ s a, Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s a := by
  constructor
  · rintro ⟨s, a, history⟩
    obtain ⟨s', a', canonical, _⟩ := canonical_representative N plainP q plainQ unopened history
    exact ⟨s', a', canonical⟩
  · rintro ⟨s, a, canonical⟩
    exact ⟨s, a, canonical_chain_named N canonical⟩

/-- **A class is complete exactly when one of its canonical histories ends in a state with no
firing.** -/
theorem completeClass_iff_canonical (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (word : List RuleName) :
    CompleteClass N P q word ↔
      ∃ s a, Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s a ∧
        Terminal N P s := by
  constructor
  · rintro ⟨s, a, history, terminal⟩
    obtain ⟨s', a', canonical, _, _, same⟩ :=
      canonical_representative_status N plainP q plainQ unopened history
    exact ⟨s', a', canonical, same.mp terminal⟩
  · rintro ⟨s, a, canonical, terminal⟩
    exact ⟨s, a, canonical_chain_named N canonical, terminal⟩

/-- **A class is finished exactly when one of its canonical histories ends in a finished state.** -/
theorem finishedClass_iff_canonical (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (word : List RuleName) :
    FinishedClass N P q word ↔
      ∃ s a, Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s a ∧
        StateFinished N s a := by
  constructor
  · rintro ⟨s, a, history, finished⟩
    obtain ⟨s', a', canonical, _, same, _⟩ :=
      canonical_representative_status N plainP q plainQ unopened history
    exact ⟨s', a', canonical, same.mp finished⟩
  · rintro ⟨s, a, canonical, finished⟩
    exact ⟨s, a, canonical_chain_named N canonical, finished⟩

/-- **The answer of a class is what the last states of its canonical histories show.** -/
theorem classAnswer_eq_canonical (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (word : List RuleName) :
    classAnswer N P q word =
      {g | ∃ s a, Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s a ∧
        g ∈ stateAnswer N s a} := by
  ext g
  constructor
  · rintro ⟨s, a, history, shown⟩
    obtain ⟨s', a', canonical, same, _, _⟩ :=
      canonical_representative_status N plainP q plainQ unopened history
    exact ⟨s', a', canonical, by rw [← same]; exact shown⟩
  · rintro ⟨s, a, canonical, shown⟩
    exact ⟨s, a, canonical_chain_named N canonical, shown⟩

end Classes

/-! ## The bag of answers from canonical histories -/

section Bag

open Classical

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

/-- **The bag of answers is read off canonical histories.** For a program and a query of the first
fragment whose names are unopened, and every source run that ends: the words some canonical history
of which ends in a state with no firing, each counted once, form a multiset `M`, and the bag of
answers is, over the words of `M` some canonical history of which ends finished, what the last
states of their canonical histories show. This is `bag_of_classes` with every class read through its
canonical histories. -/
theorem bag_of_canonical_classes (spaces : Term S Γ star → Multiset (Row κ Γ star))
    (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ M : Multiset (List RuleName),
      (∀ word, M.count word =
        if ∃ s a, Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s a ∧
          Terminal N P s then 1 else 0) ∧
      C.answers (D := D) =
        (M.filter fun word => ∃ s a,
          Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s a ∧
            StateFinished N s a).map
          fun word => {g | ∃ s a,
            Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s a ∧
              g ∈ stateAnswer N s a} := by
  obtain ⟨M, count, answers⟩ := bag_of_classes N spaces q plainP plainQ unopened runs quiet
  refine ⟨M, fun word => ?_, ?_⟩
  · rw [count word]
    by_cases complete : CompleteClass N P q word
    · rw [if_pos complete,
        if_pos ((completeClass_iff_canonical N plainP q plainQ unopened word).mp complete)]
    · rw [if_neg complete,
        if_neg fun c => complete ((completeClass_iff_canonical N plainP q plainQ unopened word).mpr c)]
  · rw [answers]
    have filters : M.filter (FinishedClass N P q) = M.filter fun word => ∃ s a,
        Chain (FiresNamedCanonical N P) (start N P q) P.equations.length word s a ∧
          StateFinished N s a :=
      Multiset.filter_congr fun word _ => finishedClass_iff_canonical N plainP q plainQ unopened word
    rw [filters]
    exact Multiset.map_congr rfl fun word _ => classAnswer_eq_canonical N plainP q plainQ unopened word

end Bag

end Theory

/-! ## Controls -/

namespace CanonicalHistoryControls

/-! ### An opening of `ret` that is not the canonical one -/

section Swapped

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)

/-- Exchange the datum and the pattern among the unknowns of a control rule. -/
def swapDatum : Unknown → Unknown
  | .datum => .pattern
  | .pattern => .datum
  | .first => .first
  | .second => .second
  | .stack => .stack

theorem swapDatum_swapDatum (x : Unknown) : swapDatum (swapDatum x) = x := by
  cases x <;> rfl

/-- **An opening of a control rule that is not the canonical one**: every unknown goes to a new
name, the datum and the pattern each to the other's. -/
def swappedOpening (F : Interface.Frames.Frame S) :
    Assignment (controlFrame Γ star).arity (RuleSyntax.Contextual.extend S F (controlFrame Γ star)).arity :=
  fun x => generator (RuleSyntax.Contextual.extend S F (controlFrame Γ star)).arity (.inr (swapDatum x))

theorem copair_swapped {F B : Interface.Frames.Frame S} (g : Assignment F.arity B.arity)
    (h : Assignment (controlFrame Γ star).arity B.arity) (t : Observation S (controlFrame Γ star).arity) :
    instantiateObservation
        (RuleSyntax.Contextual.copair S (N := controlFrame Γ star) g (fun x => h (swapDatum x)))
        (instantiateObservation (swappedOpening (Γ := Γ) (star := star) F) t) =
      instantiateObservation h t := by
  rw [instantiateObservation_comp]
  congr 1
  funext x
  exact (instantiate_generator _ _).trans (by cases x <;> rfl)

/-- The firing of `ret` opened by `swappedOpening`, taking the row `a` and making the row `k`. -/
def swappedRet {κ : Keys S} {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (s : HostState S)
    (a k : ℕ) : RuleSyntax.Firing ℕ (RuleSyntax.Contextual.declarations S) (translate N P) s.frame :=
  ⟨retRule N, retRule_mem N P, controlFrame Γ star, swappedOpening (Γ := Γ) (star := star) s.frame,
    ⟨[a], [], [k]⟩, []⟩

theorem swappedRet_simple {κ : Keys S} {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty)
    (s : HostState S) (a k : ℕ) :
    Simple (swappedRet N P s a k) a k (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack)))
      (observe (altN N (valueN N (unk .datum)) (unk .stack))) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The swapped opening is fresh at every state**, by the coproduct property of the extended
frame, as the canonical opening is (`RuleSyntax.Contextual.canonical_fresh`). -/
theorem swappedRet_fresh {κ : Keys S} {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty)
    (s : HostState S) (a k : ℕ) :
    (swappedRet N P s a k).Fresh (Interface.Frames.contextual S) s := by
  intro B g h
  exact ⟨RuleSyntax.Contextual.copair S (N := controlFrame Γ star) g (fun x => h (swapDatum x)),
    fun t _ => RuleSyntax.Contextual.copair_weaken S g _ t, fun t _ => copair_swapped g h t⟩

/-- **The swapped firing of `ret` is admitted** wherever the alternative returns a datum and its
store is live, and its result represents the returned alternative. -/
theorem swappedRet_fires {κ : Keys S} {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty} {n : ℕ}
    {K : List (Constraint κ Γ star)} {t : Data κ Γ star} {fs : List (SourceLanguage.Frame κ Γ star Ty)}
    {ps : List (Data κ Γ star × Comp κ Γ star Ty)} {s : HostState S} {a k : ℕ}
    (rep : Represents N P n ⟨K, .eval (.ret t), fs, ps⟩ s a) (live : Solvable K) (hk : k ∉ s.present) :
    FiresNamed N P .ret s a ((swappedRet N P s a k).result (Interface.Frames.contextual S) s) k ∧
      Represents N P n ⟨K, .value t, fs, ps⟩
        ((swappedRet N P s a k).result (Interface.Frames.contextual S) s) k := by
  obtain ⟨admitted, rep'⟩ := fire_simple_fresh N (swappedRet N P s a k) (swappedRet_simple N P s a k)
    (swappedRet_fresh N P s a k) rfl rfl rep (fun B q => transfer_ret N rfl q) live hk
    (entails_of_no_checks rfl rfl) (branchBelow_focus rep.fresh rfl rfl (by simp [focusData, Comp.data]))
    rep.noPending
  exact ⟨⟨retRule N, rfl, swappedRet N P s a k, rfl, admitted, rfl, rfl, rfl⟩, rep'⟩

/-- The unknown at the head of a term, if its head is an unknown. -/
def headUnknown {V : Type} {decl : V → MetaArity S} {Δ : Ctx S} {sort : S.Srt} :
    Term (signature S decl) Δ sort → Option V
  | .op (.inr op) _ => some op.key
  | _ => none

/-- The canonical opening and the swapped opening send the datum to different names. -/
theorem canonical_datum_ne_swapped (F : Interface.Frames.Frame S) :
    RuleSyntax.Contextual.canonicalOpening S F (controlFrame Γ star) .datum ≠
      swappedOpening (Γ := Γ) (star := star) F .datum := by
  intro same
  have heads := congrArg headUnknown same
  change some (Sum.inr Unknown.datum) = some (Sum.inr (swapDatum Unknown.datum)) at heads
  simp [swapDatum] at heads

/-- Two openings of `ret` that read its take pattern alike send the datum alike. -/
theorem retPattern_datum {B : Interface.Frames.Frame S} {o₁ o₂ : Assignment (unknownArity Γ star) B.arity}
    (same : instantiateObservation o₁ (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack))) =
      instantiateObservation o₂ (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack)))) :
    o₁ .datum = o₂ .datum := by
  change observe (instantiate o₁ _) = observe (instantiate o₂ _) at same
  have terms := observe_injective same
  simp only [instantiate_altN, instantiate_evalN, instantiate_retN, instantiate_unk] at terms
  have outer := vec2_inj (N.args_eq terms)
  exact vec1_inj (N.args_eq (vec1_inj (N.args_eq outer.1)))

/-- **The canonical firing of `ret` does not make the swapped firing's state**, from a state with no
knowledge, whatever rows the two make: the knowledge records the opening. -/
theorem canonical_ne_swapped {κ : Keys S} {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty)
    (s : HostState S) (noKnowledge : s.knowledge = []) (member : retRule N ∈ translate N P) (a k k' : ℕ) :
    (RuleSyntax.Contextual.canonical (F := s.frame) (retRule N) member ⟨[a], [], [k']⟩ []).result
        (Interface.Frames.contextual S) s ≠
      (swappedRet N P s a k).result (Interface.Frames.contextual S) s := by
  intro same
  have simple₁ : Simple (RuleSyntax.Contextual.canonical (F := s.frame) (retRule N) member ⟨[a], [], [k']⟩ [])
      a k' (observe (altN N (evalN N (retN N (unk .datum))) (unk .stack)))
      (observe (altN N (valueN N (unk .datum)) (unk .stack))) := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have info : (RuleSyntax.Contextual.canonical (F := s.frame) (retRule N) member ⟨[a], [], [k']⟩ []).information
        (Interface.Frames.contextual S) s =
      (swappedRet N P s a k).information (Interface.Frames.contextual S) s :=
    eq_of_heq (congr_arg_heq (fun st : HostState S => st.knowledge) same)
  rw [simple_information simple₁, simple_information (swappedRet_simple N P s a k), noKnowledge] at info
  simp only [Interface.Frames.applyStore, List.map_nil, List.nil_append, List.append_nil,
    List.singleton_append, List.cons.injEq, Prod.mk.injEq] at info
  exact canonical_datum_ne_swapped s.frame (retPattern_datum N info.1.1)

end Swapped

/-! ### A state that represents an alternative computing a `let` -/

section BesideLet

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)

/-- **A state that represents a live alternative computing a `let` represents no alternative of the
fragment**, at any scope and any row: its alternative's row reads as `alt(eval(bind …), …)`. -/
theorem no_plain_beside_let {κ : Keys S} {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}
    {n n' : ℕ} {b₁ b : Branch κ Γ star Ty} {s : HostState S} {a a' : ℕ}
    (rep₁ : Represents N P n b₁ s a) {site : κ.Site} {p : Data κ Γ star} {c k : Comp κ Γ star Ty}
    (focus₁ : b₁.focus = .eval (.let_ site p c k)) (live₁ : Solvable b₁.store)
    (rep : Represents N P n' b s a') : ¬ PlainBranch b := by
  intro plain
  have row := alt_row_unique N rep₁ rep
  subst row
  obtain ⟨W, target, σ, solved⟩ := live₁
  have reads₁ : branchReads N b₁ ⟨W, target⟩ (observe (encBranch N (instantiate σ) b₁)) :=
    ⟨σ, solved, rfl⟩
  have readsB := (rep.reads _ _).mp ((rep₁.reads _ _).mpr reads₁)
  rw [encBranch, encAlt, focus₁] at readsB
  obtain ⟨σ', c', _, focus, onComp, _⟩ := focus_eval_of_reads N readsB
  obtain ⟨_, _, _, _, rfl, _⟩ := bind_eq_encComp N (instantiate σ') onComp
  obtain ⟨_, ⟨c'', same, pc⟩ | ⟨_, same⟩⟩ := plain
  · rw [focus] at same
    cases same
    exact pc
  · rw [focus] at same
    cases same

end BesideLet

/-! ### `(ret one)`: a named history and its canonical representatives end in different states -/

section RetOne

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Alternatives.Controls

/-- The last state of the history of `(ret one)` whose one firing opens `ret` by `swappedOpening`,
making the row `1`. -/
abbrev swappedEnd : HostState MSig :=
  (swappedRet N emptyP (Hosting.start N emptyP q1) 0 1).result (Interface.Frames.contextual MSig)
    (Hosting.start N emptyP q1)

/-- The named history of `(ret one)` with the swapped opening, ending in a state that represents the
finished alternative. -/
theorem swapped_history :
    NamedFrom (D := D) N emptyP q1 [.ret] swappedEnd 1 ∧ Represents N emptyP 0 (done []) swappedEnd 1 := by
  obtain ⟨fired, rep⟩ := swappedRet_fires N q1_start live_nil (k := 1)
    (by rw [q1_present, Finset.mem_singleton]; exact one_ne_zero)
  exact ⟨Chain.single fired, rep⟩

/-- **No canonical history of the word `[ret]` ends in the swapped history's last state.** -/
theorem swappedEnd_not_canonical {s' : HostState MSig} {a' : ℕ}
    (chain : Chain (FiresNamedCanonical N emptyP) (Hosting.start N emptyP q1) 0 [.ret] s' a') :
    s' ≠ swappedEnd := by
  have chain' : Chain (FiresNamedCanonical N emptyP) (Hosting.start N emptyP q1) 0 ([] ++ [.ret]) s' a' :=
    chain
  obtain ⟨s₀, a₀, first, fired⟩ := chain'.snoc_inv
  obtain ⟨rfl, rfl⟩ := first.nil_inv
  obtain ⟨r, member, named, _, rfl⟩ := fired
  simp only [ruleNamed, Option.some.injEq] at named
  subst named
  exact canonical_ne_swapped N emptyP (Hosting.start N emptyP q1) rfl member 0 1 a'

/-- **"Possibly a new last state" is real.** The query `(ret one)` has a named history whose last state
no canonical history of its word reaches; its canonical representatives
(`canonical_representative`) exist and end elsewhere, representing the same alternative; one of them
makes the same row `1`. -/
theorem possibly_new_endpoint :
    NamedFrom (D := D) N emptyP q1 [.ret] swappedEnd 1 ∧
      (∀ s' a', Chain (FiresNamedCanonical N emptyP) (Hosting.start N emptyP q1) 0 [.ret] s' a' →
        s' ≠ swappedEnd) ∧
      (∃ s', Chain (FiresNamedCanonical N emptyP) (Hosting.start N emptyP q1) 0 [.ret] s' 1 ∧
        Represents N emptyP 0 (done []) s' 1) ∧
      ∃ s' a', Chain (FiresNamedCanonical N emptyP) (Hosting.start N emptyP q1) 0 [.ret] s' a' ∧
        ∃ (w : World mkeys [] ()) (b : Branch mkeys [] () MTy),
          Represents N emptyP w.scope b swappedEnd 1 ∧ Represents N emptyP w.scope b s' a' ∧
            PlainBranch b := by
  obtain ⟨history, _⟩ := swapped_history
  have move : NamedMove (D := D) emptyP W0 (initialBranch q1) .ret W0 (done []) := .ret [] one [] []
  have plain : PlainBranch (initialBranch (Ty := MTy) q1) := ⟨rfl, .inl ⟨_, rfl, trivial⟩⟩
  obtain ⟨s₁, fired, rep₁, _⟩ := simulation_named_canonical N emptyP_plain move q1_start plain live_nil
    (k := 1) (by rw [q1_present, Finset.mem_singleton]; exact one_ne_zero)
  exact ⟨history, fun s' a' chain => swappedEnd_not_canonical chain, ⟨s₁, Chain.single fired, rep₁⟩,
    canonical_representative N (D := D) emptyP_plain q1 trivial (one_unopened q1 (by simp [q1, Comp.data]))
      history⟩

/-- **Both sides of `completeClass_iff_canonical` on `(ret one)`**: the word `[ret]` is complete, and a
canonical history of it ends in a state with no firing; the empty word is not complete. -/
theorem q1_complete_classes :
    CompleteClass (D := D) N emptyP q1 [.ret] ∧
      (∃ s a, Chain (FiresNamedCanonical N emptyP) (Hosting.start N emptyP q1) 0 [.ret] s a ∧
        Terminal N emptyP s) ∧
      ¬ CompleteClass (D := D) N emptyP q1 [] := by
  obtain ⟨history, rep⟩ := swapped_history
  have complete : CompleteClass (D := D) N emptyP q1 [.ret] :=
    ⟨swappedEnd, 1, history, done_terminal emptyP_plain rep⟩
  refine ⟨complete, (completeClass_iff_canonical N (D := D) emptyP_plain q1 trivial
    (one_unopened q1 (by simp [q1, Comp.data])) [.ret]).mp complete, ?_⟩
  rintro ⟨s, a, empty, terminal⟩
  obtain ⟨rfl, rfl⟩ := empty.nil_inv
  obtain ⟨s', fired, _⟩ := q1_fires 1 one_ne_zero
  exact terminal s' (firesNamed_fires N fired)

end RetOne

/-! ### Existence: the hypotheses of `bag_of_canonical_classes` hold of the run of `ExampleChoice` -/

/-- **Existence**: the run of `ExampleChoice` satisfies every hypothesis of `bag_of_canonical_classes`;
its bag of answers is read off the canonical histories of its finished complete classes. -/
theorem example_canonical_bag :
    ∃ M : Multiset (List RuleName),
      ExampleChoice.final.answers (D := ExampleChoice.D) =
        (@Multiset.filter _ (fun word => ∃ s a,
            Chain (FiresNamedCanonical ExampleChoice.N ExampleBeta.program)
              (Hosting.start ExampleChoice.N ExampleBeta.program ExampleChoice.query)
              ExampleBeta.program.equations.length word s a ∧ StateFinished ExampleChoice.N s a)
          (fun _ => Classical.propDecidable _) M).map
          (fun word => {g | ∃ s a,
            Chain (FiresNamedCanonical ExampleChoice.N ExampleBeta.program)
              (Hosting.start ExampleChoice.N ExampleBeta.program ExampleChoice.query)
              ExampleBeta.program.equations.length word s a ∧ g ∈ stateAnswer ExampleChoice.N s a}) := by
  obtain ⟨M, _, answers⟩ := bag_of_canonical_classes ExampleChoice.N (supply := ExampleChoice.supply)
    (fun _ => 0) ExampleChoice.query ExampleChoice.program_plain ExampleChoice.query_plain
    ExampleChoice.query_unopened ExampleChoice.runs ExampleChoice.final_quiescent
  exact ⟨M, answers⟩

/-! ### Outside the fragment: `(let one (ret one) (ret one))` -/

section Outside

open SourceLanguage.Elaboration SourceLanguage.Toolkit
open Hosting.Alternatives.Controls

/-- A query outside the first fragment. -/
def qLet : Comp mkeys [] () MTy := .let_ [1] one (.ret one) (.ret one)

theorem qLet_not_plain : ¬ PlainComp qLet := fun plain => plain

theorem qLet_start : Represents N emptyP 0 (initialBranch qLet) (Hosting.start N emptyP qLet) 0 :=
  start_represents N emptyP qLet (one_unopened qLet (by simp [qLet, Comp.data]))

/-- **The start of the `let` query represents no alternative of the fragment.** -/
theorem qLet_no_plain {n a : ℕ} {b : Branch mkeys [] () MTy}
    (rep : Represents N emptyP n b (Hosting.start N emptyP qLet) a) : ¬ PlainBranch b :=
  no_plain_beside_let N qLet_start rfl live_nil rep

/-- **Outside the fragment the conclusion of `canonical_representative` fails already for the empty
history**: its last state, the start, represents no alternative of the fragment at any world, while
its canonical history, the empty one, exists. -/
theorem let_start_represents_no_plain :
    NamedFrom (D := D) N emptyP qLet [] (Hosting.start N emptyP qLet) 0 ∧
      Chain (FiresNamedCanonical N emptyP) (Hosting.start N emptyP qLet) 0 [] (Hosting.start N emptyP qLet) 0 ∧
      ¬ ∃ (w : World mkeys [] ()) (b : Branch mkeys [] () MTy),
        Represents N emptyP w.scope b (Hosting.start N emptyP qLet) 0 ∧ PlainBranch b :=
  ⟨.nil _ _, .nil _ _, fun ⟨_, _, rep, plain⟩ => qLet_no_plain rep plain⟩

/-- **No named firing from the start of the `let` query**: the take pattern of no named rule reads as
its alternative. -/
theorem let_start_no_named_firing {name : RuleName} {s' : HostState MSig} {a' : ℕ} :
    ¬ FiresNamed N emptyP name (Hosting.start N emptyP qLet) 0 s' a' := by
  rintro ⟨r, named, ⟨rl, member, ext, opening, selection, seen⟩, rule, admitted, _, _, _⟩
  simp only at rule
  subst rule
  cases name with
  | ret =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N qLet_start admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, same⟩ := shape_ret N reads
      cases same
  | unmatched =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N qLet_start admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      change branchReads N _ B (observe (instantiate h _)) at reads
      rw [instantiate_altN, instantiate_evalN, instantiate_applyN] at reads
      obtain ⟨_, _, same, _, _⟩ := shape_apply N reads
      cases same
  | left =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N qLet_start admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, same⟩ := shape_choice N reads
      cases same
  | right =>
      simp only [ruleNamed, Option.some.injEq] at named
      subst named
      obtain ⟨_, _, _, B, h, reads, _⟩ := admitted_takes_alternative N qLet_start admitted rfl rfl rfl
        (fun h => ⟨_, _, congrArg observe (instantiate_altN N h _ _)⟩)
      obtain ⟨_, _, same⟩ := shape_choice N reads
      cases same
  | eqn i => simp [ruleNamed, emptyP] at named

/-- **Outside the fragment named firings and named moves do not decide whether a state has a
firing**: the start of the `let` query has a firing (by the `let` rule, which no name denotes), it
has no named firing, and its alternative has no named move. So `firesNamed_of_fires` and
`represented_terminal_iff` fail there. -/
theorem let_fires_without_named_move :
    ¬ Terminal N emptyP (Hosting.start N emptyP qLet) ∧
      (∀ (name : RuleName) (s' : HostState MSig) (a' : ℕ),
        ¬ FiresNamed N emptyP name (Hosting.start N emptyP qLet) 0 s' a') ∧
      ∀ (n : RuleName) (w' : World mkeys [] ()) (b' : Branch mkeys [] () MTy),
        ¬ NamedMove (D := D) emptyP W0 (initialBranch qLet) n w' b' := by
  refine ⟨fun terminal => ?_, fun _ _ _ => let_start_no_named_firing, fun _ _ _ move => ?_⟩
  · obtain ⟨s', _, fires, _⟩ := simulation_letStart N qLet_start live_nil
    exact terminal s' fires
  · cases move

/-- The equation `(= (f) (let one (ret one) (ret one)))`, whose right side is outside the fragment. -/
def eLet : SourceLanguage.Equation mkeys [] () MTy := ⟨[3], f, qLet⟩

/-- A program whose one equation is outside the fragment. -/
def letP : SourceLanguage.Program mkeys [] () MTy := ⟨[eLet], fun t => .apply t⟩

theorem letP_not_plain : ¬ PlainProgram letP := fun plain => plain eLet (List.mem_singleton_self _)

theorem q3_letP_start : Represents N letP 0 (initialBranch q3) (Hosting.start N letP q3) 1 :=
  start_represents N letP q3 (by
    intro t member x inside
    simp only [q3, Comp.data, List.mem_singleton] at member
    subst member
    simp [f, sym, support, supportArgs] at inside)

/-- **Outside the fragment by the program**: the query `(f)` of the program `letP` (a plain query
with unopened names) has a named history `[eqn 0]`, canonical itself, whose last state represents no
alternative of the fragment at any world. So the hypothesis `PlainProgram` cannot be dropped from
`canonical_representative` either. -/
theorem eqn_let_represents_no_plain :
    ∃ s a, NamedFrom (D := D) N letP q3 [.eqn 0] s a ∧
      Chain (FiresNamedCanonical N letP) (Hosting.start N letP q3) 1 [.eqn 0] s a ∧
      ¬ ∃ (w : World mkeys [] ()) (b : Branch mkeys [] () MTy),
        Represents N letP w.scope b s a ∧ PlainBranch b := by
  have member : eLet ∈ letP.equations := List.mem_singleton_self _
  have present : (Hosting.start N letP q3).present = insert 1 (Finset.range 1) := rfl
  obtain ⟨admitted, rep⟩ := fire_simple_canonical N (schema_mem N letP member) ⟨rfl, rfl, rfl⟩ rfl
    q3_letP_start (fun B q => transfer_schema N eLet rfl q3_letP_start.fresh q) matchedStore_live
    (k := 2) (by rw [present]; simp) (entails_of_no_checks rfl rfl)
    (branchBelow_call q3_letP_start.fresh eLet) q3_letP_start.noPending
  have fired : FiresNamedCanonical N letP (.eqn 0) (Hosting.start N letP q3) 1
      ((RuleSyntax.Contextual.canonical (F := (Hosting.start N letP q3).frame) (schema N eLet)
        (schema_mem N letP member) ⟨[1], [], [2]⟩ []).result (Interface.Frames.contextual MSig)
        (Hosting.start N letP q3)) 2 :=
    ⟨_, schema_mem N letP member, rfl, admitted, rfl⟩
  refine ⟨_, 2, Chain.single (FiresNamedCanonical.firesNamed N fired), Chain.single fired, ?_⟩
  rintro ⟨_, _, rep', plain⟩
  exact no_plain_beside_let N rep rfl matchedStore_live rep' plain

end Outside

end CanonicalHistoryControls

#print axioms fire_simple_fresh
#print axioms canonical_chain_of_named
#print axioms canonical_representative
#print axioms named_chains_one_alternative
#print axioms namedFrom_one_alternative
#print axioms canonical_chain_named
#print axioms firesNamed_of_fires
#print axioms represented_terminal_iff
#print axioms represented_status
#print axioms canonical_representative_status
#print axioms canonical_every_representative
#print axioms named_word_iff_canonical
#print axioms completeClass_iff_canonical
#print axioms finishedClass_iff_canonical
#print axioms classAnswer_eq_canonical
#print axioms bag_of_canonical_classes
#print axioms CanonicalHistoryControls.swapDatum_swapDatum
#print axioms CanonicalHistoryControls.copair_swapped
#print axioms CanonicalHistoryControls.swappedRet_simple
#print axioms CanonicalHistoryControls.swappedRet_fresh
#print axioms CanonicalHistoryControls.swappedRet_fires
#print axioms CanonicalHistoryControls.canonical_datum_ne_swapped
#print axioms CanonicalHistoryControls.retPattern_datum
#print axioms CanonicalHistoryControls.canonical_ne_swapped
#print axioms CanonicalHistoryControls.swapped_history
#print axioms CanonicalHistoryControls.swappedEnd_not_canonical
#print axioms CanonicalHistoryControls.possibly_new_endpoint
#print axioms CanonicalHistoryControls.q1_complete_classes
#print axioms CanonicalHistoryControls.example_canonical_bag
#print axioms CanonicalHistoryControls.no_plain_beside_let
#print axioms CanonicalHistoryControls.qLet_not_plain
#print axioms CanonicalHistoryControls.qLet_start
#print axioms CanonicalHistoryControls.qLet_no_plain
#print axioms CanonicalHistoryControls.let_start_represents_no_plain
#print axioms CanonicalHistoryControls.let_start_no_named_firing
#print axioms CanonicalHistoryControls.let_fires_without_named_move
#print axioms CanonicalHistoryControls.letP_not_plain
#print axioms CanonicalHistoryControls.q3_letP_start
#print axioms CanonicalHistoryControls.eqn_let_represents_no_plain

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives
