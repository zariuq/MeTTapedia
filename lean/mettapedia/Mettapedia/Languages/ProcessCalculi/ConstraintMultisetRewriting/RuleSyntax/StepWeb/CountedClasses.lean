import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.CountedTransitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.StepAlone

/-!
# The bag of answers over classes of held histories

The source's bag of answers is read off classes of named histories of the translated program
(`Hosting.Alternatives.bag_of_classes`): a class is a word of names, and the histories that follow
it differ only in fresh names, extensions, openings and row identities. This module reads the same
bag off the **held presentation** (`CountedTransitions`): a class of held histories is a word of
**origins**, the ambient control rule or the held equation occurrence each firing used.

The constructions are those of `CountedTransitions`: a bag store of rows, one match per step,
guards asked after the firing's own tells, one knowledge store; the control rules fixed beside the
store and the equations held in it as persistent occurrences indexed by their positions.

## What is shown

* `run_of_heldFrom`, `heldFrom_of_run`, `completeHeldRun_iff`: held histories are the actual runs of
  the held-rule step (`Interface.Step.Run`) from the held start, read with their origins in order
  (`originsOf`); a complete held class is the origins of a complete run.
* `held_firings_compete`: at every state a held history reaches, every admitted held firing takes
  the alternative's row and the state it reaches no longer has that row. Two held firings there,
  whatever their origins, compete for that row. With `heldFrom_of_run`: the firings of a run are
  causally ordered, each taking the row the one before it made, and at each state every admitted
  firing takes that one row. `adjacent_not_exchangeable`: the row the next firing of a held history
  takes is taken by no admitted firing at the state before, so adjacent firings cannot be exchanged.
* `heldFrom_of_namedFrom`, `named_of_heldFrom`, `heldFrom_map_iff`: a named history is a held
  history whose word is its names' origins, and every held history from the start of a query of
  the first fragment is one of these, its last state representing an alternative.
* `heldTerminal_iff`: a held state has no firing exactly when the state under it has none.
* `completeHeld_map_iff`, `completeHeldRun_map_iff`, `finishedHeld_map_iff`: the origins of a word
  of names form a complete held class, the word of a complete run of the held-rule step, resp. a
  finished held class, exactly when the names form a complete, resp. finished, class.
* `classAnswer_held`: the answer observer `Hosting.Alternatives.classAnswer` (a class of names, read
  at the endpoints of its named histories) is what the endpoints of the held histories of its
  origins show. No other answer observer is defined.
* **Complete runs** (`bag_of_held_classes`): for every source run that ends, a multiset of words of
  names counts each word once exactly when its origins are the word of a complete run of the
  held-rule step, every complete run's origins are those of a member, and the bag of answers is the
  multiset of answer sets `classAnswer` of the members whose held class is finished.
* **Delivered prefixes** (`delivered_of_tracing`, `delivered_held_bag`): for every configuration and
  every traced frontier of it (`Hosting.Alternatives.Tracing`: one entry per live alternative), the
  bag of answers delivered there is the multiset of answer sets `classAnswer` of the finished
  entries, and the origins of each entry's word are the word of an actual run of the held-rule step
  to a state representing its alternative; at every configuration a source run reaches, ended or not,
  the run carries such a frontier forward step by step (`Hosting.Alternatives.tracing_runs`).

Neither theorem asks the equations to have distinct schemas: an equation written twice is held by
two occurrences, and the two are two origins, never identified (`origin_injective`). Histories that
differ in fresh names, extensions, openings and row identities are identified by the law
`Hosting.Alternatives.answer_of_rule_word`. `held_bag_determined`: the delivered bag of complete runs
is the same for every source run that ends, so it is invariant under every relation between complete
runs of one query.

## What is not shown here

The relation to the classes by words of rules, and to the counted run fibres of the held-rule
step, is in `CountedFibres`. How one source step changes a traced frontier is not stated here:
`Hosting.Alternatives.tracing_step` gives the existence of a frontier after the step, not its entries.
Potentially infinite histories are not treated: a source run that ends is finite, and its complete
classes are finite words.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Counted

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Hosting Hosting.Alternatives
open RuleOccurrences
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S}

/-! ## Classes of held histories -/

section ClassesDef

variable {Ty : Type} (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty)

/-- **A held history** from the start of the query, following a word of origins: each firing a held
firing by its origin, taking the row the firing before it made. -/
abbrev HeldFrom (word : List (Use (CRule S) ℕ)) (s : HostState S) (a : ℕ) : Prop :=
  Chain (HeldFires N P) (start N P q) P.equations.length word s a

/-- **A held state with no firing.** -/
def HeldTerminal (s : HostState S) : Prop :=
  ∀ f : HeldFiring N P s, ¬ f.Admits (Interface.Frames.contextual S) (controlRules N)

/-- **A complete held class**: a word of origins that some held history follows to a held state
with no firing. -/
def CompleteHeldClass (word : List (Use (CRule S) ℕ)) : Prop :=
  ∃ s a, HeldFrom N P q word s a ∧ HeldTerminal N P s

/-- **A finished held class**: a word of origins that some held history follows to a finished
state. -/
def FinishedHeldClass (word : List (Use (CRule S) ℕ)) : Prop :=
  ∃ s a, HeldFrom N P q word s a ∧ StateFinished N s a

end ClassesDef

/-! ## Held states with no firing -/

section Terminal

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **A held state has no firing exactly when the state under it has none.** -/
theorem heldTerminal_iff (s : HostState S) : HeldTerminal N P s ↔ Terminal N P s := by
  constructor
  · intro still s' fires
    obtain ⟨g, admitted, -⟩ := fires
    obtain ⟨u, available, code⟩ :=
      available_of_mem (P := controlRules N) (offers N P) s (fun _ => ()) g.member
    obtain ⟨f, -, -, -, fAdmitted, -⟩ :=
      lift_admits (Interface.Frames.contextual S) g admitted available code
    exact still f fAdmitted
  · intro terminal f admitted
    obtain ⟨baseAdmitted, -⟩ := heldFiring_project admitted
    exact terminal _ ⟨_, baseAdmitted, rfl⟩

end Terminal

/-! ## Held histories are the runs of the held-rule step -/

section Runs

variable {Ty : Type} {P : SourceLanguage.Program κ Γ star Ty}

/-- **The origins of a run** of the held-rule step, in order. -/
def originsOf {t : RState (RuleSyntax.Contextual.Terms S) ℕ ℕ (CRule S) Unit}
    (run : (heldStep N).toStep.Run t) : List (Use (CRule S) ℕ) :=
  run.word.map fun x => x.2.use

/-- Transporting a run along an equality of states keeps its end and its origins. -/
theorem run_cast {t t' : RState (RuleSyntax.Contextual.Terms S) ℕ ℕ (CRule S) Unit} (h : t = t')
    (run : (heldStep N).toStep.Run t) :
    (cast (congrArg (heldStep N).toStep.Run h) run).last = run.last ∧
      originsOf N (cast (congrArg (heldStep N).toStep.Run h) run) = originsOf N run := by
  subst h
  exact ⟨rfl, rfl⟩

/-- **A run from a held state of the right shape is a held history**: each firing takes the row the
firing before it made. -/
theorem chain_of_run {t : RState (RuleSyntax.Contextual.Terms S) ℕ ℕ (CRule S) Unit}
    (run : (heldStep N).toStep.Run t) : ∀ (s : HostState S) (a : ℕ), t = heldState N P s →
      StepAlone.Shaped N P s a →
        ∃ s' a', run.last = heldState N P s' ∧ Chain (HeldFires N P) s a (originsOf N run) s' a' := by
  induction run with
  | nil t =>
      intro s a h _
      exact ⟨s, a, h, .nil _ _⟩
  | cons f admitted rest ih =>
      intro s a h shaped
      subst h
      obtain ⟨baseAdmitted, endpoint⟩ := heldFiring_project admitted
      obtain ⟨a', taken, made, shaped'⟩ := StepAlone.shaped_fires N shaped baseAdmitted
      obtain ⟨s'', a'', last, chain⟩ := ih _ a' endpoint shaped'
      exact ⟨s'', a'', last, Chain.append (Chain.single ⟨f, rfl, admitted, taken, made, endpoint⟩) chain⟩

/-- **A held history is a run of the held-rule step** with its origins in order. -/
theorem run_of_chain : ∀ (w : List (Use (CRule S) ℕ)) {s s' : HostState S} {a a' : ℕ},
    Chain (HeldFires N P) s a w s' a' →
      ∃ run : (heldStep N).toStep.Run (heldState N P s), run.last = heldState N P s' ∧ originsOf N run = w
  | [], _, _, _, _, chain => by
      obtain ⟨rfl, rfl⟩ := chain.nil_inv
      exact ⟨.nil _, rfl, rfl⟩
  | u :: rest, _, _, _, _, chain => by
      obtain ⟨s₁, a₁, first, later⟩ := Chain.split [u] rest chain
      have first' : Chain (HeldFires N P) _ _ ([] ++ [u]) s₁ a₁ := first
      obtain ⟨s₀, a₀, start, fired⟩ := first'.snoc_inv
      obtain ⟨rfl, rfl⟩ := start.nil_inv
      obtain ⟨f, use, admitted, -, -, result⟩ := fired
      obtain ⟨restRun, last, word⟩ := run_of_chain rest later
      have back : heldState N P s₁ = (heldStep N).toStep.result f admitted := result.symm
      refine ⟨.cons f admitted (cast (congrArg (heldStep N).toStep.Run back) restRun), ?_, ?_⟩
      · exact (run_cast N back restRun).1.trans last
      · show f.use :: originsOf N (cast (congrArg (heldStep N).toStep.Run back) restRun) = u :: rest
        rw [(run_cast N back restRun).2, word, use]

/-- **Every held history from the start is a run of the held-rule step from the held start**, ending
at the held state over its last state, with its word as the run's origins. -/
theorem run_of_heldFrom (q : Comp κ Γ star Ty) {w : List (Use (CRule S) ℕ)} {s : HostState S} {a : ℕ}
    (held : HeldFrom N P q w s a) :
    ∃ run : (heldStep N).toStep.Run (heldState N P (start N P q)),
      run.last = heldState N P s ∧ originsOf N run = w :=
  run_of_chain N w held

/-- **Every run of the held-rule step from the held start is a held history**: it ends at the held
state over a state of the step, and its origins in order are the word of a held history to that state.
So the firings of a run are causally ordered: each takes the row the one before it made. -/
theorem heldFrom_of_run (q : Comp κ Γ star Ty) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (run : (heldStep N).toStep.Run (heldState N P (start N P q))) :
    ∃ s a, run.last = heldState N P s ∧ HeldFrom N P q (originsOf N run) s a := by
  have rep := start_represents N P q unopened
  exact chain_of_run N run _ _ rfl ⟨rep.notRow, rep.present, rep.rows⟩

/-- **Every state a held history reaches has the shape of a hosted state**: the equation rows and
one more row, the history's last made row. -/
theorem shaped_of_heldFrom (q : Comp κ Γ star Ty) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    {w : List (Use (CRule S) ℕ)} {s : HostState S} {a : ℕ} (held : HeldFrom N P q w s a) :
    StepAlone.Shaped N P s a := by
  induction held with
  | nil =>
      have rep := start_represents N P q unopened
      exact ⟨rep.notRow, rep.present, rep.rows⟩
  | snoc _ last ih =>
      obtain ⟨f, -, admitted, -, made, result⟩ := last
      obtain ⟨baseAdmitted, endpoint⟩ := heldFiring_project admitted
      obtain ⟨a', -, made', shaped'⟩ := StepAlone.shaped_fires N ih baseAdmitted
      have sameState := holding_injective (endpoint.symm.trans result)
      obtain ⟨sameRow, -⟩ := List.cons.inj (made'.symm.trans made)
      rw [← sameState, ← sameRow]
      exact shaped'

/-- **Held firings compete for the alternative's row.** At every state a held history reaches, every
admitted held firing, by any origin, takes the alternative's row `a`, and the state it reaches no
longer has that row. So two admitted held firings there are alternatives of one choice: each
consumes the row the other takes. -/
theorem held_firings_compete (q : Comp κ Γ star Ty)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {w : List (Use (CRule S) ℕ)}
    {s : HostState S} {a : ℕ} (held : HeldFrom N P q w s a) {f : HeldFiring N P s}
    (admitted : f.Admits (Interface.Frames.contextual S) (controlRules N)) :
    f.selection.taken = [a] ∧
      ∀ s' : HostState S, f.result (Interface.Frames.contextual S) = heldState N P s' → a ∉ s'.present := by
  have shaped := shaped_of_heldFrom N q unopened held
  obtain ⟨baseAdmitted, endpoint⟩ := heldFiring_project admitted
  obtain ⟨a', taken, made, shaped'⟩ := StepAlone.shaped_fires N shaped baseAdmitted
  have made₀ : f.selection.made = [a'] := made
  have fresh : a' ∉ s.present := fun inside =>
    Finset.disjoint_left.mp admitted.2.1.fresh
      (List.mem_toFinset.mpr (by rw [made₀]; exact List.mem_singleton_self _)) inside
  have present : a ∈ s.present := by
    rw [shaped.present]
    exact Finset.mem_insert_self _ _
  refine ⟨taken, fun s' reached => ?_⟩
  have sameState := holding_injective (endpoint.symm.trans reached)
  rw [← sameState, shaped'.present, Finset.mem_insert, Finset.mem_range]
  rintro (same | small)
  · exact fresh (same ▸ present)
  · exact absurd small (not_lt.mpr shaped.notRow)

/-- **Adjacent firings of a held history cannot be exchanged.** After a held history to `s₀`, a held
firing to `s₁` makes the row `a₁` that the next held firing takes; no admitted held firing at `s₀`
takes `a₁`. So the next firing cannot fire first. -/
theorem adjacent_not_exchangeable (q : Comp κ Γ star Ty)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {w : List (Use (CRule S) ℕ)}
    {s₀ s₁ : HostState S} {a₀ a₁ : ℕ} {u : Use (CRule S) ℕ} (held : HeldFrom N P q w s₀ a₀)
    (first : HeldFires N P u s₀ a₀ s₁ a₁) (f : HeldFiring N P s₀)
    (admitted : f.Admits (Interface.Frames.contextual S) (controlRules N)) :
    f.selection.taken ≠ [a₁] := by
  have shaped := shaped_of_heldFrom N q unopened held
  obtain ⟨taken, -⟩ := held_firings_compete N q unopened held admitted
  obtain ⟨f₁, -, admitted₁, -, made₁, -⟩ := first
  have fresh : a₁ ∉ s₀.present := fun inside =>
    Finset.disjoint_left.mp admitted₁.2.1.fresh
      (List.mem_toFinset.mpr (by rw [made₁]; exact List.mem_singleton_self _)) inside
  have present : a₀ ∈ s₀.present := by
    rw [shaped.present]
    exact Finset.mem_insert_self _ _
  rw [taken]
  intro same
  have rows : a₀ = a₁ := (List.cons.inj same).1
  exact fresh (rows ▸ present)

/-- **A complete run of the held-rule step** from the start, with its origins in order. -/
def CompleteHeldRun (P : SourceLanguage.Program κ Γ star Ty) (q : Comp κ Γ star Ty)
    (w : List (Use (CRule S) ℕ)) : Prop :=
  ∃ run : (heldStep N).toStep.Run (heldState N P (start N P q)), originsOf N run = w ∧
    ∀ f : RFiring ℕ ℕ (RuleSyntax.Contextual.declarations S) (ofRules (Tm := RuleSyntax.Contextual.Terms S) Unit)
      run.last, ¬ f.Admits (Interface.Frames.contextual S) (controlRules N)

/-- **Complete held classes are the origins of complete runs of the held-rule step.** -/
theorem completeHeldRun_iff (q : Comp κ Γ star Ty) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = [])
    (w : List (Use (CRule S) ℕ)) : CompleteHeldRun N P q w ↔ CompleteHeldClass N P q w := by
  constructor
  · rintro ⟨run, origins, still⟩
    obtain ⟨s, a, last, held⟩ := heldFrom_of_run N q unopened run
    refine ⟨s, a, origins ▸ held, ?_⟩
    rw [last] at still
    exact still
  · rintro ⟨s, a, held, still⟩
    obtain ⟨run, last, origins⟩ := run_of_heldFrom N q held
    refine ⟨run, origins, ?_⟩
    rw [last]
    exact still

end Runs

variable {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

/-! ## Named histories and held histories -/

section Histories

variable (q : Comp κ Γ star D.Ty)

/-- **A named history is a held history** whose word is the origins of its names. -/
theorem heldFrom_of_namedFrom {word : List RuleName} {s : HostState S} {a : ℕ}
    (named : NamedFrom N P q word s a) : HeldFrom N P q (word.map (origin N)) s a :=
  Chain.map (origin N) (fun _ _ _ _ _ fired => heldFires_of_firesNamed fired) named

/-- **Every held history from the start of a query of the first fragment is a named history**: its
word is the origins of the names, and its last state represents an alternative of the fragment. -/
theorem named_of_heldFrom (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {word : List (Use (CRule S) ℕ)}
    {s : HostState S} {a : ℕ} (held : HeldFrom N P q word s a) :
    ∃ ν : List RuleName, ν.map (origin N) = word ∧ NamedFrom N P q ν s a ∧
      ∃ (w : World κ Γ star) (b : Branch κ Γ star D.Ty), Represents N P w.scope b s a ∧ PlainBranch b := by
  induction held with
  | nil =>
      exact ⟨[], rfl, .nil _ _, ⟨0, 0, fun _ => 0⟩, initialBranch q, start_represents N P q unopened,
        rfl, .inl ⟨q, rfl, plainQ⟩⟩
  | snoc _ last ih =>
      obtain ⟨ν, mapped, named, w, b, rep, plain⟩ := ih
      obtain ⟨f, use, admitted, taken, made, result⟩ := last
      obtain ⟨n, hn⟩ := use_named N rep plain admitted
      have fired : FiresNamed N P n _ _ _ _ :=
        firesNamed_of_heldFires ⟨f, hn, admitted, taken, made, result⟩
      obtain ⟨w', b', -, rep', plain'⟩ := reflection_named N plainP rep plain fired
      refine ⟨ν ++ [n], ?_, .snoc named fired, w', b', rep', plain'⟩
      rw [List.map_append, mapped, List.map_singleton, ← hn, use]

/-- **Held histories of a word of origins of names are the named histories of the names.** -/
theorem heldFrom_map_iff (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {ν : List RuleName}
    {s : HostState S} {a : ℕ} :
    HeldFrom N P q (ν.map (origin N)) s a ↔ NamedFrom N P q ν s a := by
  constructor
  · intro held
    obtain ⟨ν', mapped, named, -⟩ := named_of_heldFrom N q plainP plainQ unopened held
    rwa [List.map_injective_iff.mpr (origin_injective N) mapped] at named
  · exact heldFrom_of_namedFrom N q

/-! ## The classes correspond -/

theorem completeHeld_map_iff (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (ν : List RuleName) :
    CompleteHeldClass N P q (ν.map (origin N)) ↔ CompleteClass N P q ν := by
  constructor
  · rintro ⟨s, a, held, still⟩
    exact ⟨s, a, (heldFrom_map_iff N q plainP plainQ unopened).mp held, (heldTerminal_iff N s).mp still⟩
  · rintro ⟨s, a, named, terminal⟩
    exact ⟨s, a, heldFrom_of_namedFrom N q named, (heldTerminal_iff N s).mpr terminal⟩

theorem finishedHeld_map_iff (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (ν : List RuleName) :
    FinishedHeldClass N P q (ν.map (origin N)) ↔ FinishedClass N P q ν := by
  constructor
  · rintro ⟨s, a, held, finished⟩
    exact ⟨s, a, (heldFrom_map_iff N q plainP plainQ unopened).mp held, finished⟩
  · rintro ⟨s, a, named, finished⟩
    exact ⟨s, a, heldFrom_of_namedFrom N q named, finished⟩

/-- **The agreed observer, read off held histories**: the answer of a class of names
(`Hosting.Alternatives.classAnswer`, defined by the endpoints of its named histories) is what the
last states of the held histories of its origins show. -/
theorem classAnswer_held (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (ν : List RuleName) :
    classAnswer N P q ν = {g | ∃ s a, HeldFrom N P q (ν.map (origin N)) s a ∧ g ∈ stateAnswer N s a} := by
  ext g
  constructor
  · rintro ⟨s, a, named, shown⟩
    exact ⟨s, a, heldFrom_of_namedFrom N q named, shown⟩
  · rintro ⟨s, a, held, shown⟩
    exact ⟨s, a, (heldFrom_map_iff N q plainP plainQ unopened).mp held, shown⟩

/-- **Complete classes of names are complete runs of the held-rule step**, read by their origins. -/
theorem completeHeldRun_map_iff (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) (ν : List RuleName) :
    CompleteHeldRun N P q (ν.map (origin N)) ↔ CompleteClass N P q ν :=
  (completeHeldRun_iff N q unopened _).trans (completeHeld_map_iff N q plainP plainQ unopened ν)

/-- **Every complete held class is the origins of a word of names.** -/
theorem completeHeld_named (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {word : List (Use (CRule S) ℕ)}
    (complete : CompleteHeldClass N P q word) : ∃ ν : List RuleName, ν.map (origin N) = word := by
  obtain ⟨s, a, held, -⟩ := complete
  obtain ⟨ν, mapped, -⟩ := named_of_heldFrom N q plainP plainQ unopened held
  exact ⟨ν, mapped⟩

end Histories

/-! ## The bag of answers -/

/-- **Complete runs: the delivered bag is the agreed observer over the complete runs of the held-rule
step.** For a program and a query of the first fragment, and every source run that ends, there is a
multiset `M` of words of names in which a word is counted once when the word of its origins is the
word of a complete run of the held-rule step from the held start, and not at all otherwise; every
complete run's word of origins is that of a member of `M`; and the bag of answers is the multiset of
answer sets `classAnswer` of the members whose held class is finished. The equations need not have
distinct schemas. The class of a run is its word of origins, which identifies runs that differ in
fresh names, extensions, openings and row identities by the law
`Hosting.Alternatives.answer_of_rule_word` (all histories of one word show one answer), read on held
histories by `classAnswer_held`; the positions of equations are never identified (`origin_injective`). -/
theorem bag_of_held_classes (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ M : Multiset (List RuleName),
      (∀ ν, M.count ν = if CompleteHeldRun N P q (ν.map (origin N)) then 1 else 0) ∧
        (∀ w, CompleteHeldRun N P q w → ∃ ν ∈ M, ν.map (origin N) = w) ∧
        C.answers (D := D) =
          (M.filter fun ν => FinishedHeldClass N P q (ν.map (origin N))).map (classAnswer N P q) := by
  obtain ⟨M, count, answers⟩ := bag_of_classes N spaces q plainP plainQ unopened runs quiet
  refine ⟨M, fun ν => ?_, fun w complete => ?_, ?_⟩
  · rw [count ν]
    by_cases complete : CompleteClass N P q ν
    · rw [if_pos complete, if_pos ((completeHeldRun_map_iff N q plainP plainQ unopened ν).mpr complete)]
    · rw [if_neg complete, if_neg fun c => complete ((completeHeldRun_map_iff N q plainP plainQ unopened ν).mp c)]
  · obtain ⟨ν, rfl⟩ := completeHeld_named N q plainP plainQ unopened ((completeHeldRun_iff N q unopened w).mp complete)
    refine ⟨ν, Multiset.count_pos.mp ?_, rfl⟩
    rw [count ν, if_pos ((completeHeldRun_map_iff N q plainP plainQ unopened ν).mp complete)]
    exact Nat.one_pos
  · rw [answers]
    congr 1
    exact Multiset.filter_congr fun ν _ => (finishedHeld_map_iff N q plainP plainQ unopened ν).symm

/-- **The delivered bag at a cut, read off any traced frontier of it.** For every configuration `C`
and every traced frontier of `C` (`Hosting.Alternatives.Tracing`: one entry per live alternative of
`C`, with the word of names of its class, every named history of that word ending in a state that
represents the alternative), each entry's word of origins is the word of an actual run of the held-rule
step from the held start, ending at the held state over a state that represents the entry's
alternative, and the bag of answers delivered at `C` is the multiset of answer sets `classAnswer` of the
entries whose held class is finished. Traced frontiers relate cuts to frontiers along the actual
steps: the start has one (`Hosting.Alternatives.tracing_initial`), and every source step from a cut
with one leads to a cut with one (`Hosting.Alternatives.tracing_step`, which states existence only);
one named move of one alternative is one held firing by the name's origin (`held_of_namedMove`). -/
theorem delivered_of_tracing (q : Comp κ Γ star D.Ty) (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    {L : Multiset (Branch κ Γ star D.Ty × List RuleName)} {G : Multiset (List RuleName)}
    (tracing : Tracing N P q C L G) :
    (∀ x ∈ L, ∃ run : (heldStep N).toStep.Run (heldState N P (start N P q)),
      originsOf N run = x.2.map (origin N) ∧
        ∃ s a, run.last = heldState N P s ∧ Represents N P C.world.scope x.1 s a) ∧
      C.answers (D := D) =
        ((L.map Prod.snd).filter fun ν => FinishedHeldClass N P q (ν.map (origin N))).map
          (classAnswer N P q) := by
  have liveOf : ∀ x ∈ L, Solvable x.1.store := fun x member => by
    have inBranches : x.1 ∈ C.branches.filter (fun b => Solvable b.store) := by
      rw [← tracing.branches]; exact Multiset.mem_map_of_mem _ member
    exact (Multiset.mem_filter.mp inBranches).2
  have finishedIff : ∀ x ∈ L, FinishedClass N P q x.2 ↔ x.1.Finished (D := D) := by
    intro x member
    constructor
    · rintro ⟨s, a, reached, finished⟩
      exact ((finished_iff N (tracing.uniform x member s a reached)).mpr finished).1
    · intro finished
      obtain ⟨s, a, reached⟩ := tracing.reached x member
      exact ⟨s, a, reached,
        (finished_iff N (tracing.uniform x member s a reached)).mp ⟨finished, liveOf x member⟩⟩
  have answerAt : ∀ x ∈ L, x.1.Finished (D := D) → classAnswer N P q x.2 = x.1.answer (D := D) := by
    intro x member finished
    ext g
    constructor
    · rintro ⟨s, a, reached, shown⟩
      rw [answer_eq N (tracing.uniform x member s a reached) finished] at shown
      exact shown
    · intro answered
      obtain ⟨s, a, reached⟩ := tracing.reached x member
      refine ⟨s, a, reached, ?_⟩
      rw [answer_eq N (tracing.uniform x member s a reached) finished]
      exact answered
  refine ⟨fun x member => ?_, ?_⟩
  · obtain ⟨s, a, reached⟩ := tracing.reached x member
    obtain ⟨run, last, origins⟩ := run_of_heldFrom N q (heldFrom_of_namedFrom N q reached)
    exact ⟨run, origins, s, a, last, tracing.uniform x member s a reached⟩
  · have heldIff : ∀ x ∈ L, FinishedHeldClass N P q (x.2.map (origin N)) ↔ x.1.Finished (D := D) :=
      fun x member => (finishedHeld_map_iff N q plainP plainQ unopened x.2).trans (finishedIff x member)
    have split : C.branches.filter (fun b => b.Finished (D := D) ∧ Solvable b.store) =
        (C.branches.filter (fun b => Solvable b.store)).filter (fun b => b.Finished (D := D)) := by
      rw [Multiset.filter_filter]
    unfold Config.answers
    rw [split, ← tracing.branches, Multiset.filter_map, Multiset.map_map, Multiset.filter_map,
      Multiset.map_map]
    have sameFilter : L.filter ((fun b : Branch κ Γ star D.Ty => b.Finished (D := D)) ∘ Prod.fst) =
        L.filter ((fun ν => FinishedHeldClass N P q (ν.map (origin N))) ∘ Prod.snd) :=
      Multiset.filter_congr fun x member => (heldIff x member).symm
    rw [sameFilter]
    apply Multiset.map_congr rfl
    intro x member
    obtain ⟨inL, finishedHeld⟩ := Multiset.mem_filter.mp member
    exact (answerAt x inL ((heldIff x inL).mp finishedHeld)).symm

/-- **Delivered prefixes, along the actual cut.** At every configuration `C` a source run reaches,
whether or not the run ends, the traced frontier the run carries step by step
(`Hosting.Alternatives.tracing_runs`) gives the bag of answers delivered at `C` as in
`delivered_of_tracing`: the multiset of answer sets `classAnswer` of its finished entries, each entry
an actual run of the held-rule step to a state representing a live alternative of `C`. -/
theorem delivered_held_bag (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) :
    ∃ (L : Multiset (Branch κ Γ star D.Ty × List RuleName)) (G : Multiset (List RuleName)),
      Tracing N P q C L G ∧
        (∀ x ∈ L, ∃ run : (heldStep N).toStep.Run (heldState N P (start N P q)),
          originsOf N run = x.2.map (origin N) ∧
            ∃ s a, run.last = heldState N P s ∧ Represents N P C.world.scope x.1 s a) ∧
        C.answers (D := D) =
          ((L.map Prod.snd).filter fun ν => FinishedHeldClass N P q (ν.map (origin N))).map
            (classAnswer N P q) := by
  obtain ⟨L, G, tracing⟩ := tracing_runs N spaces q plainP plainQ unopened runs
  obtain ⟨heldRuns, answers⟩ := delivered_of_tracing N q plainP plainQ unopened tracing
  exact ⟨L, G, tracing, heldRuns, answers⟩

/-- **The delivered bag of complete runs depends on the program and the query alone.** For two source
runs that end, one multiset of words of names, counted by the complete runs of the held-rule step,
gives both bags of answers through `classAnswer`. So this observer is invariant under every relation
between complete runs that start from one query, in particular under exchanging the steps of
different alternatives; the law used is `Hosting.Alternatives.answers_determined`'s, here
`bag_of_held_classes` with the uniqueness of a multiset of given counts. -/
theorem held_bag_determined (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C₁ C₂ : Config κ Γ star D.Ty}
    (runs₁ : Runs D P supply (Config.initial spaces q) C₁) (quiet₁ : C₁.Quiescent P supply)
    (runs₂ : Runs D P supply (Config.initial spaces q) C₂) (quiet₂ : C₂.Quiescent P supply) :
    ∃ M : Multiset (List RuleName),
      (∀ ν, M.count ν = if CompleteHeldRun N P q (ν.map (origin N)) then 1 else 0) ∧
        C₁.answers (D := D) =
          (M.filter fun ν => FinishedHeldClass N P q (ν.map (origin N))).map (classAnswer N P q) ∧
        C₂.answers (D := D) =
          (M.filter fun ν => FinishedHeldClass N P q (ν.map (origin N))).map (classAnswer N P q) := by
  obtain ⟨M, count, -, answers₁⟩ := bag_of_held_classes N spaces q plainP plainQ unopened runs₁ quiet₁
  obtain ⟨M', count', -, answers₂⟩ := bag_of_held_classes N spaces q plainP plainQ unopened runs₂ quiet₂
  have same : M' = M := Multiset.ext.mpr fun ν => by rw [count', count]
  exact ⟨M, count, answers₁, same ▸ answers₂⟩

#print axioms heldTerminal_iff
#print axioms held_bag_determined
#print axioms chain_of_run
#print axioms run_of_chain
#print axioms run_of_heldFrom
#print axioms heldFrom_of_run
#print axioms shaped_of_heldFrom
#print axioms held_firings_compete
#print axioms adjacent_not_exchangeable
#print axioms completeHeldRun_iff
#print axioms heldFrom_of_namedFrom
#print axioms named_of_heldFrom
#print axioms heldFrom_map_iff
#print axioms completeHeld_map_iff
#print axioms finishedHeld_map_iff
#print axioms classAnswer_held
#print axioms completeHeldRun_map_iff
#print axioms completeHeld_named
#print axioms bag_of_held_classes
#print axioms delivered_of_tracing
#print axioms delivered_held_bag

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.Counted
