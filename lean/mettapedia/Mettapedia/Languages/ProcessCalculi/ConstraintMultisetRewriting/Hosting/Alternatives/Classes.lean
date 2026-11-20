import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives.Named

/-!
# The bag of answers is the bag over complete classes of histories of the step

For a program and a query of the first fragment (`ret`, `apply`, `choice`, `fail`), the bag of
answers of the configuration in which a complete source run ends is read off the step of the
translated program alone, given the names of its firings:

* a **class** of histories is a word of names (`NamedFrom`): the histories that follow it differ only
  in fresh names, extensions, openings and row identities;
* a class is **complete** when one of its histories ends in a state with no firing
  (`CompleteClass`), **finished** when one ends in a finished state (`FinishedClass`), and its
  **answer** is what its histories' last states show (`classAnswer`);
* `bag_of_classes`: **the complete classes, each counted once, are a multiset `M`, and the bag of
  answers is the answers of its finished classes**. Classes that end in `fail` are complete and
  show nothing; every state a named firing reaches represents a live alternative (`live_of_named`),
  so an alternative whose store is unsolvable is reached by no history.
* `answers_determined`: so for this fragment the bag of answers does not depend on the source run
  (the order in which alternatives moved, the scopes their names were opened at).

The proof follows the source run with a **traced frontier** (`Tracing`): each live alternative
with the word of its class, such that **every** state that a history of that word reaches represents
the alternative (`Tracing.uniform`), together with the words of the alternatives that failed
(`Tracing.graveyard`). The words are distinct and none is a prefix of another, and every complete
history passes through the frontier or ends at a failed alternative (`Tracing.cover`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage
open Classical

variable {S : Signature} {Γ : Ctx S} {star : S.Srt} (N : Nodes S Γ star)
variable {κ : Keys S} {D : Discipline S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {supply : ℕ → Term S Γ star}

/-! ## Classes of histories -/

section ClassesDef

variable (P) (q : Comp κ Γ star D.Ty)

/-- A named history from the start of the query, following `word`. -/
abbrev NamedFrom (word : List RuleName) (s : HostState S) (a : ℕ) : Prop :=
  Chain (FiresNamed N P) (start N P q) P.equations.length word s a

/-- **A complete class**: a word that some history from the start follows to a state with no
firing. -/
def CompleteClass (word : List RuleName) : Prop :=
  ∃ s a, NamedFrom N P q word s a ∧ Terminal N P s

/-- **A finished class**: a word that some history follows to a finished state. -/
def FinishedClass (word : List RuleName) : Prop :=
  ∃ s a, NamedFrom N P q word s a ∧ StateFinished N s a

/-- **The answer of a class**: what the last states of its histories show. -/
def classAnswer (word : List RuleName) : Set (Term S Γ star) :=
  {g | ∃ s a, NamedFrom N P q word s a ∧ g ∈ stateAnswer N s a}

end ClassesDef

/-! ## Facts about single alternatives -/

include supply in
/-- **A failed alternative's state has no firing.** -/
theorem fail_still (plainP : PlainProgram P) {w : World κ Γ star} {b : Branch κ Γ star D.Ty}
    {s : HostState S} {a : ℕ} (rep : Represents N P w.scope b s a) (plain : PlainBranch b)
    (failing : b.focus = .eval .fail) : Terminal N P s := by
  intro s' fires
  obtain ⟨w', bs, b', a', move, child, _⟩ := reflection N (supply := supply) plainP rep plain fires
  obtain ⟨K, focus, fs, ps⟩ := b
  simp only at failing
  subst failing
  cases move
  simp at child

/-- **The state a named firing reaches represents a live alternative.** -/
theorem live_of_named {n : RuleName} {s₀ s₁ : HostState S} {a₀ a₁ n' : ℕ} {b' : Branch κ Γ star D.Ty}
    (fired : FiresNamed N P n s₀ a₀ s₁ a₁) (rep : Represents N P n' b' s₁ a₁) : Solvable b'.store := by
  obtain ⟨_, _, f, _, admitted, _, _, rfl⟩ := fired
  obtain ⟨B, u, solved⟩ := admitted.2.2.1
  obtain ⟨σ, solvedσ, _⟩ := (rep.reads B _).mp ⟨u, solved, rfl⟩
  exact ⟨B.Names, B.arity, σ, solvedσ⟩

/-- A failed alternative has not finished. -/
theorem not_finished_of_fail {b : Branch κ Γ star D.Ty} (failing : b.focus = .eval .fail) :
    ¬ b.Finished (D := D) := by
  rintro ⟨_, t, value⟩
  rw [failing] at value
  cases value

/-! ## The traced frontier -/

section Tracing

variable (P) (q : Comp κ Γ star D.Ty)

/-- **A traced frontier** of a configuration: each live alternative with the word of its class, and
the words of the alternatives that failed. -/
structure Tracing (C : Config κ Γ star D.Ty) (L : Multiset (Branch κ Γ star D.Ty × List RuleName))
    (G : Multiset (List RuleName)) : Prop where
  branches : L.map Prod.fst = C.branches.filter (fun b => Solvable b.store)
  reached : ∀ x ∈ L, ∃ s a, NamedFrom N P q x.2 s a
  plain : ∀ x ∈ L, PlainBranch x.1
  /-- Every state a history of the word reaches represents the alternative. -/
  uniform : ∀ x ∈ L, ∀ s a, NamedFrom N P q x.2 s a → Represents N P C.world.scope x.1 s a
  graveyardReached : ∀ word ∈ G, ∃ s a, NamedFrom N P q word s a
  graveyard : ∀ word ∈ G, ∀ s a, NamedFrom N P q word s a → Terminal N P s ∧ ¬ StateFinished N s a
  nodup : (L.map Prod.snd + G).Nodup
  antichain : ∀ u ∈ L.map Prod.snd + G, ∀ v ∈ L.map Prod.snd + G, u <+: v → u = v
  cover : ∀ word s a, NamedFrom N P q word s a → Terminal N P s → (∃ x ∈ L, x.2 <+: word) ∨ word ∈ G

end Tracing

/-- The start's traced frontier. -/
theorem tracing_initial (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainQ : PlainComp q) (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) :
    Tracing N P q (Config.initial spaces q) {(initialBranch q, [])} 0 where
  branches := by
    change Multiset.map Prod.fst {(initialBranch q, ([] : List RuleName))} = Multiset.filter _ {initialBranch q}
    rw [Multiset.filter_singleton,
      if_pos (show Solvable (initialBranch (Ty := D.Ty) q).store from initial_live)]
    rfl
  reached := by
    intro x member
    rw [Multiset.mem_singleton.mp member]
    exact ⟨_, _, .nil _ _⟩
  plain := by
    intro x member
    rw [Multiset.mem_singleton.mp member]
    exact ⟨rfl, .inl ⟨q, rfl, plainQ⟩⟩
  uniform := by
    intro x member s a reached
    rw [Multiset.mem_singleton.mp member] at reached ⊢
    obtain ⟨rfl, rfl⟩ := reached.nil_inv
    exact start_represents N P q unopened
  graveyardReached := by intro word member; cases member
  graveyard := by intro word member; cases member
  nodup := by simp
  antichain := by
    intro u member v member' _
    simp only [Multiset.map_singleton, add_zero, Multiset.mem_singleton] at member member'
    rw [member, member']
  cover := by
    intro word s a _ _
    exact .inl ⟨(initialBranch q, []), Multiset.mem_singleton_self _, List.nil_prefix⟩

/-- A word extended by a name is not a prefix of the word. -/
theorem snoc_not_prefix (word : List RuleName) (n : RuleName) : ¬ word ++ [n] <+: word := by
  intro pre
  have := pre.length_le
  simp at this

/-- **A source step moves the traced frontier, explicitly.** The step moves one live alternative `b₀` of
the frontier, traced by the word `ν`; its names `ns` are the step's named moves. With no name, the
alternative failed and `ν` joins the graveyard; otherwise its live children replace it, each traced by
`ν` extended by its name. -/
theorem tracing_step_witness (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty)
    {C C' : Config κ Γ star D.Ty} {L : Multiset (Branch κ Γ star D.Ty × List RuleName)}
    {G : Multiset (List RuleName)} (tracing : Tracing N P q C L G)
    (step : SourceLanguage.Step D P supply C C') :
    ∃ (b₀ : Branch κ Γ star D.Ty) (ν : List RuleName)
      (L₀ : Multiset (Branch κ Γ star D.Ty × List RuleName))
      (ns : List RuleName) (child : RuleName → Branch κ Γ star D.Ty),
      L = (b₀, ν) ::ₘ L₀ ∧ ns.Nodup ∧
      (∀ n ∈ ns, NamedMove P C.world b₀ n C'.world (child n)) ∧
      ((ns = [] ∧ Tracing N P q C' L₀ (ν ::ₘ G)) ∨
        (ns ≠ [] ∧ Tracing N P q C'
          ((((ns : Multiset RuleName).filter fun n => Solvable (child n).store).map
              fun n => (child n, ν ++ [n])) + L₀) G)) := by
  obtain ⟨w, w', b, rest, bs, live, move⟩ := step
  have bInside : b ∈ L.map Prod.fst := by
    rw [tracing.branches]
    exact Multiset.mem_filter.mpr ⟨Multiset.mem_cons_self _ _, live⟩
  obtain ⟨⟨b₀, ν⟩, xMember, xb⟩ := Multiset.mem_map.mp bInside
  simp only at xb
  subst xb
  obtain ⟨L₀, split⟩ := Multiset.exists_cons_of_mem xMember
  have restBranches : L₀.map Prod.fst = rest.filter (fun b => Solvable b.store) := by
    have whole := tracing.branches
    rw [split, Multiset.map_cons] at whole
    change _ = Multiset.filter _ (b₀ ::ₘ rest) at whole
    rw [Multiset.filter_cons_of_pos (p := fun b => Solvable b.store) rest live] at whole
    exact (Multiset.cons_inj_right _).mp whole
  have plainB : PlainBranch b₀ := tracing.plain _ xMember
  have uniformB : ∀ s a, NamedFrom N P q ν s a → Represents N P w.scope b₀ s a :=
    tracing.uniform _ xMember
  have old : ∀ y ∈ L₀, y ∈ L := fun y member => by rw [split]; exact Multiset.mem_cons_of_mem member
  obtain ⟨ns, child, nodupNs, bsEq, named, unique, failNil, someLive⟩ := move_names plainB live move
  -- the words of the frontier and the graveyard, before
  have wordsEq : L.map Prod.snd + G = ν ::ₘ (L₀.map Prod.snd + G) := by
    rw [split, Multiset.map_cons, Multiset.cons_add]
  have nodupOld := tracing.nodup
  rw [wordsEq, Multiset.nodup_cons] at nodupOld
  obtain ⟨νFresh, nodupRest⟩ := nodupOld
  have inWords : ∀ u ∈ L₀.map Prod.snd + G, u ∈ L.map Prod.snd + G := fun u member => by
    rw [wordsEq]; exact Multiset.mem_cons_of_mem member
  have νInWords : ν ∈ L.map Prod.snd + G := by rw [wordsEq]; exact Multiset.mem_cons_self _ _
  -- a history through the alternative's word and one more name is the named move to a child
  have through : ∀ (n : RuleName) (rest' : List RuleName) (s a),
      NamedFrom N P q (ν ++ n :: rest') s a →
        n ∈ ns ∧ Solvable (child n).store ∧ ∃ s₁ a₁, NamedFrom N P q (ν ++ [n]) s₁ a₁ ∧
          ∀ s₁ a₁, NamedFrom N P q (ν ++ [n]) s₁ a₁ → Represents N P w'.scope (child n) s₁ a₁ := by
    intro n rest' s a history
    have reshaped : ν ++ n :: rest' = (ν ++ [n]) ++ rest' := by simp
    rw [reshaped] at history
    obtain ⟨s₁, a₁, front, _⟩ := history.split (ν ++ [n]) rest'
    have uniformChild : ∀ s₁ a₁, NamedFrom N P q (ν ++ [n]) s₁ a₁ →
        n ∈ ns ∧ Represents N P w'.scope (child n) s₁ a₁ ∧ Solvable (child n).store := by
      intro s₁ a₁ front
      obtain ⟨s₀, a₀, before, fired⟩ := front.snoc_inv
      obtain ⟨w'', b'', namedMove, rep'', _⟩ := reflection_named N plainP (uniformB s₀ a₀ before) plainB fired
      obtain ⟨inside, rfl, rfl⟩ := unique n w'' b'' namedMove
      exact ⟨inside, rep'', live_of_named N fired rep''⟩
    obtain ⟨inside, _, liveChild⟩ := uniformChild s₁ a₁ front
    exact ⟨inside, liveChild, s₁, a₁, front, fun s₁ a₁ front => (uniformChild s₁ a₁ front).2.1⟩
  by_cases nil : ns = []
  · -- the alternative failed: its word joins the graveyard
    have failing := failNil nil
    have noChildren : bs = 0 := by rw [bsEq, nil]; rfl
    refine ⟨b₀, ν, L₀, ns, child, split, nodupNs, named, .inl ⟨nil, ?_⟩⟩
    have sameWords : L₀.map Prod.snd + ν ::ₘ G = L.map Prod.snd + G := by
      rw [wordsEq, Multiset.add_cons]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change L₀.map Prod.fst = (bs + rest).filter _
      rw [noChildren, zero_add, restBranches]
    · exact fun y member => tracing.reached y (old y member)
    · exact fun y member => tracing.plain y (old y member)
    · intro y member s a reached
      exact (tracing.uniform y (old y member) s a reached).mono N (Move.scope_le move)
    · intro word member
      rcases Multiset.mem_cons.mp member with rfl | inG
      · exact tracing.reached _ xMember
      · exact tracing.graveyardReached word inG
    · intro word member s a reached
      rcases Multiset.mem_cons.mp member with rfl | inG
      · have rep := uniformB s a reached
        refine ⟨fail_still N (supply := supply) plainP rep plainB failing, fun finished => ?_⟩
        exact not_finished_of_fail failing ((finished_iff N rep).mpr finished).1
      · exact tracing.graveyard word inG s a reached
    · rw [sameWords]; exact tracing.nodup
    · rw [sameWords]; exact tracing.antichain
    · intro word s a reached terminal
      rcases tracing.cover word s a reached terminal with ⟨y, member, pre⟩ | inG
      · rcases Multiset.mem_cons.mp (show y ∈ (b₀, ν) ::ₘ L₀ by rw [← split]; exact member) with rfl | inL₀
        · obtain ⟨t, rfl⟩ := pre
          cases t with
          | nil => exact .inr (by simp)
          | cons n rest' =>
              obtain ⟨inside, _⟩ := through n rest' s a reached
              rw [nil] at inside
              cases inside
        · exact .inl ⟨y, inL₀, pre⟩
      · exact .inr (Multiset.mem_cons_of_mem inG)
  · -- the alternative moved to its children: their words extend its word by their names
    let liveNames : Multiset RuleName := (ns : Multiset RuleName).filter fun n => Solvable (child n).store
    let new : Multiset (Branch κ Γ star D.Ty × List RuleName) := liveNames.map fun n => (child n, ν ++ [n])
    have memLive : ∀ n, n ∈ liveNames ↔ n ∈ ns ∧ Solvable (child n).store := fun n => by
      simp [liveNames]
    have newChild : ∀ n ∈ liveNames, (∃ s a, NamedFrom N P q (ν ++ [n]) s a) ∧ PlainBranch (child n) := by
      intro n member
      obtain ⟨inside, liveChild⟩ := (memLive n).mp member
      obtain ⟨s₀, a₀, from₀⟩ := tracing.reached _ xMember
      obtain ⟨s₁, fired, _, plainChild⟩ := simulation_named N plainP (named n inside) (uniformB s₀ a₀ from₀)
        plainB liveChild (freshId_not_mem s₀)
      exact ⟨⟨s₁, _, .snoc from₀ fired⟩, plainChild⟩
    have newUniform : ∀ n ∈ liveNames, ∀ s a, NamedFrom N P q (ν ++ [n]) s a →
        Represents N P w'.scope (child n) s a := by
      intro n _ s a reached
      have history : NamedFrom N P q (ν ++ n :: []) s a := by simpa using reached
      obtain ⟨_, _, _, _, _, uniformAll⟩ := through n [] s a history
      exact uniformAll s a reached
    have newMem : ∀ y, y ∈ new ↔ ∃ n ∈ liveNames, (child n, ν ++ [n]) = y := fun y => by
      simp only [new, Multiset.mem_map]
    have newWords : ∀ u, u ∈ new.map Prod.snd ↔ ∃ n ∈ liveNames, ν ++ [n] = u := fun u => by
      simp only [new, Multiset.map_map, Function.comp_def, Multiset.mem_map]
    have νPrefix : ∀ u ∈ L₀.map Prod.snd + G, ¬ ν <+: u := by
      intro u member pre
      have same := tracing.antichain ν νInWords u (inWords u member) pre
      subst same
      exact νFresh member
    refine ⟨b₀, ν, L₀, ns, child, split, nodupNs, named, .inr ⟨nil, ?_⟩⟩
    refine ⟨?_, ?_, ?_, ?_, tracing.graveyardReached, tracing.graveyard, ?_, ?_, ?_⟩
    · -- the live alternatives
      change (new + L₀).map Prod.fst = (bs + rest).filter _
      rw [Multiset.map_add, Multiset.filter_add, restBranches]
      congr 1
      rw [bsEq, ← Multiset.map_coe, Multiset.filter_map]
      simp only [new, liveNames, Multiset.map_map]
      rfl
    · intro y member
      rcases Multiset.mem_add.mp member with inNew | inL₀
      · obtain ⟨n, inside, rfl⟩ := (newMem y).mp inNew
        exact (newChild n inside).1
      · exact tracing.reached y (old y inL₀)
    · intro y member
      rcases Multiset.mem_add.mp member with inNew | inL₀
      · obtain ⟨n, inside, rfl⟩ := (newMem y).mp inNew
        exact (newChild n inside).2
      · exact tracing.plain y (old y inL₀)
    · intro y member s a reached
      rcases Multiset.mem_add.mp member with inNew | inL₀
      · obtain ⟨n, inside, rfl⟩ := (newMem y).mp inNew
        exact newUniform n inside s a reached
      · exact (tracing.uniform y (old y inL₀) s a reached).mono N (Move.scope_le move)
    · -- distinct words
      rw [Multiset.map_add, add_assoc, Multiset.nodup_add]
      refine ⟨?_, nodupRest, ?_⟩
      · simp only [Multiset.map_map, Function.comp_def]
        refine Multiset.Nodup.map (fun n m same => ?_) (Multiset.Nodup.filter _ (Multiset.coe_nodup.mpr nodupNs))
        simpa using same
      · rw [Multiset.disjoint_left]
        intro u inNew inOld
        obtain ⟨n, _, rfl⟩ := (newWords u).mp inNew
        exact νPrefix _ inOld (List.prefix_append ν [n])
    · -- no word is a prefix of another
      rw [Multiset.map_add, add_assoc]
      intro u memberU v memberV pre
      rcases Multiset.mem_add.mp memberU with newU | oldU <;> rcases Multiset.mem_add.mp memberV with newV | oldV
      · obtain ⟨n, _, rfl⟩ := (newWords u).mp newU
        obtain ⟨m, _, rfl⟩ := (newWords v).mp newV
        exact pre.eq_of_length (by simp)
      · obtain ⟨n, _, rfl⟩ := (newWords u).mp newU
        exact absurd ((List.prefix_append ν [n]).trans pre) (νPrefix v oldV)
      · obtain ⟨m, _, rfl⟩ := (newWords v).mp newV
        rcases List.prefix_concat_iff.mp pre with same | shorter
        · exact absurd (same ▸ List.prefix_append ν [m]) (νPrefix u oldU)
        · have same := tracing.antichain u (inWords u oldU) ν νInWords shorter
          subst same
          exact absurd oldU νFresh
      · exact tracing.antichain u (inWords u oldU) v (inWords v oldV) pre
    · -- every complete history passes through the frontier or a failed alternative
      intro word s a reached terminal
      rcases tracing.cover word s a reached terminal with ⟨y, member, pre⟩ | inG
      · rcases Multiset.mem_cons.mp (show y ∈ (b₀, ν) ::ₘ L₀ by rw [← split]; exact member) with rfl | inL₀
        · obtain ⟨t, rfl⟩ := pre
          cases t with
          | nil =>
              exfalso
              obtain ⟨n, inside, liveChild⟩ := someLive nil
              have reachedν : NamedFrom N P q ν s a := by simpa using reached
              obtain ⟨s₁, fired, _⟩ := simulation_named N plainP (named n inside) (uniformB s a reachedν)
                plainB liveChild (freshId_not_mem s)
              exact terminal s₁ (firesNamed_fires N fired)
          | cons n rest' =>
              obtain ⟨inside, liveChild, _⟩ := through n rest' s a reached
              refine .inl ⟨(child n, ν ++ [n]), Multiset.mem_add.mpr (.inl ((newMem _).mpr
                ⟨n, (memLive n).mpr ⟨inside, liveChild⟩, rfl⟩)), ?_⟩
              exact ⟨rest', by simp⟩
        · exact .inl ⟨y, Multiset.mem_add.mpr (.inr inL₀), pre⟩
      · exact .inr inG

/-- **A source step moves the traced frontier.** -/
theorem tracing_step (plainP : PlainProgram P) (q : Comp κ Γ star D.Ty) {C C' : Config κ Γ star D.Ty}
    {L : Multiset (Branch κ Γ star D.Ty × List RuleName)} {G : Multiset (List RuleName)}
    (tracing : Tracing N P q C L G) (step : SourceLanguage.Step D P supply C C') :
    ∃ L' G', Tracing N P q C' L' G' := by
  obtain ⟨_, _, _, _, _, _, _, _, moved⟩ := tracing_step_witness N plainP q tracing step
  rcases moved with ⟨_, next⟩ | ⟨_, next⟩
  · exact ⟨_, _, next⟩
  · exact ⟨_, _, next⟩

/-- Every configuration a source run reaches has a traced frontier. -/
theorem tracing_runs (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) : ∃ L G, Tracing N P q C L G := by
  induction runs with
  | refl => exact ⟨_, _, tracing_initial N spaces q plainQ unopened⟩
  | tail _ step ih =>
      obtain ⟨L, G, tracing⟩ := ih
      exact tracing_step N plainP q tracing step

/-! ## The bag of answers -/

/-- **The bag of answers is the bag over the complete classes of histories of the step.** For a
program and a query of the first fragment, and every source run that ends (no live alternative can
move), the complete classes of the translated program's histories from the start, each counted
once, form a multiset `M`, and the bag of answers is the answers of the finished classes of `M`. -/
theorem bag_of_classes (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C : Config κ Γ star D.Ty}
    (runs : Runs D P supply (Config.initial spaces q) C) (quiet : C.Quiescent P supply) :
    ∃ M : Multiset (List RuleName),
      (∀ word, M.count word = if CompleteClass N P q word then 1 else 0) ∧
        C.answers (D := D) = (M.filter (FinishedClass N P q)).map (classAnswer N P q) := by
  obtain ⟨L, G, tracing⟩ := tracing_runs N spaces q plainP plainQ unopened runs
  have liveIn : ∀ b ∈ C.branches, Solvable b.store → b ∈ L.map Prod.fst := fun b member live => by
    rw [tracing.branches]; exact Multiset.mem_filter.mpr ⟨member, live⟩
  have finishedAll : ∀ x ∈ L, x.1.Finished (D := D) := by
    intro x member
    have inBranches : x.1 ∈ C.branches.filter (fun b => Solvable b.store) := by
      rw [← tracing.branches]; exact Multiset.mem_map_of_mem _ member
    obtain ⟨inC, live⟩ := Multiset.mem_filter.mp inBranches
    by_contra notFinished
    obtain ⟨w', bs, move⟩ := plain_moves (supply := supply) C.world (tracing.plain x member) notFinished
    exact quiet x.1 inC live w' bs move
  have terminalAt : ∀ x ∈ L, ∀ s a, NamedFrom N P q x.2 s a → Terminal N P s := by
    intro x member s a reached s' fires
    exact finished_still N (supply := supply) plainP (tracing.uniform x member s a reached)
      (tracing.plain x member) (finishedAll x member) fires
  have complete : ∀ word, word ∈ L.map Prod.snd + G ↔ CompleteClass N P q word := by
    intro word
    constructor
    · intro member
      rcases Multiset.mem_add.mp member with inL | inG
      · obtain ⟨x, xMember, rfl⟩ := Multiset.mem_map.mp inL
        obtain ⟨s, a, reached⟩ := tracing.reached x xMember
        exact ⟨s, a, reached, terminalAt x xMember s a reached⟩
      · obtain ⟨s, a, reached⟩ := tracing.graveyardReached word inG
        exact ⟨s, a, reached, (tracing.graveyard word inG s a reached).1⟩
    · rintro ⟨s, a, reached, terminal⟩
      rcases tracing.cover word s a reached terminal with ⟨x, xMember, pre⟩ | inG
      · obtain ⟨t, rfl⟩ := pre
        cases t with
        | nil => exact Multiset.mem_add.mpr (.inl (Multiset.mem_map.mpr ⟨x, xMember, by simp⟩))
        | cons n rest' =>
            exfalso
            have reshaped : x.2 ++ n :: rest' = (x.2 ++ [n]) ++ rest' := by simp
            rw [reshaped] at reached
            obtain ⟨s₁, a₁, front, _⟩ := reached.split (x.2 ++ [n]) rest'
            obtain ⟨s₀, a₀, before, fired⟩ := front.snoc_inv
            exact terminalAt x xMember s₀ a₀ before s₁ (firesNamed_fires N fired)
      · exact Multiset.mem_add.mpr (.inr inG)
  refine ⟨L.map Prod.snd + G, ?_, ?_⟩
  · intro word
    by_cases inside : word ∈ L.map Prod.snd + G
    · rw [if_pos ((complete word).mp inside)]
      exact Multiset.count_eq_one_of_mem tracing.nodup inside
    · rw [if_neg (fun c => inside ((complete word).mpr c))]
      exact Multiset.count_eq_zero.mpr inside
  · -- the answers
    have graveNot : G.filter (FinishedClass N P q) = 0 := by
      rw [Multiset.filter_eq_nil]
      rintro word inG ⟨s, a, reached, finished⟩
      exact (tracing.graveyard word inG s a reached).2 finished
    have liveAll : (L.map Prod.snd).filter (FinishedClass N P q) = L.map Prod.snd := by
      rw [Multiset.filter_eq_self]
      intro word inL
      obtain ⟨x, xMember, rfl⟩ := Multiset.mem_map.mp inL
      obtain ⟨s, a, reached⟩ := tracing.reached x xMember
      have rep := tracing.uniform x xMember s a reached
      have live : Solvable x.1.store := by
        have inBranches : x.1 ∈ C.branches.filter (fun b => Solvable b.store) := by
          rw [← tracing.branches]; exact Multiset.mem_map_of_mem _ xMember
        exact (Multiset.mem_filter.mp inBranches).2
      exact ⟨s, a, reached, (finished_iff N rep).mp ⟨finishedAll x xMember, live⟩⟩
    have answerAt : ∀ x ∈ L, classAnswer N P q x.2 = x.1.answer (D := D) := by
      intro x member
      ext g
      constructor
      · rintro ⟨s, a, reached, shown⟩
        rw [answer_eq N (tracing.uniform x member s a reached) (finishedAll x member)] at shown
        exact shown
      · intro answered
        obtain ⟨s, a, reached⟩ := tracing.reached x member
        refine ⟨s, a, reached, ?_⟩
        rw [answer_eq N (tracing.uniform x member s a reached) (finishedAll x member)]
        exact answered
    have sameFilter : C.branches.filter (fun b => b.Finished (D := D) ∧ Solvable b.store) =
        C.branches.filter (fun b => Solvable b.store) := by
      apply Multiset.filter_congr
      intro b member
      constructor
      · exact fun both => both.2
      · intro live
        obtain ⟨x, xMember, rfl⟩ := Multiset.mem_map.mp (liveIn b member live)
        exact ⟨finishedAll x xMember, live⟩
    rw [Multiset.filter_add, graveNot, add_zero, liveAll, Multiset.map_map]
    unfold Config.answers
    rw [sameFilter, ← tracing.branches, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x member
    exact (answerAt x member).symm

include N in
/-- **For the first fragment, the bag of answers does not depend on the source run**: two runs from
one query that both end show the same bag. The proof reads both bags off the step of the translated
program, so it asks for the signature's control nodes `N`. -/
theorem answers_determined (spaces : Term S Γ star → Multiset (Row κ Γ star)) (q : Comp κ Γ star D.Ty)
    (plainP : PlainProgram P) (plainQ : PlainComp q)
    (unopened : ∀ t ∈ q.data, ∀ x ∈ support t, x.scopes = []) {C₁ C₂ : Config κ Γ star D.Ty}
    (runs₁ : Runs D P supply (Config.initial spaces q) C₁) (quiet₁ : C₁.Quiescent P supply)
    (runs₂ : Runs D P supply (Config.initial spaces q) C₂) (quiet₂ : C₂.Quiescent P supply) :
    C₁.answers (D := D) = C₂.answers (D := D) := by
  obtain ⟨M₁, count₁, answers₁⟩ := bag_of_classes N spaces q plainP plainQ unopened runs₁ quiet₁
  obtain ⟨M₂, count₂, answers₂⟩ := bag_of_classes N spaces q plainP plainQ unopened runs₂ quiet₂
  have same : M₁ = M₂ := Multiset.ext.mpr fun word => by rw [count₁, count₂]
  rw [answers₁, answers₂, same]

/-- **The answer of a class depends only on its word of rules**: two named histories whose names
denote the same rules end in states that show the same answer and are finished together. Names add
nothing to an answer; they only count. -/
theorem answer_of_rule_word (q : Comp κ Γ star D.Ty) {ν₁ ν₂ : List RuleName}
    (same : ν₁.filterMap (ruleNamed N P) = ν₂.filterMap (ruleNamed N P)) {s₁ s₂ : HostState S} {a₁ a₂ : ℕ}
    (h₁ : NamedFrom N P q ν₁ s₁ a₁) (h₂ : NamedFrom N P q ν₂ s₂ a₂) :
    stateAnswer N s₁ a₁ = stateAnswer N s₂ a₂ ∧ (StateFinished N s₁ a₁ ↔ StateFinished N s₂ a₂) := by
  have c₁ := chain_forget N h₁
  have c₂ := chain_forget N h₂
  rw [same] at c₁
  exact same_word_same_answer N q c₁ c₂

#print axioms answer_of_rule_word
#print axioms fail_still
#print axioms live_of_named
#print axioms tracing_initial
#print axioms tracing_step_witness
#print axioms tracing_step
#print axioms tracing_runs
#print axioms bag_of_classes
#print axioms answers_determined

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Alternatives
