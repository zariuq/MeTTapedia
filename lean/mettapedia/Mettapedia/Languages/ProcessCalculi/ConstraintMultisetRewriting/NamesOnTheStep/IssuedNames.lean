import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Generative names on the step: issued by the firing that makes them

A generative name is meaningful only once some firing has issued it. This module states that
discipline once, for every step of the core, without changing the core.

## Names on a step (`Mentions`)

A naming of a step says which generative names each state mentions (in its store or its
knowledge) and which names each firing writes (in what it takes, reads, tells or makes: matching is
telling, so takes and reads write their equations into the knowledge). Guards and predicate queries
only read; they are not writes. The one law, `Mentions.result_subset`, is locality: the result of an
admitted firing mentions only names of its state or of the firing's own writes.

## The ledger (`withLedger`)

Over any step and any discipline `D`, the **ledger step** has states that carry the names issued so
far and firings that carry the names they issue. Its frames, knowledge, store, preparation and
settlement are the base step's; admission is the base admission together with `D`; the result adds
the issued names to the ledger (`withLedger_result`). Its runs are runs of the base step
(`forget`, `forget_last`). The discipline of the calculus is `Issues`:

* the issued names are pairwise distinct and new to the ledger (`IssuesFresh`);
* every name the firing writes was issued before, or is issued by this firing (`ChecksUses`).

## The invariant and its preservation

`Invariant`: every name the store and the knowledge mention has been issued.

* `invariant_result`: **every admitted firing preserves the invariant**, for any discipline that
  checks uses, over any step whose naming is local.
* `issued_new`: a name issued by an admitted firing is new to the store, to the knowledge and to
  every name issued earlier, whenever the discipline issues fresh names and the invariant holds.
* Along runs (`invariant_last`, `ledger_last`, `issuedAlong_nodup`, `issued_new_along`,
  `no_use_before_issue`): the invariant holds at every reached state; the ledger grows by exactly the
  names issued; no name is issued twice or was issued before the run; every name issued along a run is
  new to the store, the knowledge and the ledger where it is issued; and no firing writes a name
  before it is issued.

Each half of `Issues` is needed, and the discipline is not stricter than needed; the
counterexamples and the positive controls are in `IssuedNamesControls` and `IssuedNamesRuns`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep

universe uO uT uH uOcc uS uF uN

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {N : Type uN}

/-- **Names on a step.** The generative names each state mentions in its store or knowledge, and
the names each firing writes. Locality: an admitted firing's result mentions only names of its
state or of the firing's writes. -/
structure Mentions (P : Interface.Step X O State Firing) (N : Type uN) where
  state : State → Set N
  firing : {s : State} → Firing s → Set N
  result_subset : ∀ {s : State} (f : Firing s) (admitted : P.Admits f),
    state (P.result f admitted) ⊆ state s ∪ firing f

/-- A discipline for issuing: given the ledger, a base firing and the names it would issue. -/
abbrev Discipline (State : Type uS) (Firing : State → Type uF) (N : Type uN) :=
  (s : State) → Set N → Firing s → List N → Prop

/-- **The step with a ledger of issued names.** A state is a base state with the names issued so
far; a firing is a base firing with the names it issues. Everything but admission and the ledger is
the base step's; admission adds the discipline `D`. -/
def withLedger (P : Interface.Step X O State Firing) (D : Discipline State Firing N) :
    Interface.Step X O (State × Set N) (fun σ => Firing σ.1 × List N) where
  frame σ := P.frame σ.1
  knowledge σ := P.knowledge σ.1
  present σ := P.present σ.1
  selection f := P.selection f.1
  target f := P.target f.1
  extension f := P.extension f.1
  information f := P.information f.1
  information_refines := fun {_s} f {_b} τ solved => P.information_refines f.1 τ solved
  Shapes f := P.Shapes f.1
  preparedResult := fun {σ} f p => (P.preparedResult f.1 p, σ.2 ∪ {n | n ∈ f.2})
  present_preparedResult := fun f p => P.present_preparedResult f.1 p
  preparedSettle := fun f p => P.preparedSettle f.1 p
  result_refines := fun {_s} f p {_b} τ solved => P.result_refines f.1 p τ solved
  Admits := fun {σ} f => P.Admits f.1 ∧ D σ.1 σ.2 f.1 f.2
  admitted_prepares := fun f admitted => P.admitted_prepares f.1 admitted.1

section Ledger

variable {P : Interface.Step X O State Firing} {D : Discipline State Firing N}

/-- The result of an admitted firing of the ledger step: the base result, and the ledger with the
issued names added. -/
theorem withLedger_result {σ : State × Set N} (f : Firing σ.1 × List N)
    (admitted : (withLedger P D).Admits f) :
    (withLedger P D).result f admitted = (P.result f.1 admitted.1, σ.2 ∪ {n | n ∈ f.2}) := rfl

theorem withLedger_admits_iff {σ : State × Set N} (f : Firing σ.1 × List N) :
    (withLedger P D).Admits f ↔ P.Admits f.1 ∧ D σ.1 σ.2 f.1 f.2 := Iff.rfl

/-- A run of the ledger step, read in the base step. -/
def forget : {σ : State × Set N} → (withLedger P D).Run σ → P.Run σ.1
  | _, .nil σ => .nil σ.1
  | _, .cons f admitted rest => .cons f.1 admitted.1 (forget rest)

theorem forget_last : ∀ {σ : State × Set N} (r : (withLedger P D).Run σ),
    (forget r).last = r.last.1
  | _, .nil _ => rfl
  | _, .cons _ _ rest => forget_last rest

/-- The names a run issues, in order. -/
def issuedAlong : {σ : State × Set N} → (withLedger P D).Run σ → List N
  | _, .nil _ => []
  | _, .cons f _ rest => f.2 ++ issuedAlong rest

/-- **The ledger grows by exactly the names issued.** -/
theorem ledger_last : ∀ {σ : State × Set N} (r : (withLedger P D).Run σ),
    r.last.2 = σ.2 ∪ {n | n ∈ issuedAlong r}
  | σ, .nil _ => by
      ext n
      simp [Interface.Step.Run.last, issuedAlong]
  | σ, .cons f admitted rest => by
      have later := ledger_last rest
      change rest.last.2 = σ.2 ∪ {n | n ∈ f.2 ++ issuedAlong rest}
      rw [later]
      change (σ.2 ∪ {n | n ∈ f.2}) ∪ {n | n ∈ issuedAlong rest} = _
      ext n
      simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_append, or_assoc]

end Ledger

/-! ## The discipline and the invariant -/

section Discipline

variable {P : Interface.Step X O State Firing}

/-- **The issuing discipline**: the issued names are pairwise distinct and new to the ledger, and
every name the firing writes was issued before or is issued by it. -/
def Issues (M : Mentions P N) : Discipline State Firing N :=
  fun _ issued f fresh => fresh.Nodup ∧ (∀ n ∈ fresh, n ∉ issued) ∧
    M.firing f ⊆ issued ∪ {n | n ∈ fresh}

/-- A discipline **checks uses**: an admitted firing writes only names issued before or by it. -/
def ChecksUses (M : Mentions P N) (D : Discipline State Firing N) : Prop :=
  ∀ (s : State) (issued : Set N) (f : Firing s) (fresh : List N), D s issued f fresh →
    M.firing f ⊆ issued ∪ {n | n ∈ fresh}

/-- A discipline **issues fresh names**: pairwise distinct and new to the ledger. -/
def IssuesFresh (D : Discipline State Firing N) : Prop :=
  ∀ (s : State) (issued : Set N) (f : Firing s) (fresh : List N), D s issued f fresh →
    fresh.Nodup ∧ ∀ n ∈ fresh, n ∉ issued

theorem issues_checksUses (M : Mentions P N) : ChecksUses M (Issues M) :=
  fun _ _ _ _ issued => issued.2.2

theorem issues_issuesFresh (M : Mentions P N) : IssuesFresh (Issues M) :=
  fun _ _ _ _ issued => ⟨issued.1, issued.2.1⟩

/-- **The issuing invariant**: every name the store and the knowledge mention has been issued. -/
def Invariant (M : Mentions P N) (σ : State × Set N) : Prop := M.state σ.1 ⊆ σ.2

variable {M : Mentions P N} {D : Discipline State Firing N}

/-- **Every admitted firing preserves the invariant**, for every step with a local naming and
every discipline that checks uses. -/
theorem invariant_result (uses : ChecksUses M D) {σ : State × Set N} (f : Firing σ.1 × List N)
    (admitted : (withLedger P D).Admits f) (invariant : Invariant M σ) :
    Invariant M ((withLedger P D).result f admitted) := by
  intro n mentioned
  have local_ := M.result_subset f.1 admitted.1 mentioned
  have written := uses σ.1 σ.2 f.1 f.2 admitted.2
  change n ∈ σ.2 ∪ {n | n ∈ f.2}
  rcases local_ with old | new
  · exact Set.mem_union_left _ (invariant old)
  · exact written new

/-- **An issued name is new**: to the store and knowledge it is issued at, and to every name issued
before. -/
theorem issued_new (fresh : IssuesFresh D) {σ : State × Set N} (f : Firing σ.1 × List N)
    (admitted : (withLedger P D).Admits f) (invariant : Invariant M σ) :
    ∀ n ∈ f.2, n ∉ M.state σ.1 ∧ n ∉ σ.2 := by
  intro n issued
  have unissued := (fresh σ.1 σ.2 f.1 f.2 admitted.2).2 n issued
  exact ⟨fun mentioned => unissued (invariant mentioned), unissued⟩

/-- **The invariant holds at the end of every run** that starts where it holds. -/
theorem invariant_last (uses : ChecksUses M D) :
    ∀ {σ : State × Set N} (r : (withLedger P D).Run σ), Invariant M σ → Invariant M r.last
  | _, .nil _, invariant => invariant
  | _, .cons f admitted rest, invariant =>
      invariant_last uses rest (invariant_result uses f admitted invariant)

/-- **No name is issued twice along a run, or issued before it.** -/
theorem issuedAlong_nodup (fresh : IssuesFresh D) :
    ∀ {σ : State × Set N} (r : (withLedger P D).Run σ),
      (issuedAlong r).Nodup ∧ ∀ n ∈ issuedAlong r, n ∉ σ.2
  | _, .nil _ => ⟨List.nodup_nil, fun _ member => absurd member List.not_mem_nil⟩
  | σ, .cons f admitted rest => by
      obtain ⟨restNodup, restNew⟩ := issuedAlong_nodup fresh rest
      obtain ⟨here, hereNew⟩ := fresh σ.1 σ.2 f.1 f.2 admitted.2
      have restNew' : ∀ n ∈ issuedAlong rest, n ∉ σ.2 ∧ n ∉ f.2 := by
        intro n member
        have outside := restNew n member
        change n ∉ σ.2 ∪ {n | n ∈ f.2} at outside
        exact ⟨fun old => outside (Set.mem_union_left _ old),
          fun new => outside (Set.mem_union_right _ new)⟩
      refine ⟨List.nodup_append.mpr ⟨here, restNodup, ?_⟩, ?_⟩
      · intro a first b second same
        exact (restNew' b second).2 (same ▸ first)
      · intro n member
        rcases List.mem_append.mp member with first | second
        · exact hereNew n first
        · exact (restNew' n second).1

/-- **Every name issued along a run is new where it is issued**: to the store, the knowledge and the
ledger of the state its firing fires at. -/
theorem issued_new_along (uses : ChecksUses M D) (fresh : IssuesFresh D) :
    ∀ {σ : State × Set N} (r : (withLedger P D).Run σ), Invariant M σ →
      ∀ x ∈ r.word, ∀ n ∈ x.2.2, n ∉ M.state x.1.1 ∧ n ∉ x.1.2
  | _, .nil _, _ => fun _ member => absurd member List.not_mem_nil
  | _, .cons f admitted rest, invariant => by
      intro x member
      simp only [Interface.Step.Run.word, List.mem_cons] at member
      rcases member with here | later
      · subst here
        exact issued_new fresh f admitted invariant
      · exact issued_new_along uses fresh rest (invariant_result uses f admitted invariant) x later

/-- **No firing writes a name before it is issued.** -/
theorem no_use_before_issue (uses : ChecksUses M D) :
    ∀ {σ : State × Set N} (r : (withLedger P D).Run σ),
      ∀ x ∈ r.word, M.firing x.2.1 ⊆ x.1.2 ∪ {n | n ∈ x.2.2}
  | _, .nil _ => fun _ member => absurd member List.not_mem_nil
  | σ, .cons f admitted rest => by
      intro x member
      simp only [Interface.Step.Run.word, List.mem_cons] at member
      rcases member with here | later
      · subst here
        exact uses σ.1 σ.2 f.1 f.2 admitted.2
      · exact no_use_before_issue uses rest x later

/-- **The calculus's discipline keeps the invariant along every run.** -/
theorem issues_invariant_last {σ : State × Set N} (r : (withLedger P (Issues M)).Run σ)
    (invariant : Invariant M σ) : Invariant M r.last :=
  invariant_last (issues_checksUses M) r invariant

end Discipline

#print axioms withLedger_result
#print axioms ledger_last
#print axioms invariant_result
#print axioms issued_new
#print axioms invariant_last
#print axioms issuedAlong_nodup
#print axioms issued_new_along
#print axioms no_use_before_issue

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep
