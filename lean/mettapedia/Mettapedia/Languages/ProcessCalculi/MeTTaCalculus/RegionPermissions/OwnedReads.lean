import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.ReadPolarity

/-!
# Owned reads: which facets others hold decides which reads stay true

`InteractionTypes.Facets` gives a system of processes that hold facets at names and learn the
facets carried by what they take or keep (`AuthorityRun`). This module asks what the *other*
processes can do to a read made by one process, the **owner** of a region.

**Others' authority** (`OthersAuthority`) at a name is a facet held there by a process other than
the owner, or carried by an occurrence of the store. Along a run of the other processes it never
grows (`run_othersAuthority_mono`); the owner's own steps keep it from growing as long as
the owner makes no occurrence carrying that facet (it does not hand the facet out).

## The owned laws

* **Nobody else can send at the read's names, so a universal read stays true**
  (`owned_antitone_stable`): absence, "every row here is like this", over any run of the others.
* **Nobody else can receive there, so an existential read stays true** (`owned_monotone_stable`).
* **Nobody else can write there, so every read stays true** (`owned_exact_stable`).

The hypotheses are needed, for held facets: a process other than the owner that holds `send` at a
name of the read falsifies its absence with one step (`absence_falsified_of_other_send`), and one
that holds `receive` there takes the only witness of an existential read
(`witness_taken_of_other_receive`). For facets that are only carried by occurrences, the bound is
sufficient but not exact: a carried facet may sit where no other process can reach it.
`DelegatedReads` gives the exact condition for authority that moves by delegation.

## The kernel as owner, and the limit of "sole writer"

When only the kernel holds `send` at its rule region, its absence check that a head is fresh
(admission) and its reads over all rules (promotion) stay true across every run of the users
(`kernel_reads_stable`). They do not stay true across the kernel's *own* other commits: two
admissions of one head are each enabled at the same store and cannot both run
(`Controls.kernel_self_skew`). "The kernel is the sole writer" means the sole *sequential* writer:
a kernel that admits concurrently must serialize or validate its own commits on that region.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

universe u v w x

variable {O : Type u} [DecidableEq O] {R : Type v} {N : Type w} {I : Type x} [DecidableEq I]

section Others

variable (label : O → R) (carries : R → Rights N)

/-- **Others' authority** at a name: a facet held there by a process other than `owner`, or
carried by an occurrence of the store. -/
def OthersAuthority (Γ : I → Rights N) (S : Finset O) (owner : I) (n : N) (f : Facet) : Prop :=
  (∃ i, i ≠ owner ∧ Γ i n f = true) ∨ ∃ o ∈ S, carries (label o) n f = true

variable {label carries} {loc : R → N}

/-- A step of the system creates none of the others' authority, as long as, when the owner is the
one stepping, it makes nothing carrying that facet. -/
theorem step_othersAuthority_mono {Γ Γ' : I → Rights N} {S S' : Finset O} {i : I}
    {c : Commit O R} (step : AuthorityStep label loc carries Γ S i c Γ' S') {owner : I} {n : N}
    {f : Facet} (keeps : i = owner → ∀ o ∈ c.made, carries (label o) n f = false)
    (after : OthersAuthority label carries Γ' S' owner n f) :
    OthersAuthority label carries Γ S owner n f := by
  rcases after with ⟨j, notOwner, held⟩ | ⟨o, inS', carried⟩
  · rw [step.rights] at held
    by_cases same : j = i
    · subst same
      rw [Function.update_self] at held
      rcases Bool.or_eq_true _ _ |>.mp held with old | new
      · exact Or.inl ⟨j, notOwner, old⟩
      · obtain ⟨o, used, carried⟩ := of_decide_eq_true new
        exact Or.inr ⟨o, step.enabled.learnedFrom_subset used, carried⟩
    · rw [Function.update_of_ne same] at held
      exact Or.inl ⟨j, notOwner, held⟩
  · rw [step.store] at inS'
    rcases mem_fire.mp inS' with ⟨inS, -⟩ | made
    · exact Or.inr ⟨o, inS, carried⟩
    · by_cases ownerStep : i = owner
      · rw [keeps ownerStep o made] at carried
        exact absurd carried (by decide)
      · exact Or.inl ⟨i, ownerStep, step.attenuates o made n f carried⟩

/-- **Along a run, the others' authority never grows**, as long as the owner hands out nothing
carrying the facet. -/
theorem run_othersAuthority_mono {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {owner : I} {n : N} {f : Facet}
    (keeps : ∀ x ∈ run, x.1 = owner → ∀ o ∈ x.2.made, carries (label o) n f = false)
    (after : OthersAuthority label carries Γ' S' owner n f) :
    OthersAuthority label carries Γ S owner n f := by
  induction h with
  | nil => exact after
  | @cons Γ₀ Γ₁ Γ₂ S₀ S₁ S₂ i c rest step _ ih =>
      have keepsRest : ∀ x ∈ rest, x.1 = owner → ∀ o ∈ x.2.made, carries (label o) n f = false :=
        fun x member => keeps x (List.mem_cons_of_mem _ member)
      exact step_othersAuthority_mono step (keeps (i, c) List.mem_cons_self) (ih keepsRest after)

/-- **Without others' `send` at a name, no other process makes there**, along any run in which
the owner hands out no `send` at that name. -/
theorem run_others_never_make {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {owner : I} {n : N}
    (keeps : ∀ x ∈ run, x.1 = owner → ∀ o ∈ x.2.made, carries (label o) n .send = false)
    (unheld : ¬ OthersAuthority label carries Γ S owner n .send) :
    ∀ x ∈ run, x.1 ≠ owner → ∀ o ∈ x.2.made, loc (label o) ≠ n := by
  induction h with
  | nil => simp
  | @cons Γ₀ Γ₁ Γ₂ S₀ S₁ S₂ i c rest step after ih =>
      intro y member notOwner o made atN
      rcases List.mem_cons.mp member with rfl | inRest
      · have held := step.formed.made o made
        rw [atN] at held
        exact unheld (Or.inl ⟨i, notOwner, held⟩)
      · have keepsRest : ∀ x ∈ rest, x.1 = owner → ∀ o ∈ x.2.made,
            carries (label o) n .send = false :=
          fun x member => keeps x (List.mem_cons_of_mem _ member)
        refine ih keepsRest (fun later => unheld ?_) y inRest notOwner o made atN
        exact step_othersAuthority_mono step (keeps (i, c) List.mem_cons_self) later

/-- **Without others' `receive` at a name, no other process takes there**, along any run in
which the owner hands out no `receive` at that name. -/
theorem run_others_never_take {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {owner : I} {n : N}
    (keeps : ∀ x ∈ run, x.1 = owner → ∀ o ∈ x.2.made, carries (label o) n .receive = false)
    (unheld : ¬ OthersAuthority label carries Γ S owner n .receive) :
    ∀ x ∈ run, x.1 ≠ owner → ∀ o ∈ x.2.taken, loc (label o) ≠ n := by
  induction h with
  | nil => simp
  | @cons Γ₀ Γ₁ Γ₂ S₀ S₁ S₂ i c rest step after ih =>
      intro y member notOwner o taken atN
      rcases List.mem_cons.mp member with rfl | inRest
      · have held := step.formed.taken o taken
        rw [atN] at held
        exact unheld (Or.inl ⟨i, notOwner, held⟩)
      · have keepsRest : ∀ x ∈ rest, x.1 = owner → ∀ o ∈ x.2.made,
            carries (label o) n .receive = false :=
          fun x member => keeps x (List.mem_cons_of_mem _ member)
        refine ih keepsRest (fun later => unheld ?_) y inRest notOwner o taken atN
        exact step_othersAuthority_mono step (keeps (i, c) List.mem_cons_self) later

/-- The store at the end of a run is the store its commits fire to. -/
theorem run_store_eq {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S') :
    S' = fireList S (run.map Prod.snd) := by
  induction h with
  | nil => rfl
  | cons step _ ih => rw [List.map_cons, fireList_cons, ← step.store]; exact ih

end Others

/-! ## The owned laws -/

section Owned

variable {label : O → R} {loc : R → N} {carries : R → Rights N} {A : N → Bool}
  {P : Finset O → Prop}

/-- The commits of a run of other processes make nothing at names where the others hold and
carry no `send`. -/
theorem others_makeOutside {Γ Γ' : I → Rights N} {S S' : Finset O} {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {owner : I} (others : ∀ x ∈ run, x.1 ≠ owner)
    (unheld : ∀ n, A n = true → ¬ OthersAuthority label carries Γ S owner n .send) :
    ∀ e ∈ run.map Prod.snd, MakesOutside label loc A e := by
  intro e member o made
  obtain ⟨x, inRun, rfl⟩ := List.mem_map.mp member
  by_contra atA
  have atA' : A (loc (label o)) = true := by simpa using atA
  exact run_others_never_make h (fun y inRun' isOwner => absurd isOwner (others y inRun'))
    (unheld _ atA') x inRun (others x inRun) o made rfl

/-- The commits of a run of other processes take nothing at names where the others hold and
carry no `receive`. -/
theorem others_takeOutside {Γ Γ' : I → Rights N} {S S' : Finset O} {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {owner : I} (others : ∀ x ∈ run, x.1 ≠ owner)
    (unheld : ∀ n, A n = true → ¬ OthersAuthority label carries Γ S owner n .receive) :
    ∀ e ∈ run.map Prod.snd, TakesOutside label loc A e := by
  intro e member o taken
  obtain ⟨x, inRun, rfl⟩ := List.mem_map.mp member
  by_contra atA
  have atA' : A (loc (label o)) = true := by simpa using atA
  exact run_others_never_take h (fun y inRun' isOwner => absurd isOwner (others y inRun'))
    (unheld _ atA') x inRun (others x inRun) o taken rfl

/-- **Owned universal reads.** When no other process holds or receives `send` at the read's
names, a universal read stays true across every run of the others. -/
theorem owned_antitone_stable {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {owner : I} (others : ∀ x ∈ run, x.1 ≠ owner)
    (unheld : ∀ n, A n = true → ¬ OthersAuthority label carries Γ S owner n .send)
    (antitone : DownwardClosed P) (holds : P (restrict label loc A S)) :
    P (restrict label loc A S') := by
  rw [run_store_eq h]
  exact antitone_stable_of_noMake antitone (others_makeOutside h others unheld) holds

/-- **Owned existential reads.** When no other process holds or receives `receive` at the read's
names, an existential read stays true across every run of the others. -/
theorem owned_monotone_stable {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {owner : I} (others : ∀ x ∈ run, x.1 ≠ owner)
    (unheld : ∀ n, A n = true → ¬ OthersAuthority label carries Γ S owner n .receive)
    (monotone : UpwardClosed P) (holds : P (restrict label loc A S)) :
    P (restrict label loc A S') := by
  rw [run_store_eq h]
  exact monotone_stable_of_noTake monotone (others_takeOutside h others unheld) holds

/-- **Owned exact reads.** When no other process can write at the read's names, nothing there
changes across a run of the others. -/
theorem owned_exact_stable {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {owner : I} (others : ∀ x ∈ run, x.1 ≠ owner)
    (noSend : ∀ n, A n = true → ¬ OthersAuthority label carries Γ S owner n .send)
    (noReceive : ∀ n, A n = true → ¬ OthersAuthority label carries Γ S owner n .receive) :
    restrict label loc A S' = restrict label loc A S := by
  rw [run_store_eq h]
  exact stable_of_noWrite (others_makeOutside h others noSend)
    (others_takeOutside h others noReceive) S

end Owned

/-! ## The hypotheses are needed: one step of another holder -/

section Necessity

variable {label : O → R} {loc : R → N} {carries : R → Rights N}

/-- **Another holder of `send` falsifies an absence read in one step.** If a process other than
the owner holds `send` at a name `n` of the read, and an occurrence `o` that carries no facet can
be made fresh at `n`, its one-step run is a run of the others and leaves `o` at the read's names. -/
theorem absence_falsified_of_other_send {Γ : I → Rights N} {S : Finset O} {owner i : I}
    (notOwner : i ≠ owner) {A : N → Bool} {o : O} (fresh : o ∉ S)
    (atA : A (loc (label o)) = true) (held : Γ i (loc (label o)) .send = true)
    (inert : ∀ m f, carries (label o) m f = false) :
    AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S [(i, Commit.makeOne (R := R) o)]
        (Function.update Γ i (fun n f => Γ i n f || learned label carries (Commit.makeOne (R := R) o) n f))
        (fire S (Commit.makeOne (R := R) o)) ∧
      (∀ x ∈ [(i, Commit.makeOne (R := R) o)], x.1 ≠ owner) ∧
      o ∈ restrict label loc A (fire S (Commit.makeOne (R := R) o)) := by
  refine ⟨.cons ⟨⟨by simp [Commit.makeOne], by simp [Commit.makeOne], by simp [Commit.makeOne],
      by simpa [Commit.makeOne] using fresh, by simp [Commit.makeOne]⟩,
    ⟨by simp [Commit.makeOne], by simp [Commit.makeOne], ?_, by simp [Commit.makeOne]⟩, ?_, rfl, rfl⟩ (.nil _ _),
    by simpa using notOwner, ?_⟩
  · intro p made
    simp only [Commit.makeOne, Finset.mem_singleton] at made
    subst made
    exact held
  · intro p made m f carried
    simp only [Commit.makeOne, Finset.mem_singleton] at made
    subst made
    rw [inert m f] at carried
    exact absurd carried (by decide)
  · exact mem_restrict.mpr ⟨mem_fire.mpr (Or.inr (by simp [Commit.makeOne])), atA⟩

/-- **Another holder of `receive` takes the witness of an existential read.** If a process other
than the owner holds `receive` at the name of `o`, and `o` is the only occurrence at the read's
names, its one-step run leaves nothing there. -/
theorem witness_taken_of_other_receive {Γ : I → Rights N} {S : Finset O} {owner i : I}
    (notOwner : i ≠ owner) {A : N → Bool} {o : O} (inS : o ∈ S)
    (only : restrict label loc A S = {o}) (held : Γ i (loc (label o)) .receive = true) :
    AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S [(i, Commit.takeOne (R := R) o)]
        (Function.update Γ i (fun n f => Γ i n f || learned label carries (Commit.takeOne (R := R) o) n f))
        (fire S (Commit.takeOne (R := R) o)) ∧
      (∀ x ∈ [(i, Commit.takeOne (R := R) o)], x.1 ≠ owner) ∧
      restrict label loc A (fire S (Commit.takeOne (R := R) o)) = ∅ := by
  refine ⟨.cons ⟨⟨by simpa [Commit.takeOne] using inS, by simp [Commit.takeOne], by simp [Commit.takeOne],
      by simp [Commit.takeOne], by simp [Commit.takeOne]⟩,
    ⟨?_, by simp [Commit.takeOne], by simp [Commit.takeOne], by simp [Commit.takeOne]⟩, ?_, rfl, rfl⟩ (.nil _ _),
    by simpa using notOwner, ?_⟩
  · intro p taken
    simp only [Commit.takeOne, Finset.mem_singleton] at taken
    subst taken
    exact held
  · intro p made
    simp [Commit.takeOne] at made
  · ext p
    simp only [mem_restrict, mem_fire, Commit.takeOne, Finset.mem_singleton, Finset.notMem_empty,
      iff_false, not_and]
    rintro (⟨inS', notO⟩ | impossible) atA
    · have : p ∈ restrict label loc A S := mem_restrict.mpr ⟨inS', atA⟩
      rw [only, Finset.mem_singleton] at this
      exact notO this
    · simp at impossible

end Necessity

/-! ## The kernel as the owner of its rule region -/

section Kernel

variable {label : O → R} {loc : R → N} {carries : R → Rights N}

/-- **The kernel's universal reads over its rule region stay true across the users' runs** when
no user holds or receives `send` there: admission's freshness check and promotion's reads over all
rules need no validation against users. -/
theorem kernel_reads_stable {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (h : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {kernel : I} (users : ∀ x ∈ run, x.1 ≠ kernel) {rules : N → Bool}
    (sole : ∀ n, rules n = true → ¬ OthersAuthority label carries Γ S kernel n .send)
    {P : Finset O → Prop} (antitone : DownwardClosed P) (holds : P (restrict label loc rules S)) :
    P (restrict label loc rules S') :=
  owned_antitone_stable h users sole antitone holds

end Kernel

namespace Controls

/-- Labels are numbers; rule region: even labels. -/
def evenRules : PredicateQuery ℕ ℕ := ⟨fun l => l % 2 == 0, ∅⟩

/-- An admission: check that no rule is there yet, and make one. -/
def admission (o : ℕ) : Commit ℕ ℕ := ⟨∅, ∅, {o}, [evenRules]⟩

theorem admission_enabled_empty (o : ℕ) : Enabled id (∅ : Finset ℕ) (admission o) :=
  ⟨by simp [admission], by simp [admission], by simp [admission], by simp [admission], by
    intro read member
    simp only [admission, List.mem_singleton] at member
    subst member
    decide⟩

/-- **The kernel's own concurrent admissions skew.** Two admissions are each enabled at the same
store, and the second is not enabled after the first: run concurrently without validation, both
would publish. -/
theorem kernel_self_skew :
    Enabled id (∅ : Finset ℕ) (admission 2) ∧ Enabled id (∅ : Finset ℕ) (admission 4) ∧
      ¬ Executable id (∅ : Finset ℕ) [admission 2, admission 4] := by
  refine ⟨admission_enabled_empty 2, admission_enabled_empty 4, ?_⟩
  intro executable
  rw [executable_cons_iff] at executable
  obtain ⟨-, after⟩ := executable
  rw [executable_cons_iff] at after
  have := after.1.queries_hold evenRules (by simp [admission])
  revert this
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions
