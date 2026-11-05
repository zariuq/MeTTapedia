import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

/-!
# Authority by possession of space names

A client possesses a space name when its terms, read through the shared store, distinguish that
name from others. Formally (`Indistinguishable`): names `a` and `b` are indistinguishable for
terms `K` under a store when exchanging `a` and `b` in any solution's reading of `K` gives the
reading of `K` in another solution. This is support in the sense of nominal sets, relative to the
store; it covers the names written in the terms and the names their variables are bound to
(`resolved_name_possessed`), and it ignores names the store binds only to variables unrelated to
`K` (`Controls.unrelated_binding_gives_no_name`).

## What is proved

* **Every effect is at a possessed name** (`resolved_name_possessed`, `footprint_possessed`):
  under the resolved-location law a space position resolves only to a name the rule's terms
  possess. Hence a client with no name for `n` takes, reads and makes nothing at `n`, checks
  nothing there, and its validity does not depend on the occurrences at `n`
  (`no_name_no_effect`, `no_name_no_observation`).
* **Possession grows only by reading or by creation.** A step adds to the store only equations
  between its own ports and tells and the labels of the occurrences it selected; whatever the
  rule's terms together with those labels could not tell apart before, they cannot tell apart
  after (`indistinguishable_after_step`, `possession_after_step`). A ground term possesses the
  names written in it (`ground_term_possessed`).
* **Reach** (`Reach`) is the least set of names containing what the client's terms possess
  together with the labels of present occurrences at names already reached: the names it could
  come to possess by reading. Every effect of a located step lies in the client's reach
  (`footprint_reached`, `effects_in_reach`). Reach grows only by reading or creation: after a
  located step, or a whole run, of rules whose terms the client holds, the client reaches only
  names it reached before (`reach_after_step`, `reach_after_run`). Another party reaches after the
  step only what it reached jointly with the stepping client (`other_reach_after_step`): a
  client learns a name from another client's step only through terms they share
  (`Controls.shared_variable_passes_name`).
* **Creation.** A name that no term of `K` and no equation of the store mentions is possessed by
  nobody (`indistinguishable_of_invariant`), so a freshly created name is possessed only by the
  rule that writes it.

## Controls (`Controls`)

* Negative: a client whose terms name only space 1 has no name for space 7
  (`board_client_has_no_name_for_seven`); its resolved step leaves the occurrence at 7 in place
  (`board_client_cannot_affect_seven`), and its rule taking at a variable space is refused by
  the law (`use_before_read_refused`).
* Positive: after reading a capability message at space 1, the same variable resolves to 7, the
  client possesses 7 (`read_gives_name`), and the take at 7 is a located step
  (`use_after_read_steps`). Passing `n` in a message extends reach.
* The store is a channel: a client sharing a variable with another learns the name the other
  binds it to (`shared_variable_passes_name`); a binding of an unrelated variable gives nothing
  (`unrelated_binding_gives_no_name`).
* Reach with and without a capability message: `NamedSpacesControls` (`message_gives_reach`,
  `no_message_no_reach`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uN uO

section Possession

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq N] [DecidableEq O]
  {A : SubstitutionAction T S} {sts : SpaceTerms A N}

/-- Exchanging two space names inside terms and inside substitutions. -/
structure NameSwap (sts : SpaceTerms A N) where
  swap : N → N → T → T
  E_swap : ∀ a b {t u : T}, A.E t u → A.E (swap a b t) (swap a b u)
  swap_name : ∀ a b k, swap a b (sts.name k) = sts.name (Equiv.swap a b k)
  swapS : N → N → S → S
  apply_swap : ∀ a b σ t, swap a b (A.apply σ t) = A.apply (swapS a b σ) (swap a b t)

variable (ns : NameSwap sts)

/-- Names `a` and `b` are **indistinguishable** for the terms `K` under the store: exchanging
them in any solution's reading of `K` gives the reading of `K` in another solution. -/
def Indistinguishable (store : EquationStore T) (K : Set T) (a b : N) : Prop :=
  ∀ σ, A.Models σ store →
    ∃ τ, A.Models τ store ∧ ∀ t ∈ K, A.E (A.apply τ t) (ns.swap a b (A.apply σ t))

/-- The terms `K` have **no name** for `n` under the store. -/
def NoNameFor (store : EquationStore T) (K : Set T) (n : N) : Prop :=
  ∃ m, m ≠ n ∧ Indistinguishable ns store K n m

/-- The terms `K` **possess** `n` under the store. -/
def Possesses (store : EquationStore T) (K : Set T) (n : N) : Prop :=
  ¬ NoNameFor ns store K n

variable {ns}

omit [DecidableEq O] in
theorem Indistinguishable.mono {store : EquationStore T} {K K' : Set T} {a b : N}
    (fewer : K' ⊆ K) (ind : Indistinguishable ns store K a b) :
    Indistinguishable ns store K' a b := by
  intro σ solved
  obtain ⟨τ, solvedτ, same⟩ := ind σ solved
  exact ⟨τ, solvedτ, fun t member => same t (fewer member)⟩

omit [DecidableEq O] in
/-- **A resolved space is never exchanged**: if the store resolves a term of `K` to `k`, every
pair of names indistinguishable for `K` avoids `k`. -/
theorem resolved_not_exchanged {store : EquationStore T} (consistent : A.Consistent store)
    {K : Set T} {a b : N} (ind : Indistinguishable ns store K a b) {s : T} (member : s ∈ K)
    {k : N} (resolved : ResolvesTo sts store s k) : Equiv.swap a b k = k := by
  obtain ⟨σ, solved⟩ := consistent
  obtain ⟨τ, solvedτ, same⟩ := ind σ solved
  have exchanged : A.E (ns.swap a b (A.apply σ s)) (sts.name (Equiv.swap a b k)) := by
    rw [← ns.swap_name]
    exact ns.E_swap a b (resolved σ solved)
  have both : A.E (sts.name (Equiv.swap a b k)) (sts.name k) :=
    A.equivalence.trans (A.equivalence.symm exchanged)
      (A.equivalence.trans (A.equivalence.symm (same s member)) (resolved τ solvedτ))
  exact (sts.E_name _ _).mp both

omit [DecidableEq O] in
/-- **A resolved name is possessed** by every term list containing the resolved term. -/
theorem resolved_name_possessed {store : EquationStore T} (consistent : A.Consistent store)
    {K : Set T} {s : T} (member : s ∈ K) {n : N} (resolved : ResolvesTo sts store s n) :
    Possesses ns store K n := by
  rintro ⟨m, different, ind⟩
  have fixed := resolved_not_exchanged consistent ind member resolved
  rw [Equiv.swap_apply_left] at fixed
  exact different fixed

omit [DecidableEq O] in
/-- A written name is possessed. -/
theorem written_name_possessed {store : EquationStore T} (consistent : A.Consistent store)
    {K : Set T} {n : N} (member : sts.name n ∈ K) : Possesses ns store K n :=
  resolved_name_possessed consistent member (resolvesTo_name store n)

omit [DecidableEq O] in
/-- **A ground term possesses every name it changes under exchange**: a written compound term
such as a capability message possesses the names written in it. -/
theorem ground_term_possessed {store : EquationStore T} (consistent : A.Consistent store)
    {K : Set T} {t : T} (member : t ∈ K) (ground : ∀ σ, A.apply σ t = t) {n : N}
    (moves : ∀ m, m ≠ n → ¬ A.E t (ns.swap n m t)) : Possesses ns store K n := by
  rintro ⟨m, different, ind⟩
  obtain ⟨σ, solved⟩ := consistent
  obtain ⟨τ, _, same⟩ := ind σ solved
  have related := same t member
  rw [ground, ground] at related
  exact moves m different related

/-- **Every space of a valid, resolved step is possessed by the rule's space terms.** -/
theorem footprint_possessed {space payload : O → T} {r : LocatedRule T}
    {before : Configuration T O} {selection : Selection O}
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    {K : Set T} (known : ∀ s ∈ r.spaces, s ∈ K) {n : N}
    (footprint : Footprint sts before.equations r n) : Possesses ns before.equations K n := by
  obtain ⟨s, member, resolved⟩ := footprint
  exact resolved_name_possessed (valid_before_consistent valid) (known s member) resolved

/-- **No name, no effect.** A client whose space terms have no name for `n` takes nothing at
`n`, makes nothing at `n` and checks nothing at `n`. -/
theorem no_name_no_effect {space payload : O → T} {r : LocatedRule T}
    {before after : Configuration T O}
    (step : LocatedStep sts space payload r before after)
    (wellLocated : WellLocated sts space before) {K : Set T} (known : ∀ s ∈ r.spaces, s ∈ K)
    {n : N} (noName : NoNameFor ns before.equations K n) :
    ¬ Footprint sts before.equations r n ∧
      (∀ o ∈ before.present, ResolvesTo sts before.equations (space o) n → o ∈ after.present) ∧
      (∀ o ∈ after.present, ResolvesTo sts before.equations (space o) n → o ∈ before.present) := by
  obtain ⟨resolved, selection, valid, rfl⟩ := step
  have outside : ¬ Footprint sts before.equations r n := fun footprint =>
    footprint_possessed valid known footprint noName
  exact ⟨outside,
    fun o present at_n => frame_survives valid resolved wellLocated present at_n outside,
    fun o present at_n => frame_no_arrival valid resolved present at_n outside⟩

/-- **No name, no observation.** If two configurations with one store differ only in occurrences
at `n`, and the rule's space terms have no name for `n`, a selection is valid in one exactly
when it is valid in the other. -/
theorem no_name_no_observation {space payload : O → T} {r : LocatedRule T}
    {C D : Configuration T O} {selection : Selection O}
    (resolved : Resolved sts C.equations r) (wellC : WellLocated sts space C)
    (wellD : WellLocated sts space D) {K : Set T} (known : ∀ s ∈ r.spaces, s ∈ K) {n : N}
    (noName : NoNameFor ns C.equations K n) (sameStore : C.equations = D.equations)
    (elsewhere : ∀ o, (∃ k, k ≠ n ∧ ResolvesTo sts C.equations (space o) k) →
      (o ∈ C.present ↔ o ∈ D.present))
    (freshC : Disjoint selection.made.toFinset C.present)
    (freshD : Disjoint selection.made.toFinset D.present)
    (consistent : A.Consistent C.equations) :
    selection.Valid A (located sts space payload) (r.toRule sts) C ↔
      selection.Valid A (located sts space payload) (r.toRule sts) D := by
  apply valid_iff_of_agree_on_spaces resolved wellC wellD _ freshC freshD
  refine ⟨sameStore, fun o ⟨k, footprint, at_k⟩ => elsewhere o ⟨k, ?_, at_k⟩⟩
  rintro rfl
  obtain ⟨s, member, resolvedS⟩ := footprint
  exact resolved_name_possessed consistent (known s member) resolvedS noName

private theorem forall₂_imp_mem {α β : Type*} {R R' : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      (∀ a ∈ l, ∀ b ∈ l', R a b → R' a b) → List.Forall₂ R' l l'
  | [], [], .nil, _ => .nil
  | a :: _, b :: _, .cons head rest, imp =>
      .cons (imp a List.mem_cons_self b List.mem_cons_self head)
        (forall₂_imp_mem rest fun x xm y ym => imp x (List.mem_cons_of_mem _ xm) y
          (List.mem_cons_of_mem _ ym))

/-- **A step teaches only what its terms and its selected labels already determined.** If two
names are indistinguishable for `K` before a valid step, where `K` holds the rule's take and
read patterns, both sides of its tells, and the labels of the occurrences it selects, they are
indistinguishable for `K` after the step. -/
theorem indistinguishable_after_step {label : O → T} {rule : RuleInstance T}
    {before : Configuration T O} {selection : Selection O}
    (valid : selection.Valid A label rule before) {K : Set T}
    (ports : ∀ p ∈ rule.take ++ rule.read, p ∈ K)
    (tells : ∀ e ∈ rule.tell, e.1 ∈ K ∧ e.2 ∈ K)
    (labels : ∀ o ∈ selection.taken ++ selection.read, label o ∈ K) {a b : N}
    (ind : Indistinguishable ns before.equations K a b) :
    Indistinguishable ns (selection.result label rule before).equations K a b := by
  intro σ solved
  obtain ⟨beforeσ, takes, reads, tellσ⟩ := Selection.models_problem A valid solved
  obtain ⟨τ, beforeτ, same⟩ := ind σ beforeσ
  have transfer : ∀ {u v : T}, u ∈ K → v ∈ K → A.E (A.apply σ u) (A.apply σ v) →
      A.E (A.apply τ u) (A.apply τ v) := by
    intro u v uK vK related
    exact A.equivalence.trans (same u uK)
      (A.equivalence.trans (ns.E_swap a b related) (A.equivalence.symm (same v vK)))
  have takesτ : List.Forall₂ (fun p o => A.E (A.apply τ p) (A.apply τ (label o)))
      rule.take selection.taken :=
    forall₂_imp_mem takes fun p pm o om related =>
      transfer (ports p (List.mem_append_left _ pm)) (labels o (List.mem_append_left _ om))
        related
  have readsτ : List.Forall₂ (fun p o => A.E (A.apply τ p) (A.apply τ (label o)))
      rule.read selection.read :=
    forall₂_imp_mem reads fun p pm o om related =>
      transfer (ports p (List.mem_append_right _ pm)) (labels o (List.mem_append_right _ om))
        related
  refine ⟨τ, ?_, same⟩
  change A.Models τ (selection.problem label rule before)
  simp only [Selection.problem, SubstitutionAction.models_append]
  refine ⟨⟨⟨beforeτ, (Selection.models_equations_iff A τ label valid.take_length).mpr takesτ⟩,
    (Selection.models_equations_iff A τ label valid.read_length).mpr readsτ⟩, ?_⟩
  intro e member
  exact transfer (tells e member).1 (tells e member).2 (tellσ e member)

/-- **Possession grows only by reading.** What the rule's terms together with the labels the
step selects possess after the step, they possessed before it. -/
theorem possession_after_step {label : O → T} {rule : RuleInstance T}
    {before : Configuration T O} {selection : Selection O}
    (valid : selection.Valid A label rule before) {K : Set T}
    (ports : ∀ p ∈ rule.take ++ rule.read, p ∈ K)
    (tells : ∀ e ∈ rule.tell, e.1 ∈ K ∧ e.2 ∈ K)
    (labels : ∀ o ∈ selection.taken ++ selection.read, label o ∈ K) {n : N}
    (after : Possesses ns (selection.result label rule before).equations K n) :
    Possesses ns before.equations K n := by
  rintro ⟨m, different, ind⟩
  exact after ⟨m, different, indistinguishable_after_step valid ports tells labels ind⟩

omit [DecidableEq O] in
/-- **Names nobody writes are possessed by nobody**: if exchanging `a` and `b` fixes every term
of `K` and both sides of every equation of the store, they are indistinguishable for `K`. -/
theorem indistinguishable_of_invariant {store : EquationStore T} {K : Set T} {a b : N}
    (fixesK : ∀ t ∈ K, ns.swap a b t = t)
    (fixesStore : ∀ e ∈ store, ns.swap a b e.1 = e.1 ∧ ns.swap a b e.2 = e.2) :
    Indistinguishable ns store K a b := by
  intro σ solved
  refine ⟨ns.swapS a b σ, ?_, ?_⟩
  · intro e member
    have related := ns.E_swap a b (solved e member)
    rw [ns.apply_swap, ns.apply_swap, (fixesStore e member).1, (fixesStore e member).2]
      at related
    exact related
  · intro t member
    rw [ns.apply_swap, fixesK t member]
    exact A.equivalence.refl _

omit [DecidableEq O] in
/-- Possession is monotone in the terms: more terms possess more names. -/
theorem Possesses.mono {store : EquationStore T} {K K' : Set T} (more : K ⊆ K') {n : N}
    (possessed : Possesses ns store K n) : Possesses ns store K' n := by
  rintro ⟨m, different, ind⟩
  exact possessed ⟨m, different, ind.mono more⟩

/-! ### Reach: possession closed under reading at reached spaces -/

variable (sts) in
/-- The labels of present occurrences at names satisfying `R`. -/
def labelsAt (store : EquationStore T) (space label : O → T) (present : Finset O)
    (R : N → Prop) : Set T :=
  {t | ∃ o ∈ present, ∃ k, R k ∧ ResolvesTo sts store (space o) k ∧ t = label o}

omit [DecidableEq N] [DecidableEq O] in
theorem labelsAt_mono {store : EquationStore T} {space label : O → T} {present : Finset O}
    {R R' : N → Prop} (more : ∀ k, R k → R' k) :
    labelsAt sts store space label present R ⊆ labelsAt sts store space label present R' := by
  rintro t ⟨o, present, k, inR, at_k, rfl⟩
  exact ⟨o, present, k, more k inR, at_k, rfl⟩

variable (ns) in
/-- **Reach** of the terms `K`: the least set of names containing every name possessed by `K`
together with the labels of the present occurrences at names already reached. -/
def Reach (store : EquationStore T) (space label : O → T) (present : Finset O) (K : Set T)
    (n : N) : Prop :=
  ∀ R : N → Prop,
    (∀ m, Possesses ns store (K ∪ labelsAt sts store space label present R) m → R m) → R n

section ReachLaws

variable {store : EquationStore T} {space label : O → T} {present : Finset O} {K : Set T}

omit [DecidableEq O] in
theorem Reach.of_possesses {n : N} (possessed : Possesses ns store K n) :
    Reach ns store space label present K n :=
  fun _ closed => closed n (possessed.mono Set.subset_union_left)

omit [DecidableEq O] in
/-- Reach is closed: what `K` and the labels at reached names possess is reached. -/
theorem Reach.closed {m : N}
    (possessed : Possesses ns store
      (K ∪ labelsAt sts store space label present (Reach ns store space label present K)) m) :
    Reach ns store space label present K m := by
  intro R closedR
  apply closedR m
  refine possessed.mono (Set.union_subset_union_right K (labelsAt_mono ?_))
  intro k reached
  exact reached R closedR

omit [DecidableEq O] in
/-- Reach grows with the terms. -/
theorem Reach.mono {K' : Set T} (more : K ⊆ K') {n : N}
    (reached : Reach ns store space label present K n) :
    Reach ns store space label present K' n := by
  intro R closedR
  apply reached R
  intro m possessed
  exact closedR m (possessed.mono (Set.union_subset_union_left _ more))

end ReachLaws

/-- The terms of a located rule a client must hold to fire it: its ports as terms, both sides
of its tells, its produced terms and its space positions. -/
structure HoldsRule (r : LocatedRule T) (K : Set T) : Prop where
  ports : ∀ p ∈ (r.toRule sts).take ++ (r.toRule sts).read, p ∈ K
  tells : ∀ e ∈ r.tell, e.1 ∈ K ∧ e.2 ∈ K
  produce : ∀ p ∈ (r.toRule sts).produce, p ∈ K
  spaces : ∀ s ∈ r.spaces, s ∈ K

/-- **Every effect of a client's step lies in its reach.** -/
theorem footprint_reached {space payload : O → T} {r : LocatedRule T}
    {before : Configuration T O} {selection : Selection O}
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    {K : Set T} (holds : HoldsRule (sts := sts) r K) {n : N}
    (footprint : Footprint sts before.equations r n) :
    Reach ns before.equations space (located sts space payload) before.present K n :=
  Reach.of_possesses (footprint_possessed valid holds.spaces footprint)

/-- **Reach grows only by reading or creation.** After a located step of a rule whose terms lie
in `K`, every name `K` reaches was reached by `K` before the step. New names enter only as
terms of `K`, that is by writing them in a rule instance (creation, or a name the client was
given). The same theorem with another party's terms added to `K` bounds what that party can
learn from the step: only names reached jointly with the stepping rule. -/
theorem reach_after_step {space payload : O → T} {r : LocatedRule T}
    {before after : Configuration T O}
    (step : LocatedStep sts space payload r before after)
    (wellLocated : WellLocated sts space before) {K : Set T} (holds : HoldsRule (sts := sts) r K)
    {n : N} (reached : Reach ns after.equations space (located sts space payload) after.present K n) :
    Reach ns before.equations space (located sts space payload) before.present K n := by
  obtain ⟨resolved, selection, valid, rfl⟩ := step
  set label := located sts space payload
  set R := Reach ns before.equations space label before.present K
  set result := selection.result label (r.toRule sts) before
  have consistentAfter : A.Consistent result.equations := valid.consistent
  -- labels at reached names after the step are labels before the step, or produced terms
  have labelsAfter : labelsAt sts result.equations space label result.present R ⊆
      K ∪ labelsAt sts before.equations space label before.present R := by
    rintro t ⟨o, presentAfter, k, inR, at_k, rfl⟩
    rcases mem_fire.mp presentAfter with ⟨old, _⟩ | madeMember
    · obtain ⟨k', at_k'⟩ := wellLocated o old
      have names : k = k' :=
        ResolvesTo.unique consistentAfter at_k (ResolvesTo.of_refines valid.refines at_k')
      subst names
      exact Or.inr ⟨o, old, k, inR, at_k', rfl⟩
    · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
      left
      apply holds.produce
      rw [← valid.outputs]
      exact List.mem_map.mpr ⟨o, made, rfl⟩
  -- the selected labels lie at reached names
  have selectedLabels : ∀ o ∈ selection.taken ++ selection.read,
      label o ∈ labelsAt sts before.equations space label before.present R := by
    intro o member
    rcases List.mem_append.mp member with taken | read
    · obtain ⟨port, portMember, k, portAt, at_k⟩ :=
        taken_at_port_space valid resolved wellLocated taken
      exact ⟨o, valid.occurrences.taken_subset (by simpa [Selection.commit] using taken), k,
        footprint_reached valid holds ⟨port.1, take_space_mem portMember, portAt⟩, at_k, rfl⟩
    · obtain ⟨port, portMember, k, portAt, at_k⟩ :=
        read_at_port_space valid resolved wellLocated read
      exact ⟨o, valid.occurrences.kept_subset (by simpa [Selection.commit] using read), k,
        footprint_reached valid holds ⟨port.1, read_space_mem portMember, portAt⟩, at_k, rfl⟩
  -- R is closed under the operator of the configuration after the step
  apply reached R
  intro m possessedAfter
  have widened : Possesses ns result.equations
      (K ∪ labelsAt sts before.equations space label before.present R) m :=
    possessedAfter.mono (Set.union_subset Set.subset_union_left labelsAfter)
  have possessedBefore := possession_after_step valid
    (fun p member => Or.inl (holds.ports p member))
    (fun e member => ⟨Or.inl (holds.tells e member).1, Or.inl (holds.tells e member).2⟩)
    (fun o member => Or.inr (selectedLabels o member)) widened
  exact Reach.closed possessedBefore

/-- **Only connectivity begets connectivity**: what another party with terms `K'` reaches after
a client's step, it reached together with the client before. -/
theorem other_reach_after_step {space payload : O → T} {r : LocatedRule T}
    {before after : Configuration T O}
    (step : LocatedStep sts space payload r before after)
    (wellLocated : WellLocated sts space before) {K K' : Set T} (holds : HoldsRule (sts := sts) r K)
    {n : N}
    (reached : Reach ns after.equations space (located sts space payload) after.present K' n) :
    Reach ns before.equations space (located sts space payload) before.present (K' ∪ K) n := by
  have holdsJoint : HoldsRule (sts := sts) r (K' ∪ K) :=
    ⟨fun p member => Or.inr (holds.ports p member),
      fun e member => ⟨Or.inr (holds.tells e member).1, Or.inr (holds.tells e member).2⟩,
      fun p member => Or.inr (holds.produce p member),
      fun s member => Or.inr (holds.spaces s member)⟩
  exact reach_after_step step wellLocated holdsJoint (reached.mono Set.subset_union_left)

/-- **Every effect of a client's located step lies in its reach**: every taken, read and made
occurrence is at a name the client reaches, and every name its checks look at is reached. -/
theorem effects_in_reach {space payload : O → T} {r : LocatedRule T}
    {before : Configuration T O} {selection : Selection O}
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) before)
    (resolved : Resolved sts before.equations r) (wellLocated : WellLocated sts space before)
    {K : Set T} (holds : HoldsRule (sts := sts) r K) :
    (∀ o ∈ selection.taken ++ selection.read ++ selection.made, ∃ k,
      Reach ns before.equations space (located sts space payload) before.present K k ∧
        ResolvesTo sts before.equations (space o) k) ∧
      ∀ k, Footprint sts before.equations r k →
        Reach ns before.equations space (located sts space payload) before.present K k := by
  refine ⟨fun o member => ?_, fun k footprint => footprint_reached valid holds footprint⟩
  rcases List.mem_append.mp member with takenOrRead | made
  · rcases List.mem_append.mp takenOrRead with taken | read
    · obtain ⟨port, portMember, k, portAt, at_k⟩ :=
        taken_at_port_space valid resolved wellLocated taken
      exact ⟨k, footprint_reached valid holds ⟨port.1, take_space_mem portMember, portAt⟩, at_k⟩
    · obtain ⟨port, portMember, k, portAt, at_k⟩ :=
        read_at_port_space valid resolved wellLocated read
      exact ⟨k, footprint_reached valid holds ⟨port.1, read_space_mem portMember, portAt⟩, at_k⟩
  · obtain ⟨port, portMember, same, k, portAt⟩ := made_at_port_space valid resolved made
    exact ⟨k, footprint_reached valid holds ⟨port.1, produce_space_mem portMember, portAt⟩,
      same ▸ portAt⟩

variable (sts) in
/-- A run of located steps. -/
inductive LocatedRun (space payload : O → T) :
    Configuration T O → List (LocatedRule T) → Configuration T O → Prop
  | nil (C : Configuration T O) : LocatedRun space payload C [] C
  | cons {C D E : Configuration T O} {r : LocatedRule T} {rest : List (LocatedRule T)} :
      LocatedStep sts space payload r C D → LocatedRun space payload D rest E →
        LocatedRun space payload C (r :: rest) E

/-- **Reach over a run**: along any run of rules whose terms lie in `K`, from a well-located
configuration, what `K` reaches at the end it reached at the start. -/
theorem reach_after_run {space payload : O → T} {C E : Configuration T O}
    {rules : List (LocatedRule T)} (run : LocatedRun sts space payload C rules E)
    (wellLocated : WellLocated sts space C) {K : Set T}
    (holds : ∀ r ∈ rules, HoldsRule (sts := sts) r K) {n : N}
    (reached : Reach ns E.equations space (located sts space payload) E.present K n) :
    Reach ns C.equations space (located sts space payload) C.present K n := by
  induction run with
  | nil => exact reached
  | cons step _ ih =>
      exact reach_after_step step wellLocated (holds _ List.mem_cons_self)
        (ih (step.wellLocated wellLocated) (fun r member => holds r (List.mem_cons_of_mem _ member))
          reached)

end Possession

namespace Controls

/-- Exchange two names in a term. -/
def Tm.swap (a b : Nat) : Tm → Tm
  | .var i => .var i
  | .nm n => .nm (Equiv.swap a b n)
  | .sym s => .sym s
  | .app f x => .app (f.swap a b) (x.swap a b)
  | .loc s p => .loc (s.swap a b) (p.swap a b)

theorem Tm.swap_subst (a b : Nat) (σ : Nat → Tm) (t : Tm) :
    (t.subst σ).swap a b = (t.swap a b).subst fun i => (σ i).swap a b := by
  induction t with
  | var => rfl
  | nm => rfl
  | sym => rfl
  | app f x ihf ihx => simp [Tm.subst, Tm.swap, ihf, ihx]
  | loc s p ihs ihp => simp [Tm.subst, Tm.swap, ihs, ihp]

/-- The first-order profile exchanges names. -/
def names : NameSwap spaces where
  swap := Tm.swap
  E_swap a b {_ _} same := congrArg (Tm.swap a b) same
  swap_name _ _ _ := rfl
  swapS a b σ i := (σ i).swap a b
  apply_swap a b σ t := Tm.swap_subst a b σ t

/-- A board at space 1 holds a capability for space 7; space 7 holds a secret. -/
def boardSpace : Nat → Tm := fun o => if o = 0 then .nm 1 else .nm 7

def boardPayload : Nat → Tm := fun o =>
  if o = 0 then .app (.sym "cap") (.nm 7) else .sym "secret"

def board : Configuration Tm Nat := ⟨[], {0, 1}⟩

/-- Read a capability from the board, binding variable 0. -/
def readCap : LocatedRule Tm := ⟨[], [(.nm 1, .app (.sym "cap") (.var 0))], [], [], []⟩

/-- Take the secret at the space variable 0 denotes. -/
def useCap : LocatedRule Tm := ⟨[(.var 0, .sym "secret")], [], [], [], []⟩

/-- The board client's terms. -/
def clientTerms : Set Tm := {.nm 1, .app (.sym "cap") (.var 0), .var 0, .sym "secret"}

theorem board_wellLocated : WellLocated spaces boardSpace board := by
  intro o present
  simp only [board, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl
  · exact ⟨1, resolvesTo_name _ 1⟩
  · exact ⟨7, resolvesTo_name _ 7⟩

/-- **Negative control**: before reading, the client has no name for space 7. -/
theorem board_client_has_no_name_for_seven : NoNameFor names board.equations clientTerms 7 := by
  refine ⟨8, by decide, indistinguishable_of_invariant ?_ ?_⟩
  · intro t member
    simp only [clientTerms, Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  · intro e member
    simp [board] at member

/-- Grab a letter on the board. -/
def grabOnBoard : LocatedRule Tm := ⟨[(.nm 1, .var 3)], [], [], [], []⟩

/-- **A client without a name for 7 cannot affect 7**: any located step of a rule whose space
terms are among the client's leaves the secret in place. -/
theorem board_client_cannot_affect_seven {after : Configuration Tm Nat}
    (step : LocatedStep spaces boardSpace boardPayload grabOnBoard board after) :
    1 ∈ after.present := by
  have known : ∀ s ∈ grabOnBoard.spaces, s ∈ clientTerms := by
    intro s member
    simp [LocatedRule.spaces, grabOnBoard] at member
    subst member
    simp [clientTerms]
  exact (no_name_no_effect step board_wellLocated known board_client_has_no_name_for_seven).2.1 1
    (by simp [board]) (resolvesTo_name _ 7)

/-- The law refuses to use the capability variable before it is read. -/
theorem use_before_read_refused : ¬ Resolved spaces board.equations useCap := by
  intro resolved
  obtain ⟨n, at_n⟩ := resolved (.var 0) (by simp [LocatedRule.spaces, useCap])
  have := at_n (fun _ => .nm (n + 1)) (by simp [board])
  simp [spaces, Tm.subst] at this

def readFirst : Selection Nat := ⟨[], [0], []⟩

theorem readCap_valid :
    readFirst.Valid action (located spaces boardSpace boardPayload) (readCap.toRule spaces) board := by
  refine ⟨by simp [readFirst], by simp [readFirst], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, readFirst], by simp [Selection.commit, readFirst, board],
      by simp [Selection.commit, readFirst], by simp [Selection.commit, readFirst],
      by simp [Selection.commit]⟩,
    ⟨fun _ => .nm 7, ?_⟩, by simp [readCap, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, readCap,
    LocatedRule.toRule, readFirst, board, place, located, spaces, boardSpace, boardPayload,
    Tm.subst]

/-- The board after reading the capability. -/
def afterRead : Configuration Tm Nat :=
  readFirst.result (located spaces boardSpace boardPayload) (readCap.toRule spaces) board

theorem afterRead_resolves : ResolvesTo spaces afterRead.equations (.var 0) 7 := by
  intro σ solved
  simp [afterRead, SubstitutionAction.Solves, Selection.result, Selection.problem,
    Selection.equations, readCap, LocatedRule.toRule, readFirst, board, place, located, spaces,
    boardSpace, boardPayload, Tm.subst] at solved
  simpa [spaces, Tm.subst] using solved

/-- **Positive control**: reading the message gives the name. -/
theorem read_gives_name : Possesses names afterRead.equations clientTerms 7 := by
  apply resolved_name_possessed _ (by simp [clientTerms]) afterRead_resolves
  obtain ⟨σ, solved⟩ := readCap_valid.consistent
  exact ⟨σ, solved⟩

def takeSecret : Selection Nat := ⟨[1], [], []⟩

/-- **Passing a name in a message extends reach**: after reading, taking at 7 is a located step. -/
theorem use_after_read_steps :
    LocatedStep spaces boardSpace boardPayload useCap afterRead
      (takeSecret.result (located spaces boardSpace boardPayload) (useCap.toRule spaces)
        afterRead) := by
  refine ⟨?_, takeSecret, ?_, rfl⟩
  · intro s member
    simp [LocatedRule.spaces, useCap] at member
    subst member
    exact ⟨7, afterRead_resolves⟩
  · refine ⟨by simp [takeSecret], by simp [takeSecret], rfl, rfl, rfl,
      ⟨?_, by simp [Selection.commit, takeSecret], by simp [Selection.commit, takeSecret],
        by simp [Selection.commit, takeSecret], by simp [Selection.commit]⟩,
      ⟨fun _ => .nm 7, ?_⟩, by simp [useCap, LocatedRule.toRule]⟩
    · intro o member
      simp only [Selection.commit, takeSecret, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.mem_singleton] at member
      subst member
      simp [afterRead, Selection.result, fire, Selection.commit, readFirst, board]
    · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, useCap,
        LocatedRule.toRule, takeSecret, afterRead, Selection.result, readCap, readFirst, board,
        place, located, spaces, boardSpace, boardPayload, Tm.subst]

/-- **The store is a channel**: a client holding only variable 5 learns name 7 when another
client, sharing that variable, binds it. -/
theorem shared_variable_passes_name :
    NoNameFor names [] {.var 5} 7 ∧ Possesses names [(.var 5, .nm 7)] {.var 5} 7 := by
  constructor
  · refine ⟨8, by decide, indistinguishable_of_invariant ?_ ?_⟩
    · intro t member
      simp only [Set.mem_singleton_iff] at member
      subst member
      rfl
    · simp
  · refine resolved_name_possessed (s := .var 5) ⟨fun _ => .nm 7, ?_⟩ (by simp) ?_
    · simp [SubstitutionAction.Solves, Tm.subst]
    · intro σ solved
      simpa [SubstitutionAction.Solves, spaces, Tm.subst] using solved

/-- A binding of an unrelated variable gives no name. -/
theorem unrelated_binding_gives_no_name : NoNameFor names [(.var 6, .nm 7)] {.var 5} 7 := by
  refine ⟨8, by decide, ?_⟩
  intro σ solved
  refine ⟨fun i => if i = 5 then (σ 5).swap 7 8 else σ i, ?_, ?_⟩
  · intro e member
    simp only [List.mem_singleton] at member
    subst member
    have := solved _ List.mem_cons_self
    simpa [SubstitutionAction.Solves, Tm.subst] using this
  · intro t member
    simp only [Set.mem_singleton_iff] at member
    subst member
    simp [Tm.subst, names]

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces
