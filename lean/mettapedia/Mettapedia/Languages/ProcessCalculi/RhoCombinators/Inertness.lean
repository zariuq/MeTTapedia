/-
# Inversion by components, inertness, and linearity

The positive results about this calculus are reachability statements: a trace
exists.  A correctness statement needs the other half — that the *unintended*
traces do not exist.  Proving an absence requires inverting reduction, and in a
system whose congruence is multiset equality of parallel components the
inversion is: *look at the components*.

`hasMatchingPair_of_step` is that inversion.  Every rule consumes one atom that
listens at some subject together with one or more atoms that speak at congruent
subjects, and all of them survive into the component multiset; `parLeft` only
adds components and `congruent` preserves them.  So a term whose components
contain no listener/speaker pair at congruent subjects admits no step at all,
however it is rearranged.

The matching relation deliberately *over*-approximates the redexes: it pairs any
listener with any speaker, ignoring that `ev` reacts with `mm` but not with `qq`,
and that a constructor needs *all* of its subjects supplied before it fires.  An
over-approximation is the right side to err on for a negative result — absence
of an over-approximate pair implies absence of a real redex.

Two consequences are developed here.

`gate_inert` says the three-atom gate, the load-bearing gadget of the encoding,
sits still until its trigger arrives.  Its side conditions are freshness
conditions, and `gate_inert_of_seeds` discharges them from seed allocation, so
they are conditions a compiler meets by counting rather than hypotheses left
standing.

`Linear` is the linearity condition the encoding needs: every name occupies at
most one listening position and at most one speaking position in the whole soup.
Stated as nodup-ness of the subject multisets it is checkable by construction,
and `listeningOccurrences_le_one` converts it into the at-most-one-atom form.

What is **not** proved here: confluence or determinism of an encoded term.
Linearity is the hypothesis such a result would need, and inversion is the tool
it would use, but the statement that a linear soup has at most one reduction up
to congruence is not established below and is not claimed.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Gate
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Seeds

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Listening and speaking positions -/

/-- The subjects an atom listens at.  The routers listen at one subject; a
constructor listens at one subject per child it assembles, and fires only when
every one of them has been supplied. -/
def listenSubjects : Comb → List Comb
  | dd a _ _ => [a]
  | kk a => [a]
  | fw a _ => [a]
  | bl a _ => [a]
  | br a _ => [a]
  | sy a _ _ => [a]
  | ev a => [a]
  | consPar a b _ => [a, b]
  | consMsg a b _ => [a, b]
  | consDup a b c _ => [a, b, c]
  | consSyn a b c _ => [a, b, c]
  | _ => []

/-- The subjects an atom speaks at.  A message offers its payload; the storage
combinator offers the code it holds. -/
def speakSubjects : Comb → List Comb
  | mm a _ => [a]
  | qq a _ => [a]
  | _ => []

/-- A component multiset contains a matching pair when some component listens
and some component speaks at name-equivalent subjects. -/
def HasMatchingPair (soup : Multiset Comb) : Prop :=
  ∃ listener ∈ soup, ∃ speaker ∈ soup,
    ∃ heard ∈ listenSubjects listener, ∃ spoken ∈ speakSubjects speaker,
      Cong heard spoken

theorem hasMatchingPair_of_mem {soup : Multiset Comb} (listener speaker : Comb)
    {heard spoken : Comb} (hl : listener ∈ soup) (hs : speaker ∈ soup)
    (hheard : heard ∈ listenSubjects listener)
    (hspoken : spoken ∈ speakSubjects speaker)
    (hcong : Cong heard spoken) : HasMatchingPair soup :=
  ⟨listener, hl, speaker, hs, heard, hheard, spoken, hspoken, hcong⟩

/-- The shape a two-participant rule has: an atom listening beside an atom
speaking.  Stating it against the term rather than the multiset lets the
subjects be read off the goal, so each rule case is discharged uniformly. -/
theorem hasMatchingPair_beside {listener speaker heard spoken : Comb}
    (hlist : components listener = {listener})
    (hspeak : components speaker = {speaker})
    (hheard : heard ∈ listenSubjects listener)
    (hspoken : spoken ∈ speakSubjects speaker)
    (hcong : Cong heard spoken) :
    HasMatchingPair (components (par listener speaker)) := by
  refine hasMatchingPair_of_mem listener speaker ?_ ?_ hheard hspoken hcong
  · simp only [components, hlist, hspeak, Multiset.mem_add, Multiset.mem_singleton]
    exact Or.inl trivial
  · simp only [components, hlist, hspeak, Multiset.mem_add, Multiset.mem_singleton]
    exact Or.inr trivial

/-- The shape a constructor rule has: a listener beside the first of several
speakers.  One matched subject is all a negative result needs, so the remaining
speakers are carried along untouched. -/
theorem hasMatchingPair_besideFirst {listener speaker rest heard spoken : Comb}
    (hlist : components listener = {listener})
    (hspeak : components speaker = {speaker})
    (hheard : heard ∈ listenSubjects listener)
    (hspoken : spoken ∈ speakSubjects speaker)
    (hcong : Cong heard spoken) :
    HasMatchingPair (components (par listener (par speaker rest))) := by
  refine hasMatchingPair_of_mem listener speaker ?_ ?_ hheard hspoken hcong
  · simp only [components, hlist, hspeak, Multiset.mem_add, Multiset.mem_singleton]
    exact Or.inl trivial
  · simp only [components, hlist, hspeak, Multiset.mem_add, Multiset.mem_singleton]
    exact Or.inr (Or.inl trivial)

/-! ## Inversion -/

/-- Inversion for the constructor-free calculus. -/
theorem hasMatchingPair_of_stepMinus {t t' : Comb} (h : StepMinus Cong t t') :
    HasMatchingPair (components t) := by
  induction h with
  | duplicate b c v hc =>
      exact hasMatchingPair_beside rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | discard v hc =>
      exact hasMatchingPair_beside rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | forward b v hc =>
      exact hasMatchingPair_beside rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | bindOut b v hc =>
      exact hasMatchingPair_beside rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | bindIn b v hc =>
      exact hasMatchingPair_beside rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | synchronise b c v hc =>
      exact hasMatchingPair_beside rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | opening p hc =>
      exact hasMatchingPair_beside rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | release b p hc =>
      exact hasMatchingPair_beside rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | parLeft r _ ih =>
      obtain ⟨listener, hl, speaker, hs, heard, hheard, spoken, hspoken, hcong⟩ := ih
      refine hasMatchingPair_of_mem listener speaker ?_ ?_ hheard hspoken hcong
      · simp only [components, Multiset.mem_add]; exact Or.inl hl
      · simp only [components, Multiset.mem_add]; exact Or.inl hs
  | congruent hcong _ _ ih =>
      rw [cong_components hcong]; exact ih

/-- **Inversion by components.**  A step can only occur when the component
multiset already contains a listener and a speaker at name-equivalent subjects.
Contrapositively: a term with no such pair is inert under every rearrangement,
constructors included. -/
theorem hasMatchingPair_of_step {t t' : Comb} (h : Step Cong t t') :
    HasMatchingPair (components t) := by
  induction h with
  | ofMinus hmin => exact hasMatchingPair_of_stepMinus hmin
  | buildPar c p q hc _ =>
      exact hasMatchingPair_besideFirst rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | buildMsg c u v hc _ =>
      exact hasMatchingPair_besideFirst rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | buildDup e p q r hc _ _ =>
      exact hasMatchingPair_besideFirst rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | buildSyn e p q r hc _ _ =>
      exact hasMatchingPair_besideFirst rfl rfl (List.Mem.head _) (List.Mem.head _) hc
  | parLeft r _ ih =>
      obtain ⟨listener, hl, speaker, hs, heard, hheard, spoken, hspoken, hcong⟩ := ih
      refine hasMatchingPair_of_mem listener speaker ?_ ?_ hheard hspoken hcong
      · simp only [components, Multiset.mem_add]; exact Or.inl hl
      · simp only [components, Multiset.mem_add]; exact Or.inl hs
  | congruent hcong _ _ ih =>
      rw [cong_components hcong]; exact ih

/-- No matching pair means no step, stated the way a correctness proof uses it. -/
theorem no_step_of_not_hasMatchingPair {t : Comb}
    (h : ¬ HasMatchingPair (components t)) : ∀ t', ¬ Step Cong t t' :=
  fun _ hstep => h (hasMatchingPair_of_step hstep)

/-! ## The gate sits still -/

/-- **A gate is inert until its trigger arrives.**  The three atoms of a gate
listen at the trigger and at the run name and speak only at the store name, so
as long as the store name differs from the other two no rearrangement of the
gate exposes a redex — not even using a constructor.  The continuation it
carries is arbitrary: it is held as a name, not as running code, which is
exactly why its size does not matter. -/
theorem gate_inert {trigger store run continuation : Comb}
    (htrigger : ¬ Cong trigger store) (hrun : ¬ Cong run store) :
    ∀ t, ¬ Step Cong (gate trigger store run continuation) t := by
  refine no_step_of_not_hasMatchingPair ?_
  rintro ⟨listener, hl, speaker, hs, heard, hheard, spoken, hspoken, hcong⟩
  simp only [gate, components, Multiset.mem_add, Multiset.mem_singleton] at hl hs
  rcases hs with rfl | rfl | rfl
  · simp [speakSubjects] at hspoken
  · simp only [speakSubjects, List.mem_singleton] at hspoken
    subst hspoken
    rcases hl with rfl | rfl | rfl
    · simp only [listenSubjects, List.mem_singleton] at hheard
      subst hheard; exact htrigger hcong
    · simp [listenSubjects] at hheard
    · simp only [listenSubjects, List.mem_singleton] at hheard
      subst hheard; exact hrun hcong
  · simp [speakSubjects] at hspoken

/-- The freshness side conditions are dischargeable by construction: allocate
the gate's three names at distinct seed positions and inertness follows.  A
compiler meets this condition by counting, with no occurrence check. -/
theorem gate_inert_of_seeds (s continuation : Comb) {wt ws wr : List Bool}
    (hwt : wt ≠ []) (hws : ws ≠ []) (hwr : wr ≠ [])
    (hts : wt ≠ ws) (hrs : wr ≠ ws) :
    ∀ t, ¬ Step Cong
      (gate (seedAt s wt) (seedAt s ws) (seedAt s wr) continuation) t :=
  gate_inert
    (fun h => hts (seedAt_cong_injective s hwt hws h))
    (fun h => hrs (seedAt_cong_injective s hwr hws h))

/-! ## Linearity -/

/-- Every listening position of the whole soup, with multiplicity. -/
def listeningSubjects (t : Comb) : Multiset Comb :=
  (components t).bind fun atom => (listenSubjects atom : Multiset Comb)

/-- Every speaking position of the whole soup, with multiplicity. -/
def speakingSubjects (t : Comb) : Multiset Comb :=
  (components t).bind fun atom => (speakSubjects atom : Multiset Comb)

/-- **Linearity.**  Every name occupies at most one listening position and at
most one speaking position in the soup.  This is the condition an encoding must
meet for its intended trace to be its only trace: a name that two atoms listen
at, or that two atoms speak at, is a point where the reduction could go a way
the encoding did not intend. -/
structure Linear (t : Comb) : Prop where
  listening : (listeningSubjects t).Nodup
  speaking : (speakingSubjects t).Nodup

/-- Linearity in the at-most-one-atom form. -/
theorem listeningOccurrences_le_one {t : Comb} (h : Linear t) (a : Comb) :
    Multiset.count a (listeningSubjects t) ≤ 1 :=
  Multiset.nodup_iff_count_le_one.mp h.listening a

theorem speakingOccurrences_le_one {t : Comb} (h : Linear t) (a : Comb) :
    Multiset.count a (speakingSubjects t) ≤ 1 :=
  Multiset.nodup_iff_count_le_one.mp h.speaking a

/-- Congruence cannot break linearity: it is a property of the components. -/
theorem linear_of_cong {p q : Comb} (hcong : Cong p q) (h : Linear p) : Linear q where
  listening := by
    simpa only [listeningSubjects, ← cong_components hcong] using h.listening
  speaking := by
    simpa only [speakingSubjects, ← cong_components hcong] using h.speaking

/-- A gate is linear exactly when its trigger and run names differ: the store
name is the only speaking position, so the speaking half is unconditional. -/
theorem gate_linear {trigger store run continuation : Comb}
    (h : trigger ≠ run) : Linear (gate trigger store run continuation) where
  listening := by
    simp only [listeningSubjects, gate, components, listenSubjects]
    simp [h]
  speaking := by
    simp only [speakingSubjects, gate, components, speakSubjects]
    simp

/-! ## What linearity buys: the partner at a name is unique -/

/-- Two distinct members of a multiset make a pair inside it. -/
theorem pair_le_of_mem_of_ne {soup : Multiset Comb} {x y : Comb}
    (hx : x ∈ soup) (hy : y ∈ soup) (hne : x ≠ y) :
    ({x, y} : Multiset Comb) ≤ soup := by
  refine Multiset.le_iff_count.mpr fun a => ?_
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  rcases eq_or_ne a x with rfl | hax
  · rw [if_neg hne, if_pos rfl]
    simpa using Multiset.one_le_count_iff_mem.mpr hx
  · rcases eq_or_ne a y with rfl | hay
    · rw [if_pos rfl, if_neg hax]
      simpa using Multiset.one_le_count_iff_mem.mpr hy
    · rw [if_neg hay, if_neg hax]
      simp

/-- **At each name, at most one atom speaks.**  Two components offering a value
at the same subject would put that name twice into the speaking multiset, which
linearity forbids.  This is the half of the paper's linearity lemma that says a
constructed name carries at most one message. -/
theorem speaker_unique_at {t : Comb} (hlin : Linear t) {a s₁ s₂ : Comb}
    (h₁ : s₁ ∈ components t) (h₂ : s₂ ∈ components t)
    (ha₁ : a ∈ speakSubjects s₁) (ha₂ : a ∈ speakSubjects s₂) : s₁ = s₂ := by
  by_contra hne
  obtain ⟨rest, hrest⟩ := Multiset.le_iff_exists_add.mp (pair_le_of_mem_of_ne h₁ h₂ hne)
  have h1 : 1 ≤ Multiset.count a ((speakSubjects s₁ : Multiset Comb)) :=
    Multiset.one_le_count_iff_mem.mpr (Multiset.mem_coe.mpr ha₁)
  have h2 : 1 ≤ Multiset.count a ((speakSubjects s₂ : Multiset Comb)) :=
    Multiset.one_le_count_iff_mem.mpr (Multiset.mem_coe.mpr ha₂)
  have hcount : 2 ≤ Multiset.count a (speakingSubjects t) := by
    rw [speakingSubjects, hrest, Multiset.add_bind]
    simp only [Multiset.insert_eq_cons, Multiset.cons_bind, Multiset.singleton_bind,
      Multiset.count_add]
    omega
  have := speakingOccurrences_le_one hlin a
  omega

/-- **At each name, at most one atom listens.**  This is the half of the paper's
linearity lemma that says a constructed name is the subject of at most one
atom. -/
theorem listener_unique_at {t : Comb} (hlin : Linear t) {a l₁ l₂ : Comb}
    (h₁ : l₁ ∈ components t) (h₂ : l₂ ∈ components t)
    (ha₁ : a ∈ listenSubjects l₁) (ha₂ : a ∈ listenSubjects l₂) : l₁ = l₂ := by
  by_contra hne
  obtain ⟨rest, hrest⟩ := Multiset.le_iff_exists_add.mp (pair_le_of_mem_of_ne h₁ h₂ hne)
  have h1 : 1 ≤ Multiset.count a ((listenSubjects l₁ : Multiset Comb)) :=
    Multiset.one_le_count_iff_mem.mpr (Multiset.mem_coe.mpr ha₁)
  have h2 : 1 ≤ Multiset.count a ((listenSubjects l₂ : Multiset Comb)) :=
    Multiset.one_le_count_iff_mem.mpr (Multiset.mem_coe.mpr ha₂)
  have hcount : 2 ≤ Multiset.count a (listeningSubjects t) := by
    rw [listeningSubjects, hrest, Multiset.add_bind]
    simp only [Multiset.insert_eq_cons, Multiset.cons_bind, Multiset.singleton_bind,
      Multiset.count_add]
    omega
  have := listeningOccurrences_le_one hlin a
  omega

/-- **No choice of partner at a name.**  In a linear soup the two participants
of a candidate redex are determined by the name they meet at.  So the reduction
has no choice to make *at a name*: what remains open is the order in which
independent redexes elsewhere in the soup fire, which is concurrency rather than
ambiguity. -/
theorem participants_unique_at {t : Comb} (hlin : Linear t) {a l₁ l₂ s₁ s₂ : Comb}
    (hl₁ : l₁ ∈ components t) (hl₂ : l₂ ∈ components t)
    (hs₁ : s₁ ∈ components t) (hs₂ : s₂ ∈ components t)
    (hal₁ : a ∈ listenSubjects l₁) (hal₂ : a ∈ listenSubjects l₂)
    (has₁ : a ∈ speakSubjects s₁) (has₂ : a ∈ speakSubjects s₂) :
    l₁ = l₂ ∧ s₁ = s₂ :=
  ⟨listener_unique_at hlin hl₁ hl₂ hal₁ hal₂,
    speaker_unique_at hlin hs₁ hs₂ has₁ has₂⟩

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
