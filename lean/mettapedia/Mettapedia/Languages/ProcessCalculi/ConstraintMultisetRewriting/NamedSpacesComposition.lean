import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesAttenuation

/-!
# Composition by name

Two located firings whose resolved spaces are disjoint touch disjoint occurrence identities: no
identity is taken by both, made by both, or taken by one and read by the other
(`disjoint_spaces_independent`). By the per-identity laws of `Exactness`
(`independent_iff_both_orders`, `fire_comm`) their resources commute, and their absence and count
checks ignore each other's writes (`disjoint_spaces_ignore_writes`). What remains of the
hypotheses of `Core.independently_ready_commute` is information: the joint equations must be
consistent (`disjoint_spaces_commute`).

That hypothesis cannot be dropped. A logic variable shared by two clients is a channel even when
their spaces are disjoint: two readers at spaces 1 and 2 that bind one variable to `a` and to `b`
are each valid and disable each other (`Controls.shared_variable_blocks_commutation`); with
separate variables they commute (`Controls.separate_variables_commute`).

Clients sharing a name need exactly the hypotheses of `independently_ready_commute`. For an owner's
forwarder and a client posting on the shared mailbox name they reduce to distinct identities
(`post_and_forward_commute`). An owner's rule that counts the posts at the shared name is spoiled
by a new post (`Controls.counting_owner_spoiled_by_post`), so that pair runs in one order only.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uN uO

section Composition

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} [DecidableEq O]
  {A : SubstitutionAction T S} {sts : SpaceTerms A N}
  {space payload : O → T}

/-- Two rules have disjoint footprints at a store. -/
def ApartFootprints (store : EquationStore T) (first second : LocatedRule T) : Prop :=
  ∀ k, Footprint sts store first k → ¬ Footprint sts store second k

/-- **Disjoint spaces, disjoint identities**: located firings with disjoint footprints are
independent in the sense of `Exactness`. -/
theorem disjoint_spaces_independent {first second : LocatedRule T}
    {s₁ s₂ : Selection O} {before : Configuration T O}
    (valid₁ : s₁.Valid A (located sts space payload) (first.toRule sts) before)
    (valid₂ : s₂.Valid A (located sts space payload) (second.toRule sts) before)
    (resolved₁ : Resolved sts before.equations first)
    (resolved₂ : Resolved sts before.equations second)
    (wellLocated : WellLocated sts space before)
    (apart : ApartFootprints (sts := sts) before.equations first second) :
    Independent (located sts space payload) (s₁.commit (T := T)) (s₂.commit (T := T)) := by
  have consistent := valid_before_consistent valid₁
  -- an identity used by both lies at a name of both footprints
  have takenAt₁ : ∀ o ∈ s₁.taken, ∃ k, Footprint sts before.equations first k ∧
      ResolvesTo sts before.equations (space o) k := by
    intro o taken
    obtain ⟨port, member, k, portAt, at_k⟩ := taken_at_port_space valid₁ resolved₁ wellLocated taken
    exact ⟨k, ⟨port.1, take_space_mem member, portAt⟩, at_k⟩
  have takenAt₂ : ∀ o ∈ s₂.taken, ∃ k, Footprint sts before.equations second k ∧
      ResolvesTo sts before.equations (space o) k := by
    intro o taken
    obtain ⟨port, member, k, portAt, at_k⟩ := taken_at_port_space valid₂ resolved₂ wellLocated taken
    exact ⟨k, ⟨port.1, take_space_mem member, portAt⟩, at_k⟩
  have readAt₁ : ∀ o ∈ s₁.read, ∃ k, Footprint sts before.equations first k ∧
      ResolvesTo sts before.equations (space o) k := by
    intro o read
    obtain ⟨port, member, k, portAt, at_k⟩ := read_at_port_space valid₁ resolved₁ wellLocated read
    exact ⟨k, ⟨port.1, read_space_mem member, portAt⟩, at_k⟩
  have readAt₂ : ∀ o ∈ s₂.read, ∃ k, Footprint sts before.equations second k ∧
      ResolvesTo sts before.equations (space o) k := by
    intro o read
    obtain ⟨port, member, k, portAt, at_k⟩ := read_at_port_space valid₂ resolved₂ wellLocated read
    exact ⟨k, ⟨port.1, read_space_mem member, portAt⟩, at_k⟩
  have madeAt₁ : ∀ o ∈ s₁.made, ∃ k, Footprint sts before.equations first k ∧
      ResolvesTo sts before.equations (space o) k := by
    intro o made
    obtain ⟨port, member, same, k, portAt⟩ := made_at_port_space valid₁ resolved₁ made
    exact ⟨k, ⟨port.1, produce_space_mem member, portAt⟩, same ▸ portAt⟩
  have madeAt₂ : ∀ o ∈ s₂.made, ∃ k, Footprint sts before.equations second k ∧
      ResolvesTo sts before.equations (space o) k := by
    intro o made
    obtain ⟨port, member, same, k, portAt⟩ := made_at_port_space valid₂ resolved₂ made
    exact ⟨k, ⟨port.1, produce_space_mem member, portAt⟩, same ▸ portAt⟩
  have never : ∀ o, (∃ k, Footprint sts before.equations first k ∧
      ResolvesTo sts before.equations (space o) k) →
      (∃ k, Footprint sts before.equations second k ∧
        ResolvesTo sts before.equations (space o) k) → False := by
    rintro o ⟨k₁, foot₁, at₁⟩ ⟨k₂, foot₂, at₂⟩
    have same : k₁ = k₂ := ResolvesTo.unique consistent at₁ at₂
    subst same
    exact apart k₁ foot₁ foot₂
  refine ⟨?_, ?_, ?_⟩
  · rintro (taken | made)
    · obtain ⟨o, in₁, in₂⟩ := Finset.not_disjoint_iff.mp taken
      exact never o (takenAt₁ o (by simpa [Selection.commit] using in₁))
        (takenAt₂ o (by simpa [Selection.commit] using in₂))
    · obtain ⟨o, in₁, in₂⟩ := Finset.not_disjoint_iff.mp made
      exact never o (madeAt₁ o (by simpa [Selection.commit] using in₁))
        (madeAt₂ o (by simpa [Selection.commit] using in₂))
  · rintro (kept | ⟨read, member, _⟩)
    · obtain ⟨o, in₁, in₂⟩ := Finset.not_disjoint_iff.mp kept
      exact never o (takenAt₁ o (by simpa [Selection.commit] using in₁))
        (readAt₂ o (by simpa [Selection.commit] using in₂))
    · simp [Selection.commit] at member
  · rintro (kept | ⟨read, member, _⟩)
    · obtain ⟨o, in₂, in₁⟩ := Finset.not_disjoint_iff.mp kept
      exact never o (readAt₁ o (by simpa [Selection.commit] using in₁))
        (takenAt₂ o (by simpa [Selection.commit] using in₂))
    · simp [Selection.commit] at member

/-- **Checks at one footprint ignore writes at a disjoint one**, under any store refining the
store before the step. -/
theorem disjoint_spaces_ignore_writes {first second : LocatedRule T}
    {s₂ : Selection O} {before : Configuration T O}
    (valid₂ : s₂.Valid A (located sts space payload) (second.toRule sts) before)
    (resolved₁ : Resolved sts before.equations first)
    (resolved₂ : Resolved sts before.equations second)
    (wellLocated : WellLocated sts space before)
    (apart : ApartFootprints (sts := sts) before.equations first second)
    {joint : EquationStore T} (refines : A.Refines joint before.equations) :
    ∀ check ∈ (first.toRule sts).checks,
      Check.IgnoresWrites A joint (located sts space payload) s₂ check := by
  intro check member
  simp only [LocatedRule.toRule, List.mem_map] at member
  obtain ⟨located_check, checkMember, rfl⟩ := member
  have written : ∀ o ∈ s₂.taken ++ s₂.made, ∃ k, Footprint sts before.equations second k ∧
      ResolvesTo sts before.equations (space o) k := by
    intro o member
    rcases List.mem_append.mp member with taken | made
    · obtain ⟨port, portMember, k, portAt, at_k⟩ :=
        taken_at_port_space valid₂ resolved₂ wellLocated taken
      exact ⟨k, ⟨port.1, take_space_mem portMember, portAt⟩, at_k⟩
    · obtain ⟨port, portMember, same, k, portAt⟩ := made_at_port_space valid₂ resolved₂ made
      exact ⟨k, ⟨port.1, produce_space_mem portMember, portAt⟩, same ▸ portAt⟩
  have apartAt : ∀ (s p : T), (∃ k, Footprint sts before.equations first k ∧
      ResolvesTo sts before.equations s k) → ∀ o ∈ s₂.taken ++ s₂.made,
        A.Apart joint (sts.atSpace s p) (located sts space payload o) := by
    rintro s p ⟨k₁, foot₁, at₁⟩ o member ⟨σ, solved⟩
    obtain ⟨k₂, foot₂, at₂⟩ := written o member
    obtain ⟨old, extra⟩ := (A.models_append _ _ _).mp solved
    have beforeσ : A.Models σ before.equations := refines σ old
    have related := extra _ List.mem_cons_self
    simp only [SubstitutionAction.Solves, located, sts.apply_atSpace, sts.E_atSpace] at related
    have same : k₁ = k₂ := at₁.name_eq beforeσ at₂ related.1
    subst same
    exact apart k₁ foot₁ foot₂
  cases located_check with
  | equal l r => trivial
  | absent s p =>
      obtain ⟨k, at_k⟩ := resolved₁ s (check_space_mem checkMember rfl)
      exact apartAt s p ⟨k, ⟨s, check_space_mem checkMember rfl, at_k⟩, at_k⟩
  | count s p n =>
      obtain ⟨k, at_k⟩ := resolved₁ s (check_space_mem checkMember rfl)
      exact apartAt s p ⟨k, ⟨s, check_space_mem checkMember rfl, at_k⟩, at_k⟩

/-- **Composition by name.** Two located firings, valid at one configuration, with disjoint
footprints, commute whenever their joint equations are consistent: each stays valid after the
other, and both orders reach the same occurrences with equivalent stores. Resources and checks
need no hypothesis; information does. -/
theorem disjoint_spaces_commute {first second : LocatedRule T}
    {s₁ s₂ : Selection O} {before : Configuration T O}
    (valid₁ : s₁.Valid A (located sts space payload) (first.toRule sts) before)
    (valid₂ : s₂.Valid A (located sts space payload) (second.toRule sts) before)
    (resolved₁ : Resolved sts before.equations first)
    (resolved₂ : Resolved sts before.equations second)
    (wellLocated : WellLocated sts space before)
    (apart : ApartFootprints (sts := sts) before.equations first second)
    (joint : A.Consistent ((before.equations ++
        GuardFreeProcessOrders.added (located sts space payload) (first.toRule sts) s₁) ++
      GuardFreeProcessOrders.added (located sts space payload) (second.toRule sts) s₂)) :
    s₂.Valid A (located sts space payload) (second.toRule sts)
        (s₁.result (located sts space payload) (first.toRule sts) before) ∧
      s₁.Valid A (located sts space payload) (first.toRule sts)
        (s₂.result (located sts space payload) (second.toRule sts) before) ∧
      GuardFreeProcessOrders.SameUpTo A
        (s₂.result (located sts space payload) (second.toRule sts)
          (s₁.result (located sts space payload) (first.toRule sts) before))
        (s₁.result (located sts space payload) (first.toRule sts)
          (s₂.result (located sts space payload) (second.toRule sts) before)) := by
  have apartSymm : ApartFootprints (sts := sts) before.equations second first :=
    fun k foot₂ foot₁ => apart k foot₁ foot₂
  have refinesJoint : A.Refines ((before.equations ++
        GuardFreeProcessOrders.added (located sts space payload) (first.toRule sts) s₁) ++
      GuardFreeProcessOrders.added (located sts space payload) (second.toRule sts) s₂)
      before.equations :=
    fun σ solved => ((A.models_append _ _ _).mp ((A.models_append _ _ _).mp solved).1).1
  exact Core.independently_ready_commute A (located sts space payload)
    (first.toRule sts, s₁) (second.toRule sts, s₂) before valid₁ valid₂
    (disjoint_spaces_independent valid₁ valid₂ resolved₁ resolved₂ wellLocated apart) joint
    (disjoint_spaces_ignore_writes valid₂ resolved₁ resolved₂ wellLocated apart refinesJoint)
    (disjoint_spaces_ignore_writes valid₁ resolved₂ resolved₁ wellLocated apartSymm refinesJoint)

/-- **An owner and an attenuated client sharing the mailbox name.** A client's new post at `m`
and the forwarder's firing on an earlier post commute, given the forwarder's own consistency
and distinct identities: these are all that `independently_ready_commute` asks here, because
neither rule has a check and the post takes nothing. -/
theorem post_and_forward_commute {label : O → T} {m n q' X : T} {o1 o2 o3 : O}
    {before : Configuration T O}
    (postValid : (makeOne o3).Valid A label ((sendRule m q').toRule sts) before)
    (forwardValid : (moveOne o1 o2).Valid A label ((forwarder m n X).toRule sts) before)
    (distinct : o3 ≠ o2) :
    (moveOne o1 o2).Valid A label ((forwarder m n X).toRule sts)
        ((makeOne o3).result label ((sendRule m q').toRule sts) before) ∧
      (makeOne o3).Valid A label ((sendRule m q').toRule sts)
        ((moveOne o1 o2).result label ((forwarder m n X).toRule sts) before) ∧
      GuardFreeProcessOrders.SameUpTo A
        ((moveOne o1 o2).result label ((forwarder m n X).toRule sts)
          ((makeOne o3).result label ((sendRule m q').toRule sts) before))
        ((makeOne o3).result label ((sendRule m q').toRule sts)
          ((moveOne o1 o2).result label ((forwarder m n X).toRule sts) before)) := by
  have postAdded : GuardFreeProcessOrders.added label ((sendRule m q').toRule sts) (makeOne o3) = [] := by
    simp [GuardFreeProcessOrders.added, Selection.equations, sendRule, LocatedRule.toRule, makeOne]
  refine Core.independently_ready_commute A label ((sendRule m q').toRule sts, makeOne o3)
    ((forwarder m n X).toRule sts, moveOne o1 o2) before postValid forwardValid ?_ ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · rintro (taken | made)
      · exact taken (by simp [Selection.commit, makeOne])
      · exact made (by simp [Selection.commit, makeOne, moveOne, distinct])
    · rintro (kept | ⟨read, member, _⟩)
      · exact kept (by simp [Selection.commit, makeOne, moveOne])
      · simp [Selection.commit] at member
    · rintro (kept | ⟨read, member, _⟩)
      · exact kept (by simp [Selection.commit, makeOne, moveOne])
      · simp [Selection.commit] at member
  · rw [postAdded, List.append_nil]
    obtain ⟨σ, solved⟩ := forwardValid.consistent
    exact ⟨σ, by simpa [GuardFreeProcessOrders.problem_eq] using solved⟩
  · simp [sendRule, LocatedRule.toRule]
  · simp [forwarder, LocatedRule.toRule]

end Composition

namespace Controls

/-! ### A shared variable is a channel across disjoint spaces -/

/-- Space 1 holds `p a`, space 2 holds `p b`. -/
def pairLabel : Nat → Tm := fun o =>
  if o = 0 then .loc (.nm 1) (.app (.sym "p") (.sym "a"))
  else .loc (.nm 2) (.app (.sym "p") (.sym "b"))

def pairSpace : Nat → Tm := fun o => if o = 0 then .nm 1 else .nm 2

def pairPayload : Nat → Tm := fun o =>
  if o = 0 then .app (.sym "p") (.sym "a") else .app (.sym "p") (.sym "b")

def pairWorld : Configuration Tm Nat := ⟨[], {0, 1}⟩

/-- Read `p X` at space 1, with variable `X` numbered `x`. -/
def readAtOne (x : Nat) : LocatedRule Tm := ⟨[], [(.nm 1, .app (.sym "p") (.var x))], [], [], []⟩

/-- Read `p X` at space 2, with variable `X` numbered `x`. -/
def readAtTwo (x : Nat) : LocatedRule Tm := ⟨[], [(.nm 2, .app (.sym "p") (.var x))], [], [], []⟩

def readZero : Selection Nat := ⟨[], [0], []⟩
def readOne : Selection Nat := ⟨[], [1], []⟩

theorem located_pair : located spaces pairSpace pairPayload = pairLabel := by
  funext o
  by_cases h : o = 0 <;> simp [located, spaces, pairSpace, pairPayload, pairLabel, h]

theorem readAtOne_valid (x : Nat) :
    readZero.Valid action (located spaces pairSpace pairPayload) ((readAtOne x).toRule spaces)
      pairWorld := by
  refine ⟨by simp [readZero], by simp [readZero], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, readZero], by simp [Selection.commit, readZero, pairWorld],
      by simp [Selection.commit, readZero], by simp [Selection.commit, readZero],
      by simp [Selection.commit]⟩, ⟨fun _ => .sym "a", ?_⟩, by simp [readAtOne, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, readAtOne,
    LocatedRule.toRule, readZero, pairWorld, place, located, spaces, pairSpace, pairPayload,
    Tm.subst]

theorem readAtTwo_valid (x : Nat) :
    readOne.Valid action (located spaces pairSpace pairPayload) ((readAtTwo x).toRule spaces)
      pairWorld := by
  refine ⟨by simp [readOne], by simp [readOne], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, readOne], by simp [Selection.commit, readOne, pairWorld],
      by simp [Selection.commit, readOne], by simp [Selection.commit, readOne],
      by simp [Selection.commit]⟩, ⟨fun _ => .sym "b", ?_⟩, by simp [readAtTwo, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, readAtTwo,
    LocatedRule.toRule, readOne, pairWorld, place, located, spaces, pairSpace, pairPayload,
    Tm.subst]

theorem pair_footprints_apart (x y : Nat) :
    ApartFootprints (sts := spaces) pairWorld.equations (readAtOne x) (readAtTwo y) := by
  rintro k ⟨s, member, at_k⟩ ⟨s', member', at_k'⟩
  simp [LocatedRule.spaces, readAtOne] at member
  simp [LocatedRule.spaces, readAtTwo] at member'
  subst member
  subst member'
  have one := at_k Tm.var (by simp [pairWorld])
  have two := at_k' Tm.var (by simp [pairWorld])
  simp [spaces, Tm.subst] at one two
  omega

/-- **A shared variable blocks commutation across disjoint spaces**: both readers of variable 0
are valid, and the reader at space 2 is not valid after the reader at space 1. -/
theorem shared_variable_blocks_commutation :
    readZero.Valid action (located spaces pairSpace pairPayload) ((readAtOne 0).toRule spaces)
        pairWorld ∧
      readOne.Valid action (located spaces pairSpace pairPayload) ((readAtTwo 0).toRule spaces)
        pairWorld ∧
      ApartFootprints (sts := spaces) pairWorld.equations (readAtOne 0) (readAtTwo 0) ∧
      ¬ readOne.Valid action (located spaces pairSpace pairPayload) ((readAtTwo 0).toRule spaces)
        (readZero.result (located spaces pairSpace pairPayload) ((readAtOne 0).toRule spaces)
          pairWorld) := by
  refine ⟨readAtOne_valid 0, readAtTwo_valid 0, pair_footprints_apart 0 0, ?_⟩
  intro valid
  obtain ⟨σ, solved⟩ := valid.consistent
  simp [SubstitutionAction.Solves, Selection.result, Selection.problem, Selection.equations,
    readAtOne, readAtTwo, LocatedRule.toRule, readZero, readOne, pairWorld, place, located,
    spaces, pairSpace, pairPayload, Tm.subst] at solved
  rw [solved.1] at solved
  simp at solved

theorem pairWorld_wellLocated : WellLocated spaces pairSpace pairWorld := by
  intro o present
  by_cases h : o = 0
  · subst h
    exact ⟨1, resolvesTo_name (sts := spaces) _ 1⟩
  · have named : pairSpace o = spaces.name 2 := by simp [pairSpace, h, spaces]
    rw [named]
    exact ⟨2, resolvesTo_name _ 2⟩

theorem pair_resolved_one (x : Nat) : Resolved spaces pairWorld.equations (readAtOne x) := by
  intro s member
  simp [LocatedRule.spaces, readAtOne] at member
  subst member
  exact ⟨1, resolvesTo_name _ 1⟩

theorem pair_resolved_two (x : Nat) : Resolved spaces pairWorld.equations (readAtTwo x) := by
  intro s member
  simp [LocatedRule.spaces, readAtTwo] at member
  subst member
  exact ⟨2, resolvesTo_name _ 2⟩

/-- **With separate variables the two readers commute.** -/
theorem separate_variables_commute :
    GuardFreeProcessOrders.SameUpTo action
      (readOne.result (located spaces pairSpace pairPayload) ((readAtTwo 1).toRule spaces)
        (readZero.result (located spaces pairSpace pairPayload) ((readAtOne 0).toRule spaces)
          pairWorld))
      (readZero.result (located spaces pairSpace pairPayload) ((readAtOne 0).toRule spaces)
        (readOne.result (located spaces pairSpace pairPayload) ((readAtTwo 1).toRule spaces)
          pairWorld)) := by
  refine (disjoint_spaces_commute (readAtOne_valid 0) (readAtTwo_valid 1) (pair_resolved_one 0)
    (pair_resolved_two 1) pairWorld_wellLocated (pair_footprints_apart 0 1) ?_).2.2
  refine ⟨fun i => if i = 0 then .sym "a" else .sym "b", ?_⟩
  simp [SubstitutionAction.Solves, GuardFreeProcessOrders.added, Selection.equations,
    readAtOne, readAtTwo, LocatedRule.toRule, readZero, readOne, pairWorld, place, located,
    spaces, pairSpace, pairPayload, Tm.subst]

/-! ### An owner rule that counts posts at the shared name -/

def countLabel : Nat → Tm := fun o =>
  if o = 7 then .loc (.nm 7) (.sym "letter") else .loc (.nm 3) (.sym "letter")

/-- One post at the mailbox 3. -/
def onePost : Configuration Tm Nat := ⟨[], {1}⟩

/-- The owner forwards only while exactly one letter is at the mailbox. -/
def countingForwarder : LocatedRule Tm :=
  ⟨[(.nm 3, .sym "letter")], [], [], [.count (.nm 3) (.sym "letter") 1],
    [(.nm 7, .sym "letter")]⟩

def clientPost : LocatedRule Tm := sendRule (.nm 3) (.sym "letter")

theorem counting_owner_valid :
    (moveOne 1 7).Valid action countLabel (countingForwarder.toRule spaces) onePost := by
  refine ⟨by simp [moveOne], by simp [moveOne], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, moveOne, onePost], by simp [Selection.commit, moveOne],
      by simp [Selection.commit, moveOne], by simp [Selection.commit, moveOne, onePost],
      by simp [Selection.commit]⟩, ⟨Tm.var, ?_⟩, ?_⟩
  · simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, countingForwarder,
      LocatedRule.toRule, moveOne, onePost, place, spaces, countLabel, Tm.subst]
  · intro check member σ _
    simp only [countingForwarder, LocatedRule.toRule, LocatedCheck.toCheck, List.map_cons,
      List.map_nil, List.mem_singleton] at member
    subst member
    classical
    show (Check.matches action σ countLabel onePost.present _).card = 1
    simp [Check.matches, onePost, Finset.filter_singleton, spaces, countLabel, Tm.subst]

/-- **A post spoils the counting owner**: after a second post the owner's rule is not valid,
though both were valid at the start. -/
theorem counting_owner_spoiled_by_post :
    (makeOne 5).Valid action countLabel (clientPost.toRule spaces) onePost ∧
      (moveOne 1 7).Valid action countLabel (countingForwarder.toRule spaces) onePost ∧
      ¬ (moveOne 1 7).Valid action countLabel (countingForwarder.toRule spaces)
        ((makeOne 5).result countLabel (clientPost.toRule spaces) onePost) := by
  refine ⟨(send_valid_iff (show countLabel 5 = spaces.atSpace (.nm 3) (.sym "letter") from rfl)
      onePost).mpr ⟨⟨Tm.var, by simp [onePost]⟩, by simp [onePost]⟩, counting_owner_valid, ?_⟩
  intro valid
  obtain ⟨σ, solved⟩ := valid.consistent
  have counted := valid.checks (.count (spaces.atSpace (.nm 3) (.sym "letter")) 1)
    (by simp [countingForwarder, LocatedRule.toRule, LocatedCheck.toCheck]) σ solved
  classical
  change (Check.matches action σ countLabel _ _).card = 1 at counted
  have presentTwo : ((makeOne 5).result countLabel (clientPost.toRule spaces) onePost).present =
      {1, 5} := by
    ext x
    simp [Selection.result, fire, Selection.commit, makeOne, onePost]
  rw [presentTwo] at counted
  simp [Check.matches, Finset.filter_insert, Finset.filter_singleton, spaces, countLabel,
    Tm.subst] at counted

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces
