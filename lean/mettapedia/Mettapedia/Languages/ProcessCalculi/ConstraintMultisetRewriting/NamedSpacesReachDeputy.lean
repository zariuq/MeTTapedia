import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesReach

/-!
# The confused-deputy discipline: literal spaces for a chosen rule set

Reach-relative selection bounds a guest by what it is handed. A privileged actor, a kernel that
holds the theorem space, reaches far, and reach does not stop it from being steered: if one of its
premise spaces comes from a request, the requester chooses where the kernel reads. The cure is a
discipline on the chosen rule set, not a law for every rule.

* **`LiteralSpaces r`**: every space position of `r` (take, read, produce, absence, count) is a
  written name. Such a rule meets the old law at every store (`LiteralSpaces.resolved`), and under
  a consistent store its footprint is exactly the names it writes (`LiteralSpaces.footprint_iff`).
* **Not steered** (`literal_footprint`): in every well-located configuration, whatever requesters
  wrote into it, every occurrence a firing of a literal rule takes, reads or makes, and every
  occurrence its checks can match, lies at a name the rule writes. Requester data at other names
  cannot change which selections are valid (`literal_not_steered`). For a privileged actor whose
  rules are all literal, the spaces its reach steps touch are among the names its rules write
  (`literal_reach_step_touches_written`), however far it reaches.

## The firewall (`DeputyControls`), after the transform-calculus firewall test

Spaces: requests at 1, `pub` at 2, `thm` at 3. The kernel's modus ponens takes a request and
publishes its conclusion at `thm`.

* **Literal premises**: `mpLiteral P Q` reads `P → Q` and `P` at `thm`. For every set of claims
  closed under modus ponens, every firing of every instance keeps `thm` sound in every
  configuration (`literal_kernel_keeps_thm_sound`), and a reach step of a requester that does
  not reach `thm` does too (`unreaching_step_keeps_thm_sound`); so does every run of such steps
  (`firewall_keeps_thm_sound`). Along every run from the firewall world, whatever requesters
  post at the request space and at `pub`, no occurrence at `thm` reads as `false`
  (`literal_kernel_never_publishes_false`). The honest request is served
  (`literal_kernel_honest`).
* **One premise space from the request** (negative control): `mpSteered S P Q` reads `P → Q` at
  the space `S` named by the request. The planted `pub:(a → false)` and the request
  `(req pub false)` make it publish `thm:false` in one firing (`steered_kernel_publishes_false`,
  `steered_breaks_thm`),
  and that firing is a reach step of the kernel (`steered_is_reach_step`): reach does not prevent
  it, the literal discipline does.

The discipline is chosen for the boundary; other rules, the mind's own among them, keep variable
spaces, search and indirection.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uN uO

section Literal

variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO} {A : SubstitutionAction T S}

variable (sts : SpaceTerms A N) in
/-- **Literal spaces**: every space position of the rule is a written name. -/
def LiteralSpaces (r : LocatedRule T) : Prop := ∀ s ∈ r.spaces, ∃ n, s = sts.name n

variable (sts : SpaceTerms A N) in
/-- The rule writes the name `n` in a space position. -/
def WrittenSpace (r : LocatedRule T) (n : N) : Prop := sts.name n ∈ r.spaces

variable {sts : SpaceTerms A N} {r : LocatedRule T}

/-- A literal rule meets the old law at every store. -/
theorem LiteralSpaces.resolved (literal : LiteralSpaces sts r) (store : EquationStore T) :
    Resolved sts store r := by
  intro s member
  obtain ⟨n, rfl⟩ := literal s member
  exact ⟨n, resolvesTo_name store n⟩

/-- Under a consistent store the footprint of a literal rule is exactly the names it writes. -/
theorem LiteralSpaces.footprint_iff (literal : LiteralSpaces sts r) {store : EquationStore T}
    (consistent : A.Consistent store) {n : N} :
    Footprint sts store r n ↔ WrittenSpace sts r n := by
  constructor
  · rintro ⟨s, member, at_n⟩
    obtain ⟨m, rfl⟩ := literal s member
    have names : m = n := ResolvesTo.unique consistent (resolvesTo_name store m) at_n
    subst names
    exact member
  · intro written
    exact ⟨sts.name n, written, resolvesTo_name store n⟩

variable [DecidableEq O] {space payload : O → T} {C : Configuration T O}
  {selection : Selection O}

/-- **A literal rule is not steered by what is present.** In every well-located configuration,
whatever requesters wrote into it, every occurrence a valid selection takes or reads lies at a
name the rule writes, every occurrence it makes is placed at a name the rule writes, and every
occurrence a check of the step can match lies at a name the rule writes. -/
theorem literal_footprint (literal : LiteralSpaces sts r)
    (valid : selection.Valid A (located sts space payload) (r.toRule sts) C)
    (wellLocated : WellLocated sts space C) :
    (∀ o ∈ selection.taken ++ selection.read,
        ∃ n, WrittenSpace sts r n ∧ ResolvesTo sts C.equations (space o) n) ∧
      (∀ o ∈ selection.made, ∃ n, WrittenSpace sts r n ∧ space o = sts.name n) ∧
      ∀ s ∈ r.spaces, ∀ p : T, ∀ σ : S, A.Models σ C.equations → ∀ o ∈ C.present,
        A.E (A.apply σ (sts.atSpace s p)) (A.apply σ (located sts space payload o)) →
          ∃ n, WrittenSpace sts r n ∧ ResolvesTo sts C.equations (space o) n := by
  have consistent := valid_before_consistent valid
  have resolved := literal.resolved C.equations
  refine ⟨fun o member => ?_, fun o made => ?_, fun s member p σ solved o present matching => ?_⟩
  · rcases List.mem_append.mp member with taken | read
    · obtain ⟨port, portMember, n, portAt, at_n⟩ :=
        taken_at_port_space valid resolved wellLocated taken
      obtain ⟨m, same⟩ := literal port.1 (take_space_mem portMember)
      rw [same] at portAt
      have names : m = n := ResolvesTo.unique consistent (resolvesTo_name _ m) portAt
      subst names
      have written := take_space_mem portMember
      rw [same] at written
      exact ⟨m, written, at_n⟩
    · obtain ⟨port, portMember, n, portAt, at_n⟩ :=
        read_at_port_space valid resolved wellLocated read
      obtain ⟨m, same⟩ := literal port.1 (read_space_mem portMember)
      rw [same] at portAt
      have names : m = n := ResolvesTo.unique consistent (resolvesTo_name _ m) portAt
      subst names
      have written := read_space_mem portMember
      rw [same] at written
      exact ⟨m, written, at_n⟩
  · obtain ⟨port, portMember, same, _⟩ := made_port valid made
    obtain ⟨m, named⟩ := literal port.1 (produce_space_mem portMember)
    have written := produce_space_mem portMember
    rw [named] at written
    exact ⟨m, written, same.symm.trans named⟩
  · obtain ⟨m, rfl⟩ := literal s member
    exact ⟨m, member, check_matches_at_space wellLocated (resolvesTo_name _ m) solved present
      matching⟩

/-- **Requester data elsewhere does not steer a literal rule**: two configurations with one
consistent store that agree on the occurrences at the names the rule writes admit the same
selections. -/
theorem literal_not_steered (literal : LiteralSpaces sts r) {D : Configuration T O}
    (consistent : A.Consistent C.equations) (sameStore : C.equations = D.equations)
    (agree : ∀ o n, WrittenSpace sts r n → ResolvesTo sts C.equations (space o) n →
      (o ∈ C.present ↔ o ∈ D.present))
    (wellC : WellLocated sts space C) (wellD : WellLocated sts space D)
    (freshC : Disjoint selection.made.toFinset C.present)
    (freshD : Disjoint selection.made.toFinset D.present) :
    selection.Valid A (located sts space payload) (r.toRule sts) C ↔
      selection.Valid A (located sts space payload) (r.toRule sts) D :=
  valid_iff_of_agree_on_spaces (literal.resolved _) wellC wellD
    ⟨sameStore, fun o ⟨n, footprint, at_n⟩ =>
      agree o n ((literal.footprint_iff consistent).mp footprint) at_n⟩ freshC freshD

/-- **A privileged actor with literal rules touches only the names its rules write**, however far
it reaches: the taken, read and made occurrences of its reach steps lie at written names. -/
theorem literal_reach_step_touches_written [DecidableEq N] {ns : NameSwap sts} {K : Set T}
    {D : Configuration T O} (literal : LiteralSpaces sts r)
    (step : ReachStep ns K space payload r C D) (wellLocated : WellLocated sts space C) :
    ∃ selection : Selection O,
      selection.Valid A (located sts space payload) (r.toRule sts) C ∧
      D = selection.result (located sts space payload) (r.toRule sts) C ∧
      (∀ o ∈ selection.taken ++ selection.read,
        ∃ n, WrittenSpace sts r n ∧ ResolvesTo sts C.equations (space o) n) ∧
      ∀ o ∈ selection.made, ∃ n, WrittenSpace sts r n ∧ space o = sts.name n := by
  obtain ⟨selection, admits, rfl⟩ := step
  have footprint := literal_footprint literal admits.valid wellLocated
  exact ⟨selection, admits.valid, rfl, footprint.1, footprint.2.1⟩

end Literal

/-! ## The firewall -/

namespace DeputyControls

open Controls

def claimA : Tm := .sym "a"
def claimB : Tm := .sym "b"
def falsum : Tm := .sym "false"

/-- `p → q`. -/
def imp (p q : Tm) : Tm := .app (.app (.sym "imp") p) q

/-- A request to publish `q`. -/
def request (q : Tm) : Tm := .app (.sym "req") q

/-- A request that also names the space of the implication premise. -/
def requestAt (s q : Tm) : Tm := .app (.app (.sym "req") s) q

theorem subst_imp (σ : Nat → Tm) (p q : Tm) : (imp p q).subst σ = imp (p.subst σ) (q.subst σ) :=
  rfl

/-- **The kernel with literal premise spaces**: take a request for `Q` at 1, read `P → Q` and `P`
at `thm` (3), publish `Q` at `thm`. -/
def mpLiteral (P Q : Tm) : LocatedRule Tm :=
  ⟨[(.nm 1, request Q)], [(.nm 3, imp P Q), (.nm 3, P)], [], [], [(.nm 3, Q)]⟩

/-- **The kernel with one premise space taken from the request.** -/
def mpSteered (premiseSpace P Q : Tm) : LocatedRule Tm :=
  ⟨[(.nm 1, requestAt premiseSpace Q)], [(premiseSpace, imp P Q), (.nm 3, P)], [], [],
    [(.nm 3, Q)]⟩

theorem mpLiteral_literal (P Q : Tm) : LiteralSpaces spaces (mpLiteral P Q) := by
  intro s member
  simp only [LocatedRule.spaces, mpLiteral, List.map_cons, List.map_nil, List.filterMap_nil,
    List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨3, rfl⟩

theorem mpSteered_not_literal : ¬ LiteralSpaces spaces (mpSteered (.var 2) (.var 0) (.var 1)) := by
  intro literal
  obtain ⟨n, same⟩ := literal (.var 2) (by simp [LocatedRule.spaces, mpSteered])
  cases same

/-- `thm` is sound for a set of claims: under every solution of the store, every occurrence that
reads as lying at `thm` reads as a claim of the set. -/
def ThmSound (Sound : Tm → Prop) (space payload : Nat → Tm) (C : Configuration Tm Nat) : Prop :=
  ∀ σ, action.Models σ C.equations → ∀ o ∈ C.present,
    (space o).subst σ = .nm 3 → Sound ((payload o).subst σ)

/-- A set of claims closed under modus ponens. -/
def MPClosed (Sound : Tm → Prop) : Prop := ∀ p q, Sound (imp p q) → Sound p → Sound q

/-- At a solution of a valid selection's problem, each read occurrence reads as its port. -/
theorem reads_pairwise {space payload : Nat → Tm} {rule : RuleInstance Tm}
    {C : Configuration Tm Nat} {selection : Selection Nat}
    (valid : selection.Valid action (located spaces space payload) rule C) {σ : Nat → Tm}
    (solved : action.Models σ (selection.problem (located spaces space payload) rule C)) :
    List.Forall₂ (fun p o => p.subst σ = Tm.loc ((space o).subst σ) ((payload o).subst σ))
      rule.read selection.read :=
  (Selection.models_problem action valid solved).2.2.1

/-- **The literal kernel keeps `thm` sound**, for every instance, in every configuration. -/
theorem literal_kernel_keeps_thm_sound {Sound : Tm → Prop} (closed : MPClosed Sound) (P Q : Tm)
    {space payload : Nat → Tm} {C : Configuration Tm Nat} {selection : Selection Nat}
    (valid : selection.Valid action (located spaces space payload)
      ((mpLiteral P Q).toRule spaces) C)
    (sound : ThmSound Sound space payload C) :
    ThmSound Sound space payload
      (selection.result (located spaces space payload) ((mpLiteral P Q).toRule spaces) C) := by
  intro σ solved o present atThm
  have beforeσ : action.Models σ C.equations := (Selection.models_problem action valid solved).1
  rcases mem_fire.mp present with ⟨old, _⟩ | madeMember
  · exact sound σ beforeσ o old atThm
  · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
    obtain ⟨port, portMember, _, payloadEq⟩ := made_port valid made
    simp only [mpLiteral, List.mem_singleton] at portMember
    subst portMember
    have readLength : selection.read.length = 2 := by
      simpa [mpLiteral, LocatedRule.toRule] using valid.read_length.symm
    obtain ⟨r1, r2, chosen⟩ := List.length_eq_two.mp readLength
    have reads := reads_pairwise valid solved
    rw [chosen] at reads
    have shape : ((mpLiteral P Q).toRule spaces).read =
        [Tm.loc (.nm 3) (imp P Q), Tm.loc (.nm 3) P] := rfl
    rw [shape] at reads
    have first := (List.forall₂_cons.mp reads).1
    have second := (List.forall₂_cons.mp (List.forall₂_cons.mp reads).2).1
    simp only [Tm.subst, Tm.loc.injEq, subst_imp] at first second
    have present1 : r1 ∈ C.present :=
      valid.occurrences.kept_subset (by simp [Selection.commit, chosen])
    have present2 : r2 ∈ C.present :=
      valid.occurrences.kept_subset (by simp [Selection.commit, chosen])
    have soundImp := sound σ beforeσ r1 present1 first.1.symm
    have soundP := sound σ beforeσ r2 present2 second.1.symm
    rw [← first.2] at soundImp
    rw [← second.2] at soundP
    rw [← payloadEq]
    exact closed _ _ soundImp soundP

/-- **A requester that does not reach `thm` keeps it sound**: its reach step makes nothing there,
and refining the store only removes solutions. -/
theorem unreaching_step_keeps_thm_sound {Sound : Tm → Prop} {space payload : Nat → Tm}
    {K : Set Tm} {r : LocatedRule Tm} {C D : Configuration Tm Nat}
    (step : ReachStep names K space payload r C D)
    (unreached : ¬ Reached names K space payload C 3)
    (sound : ThmSound Sound space payload C) : ThmSound Sound space payload D := by
  obtain ⟨selection, admits, rfl⟩ := step
  intro σ solved o present atThm
  have beforeσ : action.Models σ C.equations :=
    (Selection.models_problem action admits.valid solved).1
  rcases mem_fire.mp present with ⟨old, _⟩ | madeMember
  · exact sound σ beforeσ o old atThm
  · have made : o ∈ selection.made := by simpa [Selection.commit] using madeMember
    obtain ⟨k, reached, at_k⟩ := admits.made_reached made
    have atK : (space o).subst σ = .nm k := at_k σ solved
    rw [atThm] at atK
    cases atK
    exact absurd reached unreached

/-- A step of the firewall: a firing of the literal kernel, of any instance, or a reach step of a
requester that does not reach `thm`. -/
def FirewallStep (space payload : Nat → Tm) (C D : Configuration Tm Nat) : Prop :=
  (∃ P Q, Step action (located spaces space payload) ((mpLiteral P Q).toRule spaces) C D) ∨
    ∃ (K : Set Tm) (r : LocatedRule Tm),
      ReachStep names K space payload r C D ∧ ¬ Reached names K space payload C 3

/-- **The firewall keeps `thm` sound** along every run, for every set of claims closed under
modus ponens. -/
theorem firewall_keeps_thm_sound {Sound : Tm → Prop} (closed : MPClosed Sound)
    {space payload : Nat → Tm} {C D : Configuration Tm Nat}
    (run : Relation.ReflTransGen (FirewallStep space payload) C D)
    (sound : ThmSound Sound space payload C) : ThmSound Sound space payload D := by
  induction run with
  | refl => exact sound
  | tail _ step ih =>
      rcases step with ⟨P, Q, selection, valid, rfl⟩ | ⟨K, r, reachStep, unreached⟩
      · exact literal_kernel_keeps_thm_sound closed P Q valid ih
      · exact unreaching_step_keeps_thm_sound reachStep unreached ih

/-! ### The firewall world -/

/-- Occurrences: 0 `a` and 1 `a → b` at `thm`; 2 the planted `a → false` at `pub`; 3 a request
for `false` and 4 a request for `b` at the request space; 5 the kernel's publication at `thm`. -/
def fwSpace : Nat → Tm
  | 0 => .nm 3
  | 1 => .nm 3
  | 2 => .nm 2
  | 3 => .nm 1
  | 4 => .nm 1
  | _ => .nm 3

def fwPayload : Nat → Tm
  | 0 => claimA
  | 1 => imp claimA claimB
  | 2 => imp claimA falsum
  | 3 => request falsum
  | 4 => request claimB
  | _ => .var 1

def firewallWorld : Configuration Tm Nat := ⟨[], {0, 1, 2, 3, 4}⟩

/-- The claims sound at `thm`: `a`, `a → b` and `b`. -/
def firewallSound (c : Tm) : Prop := c = claimA ∨ c = imp claimA claimB ∨ c = claimB

theorem firewallSound_closed : MPClosed firewallSound := by
  intro p q hImp _
  rcases hImp with h | h | h
  · simp [imp, claimA] at h
  · simp only [imp, claimA, claimB, Tm.app.injEq, true_and] at h
    exact Or.inr (Or.inr h.2)
  · simp [imp, claimB] at h

theorem falsum_unsound : ¬ firewallSound falsum := by
  simp [firewallSound, falsum, claimA, claimB, imp]

theorem firewallWorld_sound {space payload : Nat → Tm}
    (initial : ∀ o ∈ firewallWorld.present, space o = fwSpace o ∧ payload o = fwPayload o) :
    ThmSound firewallSound space payload firewallWorld := by
  intro σ _ o present atThm
  obtain ⟨sameSpace, samePayload⟩ := initial o present
  rw [sameSpace] at atThm
  rw [samePayload]
  simp only [firewallWorld, Finset.mem_insert, Finset.mem_singleton] at present
  rcases present with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · simp [fwSpace, Tm.subst] at atThm
  · simp [fwSpace, Tm.subst] at atThm
  · simp [fwSpace, Tm.subst] at atThm

/-- **With literal `thm` premises the kernel never publishes `thm:false`.** Whatever labels later
occurrences carry, whatever instances the kernel fires, and whatever requesters that do not reach
`thm` do, no occurrence at `thm` ever reads as `false`. -/
theorem literal_kernel_never_publishes_false {space payload : Nat → Tm}
    (initial : ∀ o ∈ firewallWorld.present, space o = fwSpace o ∧ payload o = fwPayload o)
    {D : Configuration Tm Nat}
    (run : Relation.ReflTransGen (FirewallStep space payload) firewallWorld D) :
    ∀ σ, action.Models σ D.equations → ∀ o ∈ D.present,
      (space o).subst σ = .nm 3 → (payload o).subst σ ≠ falsum := by
  intro σ solved o present atThm isFalse
  have sound := firewall_keeps_thm_sound firewallSound_closed run (firewallWorld_sound initial)
  have claim := sound σ solved o present atThm
  rw [isFalse] at claim
  exact falsum_unsound claim

/-- The honest request: take the request for `b`, read `a → b` and `a` at `thm`, publish `b`. -/
def honestSel : Selection Nat := ⟨[4], [1, 0], [5]⟩

/-- **Positive control: the honest request is served**, publishing `b` at `thm`. -/
theorem literal_kernel_honest :
    honestSel.Valid action (located spaces fwSpace fwPayload)
        ((mpLiteral (.var 0) (.var 1)).toRule spaces) firewallWorld ∧
      ∀ σ, action.Models σ (honestSel.result (located spaces fwSpace fwPayload)
        ((mpLiteral (.var 0) (.var 1)).toRule spaces) firewallWorld).equations →
          (fwPayload 5).subst σ = claimB := by
  constructor
  · refine ⟨by simp [honestSel], by simp [honestSel], rfl, rfl, rfl,
      ⟨by simp [Selection.commit, honestSel, firewallWorld],
        by simp [Selection.commit, honestSel, firewallWorld, Finset.insert_subset_iff],
        by simp [Selection.commit, honestSel], by simp [Selection.commit, honestSel, firewallWorld],
        by simp [Selection.commit]⟩,
      ⟨fun i => if i = 0 then claimA else claimB, ?_⟩,
      by simp [mpLiteral, LocatedRule.toRule]⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, mpLiteral,
      LocatedRule.toRule, honestSel, firewallWorld, place, located, spaces, fwSpace, fwPayload,
      request, imp, claimA, claimB, Tm.subst]
  · intro σ solved
    simp [SubstitutionAction.Solves, Selection.result, Selection.problem, Selection.equations,
      mpLiteral, LocatedRule.toRule, honestSel, firewallWorld, place, located, spaces, fwSpace,
      fwPayload, request, imp, claimA, claimB, Tm.subst] at solved
    simp [fwPayload, Tm.subst, claimB, solved.1]

/-! ### Negative control: one premise space from the request -/

/-- Occurrences: 0 `a` and 1 `a → b` at `thm`; 2 the planted `a → false` at `pub`; 3 the request
`(req pub false)`; 5 the kernel's publication at `thm`. -/
def steerSpace : Nat → Tm
  | 0 => .nm 3
  | 1 => .nm 3
  | 2 => .nm 2
  | 3 => .nm 1
  | _ => .nm 3

def steerPayload : Nat → Tm
  | 0 => claimA
  | 1 => imp claimA claimB
  | 2 => imp claimA falsum
  | 3 => requestAt (.nm 2) falsum
  | _ => .var 1

def steerWorld : Configuration Tm Nat := ⟨[], {0, 1, 2, 3}⟩

def steerRule : LocatedRule Tm := mpSteered (.var 2) (.var 0) (.var 1)

/-- Take the request, read `a → false` at the space it names and `a` at `thm`, publish. -/
def steerSel : Selection Nat := ⟨[3], [2, 0], [5]⟩

def steered : Configuration Tm Nat :=
  steerSel.result (located spaces steerSpace steerPayload) (steerRule.toRule spaces) steerWorld

theorem steer_valid :
    steerSel.Valid action (located spaces steerSpace steerPayload) (steerRule.toRule spaces)
      steerWorld := by
  refine ⟨by simp [steerSel], by simp [steerSel], rfl, rfl, rfl,
    ⟨by simp [Selection.commit, steerSel, steerWorld],
      by simp [Selection.commit, steerSel, steerWorld, Finset.insert_subset_iff],
      by simp [Selection.commit, steerSel], by simp [Selection.commit, steerSel, steerWorld],
      by simp [Selection.commit]⟩,
    ⟨fun i => if i = 0 then claimA else if i = 1 then falsum else .nm 2, ?_⟩,
    by simp [steerRule, mpSteered, LocatedRule.toRule]⟩
  simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, steerRule, mpSteered,
    LocatedRule.toRule, steerSel, steerWorld, place, located, spaces, steerSpace, steerPayload,
    requestAt, imp, claimA, falsum, Tm.subst]

theorem steered_solutions (σ : Nat → Tm) (solved : action.Models σ steered.equations) :
    σ 1 = falsum ∧ σ 2 = .nm 2 := by
  simp [steered, SubstitutionAction.Solves, Selection.result, Selection.problem,
    Selection.equations, steerRule, mpSteered, LocatedRule.toRule, steerSel, steerWorld, place,
    located, spaces, steerSpace, steerPayload, requestAt, imp, claimA, falsum, Tm.subst] at solved
  exact ⟨solved.1.2, solved.1.1⟩

/-- **The confused deputy**: steered by the request, one firing publishes `thm:false`. -/
theorem steered_kernel_publishes_false :
    5 ∈ steered.present ∧ steerSpace 5 = .nm 3 ∧
      ∀ σ, action.Models σ steered.equations → (steerPayload 5).subst σ = falsum := by
  refine ⟨?_, rfl, fun σ solved => ?_⟩
  · simp [steered, Selection.result, fire, Selection.commit, steerSel]
  · simpa [steerPayload, Tm.subst] using (steered_solutions σ solved).1

/-- The world before is sound and the world after is not. -/
theorem steered_breaks_thm :
    ThmSound firewallSound steerSpace steerPayload steerWorld ∧
      ¬ ThmSound firewallSound steerSpace steerPayload steered := by
  constructor
  · intro σ _ o present atThm
    simp only [steerWorld, Finset.mem_insert, Finset.mem_singleton] at present
    rcases present with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · simp [steerSpace, Tm.subst] at atThm
    · simp [steerSpace, Tm.subst] at atThm
  · intro sound
    obtain ⟨σ, solved⟩ := steer_valid.consistent
    have published := steered_kernel_publishes_false
    have claim := sound σ solved 5 published.1 (by simp [steerSpace, Tm.subst])
    rw [published.2.2 σ solved] at claim
    exact falsum_unsound claim

/-- The kernel's terms: the request, `pub` and `thm` spaces, and its rule. -/
def kernelTerms : Set Tm :=
  {.nm 1, .nm 2, .nm 3, .var 2, .loc (.nm 1) (requestAt (.var 2) (.var 1)),
    .loc (.var 2) (imp (.var 0) (.var 1)), .loc (.nm 3) (.var 0), .loc (.nm 3) (.var 1)}

/-- **Reach does not prevent the confused deputy**: the steered firing is a reach step of the
kernel, which reaches the request space, `pub` and `thm`. -/
theorem steered_is_reach_step :
    ReachStep names kernelTerms steerSpace steerPayload steerRule steerWorld steered := by
  have written : ∀ k, Tm.nm k ∈ kernelTerms →
      Reached names kernelTerms steerSpace steerPayload steerWorld k := fun k member =>
    Reach.of_possesses (written_name_possessed ⟨Tm.var, by simp [steerWorld]⟩ member)
  refine ⟨steerSel, ⟨?_, steer_valid, ?_, ?_⟩, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [steerRule, mpSteered, LocatedRule.toRule, LocatedRule.spaces, place, kernelTerms,
        spaces]
  · intro o member
    simp only [steerSel, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨1, written 1 (by simp [kernelTerms]), resolvesTo_name _ 1⟩
    · exact ⟨2, written 2 (by simp [kernelTerms]), resolvesTo_name _ 2⟩
    · exact ⟨3, written 3 (by simp [kernelTerms]), resolvesTo_name _ 3⟩
  · intro s member
    simp only [LocatedRule.spaces, steerRule, mpSteered, List.map_cons, List.map_nil,
      List.filterMap_nil, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨1, resolvesTo_name _ 1⟩
    · refine ⟨2, fun σ solved => ?_⟩
      simpa [spaces, Tm.subst] using (steered_solutions σ solved).2
    · exact ⟨3, resolvesTo_name _ 3⟩
    · exact ⟨3, resolvesTo_name _ 3⟩

end DeputyControls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

/-! ## Axiom audit -/

section Audit

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

#print axioms LiteralSpaces.resolved
#print axioms LiteralSpaces.footprint_iff
#print axioms literal_footprint
#print axioms literal_not_steered
#print axioms literal_reach_step_touches_written
#print axioms DeputyControls.subst_imp
#print axioms DeputyControls.mpLiteral_literal
#print axioms DeputyControls.mpSteered_not_literal
#print axioms DeputyControls.reads_pairwise
#print axioms DeputyControls.literal_kernel_keeps_thm_sound
#print axioms DeputyControls.unreaching_step_keeps_thm_sound
#print axioms DeputyControls.firewall_keeps_thm_sound
#print axioms DeputyControls.firewallSound_closed
#print axioms DeputyControls.falsum_unsound
#print axioms DeputyControls.firewallWorld_sound
#print axioms DeputyControls.literal_kernel_never_publishes_false
#print axioms DeputyControls.literal_kernel_honest
#print axioms DeputyControls.steer_valid
#print axioms DeputyControls.steered_solutions
#print axioms DeputyControls.steered_kernel_publishes_false
#print axioms DeputyControls.steered_breaks_thm
#print axioms DeputyControls.steered_is_reach_step

end Audit
